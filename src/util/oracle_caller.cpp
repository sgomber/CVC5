
#include "bitvector.h"
#include "oracle_caller.h"
#include "rational_gmp_imp.h"
#include "run.h"
#include "theory/quantifiers/quantifiers_attributes.h"

#include <sstream>

namespace cvc5 {

const std::string WHITESPACE = " \n\r\t\f\v";

std::string ltrim(const std::string &s)
{
    size_t start = s.find_first_not_of(WHITESPACE);
    return (start == std::string::npos) ? "" : s.substr(start);
}
 
std::string rtrim(const std::string &s)
{
    size_t end = s.find_last_not_of(WHITESPACE);
    return (end == std::string::npos) ? "" : s.substr(0, end + 1);
}
 
std::string trim(const std::string &s) {
    return rtrim(ltrim(s));
}

bool is_digits(const std::string &str)
{
  return str.find_first_not_of("0123456789") == std::string::npos;
}

Node OracleCaller::get_hex_numeral(std::string in)
{
  // we accept any sequence of '0'-'9', 'a'-'f', 'A'-'F'
  std::size_t width = in.size()*16;
  NodeManager* nm = NodeManager::currentNM();
  unsigned int val = std::stoi(in, nullptr, 16);
  Node result =  nm->mkConst(BitVector(width,val));
  return result;
}

Node OracleCaller::get_bin_numeral(std::string in)
{
  // we accept any sequence of '0'-'1'
  std::size_t width = in.size();
  NodeManager* nm = NodeManager::currentNM();
  unsigned int val = std::stoi(in, nullptr, 2);
  Node result = nm->mkConst(BitVector(width,val));
  return result;
}

Node OracleCaller::get_dec_numeral(std::string in)
{
  // we accept any sequence of '0'-'9'
  NodeManager* nm = NodeManager::currentNM();
  unsigned int val = std::stoi(in, nullptr, 10);
  Node result  = nm->mkConst(Rational(val,1u));
  return result;
}

Node OracleCaller::responseParser(std::string &in)
{
  // Assumes the response is a singular integer or bitvector literal
  // Temporary: will eventually be replaced with some subcomponent of full parser
  NodeManager* nm = NodeManager::currentNM();
  std::string trimmedString = trim(in);
  if(in.at(0)=='#')
  {
    if(in.at(1)=='b')
    {
      return get_bin_numeral(trimmedString);
    }
    else if(in.at(1)=='x')
    {
      return get_hex_numeral(trimmedString);
    }
    else
    {
      Trace("response-parser")<< "Response string "<< in <<" had # at the start and then was not binary or hex"<<std::endl;
      Assert(0); // throw error here
    }
  }
  else if(is_digits(trimmedString))
  {
    return get_dec_numeral(trimmedString);
  }
  else if(in.find("true")!=std::string::npos)
  {
    Node result = nm->mkConst(true);
    return result;
  }
  else if(trimmedString.find("false")!=std::string::npos)
  {
    Node result = nm->mkConst(false);
    return result;
  }
  else
  {
    Trace("oracle-calls") <<"Could not parse response "<<in<<std::endl;
    Assert(0); // throw error here
  }
}

Node OracleCaller::callOracle(const Node fapp)
{

  if(d_cachedResults.find(fapp)!=d_cachedResults.end())
  {
     Trace("oracle-calls") <<"Using cached oracle result for "<< fapp << std::endl;
    return d_cachedResults.at(fapp);
  }
  Trace("oracle-calls") << "Running oracle: " << d_binaryName ;
  std::vector<std::string> string_args;
  string_args.push_back(d_binaryName);

  for (const auto &arg : fapp)
  {
    std::ostringstream oss;
    oss << arg;
    string_args.push_back(oss.str());
    Trace("oracle-calls") << ' ' << arg;
  }
  Trace("oracle-calls") << std::endl;

  // run the oracle binary
  std::ostringstream stdout_stream;

  auto run_result = run(
      d_binaryName,
      string_args,
      "",
      stdout_stream,
      "");

  // we assume that an oracle has a return code of 0 or 10. 
  if (run_result != 0 && run_result !=10)
  {
    Trace("oracle-calls") << "oracle " << d_binaryName << " has failed with exit code " << run_result << std::endl;
    Assert(run_result==0 || run_result==10);
  }
  // we assume that the oracle returns the result in SMT-LIB format
  std::string stringResponse = stdout_stream.str();
  // parse response into a Node
  Node response = responseParser(stringResponse);
  d_cachedResults[fapp]= response;
  return response;
}

std::string OracleCaller::setBinaryName(const Node n)
{
  // oracle functions have no children
  if(n.getNumChildren()<3)
  {
    return n.getAttribute(theory::OracleInterfaceAttribute());
  }

  // oracle interfaces have children, and the attribute is stored in 2nd child 
  for (const Node& v : n[2][0]) 
  { 
    if(v.getAttribute(theory::OracleInterfaceAttribute())!="")
    {
      return v.getAttribute(theory::OracleInterfaceAttribute());
    }
  }
  return "";
} 

}