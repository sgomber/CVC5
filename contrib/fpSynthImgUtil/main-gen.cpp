//g++ main.cpp -o ../fpSynthImgDiff
//g++ main.cpp -o ../fpSynthImgVerify

// REQUIRES $1: *.ppm to diff
// REQUIRES $2: *.ppm to diff

#include <iostream>
#include <string>
#include <fstream>
#include <map>
#include <vector>
#include <stdlib.h>
#include <sstream>
#include <cstring>
#include <iomanip>

int main( int argc, char* argv[] )
{
  if( argc<3 )
  {
    std::cout << "Expected two *.ppm images." << std::endl;
    return -1;
  }
  std::fstream f1(argv[1], std::ios::in);
  std::fstream f2(argv[2], std::ios::in);
  unsigned width[2];
  unsigned height[2];
  std::string tmp;
  unsigned tmpi;
  for( unsigned i=0; i<2; i++ )
  {
    std::fstream& f = ( i==0 ? f1 : f2 );
    f >> tmp;
    f >> width[i];
    f >> height[i];
    f >> tmpi;
  }
  if( width[0]!=width[1] || height[0]!=height[1] )
  {
    std::cout << "Input images have different sizes." << std::endl;
    return -1;
  }
  bool imgDiff = __DIFF;
  bool imgVerify = __VERIFY;
  if( imgDiff )
  {
    std::cout << "P3 " << width[0] << " " << height[0] << " 256" << std::endl;
  }
  unsigned numIncorrect = 0;
  unsigned numIncorrectUndef = 0;
  unsigned numTests = width[0]*height[0];
  std::map<bool, unsigned> numIncorrectRes;
  for( unsigned w=0; w<width[0]; w++ )
  {
    for( unsigned h=0; h<height[0]; h++ )
    {
      unsigned c1[3];
      unsigned c2[3];
      bool isBw = true;
      for( unsigned i=0; i<3; i++ )
      {
        f1 >> c1[i];
        f2 >> c2[i];
        if( i>0 )
        {
          if( c1[i]!=c1[i-1] || c2[i]!=c2[i-1] )
          {
            isBw = false;
            if( !imgDiff )
            {
              std::cout << "Warning: not black and white for point " << w << ", " << h << " (" << (c1[i]==c1[i-1]) << (c2[i]==c2[i-1]) << ")" << std::endl;
            }
          }
        }
      }
      if( !isBw )
      {        
        if( imgDiff )
        {
          std::cout << "128 128 128 ";
        }
        if( imgVerify )
        {
          numIncorrectUndef++;
        }
      }
      else
      {
        // assuming black and white
        if( imgDiff )
        {
          std::cout << c1[0] << " ";
          std::cout << (c1[0]<c2[0] ? c1[0] : c2[0]) << " ";
          std::cout << c2[0] << " ";
        }
        if( imgVerify )
        {
          if( c1[0]>0 && c2[0]==0 )
          {
            numIncorrectRes[0]++;
            numIncorrect++;
          }
          else if( c1[0]==0 && c2[0]>0 )
          {
            numIncorrectRes[1]++;
            numIncorrect++;
          }
        }
      }
    }
    if( imgDiff )
    {    
      std::cout << std::endl;
    }
  }
  
  if( imgVerify )
  {
    std::cout << "--- fpSynthImgVerify" << std::endl;
    std::cout << "       Total #incorrect : " << numIncorrect << std::endl;
    for (std::map<bool, unsigned>::iterator it = numIncorrectRes.begin(); it != numIncorrectRes.end(); ++it)
    {
      std::cout << "    Total #incorrect[" << it->first << "] : " << it->second
          << std::endl;
    }
    if (numIncorrectUndef > 0)
    {
      std::cout << "Total #incorrect[undef] : " << numIncorrectUndef << std::endl;
    }
    std::cout << "           Total #tests : " << numTests << std::endl;
    if (numTests > 0)
    {
      std::cout << "              % correct : "
          << 1.0 - (double(numIncorrect) / double(numTests)) << std::endl;
    }
    if( numIncorrect==0 )
    {
      std::cout << "----> FULLY VERIFIED!!!" << std::endl;
    }
  }

  
  return 0;
}
