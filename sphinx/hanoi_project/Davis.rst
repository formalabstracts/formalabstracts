* This is a bulleted list.
* It has two items, the second
  item uses two lines.

1. This is a numbered list.
2. It has two items too.

#. This is a numbered list.
#. It has two items too.

+------------------------+------------+----------+----------+
| Header row, column 1   | Header 2   | Header 3 | Header 4 |
| (header rows optional) |            |          |          |
+========================+============+==========+==========+
| body row 1, column 1   | column 2   | column 3 | column 4 |
+------------------------+------------+----------+----------+
| body row 2             | ...        | ...      |          |
+------------------------+------------+----------+----------+

.. code-block:: c++

    #include <iostream>
    using namespace std;
    #include <math.h>
    #define FOR(i,a,b) for (int i=(a),_b=(b);i<=_b;i++)
    #define FORD(i,b,a) for (int i=(b),_a=(a);i>=_a;i--)
    #define REP(i,n) for (int i=0,_n=(n);i<_n;i++)
    #define DEBUG 1
    #define IS_EVEN(n,m) (n % m ==0 ? 1:0)
    #define max(n,m) (n > m ? n:m)
    #define min(n,m) (n < m ? n:m)
    #define cerr(mess,X) { cout << mess << #X << " = " << (X) << endl; }

    int main()
    {
        int i,n;
        cin>>n;
        int tong = 0;
        bool flag = false;
        FOR(i,2,int(sqrt(n))+1)
        {
            if(IS_EVEN(n,i))
            {
                flag = true;
                #if DEBUG
                    cerr("dont pass ",i)
                #endif 
                break;
            }else
            {
                #if DEBUG
                    cerr("pass ",i)
                #endif 
            }
            
                
        }
        if (!flag)
        {
            cout<<"This is a prime number"<<endl;
        }
        return 0;
    }

