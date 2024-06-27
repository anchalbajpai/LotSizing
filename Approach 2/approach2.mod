/*********************************************
 * OPL 22.1.1.0 Model
 * Author: bajpa
 * Creation Date: 1 Apr 2024 at 18:15:39
 *********************************************/
int no_of_periods = ...;              			// time_periods
range time_periods = 1..no_of_periods;          
int P = ...;              						// no. of products
range products = 1..P;           
float r[products][time_periods] = ...;      // r[j][t] = sales revenue for one unit of product j in period t
int Ld[products][time_periods] = ...;       // Ld[j][t] = lower bound of demand of product j in period t
int Ud[products][time_periods] = ...;       // Ud[j][t] = upper bound of demand of product j in period t
int I0[products] = ...;          // I0[j] = initial inventory level for product j
int C[time_periods] = ...;           // C[t] = available capacity in each period
float Cp[products] = ...;        // Cp[j] = Production cost for one unit of product j
float Pt[products] = ...;        // Pt[j] = processing time_periods for one unit of product j
float h[products] = ...;         // h[j] = holding cost for one unit of product j
int s[products][products] = ...;        // s[i][j] = setup cost for transition from product i to product j
float St[products][products] = ...;     // St[i][j] = setup time_periods for transition from product i to product j
dvar int+ Q[products][0..no_of_periods][time_periods]; // Q[j][t][k] = production quantity of product j in period t to fulfil the demand of period k.
dvar int+ D[products][time_periods];       // D[j][t] = the accepted demand of product j in period t.
dvar int+ A[products][time_periods];       // A[j][t] = positive variable which is 1 when machine is setup for product j at the beginning of period t.
dvar int+ Y[products][time_periods];       // Y[j][t] = auxiliary variable that assign product j to period t.
dvar boolean X[products][products][time_periods];  // X[i][j][t] = Binary variable which is 1 when setup occur from product i to product j in period t.
dvar float+ M[products][time_periods][time_periods];
dvar float+ CQ[products][0..no_of_periods];//CQ[j][t] is a **parameter** which combines production cost and inventory cost of product j which will be used t periods after production period.
dvar float+ R0[products]; // R0[j] = unused portion of initial inventory of product j at the end of the planning horizon



dexpr float z = sum(j in products, t in time_periods) r[j][t] * D[j][t] - sum(j in products, t in time_periods, k in t..no_of_periods) CQ[j][k - t] * Q[j][t][k] 
-sum(j in products, i in products, t in time_periods) s[i][j] * X[i][j][t] - sum(j in products, t in time_periods) Q[j][0][t] * h[j] * (t - 1)
-sum(j in products) no_of_periods * h[j] * R0[j];
//The objective function of the model is to maximize total revenue minus production
//and inventory cost of production quantities in different periods, setup costs,
//initial inventory holding cost until the period which is used, and the unused 
//initial inventory holding cost.
maximize z;

subject to
{
  	
  	Constraint_1:
	//Constraint to show that the accepted demand in period t is fulfilled by productions for this period or initial inventory.
    forall(k in time_periods, j in products)
    {		
    		sum(t in 0..k) 
            Q[j][t][k] == D[j][k];
    }
    
    
	Constraint_2:
    forall(j in products, t in time_periods) D[j][t] <= Ud[j][t];	//Upper Bound of demand.
	
    forall(j in products, t in time_periods) D[j][t] >= Ld[j][t];	//Lower Bound of demand.
	
	Constraint_3://ensures that the initial inventory is equal to the sum of initial inventory which is used in different periods and the unused portion of initial inventory 
	//at the end of the planning horizon.
    
    forall(j in products) sum(t in time_periods) Q[j][0][t] + R0[j]== I0[j] ;
	
	
	
	Constraint_4://guarantees that the machine is setup for production, and the production’s upper bound is not exceeded
    forall(j in products, t in time_periods, k in t..no_of_periods)
    {
		Q[j][t][k] <= M[j][t][k] * (sum(i in products) X[i][j][t] + A[j][t]);
	}	
	
	forall(j in products, t in time_periods, k in t..no_of_periods) 
    if (C[t] / Pt[j] < Ud[j][t]) 
    {
    	M[j][t][k] == C[t] / Pt[j];
  	}    
    else
    {
        M[j][t][k] == Ud[j][k];
    }
    
    	
	Constraint_5://shows the capacity limit for production
    forall(t in time_periods) sum(j in products, k in t..no_of_periods) Pt[j] * Q[j][t][k] + sum(i in products, j in products) St[i][j] * X[i][j][t] <= C[t];

   
	Contraint_6://defines the sequence of products
	forall(t in time_periods) sum(j in products) A[j][t] == 1;


	Constraint_7://setup state change in each period
    forall(j in products, t in 1..(no_of_periods-1))
    { 
   
    	A[j][t] + sum(i in products) X[i][j][t] == A[j][t + 1] + sum(i in products) X[j][i][t]; 
    
    }


	Constraint_8://setup transmission between two sequential periods
    forall(i in products, j in products, t in time_periods: i!=j)
    { 
  		Y[i][t] + P*X[i][j][t] - (P - 1) - P *A[i][t] <= Y[j][t]; 
    }
    
    
	//not a constraint, helps calculate CQ[j][t] 
    forall(j in products, t in 0..no_of_periods) 
    {
      CQ[j][t] == Cp[j] + t*h[j];
    }
}
