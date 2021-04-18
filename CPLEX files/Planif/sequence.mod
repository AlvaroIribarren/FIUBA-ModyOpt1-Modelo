//CONSTANTES

 {string} i = ...;
 {string} j = ...;
 {string} n = ...;
 {string} k = ...;
 int Costo[n] = ...;
 
 //VARIABLES
 dvar int+ E[j];
 dvar int+ Emp[i,j];
 dvar int+ ER[i,j];
 dvar int+ ENR[i,j];
 dvar int+ U[i,j];
 dvar int+ EmpT[i,j,i,j];
 
 dvar boolean P[n,i,j];
 dvar boolean Persona[n,j];
 dvar int+ Pp[n];
 dvar int+ Cp[k,i,j];
 dvar boolean Y[k,i,j];
 dvar boolean YP[n, i, j, i, j];
 
 
 //OBJETIVO
 
 minimize  sum(empleado in n) Pp[empleado] * Costo[empleado];
 
 //MODELO
 
 subject to{
   
   //Cantidad mínima de unidades a realizar por día.
 	U["R","L"] >= 2200;
	U["R","W"] >= 2600;
	U["P","L"] >= 1000;
	U["P","M"] >= 1200;
	U["P","W"] >= 1112;
	U["C","L"] >= 1624;
	U["C","M"] >= 3200;
	U["C","W"] >= 1664;

	 
	//Disponibilidad máxima de empleados por día.
	E["L"] == Emp["R","L"] + Emp["P","L"] + Emp["C","L"];
	E["L"] <= 20;
	E["M"] == Emp["R","M"] + Emp["P","M"] + Emp["C","M"];
	E["M"] <= 20;

	
	E["W"] == Emp["R","W"] + Emp["P","W"] + Emp["C","W"];	
	E["W"] <= 20;
	
	//Los martes no se trabaja en la tarea R
	Emp["R","M"] == 0;
	ER["R", "M" ] == 0;
	ENR["R", "M" ] == 0;

	//Relación empleados eficientes-ineficientes el lunes
	Emp["R","L"] == ER["R","L"];        
	ENR["R","L"] == 0;
	
	Emp["P","L"] == ER["P","L"];        
	ENR["P","L"] == 0;

	Emp["C","L"] == ER["C","L"];        
	ENR["C","L"] == 0;

	//Relación empleados eficientes-ineficientes martes y miércoles
	Emp["P","M"] == ER["P","M"] + ENR["P","M"];
	Emp["C","M"] == ER["C","M"] + ENR["C","M"];
	Emp["R","W"] == ER["R","W"] + ENR["R","W"];
	Emp["P","W"] == ER["P","W"] + ENR["P","W"];
	Emp["C","W"] == ER["C","W"] + ENR["C","W"];

	//Relación producción del día y empleados
	//Lunes
	U["R","L"] == 1.1 * Emp["R","L"] * 800;
	U["P","L"] == 1.1 * Emp["P","L"] * 160;
	U["C","L"] == 1.1 * Emp["C","L"] * 480;

	//Martes
	U["P","M"] == 160 * (1.1 * ER["P","M"] + ENR["P","M"]);
	U["C","M"] == 480 * (1.1 * ER["C","M"] + ENR["C","M"]);	

	//Miércoles
	U["R","W"] == 800 * (1.1 * ER["R","W"] + ENR["R","W"]);
	U["P","W"] == 160 * (1.1 * ER["P","W"] + ENR["P","W"]);
	U["C","W"] == 480 * (1.1 * ER["C","W"] + ENR["C","W"]);
	
	//Producción nula los dias que no se trabaja
	U["N","L"] == 0;
	U["N","M"] == 0;
	U["N","W"] == 0;	
	U["R","M"] == 0;
	
	//Relación entre la tarea realizada en un día con el siguiente. 
	//(Declaro YP y E con ambas tareas en ambos días)
	
	forall(emp in n) {
	//PM, vienen del lunes
	  	forall(tarea in i){
	  		2 * YP [emp, tarea, "L", "P", "M"] <= P[emp, tarea, "L"] + P[emp, "P", "M"];
			P[emp, tarea, "L"] + P[emp, "P", "M"] <= 1 + YP [emp, tarea, "L", "P", "M"];
	  	}
	//CM, vienen del lunes
		forall(tarea in i){
	  		2 * YP [emp, tarea, "L", "C", "M"] <= P[emp, tarea, "L"] + P[emp, "C", "M"];
			P[emp, tarea, "L"] + P[emp, "C", "M"] <= 1 + YP [emp, tarea, "L", "C", "M"];
	  	}
	//RW, vienen del martes
		 forall(tarea in i){
	  		2 * YP [emp, tarea, "M", "R", "W"] <= P[emp, tarea, "M"] + P[emp, "R", "W"];
			P[emp, tarea, "M"] + P[emp, "R", "W"] <= 1 + YP [emp, tarea, "M", "R", "W"];
	  	}
	//PW, vienen del martes
		 forall(tarea in i){
	  		2 * YP [emp, tarea, "M", "P", "W"] <= P[emp, tarea, "M"] + P[emp, "P", "W"];
			P[emp, tarea, "M"] + P[emp, "P", "W"] <= 1 + YP [emp, tarea, "M", "P", "W"];
	  	}
	//CW, vienen del martes
		 forall(tarea in i){
	  		2 * YP [emp, tarea, "M", "P", "M"] <= P[emp, tarea, "M"] + P[emp, "P", "W"];
			P[emp, tarea, "M"] + P[emp, "P", "M"] <= 1 + YP[emp, tarea, "M", "P", "W"];
	  	}
	}
	
	
	//Relación entre las rotaciones y la cantidad
	//PM
	forall(tarea in i){
		EmpT[tarea,"L", "P", "M"] ==  sum(emp in n) YP[emp, tarea, "L", "P", "M"];
	}
	//CM, vienen del lunes
	forall(tarea in i){
		EmpT[tarea,"L", "C", "M"] ==  sum(emp in n) YP[emp, tarea, "L", "C", "M"];
	}
	//RW, vienen del martes
	forall(tarea in i){
		EmpT[tarea,"M", "P", "M"] ==  sum(emp in n) YP[emp, tarea, "M", "R", "W"];
	}
	//PW, vienen del martes
	forall(tarea in i){
		EmpT[tarea, "M", "P", "W"] ==  sum(emp in n) YP[emp, tarea, "M", "P", "W"];
	}
	//CW, vienen del martes
	forall(tarea in i){
		EmpT[tarea, "M", "C", "W"] ==  sum(emp in n) YP[emp, tarea, "M", "C", "W"];
	}
	
	
	//Los que no trabajan en la tarea R el día martes no toman distinción entrte rotados y no rotados
	Emp["R", "M"] == ER["R", "M"] == ENR["R", "M"] == 0;
	
	//Los que no trabajan no toman distinción entre rotados y no rotados.
	Emp["N", "L"] == ER["N", "L"] == ENR["N", "L"];
	Emp["N", "M"] == ER["N", "M"] == ENR["N", "M"];
	Emp["N", "W"] == ER["N", "W"] == ENR["N", "W"];
	
	//Relación cantidad empleados por día
	E["L"] + Emp["N","L"] == 20;
	E["M"] + Emp["N","M"] == 20;
	E["W"] + Emp["N","W"] == 20;
	
	
	//Relación entre empleados a trabajar en una tarea en un cierto día con la tarea que realizaron antes. Primero los rotados
	
	//Lunes, directamente son los que trabajaron ese dia
	ER["R","L"] == sum(emp in n) (P[emp, "R", "L"]);
	ER["P","L"] == sum(emp in n) (P[emp, "P", "L"]);
	ER["C","L"] == sum(emp in n) (P[emp, "C", "L"]);
	
	
	//Martes 
	ER["P","M"] == EmpT["R","L","P","M"] + EmpT["C","L","P","M"] + EmpT["N","L","P","M"];
	ER["C","M"] == EmpT["R","L","C","M"] + EmpT["P","L","C","M"] + EmpT["N","L","C","M"];

	//Miércoles
	ER["R","W"] == EmpT["P","M","R","W"] + EmpT["C","M","R","W"] + EmpT["N","M","R","W"];
	ER["P","W"] == EmpT["C","M","P","W"] + EmpT["N","M","P","W"];
	ER["C","W"] == EmpT["P","M","C","W"] + EmpT["N","M","C","W"];

	//No rotados
	//Martes	
	ENR["P","M"] == EmpT["P","L","P","M"];
	ENR["C","M"] == EmpT["C","L","C","M"];	

	//Miércoles
	ENR["R","W"] == 0;
	ENR["P","W"] == EmpT["P","M","P","W"];
	ENR["C","W"] == EmpT["C","M","C","W"];
	
	//Grupos
	//Cada día no pueden trabajar más de 20 empleados.
	forall(dia in j){
	  MaxEmpleadosPorDia : sum(emp in n, trabajo in i) P[emp,trabajo,dia] <= 20;
	  }

	//Relación entre cantidad de cada carácter con las personas
	//Lunes	
	Cp["1","R","L"] == P["1","R","L"] + P["5","R","L"] + P["9","R","L"] + P["13","R","L"] + P["17","R","L"]; 
	Cp["2","R","L"] == P["2","R","L"] + P["6","R","L"] + P["10","R","L"] + P["14","R","L"] + P["18","R","L"]; 	
	Cp["3","R","L"] == P["3","R","L"] + P["7","R","L"] + P["11","R","L"] + P["15","R","L"] + P["19","R","L"]; 
	Cp["4","R","L"] == P["4","R","L"] + P["8","R","L"] + P["12","R","L"] + P["16","R","L"] + P["20","R","L"]; 

	Y["1","R","L"] <= Cp["1","R","L"];
	Cp["1","R","L"] <= 5 * Y["1","R","L"]; 
	Y["2","R","L"] <= Cp["2","R","L"]; 
	Cp["2","R","L"] <= 5 * Y["2","R","L"];
	Y["3","R","L"] <= Cp["3","R","L"];
	Cp["3","R","L"] <= 5 * Y["3","R","L"];
	Y["4","R","L"] <= Cp["4","R","L"];
	Cp["4","R","L"] <= 5 * Y["4","R","L"];

	Cp["1","P","L"] == P["1","P","L"] + P["5","P","L"] + P["9","P","L"] + P["13","P","L"] + P["17","P","L"]; 
	Cp["2","P","L"] == P["2","P","L"] + P["6","P","L"] + P["10","P","L"] + P["14","P","L"] + P["18","P","L"]; 	
	Cp["3","P","L"] == P["3","P","L"] + P["7","P","L"] + P["11","P","L"] + P["15","P","L"] + P["19","P","L"]; 
	Cp["4","P","L"] == P["4","P","L"] + P["8","P","L"] + P["12","P","L"] + P["16","P","L"] + P["20","P","L"]; 

	Y["1","P","L"] <= Cp["1","P","L"];
	Cp["1","P","L"] <= 5 * Y["1","P","L"]; 
	Y["2","P","L"] <= Cp["2","P","L"]; 
	Cp["2","P","L"] <= 5 * Y["2","P","L"];
	Y["3","P","L"] <= Cp["3","P","L"];
	Cp["3","P","L"] <= 5 * Y["3","P","L"];
	Y["4","P","L"] <= Cp["4","P","L"];
	Cp["4","P","L"] <= 5 * Y["4","P","L"];
	
	
	Cp["1","C","L"] == P["1","C","L"] + P["5","C","L"] + P["9","C","L"] + P["13","C","L"] + P["17","C","L"]; 
	Cp["2","C","L"] == P["2","C","L"] + P["6","C","L"] + P["10","C","L"] + P["14","C","L"] + P["18","C","L"]; 	
	Cp["3","C","L"] == P["3","C","L"] + P["7","C","L"] + P["11","C","L"] + P["15","C","L"] + P["19","C","L"]; 
	Cp["4","C","L"] == P["4","C","L"] + P["8","C","L"] + P["12","C","L"] + P["16","C","L"] + P["20","C","L"]; 

	Y["1","C","L"] <= Cp["1","C","L"];
	Cp["1","C","L"] <= 5 * Y["1","C","L"]; 
	Y["2","C","L"] <= Cp["2","C","L"]; 
	Cp["2","C","L"] <= 5 * Y["2","C","L"];
	Y["3","C","L"] <= Cp["3","C","L"];
	Cp["3","C","L"] <= 5 * Y["3","C","L"];
	Y["4","C","L"] <= Cp["4","C","L"];
	Cp["4","C","L"] <= 5 * Y["4","C","L"];
	
	//Martes

	Cp["1","C","M"] == P["1","C","M"] + P["5","C","M"] + P["9","C","M"] + P["13","C","M"] + P["17","C","M"]; 
	Cp["2","C","M"] == P["2","C","M"] + P["6","C","M"] + P["10","C","M"] + P["14","C","M"] + P["18","C","M"]; 	
	Cp["3","C","M"] == P["3","C","M"] + P["7","C","M"] + P["11","C","M"] + P["15","C","M"] + P["19","C","M"]; 
	Cp["4","C","M"] == P["4","C","M"] + P["8","C","M"] + P["12","C","M"] + P["16","C","M"] + P["20","C","M"]; 

	Y["1","C","M"] <= Cp["1","C","M"];
	Cp["1","C","M"] <= 5 * Y["1","C","M"]; 
	Y["2","C","M"] <= Cp["2","C","M"]; 
	Cp["2","C","M"] <= 5 * Y["2","C","M"];
	Y["3","C","M"] <= Cp["3","C","M"];
	Cp["3","C","M"] <= 5 * Y["3","C","M"];
	Y["4","C","M"] <= Cp["4","C","M"];
	Cp["4","C","M"] <= 5 * Y["4","C","M"];

	Cp["1","P","M"] == P["1","P","M"] + P["5","P","M"] + P["9","P","M"] + P["13","P","M"] + P["17","P","M"]; 
	Cp["2","P","M"] == P["2","P","M"] + P["6","P","M"] + P["10","P","M"] + P["14","P","M"] + P["18","P","M"]; 	
	Cp["3","P","M"] == P["3","P","M"] + P["7","P","M"] + P["11","P","M"] + P["15","P","M"] + P["19","P","M"]; 
	Cp["4","P","M"] == P["4","P","M"] + P["8","P","M"] + P["12","P","M"] + P["16","P","M"] + P["20","P","M"]; 

	Y["1","P","M"] <= Cp["1","P","M"];
	Cp["1","P","M"] <= 5 * Y["1","P","M"]; 
	Y["2","P","M"] <= Cp["2","P","M"]; 
	Cp["2","P","M"] <= 5 * Y["2","P","M"];
	Y["3","P","M"] <= Cp["3","P","M"];
	Cp["3","P","M"] <= 5 * Y["3","P","M"];
	Y["4","P","M"] <= Cp["4","P","M"];
	Cp["4","P","M"] <= 5 * Y["4","P","M"];

	//Miércoles
	Cp["1","R","W"] == P["1","R","W"] + P["5","R","W"] + P["9","R","W"] + P["13","R","W"] + P["17","R","W"]; 
	Cp["2","R","W"] == P["2","R","W"] + P["6","R","W"] + P["10","R","W"] + P["14","R","W"] + P["18","R","W"]; 	
	Cp["3","R","W"] == P["3","R","W"] + P["7","R","W"] + P["11","R","W"] + P["15","R","W"] + P["19","R","W"]; 
	Cp["4","R","W"] == P["4","R","W"] + P["8","R","W"] + P["12","R","W"] + P["16","R","W"] + P["20","R","W"]; 

	Y["1","R","W"] <= Cp["1","R","W"];
	Cp["1","R","W"] <= 5 * Y["1","R","W"]; 
	Y["2","R","W"] <= Cp["2","R","W"]; 
	Cp["2","R","W"] <= 5 * Y["2","R","W"];
	Y["3","R","W"] <= Cp["3","R","W"];
	Cp["3","R","W"] <= 5 * Y["3","R","W"];
	Y["4","R","W"] <= Cp["4","R","W"];
	Cp["4","R","W"] <= 5 * Y["4","R","W"];
	
	Cp["1","P","W"] == P["1","P","W"] + P["5","P","W"] + P["9","P","W"] + P["13","P","W"] + P["17","P","W"]; 
	Cp["2","P","W"] == P["2","P","W"] + P["6","P","W"] + P["10","P","W"] + P["14","P","W"] + P["18","P","W"]; 	
	Cp["3","P","W"] == P["3","P","W"] + P["7","P","W"] + P["11","P","W"] + P["15","P","W"] + P["19","P","W"]; 
	Cp["4","P","W"] == P["4","P","W"] + P["8","P","W"] + P["12","P","W"] + P["16","P","W"] + P["20","P","W"]; 

	Y["1","P","W"] <= Cp["1","P","W"];
	Cp["1","P","W"] <= 5 * Y["1","P","W"]; 
	Y["2","P","W"] <= Cp["2","P","W"]; 
	Cp["2","P","W"] <= 5 * Y["2","P","W"];
	Y["3","P","W"] <= Cp["3","P","W"];
	Cp["3","P","W"] <= 5 * Y["3","P","W"];
	Y["4","P","W"] <= Cp["4","P","W"];
	Cp["4","P","W"] <= 5 * Y["4","P","W"];

	Cp["1","C","W"] == P["1","C","W"] + P["5","C","W"] + P["9","C","W"] + P["13","C","W"] + P["17","C","W"]; 
	Cp["2","C","W"] == P["2","C","W"] + P["6","C","W"] + P["10","C","W"] + P["14","C","W"] + P["18","C","W"]; 	
	Cp["3","C","W"] == P["3","C","W"] + P["7","C","W"] + P["11","C","W"] + P["15","C","W"] + P["19","C","W"]; 
	Cp["4","C","W"] == P["4","C","W"] + P["8","C","W"] + P["12","C","W"] + P["16","C","W"] + P["20","C","W"]; 

	Y["1","C","W"] <= Cp["1","C","W"];
	Cp["1","C","W"] <= 5 * Y["1","C","W"]; 
	Y["2","C","W"] <= Cp["2","C","W"]; 
	Cp["2","C","W"] <= 5 * Y["2","C","W"];
	Y["3","C","W"] <= Cp["3","C","W"];
	Cp["3","C","W"] <= 5 * Y["3","C","W"];
	Y["4","C","W"] <= Cp["4","C","W"];
	Cp["4","C","W"] <= 5 * Y["4","C","W"];

	//Personalidades conflictivas no pueden trabajar juntos en ninguna tarea y en ningún día.
	//1 y 20
	//Lunes
	P["1","R","L"] + P["20","R","L"] <= 1;
	P["1","P","L"] + P["20","P","L"] <= 1;	
	P["1","C","L"] + P["20","C","L"] <= 1;
	//Martes
	P["1","P","M"] + P["20","P","M"] <= 1;
	P["1","C","M"] + P["20","C","M"] <= 1;
	//Miércoles
	P["1","R","W"] + P["20","R","W"] <= 1;
	P["1","P","W"] + P["20","P","W"] <= 1;
	P["1","C","W"] + P["20","C","W"] <= 1;
	//3 y 6
	//Lunes
	P["3","R","L"] + P["6","R","L"] <= 1;
	P["3","P","L"] + P["6","P","L"] <= 1;
	P["3","C","L"] + P["6","C","L"] <= 1;
	//Martes
	P["3","P","M"] + P["6","P","M"] <= 1;
	P["3","C","M"] + P["6","C","M"] <= 1;
	//Miércoles
	P["3","R","W"] + P["6","R","W"] <= 1;
	P["3","P","W"] + P["6","P","W"] <= 1;
	P["3","C","W"] + P["6","C","W"] <= 1;
	
	//9 y 10
	//Lunes
	P["9","R","L"] + P["10","R","L"] <= 1;
	P["9","P","L"] + P["10","P","L"] <= 1;
	P["9","C","L"] + P["10","C","L"] <= 1;
	//Martes
	P["9","P","M"] + P["10","P","M"] <= 1;
	P["9","C","M"] + P["10","C","M"] <= 1;
	//Miércoles
	P["9","R","W"] + P["10","R","W"] <= 1;
	P["9","P","W"] + P["10","P","W"] <= 1;
	P["9","C","W"] + P["10","C","W"] <= 1;

	//Cada día debe haber un empleado de cada categoría
	//Categoría 1
	Cp["1","R","L"] + Cp["1","P","L"] + Cp["1","C","L"] >= 1;
	Cp["1","P","M"] + Cp["1","C","M"] >= 1;	
	Cp["1","R","W"] + Cp["1","P","W"] + Cp["1","C","W"] >= 1;
	
	//Categoría 2
	Cp["2","R","L"] + Cp["2","P","L"] + Cp["2","C","L"] >= 1;
	Cp["2","P","M"] + Cp["2","C","M"] >= 1;	
	Cp["2","R","W"] + Cp["2","P","W"] + Cp["2","C","W"] >= 1;

	//Categoría 3
	Cp["3","R","L"] + Cp["3","P","L"] + Cp["3","C","L"] >= 1;
	Cp["3","P","M"] + Cp["3","C","M"] >= 1;	
	Cp["3","R","W"] + Cp["3","P","W"] + Cp["3","C","W"] >= 1;

	//Categoría 4
	Cp["4","R","L"] + Cp["4","P","L"] + Cp["4","C","L"] >= 1;
	Cp["4","P","M"] + Cp["4","C","M"] >= 1;	
	Cp["4","R","W"] + Cp["4","P","W"] + Cp["4","C","W"] >= 1;
	

	//Persona solo realiza una tarea por día
	forall(empleado in n){
	  UnicaTareaLunes : Persona[empleado,"L"] == P[empleado,"R","L"] + P[empleado,"P","L"] + P[empleado,"C","L"];
	  Persona[empleado, "L"] <= 1;
	}

	forall(empleado in n){
	  UnicaTareaMartes : Persona[empleado,"M"] == P[empleado,"R","M"] + P[empleado,"P","M"] + P[empleado,"C","M"];
	  Persona[empleado, "M"] <= 1;
	}
	  
	forall(empleado in n){
	  UnicaTareaMiercoles : Persona[empleado,"W"] == P[empleado,"R","W"] + P[empleado,"P","W"] + P[empleado,"C","W"];
	  Persona[empleado, "W"] <= 1;
	}
	
	//Persona tiene que realizar una tarea en el día o no laburar.
	forall(empleado in n){
	  forall(dia in j) {
	    Persona[empleado, dia] + P[empleado, "N", dia] == 1;
	  } 
 	}
	
	//Cantidad de veces que el empleado n trabajó en el período.
	forall(empleado in n){
	  CantidadDeTrabajoEmpleado : Pp[empleado] == Persona[empleado,"L"] + Persona[empleado,"M"] + Persona[empleado, "W"];
	}
	
	//Relación entre la cantidad de empleados y las personas
	E["L"] == sum(emp in n) Persona[emp, "L"];
	E["M"] == sum(emp in n) Persona[emp, "M"];
	E["W"] == sum(emp in n) Persona[emp, "W"];
}
  