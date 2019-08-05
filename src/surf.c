/* FILE : surf.c
 * Descr: ...
*/

#include <stdio.h>
#include <math.h>
#include <stdlib.h>
#include <time.h>
#define	TP	6.283185308
#define Nt 200   //без нулевых точек
#define Nth 200
#define tmin 0.02
#define tmax 0.97
#define thetamin 0.0
#define thetamax 1.57079632
#define m 4

void 	som_init(complex double epscf);
static inline void SingleSomIntegral(double krho, const double kz, double complex vals[static 4]);

static void fillZero(FILE *fd);
static void Transform(double complex vals[static 4], double krho, double kz, double q, double t, complex double eps, unsigned char f);
static void CalcPreTable();
static void OnePoly(double x0, double x[m], complex double S1[m], complex double S0[1]);
static void PolyInt(double x0, double y0, double * x, double * y, complex double * S, double complex vals[static 4]);
static void InterpolSomVal(double krho, double kz, double complex vals[static 4]);
static void FindError(int M);

static double ht = (tmax - tmin) / (Nt - 1);
static double hth = (thetamax - thetamin) / (Nth - 1);
static double ABS[4];
static double ABSm[4];
static complex double * preTable; //interpolation table, filled in CalcPreTable


static void fillZero(FILE *fd){
	int j;
	complex double g = (eps - 1) / (eps + 1);
	double theta = thetamin;
	complex double Cos, Sin, Svr, Svz, Shr, Shp;
	complex double s, L, Z1, Z2, C1, C2, S2vz, S2hr, S2hp;
	complex double Rs, Rp, fvr, fvz, fhr, fhp;
	
	for(j = 0; j < Nth; j++){
		Sin = sin(theta);
		Cos = cos(theta);
		Rs = (Cos - csqrt(eps - Sin*Sin)) / (Cos + csqrt(eps - Sin*Sin));
		Rp = (eps * Cos - csqrt(eps - Sin*Sin)) / (eps * Cos + csqrt(eps - Sin*Sin));
		fvr = (- Rp + g)*Sin*Cos;
		fvz = (Rp - g)*Sin*Sin;
		fhr = (- Rp + g)*Cos*Cos;
		fhp = - (g + Rs);	
	
		s = csqrt(eps + 1.0);
		L = (eps / ((eps - 1.0) * s)) * clog((1.0 + s) / (eps + s * csqrt(eps)));
		Z1 = 1.0 / ((eps + 1.0)*(eps + 1.0));
		Z2 = 1.0 / (3 * (csqrt(eps) + 1.0));
		C1 = 1.0 - 3 * csqrt(eps) + 3 * eps + 2 * eps*eps;
		C2 = 1.0 + 2 * eps - eps*eps*eps + csqrt(eps) * (1.0 + 2 * eps - 2 * eps*eps);
	
		S2vz = - 2j * (g / 3 + Z1 * (C2 * Z2 + L * eps*eps));
		S2hr = 1j * (2 * g / 3 + eps * Z1 * (C1 * Z2 + L));
		S2hp = -1j * (2 * g / 3 + eps * Z1 * (C1 * Z2 + L));
		
		preTable[j*4] = - 1j * fvr;
		preTable[j*4 + 1] = S2vz - 1j * fvz;
		preTable[j*4 + 2] = S2hr - 1j * fhr;
		preTable[j*4 + 3] = S2hp - 1j * fhp;
		fprintf(fd, "%.5e %.5e %.5e %.5e %.5e %.5e %.5e %.5e %.5e %.5e %.5e %.5e %.5e\r\n", 0.0, 0.0, creal(preTable[j*4]), cimag(preTable[j*4]), creal(preTable[j*4 + 1]), cimag(preTable[j*4 + 1]), creal(preTable[j*4 + 2]), cimag(preTable[j*4 + 2]), creal(preTable[j*4 + 3]), cimag(preTable[j*4 + 3]), 0.0, theta, 0.0);
		theta += hth;
	}
	
}	

static void Transform(double complex vals[static 4], double krho, double kz, double q, double t, complex double eps, unsigned char f){     //f = 0 - преобразуем интегралы, f = 1 - преобразуем обратно
	complex double g = (eps - 1) / (eps + 1);
	double Sin = krho / q;
	double Cos = kz / q;
	complex double Rs = (Cos - csqrt(eps - Sin*Sin)) / (Cos + csqrt(eps - Sin*Sin));
	complex double Rp = (eps * Cos - csqrt(eps - Sin*Sin)) / (eps * Cos + csqrt(eps - Sin*Sin));

	complex double fvr = (- Rp + g)*Sin*Cos;
	complex double fvz = (Rp - g)*Sin*Sin;
	complex double fhr = (- Rp + g)*Cos*Cos;
	complex double fhp = - (g + Rs);

	complex double Svr = g * (eps/(eps + 1)) * (Sin / (1 + Cos));
	complex double Svz = g * eps / (eps + 1);
	complex double Shr = g * (1 - Cos / ((eps + 1) * (1 + Cos)));
	complex double Shp = - g * (eps / (eps + 1) + Cos / ((eps + 1) * (1 + Cos)));	
	double QQ = (q*q + 1) / q;
	
	if (f == 0){
		vals[0] = (vals[0] * q * cexp(- 1j*q) - (Svr + 1j * fvr * q) / (1 + 1j * q)) * QQ;
		vals[1] = (vals[1] * q * cexp(- 1j*q) - (Svz + 1j * fvz * q) / (1 + 1j * q)) * QQ;
		vals[2] = (vals[2] * q * cexp(- 1j*q) - (Shr + 1j * fhr * q) / (1 + 1j * q)) * QQ;
		vals[3] = (vals[3] * q * cexp(- 1j*q) - (Shp + 1j * fhp * q) / (1 + 1j * q)) * QQ;			
	}
	if (f == 1){	
		vals[0] = ((vals[0] / QQ) + (Svr + 1j * fvr * q) / (1 + 1j * q)) * cexp(1j*q) / q;
		vals[1] = ((vals[1] / QQ) + (Svz + 1j * fvz * q) / (1 + 1j * q)) * cexp(1j*q) / q;
		vals[2] = ((vals[2] / QQ) + (Shr + 1j * fhr * q) / (1 + 1j * q)) * cexp(1j*q) / q;
		vals[3] = ((vals[3] / QQ) + (Shp + 1j * fhp * q) / (1 + 1j * q)) * cexp(1j*q) / q;
	}	
}

static void CalcPreTable(){
	int i, j, l;
	double t = tmin;
	double theta = thetamin;
	double krho, kz, q;
	FILE *fd = fopen("preTable.txt", "wb");
	preTable = (complex double *)malloc(sizeof(complex double)*4*(Nt+1)*Nth);
	fillZero(fd);
	for (i = 0; i < 4; i++){
		ABS[i] = 0;
	}
	for(i = 1; i <= Nt; i++){
		for(j = 0; j < Nth; j++){
			q = t / (1 - t);
			kz = q / sqrt(1 + tan(theta)*tan(theta));
			krho = kz * tan(theta);
			SingleSomIntegral(krho, kz, preTable + i*Nth*4 + j*4);
			Transform(preTable + i*Nth*4 + j*4, krho, kz, q, t, eps, 0);
			fprintf(fd, "%.5e %.5e %.5e %.5e %.5e %.5e %.5e %.5e %.5e %.5e %.5e %.5e %.5e\r\n", krho, kz, creal(preTable[i*Nth*4 + j*4]), cimag(preTable[i*Nth*4 + j*4]), creal(preTable[i*Nth*4 + j*4 + 1]), cimag(preTable[i*Nth*4 + j*4 + 1]), creal(preTable[i*Nth*4 + j*4 + 2]), cimag(preTable[i*Nth*4 + j*4 + 2]), creal(preTable[i*Nth*4 + j*4 + 3]), cimag(preTable[i*Nth*4 + j*4 + 3]), q, theta, t);
			for (l = 0; l < 4; l++){
			ABS[l] += cabs(preTable[i*Nth*4 + j*4 + l]);
			}
			theta += hth;
		}
		theta = thetamin;
		t += ht;
	}
	for (i = 0; i < 4; i++){
		ABS[i] = ABS[i] / (Nt * Nth);
	}
	fclose(fd);
}

static void OnePoly(double x0, double x[m], complex double S1[m], complex double S0[1]){
	complex double A[m][m], P;
	int i, j, k;
	for (i = 0; i < m; i++){
		for (j = 0; j < m; j++){
			A[i][j] = 0;
		}
	}
	for (i = 0; i < m; i++){
		A[i][0] = S1[i];
	}
	for (k = 1; k < m; k++){
		for (i = 0; i < m - k; i++){
			A[i][k] = (A[i][k - 1] - A[i + 1][k - 1]) / (x[i] - x[i + k]);
		}
	}
	P = A[0][m - 1];
	for (j = m - 2; j >= 0; j--){
		P = P * (x0 - x[j]) + A[0][j];
	}
	S0[0] = P;
}

static void PolyInt(double x0, double y0, double * x, double * y, complex double * S, double complex vals[static 4]){
	complex double * S0;
	S0 = (complex double *)malloc(sizeof(complex double)*m*4);
	int i;
	for(i = 0; i < m; i++){
		OnePoly(y0, y, S + i*m*4, S0 + i);
		OnePoly(y0, y, S + i*m*4 + m, S0 + i + m);
		OnePoly(y0, y, S + i*m*4 + 2*m, S0 + i + 2*m);
		OnePoly(y0, y, S + i*m*4 + 3*m, S0 + i + 3*m);
	}
	OnePoly(x0, x, S0, vals);
	OnePoly(x0, x, S0 + m, vals + 1);
	OnePoly(x0, x, S0 + 2*m, vals + 2);
	OnePoly(x0, x, S0 + 3*m, vals + 3);
}


static void InterpolSomVal(double krho, double kz, double complex vals[static 4], double ABSm[static 4]){
	int i, j;
	double t0, theta0, q0;
	q0 = sqrt(krho*krho + kz*kz);
	t0 = q0 / (q0 + 1);
	theta0 = atan(krho / kz);
	double * x;
	double * y;
	complex double * S;
	int * xn;
	int * yn;
	x = (double *)malloc(sizeof(double)*m);
	y = (double *)malloc(sizeof(double)*m);
	S = (complex double *)malloc(sizeof(complex double)*m*m*4);
	xn = (int *)malloc(sizeof(int)*m);
	yn = (int *)malloc(sizeof(int)*m);
	double a, b;
	int an, bn;
	if (t0 < tmin){
		a = 0.0;
		an = 0;
	} else {
		a = (double)((int)((t0 - tmin) / ht)) * ht + tmin;
		an = (int)((t0 - tmin) / ht);
		if (tmin != 0.0){
			an++;
		}
	}
	if (theta0 < thetamin){
		b = thetamin;
		bn = 0;
	} else {
		b = (double)((int)((theta0 - thetamin) / hth)) * hth + thetamin;	
		bn = (int)((theta0 - thetamin) / hth);
	}		
	if ((an + (m + 1) / 2) >= Nt){
		for(j = 0; j < m; j++){
			x[j] = tmax - (m - 1) * ht + j * ht;
			xn[j] = Nt - (m - 1) + j;
		}
	} else {
		if ((an - m / 2 + 1) <= 0){
			x[0] = 0.0;
			xn[0] = 0;
			for(j = 1; j < m; j++){
				x[j] = tmin + (j - 1) * ht;
				xn[j] = j;
			}			
		} else {
			for(j = 0; j < m; j++){
				x[j] = a - (m / 2) * ht + (j + 1) * ht;
				xn[j] = an - (m / 2) + 1 + j;
			}
		}
	}
	if ((bn + (m + 1) / 2) >= Nth - 1){
		for(j = 0; j < m; j++){
			y[j] = thetamax - (m - 1) * hth + j * hth;
			yn[j] = Nth - 1 - (m - 1) + j;
		}
	} else {
		if ((bn - m / 2 + 1) <= 0){
			for(j = 0; j < m; j++){
				y[j] = j * hth + thetamin;
				yn[j] = j;
			}			
		} else {
			for(j = 0; j < m; j++){
				y[j] = b - (m / 2) * hth + (j + 1) * hth;
				yn[j] = bn - (m / 2) + 1 + j;
			}
		}
	}
	for(i = 0; i < m; i++){
		for (j = 0; j < m; j++){
			S[i * m * 4 + j] = preTable[xn[i]*Nth*4 + yn[j]*4];
			S[i * m * 4 + j + m] = preTable[xn[i]*Nth*4 + yn[j]*4 + 1];	
			S[i * m * 4 + j + 2*m] = preTable[xn[i]*Nth*4 + yn[j]*4 + 2];
			S[i * m * 4 + j + 3*m] = preTable[xn[i]*Nth*4 + yn[j]*4 + 3];
			ABSm[0] += cabs(preTable[xn[i]*Nth*4 + yn[j]*4]);
			ABSm[1] += cabs(preTable[xn[i]*Nth*4 + yn[j]*4 + 1]);
			ABSm[2] += cabs(preTable[xn[i]*Nth*4 + yn[j]*4 + 2]);
			ABSm[3] += cabs(preTable[xn[i]*Nth*4 + yn[j]*4 + 3]);			
		}
	}
	for (i = 0; i < 4; i++){
		ABSm[i] = ABSm[i] / (m*m);
	}
	PolyInt(t0, theta0, x, y, S, vals);
	free(x);
	free(xn);
	free(y);
	free(yn);
	free(S);
}

static void FindError(int M){
	int i, j, l;
	time_t tm;
	double krho, kz, t, theta, q;
	double ER, ERgen, ERgavg;
	double erravg[4], errmin[4], errmax[4], tM[4], thetaM[4], tMX[4], thetaMX[4], V[4], V1[4];
	for (i = 0; i < 4; i++){
		erravg[i] = 0;
		errmin[i] = 100;
		errmax[i] = 0;
		tM[i] = 0;
		tMX[i] = 0;
		thetaM[i] = 0;
		thetaMX[i] = 0;
		V[i] = 0;
		V1[i] = 0;
	}
	complex double * vals;
	complex double * vals1;
	complex double vals2[4];
	complex double vals3[4];
	complex double ERR[4];
	for (i = 0; i < 4; i++){
		ABSm[i] = 0;
	}
	vals = (complex double *)malloc(sizeof(complex double)*4);
	vals1 = (complex double *)malloc(sizeof(complex double)*4);
	srand((unsigned) time(&tm));
	ERgavg = 0;
	FILE *fd = fopen("FEi.txt", "wb");
	FILE *fd1 = fopen("FEs.txt", "wb");	
	FILE *fd2 = fopen("FEae.txt", "wb");
	FILE *fd3 = fopen("FEre.txt", "wb");
	FILE *fd4 = fopen("FEre2.txt", "wb");
	FILE *fd5 = fopen("FEre3.txt", "wb");
	FILE *fd6 = fopen("FErei.txt", "wb");
	FILE *fd7 = fopen("FEge.txt", "wb");
	for(i = 0 ; i < M; i++) {
		t = ((double)(rand() % 10000) / 10000) * 0.94 + 0.03;
		theta = (double)(rand() % 15700) / 10000;
		q = t / (1 - t);
		kz = q / (sqrt(1 + tan(theta)*tan(theta)));
		krho = kz * tan(theta);
		InterpolSomVal(krho, kz, vals);		
		fprintf(fd, "%.5f %.5f %.5e %.5e %.5e %.5e %.5e %.5e %.5e %.5e %.5e %.5f %.5f\r\n", krho, kz, creal(vals[0]), cimag(vals[0]), creal(vals[1]), cimag(vals[1]), creal(vals[2]), cimag(vals[2]), creal(vals[3]), cimag(vals[3]), q, theta, t);
		SingleSomIntegral(krho, kz, vals1);
		for (l = 0; l < 4; l++){
			vals3[l] = vals1[l];
			vals2[l] = vals[l];
		}
		Transform(vals2, krho, kz, q, t, eps, 1);
		Transform(vals1, krho, kz, q, t, eps, 0);
		for (l = 0; l < 4; l++){
			ERR[l] = vals2[l] - vals3[l];
		}
		ERgen = sqrt(cabs(ERR[0]*ERR[0]) + cabs(ERR[1]*ERR[1]) + cabs(ERR[2]*ERR[2]) + cabs(ERR[3]*ERR[3]));
		ERgen = ERgen / (cabs(vals3[0]*vals3[0]) + cabs(vals3[1]*vals3[1]) + cabs(vals3[2]*vals3[2]) + cabs(vals3[3]*vals3[3]));
		ERgavg += ERgen;
		fprintf(fd7, "%.5f %.5f %.2e\r\n", t, theta, ERgen);
		fprintf(fd1, "%.5f %.5f %.5e %.5e %.5e %.5e %.5e %.5e %.5e %.5e %.5e %.5f %.5f\r\n", krho, kz, creal(vals1[0]), cimag(vals1[0]), creal(vals1[1]), cimag(vals1[1]), creal(vals1[2]), cimag(vals1[2]), creal(vals1[3]), cimag(vals1[3]), q, theta, t);
		fprintf(fd2, "%.5f %.5f ", t, theta);
		fprintf(fd3, "%.5f %.5f ", t, theta);
		fprintf(fd4, "%.5f %.5f ", t, theta);
		fprintf(fd5, "%.5f %.5f ", t, theta);
		fprintf(fd6, "%.5f %.5f ", t, theta);
		for (j = 0; j < 4; j++){
			ER = cabs(vals2[j] - vals3[j]) / cabs(vals3[j]);
			fprintf(fd6, "%.2e ", ER);
			erravg[j] += ER;
			if (errmin[j] >= ER){
				errmin[j] = ER;
				tM[j] = t;
				thetaM[j] = theta;
			}
			if (errmax[j] <= ER){
				errmax[j] = ER;
				tMX[j] = t;
				thetaMX[j] = theta;
				V[j] = cabs(vals[j]);
				V1[j] = cabs(vals1[j]);
			}
			
			ER = cabs(vals[j] - vals1[j]);
			fprintf(fd2, "%.2e ", ER);
			fprintf(fd4, "%.2e ", ER / ABS[j]);
			fprintf(fd5, "%.2e ", ER / ABSm[j]);
			ER = ER / cabs(vals1[j]);
			fprintf(fd3, "%.2e ", ER);
		}
		fprintf(fd2, "\r\n");
		fprintf(fd3, "\r\n");
		fprintf(fd4, "\r\n");
		fprintf(fd5, "\r\n");
		fprintf(fd6, "\r\n");
	}
	for (j = 0; j < 4; j++){
		erravg[j] = erravg[j] / M;
		printf("%.2e  %.2e %.5f %.5f   %.2e %.5f %.5f %.5e %.5e\n", erravg[j], errmin[j], tM[j], thetaM[j], errmax[j], tMX[j], thetaMX[j], V[j], V1[j]);
	}
	ERgavg = ERgavg / M;
	printf("%.2e\r\n", ERgavg);
	fclose(fd);
	fclose(fd1);
	fclose(fd2);
	fclose(fd3);
	fclose(fd4);
	fclose(fd5);
	fclose(fd6);
	fclose(fd7);		
	free(vals);
	free(vals1);
}