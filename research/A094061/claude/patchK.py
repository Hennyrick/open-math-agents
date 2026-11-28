six={'z0': (6, 12), 'zr': (-3, -6), 'b1': (-3, 3), 'b2': (6, -6), 'q1': (6, 3), 'q2': (-12, -6)}
k9=(-2,-4)
cof=open('Kcof2.txt').read()
hyp=open('Khyp.txt').read()
def U(k): a,b=six[k]; return "(1 - ((%d : PK) + (%d : PK) * C om) * Gt)"%(a,b)
A="((%d : PK) + (%d : PK) * C om) * %s * %s"%(k9[0],k9[1],U('z0'),U('zr'))
E="(%s * %s)"%(U('q1'),U('q2'))
N="(C om ^ 2 * %s * %s)"%(U('b1'),U('b2'))
G="(54 * Gt)"
new='''  have hpoly : (D ^ 2 + Gb * D + Gb ^ 2) * (E ^ 2 + Nn * E + Nn ^ 2) - Gb * D * Nn * E = 0 := by
    set Gt : PK := C ((1 : KK) / 6) * Gb with hGt
    have hG6 : Gb = 6 * Gt := by
      rw [hGt, ← mul_assoc, ← map_ofNat C 6, ← map_mul]; norm_num
%s
    have hom : C om ^ 2 + C om + 1 = (0 : PK) := by rw [← map_pow, ← map_add, ← map_one C, ← map_add, om_rel, map_zero]
    have hpoly9 : ((%s) ^ 2 + %s * (%s) + %s ^ 2) * (%s ^ 2 + %s * %s + %s ^ 2) - %s * (%s) * %s * %s = 0 := by
      linear_combination (%s) * hom
    have e9D : (9 : PK) * D = %s := by
      rw [hD, uu, uu, h_z0, h_zr, ← h_k9]; ring
    have e9G : (9 : PK) * Gb = %s := by rw [hG6]; ring
    have eE : E = %s := by rw [hE, uu, uu, h_q1, h_q2]
    have eN : Nn = %s := by rw [hN, uu, uu, h_b1, h_b2]
    have h81 : ((9 * D) ^ 2 + (9 * Gb) * (9 * D) + (9 * Gb) ^ 2) * (E ^ 2 + Nn * E + Nn ^ 2)
        - (9 * Gb) * (9 * D) * Nn * E = 0 := by
      rw [e9D, e9G, eE, eN]; exact hpoly9
    have h81' : ((D ^ 2 + Gb * D + Gb ^ 2) * (E ^ 2 + Nn * E + Nn ^ 2) - Gb * D * Nn * E) * 81 = 0 := by
      rw [← h81]; ring
    have h810 : constantCoeff (81 : PK) ≠ 0 := by
      rw [show (81 : PK) = C 81 from (map_ofNat C 81).symm, constantCoeff_C]; norm_num
    exact cancel1 h810 (by rw [h81', zero_mul])
'''%("\n".join("  "+l for l in hyp.split("\n")),A,G,A,G,E,N,E,N,G,A,N,E,cof,A,G,E,N)
s=open('/home/user/open-math-agents/research/A094061/lean/Branch.lean').read()
i=s.index("  have hpoly : (D ^ 2 + Gb * D + Gb ^ 2)"); j=s.index("  rw [hpoly] at key")
s=s[:i]+new+s[j:]
open('/home/user/open-math-agents/research/A094061/lean/Branch.lean','w').write(s)
