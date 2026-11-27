import Height24.Enumeration
import Height24.Rows0
import Height24.Rows1
import Height24.Rows2
import Height24.Rows3
import Height24.Rows4
import Height24.Rows5
import Height24.Rows6

namespace BealHeight.TwoTo24

theorem rows_all : rows.all rowOK = true := by
  unfold rows
  simp only [List.all_append, row0, row1, row2, row3, row4, row5, row6, row7,
    row8, row9, row10, row11, row12, row13, row14, row15,
    row16, row17, row18, row19, row20, row21, row22, row23,
    row24, row25, row26, row27, row28, row29, row30, row31,
    row32, row33, row34, row35, row36, row37, row38, row39,
    row40, row41, row42, row43, row44, row45, row46, row47,
    row48, row49, row50, Bool.and_self]

/-- All positive solutions with exponents greater than two and C^z ≤ 2^24
have a common divisor greater than one. -/
theorem checked : HoldsUpTo (2^24) :=
  from_checked_rows (2^24) rows powers_eq rows_all

/-- Boolean certificate for the explicit-height argument at K = 2. -/
theorem certified : certifies (2^24) = true :=
  (certifies_iff (2^24)).mpr checked

end BealHeight.TwoTo24

#print axioms BealHeight.TwoTo24.checked
