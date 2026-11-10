module

public import StacksFrontier.AlgebraicGeometry.Surfaces.GenusOneChain
public import StacksFrontier.AlgebraicGeometry.Surfaces.GenusOneForkFamily
public import StacksFrontier.AlgebraicGeometry.Surfaces.GenusOneForkFinite

/-!
# The classification of minimal numerical types of genus one with at least five components

A minimal numerical type of genus one with at least five components, one of which meets three or
more others, is one of the forks and stars of **Stacks 0C8T**: cases (22), (23), (24), (29),
(30), (31), (32), (33) and (34). Together with the cycles and chains, which are the minimal
numerical types of genus one in which every component meets at most two others, and with the
cases of at most four components, this gives the full classification of minimal numerical types of
genus one.

## Main results

* `AlgebraicGeometry.NumericalType.isGenusOneConfiguration_of_three_le_neighborCount` — a
  minimal numerical type of genus one with at least five components one of which meets three or
  more others is on the list.
* `AlgebraicGeometry.NumericalType.isMinimal_and_genus_eq_one_iff_of_three_le_neighborCount` —
  the resulting two-sided statement.
* `AlgebraicGeometry.NumericalType.isMinimal_and_genus_eq_one_iff_of_five_le_componentCount` —
  the two-sided classification for every numerical type with at least five components.
* `AlgebraicGeometry.NumericalType.isMinimal_and_genus_eq_one_iff` — the classification itself:
  one biconditional about every numerical type, with no hypothesis at all.

## References

* [Stacks Project, Tag 0C8T](https://stacks.math.columbia.edu/tag/0C8T)
-/

@[expose] public section

open scoped BigOperators

namespace AlgebraicGeometry.NumericalType

/-! ### A component meeting three or more others -/

/-- **Stacks Project, Tag 0C8T** for a numerical type with at least five components one of
which meets three or more others: if it is minimal of genus one then it is one of the forks and
stars on the list — cases (22), (23) and (24) for five components, the three unbounded fork
families (29), (30) and (31) for six or more, and the three exceptional configurations (32),
(33) and (34) on seven, eight and nine components. -/
public theorem isGenusOneConfiguration_of_three_le_neighborCount (T : NumericalType)
    (hmin : IsMinimal T) (hgenus : genus T = 1) (hn : 5 ≤ T.componentCount)
    (i₀ : Fin T.componentCount) (hdeg : 3 ≤ neighborCount T i₀) :
    IsGenusOneConfiguration T := by
  have hminus : ∀ i, IsMinusTwoIndex T i :=
    forall_isMinusTwoIndex_of_isMinimal_of_genus_eq_one T hmin hgenus (by omega)
  obtain ⟨l, x, t, v, d, w, r₀, k, ht1, hlx, hleaf, hvinj, hvl, hvsurj, hcfg, hr₀, hrest,
    hmain, hpos⟩ := exists_affine_extension_of_three_le_neighborCount T hmin hgenus hn i₀ hdeg
  rcases hpos with ⟨rfl, hD⟩ | ⟨rfl, hr0, rfl⟩ | ⟨rfl, hr0, rfl⟩ | ⟨rfl, rfl, hA⟩ |
    ⟨rfl, hr0, rfl⟩ | ⟨rfl, hr0, rfl⟩ | ⟨rfl, hr0, rfl⟩
  · have ht4 : 4 ≤ t := hcfg.1
    rcases hD with ⟨hr0, rfl⟩ | ⟨hr0, rfl⟩ | ⟨hside, hkt⟩
    · rcases Nat.lt_or_ge t 5 with ht | ht
      · obtain rfl : t = 4 := by omega
        exact isGenusOneConfiguration_of_affine_D4_zero T (by omega) hminus l x hlx hleaf v
          hvinj hvl hvsurj w hcfg (by omega) r₀ hr₀ hr0 hrest hmain
      · exact isGenusOneConfiguration_of_affine_D_zero ht T (by omega) hminus l x hlx hleaf v
          hvinj hvl hvsurj w hcfg ht1 r₀ hr₀ hr0 hrest hmain
    · rcases Nat.lt_or_ge t 5 with ht | ht
      · obtain rfl : t = 4 := by omega
        exact isGenusOneConfiguration_of_affine_D4_centre T (by omega) hminus l x hlx hleaf v
          hvinj hvl hvsurj w hcfg (by omega) r₀ hr₀ hr0 hrest hmain
      · exact isGenusOneConfiguration_of_affine_D_one ht T (by omega) hminus l x hlx hleaf v
          hvinj hvl hvsurj w hcfg ht1 r₀ hr₀ hr0 hrest hmain
    · have ht4z : (4 : ℤ) ≤ (t : ℤ) := by exact_mod_cast ht4
      have hk1 : 1 ≤ k := by nlinarith
      have hk2 : k ≤ 2 := by nlinarith
      obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ : (k = 1 ∧ t = 8) ∨ (k = 2 ∧ t = 4) := by
        interval_cases k <;> [left; right] <;> exact ⟨rfl, by omega⟩
      · rcases hside with hs | hs
        · exact isGenusOneConfiguration_of_affine_D8_last T (by omega) hminus l x hlx hleaf v
            hvinj hvl hvsurj w hcfg (by omega) r₀ hr₀ (by omega) hrest hmain
        · exact isGenusOneConfiguration_of_affine_D8_mid T (by omega) hminus l x hlx hleaf v
            hvinj hvl hvsurj w hcfg (by omega) r₀ hr₀ (by omega) hrest hmain
      · rcases hside with hs | hs
        · exact isGenusOneConfiguration_of_affine_D4_last T (by omega) hminus l x hlx hleaf v
            hvinj hvl hvsurj w hcfg (by omega) r₀ hr₀ (by omega) hrest hmain
        · exact isGenusOneConfiguration_of_affine_D4_mid T (by omega) hminus l x hlx hleaf v
            hvinj hvl hvsurj w hcfg (by omega) r₀ hr₀ (by omega) hrest hmain
  · rcases Nat.lt_or_ge t 5 with ht | ht
    · obtain rfl : t = 4 := by omega
      exact isGenusOneConfiguration_of_affine_B4 T (by omega) hminus l x hlx hleaf v hvinj hvl
        hvsurj w hcfg (by omega) r₀ hr₀ hr0 hrest hmain
    · exact isGenusOneConfiguration_of_affine_B ht T (by omega) hminus l x hlx hleaf v hvinj
        hvl hvsurj w hcfg ht1 r₀ hr₀ hr0 hrest hmain
  · rcases Nat.lt_or_ge t 5 with ht | ht
    · obtain rfl : t = 4 := by omega
      exact isGenusOneConfiguration_of_affine_C4 T (by omega) hminus l x hlx hleaf v hvinj hvl
        hvsurj w hcfg (by omega) r₀ hr₀ hr0 hrest hmain
    · exact isGenusOneConfiguration_of_affine_C ht T (by omega) hminus l x hlx hleaf v hvinj
        hvl hvsurj w hcfg ht1 r₀ hr₀ hr0 hrest hmain
  · rcases hA with ⟨rfl, hr0⟩ | ⟨rfl, hr0 | hr0⟩
    · exact isGenusOneConfiguration_of_affine_A7 T (by omega) hminus l x hlx hleaf v hvinj hvl
        hvsurj w hcfg (by omega) r₀ hr₀ hr0 hrest hmain
    · exact isGenusOneConfiguration_of_affine_A8_two T (by omega) hminus l x hlx hleaf v hvinj
        hvl hvsurj w hcfg (by omega) r₀ hr₀ hr0 hrest hmain
    · exact isGenusOneConfiguration_of_affine_A8_five T (by omega) hminus l x hlx hleaf v hvinj
        hvl hvsurj w hcfg (by omega) r₀ hr₀ hr0 hrest hmain
  · obtain rfl : t = 6 := hcfg.1
    exact isGenusOneConfiguration_of_affine_E6 T (by omega) hminus l x hlx hleaf v hvinj hvl
      hvsurj w hcfg (by omega) r₀ hr₀ hr0 hrest hmain
  · obtain rfl : t = 7 := hcfg.1
    exact isGenusOneConfiguration_of_affine_E7 T (by omega) hminus l x hlx hleaf v hvinj hvl
      hvsurj w hcfg (by omega) r₀ hr₀ hr0 hrest hmain
  · obtain rfl : t = 8 := hcfg.1
    exact isGenusOneConfiguration_of_affine_E8 T (by omega) hminus l x hlx hleaf v hvinj hvl
      hvsurj w hcfg (by omega) r₀ hr₀ hr0 hrest hmain

/-- **Stacks Project, Tag 0C8T** for a numerical type with at least five components one of
which meets three or more others: it is minimal of genus one exactly when it is one of the forks
and stars on the list, cases (22), (23), (24), (29), (30), (31), (32), (33) and (34). -/
@[stacks 0C8T "the classification when some component meets three or more others \
and there are at least five of them: cases (22), (23) and (24) for five components, the unbounded \
fork families (29), (30) and (31) for six or more, and the exceptional configurations (32), (33) \
and (34) on seven, eight and nine components"]
public theorem isMinimal_and_genus_eq_one_iff_of_three_le_neighborCount (T : NumericalType)
    (hn : 5 ≤ T.componentCount) (i₀ : Fin T.componentCount) (hdeg : 3 ≤ neighborCount T i₀) :
    (IsMinimal T ∧ genus T = 1) ↔ IsGenusOneConfiguration T :=
  ⟨fun h => isGenusOneConfiguration_of_three_le_neighborCount T h.1 h.2 hn i₀ hdeg,
    isMinimal_and_genus_eq_one_of_isGenusOneConfiguration T⟩

/-! ### The classification for at least five components -/

/-- **Stacks Project, Tag 0C8T** for five or more components. A numerical type with at least
five components is minimal of genus one exactly when it is one of the configurations on the
list. Whether some component meets three or more others decides which half of the list it lies
in: if none does, the type is the cycle or one of the chains — cases (16) to (21) for five
components and cases (25) to (28) for six or more — and otherwise it is one of the forks and
stars, cases (22), (23), (24), (29), (30), (31), (32), (33) and (34). -/
@[stacks 0C8T "the classification for at least five components: cases (16)-(34)"]
public theorem isMinimal_and_genus_eq_one_iff_of_five_le_componentCount (T : NumericalType)
    (hn : 5 ≤ T.componentCount) :
    (IsMinimal T ∧ genus T = 1) ↔ IsGenusOneConfiguration T := by
  by_cases hdeg : ∀ i, neighborCount T i ≤ 2
  · exact isMinimal_and_genus_eq_one_iff_of_neighborCount_le_two T hn hdeg
  · obtain ⟨i₀, hi₀⟩ := not_forall.1 hdeg
    exact isMinimal_and_genus_eq_one_iff_of_three_le_neighborCount T hn i₀ (by omega)

/-! ### The classification -/

/-- **Stacks Project, Tag 0C8T.** A numerical type is minimal of genus one exactly when it is
one of the thirty-four configurations of the list: the single component of genus one, case (1);
the twenty-six exceptional coefficient tables on two to nine components, cases (2)-(24) and
(32)-(34); and the seven unbounded families on six or more, cases (25)-(31). -/
@[stacks 0C8T "the classification: a numerical type is minimal of genus one exactly \
when it is one of the thirty-four configurations listed, cases (1)-(34)"]
public theorem isMinimal_and_genus_eq_one_iff (T : NumericalType) :
    (IsMinimal T ∧ genus T = 1) ↔ IsGenusOneConfiguration T := by
  obtain h | h | h | h | h : T.componentCount = 1 ∨ T.componentCount = 2 ∨
      T.componentCount = 3 ∨ T.componentCount = 4 ∨ 5 ≤ T.componentCount := by
    have := T.componentCount_pos
    omega
  · exact isMinimal_and_genus_eq_one_iff_of_componentCount_eq_one T h
  · exact isMinimal_and_genus_eq_one_iff_of_componentCount_eq_two T h
  · exact isMinimal_and_genus_eq_one_iff_of_componentCount_eq_three T h
  · exact isMinimal_and_genus_eq_one_iff_of_componentCount_eq_four T h
  · exact isMinimal_and_genus_eq_one_iff_of_five_le_componentCount T h

end AlgebraicGeometry.NumericalType
