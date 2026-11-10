module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.Topology.Sheaves.CommRingCat
public import StacksCore.Tactic.StacksAttribute

/-!
# The sheaf of total quotient rings

For a sheaf of commutative rings `O` on a topological space, localize the ring of sections on
an open set at those sections whose germ at every point of that open set is a nonzerodivisor.
Sheafifying gives the *sheaf of total quotient rings* of `O`, together with a canonical
morphism from `O`, which makes it a sheaf of `O`-algebras. For a scheme this is the sheaf of
total quotient rings of the scheme.

## Main definitions

* `AlgebraicGeometry.totalQuotientSheaf`: the sheafification of the presheaf of total quotient
  rings of a sheaf of commutative rings on a topological space.
* `AlgebraicGeometry.toTotalQuotientSheaf`: its canonical morphism from the given sheaf.
* `AlgebraicGeometry.MeromorphicFunction`: a global section of the sheaf of total quotient
  rings, that is, a meromorphic function.
* `AlgebraicGeometry.Scheme.totalQuotientSheaf`, `AlgebraicGeometry.Scheme.toTotalQuotientSheaf`:
  the same construction for the structure sheaf of a scheme.

## Implementation notes

Mathlib's `TopCat.Presheaf.totalQuotientPresheaf` performs the objectwise localization. Its
denominator submonoid on `U` consists precisely of the sections whose germs at all points of
`U` belong to `nonZeroDivisors`; in particular those sections are themselves nonzerodivisors.
The definitions sheafify that presheaf and compose the objectwise localization map with the
sheafification unit. The scheme-level pair is the specialization of the topological-space pair
at the structure sheaf, so every statement about one applies to the other.

## References

* [Stacks Project, Tag 02AR](https://stacks.math.columbia.edu/tag/02AR)
* [Stacks Project, Tag 01X2](https://stacks.math.columbia.edu/tag/01X2)
* [Stacks Project, Tag 01X4](https://stacks.math.columbia.edu/tag/01X4)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

variable {X : TopCat.{u}}

/-- The sheaf of total quotient rings: the sheafification of the presheaf which localizes at
sections that are non-zero-divisors in every stalk. -/
noncomputable abbrev totalQuotientSheaf (O : TopCat.Sheaf CommRingCat.{u} X) :
    TopCat.Sheaf CommRingCat.{u} X :=
  (presheafToSheaf (Opens.grothendieckTopology X) CommRingCat.{u}).obj
    O.presheaf.totalQuotientPresheaf

/-- The canonical morphism from a sheaf of rings to its sheaf of total quotient rings. -/
noncomputable abbrev toTotalQuotientSheaf (O : TopCat.Sheaf CommRingCat.{u} X) :
    O ⟶ totalQuotientSheaf O :=
  (fullyFaithfulSheafToPresheaf (Opens.grothendieckTopology X) CommRingCat.{u}).homEquiv.symm
    (O.presheaf.toTotalQuotientPresheaf ≫
      toSheafify (Opens.grothendieckTopology X) O.presheaf.totalQuotientPresheaf)

/-- A meromorphic function on a locally ringed space is a global section of its sheaf of
meromorphic functions, the sheaf of total quotient rings of its structure sheaf. -/
@[stacks 01X2 "a meromorphic function", ega "IV 20.1.3" "M(X)"]
abbrev MeromorphicFunction (O : TopCat.Sheaf CommRingCat.{u} X) : Type u :=
  (totalQuotientSheaf O).presheaf.obj (Opposite.op ⊤)

/-- The underlying morphism of presheaves of `AlgebraicGeometry.toTotalQuotientSheaf` is the
objectwise localization map followed by the sheafification unit. -/
lemma toTotalQuotientSheaf_hom (O : TopCat.Sheaf CommRingCat.{u} X) :
    (toTotalQuotientSheaf O).hom = O.presheaf.toTotalQuotientPresheaf ≫
      toSheafify (Opens.grothendieckTopology X) O.presheaf.totalQuotientPresheaf := rfl

/-- The sheaf of total quotient rings of a scheme. It is the sheafification of the presheaf
which, on each open set, localizes the ring of regular functions at the sections whose germs
are nonzerodivisors everywhere on that open set. -/
@[stacks 02AR "total_quotient_sheaf", ega "IV 20.1.3"]
noncomputable abbrev Scheme.totalQuotientSheaf (Y : Scheme.{u}) :
    TopCat.Sheaf CommRingCat.{u} Y :=
  _root_.AlgebraicGeometry.totalQuotientSheaf Y.sheaf

/-- The canonical morphism from the structure sheaf to the sheaf of total quotient rings,
giving the latter its structure as a sheaf of `𝒪_X`-algebras. -/
@[stacks 02AR "total_quotient_sheaf"]
noncomputable def Scheme.toTotalQuotientSheaf (Y : Scheme.{u}) :
    Y.sheaf ⟶ Y.totalQuotientSheaf :=
  _root_.AlgebraicGeometry.toTotalQuotientSheaf Y.sheaf

/-- The underlying morphism of presheaves of `AlgebraicGeometry.Scheme.toTotalQuotientSheaf` is
the objectwise localization map followed by the sheafification unit. -/
lemma Scheme.toTotalQuotientSheaf_hom (Y : Scheme.{u}) :
    Y.toTotalQuotientSheaf.hom = Y.presheaf.toTotalQuotientPresheaf ≫
      toSheafify (Opens.grothendieckTopology Y) Y.presheaf.totalQuotientPresheaf := rfl

/-- On an affine open of a scheme, the sections whose germ at every point is a nonzerodivisor
are exactly the nonzerodivisors of the ring of sections. In other words, the denominator
submonoid of the total quotient presheaf is `nonZeroDivisors Γ(X, U)` there. -/
theorem submonoidPresheafOfStalk_obj_eq_nonZeroDivisors
    (Y : Scheme.{u}) (U : Y.Opens) (hU : IsAffineOpen U) :
    (Y.presheaf.submonoidPresheafOfStalk
      (fun x ↦ nonZeroDivisors (Y.presheaf.stalk x))).obj (Opposite.op U) =
        nonZeroDivisors Γ(Y, U) := by
  ext r
  delta TopCat.Presheaf.submonoidPresheafOfStalk
  simp only [Submonoid.mem_iInf, Submonoid.mem_comap]
  constructor
  · intro hr
    apply mem_nonZeroDivisors_iff.mpr
    constructor <;> intro s hs <;> apply Y.IsSheaf.section_ext <;> intro x hx
    all_goals
      have hmul : Y.presheaf.germ U x hx r *
          Y.presheaf.germ U x hx s = 0 := by
        simpa only [map_mul, map_zero, mul_comm] using congrArg
          (Y.presheaf.germ U x hx) hs
      have hs0 : Y.presheaf.germ U x hx s = 0 :=
        (mem_nonZeroDivisors_iff.mp (hr ⟨x, hx⟩)).1 _ hmul
      obtain ⟨V, hxV, iU, iV, hloc⟩ :=
        TopCat.Presheaf.germ_eq Y.presheaf x hx hx s 0
          (by simpa only [map_zero] using hs0)
      refine ⟨V, iU.le, hxV, ?_⟩
      simpa only [show iU = iV from Subsingleton.elim _ _,
        show iV = homOfLE iU.le from Subsingleton.elim _ _] using hloc
  · intro hr x
    let : Algebra Γ(Y, U) (Y.presheaf.stalk x) :=
      Y.presheaf.algebra_section_stalk ⟨x, x.2⟩
    let : IsLocalization (hU.primeIdealOf x).asIdeal.primeCompl
        (Y.presheaf.stalk x) := hU.isLocalization_stalk x
    change Y.presheaf.germ U x.1 x.2 r ∈ nonZeroDivisors (Y.presheaf.stalk x)
    exact (IsLocalization.nonZeroDivisors_le_comap
      (M := (hU.primeIdealOf x).asIdeal.primeCompl)
      (S := Y.presheaf.stalk x)) hr

add_to_stacks 01X2 "the sheaf of meromorphic functions" totalQuotientSheaf
add_to_ega "IV 20.1.3" "M_X" AlgebraicGeometry.totalQuotientSheaf
add_to_ega "I 7.3.2" AlgebraicGeometry.totalQuotientSheaf

end AlgebraicGeometry
