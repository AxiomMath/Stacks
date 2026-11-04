module

public import Mathlib.AlgebraicGeometry.Group.Affine
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.SmoothCharacteristicZero
public import StacksFrontier.RingTheory.HopfAlgebra.FinitelyGeneratedHopfSubalgebra

/-!
# Cartier's theorem: Hopf algebras over a field of characteristic zero are reduced

Let `k` be a field of characteristic `0`.  A commutative Hopf algebra `B` over `k` which is
finitely generated as a `k`-algebra is reduced: `Spec B` is a group scheme of finite type over
`Spec k`, smooth by [Stacks, Tag 047N] and hence reduced.  An arbitrary commutative Hopf algebra
`A` over `k` is the directed union of its finitely generated Hopf subalgebras (Waterhouse 3.3,
`HopfAlgebra.exists_finiteType_hopfAlgebra_mem_range`), so it is reduced as well; and an affine
group scheme over `k` is reduced, its ring of global sections being such a Hopf algebra.

## Main results

* `HopfAlgebra.isReduced_of_charZero_of_finiteType`: a finitely generated commutative Hopf
  algebra over a field of characteristic `0` is reduced.
* `HopfAlgebra.isReduced_of_charZero`: every commutative Hopf algebra over a field of
  characteristic `0` is reduced.
* `AlgebraicGeometry.isReduced_of_groupScheme_of_charZero_of_isAffine`: [Stacks, Tag 047O] for
  affine group schemes: an affine group scheme over a field of characteristic `0` is reduced.

## References

* [Stacks Project, Tag 047O](https://stacks.math.columbia.edu/tag/047O)
* W. C. Waterhouse, *Introduction to affine group schemes*, 3.3 and 11.4
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace HopfAlgebra

/-- A finitely generated commutative Hopf algebra over a field of characteristic `0` is
reduced: its spectrum is a group scheme of finite type over the field, which is reduced by
[Stacks, Tag 047N]. -/
@[sga "3 VIA 6.9" "partial", sga "3 VIII 7.1" "affine algebraic groups"]
theorem isReduced_of_charZero_of_finiteType (k : Type u) [Field k] [CharZero k]
    (B : Type u) [CommRing B] [HopfAlgebra k B] [Algebra.FiniteType k B] :
    IsReduced B :=
  (affine_isReduced_iff (CommRingCat.of B)).mp
    (@AlgebraicGeometry.isReduced_of_groupScheme_of_charZero k _ _ _
      (Spec (CommRingCat.of B) ↘ Spec (CommRingCat.of k))
      (instGrpObjSpecAsOverSpec (R := CommRingCat.of k) (A := CommRingCat.of B)) inferInstance)

/-- **Cartier's theorem for Hopf algebras.**  A commutative Hopf algebra over a field of
characteristic `0` is reduced.  A nilpotent element lies in a finitely generated Hopf subalgebra
(Waterhouse 3.3, `HopfAlgebra.exists_finiteType_hopfAlgebra_mem_range`), where it is still
nilpotent and hence zero by `HopfAlgebra.isReduced_of_charZero_of_finiteType`. -/
@[sga "3 VIII 7.1" "affine algebraic groups"]
theorem isReduced_of_charZero (k : Type u) [Field k] [CharZero k]
    (A : Type u) [CommRing A] [HopfAlgebra k A] : IsReduced A := by
  refine ⟨fun x hx => ?_⟩
  obtain ⟨B, _, _, φ, hφ, _, ⟨b, rfl⟩⟩ := exists_finiteType_hopfAlgebra_mem_range (k := k) x
  have := isReduced_of_charZero_of_finiteType k B
  obtain ⟨n, hn⟩ := hx
  have hb : IsNilpotent b := ⟨n, hφ (by simpa [map_pow] using hn)⟩
  simp [hb.eq_zero]

end HopfAlgebra

namespace AlgebraicGeometry

/-- The ring of global sections of an affine group scheme over the spectrum of a field `R` of
characteristic `0` is reduced.  The base is a bundled ring, so that the Hopf algebra structure
`HopfAlgebra R Γ(G, ⊤)` of `Mathlib.AlgebraicGeometry.Group.Affine` is found by instance
search; the field structure is passed as a proposition to avoid a second ring structure. -/
@[sga "3 VIII 7.1" "special case"]
theorem isReduced_globalSections_of_grpObj_of_isField (R : CommRingCat.{u}) (hR : IsField R)
    [CharZero R] (G : Scheme.{u}) [G.Over (Spec R)] [GrpObj (G.asOver (Spec R))] [IsAffine G] :
    _root_.IsReduced Γ(G, ⊤) := by
  let H : HopfAlgebra R Γ(G, ⊤) := inferInstance
  let := hR.toField
  exact @HopfAlgebra.isReduced_of_charZero R _ _ Γ(G, ⊤) _ H

/-- **Stacks Project, Tag 047O**, for affine group schemes.  An affine group scheme over a field
of characteristic `0` is reduced, with no finiteness hypothesis: its ring of global sections is a
commutative Hopf algebra, reduced by `HopfAlgebra.isReduced_of_charZero`. -/
@[stacks 047O "for affine group schemes",
  sga "3 VIA 6.9" "partial",
  sga "3 VIIA 8.5.1" "more general",
  sga "3 VIII 7.1" "affine group schemes"]
theorem isReduced_of_groupScheme_of_charZero_of_isAffine (k : Type u) [Field k] [CharZero k]
    (G : Scheme.{u}) (f : G ⟶ Spec (CommRingCat.of k)) [GrpObj (Over.mk f)] [IsAffine G] :
    IsReduced G := by
  let : G.Over (Spec (CommRingCat.of k)) := ⟨f⟩
  have : _root_.IsReduced Γ(G, ⊤) :=
    @isReduced_globalSections_of_grpObj_of_isField (CommRingCat.of k)
      (Field.toIsField k) (inferInstanceAs (CharZero k)) G _ ‹GrpObj (Over.mk f)› _
  exact isReduced_of_isAffine_isReduced G

end AlgebraicGeometry

end
