module

public import StacksFrontier.Topology.Sheaves.Modules.Differentials

/-!
# Uniqueness of the sheaf of relative differentials

A universal relative derivation is unique up to a unique isomorphism compatible with the
derivations. This is the comparison principle used whenever a sheaf of modules carrying a
relative derivation is to be identified with the sheaf of relative differentials: one checks
that the given derivation is universal, and the identification together with its uniqueness
then comes for free.

## Main definitions

* `AlgebraicGeometry.SheafOfModules.IsUniversal.desc`: the morphism through which a relative
  derivation factors.
* `AlgebraicGeometry.SheafOfModules.IsUniversal.uniqueIso`: the comparison isomorphism between
  two universal relative derivations along the same morphism of sheaves of rings.

## Main results

* `AlgebraicGeometry.SheafOfModules.IsUniversal.postcomp_desc` and
  `AlgebraicGeometry.SheafOfModules.IsUniversal.desc_eq`: the factorization and its uniqueness.
* `AlgebraicGeometry.SheafOfModules.IsUniversal.hom_ext`: morphisms out of a universal object
  are determined by their effect on the universal derivation.
* `AlgebraicGeometry.SheafOfModules.IsUniversal.uniqueIso_compatible` and
  `AlgebraicGeometry.SheafOfModules.IsUniversal.eq_uniqueIso`: the comparison isomorphism
  carries one universal derivation to the other, and is the only isomorphism that does.

## Implementation notes

`IsUniversal` is a unique-factorization statement, so the whole development is the usual
argument that a universal object is unique up to unique isomorphism, carried out for
postcomposition of derivations by morphisms of sheaves of modules. The two bookkeeping lemmas
`postcomp_comp_val` and `postcomp_id_val` record that postcomposition is functorial; they are
stated for the underlying morphisms of presheaves of modules because that is the form in which
`IsUniversal` uses them.

## References

* [Stacks Project, Tag 08RM](https://stacks.math.columbia.edu/tag/08RM)
-/

@[expose] public section

open CategoryTheory PresheafOfModules TopologicalSpace

universe u v w

namespace AlgebraicGeometry.SheafOfModules

variable {X : TopCat.{u}} {O₁ O₂ : TopCat.Sheaf CommRingCat.{max u v} X} {φ : O₁ ⟶ O₂}

variable {M N P : _root_.SheafOfModules.{max u v w} (underlyingRingSheaf O₂)}

/-- Postcomposition of a relative derivation is compatible with composition. -/
theorem postcomp_comp_val (d : SheafDerivation.{u, v, w} φ M) (f : M ⟶ N) (g : N ⟶ P) :
    (d.postcomp f.val).postcomp g.val = d.postcomp (f ≫ g).val := by
  ext U b
  rfl

/-- Postcomposition of a relative derivation by an identity leaves it unchanged. -/
theorem postcomp_id_val (d : SheafDerivation.{u, v, w} φ M) :
    d.postcomp (_root_.SheafOfModules.Hom.val (𝟙 M)) = d := by
  ext U b
  rfl

namespace IsUniversal

variable {Ω Ω' : _root_.SheafOfModules.{max u v w} (underlyingRingSheaf O₂)}
  {d : SheafDerivation.{u, v, w} φ Ω} {d' : SheafDerivation.{u, v, w} φ Ω'}

/-- The morphism of sheaves of modules through which a relative derivation factors. -/
noncomputable def desc (h : IsUniversal.{u, v, w} d)
    {F : _root_.SheafOfModules.{max u v w} (underlyingRingSheaf O₂)}
    (D : SheafDerivation.{u, v, w} φ F) : Ω ⟶ F :=
  (h F D).choose

/-- The defining factorization of `IsUniversal.desc`. -/
theorem postcomp_desc (h : IsUniversal.{u, v, w} d)
    {F : _root_.SheafOfModules.{max u v w} (underlyingRingSheaf O₂)}
    (D : SheafDerivation.{u, v, w} φ F) : d.postcomp (h.desc D).val = D :=
  (h F D).choose_spec.1

/-- `IsUniversal.desc` is the only morphism realizing its factorization. -/
theorem desc_eq (h : IsUniversal.{u, v, w} d)
    {F : _root_.SheafOfModules.{max u v w} (underlyingRingSheaf O₂)}
    {D : SheafDerivation.{u, v, w} φ F} (g : Ω ⟶ F) (hg : d.postcomp g.val = D) :
    g = h.desc D :=
  (h F D).choose_spec.2 g hg

/-- Two morphisms out of a universal relative derivation that have the same effect on it are
equal. -/
theorem hom_ext (h : IsUniversal.{u, v, w} d)
    {F : _root_.SheafOfModules.{max u v w} (underlyingRingSheaf O₂)} {g g' : Ω ⟶ F}
    (hgg' : d.postcomp g.val = d.postcomp g'.val) : g = g' :=
  (h.desc_eq g rfl).trans (h.desc_eq g' hgg'.symm).symm

/-- The comparison isomorphism between two universal relative derivations along the same
morphism of sheaves of commutative rings. -/
noncomputable def uniqueIso (h : IsUniversal.{u, v, w} d) (h' : IsUniversal.{u, v, w} d') :
    Ω ≅ Ω' where
  hom := h.desc d'
  inv := h'.desc d
  hom_inv_id := h.hom_ext (by
    rw [← postcomp_comp_val, h.postcomp_desc, h'.postcomp_desc, postcomp_id_val])
  inv_hom_id := h'.hom_ext (by
    rw [← postcomp_comp_val, h'.postcomp_desc, h.postcomp_desc, postcomp_id_val])

/-- The comparison isomorphism carries one universal relative derivation to the other. -/
theorem uniqueIso_compatible (h : IsUniversal.{u, v, w} d) (h' : IsUniversal.{u, v, w} d') :
    d.postcomp (h.uniqueIso h').hom.val = d' :=
  h.postcomp_desc d'

/-- The comparison isomorphism is the only isomorphism carrying one universal relative
derivation to the other. -/
theorem eq_uniqueIso (h : IsUniversal.{u, v, w} d) (h' : IsUniversal.{u, v, w} d') (e : Ω ≅ Ω')
    (he : d.postcomp e.hom.val = d') : e = h.uniqueIso h' :=
  Iso.ext (h.desc_eq e.hom he)

end IsUniversal

end AlgebraicGeometry.SheafOfModules
