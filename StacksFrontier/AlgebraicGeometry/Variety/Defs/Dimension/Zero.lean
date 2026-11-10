module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.RingTheory.Artinian.Module
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Properties.Dimension

/-!
# Zero-dimensional schemes over a field

A scheme locally of finite type over a field and of dimension zero is a disjoint union of
spectra of finite-dimensional local Artinian algebras. If the scheme is also quasi-compact,
then it is affine and its structure morphism is finite.

## Main results

* `AlgebraicGeometry.exists_iso_coproduct_spec_local_artinian_of_dimension_zero` gives the
  decomposition of a locally algebraic zero-dimensional scheme.
* `AlgebraicGeometry.isAffine_of_finiteType_of_dimension_zero` proves affineness in the
  algebraic case.
* `AlgebraicGeometry.isFinite_of_finiteType_of_dimension_zero` proves finiteness of the
  structure morphism in the algebraic case.

## Implementation notes

The given morphism to `Spec k` is retained in the decomposition: the displayed isomorphism is an
isomorphism over `Spec k`. Finite-dimensionality is expressed by `Module.Finite`. Following the
finite-type convention for schemes over a field, "locally algebraic" is `LocallyOfFiniteType`,
while "algebraic" additionally assumes `QuasiCompact`. The indexing type of the coproduct is the
set of points of the scheme and the summand rings are its stalks, matching the canonical
dimension-zero decomposition.

## References

* [Stacks Project, Tag 06LH](https://stacks.math.columbia.edu/tag/06LH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- A scheme locally of finite type over a field and of dimension zero has locally quasi-finite
structure morphism, its fibres being discrete. -/
private lemma locallyQuasiFinite_of_dimension_zero
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [LocallyOfFiniteType f] (hdim : topologicalKrullDim X = 0) :
    LocallyQuasiFinite f := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : IsLocallyArtinian X := IsLocallyArtinian.of_topologicalKrullDim_le_zero hdim.le
  exact locallyQuasiFinite_iff_isDiscrete_preimage_singleton.mpr fun _ ↦
    IsDiscrete.univ.mono (Set.subset_univ _)

/-- The structure morphism of a zero-dimensional scheme of finite type over a field is finite. -/
private lemma isFinite_toSpec_of_dimension_zero
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [LocallyOfFiniteType f] [QuasiCompact f]
    (hdim : topologicalKrullDim X = 0) : IsFinite f := by
  have := locallyQuasiFinite_of_dimension_zero k f hdim
  exact IsFinite.of_locallyQuasiFinite f

/-- A zero-dimensional scheme locally of finite type over a field is, over that field, a
coproduct of spectra of finite-dimensional local Artinian algebras. -/
@[stacks 06LH "locally algebraic case"]
theorem exists_iso_coproduct_spec_local_artinian_of_dimension_zero
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [LocallyOfFiniteType f] (hdim : topologicalKrullDim X = 0) :
    ∃ (I : Type u) (A : I → Type u)
      (_ : ∀ i, CommRing (A i))
      (_ : ∀ i, Algebra k (A i))
      (_ : ∀ i, IsLocalRing (A i))
      (_ : ∀ i, IsArtinianRing (A i))
      (_ : ∀ i, Module.Finite k (A i))
      (e : X ≅ ∐ fun i ↦ Spec (.of (A i))),
      e.hom ≫ Sigma.desc (fun i ↦ Spec.map (CommRingCat.ofHom (algebraMap k (A i)))) = f := by
  have := LocallyOfFiniteType.isLocallyNoetherian f
  have := locallyQuasiFinite_of_dimension_zero k f hdim
  let A : X → Type u := fun x ↦ X.presheaf.stalk x
  let instAlgebra (x : X) : Algebra k (A x) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.presheaf.Γgerm x).hom.toAlgebra
  let (x : X) : Algebra k (A x) := instAlgebra x
  have hspec (x : X) :
      Spec.map (CommRingCat.ofHom (algebraMap k (A x))) = X.fromSpecStalk x ≫ f := by
    dsimp [instAlgebra, A]
    rw [← cancel_mono (Spec.map (Scheme.ΓSpecIso (.of k)).hom), SpecMap_ΓSpecIso_hom,
      Category.assoc, Scheme.toSpecΓ_naturality f, ← Category.assoc,
      Scheme.fromSpecStalk_toSpecΓ, ← Spec.map_comp, ← SpecMap_ΓSpecIso_hom, ← Spec.map_comp]
    apply congrArg Spec.map
    change (Scheme.ΓSpecIso (.of k)).hom ≫
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.presheaf.Γgerm x) = _
    simp [TopCat.Presheaf.Γgerm]
  have hfinite (x : X) : @Module.Finite k (A x) _ _ (instAlgebra x).toModule := by
    let : Algebra k (A x) := instAlgebra x
    have : LocallyQuasiFinite (Spec.map (CommRingCat.ofHom (algebraMap k (A x)))) :=
      (hspec x) ▸ inferInstance
    exact Algebra.QuasiFinite.iff_of_isArtinianRing.mp
      (HasRingHomProperty.Spec_iff.mp this).toAlgebra
  have : IsIso (sigmaFromSpecStalk X) :=
    isIso_sigmaFromSpecStalk_of_topologicalKrullDim_le_zero X hdim.le
  refine ⟨X, A, fun _ ↦ inferInstance, fun _ ↦ inferInstance, fun _ ↦ inferInstance,
    fun x ↦ isArtinianRing_stalk_of_topologicalKrullDim_le_zero X hdim.le x, hfinite,
    (asIso (sigmaFromSpecStalk X)).symm, ?_⟩
  apply (cancel_epi (sigmaFromSpecStalk X)).mp
  simp only [Iso.symm_hom, asIso_inv, IsIso.hom_inv_id_assoc]
  apply Sigma.hom_ext; intro x
  change _ = (Sigma.ι _ x ≫ Sigma.desc (fun x ↦ X.fromSpecStalk x)) ≫ f
  simpa only [Category.assoc, Sigma.ι_comp_desc] using hspec x

/-- A zero-dimensional scheme of finite type over a field is affine. -/
@[stacks 06LH "affineness in the algebraic case"]
theorem isAffine_of_finiteType_of_dimension_zero
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [LocallyOfFiniteType f] [QuasiCompact f]
    (hdim : topologicalKrullDim X = 0) : IsAffine X := by
  have := isFinite_toSpec_of_dimension_zero k f hdim
  exact isAffine_of_isAffineHom f

/-- The structure morphism of a zero-dimensional scheme of finite type over a field is finite. -/
@[stacks 06LH "finiteness in the algebraic case"]
theorem isFinite_of_finiteType_of_dimension_zero
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [LocallyOfFiniteType f] [QuasiCompact f]
    (hdim : topologicalKrullDim X = 0) : IsFinite f :=
  isFinite_toSpec_of_dimension_zero k f hdim

end AlgebraicGeometry

end
