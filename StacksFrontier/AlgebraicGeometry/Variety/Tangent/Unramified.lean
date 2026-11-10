module

public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.RingTheory.LocalRing.Module
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FiniteTypeLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.UnramifiedLocusBaseChange
public import StacksFrontier.AlgebraicGeometry.Variety.GeometricFieldChange.TangentFibre
public import StacksFrontier.AlgebraicGeometry.Variety.Tangent.Cotangent
public import StacksCore.Tactic.StacksAttribute

/-!
# Injectivity of the tangent map and unramifiedness

Let `f : X ⟶ Y` be a morphism of schemes over a base `S`, locally of finite type, and let `x` be
a point of `X` whose residue field agrees with that of its image. Then the tangent map
`d f : T_{X/S, x} ⟶ T_{Y/S, f x}` is injective if and only if `f` is unramified at `x`.

## Main definitions

* `AlgebraicGeometry.dottedTangentArrowOverBase`: a tangent vector of `X` over `Y` read as a
  tangent vector of `X` over `S`.

## Main results

* `AlgebraicGeometry.tangentMap_eq_zero_iff` and
  `AlgebraicGeometry.injective_tangentMap_iff_subsingleton`: the kernel of the tangent map of
  `f` at `x` is the relative tangent space of `X` over `Y` at `x`, so the tangent map is
  injective exactly when that space vanishes.
* `AlgebraicGeometry.subsingleton_dottedTangentArrow_iff_unramifiedAt`: for a morphism locally
  of finite type, the relative tangent space at a point vanishes exactly when the morphism is
  unramified at that point.
* `AlgebraicGeometry.injective_tangentMap_iff_unramifiedAt`: the equivalence of the two
  conditions of Tag 0B2G, and
  `AlgebraicGeometry.injective_tangentMap_iff_unramifiedAt_of_locallyOfFiniteType_base` the same
  equivalence under the source's hypothesis that `X` is locally of finite type over `S`, which
  by Tag 01T8 implies that `f` is.

## Implementation notes

Equality of the residue fields at `x` and at `f x` is expressed, as in Tag 0B2F, by the
assertion that the canonical residue-field homomorphism is an isomorphism; this is what makes
the tangent map available in the first place.

A tangent vector of `X/S` at `x` lies in the kernel of the tangent map exactly when its
composite with `f` is the canonical dual-number point of `Y` at `f x`, that is, exactly when it
is a tangent vector of `X/Y` at `x`. The residue-field hypothesis enters again here: the
comparison morphism of the spectra of the dual numbers over the two residue fields is then an
isomorphism, hence can be cancelled. The source's exact sequence of relative differentials is
therefore not used — the kernel is computed geometrically.

The vanishing of a relative tangent space is read on the other side of Tag 0B2D. Tangent vectors
of `X/Y` at `x` are the `𝒪_{Y,f x}`-derivations of `𝒪_{X,x}` with values in `κ(x)`, hence the
`𝒪_{X,x}`-linear functionals on `Ω[𝒪_{X,x}⁄𝒪_{Y,f x}]` with values in `κ(x)`. That module of
differentials is a finite `𝒪_{X,x}`-module, because the stalk map of a morphism locally of
finite type is essentially of finite type, so Nakayama's lemma turns the vanishing of all its
functionals into its own vanishing, which is formal unramifiedness of the stalk map.

## References

* [Stacks Project, Tag 0B2G](https://stacks.math.columbia.edu/tag/0B2G)
* [Stacks Project, Tag 0B2D](https://stacks.math.columbia.edu/tag/0B2D)
* [Stacks Project, Tag 02G4](https://stacks.math.columbia.edu/tag/02G4)
-/

@[expose] public section

open CategoryTheory TensorProduct

universe u v

attribute [local instance] AlgebraicGeometry.residueModule AlgebraicGeometry.residueSMulComm
  AlgebraicGeometry.residueSMulComm' AlgebraicGeometry.stalkMapAlgebra
  AlgebraicGeometry.baseResidueModule AlgebraicGeometry.baseResidueSMulComm
  AlgebraicGeometry.residueIsScalarTower

/-- A finite module over a local ring vanishes exactly when all of its linear functionals with
values in the residue field vanish. This is the dual form of
`IsLocalRing.subsingleton_tensorProduct`, the functionals on a module being the functionals on
its residue-field fibre. -/
private theorem subsingleton_linearMap_residueField_iff {A : Type u} [CommRing A] [IsLocalRing A]
    {M : Type v} [AddCommGroup M] [Module A M] [Module.Finite A M] :
    Subsingleton (M →ₗ[A] IsLocalRing.ResidueField A) ↔ Subsingleton M := by
  have e : (M →ₗ[A] IsLocalRing.ResidueField A) ≃ₗ[IsLocalRing.ResidueField A]
      Module.Dual (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField A ⊗[A] M) :=
    (LinearMap.ringLmapEquivSelf (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField A)
      (M →ₗ[A] IsLocalRing.ResidueField A)).symm.trans
      (TensorProduct.AlgebraTensorModule.lift.equiv A (IsLocalRing.ResidueField A)
        (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField A) M
        (IsLocalRing.ResidueField A))
  rw [e.toEquiv.subsingleton_congr, Module.subsingleton_dual_iff,
    IsLocalRing.subsingleton_tensorProduct]

namespace AlgebraicGeometry

/-- **The relative tangent space at a point detects unramifiedness there.** For a morphism
locally of finite type, the tangent vectors of `X` over `S` at `x` are the functionals on the
stalk of relative differentials, which is a finite module over the local ring at `x`; so they
all vanish exactly when that stalk does, that is, exactly when `f` is unramified at `x`. -/
theorem subsingleton_dottedTangentArrow_iff_unramifiedAt {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (x : X) :
    Subsingleton (DottedTangentArrow f x) ↔ UnramifiedAt f x := by
  classical
  have hess : Algebra.EssFiniteType (ToType (S.presheaf.stalk (f.base x)))
      (ToType (X.presheaf.stalk x)) :=
    RingHom.essFiniteType_algebraMap.mpr (LocallyOfFiniteType.stalkMap f x)
  have e1 : DottedTangentArrow f x ≃
      Derivation (S.presheaf.stalk (f.base x)) (X.presheaf.stalk x) (X.residueField x) :=
    ((dottedDerivationLinearEquiv f x).trans (tangentDerivationsEquiv f x)).toEquiv
  have e2 := KaehlerDifferential.linearMapEquivDerivation
    (ToType (S.presheaf.stalk (f.base x))) (ToType (X.presheaf.stalk x))
    (M := ToType (X.residueField x))
  rw [unramifiedAt_iff_formallyUnramified_stalkMap f x]
  refine (Equiv.subsingleton_congr e1).trans ?_
  refine (Equiv.subsingleton_congr e2.toEquiv.symm).trans ?_
  refine subsingleton_linearMap_residueField_iff.trans ?_
  exact (Algebra.formallyUnramified_iff _ _).symm

section Kernel

variable {X Y S : Scheme.{u}} (f : X ⟶ Y) (p : X ⟶ S) (q : Y ⟶ S) (x : X)

/-- The dual-number base point at `x` of `X` over `Y`, read in `S`, is the dual-number base
point at `x` of `X` over `S`. -/
lemma dualNumberBasePoint_comp (h : f ≫ q = p) :
    dualNumberBasePoint f x ≫ q = dualNumberBasePoint p x := by
  dsimp only [dualNumberBasePoint]
  simp only [Category.assoc]
  rw [← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField q (f.base x)]
  simp only [← Spec.map_comp_assoc]
  rw [← h]
  simp only [Scheme.residueFieldMap_comp]
  rfl

/-- A tangent vector of `X` over `Y` at `x` is in particular a tangent vector of `X` over `S`
at `x`. -/
def dottedTangentArrowOverBase (h : f ≫ q = p) (θ : DottedTangentArrow f x) :
    DottedTangentArrow p x :=
  ⟨θ.val, θ.property.1, by
    calc θ.val ≫ p = (θ.val ≫ f) ≫ q := by rw [← h, Category.assoc]
      _ = dualNumberBasePoint f x ≫ q := by rw [θ.property.2]
      _ = dualNumberBasePoint p x := dualNumberBasePoint_comp f p q x h⟩

/-- **A tangent vector of `X/S` at `x` is killed by the tangent map of `f` exactly when it is a
tangent vector of `X/Y` at `x`**, that is, exactly when its composite with `f` is the
dual-number base point. -/
lemma tangentMap_eq_zero_iff (h : f ≫ q = p) [IsIso (f.residueFieldMap x)]
    (θ : DottedTangentArrow p x) :
    tangentMap f p q h x θ = 0 ↔ θ.val ≫ f = dualNumberBasePoint f x := by
  let e : X.residueField x ≃+* Y.residueField (f.base x) :=
    (asIso (f.residueFieldMap x)).symm.commRingCatIsoToRingEquiv
  let α := dualNumberCongr e
  have hα₀ (w : DualNumber (X.residueField x)) :
      TrivSqZeroExt.fst (α w) = (inv (f.residueFieldMap x)).hom (TrivSqZeroExt.fst w) := by
    cases w with
    | mk c d => rfl
  have hα₁ (w : DualNumber (X.residueField x)) :
      TrivSqZeroExt.snd (α w) = (inv (f.residueFieldMap x)).hom (TrivSqZeroExt.snd w) := by
    cases w with
    | mk c d => rfl
  have hbase : Spec.map (CommRingCat.ofHom α.toRingHom) ≫ dualNumberBasePoint f x =
      dualNumberToBase (Y.residueField (f.base x)) ≫ Y.fromSpecResidueField (f.base x) := by
    dsimp only [dualNumberBasePoint, dualNumberToBase]
    rw [← Spec.map_comp_assoc, ← Spec.map_comp_assoc]
    congr 2
    refine CommRingCat.hom_ext (RingHom.ext fun z => ?_)
    refine TrivSqZeroExt.ext ?_ ?_
    · change TrivSqZeroExt.fst (α (TrivSqZeroExt.inl ((f.residueFieldMap x).hom z))) = z
      rw [hα₀]
      change (inv (f.residueFieldMap x)).hom ((f.residueFieldMap x).hom z) = z
      exact congrArg (fun g : Y.residueField (f.base x) ⟶ Y.residueField (f.base x) ↦ g z)
        (IsIso.hom_inv_id (f.residueFieldMap x))
    · change TrivSqZeroExt.snd (α (TrivSqZeroExt.inl ((f.residueFieldMap x).hom z))) = 0
      rw [hα₁]
      exact map_zero _
  have happly := tangentMap_apply f p q h x θ α.toRingHom hα₀ hα₁
  have hzero := (dottedTangentArrowModule q (f.base x)).zero_apply
  refine ⟨fun ht => ?_, fun ht => Subtype.ext ?_⟩
  · have hv : Spec.map (CommRingCat.ofHom α.toRingHom) ≫ θ.val ≫ f =
        Spec.map (CommRingCat.ofHom α.toRingHom) ≫ dualNumberBasePoint f x := by
      rw [hbase, ← happly, ← hzero, ht]
    have : IsIso (Spec.map (CommRingCat.ofHom α.toRingHom)) := by
      have : IsIso (CommRingCat.ofHom α.toRingHom) :=
        ⟨CommRingCat.ofHom α.symm.toRingHom, ofHom_dualNumberCongr_comp_symm e,
          ofHom_dualNumberCongr_symm_comp e⟩
      infer_instance
    exact (cancel_epi (Spec.map (CommRingCat.ofHom α.toRingHom))).mp hv
  · rw [happly, hzero, ht, hbase]

/-- **The kernel of the tangent map of `f` at `x` is the relative tangent space of `X` over `Y`
at `x`.** Hence the tangent map is injective exactly when that space vanishes. -/
lemma injective_tangentMap_iff_subsingleton (h : f ≫ q = p) [IsIso (f.residueFieldMap x)] :
    Function.Injective (tangentMap f p q h x) ↔ Subsingleton (DottedTangentArrow f x) := by
  refine ⟨fun hinj => ⟨fun θ η => ?_⟩, fun hsub θ η hθη => ?_⟩
  · have key (ν : DottedTangentArrow f x) :
        tangentMap f p q h x (dottedTangentArrowOverBase f p q x h ν) = 0 :=
      (tangentMap_eq_zero_iff f p q x h _).2 ν.property.2
    exact Subtype.ext (congrArg (·.val) (hinj ((key θ).trans (key η).symm)))
  · have hzero : tangentMap f p q h x (θ - η) = 0 := by rw [map_sub, hθη, sub_self]
    let δ : DottedTangentArrow f x :=
      ⟨(θ - η).val, (θ - η).property.1, (tangentMap_eq_zero_iff f p q x h (θ - η)).1 hzero⟩
    have hv : δ.val = (0 : DottedTangentArrow f x).val :=
      congrArg Subtype.val (Subsingleton.elim δ 0)
    rw [(dottedTangentArrowModule f x).zero_apply] at hv
    refine sub_eq_zero.mp (Subtype.ext ?_)
    rwa [(dottedTangentArrowModule p x).zero_apply]

/-- **Stacks Project, Tag 0B2G.** Let `f : X ⟶ Y` be a morphism of schemes over `S`, locally of
finite type, and let `x` be a point of `X` whose residue field agrees with that of `f x`. Then
the tangent map `d f : T_{X/S, x} ⟶ T_{Y/S, f x}` is injective if and only if `f` is unramified
at `x`. -/
@[stacks 0B2G]
theorem injective_tangentMap_iff_unramifiedAt (h : f ≫ q = p) [LocallyOfFiniteType f]
    [IsIso (f.residueFieldMap x)] :
    Function.Injective (tangentMap f p q h x) ↔ UnramifiedAt f x :=
  (injective_tangentMap_iff_subsingleton f p q x h).trans
    (subsingleton_dottedTangentArrow_iff_unramifiedAt f x)

/-- **Stacks Project, Tag 0B2G** under the hypotheses of the source: for `X` locally of finite
type over `S`, the tangent map of a morphism `f : X ⟶ Y` over `S` is injective at a point where
the residue field is unchanged if and only if `f` is unramified there. Local finite type of `f`
itself is Tag 01T8. -/
@[stacks 0B2G "with the source locally of finite type over the base"]
theorem injective_tangentMap_iff_unramifiedAt_of_locallyOfFiniteType_base (h : f ≫ q = p)
    [LocallyOfFiniteType p] [IsIso (f.residueFieldMap x)] :
    Function.Injective (tangentMap f p q h x) ↔ UnramifiedAt f x :=
  have : LocallyOfFiniteType (f ≫ q) := h ▸ inferInstance
  have : LocallyOfFiniteType f := LocallyOfFiniteType.of_comp this
  injective_tangentMap_iff_unramifiedAt f p q x h

end Kernel

end AlgebraicGeometry

end
