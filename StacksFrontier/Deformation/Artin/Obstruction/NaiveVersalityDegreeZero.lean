module

public import StacksFrontier.Deformation.Artin.Infinitesimal.SiteContainment
public import StacksFrontier.Deformation.Artin.Obstruction.NaiveVersalityDerivedFibre
public import StacksFrontier.Deformation.Artin.Obstruction.NaiveVersalityFieldVersalLift
public import StacksFrontier.Deformation.Artin.Obstruction.NaiveVersalityTangentFactorization
public import StacksFrontier.RingTheory.LocalRing.ResidueFieldCardinality

/-!
# Stacks 07YM, the direction `(1) ⇒ (2)` in degree zero

Let `x` be a family over `Spec A` whose tangent theory is represented by `ξ : E ⟶ NL_{A/Λ}` in
the sense of hypothesis (ii) of Stacks 07YM, and let `u₀` be a point of `Spec A` with residue
field `κ`. This file proves that versality of `x` at `u₀` forces condition (2) in degree `0`:
the map `H^0(E ⊗ᴸ_A κ) ⟶ H^0(NL_{A/Λ} ⊗ᴸ_A κ)` is injective.

Both halves of the implication are already available. On the versality side,
`Deformation.Artin.liftsAtResiduePoint_of_isVersalAt` reads versality as the lifting property
at the residue-field point and
`Deformation.Artin.surjective_canonicalTangentMap_of_liftsAtResiduePoint` turns it into the
surjectivity of the map `Der_Λ(A, k) ⟶ T_x(k)` on tangent spaces. On the `Ext` side,
`Deformation.Artin.injective_derivedTensorFibre_zero_iff_surjective_comp` reads condition (2)
in degree `0` as the surjectivity of precomposition with `ξ` on morphisms into `k[0]`. What
joins them is this file's two steps.

First, the coefficient modules differ. Condition (2) is stated with coefficients in `ULift k`,
restricted along `A ⟶ k`, because `Ext` is formed in a module universe above that of the ring;
the lift chain is stated with coefficients in the `A`-module `ModuleCat.of A (ULift k)`. These
have the same carrier and the same action, but not definitionally: restriction of scalars
multiplies by `algebraMap A k a`, the algebra structure of `ULift k` acts through the `A`-action
on `k`, and the two agree by `Algebra.smul_def`. So the identification has to be built.

Second, the lift chain is written for a field that is a site module, and the residue field has
to be put in the site. This is a cardinality estimate: the residue field at a prime of `A` is
no larger than `A` (`Cardinal.mk_residueField_le_max`), and the site's cutoff is a strong
prelimit above `ℵ₀`, hence closed under the bound (`Deformation.Artin.contains_spec_of_mk_le`).
The three memberships the lift chain asks for are *derived* this way rather than assumed: the
statement of the tag carries no such hypothesis.

## Main definitions

* `Deformation.Artin.uliftRestrictScalarsEquiv` and
  `Deformation.Artin.uliftRestrictScalarsIso` — the identification of `ULift k` as an
  `A`-module through its algebra structure with its restriction of scalars from `k`.

## Main results

* `CategoryTheory.surjective_comp_of_iso` — surjectivity of precomposition with a morphism,
  transported along an isomorphism of the target.
* `Deformation.Artin.surjective_comp_of_liftsAtResiduePoint` — versality makes precomposition
  with `ξ` surjective on morphisms `NL_{A/Λ} ⟶ k[0]`.
* `Deformation.Artin.injective_derivedTensorFibre_zero_of_liftsAtResiduePoint` — the same,
  turned back into condition (2) in degree `0` with coefficients in a field small enough to
  lie in the site.
* `Deformation.Artin.injective_derivedTensorFibre_zero_of_isVersalAt` — **the direction
  `(1) ⇒ (2)` of Stacks 07YM in degree `0`**: versality at `u₀` implies that
  `H^0(ξ ⊗ᴸ_A κ(u₀))` is injective.

## Implementation notes

The `Λ`-algebra structure of the coefficient field and its compatibility with the `A`-algebra
structure are not hypotheses: the composite `Λ ⟶ A ⟶ k` is the only candidate and it is
introduced inside the proof, so the statements quantify over an `A`-algebra only.

As in `Deformation.Artin.exists_extends_of_liftsAtResiduePoint` the dual numbers are formed for
an abstract module and instantiated afterwards; here the abstract module is `ULift k` over
`ULift k`, whose right action is the site's.

## References

* [Stacks Project, Tag 07YM](https://stacks.math.columbia.edu/tag/07YM)
* [Stacks Project, Tag 07YC](https://stacks.math.columbia.edu/tag/07YC)
* [Stacks Project, Tag 07YK](https://stacks.math.columbia.edu/tag/07YK)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u v

/-- Whether precomposition with a fixed morphism `ξ : E ⟶ N` is surjective on morphisms into
an object depends on that object only up to isomorphism. -/
public theorem CategoryTheory.surjective_comp_of_iso {C : Type*} [Category C] {E N : C}
    (ξ : E ⟶ N) {Y Y' : C} (e : Y ≅ Y')
    (h : Function.Surjective (fun f : N ⟶ Y' => ξ ≫ f)) :
    Function.Surjective (fun f : N ⟶ Y => ξ ≫ f) := by
  intro g
  obtain ⟨f, hf⟩ := h (g ≫ e.hom)
  have hf' : ξ ≫ f = g ≫ e.hom := hf
  refine ⟨f ≫ e.inv, ?_⟩
  change ξ ≫ f ≫ e.inv = g
  rw [← Category.assoc, hf', Category.assoc, e.hom_inv_id, Category.comp_id]

namespace Deformation.Artin

attribute [local instance] HasDerivedCategory.standard

/-! ### `ULift` of an algebra as a module over the base ring -/

section UliftModule

variable (A k : Type u) [CommRing A] [CommRing k] [Algebra A k]

/-- `ULift k`, as an `A`-module through the `A`-algebra structure of `ULift k`, is `ULift k` as
a `k`-module with its scalars restricted along `A ⟶ k`.

The two module structures have the same carrier and the same action but are not definitionally
equal: restriction of scalars multiplies by `algebraMap A k a`, whereas the algebra structure
of `ULift k` acts through the `A`-action on `k`, and the two agree by `Algebra.smul_def`. -/
public def uliftRestrictScalarsEquiv :
    ((ModuleCat.restrictScalars (algebraMap A k)).obj
      (ModuleCat.of k (ULift.{u} k)) : Type u) ≃ₗ[A] ULift.{u} k where
  toFun := id
  map_add' _ _ := rfl
  map_smul' a y := by
    apply ULift.down_injective
    change algebraMap A k a * y.down = a • y.down
    rw [Algebra.smul_def]
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl

/-- `Deformation.Artin.uliftRestrictScalarsEquiv` as an isomorphism of the category of
`A`-modules. -/
public def uliftRestrictScalarsIso :
    (ModuleCat.restrictScalars (algebraMap A k)).obj (ModuleCat.of k (ULift.{u} k)) ≅
      ModuleCat.of A (ULift.{u} k) where
  hom := ModuleCat.ofHom
    (X := (ModuleCat.restrictScalars (algebraMap A k)).obj (ModuleCat.of k (ULift.{u} k)))
    (Y := ModuleCat.of A (ULift.{u} k)) (uliftRestrictScalarsEquiv A k).toLinearMap
  inv := ModuleCat.ofHom
    (X := ModuleCat.of A (ULift.{u} k))
    (Y := (ModuleCat.restrictScalars (algebraMap A k)).obj (ModuleCat.of k (ULift.{u} k)))
    (uliftRestrictScalarsEquiv A k).symm.toLinearMap
  hom_inv_id := rfl
  inv_hom_id := rfl

end UliftModule

/-! ### Surjectivity of precomposition with `ξ`, from versality -/

section SurjectiveComp

variable (Λ A k : Type u) [CommRing Λ] [CommRing A] [Field k] [Algebra Λ A] [Algebra A k]
  [Algebra Λ k] [IsScalarTower Λ A k]
variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (toS : Spec (.of A) ⟶ S) (hA : B.Contains (Spec (.of A))) (hAk : B.Contains (Spec (.of k)))
variable {X : Type v} [Category X] (p : X ⥤ BigFppfOver B S hS) (x : X)
  (hx : p.obj x = algebraOver A B S hS toS hA)
  (hxS : (p ⋙ Over.post B.inclusion).obj x = Over.mk toS)
  (hp : p.IsFiberedInGroupoids) (hRS : SatisfiesRSStar B S hS p hp)
  (hΩ : B.Contains (Spec (squareZeroRing A (differentialsModule Λ A))))
  (hk : B.Contains (Spec (squareZeroRing A (ModuleCat.of A k))))
  (hkk : B.Contains (Spec (squareZeroRing k (ModuleCat.of k k))))
  (baseMap : Spec (.of Λ) ⟶ S)
  (baseFactorization : Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ baseMap = toS)
variable (E : DerivedCategory (ModuleCat.{u} A))
  (ξ : E ⟶ derivedNaiveCotangentComplex Λ A)
  (tangentEquiv : ∀ M : SiteModule A B,
    ((tangentFunctor A B S hS toS hA p x hx hp hRS).functor.obj M : Type _) ≃+
      (E ⟶ (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M.obj))
  (tangentEquiv_natural : ∀ {M N : SiteModule A B} (f : M ⟶ N)
    (z : (tangentFunctor A B S hS toS hA p x hx hp hRS).functor.obj M),
    tangentEquiv N ((tangentFunctor A B S hS toS hA p x hx hp hRS).functor.map f z) =
      tangentEquiv M z ≫ (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).map f.hom)
  (tangentEquiv_canonical : tangentEquiv (differentialsSiteModule Λ A B hΩ)
      (canonicalDeformationElement Λ A B S hS toS hA p x hx hp hRS hΩ baseMap
        baseFactorization).element =
      ξ ≫ naiveCotangentToDifferentials Λ A)
variable (R : Type u) [CommRing R] [Algebra R k] (iR : Spec (.of R) ⟶ S)
  (hiR : Spec.map (CommRingCat.ofHom (algebraMap R k)) ≫ iR =
    Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ toS)

include hAk hxS hRS hΩ hk hkk baseFactorization hiR tangentEquiv_natural
  tangentEquiv_canonical in
/-- **Stacks 07YM, the surjectivity hypothesis (ii) turns versality into.** If the lifting
property defining versality holds at the point of `Spec A` determined by the `A`-algebra
structure of a field `k`, then precomposition with `ξ` is surjective on morphisms
`NL_{A/Λ} ⟶ k[0]` of `D(A)`.

This is `Deformation.Artin.surjective_canonicalTangentMap_of_liftsAtResiduePoint`, the
surjectivity of the map `Der_Λ(A, k) ⟶ T_x(k)` on tangent spaces, read through the functorial
isomorphism of hypothesis (ii): by
`Deformation.Artin.tangentEquiv_canonicalTangentMap` that isomorphism carries the image of a
tangent vector `θ` to `ξ` followed by the augmentation followed by `θ`, so a surjection onto
`T_x(k)` becomes a surjection onto the morphisms `E ⟶ k[0]` factoring through `ξ`. The two
identifications of `T_x(k)` with classes of lifts are bijections, so the surjectivity of the
composite in that statement is the surjectivity of the tangent map itself. -/
@[stacks 07YM "(1) implies (2), degree 0: precomposition with xi is surjective"]
public theorem surjective_comp_of_liftsAtResiduePoint [Mono baseMap]
    (hlifts : LiftsAtResiduePoint (Λ := R) (k := k) iR (p ⋙ Over.post B.inclusion)
      (Over.mk toS) x hxS (Spec.map (CommRingCat.ofHom (algebraMap A k)))) :
    Function.Surjective (fun f : derivedNaiveCotangentComplex Λ A ⟶
        (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A k) =>
      ξ ≫ f) := by
  let : p.IsFibered := hp.isFibered
  intro g
  obtain ⟨θ, hθ⟩ := surjective_canonicalTangentMap_of_liftsAtResiduePoint Λ A k B S hS toS hA
    hAk p x hx hxS hp hRS hΩ hk hkk baseMap baseFactorization R iR hiR hlifts
    (canonicalFieldBaseChangeEquiv A k B S hS toS hA p x hx hp hRS hk hAk hkk
      ((tangentFunctor A B S hS toS hA p x hx hp hRS).liftEquiv
        (⟨ModuleCat.of A k, hk⟩ : SiteModule A B)
        ((tangentEquiv (⟨ModuleCat.of A k, hk⟩ : SiteModule A B)).symm g)))
  have hz : canonicalTangentMap Λ A k B S hS toS hA p x hx hp hRS hΩ hk baseMap
      baseFactorization θ =
      (tangentEquiv (⟨ModuleCat.of A k, hk⟩ : SiteModule A B)).symm g :=
    ((tangentFunctor A B S hS toS hA p x hx hp hRS).liftEquiv
      (⟨ModuleCat.of A k, hk⟩ : SiteModule A B)).injective
      ((canonicalFieldBaseChangeEquiv A k B S hS toS hA p x hx hp hRS hk hAk hkk).injective hθ)
  refine ⟨naiveCotangentToDifferentials Λ A ≫
    (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).map (ModuleCat.ofHom θ), ?_⟩
  have hfac := tangentEquiv_canonicalTangentMap Λ A k B S hS toS hA p x hx hp hRS hΩ hk baseMap
    baseFactorization E ξ tangentEquiv tangentEquiv_natural tangentEquiv_canonical θ
  rw [hz, AddEquiv.apply_symm_apply] at hfac
  exact hfac.symm

end SurjectiveComp

/-! ### Condition (2) in degree zero -/

section DegreeZero

variable (Λ A k : Type u) [CommRing Λ] [CommRing A] [Field k] [Algebra Λ A] [Algebra A k]
variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (toS : Spec (.of A) ⟶ S) (hA : B.Contains (Spec (.of A)))
variable {X : Type v} [Category X] (p : X ⥤ BigFppfOver B S hS) (x : X)
  (hx : p.obj x = algebraOver A B S hS toS hA)
  (hxS : (p ⋙ Over.post B.inclusion).obj x = Over.mk toS)
  (hp : p.IsFiberedInGroupoids) (hRS : SatisfiesRSStar B S hS p hp)
  (hΩ : B.Contains (Spec (squareZeroRing A (differentialsModule Λ A))))
  (baseMap : Spec (.of Λ) ⟶ S)
  (baseFactorization : Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ baseMap = toS)
variable (E : DerivedCategory (ModuleCat.{u} A))
  (hE : (DerivedCategory.TStructure.t (C := ModuleCat.{u} A)).minus E)
  (ξ : E ⟶ derivedNaiveCotangentComplex Λ A)
  (tangentEquiv : ∀ M : SiteModule A B,
    ((tangentFunctor A B S hS toS hA p x hx hp hRS).functor.obj M : Type _) ≃+
      (E ⟶ (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M.obj))
  (tangentEquiv_natural : ∀ {M N : SiteModule A B} (f : M ⟶ N)
    (z : (tangentFunctor A B S hS toS hA p x hx hp hRS).functor.obj M),
    tangentEquiv N ((tangentFunctor A B S hS toS hA p x hx hp hRS).functor.map f z) =
      tangentEquiv M z ≫ (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).map f.hom)
  (tangentEquiv_canonical : tangentEquiv (differentialsSiteModule Λ A B hΩ)
      (canonicalDeformationElement Λ A B S hS toS hA p x hx hp hRS hΩ baseMap
        baseFactorization).element =
      ξ ≫ naiveCotangentToDifferentials Λ A)
variable (R : Type u) [CommRing R] [algRk : Algebra R k] (iR : Spec (.of R) ⟶ S)
  (hiR : Spec.map (CommRingCat.ofHom (algebraMap R k)) ≫ iR =
    Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ toS)
  (T : DerivedTensorProduct A)

include hxS hRS hΩ baseFactorization hE hiR tangentEquiv_natural tangentEquiv_canonical in
/-- **Stacks 07YM, condition (2) in degree `0` from the lifting property.** If the lifting
property defining versality holds at the point of `Spec A` determined by the `A`-algebra
structure of a field `k` no larger than `max ℵ₀ #A`, then the map
`H^0(E ⊗ᴸ_A k) ⟶ H^0(NL_{A/Λ} ⊗ᴸ_A k)` is injective.

`Deformation.Artin.injective_derivedTensorFibre_zero_iff_surjective_comp` turns the conclusion
into the surjectivity of precomposition with `ξ` on morphisms into `ULift k`, restricted along
`A ⟶ k`; `Deformation.Artin.uliftRestrictScalarsIso` identifies that coefficient module with
the `A`-module `ULift k`, at which
`Deformation.Artin.surjective_comp_of_liftsAtResiduePoint` supplies the surjectivity. The
lifting property is moved from `k` to `ULift k` by
`Deformation.Artin.liftsAtResiduePoint_changeResidueField`, and the three memberships in the
site that the lift chain asks of `ULift k` are derived from the cardinality bound. -/
@[stacks 07YM "(1) implies (2), degree 0, at a field in the site"]
public theorem injective_derivedTensorFibre_zero_of_liftsAtResiduePoint [Mono baseMap]
    (hmk : Cardinal.mk k ≤ max Cardinal.aleph0 (Cardinal.mk A))
    (hlifts : LiftsAtResiduePoint (Λ := R) (k := k) iR (p ⋙ Over.post B.inclusion)
      (Over.mk toS) x hxS (Spec.map (CommRingCat.ofHom (algebraMap A k)))) :
    Function.Injective
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
        ((T.tensor.flip.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
            (ModuleCat.of A k))).map ξ)) := by
  let : Algebra Λ k := ((algebraMap A k).comp (algebraMap Λ A)).toAlgebra
  have : IsScalarTower Λ A k := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hmkU : Cardinal.mk (ULift.{u} k) ≤ max Cardinal.aleph0 (Cardinal.mk A) := by
    simpa using hmk
  have hAk : B.Contains (Spec (.of (ULift.{u} k))) := contains_spec_of_mk_le B hA _ hmkU
  have hk : B.Contains (Spec (squareZeroRing A (ModuleCat.of A (ULift.{u} k)))) :=
    contains_spec_squareZeroRing_of_mk_le B hA A _ (le_max_right _ _) hmkU
  have hkk : B.Contains (Spec (squareZeroRing (ULift.{u} k)
      (ModuleCat.of (ULift.{u} k) (ULift.{u} k)))) :=
    contains_spec_squareZeroRing_of_mk_le B hA (ULift.{u} k) _ hmkU hmkU
  let e : k ≃ₐ[R] ULift.{u} k := (ULift.algEquiv (R := R) (A := k)).symm
  have halg (R' : Type u) [CommRing R'] [Algebra R' k] :
      CommRingCat.ofHom (algebraMap R' k) ≫ CommRingCat.ofHom e.toAlgHom.toRingHom =
        CommRingCat.ofHom (algebraMap R' (ULift.{u} k)) := by
    ext t
    rfl
  have hiR' : Spec.map (CommRingCat.ofHom (algebraMap R (ULift.{u} k))) ≫ iR =
      Spec.map (CommRingCat.ofHom (algebraMap A (ULift.{u} k))) ≫ toS := by
    rw [← halg A, ← halg R, Spec.map_comp, Spec.map_comp, Category.assoc, Category.assoc, hiR]
  have hlifts' : LiftsAtResiduePoint (Λ := R) (k := ULift.{u} k) iR
      (p ⋙ Over.post B.inclusion) (Over.mk toS) x hxS
      (Spec.map (CommRingCat.ofHom (algebraMap A (ULift.{u} k)))) := by
    have h := liftsAtResiduePoint_changeResidueField e iR (p ⋙ Over.post B.inclusion)
      (Over.mk toS) x hxS (Spec.map (CommRingCat.ofHom (algebraMap A k))) hlifts
    rwa [← Spec.map_comp, halg A] at h
  rw [injective_derivedTensorFibre_zero_iff_surjective_comp T E hE ξ]
  refine CategoryTheory.surjective_comp_of_iso ξ
    ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).mapIso
      (uliftRestrictScalarsIso A k)) ?_
  exact surjective_comp_of_liftsAtResiduePoint Λ A (ULift.{u} k) B S hS toS hA hAk p x hx hxS
    hp hRS hΩ hk hkk baseMap baseFactorization E ξ tangentEquiv tangentEquiv_natural
    tangentEquiv_canonical R iR hiR' hlifts'

end DegreeZero

/-! ### Condition (2) in degree zero, from versality at a point -/

section VersalDegreeZero

variable (Λ A : Type u) [CommRing Λ] [CommRing A] [Algebra Λ A]
variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (toS : Spec (.of A) ⟶ S) (hA : B.Contains (Spec (.of A)))
variable {X : Type v} [Category X] (p : X ⥤ BigFppfOver B S hS) (x : X)
  (hx : p.obj x = algebraOver A B S hS toS hA)
  (hp : p.IsFiberedInGroupoids) (hRS : SatisfiesRSStar B S hS p hp)
  (hΩ : B.Contains (Spec (squareZeroRing A (differentialsModule Λ A))))
  (baseMap : Spec (.of Λ) ⟶ S)
  (baseFactorization : Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ baseMap = toS)
variable (E : DerivedCategory (ModuleCat.{u} A))
  (hE : (DerivedCategory.TStructure.t (C := ModuleCat.{u} A)).minus E)
  (ξ : E ⟶ derivedNaiveCotangentComplex Λ A)
  (tangentEquiv : ∀ M : SiteModule A B,
    ((tangentFunctor A B S hS toS hA p x hx hp hRS).functor.obj M : Type _) ≃+
      (E ⟶ (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M.obj))
  (tangentEquiv_natural : ∀ {M N : SiteModule A B} (f : M ⟶ N)
    (z : (tangentFunctor A B S hS toS hA p x hx hp hRS).functor.obj M),
    tangentEquiv N ((tangentFunctor A B S hS toS hA p x hx hp hRS).functor.map f z) =
      tangentEquiv M z ≫ (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).map f.hom)
  (tangentEquiv_canonical : tangentEquiv (differentialsSiteModule Λ A B hΩ)
      (canonicalDeformationElement Λ A B S hS toS hA p x hx hp hRS hΩ baseMap
        baseFactorization).element =
      ξ ≫ naiveCotangentToDifferentials Λ A)
variable (u₀ : Spec (.of A)) (T : DerivedTensorProduct A)

include hRS hΩ baseFactorization hE tangentEquiv_natural tangentEquiv_canonical in
/-- **Stacks 07YM, `(1) ⇒ (2)` in degree `0`.** Let `x` be a family over `Spec A` whose tangent
theory is represented by `ξ : E ⟶ NL_{A/Λ}` as in hypothesis (ii) of the tag. If `x` is versal
at a point `u₀` of `Spec A`, then the map
`H^0(E ⊗ᴸ_A κ(u₀)) ⟶ H^0(NL_{A/Λ} ⊗ᴸ_A κ(u₀))` on the derived fibre at `u₀` is injective.

Versality is the lifting property at the residue-field point
(`Deformation.Artin.liftsAtResiduePoint_of_isVersalAt`), the residue field at a prime of `A` is
no larger than `max ℵ₀ #A` (`Cardinal.mk_residueField_le_max`), and
`Deformation.Artin.specMap_primeResidueFieldAlgebra_comp_fromSpecStalk` is the compatibility of
the residue-field point with the local ring of `S` at the image of `u₀`; with those,
`Deformation.Artin.injective_derivedTensorFibre_zero_of_liftsAtResiduePoint` applies.

No closedness of the point is used: the source invokes closedness only for the `H^{-1}` half of
condition (2). -/
@[stacks 07YM "(1) implies (2), degree 0"]
public theorem injective_derivedTensorFibre_zero_of_isVersalAt [Mono baseMap]
    (hversal : IsVersalAt (Over.mk toS) (p ⋙ Over.post B.inclusion) u₀ x
      (by change (Over.post B.inclusion).obj (p.obj x) = _; rw [hx]; rfl)) :
    Function.Injective
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
        ((T.tensor.flip.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
            (ModuleCat.of A u₀.asIdeal.ResidueField))).map ξ)) := by
  have hxS : (p ⋙ Over.post B.inclusion).obj x = Over.mk toS := by
    change (Over.post B.inclusion).obj (p.obj x) = _
    rw [hx]
    rfl
  exact injective_derivedTensorFibre_zero_of_liftsAtResiduePoint
    (algRk := primeResidueFieldAlgebra toS u₀) Λ A u₀.asIdeal.ResidueField
    B S hS toS hA p x hx hxS hp hRS hΩ baseMap baseFactorization E hE ξ tangentEquiv
    tangentEquiv_natural tangentEquiv_canonical
    (S.presheaf.stalk (basePoint (Over.mk toS) u₀))
    (S.fromSpecStalk (basePoint (Over.mk toS) u₀))
    (specMap_primeResidueFieldAlgebra_comp_fromSpecStalk toS u₀) T
    (Cardinal.mk_residueField_le_max u₀.asIdeal)
    (liftsAtResiduePoint_of_isVersalAt toS u₀ (p ⋙ Over.post B.inclusion) x hxS hversal)

end VersalDegreeZero

end Deformation.Artin
