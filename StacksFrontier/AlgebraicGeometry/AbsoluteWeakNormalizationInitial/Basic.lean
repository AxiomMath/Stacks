module

public import StacksFrontier.AlgebraicGeometry.Scheme.AffineZariskiRestriction
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.IsIso
public import Mathlib.AlgebraicGeometry.RelativeGluing
public import Mathlib.AlgebraicGeometry.Sites.SmallAffineZariski
public import StacksFrontier.AlgebraicGeometry.AbsoluteWeakNormalizationBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Defs.TwoOutOfThree
public import StacksFrontier.AlgebraicGeometry.Morphisms.WeakNormalization.Initial
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningMorphism.Topological

/-!
# Absolute weak normalization of a scheme

For a scheme `X`, consider schemes over `X` whose structure morphism is a universal
homeomorphism. This category has an initial object, the absolute weak normalization of `X`,
which remains initial after restriction to any open subscheme.

## Main results

* `AlgebraicGeometry.hasInitialUniversalHomeomorphismOver` is that statement, in the form of
  the class `AlgebraicGeometry.HasLocallyInitialUniversalHomeomorphismOver`.

## Implementation notes

The construction is affine-local on `X` and glued.  On an affine open `U` the candidate is the
spectrum of the ring-level absolute weak normalization of `Γ(X, U)`, and its functoriality
(`AlgebraicGeometry.existsUnique_absoluteWeakNormalizationMap`) makes these fit together into a
diagram over the small affine Zariski site of `X`, with the base-change statement
(`AlgebraicGeometry.exists_absoluteWeakNormalization_tensorProduct_equiv`) supplying the
coequifiberedness that `AlgebraicGeometry.Scheme.RelativeGluingData` requires.  The glued scheme
is a universal homeomorphism over `X` because being one is Zariski-local at the target, and it
is absolutely weakly normal because that is affine-local and holds on each chart by the
characterization of Tag 0EUR.

Initiality is then uniqueness of a map into an arbitrary universal homeomorphism `Z ⟶ X`,
proved chart by chart: over an affine open the target is affine, so the map is the ring-level
terminal map, and the ring-level universal property also gives its uniqueness.  The restriction
clause of the class follows because the pullback of the glued object along an open immersion is
absolutely weakly normal and a universal homeomorphism over the open subscheme, and any two such
initial objects are identified by the two-out-of-three property of universal homeomorphisms
together with the isomorphism criterion proved here.

Everything lives in a single universe `u`, as `AlgebraicGeometry.UniversalHomeomorphism` is
available only for `Scheme.{u}`.

No hypothesis beyond those of Tag 0EUS is used: `X` is an arbitrary scheme.

## References

* [Stacks Project, Tag 0EUR](https://stacks.math.columbia.edu/tag/0EUR)
* [Stacks Project, Tag 0EUS](https://stacks.math.columbia.edu/tag/0EUS)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry



attribute [local instance 2000] CategoryTheory.CategoryStruct.toQuiver

section Proof

open MorphismProperty
open TopologicalSpace
open Scheme.AffineZariskiSite

open Algebra
open scoped TensorProduct
attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- The commutative ring structure on the absolute weak normalization of the ring `A`. -/
noncomputable local instance absoluteWeakNormalization_commRing (A : Type u) [CommRing A] :
    CommRing (AbsoluteWeakNormalization A) :=
  (absoluteWeakNormalizationCategoryObject A).1.commRing

/-- The `A`-algebra structure on the absolute weak normalization of the ring `A`. -/
noncomputable local instance absoluteWeakNormalization_algebra (A : Type u) [CommRing A] :
    Algebra A (AbsoluteWeakNormalization A) :=
  (absoluteWeakNormalizationCategoryObject A).1.algebra

private noncomputable def awnMap {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) : AbsoluteWeakNormalization A →+* AbsoluteWeakNormalization B :=
  Classical.choose (existsUnique_absoluteWeakNormalizationMap φ)

private theorem awnMap_spec {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) :
    (awnMap φ).comp (algebraMap A (AbsoluteWeakNormalization A)) =
      (algebraMap B (AbsoluteWeakNormalization B)).comp φ :=
  (Classical.choose_spec (existsUnique_absoluteWeakNormalizationMap φ)).1

private theorem awnMap_unique {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (ψ : AbsoluteWeakNormalization A →+* AbsoluteWeakNormalization B)
    (hψ : ψ.comp (algebraMap A (AbsoluteWeakNormalization A)) =
      (algebraMap B (AbsoluteWeakNormalization B)).comp φ) :
    ψ = awnMap φ :=
  (Classical.choose_spec (existsUnique_absoluteWeakNormalizationMap φ)).2 ψ hψ

private theorem awnMap_id (A : Type u) [CommRing A] :
    awnMap (RingHom.id A) = RingHom.id (AbsoluteWeakNormalization A) :=
  (awnMap_unique (RingHom.id A) (RingHom.id _) (by simp)).symm

private theorem awnMap_comp {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (φ : A →+* B) (ψ : B →+* C) :
    awnMap (ψ.comp φ) = (awnMap ψ).comp (awnMap φ) := by
  symm
  apply awnMap_unique (ψ.comp φ) ((awnMap ψ).comp (awnMap φ))
  rw [RingHom.comp_assoc, awnMap_spec, ← RingHom.comp_assoc, awnMap_spec]
  rfl

private noncomputable def awnAffineDiagram (X : Scheme.{u}) :
    X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat.{u} where
  obj U := CommRingCat.of (AbsoluteWeakNormalization Γ(X, U.unop.1))
  map {V U} i := CommRingCat.ofHom (awnMap (restrictionRingMap X i.unop))
  map_id U := by
    apply CommRingCat.hom_ext
    change awnMap (restrictionRingMap X (𝟙 (Opposite.unop U))) = _
    rw [restrictionRingMap_id, awnMap_id]
    simp
  map_comp i j := by
    apply CommRingCat.hom_ext
    change awnMap (restrictionRingMap X ((i ≫ j).unop)) =
      (awnMap (restrictionRingMap X j.unop)).comp
        (awnMap (restrictionRingMap X i.unop))
    rw [show (i ≫ j).unop = j.unop ≫ i.unop by rfl,
      restrictionRingMap_comp, ← awnMap_comp]

private noncomputable def awnAffineDiagramMap (X : Scheme.{u}) :
    (toOpensFunctor X).op ⋙ X.presheaf ⟶ awnAffineDiagram X where
  app U := CommRingCat.ofHom (algebraMap Γ(X, U.unop.1) (AbsoluteWeakNormalization Γ(X, U.unop.1)))
  naturality {_ _} i := CommRingCat.hom_ext (awnMap_spec (restrictionRingMap X i.unop)).symm

private theorem awnAffineDiagramMap_coequifibered (X : Scheme.{u}) :
    (awnAffineDiagramMap X).Coequifibered := by
  refine coequifibered_iff_forall_isLocalizationAway.mpr fun U r ↦ ?_
  let A := Γ(X, U.1)
  let B := Γ(X, X.basicOpen r)
  let N := AbsoluteWeakNormalization A
  let N' := AbsoluteWeakNormalization B
  let : Algebra A B := Scheme.algebra_section_section_basicOpen r
  let φ : A →+* B := algebraMap A B
  let φ' : A →+* B := restrictionRingMap X (homOfLE (U.basicOpen_le r))
  have hφ : φ = φ' := by
    ext x
    rfl
  let : IsLocalization.Away r B := U.2.isLocalization_basicOpen r
  let : IsOpenImmersion
      (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A B)).op) :=
    IsOpenImmersion.of_isLocalization r
  let : Algebra A N := inferInstance
  let haux := exists_absoluteWeakNormalization_tensorProduct_equiv A B
  let e : (B ⊗[A] N) ≃+* N' := Classical.choose haux
  have he :
      (e.toRingHom.comp ((Algebra.TensorProduct.includeRight (R := A)
        (A := B) (B := N)).toRingHom)) = awnMap φ :=
    ((Classical.choose_spec haux).1).2
  have he' :
      (e.toRingHom.comp ((Algebra.TensorProduct.includeRight (R := A)
        (A := B) (B := N)).toRingHom)) = awnMap φ' := by
    rw [he, hφ]
  let : Algebra N N' :=
    ((awnAffineDiagram X).map (homOfLE (U.basicOpen_le r)).op).hom.toAlgebra
  let eAlg : (B ⊗[A] N) ≃ₐ[N] N' := AlgEquiv.ofRingEquiv (R := N) (f := e) fun n =>
    congrArg (fun f : N →+* N' => f n) he'
  let : IsLocalization.Away (algebraMap A N (r : A)) (B ⊗[A] N) := by
    infer_instance
  show IsLocalization.Away (algebraMap A N (r : A)) N'
  exact IsLocalization.isLocalization_of_algEquiv _ eAlg

private noncomputable def awnRelativeGluingData (X : Scheme.{u}) :=
  Scheme.AffineZariskiSite.relativeGluingData (awnAffineDiagramMap_coequifibered X)

private instance awnRelativeGluingData_isLocallyDirected (X : Scheme.{u}) :
    ((awnRelativeGluingData X).functor ⋙ Scheme.forget).IsLocallyDirected :=
  Scheme.Cover.RelativeGluingData.instIsLocallyDirectedI₀CompFunctorForgetOfIsThin ..

private theorem awnRelativeGluingData_local_universalHomeomorphism
    (X : Scheme.{u}) (U : X.AffineZariskiSite) :
    UniversalHomeomorphism ((awnRelativeGluingData X).natTrans.app U) := by
  constructor
  show (topologically @IsHomeomorph).universally
    (Scheme.Spec.map (CommRingCat.ofHom
      (algebraMap Γ(X, U.1) (AbsoluteWeakNormalization Γ(X, U.1)))).op ≫ U.2.isoSpec.inv)
  rw [MorphismProperty.cancel_right_of_respectsIso
    (P := (topologically @IsHomeomorph).universally) _ U.2.isoSpec.inv]
  exact (absoluteWeakNormalizationCategoryObject
    Γ(X, U.1)).property.universally_isHomeomorph

private theorem awnRelativeGluingData_toBase_universalHomeomorphism (X : Scheme.{u}) :
    UniversalHomeomorphism (awnRelativeGluingData X).toBase := by
  constructor
  rw [IsZariskiLocalAtTarget.iff_of_openCover
    (P := (topologically @IsHomeomorph).universally)
    (Scheme.AffineZariskiSite.directedCover X)]
  intro U
  have hPB := (awnRelativeGluingData X).isPullback_natTrans_ι_toBase U
  let : HasPullback (awnRelativeGluingData X).toBase
      ((Scheme.AffineZariskiSite.directedCover X).f U) := hPB.flip.hasPullback
  rw [Scheme.Cover.pullbackHom]
  let e : CategoryTheory.Arrow.mk (pullback.snd (awnRelativeGluingData X).toBase
        ((Scheme.AffineZariskiSite.directedCover X).f U)) ≅
    CategoryTheory.Arrow.mk ((awnRelativeGluingData X).natTrans.app U) :=
    CategoryTheory.Arrow.isoMk hPB.flip.isoPullback.symm (Iso.refl _) (by
      calc
        _ = pullback.snd (awnRelativeGluingData X).toBase
            ((Scheme.AffineZariskiSite.directedCover X).f U) :=
          hPB.flip.isoPullback_inv_snd
        _ = pullback.snd (awnRelativeGluingData X).toBase
            ((Scheme.AffineZariskiSite.directedCover X).f U) ≫ 𝟙 _ := by simp)
  exact (MorphismProperty.arrow_iso_iff _ e).2
    (awnRelativeGluingData_local_universalHomeomorphism X U).universally_isHomeomorph

private noncomputable def awnSchemeOver (X : Scheme.{u}) : Over X :=
  Over.mk (awnRelativeGluingData X).toBase

private theorem awnSchemeOver_property (X : Scheme.{u}) :
    UniversalHomeomorphism (awnSchemeOver X).hom :=
  awnRelativeGluingData_toBase_universalHomeomorphism X

private noncomputable def awnCandidateMapToAWN (A B : Type u) [CommRing A] [CommRing B]
    [Algebra A B]
    (hB : IsAbsoluteWeakNormalizationCandidate A (CommAlgCat.of A B)) :
    B →+* AbsoluteWeakNormalization A :=
  (((absoluteWeakNormalizationCategoryObject_isTerminal A).from
    ⟨CommAlgCat.of A B, hB⟩).hom.hom).toRingHom

private theorem awnCandidateMapToAWN_comp (A B : Type u) [CommRing A] [CommRing B]
    [Algebra A B]
    (hB : IsAbsoluteWeakNormalizationCandidate A (CommAlgCat.of A B)) :
    (awnCandidateMapToAWN A B hB).comp (algebraMap A B) =
      algebraMap A (AbsoluteWeakNormalization A) := by
  let f := (absoluteWeakNormalizationCategoryObject_isTerminal A).from
    (⟨CommAlgCat.of A B, hB⟩ : AbsoluteWeakNormalizationCategory A)
  show (f.hom.hom.toRingHom).comp (algebraMap A B) =
    algebraMap A (AbsoluteWeakNormalization A)
  ext a
  exact f.hom.hom.commutes a

private theorem awnCandidateMapToAWN_unique (A B : Type u) [CommRing A] [CommRing B]
    [Algebra A B]
    (hB : IsAbsoluteWeakNormalizationCandidate A (CommAlgCat.of A B))
    (ψ : B →+* AbsoluteWeakNormalization A)
    (hψ : ψ.comp (algebraMap A B) = algebraMap A (AbsoluteWeakNormalization A)) :
    ψ = awnCandidateMapToAWN A B hB := by
  let C : AbsoluteWeakNormalizationCategory A := ⟨CommAlgCat.of A B, hB⟩
  let t := absoluteWeakNormalizationCategoryObject_isTerminal A
  let eψ : B →ₐ[A] AbsoluteWeakNormalization A :=
    { toRingHom := ψ
      commutes' := fun a => congrArg (fun k : A →+* AbsoluteWeakNormalization A => k a) hψ }
  let g : C ⟶ absoluteWeakNormalizationCategoryObject A :=
    ObjectProperty.homMk (CommAlgCat.ofHom eψ)
  ext b
  exact congrArg (fun q => q.hom.hom b) (t.hom_ext g (t.from C))

/-- A universal homeomorphism is an affine morphism. -/
private theorem isAffineHom_of_universalHomeomorphism {X Y : Scheme.{u}} (f : Y ⟶ X)
    (hf : UniversalHomeomorphism f) : IsAffineHom f := by
  have hhomeo : (topologically @IsHomeomorph) f :=
    MorphismProperty.universally_le (topologically @IsHomeomorph) f hf.universally_isHomeomorph
  exact isAffineHom_of_isInducing f hhomeo.isInducing
    (hhomeo.surjective.range_eq ▸ isClosed_univ)

/-- The spectrum of the ring map `Γ(X, U) → Γ(f⁻¹ U, ⊤)` is the pullback projection up to the
affine identifications. -/
private theorem spec_map_pullback_snd_appTop {X Y : Scheme.{u}} (f : Y ⟶ X) [IsAffineHom f]
    (U : X.AffineZariskiSite) [IsAffine U.1.toScheme] :
    Scheme.Spec.map (CommRingCat.ofHom
      ((pullback.snd f U.1.ι).appTop.hom.comp U.1.topIso.inv.hom)).op =
      (pullback f U.1.ι).isoSpec.inv ≫ (pullback.snd f U.1.ι) ≫ U.1.toSpecΓ := by
  rw [CommRingCat.ofHom_comp, op_comp, Scheme.Spec.map_comp]
  have hnat : Scheme.Spec.map ((pullback.snd f U.1.ι).appTop).op ≫
      U.1.toScheme.isoSpec.inv =
      (pullback f U.1.ι).isoSpec.inv ≫ (pullback.snd f U.1.ι) :=
    Scheme.isoSpec_inv_naturality (pullback.snd f U.1.ι)
  calc
    _ = (Scheme.Spec.map ((pullback.snd f U.1.ι).appTop).op ≫
          U.1.toScheme.isoSpec.inv) ≫ U.1.toScheme.isoSpec.hom ≫
          Scheme.Spec.map (CommRingCat.ofHom U.1.topIso.inv.hom).op := by simp
    _ = ((pullback f U.1.ι).isoSpec.inv ≫ (pullback.snd f U.1.ι)) ≫
          U.1.toScheme.isoSpec.hom ≫
          Scheme.Spec.map (CommRingCat.ofHom U.1.topIso.inv.hom).op := by rw [hnat]
    _ = (pullback f U.1.ι).isoSpec.inv ≫ (pullback.snd f U.1.ι) ≫ U.1.toSpecΓ :=
        congrArg (fun g => (pullback f U.1.ι).isoSpec.inv ≫ (pullback.snd f U.1.ι) ≫ g)
          U.2.isoSpec_hom

private theorem awnLocalTarget_candidate {X Y : Scheme.{u}} (f : Y ⟶ X)
    (hf : UniversalHomeomorphism f) (U : X.AffineZariskiSite)
    (φ : Γ(X, U.1) →+* Γ(pullback f U.1.ι, ⊤))
    [Algebra Γ(X, U.1) Γ(pullback f U.1.ι, ⊤)]
    (hφ : algebraMap Γ(X, U.1) Γ(pullback f U.1.ι, ⊤) = φ)
    (hφ' : φ = (pullback.snd f U.1.ι).appTop.hom.comp U.1.topIso.inv.hom) :
    IsAbsoluteWeakNormalizationCandidate (Γ(X, U.1))
      (CommAlgCat.of (Γ(X, U.1)) (Γ(pullback f U.1.ι, ⊤))) := by
  let Z := pullback f U.1.ι
  have := isAffineHom_of_universalHomeomorphism f hf
  let : IsAffine U.1.toScheme := U.2
  let : IsAffine Z := inferInstance
  have hlocal : (topologically @IsHomeomorph).universally (pullback.snd f U.1.ι) :=
    MorphismProperty.pullback_snd f U.1.ι hf.universally_isHomeomorph
  have hspecEq := spec_map_pullback_snd_appTop f U
  have hright : IsIso U.1.toSpecΓ := by
    dsimp [Scheme.Opens.toSpecΓ]
    infer_instance
  constructor
  show (topologically @IsHomeomorph).universally
    (Scheme.Spec.map (CommRingCat.ofHom (algebraMap _ _)).op)
  rw [hφ, hφ', hspecEq]
  exact (MorphismProperty.cancel_left_of_respectsIso
    (P := (topologically @IsHomeomorph).universally) Z.isoSpec.inv _).mpr
      ((MorphismProperty.cancel_right_of_respectsIso
        (P := (topologically @IsHomeomorph).universally) (pullback.snd f U.1.ι)
          U.1.toSpecΓ).mpr hlocal)

private noncomputable def awnLocalMap {X Y : Scheme.{u}} (f : Y ⟶ X)
    (hf : UniversalHomeomorphism f) (U : X.AffineZariskiSite) :
    (awnRelativeGluingData X).functor.obj U ⟶ pullback f U.1.ι := by
  let A := Γ(X, U.1)
  let B := Γ(pullback f U.1.ι, ⊤)
  let Z := pullback f U.1.ι
  have := isAffineHom_of_universalHomeomorphism f hf
  let : IsAffine U.1.toScheme := U.2
  let : IsAffine Z := inferInstance
  let φ : A →+* B := (pullback.snd f U.1.ι).appTop.hom.comp U.1.topIso.inv.hom
  let : Algebra A B := φ.toAlgebra
  have hφ : algebraMap A B = φ := by simp [φ, RingHom.algebraMap_toAlgebra]
  have hB := awnLocalTarget_candidate f hf U φ hφ rfl
  let ψ := awnCandidateMapToAWN A B hB
  change Scheme.Spec.obj (Opposite.op (CommRingCat.of (AbsoluteWeakNormalization A))) ⟶ Z
  exact Scheme.Spec.map (CommRingCat.ofHom ψ).op ≫ (pullback f U.1.ι).isoSpec.inv

private theorem awnLocalMap_snd {X Y : Scheme.{u}} (f : Y ⟶ X)
    (hf : UniversalHomeomorphism f) (U : X.AffineZariskiSite) :
    awnLocalMap f hf U ≫ pullback.snd f U.1.ι =
      (awnRelativeGluingData X).natTrans.app U := by
  let A := Γ(X, U.1)
  let B := Γ(pullback f U.1.ι, ⊤)
  let Z := pullback f U.1.ι
  have := isAffineHom_of_universalHomeomorphism f hf
  let : IsAffine U.1.toScheme := U.2
  let : IsAffine Z := inferInstance
  let φ : A →+* B := (pullback.snd f U.1.ι).appTop.hom.comp U.1.topIso.inv.hom
  let : Algebra A B := φ.toAlgebra
  have hφ : algebraMap A B = φ := by simp [φ, RingHom.algebraMap_toAlgebra]
  have hB := awnLocalTarget_candidate f hf U φ hφ rfl
  let ψ := awnCandidateMapToAWN A B hB
  have hspec := spec_map_pullback_snd_appTop f U
  show Scheme.Spec.map (CommRingCat.ofHom ψ).op ≫ Z.isoSpec.inv ≫
      (pullback.snd f U.1.ι) =
    Scheme.Spec.map (CommRingCat.ofHom (algebraMap A (AbsoluteWeakNormalization A))).op ≫
      U.2.isoSpec.inv
  refine (cancel_mono U.2.isoSpec.hom).mp ?_
  calc
    _ = Scheme.Spec.map (CommRingCat.ofHom ψ).op ≫
          (Z.isoSpec.inv ≫ (pullback.snd f U.1.ι) ≫ U.1.toSpecΓ) := by
            simp [Category.assoc, U.2.isoSpec_hom]
    _ = Scheme.Spec.map (CommRingCat.ofHom ψ).op ≫ Scheme.Spec.map (CommRingCat.ofHom φ).op := by
          rw [← hspec]
    _ = Scheme.Spec.map (CommRingCat.ofHom (ψ.comp φ)).op := by
          rw [← Scheme.Spec.map_comp]
          congr 1
    _ = Scheme.Spec.map
          (CommRingCat.ofHom (algebraMap A (AbsoluteWeakNormalization A))).op := by
          rw [← hφ, show ψ.comp (algebraMap A B) = _ from awnCandidateMapToAWN_comp A B hB]
    _ = (Scheme.Spec.map
          (CommRingCat.ofHom (algebraMap A (AbsoluteWeakNormalization A))).op ≫
            U.2.isoSpec.inv) ≫ U.2.isoSpec.hom := by simp [Category.assoc]

private theorem awnLocalMap_unique {X Y : Scheme.{u}} (f : Y ⟶ X)
    (hf : UniversalHomeomorphism f) (U : X.AffineZariskiSite)
    (g : (awnRelativeGluingData X).functor.obj U ⟶ pullback f U.1.ι)
    (hg : g ≫ pullback.snd f U.1.ι = (awnRelativeGluingData X).natTrans.app U) :
    g = awnLocalMap f hf U := by
  let A := Γ(X, U.1)
  let B := Γ(pullback f U.1.ι, ⊤)
  let N := AbsoluteWeakNormalization A
  let Z := pullback f U.1.ι
  change Scheme.Spec.obj (Opposite.op (CommRingCat.of N)) ⟶ Z at g
  change g ≫ pullback.snd f U.1.ι =
    Scheme.Spec.map (CommRingCat.ofHom (algebraMap A N)).op ≫ U.2.isoSpec.inv at hg
  have := isAffineHom_of_universalHomeomorphism f hf
  let : IsAffine U.1.toScheme := U.2
  let : IsAffine Z := inferInstance
  let φ : A →+* B := (pullback.snd f U.1.ι).appTop.hom.comp U.1.topIso.inv.hom
  let : Algebra A B := φ.toAlgebra
  have hφ : algebraMap A B = φ := by simp [φ, RingHom.algebraMap_toAlgebra]
  have hB := awnLocalTarget_candidate f hf U φ hφ rfl
  let θ := Scheme.ΓSpecIso (CommRingCat.of N)
  let ψ : B →+* N := θ.hom.hom.comp g.appTop.hom
  have hnat : (awnRelativeGluingData X).natTrans.app U =
      Scheme.Spec.map (CommRingCat.ofHom (algebraMap A N)).op ≫ U.2.isoSpec.inv := rfl
  have htop := congrArg (fun k => k.appTop) hg
  have hcompRaw := congrArg
    (fun k : CommRingCat.Hom _ _ => (k ≫ θ.hom).hom.comp U.1.topIso.inv.hom) htop
  have hcomp : θ.hom.hom.comp
      (g.appTop.hom.comp ((pullback.snd f U.1.ι).appTop.hom.comp U.1.topIso.inv.hom)) =
      θ.hom.hom.comp
        (((awnRelativeGluingData X).natTrans.app U).appTop.hom.comp U.1.topIso.inv.hom) := by
    rw [Scheme.Hom.comp_appTop] at hcompRaw
    exact hcompRaw
  have hnatRing : θ.hom.hom.comp
      (((awnRelativeGluingData X).natTrans.app U).appTop.hom.comp U.1.topIso.inv.hom) =
      θ.hom.hom.comp
      ((Scheme.Spec.map (CommRingCat.ofHom (algebraMap A N)).op).appTop.hom.comp
        (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom) := by
    have hcancel : U.1.topIso.inv ≫ U.2.isoSpec.inv.appTop =
        (Scheme.ΓSpecIso (CommRingCat.of A)).inv := by
      rw [U.2.isoSpec_inv_appTop, ← Category.assoc, U.1.topIso.inv_hom_id, Category.id_comp]
      rfl
    have hcancelRing : U.2.isoSpec.inv.appTop.hom.comp U.1.topIso.inv.hom =
        (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom :=
      congrArg CommRingCat.Hom.hom hcancel
    rw [hnat]
    show θ.hom.hom.comp
      ((Scheme.Spec.map (CommRingCat.ofHom (algebraMap A N)).op).appTop.hom.comp
        (U.2.isoSpec.inv.appTop.hom.comp U.1.topIso.inv.hom)) = _
    rw [hcancelRing]
  have hGammaSpecRing : θ.hom.hom.comp
      ((Scheme.Spec.map (CommRingCat.ofHom (algebraMap A N)).op).appTop.hom) =
      (algebraMap A N).comp (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom :=
    congrArg CommRingCat.Hom.hom (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap A N)))
  have hGammaSpec_map : θ.hom.hom.comp
      ((Scheme.Spec.map (CommRingCat.ofHom (algebraMap A N)).op).appTop.hom.comp
        (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom) = algebraMap A N := by
    calc
      _ = ((algebraMap A N).comp (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom).comp
          (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom := by
        simpa [RingHom.comp_assoc] using congrArg
          (fun q : Γ(Scheme.Spec.obj (Opposite.op (CommRingCat.of A)), ⊤) →+* N =>
            q.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom) hGammaSpecRing
      _ = algebraMap A N := by
        have hIso : (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom.comp
            (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom = RingHom.id _ :=
          congrArg CommRingCat.Hom.hom (Scheme.ΓSpecIso (CommRingCat.of A)).inv_hom_id
        rw [RingHom.comp_assoc, hIso, RingHom.comp_id]
  have hψ : ψ.comp φ = algebraMap A N := by
    show θ.hom.hom.comp (g.appTop.hom.comp
      ((pullback.snd f U.1.ι).appTop.hom.comp U.1.topIso.inv.hom)) = _
    exact hcomp.trans (hnatRing.trans hGammaSpec_map)
  show g = Scheme.Spec.map
    (CommRingCat.ofHom (awnCandidateMapToAWN A B hB)).op ≫ Z.isoSpec.inv
  apply (cancel_mono Z.isoSpec.hom).mp
  calc
    g ≫ Z.isoSpec.hom = Scheme.Spec.map (CommRingCat.ofHom ψ).op := by
      rw [← Scheme.isoSpec_hom_naturality]
      simp [ψ, θ, SpecMap_ΓSpecIso_hom]
    _ = Scheme.Spec.map
        (CommRingCat.ofHom (awnCandidateMapToAWN A B hB)).op := by
      rw [awnCandidateMapToAWN_unique A B hB ψ hψ]
    _ = (Scheme.Spec.map
        (CommRingCat.ofHom (awnCandidateMapToAWN A B hB)).op ≫ Z.isoSpec.inv) ≫
          Z.isoSpec.hom := by simp

private noncomputable def awnLocalLift {X Y : Scheme.{u}} (f : Y ⟶ X)
    (hf : UniversalHomeomorphism f) (U : X.AffineZariskiSite) :
    (awnRelativeGluingData X).functor.obj U ⟶ Y :=
  awnLocalMap f hf U ≫ pullback.fst f U.1.ι

private theorem awnLocalLift_naturality {X Y : Scheme.{u}} (f : Y ⟶ X)
    (hf : UniversalHomeomorphism f) {U V : X.AffineZariskiSite}
    (i : U ⟶ V) :
    (awnRelativeGluingData X).functor.map i ≫ awnLocalLift f hf V =
      awnLocalLift f hf U := by
  let d := awnRelativeGluingData X
  let 𝒰 := Scheme.AffineZariskiSite.directedCover X
  let e : U.1.toScheme ⟶ V.1.toScheme := 𝒰.trans i
  have hNat : d.functor.map i ≫ d.natTrans.app V = d.natTrans.app U ≫ e := by
    show d.functor.map i ≫ d.natTrans.app V = d.natTrans.app U ≫ 𝒰.functorOfLocallyDirected.map i
    exact d.natTrans.naturality i
  have hcover : e ≫ V.1.ι = U.1.ι := by
    show 𝒰.trans i ≫ 𝒰.f V = 𝒰.f U
    exact 𝒰.trans_map i
  have hPB : pullback.fst f V.1.ι ≫ f = pullback.snd f V.1.ι ≫ V.1.ι :=
    pullback.condition
  have hLocal : awnLocalMap f hf V ≫ pullback.snd f V.1.ι = d.natTrans.app V :=
    awnLocalMap_snd f hf V
  let g : d.functor.obj U ⟶ pullback f U.1.ι :=
    pullback.lift
      (d.functor.map i ≫ awnLocalMap f hf V ≫ pullback.fst f V.1.ι)
      (d.natTrans.app U) (by
        calc
          (d.functor.map i ≫ awnLocalMap f hf V ≫ pullback.fst f V.1.ι) ≫ f =
              (d.functor.map i ≫ awnLocalMap f hf V) ≫
                (pullback.fst f V.1.ι ≫ f) := by simp only [Category.assoc]
          _ = (d.functor.map i ≫ awnLocalMap f hf V) ≫
                (pullback.snd f V.1.ι ≫ V.1.ι) := by rw [hPB]
          _ = (d.functor.map i ≫ (awnLocalMap f hf V ≫ pullback.snd f V.1.ι)) ≫ V.1.ι :=
                congrArg (fun t => t ≫ V.1.ι) (Category.assoc _ _ _)
          _ = (d.functor.map i ≫ d.natTrans.app V) ≫ V.1.ι :=
                congrArg (fun t => (d.functor.map i ≫ t) ≫ V.1.ι) hLocal
          _ = (d.natTrans.app U ≫ e) ≫ V.1.ι := congrArg (fun t => t ≫ V.1.ι) hNat
          _ = d.natTrans.app U ≫ e ≫ V.1.ι := Category.assoc _ _ _
          _ = d.natTrans.app U ≫ U.1.ι := congrArg (fun t => d.natTrans.app U ≫ t) hcover
      )
  have hg : g ≫ pullback.snd f U.1.ι = d.natTrans.app U := pullback.lift_snd _ _ _
  calc
    d.functor.map i ≫ awnLocalLift f hf V =
        d.functor.map i ≫ awnLocalMap f hf V ≫ pullback.fst f V.1.ι := rfl
    _ = g ≫ pullback.fst f U.1.ι := (pullback.lift_fst _ _ _).symm
    _ = awnLocalMap f hf U ≫ pullback.fst f U.1.ι := by rw [awnLocalMap_unique f hf U g hg]
    _ = awnLocalLift f hf U := rfl

private noncomputable def awnSchemeCocone {X Y : Scheme.{u}} (f : Y ⟶ X)
    (hf : UniversalHomeomorphism f) :
    CategoryTheory.Limits.Cocone (awnRelativeGluingData X).functor where
  pt := Y
  ι :=
    { app := awnLocalLift f hf
      naturality := fun _ _ i => awnLocalLift_naturality f hf i }

private noncomputable def awnSchemeMap {X Y : Scheme.{u}} (f : Y ⟶ X)
    (hf : UniversalHomeomorphism f) :
    (awnRelativeGluingData X).glued ⟶ Y :=
  colimit.desc (awnRelativeGluingData X).functor (awnSchemeCocone f hf)

private theorem awnSchemeMap_over {X Y : Scheme.{u}} (f : Y ⟶ X)
    (hf : UniversalHomeomorphism f) :
    awnSchemeMap f hf ≫ f = (awnRelativeGluingData X).toBase := by
  let d := awnRelativeGluingData X
  refine colimit.hom_ext fun U => ?_
  show (colimit.ι d.functor U ≫ colimit.desc d.functor (awnSchemeCocone f hf)) ≫ f =
      colimit.ι d.functor U ≫ d.toBase
  rw [colimit.ι_desc, d.ι_toBase]
  show awnLocalLift f hf U ≫ f = d.natTrans.app U ≫ U.1.ι
  rw [awnLocalLift, Category.assoc, pullback.condition, ← Category.assoc, awnLocalMap_snd]
  rfl

private theorem awnSchemeMap_unique {X Y : Scheme.{u}} (f : Y ⟶ X)
    (hf : UniversalHomeomorphism f) (g : (awnRelativeGluingData X).glued ⟶ Y)
    (hg : g ≫ f = (awnRelativeGluingData X).toBase) :
    g = awnSchemeMap f hf := by
  let d := awnRelativeGluingData X
  refine colimit.hom_ext fun U => ?_
  let gU : d.functor.obj U ⟶ pullback f U.1.ι := pullback.lift
    (colimit.ι d.functor U ≫ g) (d.natTrans.app U) (by
      calc
        (colimit.ι d.functor U ≫ g) ≫ f = colimit.ι d.functor U ≫ (g ≫ f) := by
          rw [Category.assoc]
        _ = colimit.ι d.functor U ≫ d.toBase := by rw [hg]
        _ = d.natTrans.app U ≫ U.1.ι := by rw [d.ι_toBase])
  calc
    colimit.ι d.functor U ≫ g = gU ≫ pullback.fst f U.1.ι := (pullback.lift_fst _ _ _).symm
    _ = awnLocalLift f hf U := by
      rw [awnLocalMap_unique f hf U gU (pullback.lift_snd _ _ _)]
      rfl
    _ = colimit.ι d.functor U ≫ awnSchemeMap f hf := by
      show awnLocalLift f hf U =
        colimit.ι d.functor U ≫ colimit.desc d.functor (awnSchemeCocone f hf)
      rw [colimit.ι_desc]
      rfl

private theorem absoluteWeakNormalization_ring_isAbsolutelyWeaklyNormal
    (A : Type u) [CommRing A] :
    IsAbsolutelyWeaklyNormalRing (AbsoluteWeakNormalization A) := by
  let N := AbsoluteWeakNormalization A
  let : CommRing N := absoluteWeakNormalization_commRing A
  let hN : UniversalHomeomorphism
      (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A N)).op) :=
    absoluteWeakNormalization_universalHomeomorphism A
  have hNobj : absoluteWeakNormalizationCategoryObject A =
      (⟨CommAlgCat.of A N, hN⟩ :
        AbsoluteWeakNormalizationCategory A) := by
    ext
    rfl
  have hNself : IsIso ((absoluteWeakNormalizationCategoryObject_isTerminal A).from
      (⟨CommAlgCat.of A N, hN⟩ :
        AbsoluteWeakNormalizationCategory A)) := by
    rw [← hNobj, IsTerminal.from_self]
    infer_instance
  exact (isIso_lift_to_absoluteWeakNormalization_iff_isAbsolutelyWeaklyNormalRing
    A N hN).mp hNself

private theorem awnSchemeOver_isAbsolutelyWeaklyNormal (X : Scheme.{u}) :
    IsAbsolutelyWeaklyNormal (awnSchemeOver X).left := by
  classical
  let d := awnRelativeGluingData X
  intro x
  let i := d.cover.idx x
  obtain ⟨y, hy⟩ := d.cover.covers x
  have : IsOpenImmersion (d.cover.f i) := d.cover.map_prop i
  let U := i.1
  let A := Γ(X, U)
  let N := AbsoluteWeakNormalization A
  let : CommRing N := absoluteWeakNormalization_commRing A
  let : IsAffine (d.functor.obj i) := by
    show IsAffine (Spec (.of N))
    infer_instance
  let V : d.glued.Opens := (d.cover.f i).opensRange
  have hRange : Set.range (d.cover.f i) = Set.range V.ι := by
    rw [Scheme.Opens.range_ι, Scheme.Hom.coe_opensRange]
  have : IsOpenImmersion V.ι := inferInstance
  let e : d.functor.obj i ≅ V.toScheme :=
    IsOpenImmersion.isoOfRangeEq (f := d.cover.f i) (g := V.ι)
      (H := d.cover.map_prop i) hRange
  let : IsAffine V.toScheme := IsAffine.of_isIso e.inv
  have hAffineV : IsAffineOpen V := IsAffine.of_isIso e.inv
  have hxV : x ∈ V := by
    show ∃ z, d.cover.f i z = x
    exact ⟨y, by simpa [i] using hy⟩
  refine ⟨⟨V, hAffineV⟩, hxV, ?_⟩
  · show IsAbsolutelyWeaklyNormalRing Γ(d.glued, V)
    have himg : e.hom ''ᵁ (⊤ : (d.functor.obj i).Opens) = (⊤ : V.toScheme.Opens) := by
      rw [Scheme.Hom.image_top_eq_opensRange, Scheme.Hom.opensRange_of_isIso]
    let eΓ : Γ(V.toScheme, ⊤) ≃+* N :=
      ((eqToIso (congrArg (fun W : V.toScheme.Opens => CommRingCat.of Γ(V.toScheme, W))
          himg.symm) ≪≫ e.hom.appIso ⊤) ≪≫
        Scheme.ΓSpecIso (CommRingCat.of N)).commRingCatIsoToRingEquiv
    let eV : Γ(d.glued, V) ≃+* Γ(V.toScheme, ⊤) :=
      V.topIso.symm.commRingCatIsoToRingEquiv
    exact absolutelyWeaklyNormalRing_of_ringEquiv (eV.trans eΓ).symm
      (absoluteWeakNormalization_ring_isAbsolutelyWeaklyNormal A)

private theorem absolutelyWeaklyNormal_of_iso {X Y : Scheme.{u}} (e : X ≅ Y)
    (hX : IsAbsolutelyWeaklyNormal X) :
    IsAbsolutelyWeaklyNormal Y := by
  let : IsOpenImmersion e.hom := inferInstance
  intro y
  obtain ⟨U, hx, hU⟩ := hX (e.inv y)
  let V : Y.Opens := e.hom ''ᵁ (U : X.Opens)
  let eU : U.1.toScheme ≅ V.toScheme := e.hom.isoImage U.1
  have hV : IsAffineOpen V := IsAffine.of_isIso eU.inv
  have hy : y ∈ V := by simpa [V] using e.hom.apply_mem_image_iff.mpr hx
  exact ⟨⟨V, hV⟩, hy, absolutelyWeaklyNormalRing_of_ringEquiv
    (e.hom.appIso U.1).commRingCatIsoToRingEquiv.symm hU⟩

/-- The source of an open immersion into an absolutely weakly normal scheme is absolutely weakly
normal. -/
private theorem absolutelyWeaklyNormal_of_isOpenImmersion {Z Y : Scheme.{u}} (j : Z ⟶ Y)
    [IsOpenImmersion j] (hY : IsAbsolutelyWeaklyNormal Y) : IsAbsolutelyWeaklyNormal Z :=
  absolutelyWeaklyNormal_of_iso j.isoOpensRange.symm
    (isAbsolutelyWeaklyNormal_open hY j.opensRange)

private theorem awnOpenPullback_isAbsolutelyWeaklyNormal {X U : Scheme.{u}}
    (f : U ⟶ X) [IsOpenImmersion f] :
    IsAbsolutelyWeaklyNormal
      (pullback f (awnSchemeOver X).hom) :=
  absolutelyWeaklyNormal_of_isOpenImmersion (pullback.snd f (awnSchemeOver X).hom)
    (awnSchemeOver_isAbsolutelyWeaklyNormal X)

private theorem awnAlgebraMap_isIso_of_awns {A B : Type u} [CommRing A] [CommRing B]
    [Algebra A B]
    (hAB : IsAbsoluteWeakNormalizationCandidate A
      (CommAlgCat.of A B))
    (hA : IsAbsolutelyWeaklyNormalRing A)
    (hB : IsAbsolutelyWeaklyNormalRing B) :
    IsIso (CommAlgCat.ofHom
      ({ toRingHom := algebraMap A B
         commutes' := fun a => by simp } : A →ₐ[A] B)) := by
  let t := absoluteWeakNormalizationCategoryObject_isTerminal A
  have hAA : UniversalHomeomorphism
      (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A A)).op) := by
    convert Stacks.Thickenings.universalHomeomorphism_id (Spec (.of A)) using 1 <;> simp
  let CA : AbsoluteWeakNormalizationCategory A :=
    ⟨CommAlgCat.of A A, hAA⟩
  let CB : AbsoluteWeakNormalizationCategory A :=
    ⟨CommAlgCat.of A B, hAB⟩
  let ab : A →ₐ[A] B := {
    toRingHom := algebraMap A B
    commutes' := fun a => by simp }
  let : IsIso (t.from CA) :=
    (isIso_lift_to_absoluteWeakNormalization_iff_isAbsolutelyWeaklyNormalRing
      A A hAA).2 hA
  let : IsIso (t.from CB) :=
    (isIso_lift_to_absoluteWeakNormalization_iff_isAbsolutelyWeaklyNormalRing
      A B hAB).2 hB
  let qA := (ObjectProperty.ι (IsAbsoluteWeakNormalizationCandidate A)).map
    (t.from CA)
  let qB := (ObjectProperty.ι (IsAbsoluteWeakNormalizationCandidate A)).map
    (t.from CB)
  let fAB' : CommAlgCat.of A A ⟶ CommAlgCat.of A B := CommAlgCat.ofHom ab
  have hcomp' : fAB' ≫ qB = qA := by
    apply CommAlgCat.hom_ext
    ext
  let : IsIso qA := (ObjectProperty.ι _).map_isIso (t.from CA)
  let : IsIso qB := (ObjectProperty.ι _).map_isIso (t.from CB)
  show IsIso fAB'
  rw [(IsIso.eq_comp_inv qB).mpr hcomp']
  infer_instance

private theorem awnRing_of_affineScheme {Z : Scheme.{u}} [IsAffine Z]
    (hZ : IsAbsolutelyWeaklyNormal Z) :
    IsAbsolutelyWeaklyNormalRing Γ(Z, ⊤) := by
  have h := (isAbsolutelyWeaklyNormal_tfae Z).out 1 2
  exact h.mp hZ ⟨⊤, isAffineOpen_top Z⟩

private theorem awnUniversalHomeomorphism_isIso {X Y : Scheme.{u}}
    (f : Y ⟶ X) (hf : UniversalHomeomorphism f)
    (hX : IsAbsolutelyWeaklyNormal X)
    (hY : IsAbsolutelyWeaklyNormal Y) : IsIso f := by
  have := isAffineHom_of_universalHomeomorphism f hf
  rw [← isomorphisms.iff, IsZariskiLocalAtTarget.iff_of_openCover
    (P := isomorphisms Scheme)
    (Scheme.AffineZariskiSite.directedCover X)]
  intro U
  let Z := pullback f U.1.ι
  let : IsAffine U.1.toScheme := U.2
  let : IsAffine Z := inferInstance
  have hV : IsAbsolutelyWeaklyNormal U.1.toScheme :=
    isAbsolutelyWeaklyNormal_open hX U.1
  have hZ : IsAbsolutelyWeaklyNormal Z :=
    absolutelyWeaklyNormal_of_isOpenImmersion (pullback.fst f U.1.ι) hY
  let A := Γ(X, U.1)
  let B := Γ(Z, ⊤)
  let φ : A →+* B := (pullback.snd f U.1.ι).appTop.hom.comp U.1.topIso.inv.hom
  let : Algebra A B := φ.toAlgebra
  have hCandidate := awnLocalTarget_candidate f hf U φ (by
      simp [RingHom.algebraMap_toAlgebra]) rfl
  have hA : IsAbsolutelyWeaklyNormalRing A :=
    absolutelyWeaklyNormalRing_of_ringEquiv
      U.1.topIso.symm.commRingCatIsoToRingEquiv.symm (awnRing_of_affineScheme hV)
  have hB : IsAbsolutelyWeaklyNormalRing B := awnRing_of_affineScheme hZ
  have hAB : IsAbsoluteWeakNormalizationCandidate A
      (CommAlgCat.of A B) := by
    simpa [A, B, Z, φ] using hCandidate
  let ab : A →ₐ[A] B := {
    toRingHom := algebraMap A B
    commutes' := fun a => by simp }
  have hRingIso : IsIso (CommAlgCat.ofHom ab) := awnAlgebraMap_isIso_of_awns hAB hA hB
  have hCommIso : IsIso (CommRingCat.ofHom ab.toRingHom) := by
    simpa using (forget₂ (CommAlgCat A) CommRingCat).map_isIso (CommAlgCat.ofHom ab)
  have hφIso : IsIso (CommRingCat.ofHom φ) := by
    simpa [ab, φ, RingHom.algebraMap_toAlgebra] using hCommIso
  have hAppIso : IsIso (pullback.snd f U.1.ι).appTop := by
    have hφeq : CommRingCat.ofHom φ =
        U.1.topIso.inv ≫ (pullback.snd f U.1.ι).appTop := by
      dsimp [φ]
    rw [← Iso.hom_inv_id_assoc U.1.topIso (pullback.snd f U.1.ι).appTop, ← hφeq]
    infer_instance
  have hlocal : IsIso (pullback.snd f U.1.ι) := by
    rw [← isomorphisms.iff,
      (isomorphisms Scheme).arrow_mk_iso_iff
        (arrowIsoSpecΓOfIsAffine (pullback.snd f U.1.ι))]
    infer_instance
  exact hlocal

end Proof

private noncomputable def awnOverObject (X : Scheme.{u}) : UniversalHomeomorphismOver X :=
  ⟨awnSchemeOver X, awnSchemeOver_property X⟩

private noncomputable def awnOverMap (X : Scheme.{u}) (Z : UniversalHomeomorphismOver X) :
    awnOverObject X ⟶ Z :=
  ObjectProperty.homMk (Over.homMk (awnSchemeMap Z.obj.hom Z.property)
    (awnSchemeMap_over Z.obj.hom Z.property))

private noncomputable def awnOverObject_isInitial (X : Scheme.{u}) :
    IsInitial (awnOverObject X) := by
  refine IsInitial.ofUniqueHom (fun Z => awnOverMap X Z) ?_
  intro Z g
  apply ObjectProperty.hom_ext
  apply CategoryTheory.CostructuredArrow.hom_ext
  exact awnSchemeMap_unique Z.obj.hom Z.property g.hom.left (by
    simp [awnOverObject, awnSchemeOver])

/-- The category of universal homeomorphisms to a scheme `X` has an initial object, the absolute
weak normalization of `X`, which remains initial over every open subscheme. -/
@[stacks 0EUS "absolute_weak_normalization_initial"]
public instance hasInitialUniversalHomeomorphismOver (X : Scheme.{u}) :
    HasLocallyInitialUniversalHomeomorphismOver X := by
  let : HasInitial (UniversalHomeomorphismOver X) :=
    (awnOverObject_isInitial X).hasInitial
  refine { nonempty_isInitial_pullback := ?_ }
  intro U f hf
  let : HasInitial (UniversalHomeomorphismOver U) :=
    (awnOverObject_isInitial U).hasInitial
  let Z := UniversalHomeomorphismOver.pullback f
    (initial (UniversalHomeomorphismOver X))
  let eX : initial (UniversalHomeomorphismOver X) ≅ awnOverObject X :=
    initialIsInitial.uniqueUpToIso (awnOverObject_isInitial X)
  let eScheme : (initial (UniversalHomeomorphismOver X)).obj.left ≅
      (awnOverObject X).obj.left := asIso ((Over.forget X).map eX.hom.hom)
  have : IsIso eScheme.hom := inferInstance
  let pmap := pullback.map f
      (initial (UniversalHomeomorphismOver X)).obj.hom f (awnOverObject X).obj.hom
      (𝟙 U) eScheme.hom (𝟙 X) (by simp) (by
        simp [eScheme])
  have hPullMap : IsIso pmap := by
    dsimp [pmap]
    let : IsIso (𝟙 U) := inferInstance
    let : IsIso (𝟙 X) := inferInstance
    exact pullback.map_isIso f (initial (UniversalHomeomorphismOver X)).obj.hom
      f (awnOverObject X).obj.hom (𝟙 U) eScheme.hom (𝟙 X) (by simp) (by
        simp [eScheme])
  let ePull : Z.obj.left ≅ (UniversalHomeomorphismOver.pullback f
      (awnOverObject X)).obj.left := {
    hom := pmap
    inv := Classical.choose hPullMap.out
    hom_inv_id := (Classical.choose_spec hPullMap.out).1
    inv_hom_id := (Classical.choose_spec hPullMap.out).2 }
  have hZ : IsAbsolutelyWeaklyNormal Z.obj.left := by
    change IsAbsolutelyWeaklyNormal
      (pullback f (initial (UniversalHomeomorphismOver X)).obj.hom)
    exact absolutelyWeaklyNormal_of_iso ePull.symm (awnOpenPullback_isAbsolutelyWeaklyNormal f)
  let g := awnSchemeMap Z.obj.hom Z.property
  have hg : UniversalHomeomorphism g := by
    let : MorphismProperty.HasOfPostcompProperty (@UniversalHomeomorphism.{u})
        (@UniversalHomeomorphism.{u}) :=
      universalHomeomorphism_hasTwoOutOfThreeProperty.toHasOfPostcompProperty
    apply MorphismProperty.of_postcomp (W := @UniversalHomeomorphism.{u})
      g Z.obj.hom Z.property
    simpa [g, awnSchemeMap_over] using awnRelativeGluingData_toBase_universalHomeomorphism U
  have hgIso : IsIso g := awnUniversalHomeomorphism_isIso g hg hZ
    (awnSchemeOver_isAbsolutelyWeaklyNormal U)
  let eG : (awnSchemeOver U).left ≅ Z.obj.left := {
    hom := awnSchemeMap Z.obj.hom Z.property
    inv := Classical.choose hgIso.out
    hom_inv_id := (Classical.choose_spec hgIso.out).1
    inv_hom_id := (Classical.choose_spec hgIso.out).2 }
  let eOver : awnSchemeOver U ≅ Z.obj := Over.isoMk eG (awnSchemeMap_over Z.obj.hom Z.property)
  let eCat : awnOverObject U ≅ Z :=
    ObjectProperty.isoMk (fun W : Over U => UniversalHomeomorphism W.hom) eOver
  exact ⟨(awnOverObject_isInitial U).ofIso eCat⟩

end AlgebraicGeometry

end
