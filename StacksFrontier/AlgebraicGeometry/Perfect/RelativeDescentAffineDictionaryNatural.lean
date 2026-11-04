module

public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeDescentAffineDictionary
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeDescentAffineCase
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeDescentAffineAvatar
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectArrowIso

/-!
# The affine case of Stacks 0DI7, unconditionally

Over an affine open `V₀ ⊆ X₀` lying over an affine open `W₀ ⊆ S₀`, the stages and the limit of
the restricted relative descent situation are the spectra of the algebras of Stacks 0DHX, and
the identifications of their derived morphism sets with derived morphism sets over those
algebras commute with the transition maps and the comparison maps. Stacks 0DHX then gives
Stacks 0DI7 for the restriction to `V₀`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry RingedSpaceModuleAdjunction
open CochainComplex.DerivedExtensionScalars
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)
open scoped TensorProduct
open StacksDraft.TorAmplitude

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace CommRingCat

/-- **The identification of a pushout with a tensor product is natural.** Given two pushout
squares of commutative rings over the same `R ⟶ A`, a map `τ` of their other legs and a map `σ`
of their vertices compatible with `τ` and with the two maps out of `A`, the identifications of
the vertices with the tensor products carry `τ ⊗ A` to `σ`. -/
theorem tensorMap_comp_isoIsPushout_hom {R A B B' : Type u} [CommRing R] [CommRing A]
    [CommRing B] [CommRing B'] [Algebra R A] [Algebra R B] [Algebra R B'] (τ : B →ₐ[R] B')
    {C C' : CommRingCat.{u}} {inl : of B ⟶ C} {inr : of A ⟶ C} {inl' : of B' ⟶ C'}
    {inr' : of A ⟶ C'}
    (hP : IsPushout (ofHom (algebraMap R B)) (ofHom (algebraMap R A)) inl inr)
    (hP' : IsPushout (ofHom (algebraMap R B')) (ofHom (algebraMap R A)) inl' inr')
    (σ : C ⟶ C') (hl : inl ≫ σ = ofHom τ.toRingHom ≫ inl') (hr : inr ≫ σ = inr') :
    ofHom (Algebra.TensorProduct.map τ (AlgHom.id R A)).toRingHom ≫
        ((isPushout_tensorProduct R B' A).isoIsPushout _ _ hP').hom =
      ((isPushout_tensorProduct R B A).isoIsPushout _ _ hP).hom ≫ σ := by
  refine (isPushout_tensorProduct R B A).hom_ext ?_ ?_
  · rw [IsPushout.inl_isoIsPushout_hom_assoc, hl, ← Category.assoc]
    have : ofHom (S := B ⊗[R] A) Algebra.TensorProduct.includeLeftRingHom ≫
        ofHom (Algebra.TensorProduct.map τ (AlgHom.id R A)).toRingHom =
        ofHom τ.toRingHom ≫ ofHom (S := B' ⊗[R] A) Algebra.TensorProduct.includeLeftRingHom := by
      ext x
      simp
    rw [this, Category.assoc, IsPushout.inl_isoIsPushout_hom]
  · rw [IsPushout.inr_isoIsPushout_hom_assoc, hr, ← Category.assoc]
    have : ofHom (S := B ⊗[R] A) Algebra.TensorProduct.includeRight.toRingHom ≫
        ofHom (Algebra.TensorProduct.map τ (AlgHom.id R A)).toRingHom =
        ofHom (S := B' ⊗[R] A) Algebra.TensorProduct.includeRight.toRingHom := by
      ext x
      simp
    rw [this, IsPushout.inr_isoIsPushout_hom]

end CommRingCat

namespace AlgebraicGeometry.RelativeDescentSituation

variable {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] (D : RelativeDescentSituation.{u, u} I)

attribute [local implicit_reducible] restrict

section Squares

variable (W₀ : (D.descent.system.obj (op D.descent.base)).Opens)
  (V₀ : D.X₀.left.Opens) (hV₀ : IsAffineOpen V₀) (hVW : V₀ ≤ D.X₀.hom ⁻¹ᵁ W₀)
  (hW₀ : IsAffineOpen W₀)

/-- **The identification `Rᵢ ⊗_{R₀} A₀ ≅ Γ(Vᵢ)` is compatible with the transition maps.** -/
theorem stageAlgebraIsoSections_transition {i j : D.LaterIndex} (h : i ≤ j) :
    (letI : Algebra Γ(W₀.toScheme, ⊤) Γ(V₀.toScheme, ⊤) :=
      ((D.X₀.hom.resLE W₀ V₀ hVW).appTop).hom.toAlgebra
    CommRingCat.ofHom (PseudoCoherence.stageMap (D.baseRingAlgDiagram W₀) Γ(V₀.toScheme, ⊤)
        (homOfLE h)) ≫ (D.stageAlgebraIsoSections W₀ V₀ hV₀ hVW hW₀ j).hom =
      (D.stageAlgebraIsoSections W₀ V₀ hV₀ hVW hW₀ i).hom ≫
        ((D.restrict V₀ hV₀.isCompact).transition h).appTop) := by
  let : Algebra Γ(W₀.toScheme, ⊤) Γ(V₀.toScheme, ⊤) :=
    ((D.X₀.hom.resLE W₀ V₀ hVW).appTop).hom.toAlgebra
  exact CommRingCat.tensorMap_comp_isoIsPushout_hom (A := Γ(V₀.toScheme, ⊤))
    ((D.baseRingAlgDiagram W₀).map (homOfLE h)).hom
    (D.isPushout_appTop_restrictToBasePreimage W₀ V₀ hV₀ hVW hW₀ i)
    (D.isPushout_appTop_restrictToBasePreimage W₀ V₀ hV₀ hVW hW₀ j) _
    (by
      have := congrArg Scheme.Hom.appTop (D.restrictToBasePreimage_naturality W₀ V₀ hV₀ hVW h)
      rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop] at this
      exact this.symm)
    (by
      have := congrArg Scheme.Hom.appTop
        ((D.restrict V₀ hV₀.isCompact).transition_comp_toFixedStage h)
      rw [Scheme.Hom.comp_appTop] at this
      exact this)

/-- **The identification `R ⊗_{R₀} A₀ ≅ Γ(V)` is compatible with the comparison maps.** -/
theorem limitAlgebraIsoSections_comparison (i : D.LaterIndex) :
    (letI : Algebra Γ(W₀.toScheme, ⊤) Γ(V₀.toScheme, ⊤) :=
      ((D.X₀.hom.resLE W₀ V₀ hVW).appTop).hom.toAlgebra
    CommRingCat.ofHom (PseudoCoherence.stageToLimitMap (D.baseRingAlgCocone W₀) Γ(V₀.toScheme, ⊤)
        i) ≫ (D.limitAlgebraIsoSections W₀ V₀ hV₀ hVW hW₀).hom =
      (D.stageAlgebraIsoSections W₀ V₀ hV₀ hVW hW₀ i).hom ≫
        ((D.restrict V₀ hV₀.isCompact).projection i).appTop) := by
  let : Algebra Γ(W₀.toScheme, ⊤) Γ(V₀.toScheme, ⊤) :=
    ((D.X₀.hom.resLE W₀ V₀ hVW).appTop).hom.toAlgebra
  exact CommRingCat.tensorMap_comp_isoIsPushout_hom (A := Γ(V₀.toScheme, ⊤))
    ((D.baseRingAlgCocone W₀).ι.app i).hom
    (D.isPushout_appTop_restrictToBasePreimage W₀ V₀ hV₀ hVW hW₀ i)
    (D.isPushout_appTop_restrictToBasePreimageLimit W₀ V₀ hV₀ hVW hW₀) _
    (by
      have := congrArg Scheme.Hom.appTop
        (D.restrictToBasePreimageLimit_comp_baseProjectionPreimage W₀ V₀ hV₀ hVW i)
      rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop] at this
      exact this.symm)
    (by
      have := congrArg Scheme.Hom.appTop
        ((D.restrict V₀ hV₀.isCompact).projection_comp_toFixedStage i)
      rw [Scheme.Hom.comp_appTop] at this
      exact this)

/-- Isomorphisms `Spec Γ(-) ≅ -` given by ring isomorphisms of sections are natural in a map of
affine schemes whose map of sections is compatible with a ring map `m`. -/
private theorem spec_map_comp_isoSpec_trans_inv {X Y : Scheme} [IsAffine X] [IsAffine Y]
    {P Q : CommRingCat} (eX : P ≅ Γ(X, ⊤)) (eY : Q ≅ Γ(Y, ⊤)) (f : Y ⟶ X) (m : P ⟶ Q)
    (h : m ≫ eY.hom = eX.hom ≫ f.appTop) :
    Spec.map m ≫ (Scheme.isoSpec X ≪≫ Scheme.Spec.mapIso eX.op).inv =
      (Scheme.isoSpec Y ≪≫ Scheme.Spec.mapIso eY.op).inv ≫ f := by
  rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp, Iso.trans_hom, Iso.trans_hom,
    Category.assoc, ← Scheme.isoSpec_hom_naturality_assoc]
  exact congrArg (_ ≫ ·) ((Spec.map_comp _ _).symm.trans
    ((congrArg Spec.map h).trans (Spec.map_comp _ _)))

/-- If `Vᵢ ⟶ V₀` is the spectrum of a ring map `u` under `a`, with `V₀ ≅ Spec A`, then it is the
spectrum of `j ≫ u` for `j` any ring isomorphism `B ≅ A`, under `a` and `V₀ ≅ Spec B`. -/
private theorem iso_inv_comp_eq_spec_map_comp_inv {X V : Scheme} {P A B : CommRingCat}
    (a : X ≅ Spec P) (s : V ≅ Spec A) (j : B ≅ A) (f : X ⟶ V) (u : A ⟶ P)
    (h : a.hom ≫ Spec.map u = f ≫ s.hom) :
    a.inv ≫ f = Spec.map (j.hom ≫ u) ≫ (s ≪≫ Scheme.Spec.mapIso j.op).inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv, Iso.trans_hom, ← Category.assoc, ← h,
    Category.assoc]
  exact congrArg (_ ≫ ·) (Spec.map_comp _ _).symm

/-- **The stages are spectra compatibly with the transition maps.** -/
theorem stageSpecIso_inv_transition {i j : D.LaterIndex} (h : i ≤ j) :
    (letI : Algebra Γ(W₀.toScheme, ⊤) Γ(V₀.toScheme, ⊤) :=
      ((D.X₀.hom.resLE W₀ V₀ hVW).appTop).hom.toAlgebra
    Spec.map (CommRingCat.ofHom (PseudoCoherence.stageMap (D.baseRingAlgDiagram W₀)
        Γ(V₀.toScheme, ⊤) (homOfLE h))) ≫ (D.stageSpecIso W₀ V₀ hV₀ hVW hW₀ i).inv =
      (D.stageSpecIso W₀ V₀ hV₀ hVW hW₀ j).inv ≫ (D.restrict V₀ hV₀.isCompact).transition h) := by
  let : Algebra Γ(W₀.toScheme, ⊤) Γ(V₀.toScheme, ⊤) :=
    ((D.X₀.hom.resLE W₀ V₀ hVW).appTop).hom.toAlgebra
  have : IsAffine ((D.restrict V₀ hV₀.isCompact).schemeAt i) :=
    D.isAffine_restrict_schemeAt V₀ hV₀ i
  have : IsAffine ((D.restrict V₀ hV₀.isCompact).schemeAt j) :=
    D.isAffine_restrict_schemeAt V₀ hV₀ j
  exact spec_map_comp_isoSpec_trans_inv _ _ _ _
    (D.stageAlgebraIsoSections_transition W₀ V₀ hV₀ hVW hW₀ h)

/-- **The limit is a spectrum compatibly with the comparison maps.** -/
theorem limitSpecIso_inv_comparison (i : D.LaterIndex) :
    (letI : Algebra Γ(W₀.toScheme, ⊤) Γ(V₀.toScheme, ⊤) :=
      ((D.X₀.hom.resLE W₀ V₀ hVW).appTop).hom.toAlgebra
    Spec.map (CommRingCat.ofHom (PseudoCoherence.stageToLimitMap (D.baseRingAlgCocone W₀)
        Γ(V₀.toScheme, ⊤) i)) ≫ (D.stageSpecIso W₀ V₀ hV₀ hVW hW₀ i).inv =
      (D.limitSpecIso W₀ V₀ hV₀ hVW hW₀).inv ≫ (D.restrict V₀ hV₀.isCompact).projection i) := by
  let : Algebra Γ(W₀.toScheme, ⊤) Γ(V₀.toScheme, ⊤) :=
    ((D.X₀.hom.resLE W₀ V₀ hVW).appTop).hom.toAlgebra
  have : IsAffine ((D.restrict V₀ hV₀.isCompact).schemeAt i) :=
    D.isAffine_restrict_schemeAt V₀ hV₀ i
  have : IsAffine ((D.restrict V₀ hV₀.isCompact).limitScheme) :=
    D.isAffine_restrict_limitScheme V₀ hV₀
  exact spec_map_comp_isoSpec_trans_inv _ _ _ _
    (D.limitAlgebraIsoSections_comparison W₀ V₀ hV₀ hVW hW₀ i)

/-- The base ring of the 0DHX system read as a universe-lifted ring, which is the ring over
which the objects of the system are extended. -/
def fixedRingLiftIso : CommRingCat.of (ULift.{u} Γ(V₀.toScheme, ⊤)) ≅ Γ(V₀.toScheme, ⊤) :=
  (ULift.ringEquiv : ULift.{u} Γ(V₀.toScheme, ⊤) ≃+* Γ(V₀.toScheme, ⊤)).toCommRingCatIso

/-- `V₀` as the spectrum of the universe-lifted ring of its sections. -/
def fixedSpecIso : V₀.toScheme ≅ Spec (CommRingCat.of (ULift.{u} Γ(V₀.toScheme, ⊤))) :=
  have : IsAffine V₀.toScheme := hV₀
  Scheme.isoSpec V₀.toScheme ≪≫ Scheme.Spec.mapIso (D.fixedRingLiftIso V₀).op

/-- The ring map `ULift A₀ ⟶ Rᵢ ⊗_{R₀} A₀` along which Stacks 0DHX extends objects to a stage. -/
def stageRingMap (i : D.LaterIndex) :
    (letI : Algebra Γ(W₀.toScheme, ⊤) Γ(V₀.toScheme, ⊤) :=
      ((D.X₀.hom.resLE W₀ V₀ hVW).appTop).hom.toAlgebra
    CommRingCat.of (ULift.{u} Γ(V₀.toScheme, ⊤)) ⟶
      CommRingCat.of (PseudoCoherence.stageAlgebra (D.baseRingAlgDiagram W₀)
        Γ(V₀.toScheme, ⊤) i)) :=
  let : Algebra Γ(W₀.toScheme, ⊤) Γ(V₀.toScheme, ⊤) :=
    ((D.X₀.hom.resLE W₀ V₀ hVW).appTop).hom.toAlgebra
  CommRingCat.ofHom (PseudoCoherence.liftBaseToStageMap (D.baseRingAlgDiagram W₀)
    Γ(V₀.toScheme, ⊤) i)

/-- The ring map `ULift A₀ ⟶ R ⊗_{R₀} A₀` along which Stacks 0DHX extends objects to the
limit. -/
def limitRingMap :
    (letI : Algebra Γ(W₀.toScheme, ⊤) Γ(V₀.toScheme, ⊤) :=
      ((D.X₀.hom.resLE W₀ V₀ hVW).appTop).hom.toAlgebra
    CommRingCat.of (ULift.{u} Γ(V₀.toScheme, ⊤)) ⟶
      CommRingCat.of ((D.baseRingAlgCocone W₀).pt ⊗[Γ(W₀.toScheme, ⊤)] Γ(V₀.toScheme, ⊤))) :=
  let : Algebra Γ(W₀.toScheme, ⊤) Γ(V₀.toScheme, ⊤) :=
    ((D.X₀.hom.resLE W₀ V₀ hVW).appTop).hom.toAlgebra
  CommRingCat.ofHom (PseudoCoherence.liftBaseToLimitMap (D.baseRingAlgCocone W₀)
    Γ(V₀.toScheme, ⊤))

/-- Under the identifications `Vᵢ ≅ Spec (Rᵢ ⊗_{R₀} A₀)` and `V₀ ≅ Spec A₀`, the map `Vᵢ ⟶ V₀`
is the spectrum of `stageRingMap`. -/
theorem stageSpecIso_inv_comp_toFixedStage (i : D.LaterIndex) :
    (D.stageSpecIso W₀ V₀ hV₀ hVW hW₀ i).inv ≫ (D.restrict V₀ hV₀.isCompact).toFixedStage i =
      Spec.map (D.stageRingMap W₀ V₀ hVW i) ≫ (D.fixedSpecIso V₀ hV₀).inv := by
  have : IsAffine V₀.toScheme := hV₀
  exact iso_inv_comp_eq_spec_map_comp_inv (D.stageSpecIso W₀ V₀ hV₀ hVW hW₀ i)
    (Scheme.isoSpec V₀.toScheme) (D.fixedRingLiftIso V₀) _ _
    (D.stageSpecIso_hom_comp W₀ V₀ hV₀ hVW hW₀ i)

/-- Under the identifications `V ≅ Spec (R ⊗_{R₀} A₀)` and `V₀ ≅ Spec A₀`, the map `V ⟶ V₀` is
the spectrum of `limitRingMap`. -/
theorem limitSpecIso_inv_comp_limitToFixedStage :
    (D.limitSpecIso W₀ V₀ hV₀ hVW hW₀).inv ≫ (D.restrict V₀ hV₀.isCompact).limitToFixedStage =
      Spec.map (D.limitRingMap W₀ V₀ hVW) ≫ (D.fixedSpecIso V₀ hV₀).inv := by
  have : IsAffine V₀.toScheme := hV₀
  exact iso_inv_comp_eq_spec_map_comp_inv (D.limitSpecIso W₀ V₀ hV₀ hVW hW₀)
    (Scheme.isoSpec V₀.toScheme) (D.fixedRingLiftIso V₀) _ _
    (D.limitSpecIso_hom_comp W₀ V₀ hV₀ hVW hW₀)

/-- The ring maps `stageRingMap` commute with the transition maps `Rᵢ ⊗_{R₀} A₀ ⟶ Rⱼ ⊗_{R₀} A₀`. -/
theorem stageRingMap_comp_stageMap {i j : D.LaterIndex} (f : i ⟶ j) :
    (letI : Algebra Γ(W₀.toScheme, ⊤) Γ(V₀.toScheme, ⊤) :=
      ((D.X₀.hom.resLE W₀ V₀ hVW).appTop).hom.toAlgebra
    D.stageRingMap W₀ V₀ hVW i ≫ CommRingCat.ofHom (PseudoCoherence.stageMap
        (D.baseRingAlgDiagram W₀) Γ(V₀.toScheme, ⊤) f) = D.stageRingMap W₀ V₀ hVW j) :=
  let : Algebra Γ(W₀.toScheme, ⊤) Γ(V₀.toScheme, ⊤) :=
    ((D.X₀.hom.resLE W₀ V₀ hVW).appTop).hom.toAlgebra
  congrArg CommRingCat.ofHom
    (PseudoCoherence.stageMap_comp_liftBaseToStageMap (D.baseRingAlgDiagram W₀) Γ(V₀.toScheme, ⊤) f)

/-- The composite of `stageRingMap` with the comparison map `Rᵢ ⊗_{R₀} A₀ ⟶ R ⊗_{R₀} A₀` is
`limitRingMap`. -/
theorem stageRingMap_comp_stageToLimitMap (i : D.LaterIndex) :
    (letI : Algebra Γ(W₀.toScheme, ⊤) Γ(V₀.toScheme, ⊤) :=
      ((D.X₀.hom.resLE W₀ V₀ hVW).appTop).hom.toAlgebra
    D.stageRingMap W₀ V₀ hVW i ≫ CommRingCat.ofHom (PseudoCoherence.stageToLimitMap
        (D.baseRingAlgCocone W₀) Γ(V₀.toScheme, ⊤) i) = D.limitRingMap W₀ V₀ hVW) :=
  let : Algebra Γ(W₀.toScheme, ⊤) Γ(V₀.toScheme, ⊤) :=
    ((D.X₀.hom.resLE W₀ V₀ hVW).appTop).hom.toAlgebra
  congrArg CommRingCat.ofHom
    (PseudoCoherence.stageToLimitMap_comp_liftBaseToStageMap (D.baseRingAlgCocone W₀)
      Γ(V₀.toScheme, ⊤) i)

end Squares

section Dictionary

variable (W₀ : (D.descent.system.obj (op D.descent.base)).Opens)
  (V₀ : D.X₀.left.Opens) (hV₀ : IsAffineOpen V₀) (hVW : V₀ ≤ D.X₀.hom ⁻¹ᵁ W₀)
  (hW₀ : IsAffineOpen W₀)
  (K₀ L₀ : DerivedCategory (SheafOfModules.{u} (structureSheafRing D.X₀.left.toRingedSpace)))

/-- **The affine dictionary of Stacks 0DI7, from ring-level avatars over `V₀`.** -/
def affineDerivedHomEquivOfLiftedAvatar
    (𝕂 𝕃 : DerivedCategory (ModuleCat.{u} Γ(V₀.toScheme, ⊤)))
    (h𝕂 : StacksDraft.PseudoCoherence.IsPseudoCoherent 𝕂)
    (h𝕃 :
      letI : Algebra Γ(W₀.toScheme, ⊤) Γ(V₀.toScheme, ⊤) :=
        ((D.X₀.hom.resLE W₀ V₀ hVW).appTop).hom.toAlgebra
      HasFiniteTorDimensionCanonical Γ(W₀.toScheme, ⊤)
        ((ModuleCat.restrictScalars
          (algebraMap Γ(W₀.toScheme, ⊤) Γ(V₀.toScheme, ⊤))).mapDerivedCategory.obj 𝕃))
    (eK : (derivedPullback (D.fixedSpecIso V₀ hV₀).inv.toLRSHom.toShHom).obj
        ((derivedPullback V₀.ι.toLRSHom.toShHom).obj K₀) ≅
      derivedTildeObj (CommRingCat.of (ULift.{u} Γ(V₀.toScheme, ⊤)))
        ((PseudoCoherence.baseLiftRestriction Γ(V₀.toScheme, ⊤)).obj 𝕂))
    (eL : (derivedPullback (D.fixedSpecIso V₀ hV₀).inv.toLRSHom.toShHom).obj
        ((derivedPullback V₀.ι.toLRSHom.toShHom).obj L₀) ≅
      derivedTildeObj (CommRingCat.of (ULift.{u} Γ(V₀.toScheme, ⊤)))
        ((PseudoCoherence.baseLiftRestriction Γ(V₀.toScheme, ⊤)).obj 𝕃)) :
    D.AffineDerivedHomEquiv W₀ V₀ hV₀ hVW K₀ L₀ where
  moduleFst := 𝕂
  moduleSnd := 𝕃
  isPseudoCoherent_moduleFst := h𝕂
  hasFiniteTorDimension_moduleSnd := h𝕃
  stageEquiv i :=
    StandardModel.stageDictionary (D.fixedSpecIso V₀ hV₀) (D.stageSpecIso W₀ V₀ hV₀ hVW hW₀ i)
      ((D.restrict V₀ hV₀.isCompact).toFixedStage i) (D.stageRingMap W₀ V₀ hVW i)
      (D.stageSpecIso_inv_comp_toFixedStage W₀ V₀ hV₀ hVW hW₀ i) eK eL
  limitEquiv :=
    StandardModel.stageDictionary (D.fixedSpecIso V₀ hV₀) (D.limitSpecIso W₀ V₀ hV₀ hVW hW₀)
      ((D.restrict V₀ hV₀.isCompact).limitToFixedStage) (D.limitRingMap W₀ V₀ hVW)
      (D.limitSpecIso_inv_comp_limitToFixedStage W₀ V₀ hV₀ hVW hW₀) eK eL

/-- **The affine dictionary of Stacks 0DI7 is natural.** -/
theorem isNatural_affineDerivedHomEquivOfLiftedAvatar
    (𝕂 𝕃 : DerivedCategory (ModuleCat.{u} Γ(V₀.toScheme, ⊤)))
    (h𝕂 : StacksDraft.PseudoCoherence.IsPseudoCoherent 𝕂)
    (h𝕃 :
      letI : Algebra Γ(W₀.toScheme, ⊤) Γ(V₀.toScheme, ⊤) :=
        ((D.X₀.hom.resLE W₀ V₀ hVW).appTop).hom.toAlgebra
      HasFiniteTorDimensionCanonical Γ(W₀.toScheme, ⊤)
        ((ModuleCat.restrictScalars
          (algebraMap Γ(W₀.toScheme, ⊤) Γ(V₀.toScheme, ⊤))).mapDerivedCategory.obj 𝕃))
    (eK : (derivedPullback (D.fixedSpecIso V₀ hV₀).inv.toLRSHom.toShHom).obj
        ((derivedPullback V₀.ι.toLRSHom.toShHom).obj K₀) ≅
      derivedTildeObj (CommRingCat.of (ULift.{u} Γ(V₀.toScheme, ⊤)))
        ((PseudoCoherence.baseLiftRestriction Γ(V₀.toScheme, ⊤)).obj 𝕂))
    (eL : (derivedPullback (D.fixedSpecIso V₀ hV₀).inv.toLRSHom.toShHom).obj
        ((derivedPullback V₀.ι.toLRSHom.toShHom).obj L₀) ≅
      derivedTildeObj (CommRingCat.of (ULift.{u} Γ(V₀.toScheme, ⊤)))
        ((PseudoCoherence.baseLiftRestriction Γ(V₀.toScheme, ⊤)).obj 𝕃)) :
    (D.affineDerivedHomEquivOfLiftedAvatar W₀ V₀ hV₀ hVW hW₀ K₀ L₀ 𝕂 𝕃 h𝕂 h𝕃 eK eL).IsNatural := by
  let : Algebra Γ(W₀.toScheme, ⊤) Γ(V₀.toScheme, ⊤) :=
    ((D.X₀.hom.resLE W₀ V₀ hVW).appTop).hom.toAlgebra
  refine ⟨fun {i j} f φ => ?_, fun i φ => ?_⟩
  · exact StandardModel.stageDictionary_naturality (D.fixedSpecIso V₀ hV₀)
      (D.stageSpecIso W₀ V₀ hV₀ hVW hW₀ i) (D.stageSpecIso W₀ V₀ hV₀ hVW hW₀ j)
      ((D.restrict V₀ hV₀.isCompact).toFixedStage i) ((D.restrict V₀ hV₀.isCompact).toFixedStage j)
      (D.stageRingMap W₀ V₀ hVW i) (D.stageRingMap W₀ V₀ hVW j)
      (D.stageSpecIso_inv_comp_toFixedStage W₀ V₀ hV₀ hVW hW₀ i)
      (D.stageSpecIso_inv_comp_toFixedStage W₀ V₀ hV₀ hVW hW₀ j) eK eL
      ((D.restrict V₀ hV₀.isCompact).transition (leOfHom f))
      ((D.restrict V₀ hV₀.isCompact).transition_comp_toFixedStage (leOfHom f))
      (CommRingCat.ofHom (PseudoCoherence.stageMap (D.baseRingAlgDiagram W₀) Γ(V₀.toScheme, ⊤) f))
      (D.stageRingMap_comp_stageMap W₀ V₀ hVW f)
      (D.stageSpecIso_inv_transition W₀ V₀ hV₀ hVW hW₀ (leOfHom f)) φ
  · exact StandardModel.stageDictionary_naturality (D.fixedSpecIso V₀ hV₀)
      (D.stageSpecIso W₀ V₀ hV₀ hVW hW₀ i) (D.limitSpecIso W₀ V₀ hV₀ hVW hW₀)
      ((D.restrict V₀ hV₀.isCompact).toFixedStage i)
      ((D.restrict V₀ hV₀.isCompact).limitToFixedStage)
      (D.stageRingMap W₀ V₀ hVW i) (D.limitRingMap W₀ V₀ hVW)
      (D.stageSpecIso_inv_comp_toFixedStage W₀ V₀ hV₀ hVW hW₀ i)
      (D.limitSpecIso_inv_comp_limitToFixedStage W₀ V₀ hV₀ hVW hW₀) eK eL
      ((D.restrict V₀ hV₀.isCompact).projection i)
      ((D.restrict V₀ hV₀.isCompact).projection_comp_toFixedStage i)
      (CommRingCat.ofHom (PseudoCoherence.stageToLimitMap (D.baseRingAlgCocone W₀)
        Γ(V₀.toScheme, ⊤) i))
      (D.stageRingMap_comp_stageToLimitMap W₀ V₀ hVW i)
      (D.limitSpecIso_inv_comparison W₀ V₀ hV₀ hVW hW₀ i) φ

/-- **The avatar of a pseudo-coherent object is pseudo-coherent.** This is Stacks 09U7 along
`V₀ ⟶ X₀` and along `Scheme.isoSpec`, followed by Stacks 08E7 on `Spec Γ(V₀)`. -/
theorem isPseudoCoherent_of_isAvatarOver
    (hK₀ : RingedSpace.IsPseudoCoherent (X := D.X₀.left.toRingedSpace) K₀)
    (𝕂 : DerivedCategory (ModuleCat.{u} Γ(V₀.toScheme, ⊤)))
    (h : IsAvatarOver D.X₀.left V₀ hV₀ K₀ 𝕂) :
    StacksDraft.PseudoCoherence.IsPseudoCoherent 𝕂 := by
  have : IsAffine V₀.toScheme := hV₀
  obtain ⟨e⟩ := h
  have h1 := RingedSpace.KFlatDerivedPullback.isPseudoCoherent_derivedPullback
    (Scheme.isoSpec V₀.toScheme).inv.toLRSHom.toShHom _
    (RingedSpace.KFlatDerivedPullback.isPseudoCoherent_derivedPullback V₀.ι.toLRSHom.toShHom K₀ hK₀)
  obtain ⟨M, ⟨eM⟩⟩ : (DerivedCategory.Q (C := ModuleCat.{u} Γ(V₀.toScheme, ⊤))).essImage 𝕂 :=
    Functor.EssSurj.mem_essImage (F := DerivedCategory.Q) 𝕂
  have h3 : RingedSpace.IsPseudoCoherent (X := (Spec Γ(V₀.toScheme, ⊤)).toRingedSpace)
      (derivedTildeObj Γ(V₀.toScheme, ⊤) 𝕂) := h1.of_iso e
  have h4 : RingedSpace.IsPseudoCoherent (X := (Spec Γ(V₀.toScheme, ⊤)).toRingedSpace)
      (derivedTildeObj Γ(V₀.toScheme, ⊤) (DerivedCategory.Q.obj M)) :=
    h3.of_iso (derivedTildeObjMapIso _ eM.symm)
  have h2 : RingedSpace.IsPseudoCoherent
      (X := (Spec (CommRingCat.of Γ(V₀.toScheme, ⊤))).toRingedSpace)
      (DerivedCategory.Q.obj (((tilde.functor (CommRingCat.of Γ(V₀.toScheme, ⊤)) :
        ModuleCat.{u} Γ(V₀.toScheme, ⊤) ⥤
          StrictlyPerfect.OXMod.{u, u} (Spec (CommRingCat.of Γ(V₀.toScheme, ⊤))).toRingedSpace
        ).mapHomologicalComplex (ComplexShape.up ℤ)).obj M)) :=
    h4.of_iso ((tilde.functor Γ(V₀.toScheme, ⊤)).mapDerivedCategoryFactors.app M)
  exact ((RingedSpace.isPseudoCoherent_tilde_iff M).1 h2).ofIso eM

/-- **The avatar over `V₀` read over the universe-lifted ring of sections.** -/
theorem nonempty_liftedAvatarIso (𝕂 : DerivedCategory (ModuleCat.{u} Γ(V₀.toScheme, ⊤)))
    (e : IsAvatarOver D.X₀.left V₀ hV₀ K₀ 𝕂) :
    Nonempty ((derivedPullback (D.fixedSpecIso V₀ hV₀).inv.toLRSHom.toShHom).obj
        ((derivedPullback V₀.ι.toLRSHom.toShHom).obj K₀) ≅
      derivedTildeObj (CommRingCat.of (ULift.{u} Γ(V₀.toScheme, ⊤)))
        ((PseudoCoherence.baseLiftRestriction Γ(V₀.toScheme, ⊤)).obj 𝕂)) := by
  have : IsAffine V₀.toScheme := hV₀
  obtain ⟨e⟩ := e
  let σ := Scheme.Spec.mapIso (D.fixedRingLiftIso V₀).op
  let N := (PseudoCoherence.baseLiftRestriction Γ(V₀.toScheme, ⊤)).obj 𝕂
  have hinv : (D.fixedSpecIso V₀ hV₀).inv = σ.inv ≫ (Scheme.isoSpec V₀.toScheme).inv := rfl
  refine ⟨((Stacks.DerivedPullback.schemeFactorIso σ.inv (Scheme.isoSpec V₀.toScheme).inv
      (D.fixedSpecIso V₀ hV₀).inv hinv.symm).app _).symm ≪≫
    (derivedPullback σ.inv.toLRSHom.toShHom).mapIso e ≪≫
    (derivedPullback σ.inv.toLRSHom.toShHom).mapIso
      ((tilde.functor Γ(V₀.toScheme, ⊤)).mapDerivedCategory.mapIso
        ((totalDerivedRestrictExtendScalarsSelfIso.{u, u}
          (ULift.ringEquiv : ULift.{u} Γ(V₀.toScheme, ⊤) ≃+* Γ(V₀.toScheme, ⊤))).app 𝕂).symm) ≪≫
    (derivedPullback σ.inv.toLRSHom.toShHom).mapIso
      ((StandardModel.affinePullbackComparison _ _ (D.fixedRingLiftIso V₀).hom).app N).symm ≪≫
    (Stacks.DerivedPullback.schemeFactorIso σ.inv σ.hom (𝟙 _) σ.inv_hom_id).app _ ≪≫
    (Stacks.Cohomology.DerivedPushforwardAssociativity.derivedPullbackIdIso _).app _⟩

include hW₀ in
/-- **The avatar of an object of finite Tor dimension over `W₀` has finite Tor dimension over
`Γ(W₀)`.** The Tor-dimension clause of Stacks 0DI0 for `V₀ ⟶ W₀` transports along the
isomorphism of arrows with `Spec Γ(V₀) ⟶ Spec Γ(W₀)`, where it is Stacks 0DHY. -/
theorem hasFiniteTorDimension_of_isAvatarOver
    (hL₀tor : RingedSpace.LocallyHasFiniteTorDimension
      (RingedSpace.inverseImage W₀.toScheme.toRingedSpace (D.X₀.hom.resLE W₀ V₀ hVW).base)
      (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily _)
      ((Scheme.Hom.derivedScalarRestriction (D.X₀.hom.resLE W₀ V₀ hVW)).obj
        ((derivedPullback V₀.ι.toLRSHom.toShHom).obj L₀)))
    (𝕃 : DerivedCategory (ModuleCat.{u} Γ(V₀.toScheme, ⊤)))
    (h : IsAvatarOver D.X₀.left V₀ hV₀ L₀ 𝕃) :
    (letI : Algebra Γ(W₀.toScheme, ⊤) Γ(V₀.toScheme, ⊤) :=
      ((D.X₀.hom.resLE W₀ V₀ hVW).appTop).hom.toAlgebra
    HasFiniteTorDimensionCanonical Γ(W₀.toScheme, ⊤)
      ((ModuleCat.restrictScalars
        (algebraMap Γ(W₀.toScheme, ⊤) Γ(V₀.toScheme, ⊤))).mapDerivedCategory.obj 𝕃)) := by
  let : Algebra Γ(W₀.toScheme, ⊤) Γ(V₀.toScheme, ⊤) :=
    ((D.X₀.hom.resLE W₀ V₀ hVW).appTop).hom.toAlgebra
  have : IsAffine V₀.toScheme := hV₀
  have : IsAffine W₀.toScheme := hW₀
  obtain ⟨e⟩ := h
  let f := D.X₀.hom.resLE W₀ V₀ hVW
  let ε := Scheme.forgetToRingedSpace.mapIso (Scheme.isoSpec V₀.toScheme)
  let E' := derivedTildeObj Γ(V₀.toScheme, ⊤) 𝕃
  have e1 : (derivedPullback V₀.ι.toLRSHom.toShHom).obj L₀ ≅ (derivedPullback ε.hom).obj E' :=
    ((Stacks.Cohomology.TorAmplitude.derivedPullbackHomCompInvIso ε.symm).app _).symm ≪≫
      (derivedPullback ε.hom).mapIso e
  have h1 := RingedSpace.locallyHasFiniteTorDimension_canonicalCertificate_of_iso
    ((Scheme.Hom.derivedScalarRestriction f).mapIso e1) hL₀tor
  have h2 := RingedSpace.locallyHasFiniteTorDimension_canonicalCertificate_of_iso
    (Scheme.Hom.derivedMatchingIso f (Spec.map f.appTop) (Scheme.Hom.ringedArrowIsoSpec f) E') h1
  have h3 := (RingedSpace.locallyHasFiniteTorDimension_canonicalCertificate_iso_iff
    (Scheme.Hom.arrowInverseImageIso f (Spec.map f.appTop)
      (Scheme.Hom.ringedArrowIsoSpec f)) _).1 h2
  obtain ⟨M, ⟨eM⟩⟩ : (DerivedCategory.Q (C := ModuleCat.{u} Γ(V₀.toScheme, ⊤))).essImage 𝕃 :=
    Functor.EssSurj.mem_essImage (F := DerivedCategory.Q) 𝕃
  have e2 : E' ≅ AffinePerfectDescent.tildeObj Γ(V₀.toScheme, ⊤) M :=
    derivedTildeObjMapIso _ eM.symm ≪≫
      (tilde.functor Γ(V₀.toScheme, ⊤)).mapDerivedCategoryFactors.app M
  have h4 := RingedSpace.locallyHasFiniteTorDimension_canonicalCertificate_of_iso
    ((Scheme.Hom.derivedScalarRestriction (Spec.map f.appTop)).mapIso e2) h3
  have h5 := (AffinePerfectDescent.locallyHasFiniteTorDimension_tildeObj_iff Γ(W₀.toScheme, ⊤)
    Γ(V₀.toScheme, ⊤) M).1 h4
  obtain ⟨a, b, hab⟩ :=
    (hasFiniteTorDimensionCanonical_iff_exists_hasTorAmplitudeCanonical _ _).1 h5
  exact (hasFiniteTorDimensionCanonical_iff_exists_hasTorAmplitudeCanonical _ _).2
    ⟨a, b, AlgebraicGeometry.BaseChangeTorAmplitude.hasTorAmplitudeCanonical_of_iso
      (((ModuleCat.restrictScalars (algebraMap Γ(W₀.toScheme, ⊤) Γ(V₀.toScheme, ⊤))
        ).mapDerivedCategoryFactors.app M).symm ≪≫
        (ModuleCat.restrictScalars (algebraMap Γ(W₀.toScheme, ⊤) Γ(V₀.toScheme, ⊤))
          ).mapDerivedCategory.mapIso eM) a b hab⟩

include hW₀ in
/-- **The affine ring-translation dictionary of Stacks 0DI7 holds.** Over an affine open `V₀` of
`X₀` lying over an affine open `W₀` of `S₀`, for `K₀` pseudo-coherent and `L₀` with
quasi-coherent cohomology whose restriction to `V₀` has, over `W₀`, the Tor-dimension clause of
Stacks 0DI0, the identifications of the derived morphism sets over the stages and the limit with
those over the algebras of Stacks 0DHX exist and are natural. -/
theorem affineRingTranslation_of_isAffineOpen_resLE
    (hK₀ : RingedSpace.IsPseudoCoherent (X := D.X₀.left.toRingedSpace) K₀)
    (hL₀qc : ∀ n : ℤ,
      ((DerivedCategory.homologyFunctor D.X₀.left.Modules n).obj L₀).IsQuasicoherent)
    (hL₀tor : RingedSpace.LocallyHasFiniteTorDimension
      (RingedSpace.inverseImage W₀.toScheme.toRingedSpace (D.X₀.hom.resLE W₀ V₀ hVW).base)
      (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily _)
      ((Scheme.Hom.derivedScalarRestriction (D.X₀.hom.resLE W₀ V₀ hVW)).obj
        ((derivedPullback V₀.ι.toLRSHom.toShHom).obj L₀))) :
    D.AffineRingTranslation W₀ V₀ hV₀ hVW K₀ L₀ := by
  obtain ⟨𝕂, hK⟩ := exists_isAvatarOver_of_isPseudoCoherent D.X₀.left V₀ hV₀ K₀ hK₀
  obtain ⟨𝕃, hL⟩ := exists_isAvatarOver_of_isQuasicoherent D.X₀.left V₀ hV₀ L₀ hL₀qc
  obtain ⟨eK⟩ := D.nonempty_liftedAvatarIso V₀ hV₀ K₀ 𝕂 hK
  obtain ⟨eL⟩ := D.nonempty_liftedAvatarIso V₀ hV₀ L₀ 𝕃 hL
  have h𝕂 := D.isPseudoCoherent_of_isAvatarOver V₀ hV₀ K₀ hK₀ 𝕂 hK
  have h𝕃 := D.hasFiniteTorDimension_of_isAvatarOver W₀ V₀ hV₀ hVW hW₀ L₀ hL₀tor 𝕃 hL
  exact ⟨_, D.isNatural_affineDerivedHomEquivOfLiftedAvatar W₀ V₀ hV₀ hVW hW₀ K₀ L₀ 𝕂 𝕃 h𝕂 h𝕃
    eK eL⟩

include hW₀ in
/-- **Stacks 0DI7 over an affine open of `X₀` lying over an affine open of `S₀`.** If `K₀` is
pseudo-coherent and `L₀` has quasi-coherent cohomology sheaves and, restricted to `V₀`, the
Tor-dimension clause of Stacks 0DI0 over `W₀`, then the colimit over the stages of the derived
morphism sets between the derived pullbacks of `K₀|_{V₀}` and `L₀|_{V₀}` is the derived morphism
set over the limit. -/
theorem restrictHomDescent_of_isAffineOpen_resLE
    (hK₀ : RingedSpace.IsPseudoCoherent (X := D.X₀.left.toRingedSpace) K₀)
    (hL₀qc : ∀ n : ℤ,
      ((DerivedCategory.homologyFunctor D.X₀.left.Modules n).obj L₀).IsQuasicoherent)
    (hL₀tor : RingedSpace.LocallyHasFiniteTorDimension
      (RingedSpace.inverseImage W₀.toScheme.toRingedSpace (D.X₀.hom.resLE W₀ V₀ hVW).base)
      (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily _)
      ((Scheme.Hom.derivedScalarRestriction (D.X₀.hom.resLE W₀ V₀ hVW)).obj
        ((derivedPullback V₀.ι.toLRSHom.toShHom).obj L₀))) :
    D.RestrictHomDescent K₀ L₀ V₀ hV₀.isCompact :=
  D.restrictHomDescent_of_affineRingTranslation W₀ V₀ hV₀ hVW K₀ L₀ hW₀
    (D.affineRingTranslation_of_isAffineOpen_resLE W₀ V₀ hV₀ hVW hW₀ K₀ L₀ hK₀ hL₀qc hL₀tor)

end Dictionary


end AlgebraicGeometry.RelativeDescentSituation

end
