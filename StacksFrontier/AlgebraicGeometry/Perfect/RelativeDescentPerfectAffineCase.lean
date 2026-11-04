module

public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeDescentAffineCase
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeDescentAffineEssentialSurjectivity
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeDescentPerfectInduction
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectBaseOpen

/-!
# The affine case of the essential-surjectivity half of Stacks 0DI8

Let `D` be a relative descent situation of Stacks 0DI6, `W₀ ⊆ S₀` an affine open and
`V₀ ⊆ X₀` an affine open contained in the preimage of `W₀`. Restricted to `V₀`, the situation is
the filtered system of spectra of the algebras `Rᵢ ⊗_{R₀} A₀`, where `R₀ = Γ(W₀)`,
`Rᵢ = Γ(g_i^{-1}W₀)` and `A₀ = Γ(V₀)`, over the spectra of the `Rᵢ`; and the structure morphisms
`Vᵢ ⟶ Sᵢ` and `V ⟶ S` factor through the open subschemes `g_i^{-1}W₀` and `g^{-1}W₀`. This file
proves that every `S`-perfect object of `D(𝒪_V)` is the derived pullback of an `Sᵢ`-perfect object
of `D(𝒪_{Vᵢ})` at some stage, from the ring-theoretic case
`AlgebraicGeometry.AffinePerfectDescent.exists_isPerfectRelativeTo_stage`: relative perfectness
over `Sᵢ` is relative perfectness over the open `g_i^{-1}W₀`
(`AlgebraicGeometry.Scheme.Hom.isPerfectRelativeTo_baseOpen_iff`), and that transports along the
isomorphisms of arrows with the spectra
(`AlgebraicGeometry.Scheme.Hom.isPerfectRelativeTo_arrowIso_iff`).

## Main results

* `AlgebraicGeometry.RelativeDescentSituation.limitSpecIso_hom_comp_specMap` and
  `stageSpecIso_hom_comp_specMap`: the morphisms `V ⟶ g^{-1}W₀` and `Vᵢ ⟶ g_i^{-1}W₀` are, up to
  the identifications with spectra, the spectra of the base-change maps `R ⟶ R ⊗_{R₀} A₀` and
  `Rᵢ ⟶ Rᵢ ⊗_{R₀} A₀`.
* `AlgebraicGeometry.RelativeDescentSituation.projection_comp_stageSpecIso_hom`: the projection
  `V ⟶ Vᵢ` is the spectrum of `Rᵢ ⊗_{R₀} A₀ ⟶ R ⊗_{R₀} A₀`.
* `restrictPerfectEssentiallySurjective_of_isAffineOpenOverAffine`: **the affine case of the
  essential-surjectivity half of Stacks 0DI8** for a general situation.

## References

* [Stacks Project, Lemma 36.35.9 (Tag 0DI8)](https://stacks.math.columbia.edu/tag/0DI8)
* [Stacks Project, Tag 0DI6](https://stacks.math.columbia.edu/tag/0DI6)
* [Stacks Project, Tag 0DHX](https://stacks.math.columbia.edu/tag/0DHX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry StrictlyPerfect
open scoped TensorProduct
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.RelativeDescentSituation

variable {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] (D : RelativeDescentSituation.{u, u} I)

attribute [local implicit_reducible] restrict

variable (W₀ : (D.descent.system.obj (op D.descent.base)).Opens)
  (V₀ : D.X₀.left.Opens) (hV₀ : IsAffineOpen V₀) (hVW : V₀ ≤ D.X₀.hom ⁻¹ᵁ W₀)
  (hW₀ : IsAffineOpen W₀)

/-! ### The bases as spectra -/

/-- The preimage `g^{-1}W₀` of `W₀` in the limit `S`, as the spectrum of the colimit ring `R`. -/
def limitBaseSpecIso :
    (D.descent.limitCone.π.app (op D.descent.base) ⁻¹ᵁ W₀ : _).toScheme ≅
      Spec (CommRingCat.of (D.baseRingAlgCocone W₀).pt) :=
  have : IsAffine (D.descent.limitCone.π.app (op D.descent.base) ⁻¹ᵁ W₀ : _).toScheme :=
    D.isAffineOpen_preimage_baseProjection W₀ hW₀
  Scheme.isoSpec _

/-- The preimage `g_i^{-1}W₀` of `W₀` in the stage `Sᵢ`, as the spectrum of `Rᵢ`. -/
def stageBaseSpecIso (i : D.LaterIndex) :
    (D.baseMap i ⁻¹ᵁ W₀ : _).toScheme ≅ Spec (CommRingCat.of ((D.baseRingAlgDiagram W₀).obj i)) :=
  have : IsAffine (D.baseMap i ⁻¹ᵁ W₀ : _).toScheme := D.isAffineOpen_preimage_baseMap W₀ hW₀ i
  Scheme.isoSpec _

/-! ### The base legs of the pushout squares -/

/-- The base leg `R ⟶ R ⊗_{R₀} A₀ ⟶ Γ(V)` is the map of sections of `V ⟶ g^{-1}W₀`. -/
theorem includeLeft_comp_limitAlgebraIsoSections_hom :
    (letI : Algebra Γ(W₀.toScheme, ⊤) Γ(V₀.toScheme, ⊤) :=
      ((D.X₀.hom.resLE W₀ V₀ hVW).appTop).hom.toAlgebra
    CommRingCat.ofHom (algebraMap (D.baseRingAlgCocone W₀).pt
        ((D.baseRingAlgCocone W₀).pt ⊗[Γ(W₀.toScheme, ⊤)] Γ(V₀.toScheme, ⊤))) ≫
        (D.limitAlgebraIsoSections W₀ V₀ hV₀ hVW hW₀).hom =
      (D.restrictToBasePreimageLimit W₀ V₀ hV₀ hVW).appTop) :=
  IsPushout.inl_isoIsPushout_hom _ _ _
    (D.isPushout_appTop_restrictToBasePreimageLimit W₀ V₀ hV₀ hVW hW₀)

/-- The base leg `Rᵢ ⟶ Rᵢ ⊗_{R₀} A₀ ⟶ Γ(Vᵢ)` is the map of sections of `Vᵢ ⟶ g_i^{-1}W₀`. -/
theorem includeLeft_comp_stageAlgebraIsoSections_hom (i : D.LaterIndex) :
    (letI : Algebra Γ(W₀.toScheme, ⊤) Γ(V₀.toScheme, ⊤) :=
      ((D.X₀.hom.resLE W₀ V₀ hVW).appTop).hom.toAlgebra
    CommRingCat.ofHom (algebraMap ((D.baseRingAlgDiagram W₀).obj i)
        (PseudoCoherence.stageAlgebra (D.baseRingAlgDiagram W₀) Γ(V₀.toScheme, ⊤) i)) ≫
        (D.stageAlgebraIsoSections W₀ V₀ hV₀ hVW hW₀ i).hom =
      (D.restrictToBasePreimage W₀ V₀ hV₀ hVW i).appTop) :=
  IsPushout.inl_isoIsPushout_hom _ _ _
    (D.isPushout_appTop_restrictToBasePreimage W₀ V₀ hV₀ hVW hW₀ i)

/-- The fibre leg `A₀ ⟶ Rᵢ ⊗_{R₀} A₀ ⟶ Γ(Vᵢ)` is the map of sections of `Vᵢ ⟶ V₀`. -/
theorem includeRight_comp_stageAlgebraIsoSections_hom (i : D.LaterIndex) :
    (letI : Algebra Γ(W₀.toScheme, ⊤) Γ(V₀.toScheme, ⊤) :=
      ((D.X₀.hom.resLE W₀ V₀ hVW).appTop).hom.toAlgebra
    D.stageAlgebraUnit W₀ V₀ hVW i ≫ (D.stageAlgebraIsoSections W₀ V₀ hV₀ hVW hW₀ i).hom =
      ((D.restrict V₀ hV₀.isCompact).toFixedStage i).appTop) :=
  IsPushout.inr_isoIsPushout_hom _ _ _
    (D.isPushout_appTop_restrictToBasePreimage W₀ V₀ hV₀ hVW hW₀ i)

/-- The fibre leg `A₀ ⟶ R ⊗_{R₀} A₀ ⟶ Γ(V)` is the map of sections of `V ⟶ V₀`. -/
theorem includeRight_comp_limitAlgebraIsoSections_hom :
    (letI : Algebra Γ(W₀.toScheme, ⊤) Γ(V₀.toScheme, ⊤) :=
      ((D.X₀.hom.resLE W₀ V₀ hVW).appTop).hom.toAlgebra
    D.limitAlgebraUnit W₀ V₀ hVW ≫ (D.limitAlgebraIsoSections W₀ V₀ hV₀ hVW hW₀).hom =
      ((D.restrict V₀ hV₀.isCompact).limitToFixedStage).appTop) :=
  IsPushout.inr_isoIsPushout_hom _ _ _
    (D.isPushout_appTop_restrictToBasePreimageLimit W₀ V₀ hV₀ hVW hW₀)

/-! ### The structure morphisms as spectra of base-change maps -/

/-- A morphism of affine schemes with sections map `a ≫ e.hom` is, up to the identifications
`isoSpec` and `e`, the spectrum of `a`. -/
private theorem isoSpec_hom_comp_specMap_eq {X Y : Scheme} [IsAffine X] [IsAffine Y] (f : X ⟶ Y)
    {A : CommRingCat} (a : Γ(Y, ⊤) ⟶ A) (e : A ≅ Γ(X, ⊤)) (h : a ≫ e.hom = f.appTop) :
    (X.isoSpec ≪≫ Scheme.Spec.mapIso e.op).hom ≫ Spec.map a = f ≫ Y.isoSpec.hom := by
  simp [← Spec.map_comp, h, Scheme.isoSpec_hom_naturality]

/-- **`V ⟶ g^{-1}W₀` is the spectrum of `R ⟶ R ⊗_{R₀} A₀`.** -/
theorem limitSpecIso_hom_comp_specMap :
    (letI : Algebra Γ(W₀.toScheme, ⊤) Γ(V₀.toScheme, ⊤) :=
      ((D.X₀.hom.resLE W₀ V₀ hVW).appTop).hom.toAlgebra
    (D.limitSpecIso W₀ V₀ hV₀ hVW hW₀).hom ≫
        AffineRelativeTorAmplitude.specMap (D.baseRingAlgCocone W₀).pt
          ((D.baseRingAlgCocone W₀).pt ⊗[Γ(W₀.toScheme, ⊤)] Γ(V₀.toScheme, ⊤)) =
      D.restrictToBasePreimageLimit W₀ V₀ hV₀ hVW ≫ (D.limitBaseSpecIso W₀ hW₀).hom) :=
  let : Algebra Γ(W₀.toScheme, ⊤) Γ(V₀.toScheme, ⊤) :=
    ((D.X₀.hom.resLE W₀ V₀ hVW).appTop).hom.toAlgebra
  have : IsAffine ((D.restrict V₀ hV₀.isCompact).limitScheme) :=
    D.isAffine_restrict_limitScheme V₀ hV₀
  have : IsAffine (D.descent.limitCone.π.app (op D.descent.base) ⁻¹ᵁ W₀ : _).toScheme :=
    D.isAffineOpen_preimage_baseProjection W₀ hW₀
  isoSpec_hom_comp_specMap_eq (D.restrictToBasePreimageLimit W₀ V₀ hV₀ hVW) _
    (D.limitAlgebraIsoSections W₀ V₀ hV₀ hVW hW₀)
    (D.includeLeft_comp_limitAlgebraIsoSections_hom W₀ V₀ hV₀ hVW hW₀)

/-- **`Vᵢ ⟶ g_i^{-1}W₀` is the spectrum of `Rᵢ ⟶ Rᵢ ⊗_{R₀} A₀`.** -/
theorem stageSpecIso_hom_comp_specMap (i : D.LaterIndex) :
    (letI : Algebra Γ(W₀.toScheme, ⊤) Γ(V₀.toScheme, ⊤) :=
      ((D.X₀.hom.resLE W₀ V₀ hVW).appTop).hom.toAlgebra
    (D.stageSpecIso W₀ V₀ hV₀ hVW hW₀ i).hom ≫
        AffineRelativeTorAmplitude.specMap ((D.baseRingAlgDiagram W₀).obj i)
          (PseudoCoherence.stageAlgebra (D.baseRingAlgDiagram W₀) Γ(V₀.toScheme, ⊤) i) =
      D.restrictToBasePreimage W₀ V₀ hV₀ hVW i ≫ (D.stageBaseSpecIso W₀ hW₀ i).hom) :=
  let : Algebra Γ(W₀.toScheme, ⊤) Γ(V₀.toScheme, ⊤) :=
    ((D.X₀.hom.resLE W₀ V₀ hVW).appTop).hom.toAlgebra
  have : IsAffine ((D.restrict V₀ hV₀.isCompact).schemeAt i) :=
    D.isAffine_restrict_schemeAt V₀ hV₀ i
  have : IsAffine (D.baseMap i ⁻¹ᵁ W₀ : _).toScheme := D.isAffineOpen_preimage_baseMap W₀ hW₀ i
  isoSpec_hom_comp_specMap_eq (D.restrictToBasePreimage W₀ V₀ hV₀ hVW i) _
    (D.stageAlgebraIsoSections W₀ V₀ hV₀ hVW hW₀ i)
    (D.includeLeft_comp_stageAlgebraIsoSections_hom W₀ V₀ hV₀ hVW hW₀ i)

/-! ### The projection to a stage as the spectrum of the comparison of algebras -/

/-- The base-change map `Rᵢ ⊗_{R₀} A₀ ⟶ R ⊗_{R₀} A₀` restricts to `Rᵢ ⟶ R` on the base leg. -/
theorem includeLeft_comp_stageToLimitMap (i : D.LaterIndex) :
    (letI : Algebra Γ(W₀.toScheme, ⊤) Γ(V₀.toScheme, ⊤) :=
      ((D.X₀.hom.resLE W₀ V₀ hVW).appTop).hom.toAlgebra
    CommRingCat.ofHom (algebraMap ((D.baseRingAlgDiagram W₀).obj i)
        (PseudoCoherence.stageAlgebra (D.baseRingAlgDiagram W₀) Γ(V₀.toScheme, ⊤) i)) ≫
        CommRingCat.ofHom (PseudoCoherence.stageToLimitMap (D.baseRingAlgCocone W₀)
          Γ(V₀.toScheme, ⊤) i) =
      (D.baseProjectionPreimage W₀ i).appTop ≫
        CommRingCat.ofHom (algebraMap (D.baseRingAlgCocone W₀).pt
          ((D.baseRingAlgCocone W₀).pt ⊗[Γ(W₀.toScheme, ⊤)] Γ(V₀.toScheme, ⊤)))) := by
  ext x
  simp [PseudoCoherence.stageToLimitMap]
  rfl

/-- The base-change map `Rᵢ ⊗_{R₀} A₀ ⟶ R ⊗_{R₀} A₀` is the identity on the fibre leg. -/
theorem includeRight_comp_stageToLimitMap (i : D.LaterIndex) :
    (letI : Algebra Γ(W₀.toScheme, ⊤) Γ(V₀.toScheme, ⊤) :=
      ((D.X₀.hom.resLE W₀ V₀ hVW).appTop).hom.toAlgebra
    D.stageAlgebraUnit W₀ V₀ hVW i ≫
        CommRingCat.ofHom (PseudoCoherence.stageToLimitMap (D.baseRingAlgCocone W₀)
          Γ(V₀.toScheme, ⊤) i) =
      D.limitAlgebraUnit W₀ V₀ hVW) := by
  let : Algebra Γ(W₀.toScheme, ⊤) Γ(V₀.toScheme, ⊤) :=
    ((D.X₀.hom.resLE W₀ V₀ hVW).appTop).hom.toAlgebra
  ext x
  show (PseudoCoherence.stageToLimitMap (D.baseRingAlgCocone W₀) Γ(V₀.toScheme, ⊤) i)
    ((1 : (D.baseRingAlgDiagram W₀).obj i) ⊗ₜ x) = 1 ⊗ₜ x
  simp [PseudoCoherence.stageToLimitMap]

/-- **On sections, the projection `V ⟶ Vᵢ` is `Rᵢ ⊗_{R₀} A₀ ⟶ R ⊗_{R₀} A₀`.** Both maps out of
the tensor product agree on its two legs. -/
theorem stageAlgebraIsoSections_hom_comp_projection_appTop (i : D.LaterIndex) :
    (letI : Algebra Γ(W₀.toScheme, ⊤) Γ(V₀.toScheme, ⊤) :=
      ((D.X₀.hom.resLE W₀ V₀ hVW).appTop).hom.toAlgebra
    (D.stageAlgebraIsoSections W₀ V₀ hV₀ hVW hW₀ i).hom ≫
        ((D.restrict V₀ hV₀.isCompact).projection i).appTop =
      CommRingCat.ofHom (PseudoCoherence.stageToLimitMap (D.baseRingAlgCocone W₀)
          Γ(V₀.toScheme, ⊤) i) ≫ (D.limitAlgebraIsoSections W₀ V₀ hV₀ hVW hW₀).hom) :=
  let : Algebra Γ(W₀.toScheme, ⊤) Γ(V₀.toScheme, ⊤) :=
    ((D.X₀.hom.resLE W₀ V₀ hVW).appTop).hom.toAlgebra
  by
  refine (CommRingCat.isPushout_tensorProduct Γ(W₀.toScheme, ⊤) ((D.baseRingAlgDiagram W₀).obj i)
    Γ(V₀.toScheme, ⊤)).hom_ext ?_ ?_
  · have e1 : CommRingCat.ofHom (algebraMap ((D.baseRingAlgDiagram W₀).obj i)
          (PseudoCoherence.stageAlgebra (D.baseRingAlgDiagram W₀) Γ(V₀.toScheme, ⊤) i)) ≫
          (D.stageAlgebraIsoSections W₀ V₀ hV₀ hVW hW₀ i).hom ≫
            ((D.restrict V₀ hV₀.isCompact).projection i).appTop =
        (D.restrictToBasePreimage W₀ V₀ hV₀ hVW i).appTop ≫
          ((D.restrict V₀ hV₀.isCompact).projection i).appTop :=
      (Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ ((D.restrict V₀ hV₀.isCompact).projection i).appTop)
          (D.includeLeft_comp_stageAlgebraIsoSections_hom W₀ V₀ hV₀ hVW hW₀ i))
    have e2 : (D.restrictToBasePreimage W₀ V₀ hV₀ hVW i).appTop ≫
          ((D.restrict V₀ hV₀.isCompact).projection i).appTop =
        (D.baseProjectionPreimage W₀ i).appTop ≫
          (D.restrictToBasePreimageLimit W₀ V₀ hV₀ hVW).appTop :=
      congrArg Scheme.Hom.appTop
        (D.restrictToBasePreimageLimit_comp_baseProjectionPreimage W₀ V₀ hV₀ hVW i).symm
    have e3 : CommRingCat.ofHom (algebraMap ((D.baseRingAlgDiagram W₀).obj i)
          (PseudoCoherence.stageAlgebra (D.baseRingAlgDiagram W₀) Γ(V₀.toScheme, ⊤) i)) ≫
          CommRingCat.ofHom (PseudoCoherence.stageToLimitMap (D.baseRingAlgCocone W₀)
            Γ(V₀.toScheme, ⊤) i) ≫ (D.limitAlgebraIsoSections W₀ V₀ hV₀ hVW hW₀).hom =
        (D.baseProjectionPreimage W₀ i).appTop ≫
          (D.restrictToBasePreimageLimit W₀ V₀ hV₀ hVW).appTop :=
      (Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ (D.limitAlgebraIsoSections W₀ V₀ hV₀ hVW hW₀).hom)
          (D.includeLeft_comp_stageToLimitMap W₀ V₀ hVW i)).trans
          ((Category.assoc _ _ _).trans (congrArg ((D.baseProjectionPreimage W₀ i).appTop ≫ ·)
            (D.includeLeft_comp_limitAlgebraIsoSections_hom W₀ V₀ hV₀ hVW hW₀))))
    exact e1.trans (e2.trans e3.symm)
  · have e1 : D.stageAlgebraUnit W₀ V₀ hVW i ≫
          (D.stageAlgebraIsoSections W₀ V₀ hV₀ hVW hW₀ i).hom ≫
            ((D.restrict V₀ hV₀.isCompact).projection i).appTop =
        ((D.restrict V₀ hV₀.isCompact).limitToFixedStage).appTop :=
      (Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ ((D.restrict V₀ hV₀.isCompact).projection i).appTop)
          (D.includeRight_comp_stageAlgebraIsoSections_hom W₀ V₀ hV₀ hVW hW₀ i)).trans
          (congrArg Scheme.Hom.appTop
            ((D.restrict V₀ hV₀.isCompact).projection_comp_toFixedStage i)))
    have e3 : D.stageAlgebraUnit W₀ V₀ hVW i ≫
          CommRingCat.ofHom (PseudoCoherence.stageToLimitMap (D.baseRingAlgCocone W₀)
            Γ(V₀.toScheme, ⊤) i) ≫ (D.limitAlgebraIsoSections W₀ V₀ hV₀ hVW hW₀).hom =
        ((D.restrict V₀ hV₀.isCompact).limitToFixedStage).appTop :=
      (Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ (D.limitAlgebraIsoSections W₀ V₀ hV₀ hVW hW₀).hom)
          (D.includeRight_comp_stageToLimitMap W₀ V₀ hVW i)).trans
          (D.includeRight_comp_limitAlgebraIsoSections_hom W₀ V₀ hV₀ hVW hW₀))
    exact e1.trans e3.symm

/-- **The projection `V ⟶ Vᵢ` is the spectrum of `Rᵢ ⊗_{R₀} A₀ ⟶ R ⊗_{R₀} A₀`**, through the
identifications of `V` and `Vᵢ` with spectra. -/
theorem projection_comp_stageSpecIso_hom (i : D.LaterIndex) :
    (letI : Algebra Γ(W₀.toScheme, ⊤) Γ(V₀.toScheme, ⊤) :=
      ((D.X₀.hom.resLE W₀ V₀ hVW).appTop).hom.toAlgebra
    (D.restrict V₀ hV₀.isCompact).projection i ≫ (D.stageSpecIso W₀ V₀ hV₀ hVW hW₀ i).hom =
      (D.limitSpecIso W₀ V₀ hV₀ hVW hW₀).hom ≫
        Spec.map (CommRingCat.ofHom (PseudoCoherence.stageToLimitMap (D.baseRingAlgCocone W₀)
          Γ(V₀.toScheme, ⊤) i))) :=
  let : Algebra Γ(W₀.toScheme, ⊤) Γ(V₀.toScheme, ⊤) :=
    ((D.X₀.hom.resLE W₀ V₀ hVW).appTop).hom.toAlgebra
  have : IsAffine ((D.restrict V₀ hV₀.isCompact).schemeAt i) :=
    D.isAffine_restrict_schemeAt V₀ hV₀ i
  have : IsAffine ((D.restrict V₀ hV₀.isCompact).limitScheme) :=
    D.isAffine_restrict_limitScheme V₀ hV₀
  by
  calc (D.restrict V₀ hV₀.isCompact).projection i ≫
        (((D.restrict V₀ hV₀.isCompact).schemeAt i).isoSpec.hom ≫
          Spec.map (D.stageAlgebraIsoSections W₀ V₀ hV₀ hVW hW₀ i).hom)
      = ((D.restrict V₀ hV₀.isCompact).limitScheme.isoSpec.hom ≫
          Spec.map ((D.restrict V₀ hV₀.isCompact).projection i).appTop) ≫
          Spec.map (D.stageAlgebraIsoSections W₀ V₀ hV₀ hVW hW₀ i).hom := by
        rw [← Category.assoc, Scheme.isoSpec_hom_naturality]
    _ = (D.restrict V₀ hV₀.isCompact).limitScheme.isoSpec.hom ≫
          Spec.map ((D.stageAlgebraIsoSections W₀ V₀ hV₀ hVW hW₀ i).hom ≫
            ((D.restrict V₀ hV₀.isCompact).projection i).appTop) := by
        rw [Spec.map_comp, Category.assoc]
    _ = (D.restrict V₀ hV₀.isCompact).limitScheme.isoSpec.hom ≫
          Spec.map (CommRingCat.ofHom (PseudoCoherence.stageToLimitMap (D.baseRingAlgCocone W₀)
            Γ(V₀.toScheme, ⊤) i) ≫ (D.limitAlgebraIsoSections W₀ V₀ hV₀ hVW hW₀).hom) := by
        rw [D.stageAlgebraIsoSections_hom_comp_projection_appTop W₀ V₀ hV₀ hVW hW₀ i]
    _ = ((D.restrict V₀ hV₀.isCompact).limitScheme.isoSpec.hom ≫
          Spec.map (D.limitAlgebraIsoSections W₀ V₀ hV₀ hVW hW₀).hom) ≫
          Spec.map (CommRingCat.ofHom (PseudoCoherence.stageToLimitMap (D.baseRingAlgCocone W₀)
            Γ(V₀.toScheme, ⊤) i)) := by
        rw [Spec.map_comp, Category.assoc]

/-! ### The arrows over the bases as arrows of spectra -/

/-- The arrow `V ⟶ g^{-1}W₀` is isomorphic to the arrow `Spec(R ⊗_{R₀} A₀) ⟶ Spec R`. -/
def limitArrowIso :
    (letI : Algebra Γ(W₀.toScheme, ⊤) Γ(V₀.toScheme, ⊤) :=
      ((D.X₀.hom.resLE W₀ V₀ hVW).appTop).hom.toAlgebra
    Arrow.mk (D.restrictToBasePreimageLimit W₀ V₀ hV₀ hVW) ≅
      Arrow.mk (AffineRelativeTorAmplitude.specMap (D.baseRingAlgCocone W₀).pt
        ((D.baseRingAlgCocone W₀).pt ⊗[Γ(W₀.toScheme, ⊤)] Γ(V₀.toScheme, ⊤)))) :=
  let : Algebra Γ(W₀.toScheme, ⊤) Γ(V₀.toScheme, ⊤) :=
    ((D.X₀.hom.resLE W₀ V₀ hVW).appTop).hom.toAlgebra
  Arrow.isoMk (D.limitSpecIso W₀ V₀ hV₀ hVW hW₀) (D.limitBaseSpecIso W₀ hW₀)
    (D.limitSpecIso_hom_comp_specMap W₀ V₀ hV₀ hVW hW₀)

/-- The arrow `Vᵢ ⟶ g_i^{-1}W₀` is isomorphic to the arrow `Spec(Rᵢ ⊗_{R₀} A₀) ⟶ Spec Rᵢ`. -/
def stageArrowIso (i : D.LaterIndex) :
    (letI : Algebra Γ(W₀.toScheme, ⊤) Γ(V₀.toScheme, ⊤) :=
      ((D.X₀.hom.resLE W₀ V₀ hVW).appTop).hom.toAlgebra
    Arrow.mk (D.restrictToBasePreimage W₀ V₀ hV₀ hVW i) ≅
      Arrow.mk (AffineRelativeTorAmplitude.specMap ((D.baseRingAlgDiagram W₀).obj i)
        (PseudoCoherence.stageAlgebra (D.baseRingAlgDiagram W₀) Γ(V₀.toScheme, ⊤) i))) :=
  let : Algebra Γ(W₀.toScheme, ⊤) Γ(V₀.toScheme, ⊤) :=
    ((D.X₀.hom.resLE W₀ V₀ hVW).appTop).hom.toAlgebra
  Arrow.isoMk (D.stageSpecIso W₀ V₀ hV₀ hVW hW₀ i) (D.stageBaseSpecIso W₀ hW₀ i)
    (D.stageSpecIso_hom_comp_specMap W₀ V₀ hV₀ hVW hW₀ i)

/-- The morphism `V ⟶ g^{-1}W₀` is the composite of the identification of `V` with
`Spec(R ⊗_{R₀} A₀)`, the spectrum of `R ⟶ R ⊗_{R₀} A₀`, and the identification of `Spec R` with
`g^{-1}W₀`. -/
theorem restrictToBasePreimageLimit_eq :
    (letI : Algebra Γ(W₀.toScheme, ⊤) Γ(V₀.toScheme, ⊤) :=
      ((D.X₀.hom.resLE W₀ V₀ hVW).appTop).hom.toAlgebra
    D.restrictToBasePreimageLimit W₀ V₀ hV₀ hVW =
      ((D.limitSpecIso W₀ V₀ hV₀ hVW hW₀).hom ≫
        AffineRelativeTorAmplitude.specMap (D.baseRingAlgCocone W₀).pt
          ((D.baseRingAlgCocone W₀).pt ⊗[Γ(W₀.toScheme, ⊤)] Γ(V₀.toScheme, ⊤))) ≫
        (D.limitBaseSpecIso W₀ hW₀).inv) :=
  (Iso.eq_comp_inv _).2 (D.limitSpecIso_hom_comp_specMap W₀ V₀ hV₀ hVW hW₀).symm

/-- The morphism `Vᵢ ⟶ g_i^{-1}W₀` is the composite of the identification of `Vᵢ` with
`Spec(Rᵢ ⊗_{R₀} A₀)`, the spectrum of `Rᵢ ⟶ Rᵢ ⊗_{R₀} A₀`, and the identification of `Spec Rᵢ`
with `g_i^{-1}W₀`. -/
theorem restrictToBasePreimage_eq (i : D.LaterIndex) :
    (letI : Algebra Γ(W₀.toScheme, ⊤) Γ(V₀.toScheme, ⊤) :=
      ((D.X₀.hom.resLE W₀ V₀ hVW).appTop).hom.toAlgebra
    D.restrictToBasePreimage W₀ V₀ hV₀ hVW i =
      ((D.stageSpecIso W₀ V₀ hV₀ hVW hW₀ i).hom ≫
        AffineRelativeTorAmplitude.specMap ((D.baseRingAlgDiagram W₀).obj i)
          (PseudoCoherence.stageAlgebra (D.baseRingAlgDiagram W₀) Γ(V₀.toScheme, ⊤) i)) ≫
        (D.stageBaseSpecIso W₀ hW₀ i).inv) :=
  (Iso.eq_comp_inv _).2 (D.stageSpecIso_hom_comp_specMap W₀ V₀ hV₀ hVW hW₀ i).symm

include hW₀ in
/-- `V ⟶ g^{-1}W₀` is flat and locally of finite presentation. -/
theorem flat_restrictToBasePreimageLimit :
    Flat (D.restrictToBasePreimageLimit W₀ V₀ hV₀ hVW) ∧
      LocallyOfFinitePresentation (D.restrictToBasePreimageLimit W₀ V₀ hV₀ hVW) := by
  let : Algebra Γ(W₀.toScheme, ⊤) Γ(V₀.toScheme, ⊤) :=
    ((D.X₀.hom.resLE W₀ V₀ hVW).appTop).hom.toAlgebra
  have : Module.Flat Γ(W₀.toScheme, ⊤) Γ(V₀.toScheme, ⊤) :=
    D.moduleFlat_appTop_resLE W₀ V₀ hVW hW₀ hV₀
  have : Algebra.FinitePresentation Γ(W₀.toScheme, ⊤) Γ(V₀.toScheme, ⊤) :=
    D.algebraFinitePresentation_appTop_resLE W₀ V₀ hVW hW₀ hV₀
  rw [D.restrictToBasePreimageLimit_eq W₀ V₀ hV₀ hVW hW₀]
  exact ⟨inferInstance, inferInstance⟩

include hW₀ in
/-- `Vᵢ ⟶ g_i^{-1}W₀` is flat and locally of finite presentation. -/
theorem flat_restrictToBasePreimage (i : D.LaterIndex) :
    Flat (D.restrictToBasePreimage W₀ V₀ hV₀ hVW i) ∧
      LocallyOfFinitePresentation (D.restrictToBasePreimage W₀ V₀ hV₀ hVW i) := by
  let : Algebra Γ(W₀.toScheme, ⊤) Γ(V₀.toScheme, ⊤) :=
    ((D.X₀.hom.resLE W₀ V₀ hVW).appTop).hom.toAlgebra
  have : Module.Flat Γ(W₀.toScheme, ⊤) Γ(V₀.toScheme, ⊤) :=
    D.moduleFlat_appTop_resLE W₀ V₀ hVW hW₀ hV₀
  have : Algebra.FinitePresentation Γ(W₀.toScheme, ⊤) Γ(V₀.toScheme, ⊤) :=
    D.algebraFinitePresentation_appTop_resLE W₀ V₀ hVW hW₀ hV₀
  rw [D.restrictToBasePreimage_eq W₀ V₀ hV₀ hVW hW₀ i]
  exact ⟨inferInstance, inferInstance⟩

/-! ### The affine case -/

include hW₀ hVW in
/-- **The affine case of the essential-surjectivity half of Stacks 0DI8, over a given affine open
of the base.** For an affine open `V₀ ⊆ X₀` contained in the preimage of an affine open `W₀ ⊆ S₀`,
every object of `D(𝒪_V)` perfect relative to `S` is the derived pullback along `V ⟶ Vᵢ` of an
object of `D(𝒪_{Vᵢ})` perfect relative to `Sᵢ`, for some stage `i`. -/
theorem restrictPerfectEssentiallySurjective_of_le :
    D.RestrictPerfectEssentiallySurjective V₀ hV₀.isCompact := by
  let : Algebra Γ(W₀.toScheme, ⊤) Γ(V₀.toScheme, ⊤) :=
    ((D.X₀.hom.resLE W₀ V₀ hVW).appTop).hom.toAlgebra
  have : Module.Flat Γ(W₀.toScheme, ⊤) Γ(V₀.toScheme, ⊤) :=
    D.moduleFlat_appTop_resLE W₀ V₀ hVW hW₀ hV₀
  have : Algebra.FinitePresentation Γ(W₀.toScheme, ⊤) Γ(V₀.toScheme, ⊤) :=
    D.algebraFinitePresentation_appTop_resLE W₀ V₀ hVW hW₀ hV₀
  have : IsFiltered D.LaterIndex := D.isFiltered_laterIndex
  have hc := PseudoCoherence.isColimit_mapCocone_commAlgCat_uliftFunctor
    (D.isColimitBaseRingAlgCocone W₀ hW₀)
  have : Flat D.X₀.hom := D.flat
  have : LocallyOfFinitePresentation D.X₀.hom :=
    D.finitePresentation.locallyOfFinitePresentation
  have : IsAffine (D.restrict V₀ hV₀.isCompact).limitScheme :=
    D.isAffine_restrict_limitScheme V₀ hV₀
  obtain ⟨hfl, hlfp⟩ := D.flat_restrictToBasePreimageLimit W₀ V₀ hV₀ hVW hW₀
  unfold RestrictPerfectEssentiallySurjective PerfectEssentiallySurjectiveCanonical
    PerfectEssentiallySurjective
  intro E hE
  have h1 := (Scheme.Hom.isPerfectRelativeTo_baseOpen_iff
    (D.restrictToBasePreimageLimit W₀ V₀ hV₀ hVW)
    (D.descent.limitCone.π.app (op D.descent.base) ⁻¹ᵁ W₀).ι
    (D.restrictToBasePreimageLimit_comp_ι W₀ V₀ hV₀ hVW) E).1 hE
  let φ : Scheme.Hom.ringedArrow (D.restrictToBasePreimageLimit W₀ V₀ hV₀ hVW) ≅
      Scheme.Hom.ringedArrow (AffineRelativeTorAmplitude.specMap (D.baseRingAlgCocone W₀).pt
        ((D.baseRingAlgCocone W₀).pt ⊗[Γ(W₀.toScheme, ⊤)] Γ(V₀.toScheme, ⊤))) :=
    Scheme.forgetToRingedSpace.mapArrow.mapIso (D.limitArrowIso W₀ V₀ hV₀ hVW hW₀)
  let E' := (derivedPullback (D.limitSpecIso W₀ V₀ hV₀ hVW hW₀).inv.toLRSHom.toShHom).obj E
  have eE : (derivedPullback (Scheme.Hom.arrowLeftIso _ _ φ).hom).obj E' ≅ E :=
    (Stacks.Cohomology.TorAmplitude.derivedPullbackHomCompInvIso
      (Scheme.forgetToRingedSpace.mapIso (D.limitSpecIso W₀ V₀ hV₀ hVW hW₀)).symm).app E
  have := Scheme.Hom.isClosedUnderIsomorphisms_isPerfectRelativeTo
    (D.restrictToBasePreimageLimit W₀ V₀ hV₀ hVW)
    (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily _)
  have hE' := (Scheme.Hom.isPerfectRelativeTo_arrowIso_iff _ _ φ E').1
    ((Scheme.Hom.isPerfectRelativeTo (D.restrictToBasePreimageLimit W₀ V₀ hV₀ hVW)
      (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily _)).prop_of_iso eE.symm h1)
  obtain ⟨i, Ei', hEi', ⟨eEi'⟩⟩ := AffinePerfectDescent.exists_isPerfectRelativeTo_stage
    (D.baseRingAlgDiagram W₀) (D.baseRingAlgCocone W₀) hc Γ(V₀.toScheme, ⊤) E' hE'
  have : IsAffine ((D.restrict V₀ hV₀.isCompact).schemeAt i) :=
    D.isAffine_restrict_schemeAt V₀ hV₀ i
  obtain ⟨hfli, hlfpi⟩ := D.flat_restrictToBasePreimage W₀ V₀ hV₀ hVW hW₀ i
  let φi : Scheme.Hom.ringedArrow (D.restrictToBasePreimage W₀ V₀ hV₀ hVW i) ≅
      Scheme.Hom.ringedArrow (AffineRelativeTorAmplitude.specMap ((D.baseRingAlgDiagram W₀).obj i)
        (PseudoCoherence.stageAlgebra (D.baseRingAlgDiagram W₀) Γ(V₀.toScheme, ⊤) i)) :=
    Scheme.forgetToRingedSpace.mapArrow.mapIso (D.stageArrowIso W₀ V₀ hV₀ hVW hW₀ i)
  refine ⟨i, (derivedPullback (D.stageSpecIso W₀ V₀ hV₀ hVW hW₀ i).hom.toLRSHom.toShHom).obj Ei',
    (Scheme.Hom.isPerfectRelativeTo_baseOpen_iff (D.restrictToBasePreimage W₀ V₀ hV₀ hVW i)
      (D.baseMap i ⁻¹ᵁ W₀).ι (D.restrictToBasePreimage_comp_ι W₀ V₀ hV₀ hVW i) _).2
      ((Scheme.Hom.isPerfectRelativeTo_arrowIso_iff _ _ φi Ei').2 hEi'), ⟨?_⟩⟩
  exact (Stacks.DerivedPullback.schemeFactorIso ((D.restrict V₀ hV₀.isCompact).projection i)
      (D.stageSpecIso W₀ V₀ hV₀ hVW hW₀ i).hom _
      (D.projection_comp_stageSpecIso_hom W₀ V₀ hV₀ hVW hW₀ i)).app Ei' ≪≫
    ((Stacks.DerivedPullback.schemeFactorIso (D.limitSpecIso W₀ V₀ hV₀ hVW hW₀).hom
      (Spec.map (CommRingCat.ofHom (PseudoCoherence.stageToLimitMap (D.baseRingAlgCocone W₀)
        Γ(V₀.toScheme, ⊤) i))) _ rfl).app Ei').symm ≪≫
    (derivedPullback (D.limitSpecIso W₀ V₀ hV₀ hVW hW₀).hom.toLRSHom.toShHom).mapIso eEi' ≪≫ eE

/-- **The affine case of the essential-surjectivity half of Stacks 0DI8.** For an affine open
`V₀ ⊆ X₀` lying over an affine open of `S₀`, every object of `D(𝒪_V)` perfect relative to `S` is,
at some stage `i`, the derived pullback along `V ⟶ Vᵢ` of an object of `D(𝒪_{Vᵢ})` perfect
relative to `Sᵢ`. -/
theorem restrictPerfectEssentiallySurjective_of_isAffineOpenOverAffine
    (hQ : D.IsAffineOpenOverAffine V₀) :
    D.RestrictPerfectEssentiallySurjective V₀ hV₀.isCompact := by
  obtain ⟨W₀, hW₀, hVW⟩ := hQ
  exact D.restrictPerfectEssentiallySurjective_of_le W₀ V₀ hV₀ hVW hW₀

end AlgebraicGeometry.RelativeDescentSituation

end
