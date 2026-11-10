module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleLocalDual
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedEpsilonKernelLocal

/-!
# Stacks 0D0X: local surjectivity of the comparison of degree `-1` cohomology sheaves

Step M4 of the proof of Stacks 0D0X shows that the adjunct `ε^*𝒦₀ ⟶ 𝒦` of
`κ_{-1} : 𝒦₀ ⟶ ε_*𝒦` is an isomorphism by checking that its concrete model
`V ↦ (𝒪_X(V) ⊗_{𝒪_{X₀}(L V)} 𝒦₀(L V) ⟶ 𝒦(V))` is locally bijective.  This file provides the
Zariski half of the generators: over an affine Zariski square `Z ⊆ f_0^{-1}W`, every chart class
`h ∈ H₁(L_{𝒪_X(ε Z)/𝒪_Y(ε W)})` gives a section `m_h` of `𝒦₀` over `Z` whose image under
`κ_{-1}` is the section of `𝒦` attached to `h`.

## Main results

* `AlgebraicGeometry.Space.representedZariskiKernelSection`: the section `m_h` of `𝒦₀` over `Z`.
* `AlgebraicGeometry.Space.isAffine_representedEpsilonFunctor_obj`: the étale chart `ε(Z)` of an
  affine Zariski open is affine.
* `AlgebraicGeometry.Space.representedEpsilonKernelHom_app_representedZariskiKernelSection`:
  `κ_{-1}(m_h)` is the section of `𝒦` over `ε Z` attached to `h`.
* `AlgebraicGeometry.Space.representedEpsilonKernelModel_isLocallySurjective`: **the model
  `AlgebraicGeometry.Space.representedEpsilonKernelModel` of the adjunct of `κ_{-1}` is locally
  surjective.**  The charts `ε Z` of the affine Zariski squares cover `X_ét`; over such a chart a
  section of `𝒦` is locally `Σ sⱼ · (k_{hⱼ})|` (`chartKernelPresheafHom_imageSieve_mem`), and
  `s · (k_h)| = s • κ_{-1}(m_h)|` is the image of `s ⊗ m_h|`.

## Implementation notes

The three spellings of the sheaves involved (the chart files', the one of `NL_{X/Y}`, and the
transport to the lifted rings) are crossed only in small lemmas whose crossing is generic:
`Stacks.UniverseLift.ringTransportEquivalence_eq_map_of_eq` and
`Stacks.PresheafOfModules.imageSieve_whiskerLeft_over_arrows`.  Stating the same equations
directly at the concrete sheaves exhausts the elaborator's budget.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.Sheaves.ToposPushforward

universe u

namespace Stacks.SheafOfModules

universe v₁ u₁ w₁ z₁

variable {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C)
  {_ : HasWeakSheafify J CommRingCat.{w₁}}
  {_ : J.HasSheafCompose (forget₂ CommRingCat.{w₁} RingCat.{w₁})}

/-- **A class of `H₁` of the sections gives a section of the degree `-1` cohomology sheaf**: the
kernel of the differential of `NL_{B/A}` has a section over `U` whose image in `NL^{-1}` is the
image of `z`. -/
theorem exists_kernel_section_sectionsH1NaiveCotangent
    (_ : HasSheafify J AddCommGrpCat.{max u₁ v₁ w₁ z₁}) (A B : Sheaf J CommRingCat.{w₁})
    (a : A ⟶ B) (U : Cᵒᵖ)
    (z : @Algebra.H1Cotangent (ToType (A.obj.obj U)) (ToType (B.obj.obj U)) _ _
      (algebraSections J A B a U)) :
    ∃ m : ToType ((kernel ((naiveCotangentComplex.{v₁, u₁, w₁, z₁} J A B a).d (-1) 0)).val.obj U),
      (kernel.ι ((naiveCotangentComplex.{v₁, u₁, w₁, z₁} J A B a).d (-1) 0)).val.app U m =
        sectionsH1NaiveCotangent.{v₁, u₁, w₁, z₁} J A B a U z := by
  obtain ⟨k, hk⟩ := exists_kernel_section _ U _
    (sectionsH1Comparison_d.{v₁, u₁, w₁, z₁} J A B a U z)
  exact ⟨(canonicalConormalKernelIso.{v₁, u₁, w₁, z₁} J A B a).hom.val.app U k,
    canonicalConormalKernelIso_hom_app_ι.{v₁, u₁, w₁, z₁} J A B a U k z hk⟩

end Stacks.SheafOfModules

namespace Stacks.UniverseLift

universe v₃ u₃ r₃ m₃ z₃

variable {C : Type u₃} [Category.{v₃} C] {J : GrothendieckTopology C}

/-- **An equation of sections read in the transport of a sheaf of modules to the universe lift
of its ring**: the transport keeps the sections and the restriction maps. -/
theorem ringTransportEquivalence_eq_map_of_eq (O : Sheaf J CommRingCat.{r₃})
    (N : _root_.SheafOfModules.{m₃} (Stacks.SheafOfModules.Tensor.ringSheaf O)) {X X' : Cᵒᵖ}
    (f : X ⟶ X') (y : ToType (N.val.obj X)) (a : ToType (N.val.obj X'))
    (h : a = N.val.map f y) :
    (show ToType (((ringTransportEquivalence.{m₃, z₃} O).functor.obj N).val.obj X') from a) =
      ((ringTransportEquivalence.{m₃, z₃} O).functor.obj N).val.map f y :=
  h

end Stacks.UniverseLift

namespace Stacks.PresheafOfModules

universe v₂ u₂ w₂

variable {C : Type u₂} [Category.{v₂} C] {R : Cᵒᵖ ⥤ RingCat.{w₂}}

/-- A preimage over `V ⟶ U` in a slice puts `V ⟶ U` in the image sieve of the restriction of a
morphism of presheaves of modules to the slice. -/
theorem imageSieve_whiskerLeft_over_arrows {M N : _root_.PresheafOfModules.{w₂} R} (c : M ⟶ N)
    {Y : C} {U V : Over Y} (g : V ⟶ U) (y : N.obj (op U.left)) (t : M.obj (op V.left))
    (h : c.app (op V.left) t = N.map g.left.op y) :
    (Presheaf.imageSieve (Functor.whiskerLeft (Over.forget Y).op
      ((_root_.PresheafOfModules.toPresheaf R).map c)) y).arrows g :=
  ⟨t, h⟩

end Stacks.PresheafOfModules

namespace AlgebraicGeometry.Space

section Chart

attribute [local instance 1]
  Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Sheaf.hasWeakSheafifyCommRingCat
  Sheaf.hasSheafifyAddCommGrpCat
  Sheaf.wEqualsLocallyBijectiveAddCommGrpCat

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (d : ChartDiagram B S hS X.1 Y.1 f.hom)

/-- **The comparison of a chart on a pure tensor**: `s ⊗ m ↦ s · 𝒦(U ⟶ V)(k_m)`, read in the
sections of `𝒦` over the étale chart `U`. -/
theorem chartKernelPresheafHom_app_tmul (V : Over d.U)
    (s : ToType ((chartSliceRing B S hS f d).obj.obj (op V))) (m : chartH1GlobalModule B S hS f d) :
    ((chartKernelPresheafHom B S hS f d).app (op V)).hom
        (s ⊗ₜ[chartGlobalRing B S hS f d] m) =
      (show ToType ((Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedTopos B S hS X).O).obj.obj (op V.left)) from s) •
        (naiveCotangentKernel B S hS f).val.map V.hom.op
          (chartKernelSection B S hS f d (chartH1Down B S hS f d m)) :=
  Stacks.Cohomology.SiteModules.sectionTensorPresheafHomOfSections_app_tmul.{u + 1, u, u, u}
    (O := chartSliceRing B S hS f d) (chartKernelTheta B S hS f d) (op V) s m


end Chart

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) {U V : BigFppfOver B S hS}
  (φ : U ⟶ V) {Z : ((BigFppfOver.toScheme B S hS).obj U).Opens}
  {W : ((BigFppfOver.toScheme B S hS).obj V).Opens}

/-- A chart class `h` gives a section of `𝒦₀` over `Z` whose image in `NL^{-1}_{X₀/Y₀}` is the
image of `h` carried to `H₁` of the Zariski sections over `Z`. -/
theorem exists_representedZariskiKernelSection
    (hZW : Z ≤ (BigFppfOver.toScheme B S hS).map φ ⁻¹ᵁ W)
    (h : chartH1 B S hS (representedSpaceMap B S hS φ)
      (representedEpsilonChartDiagram B S hS φ hZW)) :
    ∃ m : ToType
        ((kernel ((representedZariskiToposNaiveCotangentComplex B S hS φ).d (-1) 0)).val.obj
          (op Z)),
      (kernel.ι ((representedZariskiToposNaiveCotangentComplex B S hS φ).d (-1) 0)).val.app
          (op Z) m =
        Stacks.SheafOfModules.sectionsH1NaiveCotangent.{u, u, u, u + 1} _ _ _
          (representedZariskiSchemeHom B S hS φ).fSharpInverseImage (op Z)
          (representedChartToZariskiH1 B S hS φ hZW h) :=
  Stacks.SheafOfModules.exists_kernel_section_sectionsH1NaiveCotangent.{u, u, u, u + 1}
    _ (hasSheafify_representedZariski_addCommGrpCat B S hS U) _ _ _ (op Z) _

/-- **The section `m_h` of `𝒦₀` over `Z` attached to a chart class `h`**: its image in
`NL^{-1}_{X₀/Y₀}` is the image of `h` carried to `H₁` of the Zariski sections over `Z`. -/
def representedZariskiKernelSection (hZW : Z ≤ (BigFppfOver.toScheme B S hS).map φ ⁻¹ᵁ W)
    (h : chartH1 B S hS (representedSpaceMap B S hS φ)
      (representedEpsilonChartDiagram B S hS φ hZW)) :
    ToType ((kernel ((representedZariskiToposNaiveCotangentComplex B S hS φ).d (-1) 0)).val.obj
      (op Z)) :=
  (exists_representedZariskiKernelSection B S hS φ hZW h).choose

/-- The image of `representedZariskiKernelSection` in `NL^{-1}_{X₀/Y₀}` is the image of the
chart class carried to `H₁` of the Zariski sections over `Z`. -/
theorem kernel_ι_representedZariskiKernelSection
    (hZW : Z ≤ (BigFppfOver.toScheme B S hS).map φ ⁻¹ᵁ W)
    (h : chartH1 B S hS (representedSpaceMap B S hS φ)
      (representedEpsilonChartDiagram B S hS φ hZW)) :
    (kernel.ι ((representedZariskiToposNaiveCotangentComplex B S hS φ).d (-1) 0)).val.app (op Z)
        (representedZariskiKernelSection B S hS φ hZW h) =
      Stacks.SheafOfModules.sectionsH1NaiveCotangent.{u, u, u, u + 1} _ _ _
        (representedZariskiSchemeHom B S hS φ).fSharpInverseImage (op Z)
        (representedChartToZariskiH1 B S hS φ hZW h) :=
  (exists_representedZariskiKernelSection B S hS φ hZW h).choose_spec

/-- **The étale chart of an affine Zariski open is affine**: the scheme underlying `ε(Z)` is the
open subscheme `Z`. -/
theorem isAffine_representedEpsilonFunctor_obj (T : BigFppfOver B S hS)
    {Z : ((BigFppfOver.toScheme B S hS).obj T).Opens} (hZ : IsAffineOpen Z) :
    IsAffine ((SmallEtale.toOver B S hS (yoneda.obj T) ⋙ BigFppfOver.toScheme B S hS).obj
      ((representedEpsilonFunctor B S hS T).obj Z)) :=
  hZ

/-- **`κ_{-1}(m_h)` is the section of `𝒦` attached to `h`.** -/
theorem representedEpsilonKernelHom_app_representedZariskiKernelSection
    (hZW : Z ≤ (BigFppfOver.toScheme B S hS).map φ ⁻¹ᵁ W)
    (h : chartH1 B S hS (representedSpaceMap B S hS φ)
      (representedEpsilonChartDiagram B S hS φ hZW)) :
    (representedEpsilonKernelHom B S hS φ).val.app (op Z)
        (representedZariskiKernelSection B S hS φ hZW h) =
      (representedNaiveCotangentKernelIso B S hS φ).hom.val.app
        (op ((representedToZariskiRingedToposSiteHom B S hS U).u.obj Z))
        (chartKernelSection B S hS (representedSpaceMap B S hS φ)
          (representedEpsilonChartDiagram B S hS φ hZW) h) :=
  representedEpsilonKernelHom_app_chartKernelSection B S hS φ hZW h _
    (kernel_ι_representedZariskiKernelSection B S hS φ hZW h)

attribute [local instance] isContinuous_representedToZariskiRingedToposSiteHom_u

/-- **The concrete model of the adjunct of `κ_{-1}`**: the map of presheaves
`V ↦ (𝒪_X(V) ⊗_{𝒪_{X₀}(L V)} 𝒦₀(L V) ⟶ 𝒦(V))`, `s ⊗ m ↦ s • 𝒦(V ⟶ ε(L V))(κ_{-1} m)`, over
the universe lifts of the structure rings. -/
abbrev representedEpsilonKernelModel :=
  ((Stacks.PullbackLeftAdjoint.modelAdjunction (representedImageOpenEpsilonAdjunction B S hS U)
    (Stacks.PullbackLeftAdjoint.commRingHom (Stacks.UniverseLift.liftedRingHom.{u + 1}
      (representedToZariskiRingedToposSiteHom B S hS U).fSharpRing))
    (Stacks.UniverseLift.liftedRingHom.{u + 1}
      (representedToZariskiRingedToposSiteHom B S hS U).fSharpRing).hom
    (Stacks.PullbackLeftAdjoint.ringHom_commRingHom _)).homEquiv _ _).symm
      (Stacks.UniverseLift.liftedPushforwardHom.{u + 1, u + 1}
        (representedToZariskiRingedToposSiteHom B S hS U).fSharpRing
        (representedEpsilonKernelHom B S hS φ)).val

/-- **The model map on the generator `1 ⊗ m|`**, in the spelling of the lifted rings: for a
section `m` of `𝒦₀` over `Z` and a morphism `g : A ⟶ ε Z`, the tensor `1 ⊗ m|_{L A}` is sent to
`κ_{-1}(m)|_A`. -/
theorem representedEpsilonKernelModel_app_tmul_one_map
    (Z : ((BigFppfOver.toScheme B S hS).obj U).Opens)
    (m : ToType ((kernel ((representedZariskiToposNaiveCotangentComplex B S hS φ).d (-1) 0)).val.obj
      (op Z)))
    (A : SmallEtale B S hS (yoneda.obj U)) (g : A ⟶ (representedEpsilonFunctor B S hS U).obj Z) :
    (representedEpsilonKernelModel B S hS φ).app (op A)
        (Stacks.PullbackModel.tmul
          ((Stacks.PullbackLeftAdjoint.transposeRingHom
            (representedImageOpenEpsilonAdjunction B S hS U)
            (Stacks.PullbackLeftAdjoint.commRingHom (Stacks.UniverseLift.liftedRingHom.{u + 1}
              (representedToZariskiRingedToposSiteHom B S hS U).fSharpRing))).app (op A)).hom 1
          (((Stacks.UniverseLift.ringTransportEquivalence.{u + 1, u + 1}
              ((BigFppfOver.toScheme B S hS).obj U).zariskiRingedTopos.O).functor.obj
              (kernel ((representedZariskiToposNaiveCotangentComplex B S hS φ).d (-1) 0))).val.map
            (((representedImageOpenEpsilonAdjunction B S hS U).homEquiv A Z).symm g).op m)) =
      ((Stacks.UniverseLift.ringTransportEquivalence.{u + 1, u + 1}
          (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U)).O).functor.obj
          (kernel ((representedSpaceNaiveCotangentComplex B S hS φ).d (-1) 0))).val.map g.op
        ((Stacks.UniverseLift.liftedPushforwardHom.{u + 1, u + 1}
          (representedToZariskiRingedToposSiteHom B S hS U).fSharpRing
          (representedEpsilonKernelHom B S hS φ)).val.app (op Z) m) :=
  Stacks.PullbackLeftAdjoint.modelAdjunction_homEquiv_symm_app_tmul_one_map
    (representedImageOpenEpsilonAdjunction B S hS U)
    (Stacks.PullbackLeftAdjoint.commRingHom (Stacks.UniverseLift.liftedRingHom.{u + 1}
      (representedToZariskiRingedToposSiteHom B S hS U).fSharpRing))
    (Stacks.UniverseLift.liftedRingHom.{u + 1}
      (representedToZariskiRingedToposSiteHom B S hS U).fSharpRing).hom
    (Stacks.PullbackLeftAdjoint.ringHom_commRingHom _)
    (Stacks.UniverseLift.liftedPushforwardHom.{u + 1, u + 1}
        (representedToZariskiRingedToposSiteHom B S hS U).fSharpRing
        (representedEpsilonKernelHom B S hS φ)).val g m

/-- The model map on `1 ⊗ m_h|`, `m_h` the section of `𝒦₀` attached to a chart class `h`. -/
theorem representedEpsilonKernelModel_app_tmul_one_representedZariskiKernelSection
    (hZW : Z ≤ (BigFppfOver.toScheme B S hS).map φ ⁻¹ᵁ W)
    (h : chartH1 B S hS (representedSpaceMap B S hS φ)
      (representedEpsilonChartDiagram B S hS φ hZW))
    (A : SmallEtale B S hS (yoneda.obj U)) (g : A ⟶ (representedEpsilonFunctor B S hS U).obj Z) :
    (representedEpsilonKernelModel B S hS φ).app (op A)
        (Stacks.PullbackModel.tmul
          ((Stacks.PullbackLeftAdjoint.transposeRingHom
            (representedImageOpenEpsilonAdjunction B S hS U)
            (Stacks.PullbackLeftAdjoint.commRingHom (Stacks.UniverseLift.liftedRingHom.{u + 1}
              (representedToZariskiRingedToposSiteHom B S hS U).fSharpRing))).app (op A)).hom 1
          (((Stacks.UniverseLift.ringTransportEquivalence.{u + 1, u + 1}
              ((BigFppfOver.toScheme B S hS).obj U).zariskiRingedTopos.O).functor.obj
              (kernel ((representedZariskiToposNaiveCotangentComplex B S hS φ).d (-1) 0))).val.map
            (((representedImageOpenEpsilonAdjunction B S hS U).homEquiv A Z).symm g).op
            (representedZariskiKernelSection B S hS φ hZW h))) =
      ((Stacks.UniverseLift.ringTransportEquivalence.{u + 1, u + 1}
          (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U)).O).functor.obj
          (kernel ((representedSpaceNaiveCotangentComplex B S hS φ).d (-1) 0))).val.map g.op
        ((representedNaiveCotangentKernelIso B S hS φ).hom.val.app
          (op ((representedToZariskiRingedToposSiteHom B S hS U).u.obj Z))
          (chartKernelSection B S hS (representedSpaceMap B S hS φ)
            (representedEpsilonChartDiagram B S hS φ hZW) h)) :=
  (representedEpsilonKernelModel_app_tmul_one_map B S hS φ Z _ A g).trans
    (congrArg _ (representedEpsilonKernelHom_app_representedZariskiKernelSection B S hS φ hZW h))

/-- **The comparison of the chart on a pure tensor, through `e`, is in the image of the model
map**: `e(s · (θ m)|_V) = s • (1 ⊗ m_h|)` is the image of `s ⊗ (1 ⊗ m_h|)`. -/
theorem exists_representedEpsilonKernelModel_app_eq_chartKernelPresheafHom_tmul
    (hZW : Z ≤ (BigFppfOver.toScheme B S hS).map φ ⁻¹ᵁ W)
    (V : Over (representedEpsilonChartDiagram B S hS φ hZW).U)
    (s : ToType ((chartSliceRing B S hS (representedSpaceMap B S hS φ)
      (representedEpsilonChartDiagram B S hS φ hZW)).obj.obj (op V)))
    (m : chartH1GlobalModule B S hS (representedSpaceMap B S hS φ)
      (representedEpsilonChartDiagram B S hS φ hZW)) :
    ∃ t, (representedEpsilonKernelModel B S hS φ).app (op V.left) t =
      (representedNaiveCotangentKernelIso B S hS φ).hom.val.app (op V.left)
        (((chartKernelPresheafHom B S hS (representedSpaceMap B S hS φ)
          (representedEpsilonChartDiagram B S hS φ hZW)).app (op V)).hom
          (s ⊗ₜ[chartGlobalRing B S hS (representedSpaceMap B S hS φ)
            (representedEpsilonChartDiagram B S hS φ hZW)] m)) := by
  let T := ((Stacks.PullbackLeftAdjoint.transposeRingHom
    (representedImageOpenEpsilonAdjunction B S hS U)
    (Stacks.PullbackLeftAdjoint.commRingHom (Stacks.UniverseLift.liftedRingHom.{u + 1}
      (representedToZariskiRingedToposSiteHom B S hS U).fSharpRing))).app (op V.left)).hom
  let x := ((Stacks.UniverseLift.ringTransportEquivalence.{u + 1, u + 1}
      ((BigFppfOver.toScheme B S hS).obj U).zariskiRingedTopos.O).functor.obj
      (kernel ((representedZariskiToposNaiveCotangentComplex B S hS φ).d (-1) 0))).val.map
    (((representedImageOpenEpsilonAdjunction B S hS U).homEquiv V.left Z).symm V.hom).op
    (representedZariskiKernelSection B S hS φ hZW (chartH1Down B S hS _ _ m))
  refine ⟨Stacks.PullbackModel.tmul T (ULift.up.{u + 1} s) x, ?_⟩
  refine (congrArg ((representedEpsilonKernelModel B S hS φ).app (op V.left))
    ((congrArg (Stacks.PullbackModel.tmul T · x) (mul_one _).symm).trans
      (Stacks.PullbackModel.smul_tmul T _ 1 x).symm)).trans ?_
  refine (((representedEpsilonKernelModel B S hS φ).app (op V.left)).hom.map_smul _ _).trans ?_
  refine (congrArg (@HSMul.hSMul _ _ _ _ _)
    (representedEpsilonKernelModel_app_tmul_one_representedZariskiKernelSection B S hS φ hZW
      (chartH1Down B S hS _ _ m) V.left V.hom)).trans ?_
  refine Eq.trans ?_ (congrArg ((representedNaiveCotangentKernelIso B S hS φ).hom.val.app
    (op V.left)).hom (chartKernelPresheafHom_app_tmul B S hS
      (representedSpaceMap B S hS φ) (representedEpsilonChartDiagram B S hS φ hZW) V s m).symm)
  refine Eq.trans ?_ (((representedNaiveCotangentKernelIso B S hS φ).hom.val.app
    (op V.left)).hom.map_smul _ _).symm
  exact congrArg (@HSMul.hSMul _ _ _ _ _) (PresheafOfModules.naturality_apply
    (representedNaiveCotangentKernelIso B S hS φ).hom.val V.hom.op _).symm

/-- **The comparison of the chart, through `e`, lands in the image of the model map.** -/
theorem exists_representedEpsilonKernelModel_app_eq_chartKernelPresheafHom
    (hZW : Z ≤ (BigFppfOver.toScheme B S hS).map φ ⁻¹ᵁ W)
    (V : Over (representedEpsilonChartDiagram B S hS φ hZW).U)
    (x : chartGlobalTensor B S hS (representedSpaceMap B S hS φ)
      (representedEpsilonChartDiagram B S hS φ hZW) V) :
    ∃ t, (representedEpsilonKernelModel B S hS φ).app (op V.left) t =
      (representedNaiveCotangentKernelIso B S hS φ).hom.val.app (op V.left)
        (((chartKernelPresheafHom B S hS (representedSpaceMap B S hS φ)
          (representedEpsilonChartDiagram B S hS φ hZW)).app (op V)).hom x) := by
  let c := ((representedEpsilonKernelModel B S hS φ).app (op V.left)).hom
  let k := ((chartKernelPresheafHom B S hS (representedSpaceMap B S hS φ)
    (representedEpsilonChartDiagram B S hS φ hZW)).app (op V)).hom
  let e := ((representedNaiveCotangentKernelIso B S hS φ).hom.val.app (op V.left)).hom
  induction x using TensorProduct.inductionOn with
  | tmul s m =>
    exact exists_representedEpsilonKernelModel_app_eq_chartKernelPresheafHom_tmul B S hS φ hZW V s m
  | add x y hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨a + b, (c.map_add a b).trans ((congrArg₂ (· + ·) ha hb).trans
      ((congrArg e (k.map_add x y)).trans (e.map_add _ _)).symm)⟩

/-- **The last step of local surjectivity**: through `e`, the comparison of the chart on a
preimage of `e⁻¹(y)|` is `y|`. -/
theorem representedNaiveCotangentKernelIso_hom_app_chartKernelPresheafHom_of_eq
    (hZW : Z ≤ (BigFppfOver.toScheme B S hS).map φ ⁻¹ᵁ W)
    {V' U'' : Over (representedEpsilonChartDiagram B S hS φ hZW).U} (g : V' ⟶ U'')
    (y : ToType ((kernel ((representedSpaceNaiveCotangentComplex B S hS φ).d (-1) 0)).val.obj
      (op U''.left)))
    (x : chartGlobalTensor B S hS (representedSpaceMap B S hS φ)
      (representedEpsilonChartDiagram B S hS φ hZW) V')
    (hx : ((chartKernelPresheafHom B S hS (representedSpaceMap B S hS φ)
      (representedEpsilonChartDiagram B S hS φ hZW)).app (op V')).hom x =
      (naiveCotangentKernel B S hS (representedSpaceMap B S hS φ)).val.map g.left.op
        ((representedNaiveCotangentKernelIso B S hS φ).inv.val.app (op U''.left) y)) :
    (representedNaiveCotangentKernelIso B S hS φ).hom.val.app (op V'.left)
        (((chartKernelPresheafHom B S hS (representedSpaceMap B S hS φ)
          (representedEpsilonChartDiagram B S hS φ hZW)).app (op V')).hom x) =
      (kernel ((representedSpaceNaiveCotangentComplex B S hS φ).d (-1) 0)).val.map g.left.op y := by
  refine (congrArg ((representedNaiveCotangentKernelIso B S hS φ).hom.val.app (op V'.left)).hom
    hx).trans ?_
  refine (PresheafOfModules.naturality_apply (representedNaiveCotangentKernelIso B S hS φ).hom.val
    g.left.op _).trans ?_
  exact congrArg _ (ConcreteCategory.congr_hom (congrArg (fun a => a.val.app (op U''.left))
    (representedNaiveCotangentKernelIso B S hS φ).inv_hom_id) y)

/-- **Local surjectivity of the model of the adjunct of `κ_{-1}`.** -/
theorem representedEpsilonKernelModel_isLocallySurjective :
    PresheafOfModules.IsLocallySurjective
      (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U)).J
      (representedEpsilonKernelModel B S hS φ) := by
  refine Presheaf.isLocallySurjective_of_coversTop _ _
    (coversTop_representedEpsilonFunctor_affineSquare B S hS φ) fun i => ⟨fun {U''} y => ?_⟩
  obtain ⟨⟨Z, W⟩, hZ, hW, hZW⟩ := i
  have hmem := chartKernelPresheafHom_imageSieve_mem B S hS (representedSpaceMap B S hS φ)
    (representedEpsilonChartDiagram B S hS φ hZW)
    (isAffine_representedEpsilonFunctor_obj B S hS U hZ)
    (isAffine_representedEpsilonFunctor_obj B S hS V hW) U''
    ((representedNaiveCotangentKernelIso B S hS φ).inv.val.app (op U''.left) y)
  refine GrothendieckTopology.superset_covering _ ?_ hmem
  rintro V' g ⟨x, hx⟩
  obtain ⟨t, ht⟩ :=
    exists_representedEpsilonKernelModel_app_eq_chartKernelPresheafHom B S hS φ hZW V' x
  refine Stacks.PresheafOfModules.imageSieve_whiskerLeft_over_arrows _ g y t ?_
  rw [ht]
  exact Stacks.UniverseLift.ringTransportEquivalence_eq_map_of_eq _ _ _ _ _
    (representedNaiveCotangentKernelIso_hom_app_chartKernelPresheafHom_of_eq B S hS φ hZW g y x hx)

end AlgebraicGeometry.Space
