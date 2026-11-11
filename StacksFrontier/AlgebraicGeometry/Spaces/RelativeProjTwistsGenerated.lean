module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjF1Generated
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.PsiDescended
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.TwistAlgebraOfProj
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.PointTwistGradedMulPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.FunctorialityTwistAlgebraHom
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.FunctorialityTwistMapEpi
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleMapEtaleAtlasDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedTwistedCohomology
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparisonTopologies
public import StacksFrontier.AlgebraicGeometry.Quot.PicardDescent.InvertibleDescent
public import StacksFrontier.AlgebraicGeometry.Picard.GaloisDescent.Pullback
public import StacksFrontier.AlgebraicGeometry.RelativeProjDegreeOne.Epi
public import StacksFrontier.AlgebraicGeometry.TwistMapsInvertible.Multiplication
public import StacksFrontier.AlgebraicGeometry.Morphism.TwistAlgebra
public import StacksFrontier.AlgebraicGeometry.TwistTensor.RelativeLaurentComparison

/-!
# Stacks 085D (2) and (3) on the constructed relative Proj

In Situation 0849 let `𝒜` be a quasi-coherent graded `𝒪_X`-algebra on the algebraic space `X`,
generated as an `𝒜₀`-algebra by `𝒜₁`
(`AlgebraicGeometry.Space.RelativeProjSituation.IsGeneratedInDegreeOne`), and let
`π : P = Proj_X(𝒜) ⟶ X` be the relative homogeneous spectrum constructed in Stacks 084A–084B, with
its twists `𝒪_P(n)` (`…RelativeProjSituation.twistModule`), its sheaf of `ℤ`-graded algebras
`⨁_{n ∈ ℤ} 𝒪_P(n)` (`…RelativeProjSituation.twistGradedAlgebra`) and the canonical maps
`ψ_n : π^*𝒜_n ⟶ 𝒪_P(n)` (`…RelativeProjSituation.psiTwistHom`) of Stacks 084D.  This file proves
the two remaining assertions of Stacks 085D on that `P`:

* (2) the canonical map `π^*𝒜₁ ⟶ 𝒪_P(1)` is surjective;
* (3) every `𝒪_P(n)` is invertible, and the multiplication maps
  `𝒪_P(n) ⊗_{𝒪_P} 𝒪_P(m) ⟶ 𝒪_P(n + m)` are isomorphisms.

Part (1) on the same `P` is `…RelativeProjSituation.relativeProjIsoF1OfGenerated`.

## The argument

The source's proof is "see Constructions, Lemma 01O4 for the case of schemes": all three
properties are étale local on `P`.  Fix a presentation `X = U/R` of the base; then
`P_U = U ×_X P = Proj_U(u^*𝒜)` is a surjective étale atlas of `P`, and the restriction `u^*𝒜` is
generated in degree one (`…IsGeneratedInDegreeOne.isGeneratedInDegreeOneOnCharts`).

* On the atlas, `ψ₁` is `ψ` of Tag 01NR on `Proj_U(u^*𝒜)` read through Stacks 03DX (2)
  (`…modulePullback_map_psiTwistHom_comp_twistModuleChartIso_hom`), which is surjective by the
  scheme case `Stacks.AlgebraicGeometry.RelativeProjDegreeOne.epi_psiTranspose`; surjectivity
  descends along the atlas (`AlgebraicGeometry.Space.epi_modulePullback_map_iff_of_isEtale_of_isSurjective`).
* The inverse image of `𝒪_P(n)` along the atlas is the module attached to the twist `𝒪(n)` of
  `Proj_U(u^*𝒜)` (`…twistModuleChartIso`), which is invertible by the scheme case
  (`Stacks.AlgebraicGeometry.TwistMapsInvertible.twistDataOfGradedAlgebra_isInvertible`);
  invertibility of a quasi-coherent module descends along an fpqc covering
  (`AlgebraicGeometry.Space.isInvertibleModule_of_pullback_isFpqcCovering`).
* On the atlas the multiplication of the twists is that of Tag 01NR on `Proj_U(u^*𝒜)`
  (`…fibreToSpaceTwistModuleIso_twistAlgebraMul`), an isomorphism by the scheme case
  (`Stacks.AlgebraicGeometry.TwistMapsInvertible.isIso_mulSheaf_twistDataOfGradedAlgebra`); being
  an isomorphism descends along the atlas
  (`AlgebraicGeometry.Space.isIso_modulePullback_map_iff_of_isEtale_of_isSurjective`).

## Main results

* `AlgebraicGeometry.Space.RelativeProjSituation.epi_psiTwistHom_one`: **Stacks 085D (2)**.
* `AlgebraicGeometry.Space.RelativeProjSituation.isInvertibleModule_twistModule`:
  **Stacks 085D (3)**, invertibility.
* `AlgebraicGeometry.Space.RelativeProjSituation.isIso_mulSheaf_twistGradedAlgebra`:
  **Stacks 085D (3)**, the multiplication isomorphisms.

## References

* [Stacks Project, Tag 085D](https://stacks.math.columbia.edu/tag/085D)
* [Stacks Project, Tag 01O4](https://stacks.math.columbia.edu/tag/01O4)
* [Stacks Project, Tag 084D](https://stacks.math.columbia.edu/tag/084D)
-/

@[expose] public noncomputable section

universe u m

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open Stacks.AlgebraicGeometry.RelativeProj (relativeProj)

namespace AlgebraicGeometry.Space

attribute [local instance] modulesMonoidalCategory

attribute [local instance 5000] SmallEtale.instHasSheafify SmallEtale.instWEqualsLocallyBijective

namespace RelativeProjSituation

variable (s : RelativeProjSituation.{u, m})

section Scheme

open Stacks.AlgebraicGeometry.RelativeProjBridge (SheafGradedAlgebra) in
/-- Tag 01NR's `ψ₁` in adjoint form, read along a factorization `f = ι ≫ π` through the
relative Proj, `f^*𝒜₁ ⟶ ι^*𝒪(1)`, is surjective when `𝒜` is generated in degree one: it is the
inverse image along `ι` of the transpose `π^*𝒜₁ ⟶ 𝒪(1)` of `ψ₁`, surjective by
`Stacks.AlgebraicGeometry.RelativeProjDegreeOne.epi_psiTranspose`, between two isomorphisms. -/
theorem epi_pullbackAdjointPsi_one {X Y : Scheme.{u}} (A : SheafGradedAlgebra Y)
    (ι : X ⟶ (relativeProj A).scheme) (f : X ⟶ Y) (hf : f = ι ≫ (relativeProj A).toBase)
    (hgen : Stacks.AlgebraicGeometry.ProjRepresentsF1.IsGeneratedInDegreeOne A) :
    Epi (pullbackAdjointPsi A ι f hf 1) := by
  have h := Stacks.AlgebraicGeometry.RelativeProjDegreeOne.epi_psiTranspose
    (Stacks.AlgebraicGeometry.GluedTwistAlgebra.twistDataOfGradedAlgebra A) hgen
  have := (Scheme.Modules.pullbackPushforwardAdjunction ι).isLeftAdjoint
  have h1 := @Functor.map_epi _ _ _ _ (Scheme.Modules.pullback ι)
    (Functor.preservesEpimorphisms_of_isLeftAdjoint _) _ _ _ h
  unfold pullbackAdjointPsi pullbackAdjointOfComp
  have h2 : Epi ((Scheme.Modules.pullback ι).map
      (((Scheme.Modules.pullbackPushforwardAdjunction (relativeProj A).toBase).homEquiv _ _).symm
        ((Stacks.AlgebraicGeometry.GluedTwistAlgebra.twistDataOfGradedAlgebra A).ψ 1))) := h1
  exact epi_comp'
    (@IsIso.epi_of_iso _ _ _ _ _ (Iso.app (Scheme.Modules.pullbackCongr hf) _).isIso_hom)
    (epi_comp' (@IsIso.epi_of_iso _ _ _ _ _
      (Iso.app (Scheme.Modules.pullbackComp ι (relativeProj A).toBase).symm _).isIso_hom) h2)

variable (V : BigFppfOver s.site s.base s.containsBase) (v : yoneda.obj V ⟶ s.space.1)

/-- On the scheme of `V ×_X P = Proj_V(v^*𝒜)`, Tag 01NR's `ψ₁` in adjoint form,
`π_V^*(v^*𝒜)₁ ⟶ 𝒪(1)`, is surjective when `v^*𝒜` is generated in degree one: it is the inverse
image along the identification `V ×_X P = Proj_V(v^*𝒜)` of the transpose of `ψ₁`, which is
surjective by the case of schemes of Stacks 085D (2). -/
theorem epi_psiChartSchemeHomOfAdjoint_one
    (hgen : Stacks.AlgebraicGeometry.ProjRepresentsF1.IsGeneratedInDegreeOne
      (s.shrink.pointAlgebra V v)) :
    Epi (s.psiChartSchemeHomOfAdjoint V v 1) :=
  epi_pullbackAdjointPsi_one _ _ _ _ hgen

/-- On the scheme of `V ×_X P = Proj_V(v^*𝒜)` the multiplication `𝒪(i) ⊗ 𝒪(j) ⟶ 𝒪(i + j)` of
Tag 01NR's `⨁_n 𝒪(n)` is an isomorphism when `v^*𝒜` is generated in degree one: it is the inverse
image along `V ×_X P = Proj_V(v^*𝒜)` of the multiplication there, read through the comparison of
inverse images of tensor products, and that is an isomorphism by the case of schemes,
Stacks 01O4. -/
theorem isIso_twistPieceMul_hom
    (hgen : Stacks.AlgebraicGeometry.ProjRepresentsF1.IsGeneratedInDegreeOne
      (s.shrink.pointAlgebra V v)) (i j : ℤ) :
    IsIso (s.twistPieceMul V v i j).hom :=
  Stacks.RingedSpace.isIso_mulSheaf_pullbackGradedAlgebra (s.toRelativeProj V v).toLRSHom.toShHom
    _ i j (Stacks.AlgebraicGeometry.TwistMapsInvertible.isIso_mulSheaf_twistDataOfGradedAlgebra
      hgen i j)

end Scheme

variable (Px : Presentation s.site s.base s.containsBase s.space.obj s.space.property)

/-- The atlas `U ⟶ X` of a presentation of the base, as an étale chart of `X`. -/
abbrev presentationEtaleChart : SmallEtale s.site s.base s.containsBase s.space.1 :=
  ⟨CostructuredArrow.mk Px.toSpace, Px.etale⟩

/-- Generation in degree one of `𝒜` gives generation in degree one of its restriction `u^*𝒜` to
the atlas `u : U ⟶ X` of a presentation of the base. -/
theorem IsGeneratedInDegreeOne.pointAlgebra_presentation {s : RelativeProjSituation.{u, m}}
    (hgen : s.IsGeneratedInDegreeOne)
    (Px : Presentation s.site s.base s.containsBase s.space.obj s.space.property) :
    Stacks.AlgebraicGeometry.ProjRepresentsF1.IsGeneratedInDegreeOne
      (s.shrink.pointAlgebra Px.U Px.toSpace) :=
  hgen.isGeneratedInDegreeOneOnCharts (s.presentationEtaleChart Px)

/-- The atlas `U ×_X P ⟶ P` of the presentation of `P` over a presentation of `X` is étale. -/
theorem isEtale_fibreToSpaceHom_presentation :
    IsEtale s.site s.base s.containsBase (s.fibreToSpaceHom Px.U Px.toSpace).hom :=
  presentationAtlas_isEtale
    (s.relativeProjPoints.spacePresentation Px s.isAlgebraicSpace_relativeProjFunctor)

/-- The atlas `U ×_X P ⟶ P` of the presentation of `P` over a presentation of `X` is surjective. -/
theorem isSurjective_fibreToSpaceHom_presentation :
    IsSurjective s.site s.base s.containsBase (s.fibreToSpaceHom Px.U Px.toSpace).hom :=
  (s.relativeProjPoints.spacePresentation Px s.isAlgebraicSpace_relativeProjFunctor).isSurjective_atlas

/-! ### Stacks 085D (2) -/

/-- **Stacks 085D (2).**  For a quasi-coherent graded `𝒪_X`-algebra `𝒜` on an algebraic space `X`
generated as an `𝒜₀`-algebra by `𝒜₁`, and `P = Proj_X(𝒜)` the relative Proj of
Stacks 084A–084B, the canonical map `ψ₁ : π^*𝒜₁ ⟶ 𝒪_P(1)` of Stacks 084D is surjective (an
epimorphism of `𝒪_P`-modules on the small étale site of `P`).

On the atlas `U ×_X P = Proj_U(u^*𝒜)` of `P` it is Tag 01NR's `ψ₁`, surjective by the case of
schemes; surjectivity descends along the surjective étale atlas. -/
@[stacks 085D "(2): for a quasi-coherent graded O_X-algebra A on an algebraic space X generated \
as an A_0-algebra by A_1 (s.IsGeneratedInDegreeOne), the canonical map psi_1 : pi^*A_1 -> O_P(1) \
of Tag 084D (psiTwistHom) on the relative Proj P = Proj_X(A) of Tags 084A-084B is surjective, \
i.e. an epimorphism of O_P-modules on the small etale site of P"]
theorem epi_psiTwistHom_one (hgen : s.IsGeneratedInDegreeOne) : Epi (s.psiTwistHom Px 1) := by
  have hs : Epi (s.psiChartSchemeHomOfAdjoint Px.U Px.toSpace 1) :=
    s.epi_psiChartSchemeHomOfAdjoint_one Px.U Px.toSpace (hgen.pointAlgebra_presentation Px)
  have hc : Epi (s.fibrePsiHom Px.U Px.toSpace 1) := by
    unfold fibrePsiHom
    exact @epi_comp _ _ _ _ _ _ (@IsIso.epi_of_iso _ _ _ _ _ (Iso.isIso_hom _)) _
      (epi_representedQuasicoherentSchemeEquivalence_map_hom _ _ hs)
  rw [← s.modulePullback_map_psiTwistHom_comp_fibreToSpaceTwistModuleIso Px Px.U Px.toSpace 1]
    at hc
  haveI := Iso.isIso_hom (s.fibreToSpaceTwistModuleIso Px Px.U Px.toSpace ((1 : ℕ) : ℤ))
  have h2 := (epi_comp_iff_of_isIso _ _).1 hc
  exact (epi_modulePullback_map_iff_of_isEtale_of_isSurjective s.site s.base s.containsBase
    (s.fibreToSpaceHom Px.U Px.toSpace) (s.isEtale_fibreToSpaceHom_presentation Px)
    (s.isSurjective_fibreToSpaceHom_presentation Px) (s.psiTwistHom Px 1)).1 h2

/-! ### Stacks 085D (3) -/

/-- **Stacks 085D (3), invertibility.**  For a quasi-coherent graded `𝒪_X`-algebra `𝒜` on an
algebraic space `X` generated as an `𝒜₀`-algebra by `𝒜₁`, and `P = Proj_X(𝒜)` the relative Proj
of Stacks 084A–084B, every twist `𝒪_P(n)`, `n ∈ ℤ`, of Stacks 084D is an invertible
`𝒪_P`-module.

Its inverse image along the atlas `U ×_X P = Proj_U(u^*𝒜)` of `P` is the module attached to the
twist `𝒪(n)` of `Proj_U(u^*𝒜)`, invertible by the case of schemes; invertibility of a
quasi-coherent module descends along the fpqc covering formed by the atlas. -/
@[stacks 085D "(3), invertibility: for a quasi-coherent graded O_X-algebra A on an algebraic \
space X generated as an A_0-algebra by A_1 (s.IsGeneratedInDegreeOne), every twist O_P(n), n in \
Z, of Tag 084D (twistModule) on the relative Proj P = Proj_X(A) of Tags 084A-084B is an \
invertible O_P-module on the small etale site of P"]
theorem isInvertibleModule_twistModule (hgen : s.IsGeneratedInDegreeOne) (n : ℤ) :
    IsInvertibleModule
      (⟨s.relativeProjFunctor, s.isAlgebraicSpace_relativeProjFunctor⟩ :
        AlgebraicSpaces s.site s.base s.containsBase)
      (s.twistModule Px n).obj := by
  have hA := Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _
    (Stacks.AlgebraicGeometry.TwistMapsInvertible.twistDataOfGradedAlgebra_isInvertible
      (hgen.pointAlgebra_presentation Px) n)
  have hL : Stacks.SheafOfModules.IsInvertible
      ((BigFppfOver.toScheme s.site s.base s.containsBase).obj
        (s.relativeProjPoints.fibre Px.U Px.toSpace)).presheaf
      (_root_.AlgebraicGeometry.SmallEtale.zariskiStructureIsSheaf _)
      (s.twistPieceQcoh Px.U Px.toSpace n).obj :=
    Stacks.RingedSpace.modulePullback_isInvertible_of
      (s.toRelativeProj Px.U Px.toSpace).toLRSHom.toShHom _ hA
  have hM := isInvertible_representedSmallEtaleModuleEquivalence_functor_obj_associatedModule
    s.site s.base s.containsBase (s.relativeProjPoints.fibre Px.U Px.toSpace)
    (s.twistPieceQcoh Px.U Px.toSpace n).obj hL
  refine isInvertibleModule_of_pullback_isFpqcCovering s.site s.base s.containsBase
    (fun _ : Unit => s.fibreToSpaceHom Px.U Px.toSpace)
    (isFpqcCovering_of_isEtaleCovering s.site s.base s.containsBase _ _
      (presentationAtlas_isEtaleCovering
        (s.relativeProjPoints.spacePresentation Px s.isAlgebraicSpace_relativeProjFunctor)))
    _ (s.isQuasicoherentOnSite_twistModule Px n) fun _ => ?_
  have : IsInvertibleModule (representedAlgebraicSpace s.site s.base s.containsBase
        (s.relativeProjPoints.fibre Px.U Px.toSpace))
      ((representedQuasicoherentSchemeEquivalence s.site s.base s.containsBase
        (s.relativeProjPoints.fibre Px.U Px.toSpace)).functor.obj
          (s.twistPieceQcoh Px.U Px.toSpace n)).obj := hM
  exact Stacks.SheafOfModules.isInvertible_of_iso _ _ (s.fibreToSpaceTwistModuleIso Px Px.U
    Px.toSpace n).symm

/-- **The multiplication `𝒪_P(i) ⊗ 𝒪_P(j) ⟶ 𝒪_P(i + j)` of the twists is an isomorphism**, for
`𝒜` generated in degree one, with the tensor product of `𝒪_P`-modules of
`AlgebraicGeometry.Space.modulesMonoidalCategory`.

On the atlas `U ×_X P = Proj_U(u^*𝒜)` of `P` it is the multiplication of the twists of Tag 01NR,
an isomorphism by the case of schemes; being an isomorphism descends along the surjective étale
atlas. -/
theorem isIso_twistAlgebraMul (hgen : s.IsGeneratedInDegreeOne) (i j : ℤ) :
    IsIso (s.twistAlgebraMul Px i j) := by
  have hm := s.isIso_twistPieceMul_hom Px.U Px.toSpace (hgen.pointAlgebra_presentation Px) i j
  have hΦ := isIso_representedQuasicoherentSchemeEquivalence_map_hom
    (s.relativeProjPoints.fibre Px.U Px.toSpace) (s.twistPieceMul Px.U Px.toSpace i j) hm
  have hR : IsIso (representedTensorChartMul s.site s.base s.containsBase
      (s.twistPieceMul Px.U Px.toSpace i j)) :=
    @IsIso.comp_isIso _ _ _ _ _ _ _ (Iso.isIso_inv (representedQuasicoherentSchemeTensorIso
      s.site s.base s.containsBase (s.relativeProjPoints.fibre Px.U Px.toSpace)
      (s.twistPieceQcoh Px.U Px.toSpace i) (s.twistPieceQcoh Px.U Px.toSpace j))) hΦ
  have key := s.fibreToSpaceTwistModuleIso_twistAlgebraMul Px Px.U Px.toSpace i j
  have h1 : IsIso ((modulePullbackTensorIso s.site s.base s.containsBase
        (s.fibreToSpaceHom Px.U Px.toSpace)
        (s.twistModule Px i).obj (s.twistModule Px j).obj).inv ≫
      (modulePullback s.site s.base s.containsBase (s.fibreToSpaceHom Px.U Px.toSpace)).map
        (s.twistAlgebraMul Px i j) ≫
        (s.fibreToSpaceTwistModuleIso Px Px.U Px.toSpace (i + j)).hom) := by
    rw [key]
    exact @IsIso.comp_isIso _ _ _ _ _ _ _
      (Iso.isIso_hom (tensorIso (s.fibreToSpaceTwistModuleIso Px Px.U Px.toSpace i)
        (s.fibreToSpaceTwistModuleIso Px Px.U Px.toSpace j))) hR
  have h2 := @IsIso.of_isIso_comp_left _ _ _ _ _ _ _
    (Iso.isIso_inv (modulePullbackTensorIso s.site s.base s.containsBase
      (s.fibreToSpaceHom Px.U Px.toSpace) (s.twistModule Px i).obj (s.twistModule Px j).obj)) h1
  have h3 := @IsIso.of_isIso_comp_right _ _ _ _ _ _ _
    (Iso.isIso_hom (s.fibreToSpaceTwistModuleIso Px Px.U Px.toSpace (i + j))) h2
  exact (isIso_modulePullback_map_iff_of_isEtale_of_isSurjective s.site s.base s.containsBase
    (s.fibreToSpaceHom Px.U Px.toSpace) (s.isEtale_fibreToSpaceHom_presentation Px)
    (s.isSurjective_fibreToSpaceHom_presentation Px) (s.twistAlgebraMul Px i j)).1 h3

/-- **Stacks 085D (3), multiplication.**  For a quasi-coherent graded `𝒪_X`-algebra `𝒜` on an
algebraic space `X` generated as an `𝒜₀`-algebra by `𝒜₁`, and `P = Proj_X(𝒜)` the relative Proj
of Stacks 084A–084B, the multiplication maps of `⨁_{n ∈ ℤ} 𝒪_P(n)` (Stacks 084D) induce
isomorphisms `𝒪_P(n) ⊗_{𝒪_P} 𝒪_P(m) ⟶ 𝒪_P(n + m)` for all integers `n` and `m`, the tensor
product being the tensor product sheaf of `𝒪_P`-modules.

It is `AlgebraicGeometry.Space.RelativeProjSituation.isIso_twistAlgebraMul` read through the
identification of the two tensor products (`…mulSheaf_twistGradedAlgebra`). -/
@[stacks 085D "(3), multiplication: for a quasi-coherent graded O_X-algebra A on an algebraic \
space X generated as an A_0-algebra by A_1 (s.IsGeneratedInDegreeOne), the multiplication maps \
O_P(n) (x)_{O_P} O_P(m) -> O_P(n + m) of the graded algebra (+)_{n in Z} O_P(n) of Tag 084D \
(twistGradedAlgebra) on the relative Proj P = Proj_X(A) of Tags 084A-084B are isomorphisms for \
all integers n, m"]
theorem isIso_mulSheaf_twistGradedAlgebra (hgen : s.IsGeneratedInDegreeOne) (n m : ℤ) :
    haveI := SmallEtale.instHasSheafify s.site s.base s.containsBase s.relativeProjFunctor
      AddCommGrpCat.{u}
    haveI := SmallEtale.instWEqualsLocallyBijective s.site s.base s.containsBase
      s.relativeProjFunctor AddCommGrpCat.{u}
    IsIso (SheafOfModules.GradedAlgebra.mulSheaf.{u, u + 1, u, u}
        (J := SmallEtale.topology s.site s.base s.containsBase s.relativeProjFunctor)
        (s.twistGradedAlgebra Px) n m) := by
  haveI := SmallEtale.instHasSheafify s.site s.base s.containsBase s.relativeProjFunctor
    AddCommGrpCat.{u}
  haveI := SmallEtale.instWEqualsLocallyBijective s.site s.base s.containsBase
    s.relativeProjFunctor AddCommGrpCat.{u}
  have := s.isIso_twistAlgebraMul Px hgen n m
  rw [s.mulSheaf_twistGradedAlgebra Px n m]
  exact @IsIso.comp_isIso _ _ _ _ _ _ _
    (Iso.isIso_inv (modulesTensorObjIso s.site s.base s.containsBase s.relativeProjFunctor
      s.isAlgebraicSpace_relativeProjFunctor (s.twistModule Px n).obj (s.twistModule Px m).obj))
    this

end RelativeProjSituation

end AlgebraicGeometry.Space

end
