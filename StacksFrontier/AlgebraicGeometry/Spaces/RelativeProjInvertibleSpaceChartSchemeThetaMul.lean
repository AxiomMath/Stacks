module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjInvertibleSpaceChartMap
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjInvertibleThetaBaseChange
public import StacksFrontier.AlgebraicGeometry.RelativeProjBaseChangeTwist.LegSections
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.PsiMultiplicativeScheme
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.TwistMul
public import StacksFrontier.AlgebraicGeometry.Morphism.TwistMulLeg
public import StacksFrontier.AlgebraicGeometry.RelativeProjInvertibleMorphism.ThetaUnit

/-!
# The scheme factor of the chart maps of `θ` of Stacks 0D2Z is multiplicative and unital

Let `w : W ⟶ U(ψ)` be a scheme point of the open subspace `U(ψ)` of Stacks 0D2Z.  The chart map
`χ_w = σ_w ≫ m_w ≫ τ_w` of `θ` at `w` (`…InvertibleTwistingRestriction.chartMap`) has as middle
factor `m_w` the module attached (Stacks 03DX (2)) to the map `θ` of [Stacks, Tag 01O9] on `W`,
read along the section `c_w : W ⟶ W ×_Y Proj_Y(𝒜)`
(`…InvertibleTwistingRestriction.chartSchemeTheta`):

`c_w^*𝒪(d) ≅ (c_w ≫ t)^*𝒪(d) = r_w^*𝒪(d) ≅ g^*r^*𝒪(d) ⟶ g^*(ℒ^{⊗ d}|_{U(w^*ψ)}) ≅ (w^*ℒ)^{⊗ d}`.

This file shows that this map carries the pullback along `c_w` of the multiplication of the twists
of Stacks 01NR (read through Stacks 03EL) to the multiplication of the Laurent algebra
`⨁_d (w^*ℒ)^{⊗ d}`: each factor carries the multiplication of its source to that of its target —
the comparisons of Stacks 03LU, the inverse image of `θ` (a homomorphism of graded algebras), and
`g^*(ℒ^{⊗ d}|_{U(w^*ψ)}) ≅ ℒ^{⊗ d}` (`…GradedPowerMap.laurentOnSectionPieceIso`, checked on the
images of local sections under the unit of `g^* ⊣ g_*`).  It is the middle square `hm` of
`AlgebraicGeometry.Space.mul_of_factor_squares`.  In degree `0` the same map carries the pullback
along `c_w` of the unit of the twists (read through Stacks 03LU) to the unit of
`⨁_d (w^*ℒ)^{⊗ d}`: the comparisons of Stacks 03LU are isomorphisms of sheaves of graded algebras,
`θ` is unital (`…GradedPowerMap.theta_map_one`), and `g^*(ℒ^{⊗ 0}|_{U(w^*ψ)}) ≅ ℒ^{⊗ 0}` is
checked on the global section `1`.

## Main definitions

* `…GradedPowerMap.laurentOnSectionHom`: `g^*(⨁_d ℒ^{⊗ d}|_{U(ψ)}) ⟶ ⨁_d ℒ^{⊗ d}` for a right
  inverse `g` of `U(ψ) ⊆ T`, as a homomorphism of sheaves of graded algebras.

## Main results

* `…GradedPowerMap.pbMul_comp_thetaOnSection`: `θ` read on `T` along `g`, preceded by the
  comparisons along a factorisation `C ≫ t = g ≫ r`, carries the twice pulled-back multiplication
  of the twists to the multiplication of `⨁_d ℒ^{⊗ d}`; at free morphisms.
* `…GradedPowerMap.pullbackTensorIso_inv_comp_map_mulSheaf_comp_of_heq`: the same in the spelling
  of the quasi-coherent modules on schemes, with the twists and the maps `θ_n` as variables.
* `…InvertibleTwistingRestriction.pullbackTensorIso_inv_comp_map_mulSheaf_comp_chartTheta`:
  **`θ` at a scheme point `w` of `U(ψ)` is multiplicative**, for a general
  `R : s.InvertibleTwistingRestriction f` and any morphism `c : W ⟶ W ×_Y Proj_Y(𝒜)` with
  `c ≫ t = r_w`: the underlying morphisms of `…InvertibleTwistingRestriction.chartSchemeTheta`
  (for `R = ofUnitalHom`, `c = c_w`) carry the pulled-back multiplication of the twists of
  Stacks 01NR to the multiplication of `⨁_d (w^*ℒ)^{⊗ d}`.
* `…GradedPowerMap.oneHom_comp_laurentOnSectionPieceIso_hom`,
  `…GradedPowerMap.oneHom_comp_thetaOnSection`: `g^*(ℒ^{⊗ 0}|_{U(ψ)}) ≅ ℒ^{⊗ 0}` and `θ` read on
  `T` along `g` carry the unit to the unit.
* `…GradedPowerMap.pullbackUnitIso_inv_comp_map_oneHom_comp_of_heq`: the same preceded by the
  comparisons along a factorisation `C ≫ t = g ≫ r`, with the twists and the maps `θ_n` as
  variables.
* `…InvertibleTwistingRestriction.pullbackUnitIso_inv_comp_map_oneHom_comp_chartTheta`:
  **`θ` at a scheme point `w` of `U(ψ)` is unital**, for a general
  `R : s.InvertibleTwistingRestriction f` and any `c : W ⟶ W ×_Y Proj_Y(𝒜)` with `c ≫ t = r_w`:
  the unit companion of `…pullbackTensorIso_inv_comp_map_mulSheaf_comp_chartTheta`.

## Implementation notes

The steps are proved at free variables and instantiated once.  The quasi-coherent statement is
glued from the scheme-level one factor by factor
(`AlgebraicGeometry.Space.comp_comp_eq_comp_of_hom_eq`), so that no two spellings of a whole
composite are compared.

## References

* [Stacks Project, Tag 0D2Z](https://stacks.math.columbia.edu/tag/0D2Z)
* [Stacks Project, Tag 01O9](https://stacks.math.columbia.edu/tag/01O9)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite
open AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules (pullbackSection)
open Stacks.AmpleProjectiveImmersion (tensorPowerModule)
open Stacks.RingedSpace RingedSpaceModuleAdjunction
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf
open Stacks.AlgebraicGeometry.ProjChartGradedTriple (laurentOn)
open Stacks.Sheaves.GradedAlgebraEssentiallySmall (gradedPull)

universe u m

attribute [local instance 5000] AlgebraicGeometry.Space.SmallEtale.instHasSheafify
  AlgebraicGeometry.Space.SmallEtale.instWEqualsLocallyBijective

namespace Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism.GradedPowerMap

open Stacks.AlgebraicGeometry.TwistMulLeg

attribute [local irreducible] GradedPowerMap.globalMorphism
  Stacks.AlgebraicGeometry.ProjChartFullGraded.GradedSections.glued

variable {S : Scheme.{u}} {A : SheafGradedAlgebra.{u} S} {T : Scheme.{u}} {f : T ⟶ S}
  (P : GradedPowerMap A f) (g : T ⟶ P.coveringOpen.toScheme) (hg : g ≫ P.coveringOpen.ι = 𝟙 T)

include hg in
/-- An open `V` of `T` over an open `O'` of `U(ψ)` along a right inverse `g` of the inclusion
lies in the image of `O'`. -/
theorem le_image_of_le_preimage (O' : P.coveringOpen.toScheme.Opens) {V : T.Opens}
    (h4 : V ≤ g ⁻¹ᵁ O') : V ≤ P.coveringOpen.ι ''ᵁ O' := fun x hx =>
  ⟨g.base x, h4 hx, congrArg (fun k : T ⟶ T => k.base x) hg⟩

/-- **`g^*(ℒ^{⊗ n}|_{U(ψ)}) ≅ ℒ^{⊗ n}` on a pulled-back section is the restriction.** -/
theorem laurentOnSectionPieceIso_hom_pullbackSection (n : ℤ) (O' : P.coveringOpen.toScheme.Opens)
    (V : T.Opens) (h4 : V ≤ g ⁻¹ᵁ O')
    (t : Γ((tensorPowerModule T P.L n).restrict P.coveringOpen.ι, O')) :
    (P.laurentOnSectionPieceIso g hg n).hom.val.app (op V)
        (pullbackSection g ((laurentOn P.L P.coveringOpen).piece n) O' V h4 t) =
      (tensorPowerModule T P.L n).val.map
        (homOfLE (P.le_image_of_le_preimage g hg O' h4)).op t := by
  have hO : O' ≤ P.coveringOpen.ι ⁻¹ᵁ (P.coveringOpen.ι ''ᵁ O') :=
    (P.coveringOpen.ι.preimage_image_eq O').ge
  have h5 : V ≤ (g ≫ P.coveringOpen.ι) ⁻¹ᵁ (P.coveringOpen.ι ''ᵁ O') :=
    h4.trans (g.preimage_mono hO)
  have h6 : V ≤ (𝟙 T) ⁻¹ᵁ (P.coveringOpen.ι ''ᵁ O') := hg ▸ h5
  have g1 := (Scheme.Modules.pullbackSection_naturality g
    ((Scheme.Modules.restrictFunctorIsoPullback P.coveringOpen.ι).hom.app
      (tensorPowerModule T P.L n)) O' V h4 t).trans
      (congrArg (pullbackSection g _ O' V h4)
        (restrictFunctorIsoPullback_hom_val_app P.coveringOpen.ι (tensorPowerModule T P.L n) O'
          hO t))
  have g2 := Scheme.Modules.pullbackSection_comp g P.coveringOpen.ι (tensorPowerModule T P.L n)
    _ O' V hO h4 h5 t
  have g3 := Scheme.Modules.pullbackSection_congr hg (tensorPowerModule T P.L n) _ V h5 h6 t
  have g4 := Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.pullbackId_hom_pullbackSection
    (tensorPowerModule T P.L n) _ V h6 (P.le_image_of_le_preimage g hg O' h4) t
  have g12 := (congrArg (((Scheme.Modules.pullbackComp g P.coveringOpen.ι).hom.app
    (tensorPowerModule T P.L n)).val.app (op V)) g1).trans g2
  have g123 := (congrArg (((Scheme.Modules.pullbackCongr hg).hom.app
    (tensorPowerModule T P.L n)).val.app (op V)) g12).trans g3
  exact (congrArg (((Scheme.Modules.pullbackId T).hom.app
    (tensorPowerModule T P.L n)).val.app (op V)) g123).trans g4

/-- `…laurentOnSectionPieceIso_hom_pullbackSection` on the image of a section under the unit of
`g^* ⊣ g_*`. -/
theorem laurentOnSectionPieceIso_hom_pullbackUnit (n : ℤ) (O' : P.coveringOpen.toScheme.Opens)
    (t : Γ((tensorPowerModule T P.L n).restrict P.coveringOpen.ι, O')) :
    (P.laurentOnSectionPieceIso g hg n).hom.val.app (op (g ⁻¹ᵁ O'))
        (pullbackUnit g.toLRSHom.toShHom ((laurentOn P.L P.coveringOpen).piece n) (op O') t) =
      (tensorPowerModule T P.L n).val.map
        (homOfLE (P.le_image_of_le_preimage g hg O' le_rfl)).op t :=
  (congrArg ((P.laurentOnSectionPieceIso g hg n).hom.val.app (op (g ⁻¹ᵁ O')))
    (Stacks.Conormal.pullbackSection_self g ((laurentOn P.L P.coveringOpen).piece n) O'
      t).symm).trans
    (P.laurentOnSectionPieceIso_hom_pullbackSection g hg n O' _ le_rfl t)

/-- **`g^*(ℒ^{⊗ n}|_{U(ψ)}) ≅ ℒ^{⊗ n}` is multiplicative on the images of sections under the
unit.** -/
theorem laurentOnSectionPieceIso_hom_mul_pullbackUnit (i k : ℤ)
    (O' : P.coveringOpen.toScheme.Opens)
    (a : Γ((tensorPowerModule T P.L i).restrict P.coveringOpen.ι, O'))
    (b : Γ((tensorPowerModule T P.L k).restrict P.coveringOpen.ι, O')) :
    (P.laurentOnSectionPieceIso g hg (i + k)).hom.val.app (op (g ⁻¹ᵁ O'))
        (pullbackUnit g.toLRSHom.toShHom ((laurentOn P.L P.coveringOpen).piece (i + k)) (op O')
          (Stacks.TensorPowerDivision.localMul P.L a b)) =
      Stacks.TensorPowerDivision.localMul P.L
        ((P.laurentOnSectionPieceIso g hg i).hom.val.app (op (g ⁻¹ᵁ O'))
          (pullbackUnit g.toLRSHom.toShHom ((laurentOn P.L P.coveringOpen).piece i) (op O') a))
        ((P.laurentOnSectionPieceIso g hg k).hom.val.app (op (g ⁻¹ᵁ O'))
          (pullbackUnit g.toLRSHom.toShHom ((laurentOn P.L P.coveringOpen).piece k) (op O')
            b)) := by
  refine (P.laurentOnSectionPieceIso_hom_pullbackUnit g hg (i + k) O' _).trans ?_
  refine Eq.trans ?_ (congrArg₂ (Stacks.TensorPowerDivision.localMul P.L)
    (P.laurentOnSectionPieceIso_hom_pullbackUnit g hg i O' a).symm
    (P.laurentOnSectionPieceIso_hom_pullbackUnit g hg k O' b).symm)
  exact Stacks.TensorPowerDivision.map_localMul _ _ _ _

/-- **`g^*(⨁_d ℒ^{⊗ d}|_{U(ψ)}) ⟶ ⨁_d ℒ^{⊗ d}`** for a right inverse `g` of the inclusion
`U(ψ) ⊆ T`, as a homomorphism of sheaves of graded algebras: degreewise
`…GradedPowerMap.laurentOnSectionPieceIso`. -/
def laurentOnSectionHom :
    haveI := Stacks.AlgebraicGeometry.ProjChartGradedThetaBuild.isInvertible_of_isInvertibleModule
      (L := P.L)
    SheafOfModules.GradedAlgebra.Hom
      (Stacks.Conormal.gradedPullback g (laurentOn P.L P.coveringOpen)) (laurent P.L) :=
  haveI := Stacks.AlgebraicGeometry.ProjChartGradedThetaBuild.isInvertible_of_isInvertibleModule
    (L := P.L)
  { app := fun n => (P.laurentOnSectionPieceIso g hg n).hom
    map_mul := fun i k U x y => map_mul_of_pullbackUnit g.toLRSHom.toShHom
      (A := laurentOn P.L P.coveringOpen) (B := laurent P.L)
      (fun n => (P.laurentOnSectionPieceIso g hg n).hom) i k
      (fun V a b => P.laurentOnSectionPieceIso_hom_mul_pullbackUnit g hg i k V a b) U x y }

/-- **`θ` of [Stacks, Tag 01O9] is multiplicative, at the level of morphisms**: the degree
components of `θ` carry the inverse image along `r = r_{ℒ,ψ}` of the multiplication of the twists
(read through Stacks 03EL) to the multiplication of `⨁_d ℒ^{⊗ d}|_{U(ψ)}`. -/
theorem pbMul_comp_theta_app (i j : ℤ) :
    pbMul (P.globalMorphism (relativeProj A))
        (SheafOfModules.GradedAlgebra.mulSheaf (twD A).algebra i j) ≫ P.theta.app (i + j) =
      (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨P.coveringOpen.toScheme.toRingedSpace.presheaf,
            P.coveringOpen.toScheme.toRingedSpace.IsSheaf⟩)).map
        ((P.theta.app i, P.theta.app j) : (_, _) ⟶ (_, _)) ≫
        SheafOfModules.GradedAlgebra.mulSheaf (laurentOn P.L P.coveringOpen) i j :=
  (eq_whisker (Tag07ZGTwist.mulSheaf_pullbackGradedAlgebra_eq_pbMul
    (P.globalMorphism (relativeProj A)) (twD A).algebra i j) (P.theta.app (i + j))).symm.trans
    (AlgebraicGeometry.Space.mulSheaf_comp_tensorSheafMap_of_hom P.theta i j)

/-- **`g^*(ℒ^{⊗ d}|_{U(ψ)}) ≅ ℒ^{⊗ d}` is multiplicative, at the level of morphisms**: it carries
the inverse image along `g` of the multiplication of `⨁_d ℒ^{⊗ d}|_{U(ψ)}` (read through
Stacks 03EL) to the multiplication of `⨁_d ℒ^{⊗ d}`. -/
theorem pbMul_comp_laurentOnSectionPieceIso_hom (i j : ℤ) :
    haveI := Stacks.AlgebraicGeometry.ProjChartGradedThetaBuild.isInvertible_of_isInvertibleModule
      (L := P.L)
    pbMul g (SheafOfModules.GradedAlgebra.mulSheaf (laurentOn P.L P.coveringOpen) i j) ≫
        (P.laurentOnSectionPieceIso g hg (i + j)).hom =
      (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨T.toRingedSpace.presheaf, T.toRingedSpace.IsSheaf⟩)).map
        (((P.laurentOnSectionPieceIso g hg i).hom, (P.laurentOnSectionPieceIso g hg j).hom) :
          (_, _) ⟶ (_, _)) ≫
        SheafOfModules.GradedAlgebra.mulSheaf (laurent P.L) i j :=
  have := Stacks.AlgebraicGeometry.ProjChartGradedThetaBuild.isInvertible_of_isInvertibleModule
    (L := P.L)
  (eq_whisker (Tag07ZGTwist.mulSheaf_pullbackGradedAlgebra_eq_pbMul g
    (laurentOn P.L P.coveringOpen) i j) ((P.laurentOnSectionPieceIso g hg (i + j)).hom)).symm.trans
    (AlgebraicGeometry.Space.mulSheaf_comp_tensorSheafMap_of_hom (P.laurentOnSectionHom g hg) i j)

/-- **`θ` read on `T` along `g` is multiplicative**: `…GradedPowerMap.thetaOnSection` carries the
inverse image along `g ≫ r` of the multiplication of the twists, read through Stacks 03EL, to the
multiplication of `⨁_d ℒ^{⊗ d}`. -/
theorem pbMul_comp_thetaOnSection_self (i j : ℤ) :
    haveI := Stacks.AlgebraicGeometry.ProjChartGradedThetaBuild.isInvertible_of_isInvertibleModule
      (L := P.L)
    pbMul (g ≫ P.globalMorphism (relativeProj A))
        (SheafOfModules.GradedAlgebra.mulSheaf (twD A).algebra i j) ≫
        P.thetaOnSection g hg (i + j) =
      (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨T.toRingedSpace.presheaf, T.toRingedSpace.IsSheaf⟩)).map
        ((P.thetaOnSection g hg i, P.thetaOnSection g hg j) : (_, _) ⟶ (_, _)) ≫
        SheafOfModules.GradedAlgebra.mulSheaf (laurent P.L) i j :=
  mul_comp
    (mul_inv ((Scheme.Modules.pullbackComp g (P.globalMorphism (relativeProj A))).app _)
      ((Scheme.Modules.pullbackComp g (P.globalMorphism (relativeProj A))).app _)
      ((Scheme.Modules.pullbackComp g (P.globalMorphism (relativeProj A))).app _)
      (mul_pullbackComp g (P.globalMorphism (relativeProj A))
        (SheafOfModules.GradedAlgebra.mulSheaf (twD A).algebra i j)))
    (mul_comp (mul_pullback g (P.pbMul_comp_theta_app i j))
      (P.pbMul_comp_laurentOnSectionPieceIso_hom g hg i j))

attribute [local irreducible] GradedPowerMap.thetaOnSection

/-- `…GradedPowerMap.pbMul_comp_thetaOnSection_self` preceded by the transport along an equation
`ρ = g ≫ r`. -/
theorem pbMul_comp_pullbackCongr_thetaOnSection {ρ : T ⟶ (relativeProj A).scheme}
    (h : ρ = g ≫ P.globalMorphism (relativeProj A)) (i j : ℤ) :
    haveI := Stacks.AlgebraicGeometry.ProjChartGradedThetaBuild.isInvertible_of_isInvertibleModule
      (L := P.L)
    pbMul ρ (SheafOfModules.GradedAlgebra.mulSheaf (twD A).algebra i j) ≫
        ((Scheme.Modules.pullbackCongr h).hom.app ((twD A).algebra.piece (i + j)) ≫
          P.thetaOnSection g hg (i + j)) =
      (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨T.toRingedSpace.presheaf, T.toRingedSpace.IsSheaf⟩)).map
        (((Scheme.Modules.pullbackCongr h).hom.app ((twD A).algebra.piece i) ≫
            P.thetaOnSection g hg i,
          (Scheme.Modules.pullbackCongr h).hom.app ((twD A).algebra.piece j) ≫
            P.thetaOnSection g hg j) : (_, _) ⟶ (_, _)) ≫
        SheafOfModules.GradedAlgebra.mulSheaf (laurent P.L) i j :=
  mul_comp (X := T)
    (mul_pullbackCongr h (SheafOfModules.GradedAlgebra.mulSheaf (twD A).algebra i j))
    (P.pbMul_comp_thetaOnSection_self g hg i j)

/-- **`θ` read on `T` along `g` is multiplicative** (Stacks 01O9): for a factorisation
`C ≫ t = g ≫ r` of `g ≫ r`, `r = r_{ℒ,ψ}`, the map
`C^*t^*𝒪(d) ≅ (C ≫ t)^*𝒪(d) = (g ≫ r)^*𝒪(d) ⟶ ℒ^{⊗ d}` (the comparisons of Stacks 03LU followed by
`…GradedPowerMap.thetaOnSection`) carries the twice pulled-back multiplication of the twists, read
through Stacks 03EL, to the multiplication of the Laurent algebra `⨁_d ℒ^{⊗ d}`.  Every scheme
and morphism other than `θ` is free. -/
theorem pbMul_comp_thetaOnSection {F : Scheme.{u}} (C : T ⟶ F) (t : F ⟶ (relativeProj A).scheme)
    (h : C ≫ t = g ≫ P.globalMorphism (relativeProj A)) (i j : ℤ) :
    haveI := Stacks.AlgebraicGeometry.ProjChartGradedThetaBuild.isInvertible_of_isInvertibleModule
      (L := P.L)
    pbMul C (pbMul t (SheafOfModules.GradedAlgebra.mulSheaf (twD A).algebra i j)) ≫
        ((Scheme.Modules.pullbackComp C t).hom.app ((twD A).algebra.piece (i + j)) ≫
          (Scheme.Modules.pullbackCongr h).hom.app ((twD A).algebra.piece (i + j)) ≫
          P.thetaOnSection g hg (i + j)) =
      (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨T.toRingedSpace.presheaf, T.toRingedSpace.IsSheaf⟩)).map
        (((Scheme.Modules.pullbackComp C t).hom.app ((twD A).algebra.piece i) ≫
            (Scheme.Modules.pullbackCongr h).hom.app ((twD A).algebra.piece i) ≫
            P.thetaOnSection g hg i,
          (Scheme.Modules.pullbackComp C t).hom.app ((twD A).algebra.piece j) ≫
            (Scheme.Modules.pullbackCongr h).hom.app ((twD A).algebra.piece j) ≫
            P.thetaOnSection g hg j) : (_, _) ⟶ (_, _)) ≫
        SheafOfModules.GradedAlgebra.mulSheaf (laurent P.L) i j :=
  mul_comp (X := T)
    (mul_pullbackComp C t (SheafOfModules.GradedAlgebra.mulSheaf (twD A).algebra i j))
    (P.pbMul_comp_pullbackCongr_thetaOnSection g hg h i j)

omit P g hg in
/-- **The multiplication of a pulled-back sheaf of graded algebras, in the two spellings of the
inverse image of a multiplication**: Stacks 03EL as
`Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso` followed by the inverse image of the
multiplication is `Stacks.AlgebraicGeometry.TwistMulLeg.pbMul` of it; at free variables. -/
theorem pullbackTensorIso_inv_comp_map_mulSheaf_eq_pbMul {X Y : Scheme.{u}} (q : X ⟶ Y)
    (G : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf Y.toRingedSpace)) (i j : ℤ) :
    @CategoryStruct.comp (SheafOfModules X.ringCatSheaf) _ _ _ _
        (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso q (G.piece i) (G.piece j)).inv
        ((Scheme.Modules.pullback q).map (SheafOfModules.GradedAlgebra.mulSheaf G i j)) =
      pbMul q (SheafOfModules.GradedAlgebra.mulSheaf G i j) :=
  (Stacks.RingedSpace.mulSheaf_pullbackGradedAlgebra q.toLRSHom.toShHom G i j).symm.trans
    (Tag07ZGTwist.mulSheaf_pullbackGradedAlgebra_eq_pbMul q G i j)

/-- `…GradedPowerMap.pbMul_comp_thetaOnSection` in the spelling of the quasi-coherent modules on
schemes: the source multiplication as Stacks 03EL
(`Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso`) followed by the inverse image along `C`
of the multiplication of `t^*(⨁_d 𝒪(d))`, the tensor products on the Zariski ringed site of `T`,
every composite taken in the category of sheaves of modules over `T.ringCatSheaf`; at free
variables. -/
theorem pullbackTensorIso_inv_comp_map_mulSheaf_comp_thetaOnSection {F : Scheme.{u}}
    (C : T ⟶ F) (t : F ⟶ (relativeProj A).scheme)
    (h : C ≫ t = g ≫ P.globalMorphism (relativeProj A)) (i j : ℤ) :
    haveI := Stacks.AlgebraicGeometry.ProjChartGradedThetaBuild.isInvertible_of_isInvertibleModule
      (L := P.L)
    @CategoryStruct.comp (SheafOfModules T.ringCatSheaf) _ _ _ _
        (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso C
          ((Scheme.Modules.pullback t).obj ((twD A).algebra.piece i))
          ((Scheme.Modules.pullback t).obj ((twD A).algebra.piece j))).inv
        (@CategoryStruct.comp (SheafOfModules T.ringCatSheaf) _ _ _ _
          ((Scheme.Modules.pullback C).map (SheafOfModules.GradedAlgebra.mulSheaf
            (Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.pbAlgS t (twD A).algebra) i j))
          ((Scheme.Modules.pullbackComp C t).hom.app ((twD A).algebra.piece (i + j)) ≫
            (Scheme.Modules.pullbackCongr h).hom.app ((twD A).algebra.piece (i + j)) ≫
            P.thetaOnSection g hg (i + j))) =
      @CategoryStruct.comp (SheafOfModules T.ringCatSheaf) _ _ _ _
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            T.zariskiRingedSite.toRingedTopos.O).map
            ((Scheme.Modules.pullbackComp C t).hom.app ((twD A).algebra.piece i) ≫
              (Scheme.Modules.pullbackCongr h).hom.app ((twD A).algebra.piece i) ≫
              P.thetaOnSection g hg i)).app
            ((Scheme.Modules.pullback C).obj
              ((Scheme.Modules.pullback t).obj ((twD A).algebra.piece j))) ≫
          ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            T.zariskiRingedSite.toRingedTopos.O).obj (tensorPowerModule T P.L i)).map
            ((Scheme.Modules.pullbackComp C t).hom.app ((twD A).algebra.piece j) ≫
              (Scheme.Modules.pullbackCongr h).hom.app ((twD A).algebra.piece j) ≫
              P.thetaOnSection g hg j))
        (SheafOfModules.GradedAlgebra.mulSheaf (laurent P.L) i j) :=
  (Category.assoc _ _ _).symm.trans
    ((eq_whisker ((pullbackTensorIso_inv_comp_map_mulSheaf_eq_pbMul C
        (Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.pbAlgS t (twD A).algebra) i j).trans
      (congrArg (pbMul C)
        (Tag07ZGTwist.mulSheaf_pullbackGradedAlgebra_eq_pbMul t (twD A).algebra i j))) _).trans
      (P.pbMul_comp_thetaOnSection g hg C t h i j))

/-- `…GradedPowerMap.pullbackTensorIso_inv_comp_map_mulSheaf_comp_thetaOnSection` with the twists
`G` and the maps `Θ_n` as variables, given by an equation `G = ⨁_d 𝒪(d)` and by
`Θ_n ≍ …GradedPowerMap.thetaOnSection` (both substituted inside), so that an instance is read off
the spelling of its own data. -/
theorem pullbackTensorIso_inv_comp_map_mulSheaf_comp_of_heq {F : Scheme.{u}} (C : T ⟶ F)
    (t : F ⟶ (relativeProj A).scheme) (h : C ≫ t = g ≫ P.globalMorphism (relativeProj A))
    {G : Stacks.AlgebraicGeometry.RelativeProjTwists.SchemeGradedAlgebra (relativeProj A).scheme}
    (eG : G = (twD A).algebra)
    {Θ : ∀ n : ℤ, (Scheme.Modules.pullback (g ≫ P.globalMorphism (relativeProj A))).obj
      (G.piece n) ⟶ tensorPowerModule T P.L n}
    (hΘ : ∀ n : ℤ, HEq (Θ n) (P.thetaOnSection g hg n)) (i j : ℤ) :
    haveI := Stacks.AlgebraicGeometry.ProjChartGradedThetaBuild.isInvertible_of_isInvertibleModule
      (L := P.L)
    @CategoryStruct.comp (SheafOfModules T.ringCatSheaf) _ _ _ _
        (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso C
          ((Scheme.Modules.pullback t).obj (G.piece i))
          ((Scheme.Modules.pullback t).obj (G.piece j))).inv
        (@CategoryStruct.comp (SheafOfModules T.ringCatSheaf) _ _ _ _
          ((Scheme.Modules.pullback C).map (SheafOfModules.GradedAlgebra.mulSheaf
            (Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.pbAlgS t G) i j))
          ((Scheme.Modules.pullbackComp C t).hom.app (G.piece (i + j)) ≫
            (Scheme.Modules.pullbackCongr h).hom.app (G.piece (i + j)) ≫ Θ (i + j))) =
      @CategoryStruct.comp (SheafOfModules T.ringCatSheaf) _ _ _ _
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            T.zariskiRingedSite.toRingedTopos.O).map
            ((Scheme.Modules.pullbackComp C t).hom.app (G.piece i) ≫
              (Scheme.Modules.pullbackCongr h).hom.app (G.piece i) ≫ Θ i)).app
            ((Scheme.Modules.pullback C).obj ((Scheme.Modules.pullback t).obj (G.piece j))) ≫
          ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            T.zariskiRingedSite.toRingedTopos.O).obj (tensorPowerModule T P.L i)).map
            ((Scheme.Modules.pullbackComp C t).hom.app (G.piece j) ≫
              (Scheme.Modules.pullbackCongr h).hom.app (G.piece j) ≫ Θ j))
        (SheafOfModules.GradedAlgebra.mulSheaf (laurent P.L) i j) := by
  subst eG
  obtain rfl : Θ = fun n => P.thetaOnSection g hg n := funext fun n => eq_of_heq (hΘ n)
  exact P.pullbackTensorIso_inv_comp_map_mulSheaf_comp_thetaOnSection g hg C t h i j

end Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism.GradedPowerMap


namespace AlgebraicGeometry.Space

section PointLaurentMul

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : AlgebraicSpaces B S hS}
  (L : SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O))
  [hL : Stacks.SheafOfModules.IsInvertible (smallEtaleRingedTopos B S hS X).O.obj
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O).property L]

/-- **The multiplication `(x^*ℒ)^{⊗ i} ⊗ (x^*ℒ)^{⊗ j} ⟶ (x^*ℒ)^{⊗ (i + j)}`** of the Laurent
algebra of the restriction `x^*ℒ` of `ℒ` to a scheme point `x : T ⟶ X`, as a morphism of
quasi-coherent modules on `T`. -/
def pointLaurentPieceMul (T : BigFppfOver B S hS) (x : yoneda.obj T ⟶ X.1) (i j : ℤ) :
    quasicoherentTensorObj B S hS T (pointLaurentPieceQcoh L T x i)
        (pointLaurentPieceQcoh L T x j) ⟶
      pointLaurentPieceQcoh L T x (i + j) :=
  ObjectProperty.homMk
    (SheafOfModules.GradedAlgebra.mulSheaf (laurent (pointLine B S hS L T x)) i j)

/-- The underlying morphism of `AlgebraicGeometry.Space.pointLaurentPieceMul`. -/
theorem pointLaurentPieceMul_hom (T : BigFppfOver B S hS) (x : yoneda.obj T ⟶ X.1) (i j : ℤ) :
    (pointLaurentPieceMul L T x i j).hom =
      SheafOfModules.GradedAlgebra.mulSheaf (laurent (pointLine B S hS L T x)) i j :=
  ObjectProperty.homMk_hom _

end PointLaurentMul

namespace RelativeProjSituation.InvertibleTwistingRestriction

open Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism

section Restriction

variable {s : RelativeProjSituation.{u, m}}
  {X : (BigFppfOver s.site s.base s.containsBase)ᵒᵖ ⥤ Type u} {f : X ⟶ s.space.1}
  (R : s.InvertibleTwistingRestriction f)
  {W : BigFppfOver s.site s.base s.containsBase} (w : yoneda.obj W ⟶ X) (hw : R.locusOpen W w = ⊤)

/-- **`θ` at a scheme point `w` of `U(ψ)` is multiplicative** (Stacks 0D2Z and 01O9), for a
general restriction datum `R` and any morphism `c : W ⟶ W ×_Y Proj_Y(𝒜)` of the site with
`c ≫ t = r_w`: the pullback along `c` of the multiplication of the twists of Stacks 01NR on
`W ×_Y Proj_Y(𝒜)` (read through Stacks 03EL), followed by
`c^*𝒪(i + j) ≅ (c ≫ t)^*𝒪(i + j) = r_w^*𝒪(i + j) ⟶ (w^*ℒ)^{⊗ (i + j)}`
(`…InvertibleTwistingRestriction.chartTheta`), is the tensor product of the same maps in degrees
`i` and `j` followed by the multiplication of the Laurent algebra `⨁_d (w^*ℒ)^{⊗ d}`; in the
spelling of the quasi-coherent modules on schemes. -/
theorem pullbackTensorIso_inv_comp_map_mulSheaf_comp_chartTheta
    (c : W ⟶ s.relativeProjPoints.fibre W (w ≫ f))
    (h : (BigFppfOver.toScheme s.site s.base s.containsBase).map c ≫ s.toRelativeProj W (w ≫ f) =
      R.chartMorphism w hw) (i j : ℤ) :
    type_of% (GradedPowerMap.pullbackTensorIso_inv_comp_map_mulSheaf_comp_of_heq
      (toGradedPowerMap (R.twisting W w)) (R.chartLift w hw) (R.chartLift_ι w hw)
      ((BigFppfOver.toScheme s.site s.base s.containsBase).map c) (s.toRelativeProj W (w ≫ f)) h
      (G := Stacks.AlgebraicGeometry.Tag07ZGTwist.twistAlgebra (s.shrink.pointAlgebra W (w ≫ f)))
      rfl (Θ := fun n => R.chartTheta w hw n)
      (fun n => heq_of_eq (InvertibleTwistingRestriction.chartTheta.eq_1 R w hw n)) i j) :=
  GradedPowerMap.pullbackTensorIso_inv_comp_map_mulSheaf_comp_of_heq
    (toGradedPowerMap (R.twisting W w)) (R.chartLift w hw) (R.chartLift_ι w hw)
    ((BigFppfOver.toScheme s.site s.base s.containsBase).map c) (s.toRelativeProj W (w ≫ f)) h
    (G := Stacks.AlgebraicGeometry.Tag07ZGTwist.twistAlgebra (s.shrink.pointAlgebra W (w ≫ f)))
    rfl (Θ := fun n => R.chartTheta w hw n)
    (fun n => heq_of_eq (InvertibleTwistingRestriction.chartTheta.eq_1 R w hw n)) i j

end Restriction


end RelativeProjSituation.InvertibleTwistingRestriction

end AlgebraicGeometry.Space


namespace Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism.GradedPowerMap

open Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist (pbAlgS)
open Stacks.AlgebraicGeometry.GradedAlgebraPullbackComp

section Unit

attribute [local irreducible] GradedPowerMap.globalMorphism
  Stacks.AlgebraicGeometry.ProjChartFullGraded.GradedSections.glued

variable {S : Scheme.{u}} {A : SheafGradedAlgebra.{u} S} {T : Scheme.{u}} {f : T ⟶ S}
  (P : GradedPowerMap A f)

/-- **`θ` of [Stacks, Tag 01O9] is unital, at the level of morphisms**: the unit of the inverse
image along `r = r_{ℒ,ψ}` of the twists followed by the degree-`0` part of `θ` is the unit of
`⨁_d ℒ^{⊗ d}|_{U(ψ)}`. -/
theorem oneHom_comp_theta_app_zero :
    SheafOfModules.GradedAlgebra.oneHom
        (pbAlgS (P.globalMorphism (relativeProj A)) (twD A).algebra) ≫ P.theta.app 0 =
      SheafOfModules.GradedAlgebra.oneHom (laurentOn P.L P.coveringOpen) :=
  oneHom_comp_app_zero P.thetaUnital

/-- **The inverse image along `g` of `θ` is unital**: the unit of `g^*r^*(⨁_d 𝒪(d))` followed by
the inverse image along `g` of the degree-`0` part of `θ` is the unit of
`g^*(⨁_d ℒ^{⊗ d}|_{U(ψ)})`. -/
theorem oneHom_comp_pullback_map_theta_app_zero {T' : Scheme.{u}}
    (g : T' ⟶ P.coveringOpen.toScheme) :
    SheafOfModules.GradedAlgebra.oneHom
        (pbAlgS g (pbAlgS (P.globalMorphism (relativeProj A)) (twD A).algebra)) ≫
        (Scheme.Modules.pullback g).map (P.theta.app 0) =
      SheafOfModules.GradedAlgebra.oneHom (pbAlgS g (laurentOn P.L P.coveringOpen)) := by
  refine (congrArg (· ≫ (Scheme.Modules.pullback g).map (P.theta.app 0))
    (AlgebraicGeometry.Space.oneHom_pullbackGradedAlgebra_eq_pullbackUnitIso g
      (pbAlgS (P.globalMorphism (relativeProj A)) (twD A).algebra))).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg ((Scheme.Modules.pullbackUnitIso g).inv ≫ ·)
    (((Scheme.Modules.pullback g).map_comp _ _).symm.trans
      (congrArg (Scheme.Modules.pullback g).map P.oneHom_comp_theta_app_zero))).trans ?_
  exact (AlgebraicGeometry.Space.oneHom_pullbackGradedAlgebra_eq_pullbackUnitIso g
    (laurentOn P.L P.coveringOpen)).symm

variable (g : T ⟶ P.coveringOpen.toScheme) (hg : g ≫ P.coveringOpen.ι = 𝟙 T)

/-- **`g^*(ℒ^{⊗ 0}|_{U(ψ)}) ≅ ℒ^{⊗ 0}` is unital**: it carries the unit of the inverse image along
`g` of `⨁_d ℒ^{⊗ d}|_{U(ψ)}` to the unit of `⨁_d ℒ^{⊗ d}`.  Both are morphisms out of the
structure sheaf, so they are compared on the global section `1`, where the unit of the inverse
image is the image of the unit under the unit of `g^* ⊣ g_*` and
`…GradedPowerMap.laurentOnSectionPieceIso_hom_pullbackUnit` computes the identification. -/
theorem oneHom_comp_laurentOnSectionPieceIso_hom :
    haveI := Stacks.AlgebraicGeometry.ProjChartGradedThetaBuild.isInvertible_of_isInvertibleModule
      (L := P.L)
    SheafOfModules.GradedAlgebra.oneHom (pbAlgS g (laurentOn P.L P.coveringOpen)) ≫
        (P.laurentOnSectionPieceIso g hg 0).hom =
      SheafOfModules.GradedAlgebra.oneHom (laurent P.L) := by
  have := Stacks.AlgebraicGeometry.ProjChartGradedThetaBuild.isInvertible_of_isInvertibleModule
    (L := P.L)
  refine ((laurent P.L).piece 0).unitHomEquiv.injective ?_
  refine (SheafOfModules.unitHomEquiv_comp_apply _ _).trans ?_
  refine (congrArg (SheafOfModules.sectionsMap (P.laurentOnSectionPieceIso g hg 0).hom)
    (SheafOfModules.GradedAlgebra.unitHomEquiv_oneHom
      (pbAlgS g (laurentOn P.L P.coveringOpen)))).trans ?_
  refine Eq.trans ?_ (SheafOfModules.GradedAlgebra.unitHomEquiv_oneHom (laurent P.L)).symm
  refine Stacks.AlgebraicGeometry.AffineTwisting.sections_eq_of_eval_top _ _ _ ?_
  have hWt : (⊤ : T.Opens) ≤ g ⁻¹ᵁ ⊤ := fun _ _ => trivial
  have hI : g ⁻¹ᵁ ⊤ ≤ P.coveringOpen.ι ''ᵁ ⊤ := P.le_image_of_le_preimage g hg ⊤ le_rfl
  have hsrc : (pbAlgS g (laurentOn P.L P.coveringOpen)).one.eval (op ⊤) =
      ((Scheme.Modules.pullback g).obj ((laurentOn P.L P.coveringOpen).piece 0)).presheaf.map
        (homOfLE hWt).op
        (Stacks.RingedSpace.pullbackUnit g.toLRSHom.toShHom
          ((laurentOn P.L P.coveringOpen).piece 0) (op ⊤)
          ((laurentOn P.L P.coveringOpen).one.eval (op ⊤))) :=
    (PresheafOfModules.sections_property (pbAlgS g (laurentOn P.L P.coveringOpen)).one
        (homOfLE hWt).op).symm.trans
      (congrArg _ (Stacks.RingedSpace.pullbackGradedAlgebra_one_eval g.toLRSHom.toShHom
        (laurentOn P.L P.coveringOpen) ⊤))
  refine (congrArg (fun z => (P.laurentOnSectionPieceIso g hg 0).hom.val.app (op ⊤) z)
    hsrc).trans ?_
  refine (Stacks.AlgebraicGeometry.ProjChartRatioPullback.app_map
    (P.laurentOnSectionPieceIso g hg 0).hom (homOfLE hWt) _).trans ?_
  refine (congrArg (fun z => (tensorPowerModule T P.L 0).presheaf.map (homOfLE hWt).op z)
    ((P.laurentOnSectionPieceIso_hom_pullbackUnit g hg 0 ⊤ _).trans
      (PresheafOfModules.sections_property (laurent P.L).one (homOfLE hI).op))).trans ?_
  exact PresheafOfModules.sections_property (laurent P.L).one (homOfLE hWt).op

/-- **`θ` read on `T` along `g` is unital**: `…GradedPowerMap.thetaOnSection` in degree `0`
carries the unit of the inverse image along `g ≫ r` of the twists to the unit of
`⨁_d ℒ^{⊗ d}`. -/
theorem oneHom_comp_thetaOnSection :
    haveI := Stacks.AlgebraicGeometry.ProjChartGradedThetaBuild.isInvertible_of_isInvertibleModule
      (L := P.L)
    SheafOfModules.GradedAlgebra.oneHom
        (pbAlgS (g ≫ P.globalMorphism (relativeProj A)) (twD A).algebra) ≫
        P.thetaOnSection g hg 0 =
      SheafOfModules.GradedAlgebra.oneHom (laurent P.L) := by
  have h1 := AlgebraicGeometry.Space.oneHom_comp_iso_hom_app_zero
    (pullbackGradedAlgebraCompIso (twD A).algebra g (P.globalMorphism (relativeProj A))).symm
  have h2 := P.oneHom_comp_pullback_map_theta_app_zero g
  refine (congrArg (_ ≫ ·) (P.thetaOnSection_eq g hg 0)).trans ?_
  refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) h1).trans ?_)
  refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) h2).trans ?_)
  exact P.oneHom_comp_laurentOnSectionPieceIso_hom g hg

/-- **`θ` read on `T` along `g` is unital** (Stacks 01O9): for a factorisation `C ≫ t = g ≫ r` of
`g ≫ r`, `r = r_{ℒ,ψ}`, the map `C^*t^*𝒪(0) ≅ (C ≫ t)^*𝒪(0) = (g ≫ r)^*𝒪(0) ⟶ ℒ^{⊗ 0}` (the
comparisons of Stacks 03LU followed by `…GradedPowerMap.thetaOnSection`) carries the twice
pulled-back unit of the twists, read through Stacks 03LU, to the unit of the Laurent algebra
`⨁_d ℒ^{⊗ d}`.  Every scheme and morphism other than `θ` is free. -/
theorem pullbackUnitIso_inv_comp_map_oneHom_comp_thetaOnSection {F : Scheme.{u}} (C : T ⟶ F)
    (t : F ⟶ (relativeProj A).scheme) (h : C ≫ t = g ≫ P.globalMorphism (relativeProj A)) :
    haveI := Stacks.AlgebraicGeometry.ProjChartGradedThetaBuild.isInvertible_of_isInvertibleModule
      (L := P.L)
    (Scheme.Modules.pullbackUnitIso C).inv ≫
        (Scheme.Modules.pullback C).map
          (SheafOfModules.GradedAlgebra.oneHom (pbAlgS t (twD A).algebra)) ≫
        ((Scheme.Modules.pullbackComp C t).hom.app ((twD A).algebra.piece 0) ≫
          (Scheme.Modules.pullbackCongr h).hom.app ((twD A).algebra.piece 0) ≫
          P.thetaOnSection g hg 0) =
      SheafOfModules.GradedAlgebra.oneHom (laurent P.L) := by
  refine ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _)
    (AlgebraicGeometry.Space.oneHom_pullbackGradedAlgebra_eq_pullbackUnitIso C
      (pbAlgS t (twD A).algebra)).symm)).trans ?_
  have h1 := AlgebraicGeometry.Space.oneHom_comp_iso_hom_app_zero
    (pullbackGradedAlgebraCompIso (twD A).algebra C t)
  have h2 := AlgebraicGeometry.Space.oneHom_comp_iso_hom_app_zero
    (pullbackGradedAlgebraCongrIso (twD A).algebra h)
  refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) h1).trans ?_)
  refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) h2).trans ?_)
  exact P.oneHom_comp_thetaOnSection g hg

/-- `…GradedPowerMap.pullbackUnitIso_inv_comp_map_oneHom_comp_thetaOnSection` with the twists `G`
and the maps `Θ_n` as variables, given by an equation `G = ⨁_d 𝒪(d)` and by
`Θ_n ≍ …GradedPowerMap.thetaOnSection` (both substituted inside), so that an instance is read off
the spelling of its own data. -/
theorem pullbackUnitIso_inv_comp_map_oneHom_comp_of_heq {F : Scheme.{u}} (C : T ⟶ F)
    (t : F ⟶ (relativeProj A).scheme) (h : C ≫ t = g ≫ P.globalMorphism (relativeProj A))
    {G : Stacks.AlgebraicGeometry.RelativeProjTwists.SchemeGradedAlgebra (relativeProj A).scheme}
    (eG : G = (twD A).algebra)
    {Θ : ∀ n : ℤ, (Scheme.Modules.pullback (g ≫ P.globalMorphism (relativeProj A))).obj
      (G.piece n) ⟶ tensorPowerModule T P.L n}
    (hΘ : ∀ n : ℤ, HEq (Θ n) (P.thetaOnSection g hg n)) :
    haveI := Stacks.AlgebraicGeometry.ProjChartGradedThetaBuild.isInvertible_of_isInvertibleModule
      (L := P.L)
    @CategoryStruct.comp (SheafOfModules T.ringCatSheaf) _ _ _ _
        (Scheme.Modules.pullbackUnitIso C).inv
        (@CategoryStruct.comp (SheafOfModules T.ringCatSheaf) _ _ _ _
          ((Scheme.Modules.pullback C).map (SheafOfModules.GradedAlgebra.oneHom (pbAlgS t G)))
          (@CategoryStruct.comp (SheafOfModules T.ringCatSheaf) _ _ _ _
            ((Scheme.Modules.pullbackComp C t).hom.app (G.piece 0))
            (@CategoryStruct.comp (SheafOfModules T.ringCatSheaf) _ _ _ _
              ((Scheme.Modules.pullbackCongr h).hom.app (G.piece 0)) (Θ 0)))) =
      SheafOfModules.GradedAlgebra.oneHom (laurent P.L) := by
  subst eG
  obtain rfl : Θ = fun n => P.thetaOnSection g hg n := funext fun n => eq_of_heq (hΘ n)
  exact P.pullbackUnitIso_inv_comp_map_oneHom_comp_thetaOnSection g hg C t h

end Unit

end Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism.GradedPowerMap


namespace AlgebraicGeometry.Space.RelativeProjSituation.InvertibleTwistingRestriction

open Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism

section RestrictionUnit

variable {s : RelativeProjSituation.{u, m}}
  {X : (BigFppfOver s.site s.base s.containsBase)ᵒᵖ ⥤ Type u} {f : X ⟶ s.space.1}
  (R : s.InvertibleTwistingRestriction f)
  {W : BigFppfOver s.site s.base s.containsBase} (w : yoneda.obj W ⟶ X) (hw : R.locusOpen W w = ⊤)

/-- **`θ` at a scheme point `w` of `U(ψ)` is unital** (Stacks 0D2Z and 01O9), for a general
restriction datum `R` and any morphism `c : W ⟶ W ×_Y Proj_Y(𝒜)` of the site with `c ≫ t = r_w`:
the pullback along `c` of the unit of the twists of Stacks 01NR on `W ×_Y Proj_Y(𝒜)` (read through
Stacks 03LU), followed by `c^*𝒪(0) ≅ (c ≫ t)^*𝒪(0) = r_w^*𝒪(0) ⟶ (w^*ℒ)^{⊗ 0}`
(`…InvertibleTwistingRestriction.chartTheta`), is the unit of the Laurent algebra
`⨁_d (w^*ℒ)^{⊗ d}`. -/
theorem pullbackUnitIso_inv_comp_map_oneHom_comp_chartTheta
    (c : W ⟶ s.relativeProjPoints.fibre W (w ≫ f))
    (h : (BigFppfOver.toScheme s.site s.base s.containsBase).map c ≫ s.toRelativeProj W (w ≫ f) =
      R.chartMorphism w hw) :
    type_of% (GradedPowerMap.pullbackUnitIso_inv_comp_map_oneHom_comp_of_heq
      (toGradedPowerMap (R.twisting W w)) (R.chartLift w hw) (R.chartLift_ι w hw)
      ((BigFppfOver.toScheme s.site s.base s.containsBase).map c) (s.toRelativeProj W (w ≫ f)) h
      (G := Stacks.AlgebraicGeometry.Tag07ZGTwist.twistAlgebra (s.shrink.pointAlgebra W (w ≫ f)))
      rfl (Θ := fun n => R.chartTheta w hw n)
      (fun n => heq_of_eq (InvertibleTwistingRestriction.chartTheta.eq_1 R w hw n))) :=
  GradedPowerMap.pullbackUnitIso_inv_comp_map_oneHom_comp_of_heq _ _ _ _ _ h rfl
    (fun n => heq_of_eq (InvertibleTwistingRestriction.chartTheta.eq_1 R w hw n))

end RestrictionUnit

end AlgebraicGeometry.Space.RelativeProjSituation.InvertibleTwistingRestriction

end
