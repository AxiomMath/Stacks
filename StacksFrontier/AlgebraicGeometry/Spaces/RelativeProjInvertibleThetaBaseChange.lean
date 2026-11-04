module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjChartRatioPullbackLocalMul
public import StacksFrontier.AlgebraicGeometry.PullbackTensor.GradedAlgebraPullbackComp
public import StacksFrontier.AlgebraicGeometry.PullbackTensor.PullbackAlgebraMap
public import StacksFrontier.AlgebraicGeometry.RelativeProjInvertibleMorphism.ThetaClauseThree
public import StacksFrontier.AlgebraicGeometry.RelativeProjInvertibleMorphism.ThetaUniqueClauseOne
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjInvertibleMorphismPoints
public import StacksFrontier.AlgebraicGeometry.SymmetricPullback.BilinearExt
import StacksFrontier.AlgebraicGeometry.Descent.SectionsPullbackComparison.PullbackSection

/-!
# `θ'` is the pullback of `θ`: the last assertion of clause (3) of Stacks Tag 0D2Z

Let `f : X ⟶ S` be a morphism of schemes, `𝒜` a quasi-coherent graded `𝒪_S`-algebra, `ℒ` an
invertible `𝒪_X`-module and `ψ : f^*𝒜 ⟶ ⨁_d ℒ^{⊗ d}` a homomorphism of graded algebras, with
the open `U(ψ)`, the morphism `r = r_{ℒ,ψ} : U(ψ) ⟶ Proj_S(𝒜)` and the map of graded algebras
`θ : r^*(⨁_d 𝒪(d)) ⟶ ⨁_d ℒ^{⊗ d}|_{U(ψ)}` of [Stacks, Tag 01O9].  For a morphism of schemes
`q : W ⟶ X` put `ψ' = q^*ψ`, with `U(ψ') = q^{-1}(U(ψ))`, `r' = r_{q^*ℒ, ψ'}` and `θ'`, and let
`j : U(ψ') ⟶ U(ψ)` be the restriction of `q`, so that `j ≫ r = r'`
(`…RelativeProjInvertibleMorphism.coveringOpenPullback_globalMorphism`).  This file proves that
**`θ'` is the pullback `j^*θ` of `θ`**, read through the two canonical identifications of graded
`𝒪_{U(ψ')}`-algebras

* `j^*r^*(⨁_d 𝒪(d)) ≅ r'^*(⨁_d 𝒪(d))`, the pseudofunctoriality of the inverse image of graded
  algebras (`…GradedAlgebraPullbackComp.pullbackGradedAlgebraCompIso`) followed by the
  congruence along `j ≫ r = r'` (`…pullbackGradedAlgebraCongrIso`): `…thetaSourceIso`;
* `j^*(⨁_d ℒ^{⊗ d}|_{U(ψ)}) ≅ ⨁_d (q^*ℒ)^{⊗ d}|_{U(ψ')}`, degreewise the restriction to `U(ψ)`
  read as an inverse image, the pseudofunctoriality along `j ≫ ι_{U(ψ)} = ι_{U(ψ')} ≫ q`, and the
  comparison `q^*(ℒ^{⊗ d}) ≅ (q^*ℒ)^{⊗ d}` of the integral tensor powers of [Stacks, Tag 01CU]
  (`…ProjChartIntPullbackMul.intPullIso`), which is multiplicative: `…thetaTargetIso`.

The proof is the "clause-(1) check through them": the composite
`thetaSourceIso⁻¹ ≫ j^*θ ≫ thetaTargetIso` is a map of graded algebras, it satisfies clause (1)
of Tag 01O9 for `ψ'` (on a pulled-back homogeneous section both sides are the pullback along `q`
of `ψ(a)`, by `…valueSec_pullback`), and `θ'` is the only such map
(`…GradedPowerMap.eq_theta_of_clauseOne`).

In the situation of [Stacks, Tag 0D2Z] this is the assertion "`θ'` is the pullback of `θ`" of
clause (3), for the squares already treated in
`StacksFrontier/AlgebraicGeometry/Spaces/RelativeProjInvertibleMorphismPoints.lean`: `Y' = X`,
`g = f : X ⟶ Y` a scheme point of the algebraic space `Y`, a scheme `g' : X' ⟶ X` and `f' = g'`.
There `𝒜' = f^*𝒜` is `d.algebra X f`, `ψ' = g'^*ψ`, and the twists `𝒪(d)` of `Proj_Y(𝒜)` at the
point `f` are those of `Proj_X(f^*𝒜)`, as in
`AlgebraicGeometry.Space.RelativeProjPoints.invertibleTheta_clauseOne`.

## Main definitions

* `…RelativeProjInvertibleMorphism.thetaSourceIso`: `j^*r^*(⨁ 𝒪(d)) ≅ r'^*(⨁ 𝒪(d))`.
* `…RelativeProjInvertibleMorphism.thetaTargetPieceIso`,
  `…RelativeProjInvertibleMorphism.thetaTargetIso`:
  `j^*(⨁ ℒ^{⊗ d}|_{U(ψ)}) ≅ ⨁ (q^*ℒ)^{⊗ d}|_{U(ψ')}`.

## Main results

* `…RelativeProjInvertibleMorphism.thetaTargetPieceIso_hom_mul_pullbackUnit` with
  `…RelativeProjInvertibleMorphism.map_mul_of_pullbackUnit`: the target identification is
  multiplicative (it suffices to check this on pulled-back sections).
* `…RelativeProjInvertibleMorphism.theta_pullback`: **`θ' = j^*θ`** through the two
  identifications, for an arbitrary morphism of schemes `q : W ⟶ X`.
* `AlgebraicGeometry.Space.RelativeProjPoints.invertibleTheta_baseChange`: **the last sentence of
  clause (3) of [Stacks, Tag 0D2Z]**, for the squares with `Y' = X`, `g = f`, `f' = g'`.

## Clause (3) for an arbitrary scheme `Y' ⟶ Y`

Clause (3) of Tag 0D2Z is stated for an arbitrary scheme `Y'` with a morphism `g : Y' ⟶ Y` and a
scheme `X'` with `f' : X' ⟶ Y'` and `g' : X' ⟶ X` such that `g ∘ f' = f ∘ g'`.  For such squares
it needs the comparison `f'^*(g^*𝒜) ≅ (g ∘ f')^*𝒜 = (f ∘ g')^*𝒜 ≅ g'^*(f^*𝒜)` of the
restrictions of `𝒜` to two scheme points, and the compatibility of the fibre identifications of
Stacks 084B with it.  Both are read off the restriction datum of Stacks 084A
(`AlgebraicGeometry.Space.RelativeProjSituation.quadrupleRestriction`) in
`StacksFrontier/AlgebraicGeometry/Spaces/RelativeProjInvertibleBaseChange.lean`, which proves the
general case (`AlgebraicGeometry.Space.RelativeProjSituation.clauseThree_theta`) and states the
whole lemma (`AlgebraicGeometry.Space.RelativeProjSituation.tag0D2Z`).  At the point `f` itself
(the case proved here) both identifications are identities, which is why no comparison enters.

## References

* [Stacks Project, Tag 0D2Z](https://stacks.math.columbia.edu/tag/0D2Z)
* [Stacks Project, Tag 01O9](https://stacks.math.columbia.edu/tag/01O9)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 084A](https://stacks.math.columbia.edu/tag/084A)
* [Stacks Project, Tag 084B](https://stacks.math.columbia.edu/tag/084B)
* [Stacks Project, Tag 085C](https://stacks.math.columbia.edu/tag/085C)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open AlgebraicGeometry.Scheme.Modules (pullbackSection)
open Stacks.AmpleProjectiveImmersion (tensorPowerModule)
open Stacks.RingedSpace RingedSpaceModuleAdjunction
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf
open Stacks.AlgebraicGeometry.CoherentMulSections (powCompare)
open Stacks.AlgebraicGeometry.ProjChartGradedTriple (laurentOn)
open Stacks.AlgebraicGeometry.ProjChartIntPullbackMul (intPullIso)
open Stacks.TensorPowers (natTensorPow)

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.AlgebraicGeometry.ProjChartIntPullbackMul.stacksInvertible

attribute [local irreducible] GradedPowerMap.globalMorphism
  Stacks.AlgebraicGeometry.ProjChartFullGraded.GradedSections.glued

open GradedPowerMap (twD Otw psiU)

variable {S X W : Scheme.{u}} {A : SheafGradedAlgebra.{u} S} {f : X ⟶ S}
  {L : X.Modules} [Stacks.Ample.IsInvertibleModule X L]
  (ψ : Twisting f (situationAlgebra A) 1 L) (q : W ⟶ X)

/-- **`j^*r^*(⨁_d 𝒪(d)) ≅ r'^*(⨁_d 𝒪(d))`** for the restriction `j : U(q^*ψ) ⟶ U(ψ)` of `q`, as
sheaves of graded algebras: the pseudofunctoriality of the inverse image of graded algebras,
followed by the congruence along `j ≫ r_{ℒ,ψ} = r_{q^*ℒ, q^*ψ}`. -/
def thetaSourceIso :
    Stacks.Conormal.gradedPullback (coveringOpenPullback ψ q)
        (Stacks.Conormal.gradedPullback ((toGradedPowerMap ψ).globalMorphism (relativeProj A))
          (twD A).algebra) ≅
      Stacks.Conormal.gradedPullback
        ((toGradedPowerMap (ψ.pullback q)).globalMorphism (relativeProj A)) (twD A).algebra :=
  Stacks.AlgebraicGeometry.GradedAlgebraPullbackComp.pullbackGradedAlgebraCompIso
      (twD A).algebra (coveringOpenPullback ψ q)
      ((toGradedPowerMap ψ).globalMorphism (relativeProj A)) ≪≫
    Stacks.AlgebraicGeometry.GradedAlgebraPullbackComp.pullbackGradedAlgebraCongrIso
      (twD A).algebra (coveringOpenPullback_globalMorphism ψ q)

/-- **`j^*(ℒ^{⊗ n}|_{U(ψ)}) ≅ (q^*ℒ)^{⊗ n}|_{U(q^*ψ)}`**: the restriction to `U(ψ)` read as an
inverse image, the pseudofunctoriality of the inverse image along
`j ≫ ι_{U(ψ)} = ι_{U(q^*ψ)} ≫ q`, and the comparison `q^*(ℒ^{⊗ n}) ≅ (q^*ℒ)^{⊗ n}` of the
integral tensor powers of [Stacks, Tag 01CU]. -/
def thetaTargetPieceIso (n : ℤ) :
    (Scheme.Modules.pullback (coveringOpenPullback ψ q)).obj
        ((laurentOn L (toGradedPowerMap ψ).coveringOpen).piece n) ≅
      (laurentOn (toGradedPowerMap (ψ.pullback q)).L
        (toGradedPowerMap (ψ.pullback q)).coveringOpen).piece n :=
  (Scheme.Modules.pullback (coveringOpenPullback ψ q)).mapIso
      ((Scheme.Modules.restrictFunctorIsoPullback (toGradedPowerMap ψ).coveringOpen.ι).app
        (tensorPowerModule X L n))
    ≪≫ (Scheme.Modules.pullbackComp (coveringOpenPullback ψ q)
          (toGradedPowerMap ψ).coveringOpen.ι).app _
    ≪≫ (Scheme.Modules.pullbackCongr (coveringOpenPullback_ι ψ q)).app _
    ≪≫ (Scheme.Modules.pullbackComp (toGradedPowerMap (ψ.pullback q)).coveringOpen.ι q).symm.app _
    ≪≫ (Scheme.Modules.pullback (toGradedPowerMap (ψ.pullback q)).coveringOpen.ι).mapIso
          (intPullIso q L n)
    ≪≫ ((Scheme.Modules.restrictFunctorIsoPullback
          (toGradedPowerMap (ψ.pullback q)).coveringOpen.ι).app _).symm

/-- The image in `W` of an open of `U(q^*ψ)` lying over `O' ⊆ U(ψ)` lies over the image of `O'`
in `X`. -/
theorem image_le_preimage_image_coveringOpen (O' : (toGradedPowerMap ψ).coveringOpen.toScheme.Opens)
    {V : (toGradedPowerMap (ψ.pullback q)).coveringOpen.toScheme.Opens}
    (hV : V ≤ coveringOpenPullback ψ q ⁻¹ᵁ O') :
    (toGradedPowerMap (ψ.pullback q)).coveringOpen.ι ''ᵁ V
      ≤ q ⁻¹ᵁ ((toGradedPowerMap ψ).coveringOpen.ι ''ᵁ O') := by
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨(coveringOpenPullback ψ q).base x, hV hx,
    congrArg (fun h : (toGradedPowerMap (ψ.pullback q)).coveringOpen.toScheme ⟶ X => h.base x)
      (coveringOpenPullback_ι ψ q)⟩

/-- **The target identification on a pulled-back section**: it is the pullback along `q` of the
section, read in `(q^*ℒ)^{⊗ n}` and restricted to the image of the open in `W`. -/
theorem thetaTargetPieceIso_hom_pullbackSection (n : ℤ)
    (O' : (toGradedPowerMap ψ).coveringOpen.toScheme.Opens)
    (V : (toGradedPowerMap (ψ.pullback q)).coveringOpen.toScheme.Opens)
    (h4 : V ≤ coveringOpenPullback ψ q ⁻¹ᵁ O')
    (t : Γ((tensorPowerModule X L n).restrict (toGradedPowerMap ψ).coveringOpen.ι, O')) :
    (thetaTargetPieceIso ψ q n).hom.val.app (op V)
        (pullbackSection (coveringOpenPullback ψ q) _ O' V h4 t) =
      (tensorPowerModule W ((Scheme.Modules.pullback q).obj L) n).val.map
        (homOfLE (image_le_preimage_image_coveringOpen ψ q O' h4)).op
        ((intPullIso q L n).hom.val.app (op (q ⁻¹ᵁ ((toGradedPowerMap ψ).coveringOpen.ι ''ᵁ O')))
          (pullbackSection q (tensorPowerModule X L n)
            ((toGradedPowerMap ψ).coveringOpen.ι ''ᵁ O') _ le_rfl t)) :=
  tgt_hom_pullbackSection (coveringOpenPullback ψ q) (toGradedPowerMap ψ).coveringOpen.ι
    (toGradedPowerMap (ψ.pullback q)).coveringOpen.ι q (coveringOpenPullback_ι ψ q)
    (tensorPowerModule X L n) (intPullIso q L n) O' V h4 t
    (image_le_preimage_image_coveringOpen ψ q O' h4)

/-- **The target identification is multiplicative on the images of sections under the unit of
`j^* ⊣ j_*`.** -/
theorem thetaTargetPieceIso_hom_mul_pullbackUnit (i k : ℤ)
    (O' : (toGradedPowerMap ψ).coveringOpen.toScheme.Opens)
    (a : Γ((tensorPowerModule X L i).restrict (toGradedPowerMap ψ).coveringOpen.ι, O'))
    (b : Γ((tensorPowerModule X L k).restrict (toGradedPowerMap ψ).coveringOpen.ι, O')) :
    (thetaTargetPieceIso ψ q (i + k)).hom.val.app (op (coveringOpenPullback ψ q ⁻¹ᵁ O'))
        (pullbackUnit (coveringOpenPullback ψ q).toLRSHom.toShHom
          ((laurentOn L (toGradedPowerMap ψ).coveringOpen).piece (i + k)) (op O')
          (Stacks.TensorPowerDivision.localMul L a b)) =
      Stacks.TensorPowerDivision.localMul ((Scheme.Modules.pullback q).obj L)
        ((thetaTargetPieceIso ψ q i).hom.val.app (op (coveringOpenPullback ψ q ⁻¹ᵁ O'))
          (pullbackUnit (coveringOpenPullback ψ q).toLRSHom.toShHom
            ((laurentOn L (toGradedPowerMap ψ).coveringOpen).piece i) (op O') a))
        ((thetaTargetPieceIso ψ q k).hom.val.app (op (coveringOpenPullback ψ q ⁻¹ᵁ O'))
          (pullbackUnit (coveringOpenPullback ψ q).toLRSHom.toShHom
            ((laurentOn L (toGradedPowerMap ψ).coveringOpen).piece k) (op O') b)) := by
  have hV := image_le_preimage_image_coveringOpen ψ q O'
    (le_refl (coveringOpenPullback ψ q ⁻¹ᵁ O'))
  -- the target identification on each of the three sections
  have τ : ∀ (n : ℤ)
      (t : Γ((tensorPowerModule X L n).restrict (toGradedPowerMap ψ).coveringOpen.ι, O')),
      (thetaTargetPieceIso ψ q n).hom.val.app (op (coveringOpenPullback ψ q ⁻¹ᵁ O'))
          (pullbackUnit (coveringOpenPullback ψ q).toLRSHom.toShHom
            ((laurentOn L (toGradedPowerMap ψ).coveringOpen).piece n) (op O') t) =
        (tensorPowerModule W ((Scheme.Modules.pullback q).obj L) n).val.map (homOfLE hV).op
          ((intPullIso q L n).hom.val.app
            (op (q ⁻¹ᵁ ((toGradedPowerMap ψ).coveringOpen.ι ''ᵁ O')))
            (pullbackUnit q.toLRSHom.toShHom (tensorPowerModule X L n)
              (op ((toGradedPowerMap ψ).coveringOpen.ι ''ᵁ O')) t)) := fun n t =>
    ((congrArg ((thetaTargetPieceIso ψ q n).hom.val.app (op (coveringOpenPullback ψ q ⁻¹ᵁ O')))
      (Stacks.Conormal.pullbackSection_self (coveringOpenPullback ψ q)
        ((laurentOn L (toGradedPowerMap ψ).coveringOpen).piece n) O' t).symm).trans
      (thetaTargetPieceIso_hom_pullbackSection ψ q n O' _ le_rfl t)).trans
      (congrArg (fun z => (tensorPowerModule W ((Scheme.Modules.pullback q).obj L) n).val.map
        (homOfLE hV).op ((intPullIso q L n).hom.val.app
          (op (q ⁻¹ᵁ ((toGradedPowerMap ψ).coveringOpen.ι ''ᵁ O'))) z))
        (Stacks.Conormal.pullbackSection_self q (tensorPowerModule X L n)
          ((toGradedPowerMap ψ).coveringOpen.ι ''ᵁ O') t))
  refine (τ (i + k) _).trans ?_
  refine Eq.trans ?_ (congrArg₂ (Stacks.TensorPowerDivision.localMul
    ((Scheme.Modules.pullback q).obj L)) (τ i a).symm (τ k b).symm)
  refine (congrArg ((tensorPowerModule W ((Scheme.Modules.pullback q).obj L) (i + k)).val.map
    (homOfLE hV).op)
    (Stacks.AlgebraicGeometry.ProjChartRatioPullbackLocalMul.pullbackIntPowIso_pullbackUnit_localMul
      q L i k _ a b)).trans ?_
  exact Stacks.TensorPowerDivision.map_localMul _ (homOfLE hV) _ _

section Generic

variable {Y₁ Y₂ : RingedSpace.{u, u}} (g : Y₁ ⟶ Y₂)

/-- **A degreewise family out of the inverse image of a sheaf of graded algebras is multiplicative
as soon as it is on the images of local sections under the unit of `g^* ⊣ g_*`.** -/
theorem map_mul_of_pullbackUnit
    {A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf Y₂)}
    {B : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf Y₁)}
    (e : ∀ n : ℤ, (pullbackFunctor g).obj (A.piece n) ⟶ B.piece n) (i k : ℤ)
    (h : ∀ (V : Opens Y₂.carrier) (a : (A.piece i).val.obj (op V))
      (b : (A.piece k).val.obj (op V)),
      (e (i + k)).val.app (op ((opensMap g).obj V))
          (pullbackUnit g (A.piece (i + k)) (op V) ((A.mul i k).app (op V) a b)) =
        (B.mul i k).app (op ((opensMap g).obj V))
          ((e i).val.app (op ((opensMap g).obj V)) (pullbackUnit g (A.piece i) (op V) a))
          ((e k).val.app (op ((opensMap g).obj V)) (pullbackUnit g (A.piece k) (op V) b)))
    (U : (Opens Y₁.carrier)ᵒᵖ) (x : ((pullbackGradedAlgebra g A).piece i).val.obj U)
    (y : ((pullbackGradedAlgebra g A).piece k).val.obj U) :
    (e (i + k)).val.app U (((pullbackGradedAlgebra g A).mul i k).app U x y) =
      (B.mul i k).app U ((e i).val.app U x) ((e k).val.app U y) := by
  obtain ⟨U⟩ := U
  refine pullbackBilinear_ext g
    (bilinPostcomp ((pullbackGradedAlgebra g A).mul i k) (e (i + k)))
    (((B.mul i k).compLeft (e i).val).compRight (e k).val) (fun V a b => ?_) U x y
  change (e (i + k)).val.app (op ((opensMap g).obj V))
      (((pullbackGradedAlgebra g A).mul i k).app (op ((opensMap g).obj V))
        (pullbackUnit g (A.piece i) (op V) a) (pullbackUnit g (A.piece k) (op V) b)) =
    (B.mul i k).app (op ((opensMap g).obj V))
      ((e i).val.app (op ((opensMap g).obj V)) (pullbackUnit g (A.piece i) (op V) a))
      ((e k).val.app (op ((opensMap g).obj V)) (pullbackUnit g (A.piece k) (op V) b))
  rw [pullbackGradedAlgebra_mul_pullbackUnit]
  exact h V a b

end Generic

/-- **`j^*(⨁_d ℒ^{⊗ d}|_{U(ψ)}) ≅ ⨁_d (q^*ℒ)^{⊗ d}|_{U(q^*ψ)}`** as sheaves of graded algebras:
degreewise `thetaTargetPieceIso`, which is multiplicative because the comparison of the integral
tensor powers is ([Stacks, Tag 01CU]). -/
def thetaTargetIso :
    Stacks.Conormal.gradedPullback (coveringOpenPullback ψ q)
        (laurentOn L (toGradedPowerMap ψ).coveringOpen) ≅
      laurentOn (toGradedPowerMap (ψ.pullback q)).L
        (toGradedPowerMap (ψ.pullback q)).coveringOpen :=
  SheafOfModules.GradedAlgebra.isoOfPieceIso
    (A := Stacks.Conormal.gradedPullback (coveringOpenPullback ψ q)
      (laurentOn L (toGradedPowerMap ψ).coveringOpen))
    (B := laurentOn (toGradedPowerMap (ψ.pullback q)).L
      (toGradedPowerMap (ψ.pullback q)).coveringOpen)
    (fun n => thetaTargetPieceIso ψ q n)
    (fun i k U x y => map_mul_of_pullbackUnit (coveringOpenPullback ψ q).toLRSHom.toShHom
      (A := laurentOn L (toGradedPowerMap ψ).coveringOpen)
      (B := laurentOn (toGradedPowerMap (ψ.pullback q)).L
        (toGradedPowerMap (ψ.pullback q)).coveringOpen)
      (fun n => (thetaTargetPieceIso ψ q n).hom) i k
      (fun V a b => thetaTargetPieceIso_hom_mul_pullbackUnit ψ q i k V a b) U x y)

/-- `r'^{-1}(π^{-1}(V)) ⊆ j^{-1}(r^{-1}(π^{-1}(V)))`. -/
theorem preimage_globalMorphism_pullback_le (V : S.Opens) :
    (toGradedPowerMap (ψ.pullback q)).globalMorphism (relativeProj A) ⁻¹ᵁ
        ((relativeProj A).toBase ⁻¹ᵁ V) ≤
      coveringOpenPullback ψ q ⁻¹ᵁ ((toGradedPowerMap ψ).globalMorphism (relativeProj A) ⁻¹ᵁ
        ((relativeProj A).toBase ⁻¹ᵁ V)) := by
  have h' : (toGradedPowerMap (ψ.pullback q)).globalMorphism (relativeProj A) ⁻¹ᵁ
      ((relativeProj A).toBase ⁻¹ᵁ V) ≤
      (coveringOpenPullback ψ q ≫ (toGradedPowerMap ψ).globalMorphism (relativeProj A)) ⁻¹ᵁ
        ((relativeProj A).toBase ⁻¹ᵁ V) := by
    rw [coveringOpenPullback_globalMorphism]
  exact h'

/-- `q^{-1}` of the image in `X` of `r^{-1}(π^{-1}(V))` lies in `q^{-1}(f^{-1}(V))`. -/
theorem preimage_image_preimage_le (V : S.Opens) :
    q ⁻¹ᵁ ((toGradedPowerMap ψ).coveringOpen.ι ''ᵁ
        ((toGradedPowerMap ψ).globalMorphism (relativeProj A) ⁻¹ᵁ
          ((relativeProj A).toBase ⁻¹ᵁ V))) ≤
      q ⁻¹ᵁ (f ⁻¹ᵁ V) :=
  q.preimage_mono ((toGradedPowerMap ψ).image_preimage_preimage_le V)

/-- **`thetaSourceIso⁻¹ ≫ j^*θ ≫ thetaTargetIso` on a pulled-back homogeneous section**: the
pullback along `r'` of the section `ψ_{Proj}(a)` of `𝒪(d)` is carried to the pullback along `q` of
`ψ(a) ∈ Γ(f^{-1}(V), ℒ^{⊗ d})`, read in `(q^*ℒ)^{⊗ d}` and restricted. -/
theorem thetaPullback_app_pullbackUnit (V : S.Opens) (d : ℕ) (a : Γ(A.piece (d : ℤ), V)) :
    (thetaTargetPieceIso ψ q d).hom.val.app
      (op ((toGradedPowerMap (ψ.pullback q)).globalMorphism (relativeProj A) ⁻¹ᵁ
        ((relativeProj A).toBase ⁻¹ᵁ V)))
      (((Scheme.Modules.pullback (coveringOpenPullback ψ q)).map
        (X := (Scheme.Modules.pullback
          ((toGradedPowerMap ψ).globalMorphism (relativeProj A))).obj (Otw A d))
        (Y := (laurentOn L (toGradedPowerMap ψ).coveringOpen).piece d)
        ((toGradedPowerMap ψ).theta.app d)).val.app
        (op ((toGradedPowerMap (ψ.pullback q)).globalMorphism (relativeProj A) ⁻¹ᵁ
          ((relativeProj A).toBase ⁻¹ᵁ V)))
        (((Scheme.Modules.pullbackComp (coveringOpenPullback ψ q)
        ((toGradedPowerMap ψ).globalMorphism (relativeProj A))).inv.app (Otw A d)).val.app
          (op ((toGradedPowerMap (ψ.pullback q)).globalMorphism (relativeProj A) ⁻¹ᵁ
            ((relativeProj A).toBase ⁻¹ᵁ V)))
          (((Scheme.Modules.pullbackCongr (coveringOpenPullback_globalMorphism ψ q)).inv.app
            (Otw A d)).val.app
            (op ((toGradedPowerMap (ψ.pullback q)).globalMorphism (relativeProj A) ⁻¹ᵁ
              ((relativeProj A).toBase ⁻¹ᵁ V)))
            (pullbackUnit
              ((toGradedPowerMap (ψ.pullback q)).globalMorphism (relativeProj A)).toLRSHom.toShHom
              (Otw A d) (op ((relativeProj A).toBase ⁻¹ᵁ V)) (psiU A d V a))))) =
      (tensorPowerModule W ((Scheme.Modules.pullback q).obj L) d).val.map
        (homOfLE (image_le_preimage_image_coveringOpen ψ q _
          (preimage_globalMorphism_pullback_le ψ q V))).op
        ((tensorPowerModule W ((Scheme.Modules.pullback q).obj L) d).val.map
          (homOfLE (preimage_image_preimage_le ψ q V)).op
          ((intPullIso q L d).hom.val.app (op (q ⁻¹ᵁ (f ⁻¹ᵁ V)))
        (pullbackUnit q.toLRSHom.toShHom (tensorPowerModule X L d) (op (f ⁻¹ᵁ V))
          ((powCompare L d).hom.app (f ⁻¹ᵁ V) (valueSec ψ d V a))))) := by
  have hr := coveringOpenPullback_globalMorphism ψ q
  have h4 := preimage_globalMorphism_pullback_le ψ q V
  have h0 := (toGradedPowerMap ψ).image_preimage_preimage_le V
  have h6 := preimage_image_preimage_le ψ q V
  have s1 : (pullbackUnit
      ((toGradedPowerMap (ψ.pullback q)).globalMorphism (relativeProj A)).toLRSHom.toShHom
      (Otw A d) (op ((relativeProj A).toBase ⁻¹ᵁ V)) (psiU A d V a)) =
      pullbackSection ((toGradedPowerMap (ψ.pullback q)).globalMorphism (relativeProj A))
        (Otw A d) ((relativeProj A).toBase ⁻¹ᵁ V) _ le_rfl (psiU A d V a) :=
    (Stacks.Conormal.pullbackSection_self
      ((toGradedPowerMap (ψ.pullback q)).globalMorphism (relativeProj A)) (Otw A d)
      ((relativeProj A).toBase ⁻¹ᵁ V) (psiU A d V a)).symm
  have s2 := pullbackSection_congr_inv hr (Otw A d) ((relativeProj A).toBase ⁻¹ᵁ V) _ h4 le_rfl
    (psiU A d V a)
  have s3 := Stacks.AlgebraicGeometry.ModuleLimits.pullbackComp_inv_val_app_pullbackSection
    (coveringOpenPullback ψ q) ((toGradedPowerMap ψ).globalMorphism (relativeProj A)) (Otw A d)
    ((relativeProj A).toBase ⁻¹ᵁ V) _ _ le_rfl h4 h4 (psiU A d V a)
  have s4 := Scheme.Modules.pullbackSection_naturality (coveringOpenPullback ψ q)
    (F := (Scheme.Modules.pullback
      ((toGradedPowerMap ψ).globalMorphism (relativeProj A))).obj (Otw A d))
    (G := (laurentOn L (toGradedPowerMap ψ).coveringOpen).piece d)
    ((toGradedPowerMap ψ).theta.app d) _ _ h4
    (pullbackSection ((toGradedPowerMap ψ).globalMorphism (relativeProj A)) (Otw A d)
      ((relativeProj A).toBase ⁻¹ᵁ V) _ le_rfl (psiU A d V a))
  have s5 := (toGradedPowerMap ψ).theta_app_pullbackSection d ((relativeProj A).toBase ⁻¹ᵁ V)
    (psiU A d V a)
  have s6 := ((toGradedPowerMap ψ).thetaPush_psiU V d a).trans
    (congrArg (fun z => (tensorPowerModule X L d).presheaf.map (homOfLE h0).op
      ((powCompare L d).hom.app (f ⁻¹ᵁ V) z)) (toGradedPowerMap_value ψ d V a))
  have s7 := thetaTargetPieceIso_hom_pullbackSection ψ q d _ _ h4
    ((tensorPowerModule X L d).presheaf.map (homOfLE h0).op
      ((powCompare L d).hom.app (f ⁻¹ᵁ V) (valueSec ψ d V a)))
  have s8 : pullbackSection q (tensorPowerModule X L d)
      ((toGradedPowerMap ψ).coveringOpen.ι ''ᵁ
        ((toGradedPowerMap ψ).globalMorphism (relativeProj A) ⁻¹ᵁ
          ((relativeProj A).toBase ⁻¹ᵁ V))) _ le_rfl
      ((tensorPowerModule X L d).presheaf.map (homOfLE h0).op
        ((powCompare L d).hom.app (f ⁻¹ᵁ V) (valueSec ψ d V a))) =
      pullbackSection q (tensorPowerModule X L d) (f ⁻¹ᵁ V) _ h6
        ((powCompare L d).hom.app (f ⁻¹ᵁ V) (valueSec ψ d V a)) :=
    pullbackSectionHom_map q (tensorPowerModule X L d) (f ⁻¹ᵁ V) _ h0 _ le_rfl h6 _
  have s9 := PresheafOfModules.naturality_apply (intPullIso q L d).hom.val (homOfLE h6).op
    (pullbackUnit q.toLRSHom.toShHom (tensorPowerModule X L d) (op (f ⁻¹ᵁ V))
      ((powCompare L d).hom.app (f ⁻¹ᵁ V) (valueSec ψ d V a)))
  simp only [s1, s2, s3, s4]
  refine (congrArg (fun z => (thetaTargetPieceIso ψ q d).hom.val.app
      (op ((toGradedPowerMap (ψ.pullback q)).globalMorphism (relativeProj A) ⁻¹ᵁ
        ((relativeProj A).toBase ⁻¹ᵁ V)))
    (pullbackSection (coveringOpenPullback ψ q) _ _ _ h4 z)) (s5.trans s6)).trans ?_
  refine s7.trans ?_
  simp only [s8]
  exact congrArg _ s9

/-- **The value of `q^*ψ`, read in `(q^*ℒ)^{⊗ d}`, is the pullback along `q` of the value of
`ψ`.** -/
theorem powCompare_value_pullback (V : S.Opens) (d : ℕ) (a : Γ(A.piece (d : ℤ), V)) :
    (powCompare (toGradedPowerMap (ψ.pullback q)).L d).hom.app ((q ≫ f) ⁻¹ᵁ V)
        ((toGradedPowerMap (ψ.pullback q)).value d V a) =
      ((intPullIso q L d).hom.val.app (op (q ⁻¹ᵁ (f ⁻¹ᵁ V)))
        (pullbackUnit q.toLRSHom.toShHom (tensorPowerModule X L d) (op (f ⁻¹ᵁ V))
          ((powCompare L d).hom.app (f ⁻¹ᵁ V) (valueSec ψ d V a)))) := by
  have hv := (toGradedPowerMap_value (ψ.pullback q) d V a).trans
    ((valueSec_pullback ψ q d V a).trans
      (pullPowSection_eq_powTransport q L d (f ⁻¹ᵁ V) (valueSec ψ d V a)))
  refine (congrArg ((powCompare (toGradedPowerMap (ψ.pullback q)).L d).hom.app
    ((q ≫ f) ⁻¹ᵁ V)) hv).trans ?_
  have hT : (powTransport q L d).hom.app (q ⁻¹ᵁ (f ⁻¹ᵁ V))
      (pullbackUnit q.toLRSHom.toShHom (natTensorPow L d : X.Modules) (op (f ⁻¹ᵁ V))
        (valueSec ψ d V a)) =
      (powCompare ((Scheme.Modules.pullback q).obj L) d).inv.app (q ⁻¹ᵁ (f ⁻¹ᵁ V))
        ((intPullIso q L d).hom.val.app (op (q ⁻¹ᵁ (f ⁻¹ᵁ V)))
          (((Scheme.Modules.pullback q).map (powCompare L d).hom).val.app
            (op (q ⁻¹ᵁ (f ⁻¹ᵁ V)))
            (pullbackUnit q.toLRSHom.toShHom (natTensorPow L d : X.Modules) (op (f ⁻¹ᵁ V))
              (valueSec ψ d V a)))) := rfl
  refine (congrArg ((powCompare ((Scheme.Modules.pullback q).obj L) d).hom.app
    (q ⁻¹ᵁ (f ⁻¹ᵁ V))) hT).trans ?_
  refine (Stacks.AlgebraicGeometry.ProjChartRatioPullbackLocalMul.hom_app_inv_app _ _ _).trans ?_
  exact congrArg ((intPullIso q L d).hom.val.app (op (q ⁻¹ᵁ (f ⁻¹ᵁ V))))
    (pullbackUnit_naturality q.toLRSHom.toShHom (powCompare L d).hom (op (f ⁻¹ᵁ V))
      (valueSec ψ d V a))

/-- The degree-`d` component of `thetaSourceIso⁻¹ ≫ j^*θ ≫ thetaTargetIso`. -/
theorem thetaPullback_app (d : ℤ) :
    (((thetaSourceIso ψ q).inv ≫
        pullbackGradedAlgebraMap (coveringOpenPullback ψ q).toLRSHom.toShHom
          (toGradedPowerMap ψ).theta ≫ (thetaTargetIso ψ q).hom :
        Stacks.Conormal.gradedPullback
          ((toGradedPowerMap (ψ.pullback q)).globalMorphism (relativeProj A)) (twD A).algebra ⟶
        laurentOn (toGradedPowerMap (ψ.pullback q)).L
          (toGradedPowerMap (ψ.pullback q)).coveringOpen).app d) =
      (((Scheme.Modules.pullbackCongr (coveringOpenPullback_globalMorphism ψ q)).inv.app
          (Otw A d)) ≫
        ((Scheme.Modules.pullbackComp (coveringOpenPullback ψ q)
          ((toGradedPowerMap ψ).globalMorphism (relativeProj A))).inv.app (Otw A d))) ≫
        ((Scheme.Modules.pullback (coveringOpenPullback ψ q)).map
          (X := (Scheme.Modules.pullback
            ((toGradedPowerMap ψ).globalMorphism (relativeProj A))).obj (Otw A d))
          (Y := (laurentOn L (toGradedPowerMap ψ).coveringOpen).piece d)
          ((toGradedPowerMap ψ).theta.app d)) ≫ (thetaTargetPieceIso ψ q d).hom := by
  simp only [thetaSourceIso, thetaTargetIso,
    Stacks.AlgebraicGeometry.GradedAlgebraPullbackComp.pullbackGradedAlgebraCongrIso,
    SheafOfModules.GradedAlgebra.categoryStruct_comp_app]
  rfl

attribute [local irreducible] thetaTargetPieceIso

/-- `thetaSourceIso⁻¹ ≫ j^*θ ≫ thetaTargetIso` in degree `d`, on a pulled-back section, as the
four factors applied in turn. -/
theorem thetaPullback_comp_apply (V : S.Opens) (d : ℕ) (a : Γ(A.piece (d : ℤ), V)) :
    ((((Scheme.Modules.pullbackCongr (coveringOpenPullback_globalMorphism ψ q)).inv.app
        (Otw A d)) ≫
      ((Scheme.Modules.pullbackComp (coveringOpenPullback ψ q)
        ((toGradedPowerMap ψ).globalMorphism (relativeProj A))).inv.app (Otw A d))) ≫
      ((Scheme.Modules.pullback (coveringOpenPullback ψ q)).map
        (X := (Scheme.Modules.pullback
          ((toGradedPowerMap ψ).globalMorphism (relativeProj A))).obj (Otw A d))
        (Y := (laurentOn L (toGradedPowerMap ψ).coveringOpen).piece d)
        ((toGradedPowerMap ψ).theta.app d)) ≫ (thetaTargetPieceIso ψ q d).hom).val.app
        (op ((toGradedPowerMap (ψ.pullback q)).globalMorphism (relativeProj A) ⁻¹ᵁ
          ((relativeProj A).toBase ⁻¹ᵁ V)))
        (pullbackUnit
          ((toGradedPowerMap (ψ.pullback q)).globalMorphism (relativeProj A)).toLRSHom.toShHom
          (Otw A d) (op ((relativeProj A).toBase ⁻¹ᵁ V)) (psiU A d V a)) =
      (thetaTargetPieceIso ψ q d).hom.val.app
        (op ((toGradedPowerMap (ψ.pullback q)).globalMorphism (relativeProj A) ⁻¹ᵁ
          ((relativeProj A).toBase ⁻¹ᵁ V)))
        (((Scheme.Modules.pullback (coveringOpenPullback ψ q)).map
          (X := (Scheme.Modules.pullback
            ((toGradedPowerMap ψ).globalMorphism (relativeProj A))).obj (Otw A d))
          (Y := (laurentOn L (toGradedPowerMap ψ).coveringOpen).piece d)
          ((toGradedPowerMap ψ).theta.app d)).val.app
          (op ((toGradedPowerMap (ψ.pullback q)).globalMorphism (relativeProj A) ⁻¹ᵁ
            ((relativeProj A).toBase ⁻¹ᵁ V)))
          (((Scheme.Modules.pullbackComp (coveringOpenPullback ψ q)
            ((toGradedPowerMap ψ).globalMorphism (relativeProj A))).inv.app (Otw A d)).val.app
            (op ((toGradedPowerMap (ψ.pullback q)).globalMorphism (relativeProj A) ⁻¹ᵁ
              ((relativeProj A).toBase ⁻¹ᵁ V)))
            (((Scheme.Modules.pullbackCongr (coveringOpenPullback_globalMorphism ψ q)).inv.app
              (Otw A d)).val.app
              (op ((toGradedPowerMap (ψ.pullback q)).globalMorphism (relativeProj A) ⁻¹ᵁ
                ((relativeProj A).toBase ⁻¹ᵁ V)))
            (pullbackUnit
              ((toGradedPowerMap (ψ.pullback q)).globalMorphism (relativeProj A)).toLRSHom.toShHom
              (Otw A d) (op ((relativeProj A).toBase ⁻¹ᵁ V)) (psiU A d V a))))) := rfl

/-- **`θ'` is the pullback of `θ`.**  For a morphism of schemes `q : W ⟶ X`, the map
`θ' : r'^*(⨁_d 𝒪(d)) ⟶ ⨁_d (q^*ℒ)^{⊗ d}|_{U(q^*ψ)}` of [Stacks, Tag 01O9] for `q^*ψ` is the
inverse image `j^*θ` of the map `θ` for `ψ` along the restriction `j : U(q^*ψ) ⟶ U(ψ)` of `q`,
read through the canonical identifications `thetaSourceIso` and `thetaTargetIso` of its source
and target. -/
theorem theta_pullback :
    (toGradedPowerMap (ψ.pullback q)).theta =
      (thetaSourceIso ψ q).inv ≫
        pullbackGradedAlgebraMap (coveringOpenPullback ψ q).toLRSHom.toShHom
          (toGradedPowerMap ψ).theta ≫ (thetaTargetIso ψ q).hom := by
  refine ((toGradedPowerMap (ψ.pullback q)).eq_theta_of_clauseOne fun V d a => ?_).symm
  rw [thetaPullback_app]
  have m1 := thetaPullback_comp_apply ψ q V d a
  have m2 := thetaPullback_app_pullbackUnit ψ q V d a
  have k := m1.trans m2
  refine (congrArg (((toGradedPowerMap (ψ.pullback q)).powK d).presheaf.map
    (eqToHom ((toGradedPowerMap (ψ.pullback q)).toBase_preimage_eq V)).op) k).trans ?_
  refine Eq.trans ?_ (congrArg ((tensorPowerModule W (toGradedPowerMap (ψ.pullback q)).L
    d).presheaf.map (homOfLE ((toGradedPowerMap (ψ.pullback q)).coveringOpen.ι.image_preimage_le
      ((q ≫ f) ⁻¹ᵁ V))).op) (powCompare_value_pullback ψ q V d a)).symm
  exact map_map3 (tensorPowerModule W (toGradedPowerMap (ψ.pullback q)).L d)
    (homOfLE (preimage_image_preimage_le ψ q V)).op
    (homOfLE (image_le_preimage_image_coveringOpen ψ q _
      (preimage_globalMorphism_pullback_le ψ q V))).op
    ((toGradedPowerMap (ψ.pullback q)).coveringOpen.ι.opensFunctor.map
      (eqToHom ((toGradedPowerMap (ψ.pullback q)).toBase_preimage_eq V))).op
    (homOfLE ((toGradedPowerMap (ψ.pullback q)).coveringOpen.ι.image_preimage_le
      ((q ≫ f) ⁻¹ᵁ V))).op ((intPullIso q L d).hom.val.app (op (q ⁻¹ᵁ (f ⁻¹ᵁ V)))
        (pullbackUnit q.toLRSHom.toShHom (tensorPowerModule X L d) (op (f ⁻¹ᵁ V))
          ((powCompare L d).hom.app (f ⁻¹ᵁ V) (valueSec ψ d V a))))

end Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism

namespace AlgebraicGeometry.Space.RelativeProjPoints

open Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {Y Proj : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {π : Proj ⟶ Y}
    (d : RelativeProjPoints B S hS π) {X : BigFppfOver B S hS} {f : yoneda.obj X ⟶ Y}
    {L : ((BigFppfOver.toScheme B S hS).obj X).Modules}
    [Stacks.Ample.IsInvertibleModule _ L]
    (ψ : Twisting (𝟙 ((BigFppfOver.toScheme B S hS).obj X)) (situationAlgebra (d.algebra X f)) 1 L)

/-- **The last sentence of clause (3) of [Stacks, Tag 0D2Z]: `θ'` is the pullback of `θ`**, for
the squares in which `Y' ⟶ Y` is the scheme point `f : X ⟶ Y`.  Consider the square with
`Y' = X`, `g = f`, a scheme `g' : X' ⟶ X` and `f' = g'`, so that `𝒜' = f^*𝒜` (the algebra
`d.algebra X f` of the presentation of `Proj_Y(𝒜)` at `f`), `ℒ' = g'^*ℒ` and `ψ' = g'^*ψ`; at the
point `f` the twists `𝒪(d)` of `Proj_Y(𝒜)` are those of `Proj_X(f^*𝒜)`, as in
`invertibleTheta_clauseOne`.  Then the map
`θ' : r_{ℒ',ψ'}^*(⨁_d 𝒪(d)) ⟶ ⨁_d (ℒ')^{⊗ d}|_{U(ψ')}` is the inverse image of
`θ : r_{ℒ,ψ}^*(⨁_d 𝒪(d)) ⟶ ⨁_d ℒ^{⊗ d}|_{U(ψ)}` along the restriction
`j : U(ψ') = g'^{-1}(U(ψ)) ⟶ U(ψ)` of `g'`, read through the canonical identifications
`j^*r_{ℒ,ψ}^*(⨁ 𝒪(d)) ≅ r_{ℒ',ψ'}^*(⨁ 𝒪(d))` (pseudofunctoriality of the inverse image, along
`j ≫ r_{ℒ,ψ} = r_{ℒ',ψ'}`, which is `invertibleMorphism_baseChange`) and
`j^*(⨁ ℒ^{⊗ d}|_{U(ψ)}) ≅ ⨁ (g'^*ℒ)^{⊗ d}|_{U(ψ')}` of sheaves of graded algebras. -/
@[stacks 0D2Z "variant: clause (3), last sentence, for the squares in which \
Y' -> Y is the scheme point f : X -> Y; the tag is AlgebraicGeometry.Space.RelativeProjSituation.tag0D2Z"]
theorem invertibleTheta_baseChange {X' : BigFppfOver B S hS} (g' : X' ⟶ X) :
    (toGradedPowerMap (ψ.pullback ((BigFppfOver.toScheme B S hS).map g'))).theta =
      (thetaSourceIso ψ ((BigFppfOver.toScheme B S hS).map g')).inv ≫
        pullbackGradedAlgebraMap
          (coveringOpenPullback ψ ((BigFppfOver.toScheme B S hS).map g')).toLRSHom.toShHom
          (toGradedPowerMap ψ).theta ≫
        (thetaTargetIso ψ ((BigFppfOver.toScheme B S hS).map g')).hom :=
  theta_pullback ψ ((BigFppfOver.toScheme B S hS).map g')

end AlgebraicGeometry.Space.RelativeProjPoints

end
