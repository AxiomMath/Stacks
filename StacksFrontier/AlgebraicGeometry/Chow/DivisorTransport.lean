module

public import StacksFrontier.AlgebraicGeometry.Chow.DivisorTransport.PrincipalCycle
public import StacksFrontier.AlgebraicGeometry.Chow.GysinConstruction.IntegralComponent
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardChow.Reduction

/-!
# Proper pushforward of a principal divisor along a closed immersion

Let `p : X ⟶ Y` be a closed immersion of schemes over the base of a Chow situation. For an
integral closed subscheme `V ⊆ X` of delta-dimension `k + 1` and a nonzero rational function `g`
on `V`, the proper pushforward of `div(g)` along `p` is the principal divisor of the transport of
`g` to the scheme-theoretic image `V.map p`, which is isomorphic to `V`. Consequently proper
pushforward along a closed immersion factors through rational equivalence.

## Main definitions

* `Stacks.Chow.imageIsoOfIsClosedImmersion`: for a closed immersion `p`, the isomorphism between a
  closed subscheme `V` and its scheme-theoretic image `V.map p`.

## Main results

* `Stacks.Chow.algebraicCycle_map_comp_relativeDimension`: the weighted pushforward of cycles,
  with relative-dimension weights, is functorial for composable proper morphisms over the base.
* `Stacks.Chow.properPushforwardKillsPrincipalDivisor_of_isClosedImmersion`: along a closed
  immersion, the proper pushforward of a principal divisor on an integral closed subscheme is the
  principal divisor of a rational function on its scheme-theoretic image.
* `Stacks.Chow.properPushforwardFactorsThroughRationalEquivalence_of_isClosedImmersion`: proper
  pushforward along a closed immersion factors through rational equivalence.

## References

* [Stacks Project, Tag 02S2](https://stacks.math.columbia.edu/tag/02S2)
* [Stacks Project, Tag 02RT](https://stacks.math.columbia.edu/tag/02RT)
* [Stacks Project, Tag 02R5](https://stacks.math.columbia.edu/tag/02R5)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### Functoriality of the weighted pushforward on a single cycle -/

/-- For proper morphisms `f : X ⟶ Y` and `g : Y ⟶ Z` over the base, pushing a cycle on `X`
forward along `f` and then along `g`, with the relative-dimension weights, agrees with pushing it
forward along `f ≫ g`. -/
theorem algebraicCycle_map_comp_relativeDimension (C : ChowSituation.{u}) {X Y Z : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
    (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ] (f : X ⟶ Y) [IsProper f] (g : Y ⟶ Z) [IsProper g]
    (hf : f ≫ sY = sX) (hg : g ≫ sZ = sY) (c : AlgebraicCycle X ℤ) :
    AlgebraicCycle.map g (relativeDimension C.dimensionFunction sY)
        (relativeDimension C.dimensionFunction sZ)
        (AlgebraicCycle.map f (relativeDimension C.dimensionFunction sX)
          (relativeDimension C.dimensionFunction sY) c) =
      AlgebraicCycle.map (f ≫ g) (relativeDimension C.dimensionFunction sX)
        (relativeDimension C.dimensionFunction sZ) c := by
  refine Function.locallyFinsuppWithin.ext fun z ↦ ?_
  set wx : X → ℤ := relativeDimension C.dimensionFunction sX
  set wy : Y → ℤ := relativeDimension C.dimensionFunction sY
  set wz : Z → ℤ := relativeDimension C.dimensionFunction sZ
  set wf : X → ℤ := fun x ↦ if wx x = wy (f.base x) then (f.residueDegree x : ℤ) else 0 with hwf
  set wg' : Y → ℤ := fun y ↦ if wy y = wz (g.base y) then (g.residueDegree y : ℤ) else 0
    with hwg'
  set wfg : X → ℤ :=
    fun x ↦ if wx x = wz (g.base (f.base x)) then ((f ≫ g).residueDegree x : ℤ) else 0 with hwfg
  have hmapf : AlgebraicCycle.map f wx wy c =
      Function.locallyFinsupp.map f.base wf f.isSpectralMap c := by
    ext y
    simp [AlgebraicCycle.map, AlgebraicCycle.mapCoeff, hwf]
  have hmapg : AlgebraicCycle.map g wy wz =
      Function.locallyFinsupp.map g.base wg' g.isSpectralMap := by
    funext d
    ext z'
    simp [AlgebraicCycle.map, AlgebraicCycle.mapCoeff, hwg']
  have hmapfg : AlgebraicCycle.map (f ≫ g) wx wz c =
      Function.locallyFinsupp.map (g.base ∘ f.base) wfg
        (g.isSpectralMap.comp f.isSpectralMap) c := by
    ext z'
    refine finsum_mem_congr rfl fun x _ ↦ ?_
    by_cases hdim : wx x = wz (g.base (f.base x)) <;>
      simp [AlgebraicCycle.mapCoeff, hwfg, hdim]
  show AlgebraicCycle.map g wy wz (AlgebraicCycle.map f wx wy c) z =
    AlgebraicCycle.map (f ≫ g) wx wz c z
  rw [hmapf, hmapg, hmapfg]
  exact congrArg (fun d : AlgebraicCycle Z ℤ ↦ d z)
    (locallyFinsupp_map_comp_of_weight_mul f g c wf wg' wfg
      (properPushforward_weight_comp C sX sY sZ f g hf hg))

/-- Equal morphisms induce the same weighted pushforward of cycles. -/
theorem algebraicCycle_map_congr {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) [QuasiCompact f]
    [QuasiCompact g] (wx : X → ℤ) (wy : Y → ℤ) (c : AlgebraicCycle X ℤ) :
    AlgebraicCycle.map f wx wy c = AlgebraicCycle.map g wx wy c := by
  subst h
  rfl

/-! ### Transporting the relative dimension and the delta-dimension along an isomorphism -/

/-- The relative dimension over the base is an isomorphism invariant: for an isomorphism
`φ : V ≅ W` of schemes over `S`, the relative dimension of `φ z` equals that of `z`. -/
theorem relativeDimension_of_iso {S V W : Scheme.{u}} (δ : DimensionFunction S) (sV : V ⟶ S)
    (sW : W ⟶ S) (φ : V ≅ W) (h : φ.hom ≫ sW = sV) (z : V) :
    relativeDimension δ sW (φ.hom.base z) = relativeDimension δ sV z := by
  rw [← relativeDimension_comp_closedImmersion δ φ.hom sW z, h]

/-- The delta-dimension of Stacks 02QP is an isomorphism invariant: isomorphic irreducible
schemes over the base have the same delta-dimension. -/
theorem schemeDeltaDimension_of_iso (C : ChowSituation.{u}) {V W : Scheme.{u}} (sV : V ⟶ C.S)
    [LocallyOfFiniteType sV] (sW : W ⟶ C.S) [LocallyOfFiniteType sW] [IrreducibleSpace V]
    [IrreducibleSpace W] (φ : V ≅ W) (h : φ.hom ≫ sW = sV) :
    schemeDeltaDimension C sW = schemeDeltaDimension C sV := by
  rw [schemeDeltaDimension_eq_genericPoint C sW, schemeDeltaDimension_eq_genericPoint C sV,
    ← genericPoint_eq_of_isOpenImmersion φ.hom, relativeDimension_of_iso C.dimensionFunction sV sW φ
        h]

/-! ### The scheme-theoretic image of a closed subscheme under a closed immersion -/

variable {X Y : Scheme.{u}} (p : X ⟶ Y) [IsClosedImmersion p]

/-- For a closed immersion `p`, the closed subscheme `V ⊆ X` is isomorphic to its
scheme-theoretic image `V.map p ⊆ Y`. -/
def imageIsoOfIsClosedImmersion (V : X.IdealSheafData) : V.subscheme ≅ (V.map p).subscheme :=
  show V.subscheme ≅ (V.subschemeι ≫ p).image from asIso (V.subschemeι ≫ p).toImage

/-- The isomorphism of `Stacks.Chow.imageIsoOfIsClosedImmersion` factors `V.subschemeι ≫ p`
through the closed immersion of the scheme-theoretic image. -/
@[simp]
theorem imageIsoOfIsClosedImmersion_hom_subschemeι (V : X.IdealSheafData) :
    (imageIsoOfIsClosedImmersion p V).hom ≫ (V.map p).subschemeι = V.subschemeι ≫ p :=
  (V.subschemeι ≫ p).toImage_imageι

/-- The scheme-theoretic image under a closed immersion of an integral closed subscheme is
integral. -/
theorem isIntegral_subscheme_map (V : X.IdealSheafData) (hV : IsIntegral V.subscheme) :
    IsIntegral (V.map p).subscheme := by
  have : Nonempty (V.map p).subscheme :=
    ⟨(imageIsoOfIsClosedImmersion p V).hom.base (Nonempty.some inferInstance)⟩
  exact isIntegral_of_isOpenImmersion (imageIsoOfIsClosedImmersion p V).inv

/-! ### Stacks 02S2 for a closed immersion -/

/-- Along a closed immersion `p : X ⟶ Y` over the base, the proper pushforward of the principal
divisor of a nonzero rational function `g` on an integral closed subscheme `V ⊆ X` of
delta-dimension `k + 1` is the principal divisor of the transported rational function on the
scheme-theoretic image `V.map p`, which has the same delta-dimension. -/
theorem properPushforwardKillsPrincipalDivisor_of_isClosedImmersion (C : ChowSituation.{u})
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
    (hp : p ≫ sY = sX) (k : ℤ) :
    ProperPushforwardKillsPrincipalDivisor C sX sY p k := by
  intro V hV hdim g
  have hT : IsIntegral (V.map p).subscheme := isIntegral_subscheme_map p V hV
  have _ : IsLocallyNoetherian V.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (V.subschemeι ≫ sX)
  have _ : IsLocallyNoetherian (V.map p).subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian ((V.map p).subschemeι ≫ sY)
  obtain ⟨φ, hφ1⟩ : ∃ φ : V.subscheme ≅ (V.map p).subscheme,
      φ.hom ≫ (V.map p).subschemeι = V.subschemeι ≫ p :=
    ⟨imageIsoOfIsClosedImmersion p V, imageIsoOfIsClosedImmersion_hom_subschemeι p V⟩
  have hφ : φ.hom ≫ ((V.map p).subschemeι ≫ sY) = V.subschemeι ≫ sX := by
    rw [← Category.assoc, hφ1, Category.assoc, hp]
  have hw : ∀ z : V.subscheme,
      relativeDimension C.dimensionFunction (V.subschemeι ≫ sX) z =
        relativeDimension C.dimensionFunction ((V.map p).subschemeι ≫ sY) (φ.hom.base z) :=
    fun z ↦ (relativeDimension_of_iso C.dimensionFunction (V.subschemeι ≫ sX)
      ((V.map p).subschemeι ≫ sY) φ hφ z).symm
  refine Or.inr ⟨hT, ?_, rationalFunctionsUnitsMulEquivOfIso φ g, ?_⟩
  · rwa [schemeDeltaDimension_of_iso C (V.subschemeι ≫ sX) ((V.map p).subschemeι ≫ sY) φ hφ]
  set c := principalCycle V.subscheme ((rationalFunctionsEquivFunctionField V.subscheme).1
    (g : rationalFunctions V.subscheme))
  refine (algebraicCycle_map_comp_relativeDimension C (V.subschemeι ≫ sX) sX sY V.subschemeι p
    rfl hp c).trans ?_
  rw [algebraicCycle_map_congr hφ1.symm, ← algebraicCycle_map_comp_relativeDimension C
    (V.subschemeι ≫ sX) ((V.map p).subschemeι ≫ sY) sY φ.hom (V.map p).subschemeι hφ rfl,
    map_principalCycle_rationalFunctions_of_iso φ _ _ hw]
  rfl

/-- Proper pushforward of `k`-cycles along a closed immersion over the base factors through
rational equivalence. -/
theorem properPushforwardFactorsThroughRationalEquivalence_of_isClosedImmersion
    (C : ChowSituation.{u}) (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S)
    [LocallyOfFiniteType sY] (hp : p ≫ sY = sX) (k : ℤ) :
    ProperPushforwardFactorsThroughRationalEquivalence C sX sY p hp k :=
  properPushforwardFactorsThroughRationalEquivalence_of_killsPrincipalDivisor C sX sY p hp k
    (properPushforwardKillsPrincipalDivisor_of_isClosedImmersion p C sX sY hp k)

end Stacks.Chow

end
