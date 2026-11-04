module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FibreProductFormalBase
public import StacksFrontier.AlgebraicGeometry.FormalSpace.LocalPropertyBaseChangeRefined
public import StacksFrontier.AlgebraicGeometry.FormalSpace.LocalPropertyComposition
public import StacksFrontier.AlgebraicGeometry.FormalSpace.TautMorphismRepresentabilityRefined
public import StacksFrontier.Topology.Algebra.AdicTopology.LocalPropertiesRefined
import all StacksFrontier.AlgebraicGeometry.FormalSpace.LocalPropertyComposition

/-!
# Composition and cancellation of local properties of morphisms of formal algebraic spaces

A local property of arrows which is stable under composition holds for a composite of
morphisms of formal algebraic spaces having it, and one with the cancellation property holds
for the first factor whenever it holds for the composite and the second factor. Both are proved
by an affine étale covering adapted to the pair of morphisms.

## Main results

* `exists_affineEtaleCover_chartFactorization_comp'`: the affine étale covering adapted to a
  composite of morphisms.
* `hasPropertyOnEveryAffineEtaleDiagram_comp'`: stability under composition.
* `hasPropertyOnEveryAffineEtaleDiagram_of_comp'`: cancellation.
* `transfersCompositionOnAffineEtaleDiagrams'`, `transfersCancellationOnAffineEtaleDiagrams'`:
  the Noetherian variants, uniformly over all properties.

## Implementation notes

This module holds the strengthened and the additional declarations that belong with
`StacksFrontier.AlgebraicGeometry.FormalSpace.LocalPropertyComposition`. A declaration of that
module whose statement is strengthened here keeps its original statement there; its strengthened
form lives here under a primed name.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A family of morphisms of fppf sheaves obtained by composing a jointly locally surjective
family `(qⱼ : Gⱼ ⟶ X)` with a jointly locally surjective family over each of its sources is
again jointly locally surjective: each `Sigma.desc` is an epimorphism of sheaves of sets, and
the composite family cancels through the two of them in turn. -/
alias isLocallySurjective_sigmaDesc_comp' := isLocallySurjective_sigmaDesc_comp

variable (C : ∀ (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [IsLinearTopology R R], Prop)
  (P : ∀ {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
    [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂], (R₁ →+* R₂) → Prop)

/-- The covering constructed in the proofs of **Stacks 0GBI** and **Stacks 0GBM**: an affine
étale covering `{Uᵢ ⟶ X}` of the source of `f : X ⟶ Y`, together with factorizations
`Uᵢ ⟶ Vᵢ ⟶ Y` through affine étale charts of `Y` and `Vᵢ ⟶ Wᵢ ⟶ Z` through affine étale charts
of `Z`, with `P` on each `Vᵢ ⟶ Wᵢ`.

It is obtained from the implications (1) ⟹ (2) ⟹ (3) of Stacks 0ANG for `g`, which produce the
covering of `Y` and the factorizations of its members through charts of `Z`, followed by
coverings of the fibre products of those members with `X`. Those fibre products are formal
algebraic spaces by **Stacks 0AJ3**, which this library proves outright:
`AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_pullback_chart_of_isFormalAlgebraicSpace`
needs only that the two ends of the morphism and the chart be formal algebraic spaces. -/
theorem exists_affineEtaleCover_chartFactorization_comp'
    {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hX : IsFormalAlgebraicSpace B S hS X)
    (hY : IsFormalAlgebraicSpace B S hS Y)
    (hZ : IsFormalAlgebraicSpace B S hS Z)
    (hg : HasPropertyOnEveryAffineEtaleDiagram B S hS C P g) :
    ∃ (I : Type (u + 1)) (U V W : I → FppfSheaf B S hS) (u : ∀ i, U i ⟶ X)
      (t : ∀ i, U i ⟶ V i) (s : ∀ i, V i ⟶ W i) (v : ∀ i, V i ⟶ Y) (w : ∀ i, W i ⟶ Z),
      IsAffineEtaleCover B S hS U u ∧
        (∀ i, IsAffineFormalAlgebraicSpace B S hS (V i)) ∧
        (∀ i, IsAffineFormalAlgebraicSpace B S hS (W i)) ∧
        (∀ i, IsRepresentableEtale B S hS (v i)) ∧
        (∀ i, IsRepresentableEtale B S hS (w i)) ∧
        (∀ i, u i ≫ f = t i ≫ v i) ∧ (∀ i, v i ≫ g = s i ≫ w i) ∧
        ∀ i, HasPropertyOnAffineChartMap B S hS C P (s i) := by
  obtain ⟨J, V, v, hVcover, hfac⟩ :=
    hasPropertyAfterSourceCover_of_afterTargetCover B S hS C P g
      (hasPropertyAfterTargetCover_of_everyAffineEtaleDiagram B S hS C P g hZ
        (fun _V' v' hV' _ ↦ isFormalAlgebraicSpace_pullback_chart_of_isFormalAlgebraicSpace
          B S hS v' g hZ hV' hY) hg)
  choose W w s hWaffine hWetale hWsquare hWproperty using hfac
  choose I U m hUaffine hUetale hUsurj using fun j ↦
    (isFormalAlgebraicSpace_pullback_chart_of_isFormalAlgebraicSpace B S hS (v j) f hY
      (hVcover.1 j) hX).2
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  refine ⟨Σ j, I j, fun p ↦ U p.1 p.2, fun p ↦ V p.1, fun p ↦ W p.1,
    fun p ↦ m p.1 p.2 ≫ pullback.snd (v p.1) f,
    fun p ↦ m p.1 p.2 ≫ pullback.fst (v p.1) f, fun p ↦ s p.1, fun p ↦ v p.1, fun p ↦ w p.1,
    ⟨fun p ↦ hUaffine p.1 p.2,
      fun p ↦ IsRepresentableEtale.comp B S hS (hUetale p.1 p.2)
        (isRepresentableEtale_pullback_snd B S hS (v p.1) f (hVcover.2.1 p.1)), ?_⟩,
    fun p ↦ hVcover.1 p.1, fun p ↦ hWaffine p.1, fun p ↦ hVcover.2.1 p.1,
    fun p ↦ hWetale p.1, fun p ↦ ?_, fun p ↦ hWsquare p.1, fun p ↦ hWproperty p.1⟩
  · exact isLocallySurjective_sigmaDesc_comp' B S hS (fun j ↦ pullback.snd (v j) f) m
      (Sheaf.isLocallySurjective_sigmaDesc_pullback_snd f v hVcover.2.2) hUsurj
  · rw [Category.assoc, Category.assoc, ← pullback.condition]

/-- **Stacks 0GBI**, in the form the covering of its proof produces: if `P` is stable under
composition on charts and `f : X ⟶ Y`, `g : Y ⟶ Z` satisfy condition (1) of Stacks 0ANG, then
the composite `g ∘ f` satisfies condition (3) of Stacks 0ANG.

Each member `Uᵢ ⟶ X` of the covering factors as `Uᵢ ⟶ Wᵢ ⟶ Z` through the chart `Wᵢ` of `Z`,
and `P` holds on `Uᵢ ⟶ Wᵢ` because it holds on `Uᵢ ⟶ Vᵢ` by condition (1) for `f` and on
`Vᵢ ⟶ Wᵢ` by condition (1) for `g`. -/
theorem hasPropertyAfterSourceCover_comp'
    (hchart : ChartPropertyIsStableUnderComposition B S hS C P)
    {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hX : IsFormalAlgebraicSpace B S hS X)
    (hY : IsFormalAlgebraicSpace B S hS Y)
    (hZ : IsFormalAlgebraicSpace B S hS Z)
    (hf : HasPropertyOnEveryAffineEtaleDiagram B S hS C P f)
    (hg : HasPropertyOnEveryAffineEtaleDiagram B S hS C P g) :
    HasPropertyAfterSourceCover B S hS C P (f ≫ g) := by
  obtain ⟨I, U, V, W, u, t, s, v, w, hUcover, hVaffine, hWaffine, hv, hw, hsq₁, hsq₂, hs⟩ :=
    exists_affineEtaleCover_chartFactorization_comp' B S hS C P f g hX hY hZ hg
  refine ⟨I, U, u, hUcover, fun i ↦ ⟨W i, w i, t i ≫ s i, hWaffine i, hw i, ?_, ?_⟩⟩
  · rw [← Category.assoc, hsq₁ i, Category.assoc, hsq₂ i, Category.assoc]
  · exact hchart (t i) (s i) (hUcover.1 i) (hVaffine i) (hWaffine i)
      (hf (U i) (V i) (u i) (v i) (t i) (hUcover.1 i) (hVaffine i) (hUcover.2.1 i) (hv i)
        (hsq₁ i)) (hs i)

/-- **Stacks 0GBI.** Let `P` be a local property of arrows of the class `C` which is stable
under composition. If `f : X ⟶ Y` and `g : Y ⟶ Z` are morphisms of formal algebraic spaces over
`S` satisfying the equivalent conditions of Stacks 0ANG for `P`, then so does `g ∘ f`.

Condition (3) is what the covering of the proof gives; the passage back to condition (1) is the
implication (3) ⟹ (1) of Stacks 0ANG, which is `h31`.

That `X`, `Y` and `Z` are formal algebraic spaces is the tag's own setting, which asks them to
be locally countably indexed formal algebraic spaces; the fibre products of `f` and of `g` with
the affine étale charts of their targets are then formal algebraic spaces by **Stacks 0AJ3**,
which this library proves outright, so nothing of Stacks 0AJ3 is assumed here.

Two inputs are still missing from the library, so no `@[stacks]` attribute sits on this
statement. `h31` reduces, through
`AlgebraicGeometry.FormalSpace.sourceCoverImpliesEveryAffineEtaleDiagram_of_propertyIsLocal`, to
the presented étale refinement of a covering of the source; and `hchart` is the composition axiom
of Situation 0GBH read on morphisms of affine formal algebraic spaces, which needs a ring
of the class `C` presenting the middle object of a composable pair, that is the implication
(2) ⟹ (1) of Stacks 0AKX. The composition assumption on `P` is the tag's own: Stacks 0GBI is
stated for a local property of morphisms of `WAdm^{count}` which is stable under composition,
and `hchart` is that assumption read where the geometry uses it. Narrowing `hchart` to the
instance used below does not reduce it, for the reason recorded in the module docstring. -/
theorem hasPropertyOnEveryAffineEtaleDiagram_comp'
    (hchart : ChartPropertyIsStableUnderComposition B S hS C P)
    (h31 : SourceCoverImpliesEveryAffineEtaleDiagram B S hS C P)
    {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hX : IsFormalAlgebraicSpace B S hS X)
    (hY : IsFormalAlgebraicSpace B S hS Y)
    (hZ : IsFormalAlgebraicSpace B S hS Z)
    (hf : HasPropertyOnEveryAffineEtaleDiagram B S hS C P f)
    (hg : HasPropertyOnEveryAffineEtaleDiagram B S hS C P g) :
    HasPropertyOnEveryAffineEtaleDiagram B S hS C P (f ≫ g) :=
  h31 _ (hasPropertyAfterSourceCover_comp' B S hS C P hchart f g hX hY hZ hf hg)

/-- **Stacks 0GBM**, in the form the covering of its proof produces: if `P` has the
cancellation property on charts and `g ∘ f`, `g` satisfy condition (1) of Stacks 0ANG, then
`f : X ⟶ Y` satisfies condition (3) of Stacks 0ANG.

Each member `Uᵢ ⟶ X` of the covering factors as `Uᵢ ⟶ Vᵢ ⟶ Y` through the chart `Vᵢ` of `Y`,
and `P` holds on `Uᵢ ⟶ Vᵢ` by cancellation against `Vᵢ ⟶ Wᵢ`, which has `P` by condition (1)
for `g`, and `Uᵢ ⟶ Wᵢ`, which has `P` by condition (1) for `g ∘ f`. -/
theorem hasPropertyAfterSourceCover_of_comp'
    (hchart : ChartPropertyHasCancellation B S hS C P)
    {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hX : IsFormalAlgebraicSpace B S hS X)
    (hY : IsFormalAlgebraicSpace B S hS Y)
    (hZ : IsFormalAlgebraicSpace B S hS Z)
    (hfg : HasPropertyOnEveryAffineEtaleDiagram B S hS C P (f ≫ g))
    (hg : HasPropertyOnEveryAffineEtaleDiagram B S hS C P g) :
    HasPropertyAfterSourceCover B S hS C P f := by
  obtain ⟨I, U, V, W, u, t, s, v, w, hUcover, hVaffine, hWaffine, hv, hw, hsq₁, hsq₂, hs⟩ :=
    exists_affineEtaleCover_chartFactorization_comp' B S hS C P f g hX hY hZ hg
  refine ⟨I, U, u, hUcover, fun i ↦ ⟨V i, v i, t i, hVaffine i, hv i, hsq₁ i, ?_⟩⟩
  exact hchart (t i) (s i) (hUcover.1 i) (hVaffine i) (hWaffine i) (hs i)
    (hfg (U i) (W i) (u i) (w i) (t i ≫ s i) (hUcover.1 i) (hWaffine i) (hUcover.2.1 i)
      (hw i) (by rw [← Category.assoc, hsq₁ i, Category.assoc, hsq₂ i, Category.assoc]))

/-- **Stacks 0GBM.** Let `P` be a local property of arrows of the class `C` with the
cancellation property. If `g ∘ f` and `g : Y ⟶ Z` satisfy the equivalent conditions of Stacks
0ANG for `P`, then so does `f : X ⟶ Y`.

Condition (3) is what the covering of the proof gives; the passage back to condition (1) is the
implication (3) ⟹ (1) of Stacks 0ANG, which is `h31`.

That `X`, `Y` and `Z` are formal algebraic spaces is the tag's own setting, and the fibre
products with the affine étale charts of the targets are formal algebraic spaces by **Stacks
0AJ3**, which this library proves outright, so nothing of Stacks 0AJ3 is assumed here.

The two missing inputs are the same as for
`AlgebraicGeometry.FormalSpace.hasPropertyOnEveryAffineEtaleDiagram_comp'`, so no `@[stacks]`
attribute sits on this statement either: `h31` reduces to the presented étale refinement of a
covering of the source, and `hchart` is the cancellation property of Situation 0GBL read on
morphisms of affine formal algebraic spaces, which needs a ring of the class `C` presenting the
middle object of a composable pair, that is the implication (2) ⟹ (1) of Stacks 0AKX. The
cancellation assumption on `P` is the tag's own: Stacks 0GBM is stated for a local property of
morphisms of `WAdm^{count}` which has the cancellation property. Narrowing `hchart` to the
instance used below does not reduce it, for the reason recorded in the module docstring. -/
theorem hasPropertyOnEveryAffineEtaleDiagram_of_comp'
    (hchart : ChartPropertyHasCancellation B S hS C P)
    (h31 : SourceCoverImpliesEveryAffineEtaleDiagram B S hS C P)
    {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hX : IsFormalAlgebraicSpace B S hS X)
    (hY : IsFormalAlgebraicSpace B S hS Y)
    (hZ : IsFormalAlgebraicSpace B S hS Z)
    (hfg : HasPropertyOnEveryAffineEtaleDiagram B S hS C P (f ≫ g))
    (hg : HasPropertyOnEveryAffineEtaleDiagram B S hS C P g) :
    HasPropertyOnEveryAffineEtaleDiagram B S hS C P f :=
  h31 _ (hasPropertyAfterSourceCover_of_comp' B S hS C P hchart f g hX hY hZ hfg hg)

/-- **The Noetherian variant of Stacks 0GBI, uniformly over all properties:** whenever `P` is a
local property of arrows of `WAdm^{Noeth}` stable under composition, condition (1) of
Stacks 0ANG transfers from `(f, P)` and `(g, P)` to `(g ∘ f, P)`.

The two inputs of the single-pair statement are asked of every property carrying the bundle
of Remark 0GBK, which is how that bundle supplies locality, and of every pair of morphisms. -/
theorem transfersCompositionOnAffineEtaleDiagrams'
    (hchart : ∀ P : ∀ {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
        [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂], (R₁ →+* R₂) → Prop,
      TopologicalRing.PropertyIsStableUnderCompositionNoetherian'.{u} P →
        ChartPropertyIsStableUnderComposition B S hS
          (fun R ↦ TopologicalRing.IsAdic R ∧ IsNoetherianRing R) P)
    (h31 : ∀ P : ∀ {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
        [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂], (R₁ →+* R₂) → Prop,
      TopologicalRing.PropertyIsLocalNoetherian'.{u} P →
        SourceCoverImpliesEveryAffineEtaleDiagram B S hS
          (fun R ↦ TopologicalRing.IsAdic R ∧ IsNoetherianRing R) P)
    (hspace : ∀ Z : FppfSheaf B S hS, IsFormalAlgebraicSpace B S hS Z) :
    ∀ (P : ∀ {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
        [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂], (R₁ →+* R₂) → Prop),
      TopologicalRing.PropertyIsStableUnderCompositionNoetherian'.{u} P →
      ∀ {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Y ⟶ Z),
        HasPropertyOnEveryAffineEtaleDiagram B S hS
            (fun R ↦ TopologicalRing.IsAdic R ∧ IsNoetherianRing R) P f →
          HasPropertyOnEveryAffineEtaleDiagram B S hS
              (fun R ↦ TopologicalRing.IsAdic R ∧ IsNoetherianRing R) P g →
            HasPropertyOnEveryAffineEtaleDiagram B S hS
              (fun R ↦ TopologicalRing.IsAdic R ∧ IsNoetherianRing R) P (f ≫ g) :=
  fun P hP {X Y Z} f g hf hg ↦ hasPropertyOnEveryAffineEtaleDiagram_comp' B S hS _ P
    (hchart P hP) (h31 P hP.isLocal) f g (hspace X) (hspace Y) (hspace Z) hf hg

/-- **The Noetherian variant of Stacks 0GBM, uniformly over all properties:** whenever `P` is a
local property of arrows of `WAdm^{Noeth}` with the cancellation property, condition (1) of
Stacks 0ANG transfers from `(g ∘ f, P)` and `(g, P)` to `(f, P)`.

Locality is asked separately here, as in the statement of Remark 0GBP, because the cancellation
property of Situation 0GBL carries no locality field for the Noetherian class. -/
theorem transfersCancellationOnAffineEtaleDiagrams'
    (hchart : ∀ P : ∀ {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
        [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂], (R₁ →+* R₂) → Prop,
      TopologicalRing.PropertyIsLocalNoetherian'.{u} P →
      TopologicalRing.HasNoetherianCancellationProperty.{u} P →
        ChartPropertyHasCancellation B S hS
          (fun R ↦ TopologicalRing.IsAdic R ∧ IsNoetherianRing R) P)
    (h31 : ∀ P : ∀ {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
        [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂], (R₁ →+* R₂) → Prop,
      TopologicalRing.PropertyIsLocalNoetherian'.{u} P →
        SourceCoverImpliesEveryAffineEtaleDiagram B S hS
          (fun R ↦ TopologicalRing.IsAdic R ∧ IsNoetherianRing R) P)
    (hspace : ∀ Z : FppfSheaf B S hS, IsFormalAlgebraicSpace B S hS Z) :
    ∀ (P : ∀ {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
        [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂], (R₁ →+* R₂) → Prop),
      TopologicalRing.PropertyIsLocalNoetherian'.{u} P →
      TopologicalRing.HasNoetherianCancellationProperty.{u} P →
      ∀ {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Y ⟶ Z),
        HasPropertyOnEveryAffineEtaleDiagram B S hS
            (fun R ↦ TopologicalRing.IsAdic R ∧ IsNoetherianRing R) P (f ≫ g) →
          HasPropertyOnEveryAffineEtaleDiagram B S hS
              (fun R ↦ TopologicalRing.IsAdic R ∧ IsNoetherianRing R) P g →
            HasPropertyOnEveryAffineEtaleDiagram B S hS
              (fun R ↦ TopologicalRing.IsAdic R ∧ IsNoetherianRing R) P f :=
  fun P hlocal hcancel {X Y Z} f g hfg hg ↦ hasPropertyOnEveryAffineEtaleDiagram_of_comp' B S hS
    _ P (hchart P hlocal hcancel) (h31 P hlocal) f g (hspace X) (hspace Y) (hspace Z) hfg hg

end AlgebraicGeometry.FormalSpace

end
