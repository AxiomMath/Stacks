module

public import StacksFrontier.AlgebraicGeometry.Descent.PullbackSectionsSheaf.UnitComparison
public import StacksFrontier.AlgebraicGeometry.FlatBaseChange.Pushforward
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.ContractingRationalCurves

/-!
# The degree-zero base-change comparison for the structure sheaf

Let `f : X ⟶ Y` be a proper morphism all of whose fibres have dimension at most one and
vanishing first cohomology, and suppose `𝒪_Y ⟶ f_* 𝒪_X` is surjective. [Stacks, Tag 0E7I]
asserts that `𝒪_{Y'} ⟶ f'_* 𝒪_{X'}` is again surjective for every base change `f'` of `f`; it
is proved, under exactly the hypotheses of the tag, as `epi_unitToPushforwardUnit_of_baseChange`
in `SurjectivityAfterBaseChange.lean`.

This file builds the canonical comparison `g^* (f_* 𝒪_X) ⟶ f'_* 𝒪_{X'}`, proves its
compatibility with the canonical maps out of the structure sheaves, and names the degree-zero
companion of the base-change clause that `ContractingRationalCurves.lean` already carries in
degree one.

## Main definitions

All in the namespace `Stacks.AlgebraicGeometry.TopDegreeBaseChange`.

* `directImageStructureSheaf`: `f_* 𝒪_X`.
* `directImageStructureSheafBaseChangeMap`: the canonical comparison
  `g^* (f_* 𝒪_X) ⟶ f'_* 𝒪_{X'}` for the base change of `f` along `g : Y' ⟶ Y`, assembled from
  the degree-zero base-change map of [Stacks, Tag 02N7] and the identification of the pullback
  of a structure sheaf with a structure sheaf.
* `DirectImageStructureSheafCommutesBaseChange` and
  `DirectImageStructureSheafCommutesBaseChangeOfFibreDimensionOne`: invertibility of that
  comparison, for one morphism and for all proper morphisms with one-dimensional fibres of
  vanishing first cohomology.

## Main results

* `unitToPushforwardUnit_comp_directImageStructureSheafBaseChangeMap`: **the canonical
  comparison is compatible with the canonical maps from the structure sheaves.** Over `Y'` the
  map `𝒪_{Y'} ⟶ f'_* 𝒪_{X'}` is the pullback along `g` of `𝒪_Y ⟶ f_* 𝒪_X` followed by the
  comparison. This is what makes the surjectivity transport once the comparison is invertible,
  and it is proved here, not assumed.

## The degree-zero base-change clause, and why it is not the tag

`ContractingRationalCurves.lean` records the house convention of this directory: the clause of
[Stacks, Tag 0EX3] (b) saying that formation of `R^d f_* 𝒪_X` commutes with arbitrary base
change is not proved in this development at fibre dimension one, and travels as a named
hypothesis `hbc`. That file needs it in degree one, as
`FirstDirectImageCommutesBaseChange`; the same clause in degree **zero** is
`DirectImageStructureSheafCommutesBaseChange`. Of [Stacks, Tag 0EX3] only conclusion (a)
is proved in this development, in `BaseChangeVanishing.lean`; conclusion (c) — the invertibility
of the canonical comparison — is explicitly open, see `BaseChangeMapDegenerate.lean`.

*Why the clause is true in degree zero under these hypotheses, and why it is nevertheless not
available here.* Over an affine base `Y = Spec A` the functor `M ↦ H⁰(X, f^* M~)` is right
exact: the kernel of `f^* M₂ ⟶ f^* M₃` is a quotient of `f^* M₁`, hence globally generated, so
its first cohomology vanishes by [Stacks, Tag 0E7H] clause (4) — which is exactly where the two
fibrewise hypotheses are consumed. It is also additive, `A`-linear, and commutes with direct
sums by [Stacks, Tag 01FF]. Eilenberg-Watts then identifies it with `- ⊗_A H⁰(X, 𝒪_X)`, which
is the clause. What this development cannot do is run that argument: the Eilenberg-Watts
package of this directory, `EilenbergWattsGeometricFactor.lean` and
`EilenbergWattsSituation.lean`, takes its vanishing input as `H^{d+1}(W, G) = 0` for **every**
quasi-coherent `G`, and at `d = 0` that is false for a proper morphism with one-dimensional
fibres over an affine base — `R¹ f_* 𝒪(-2)` is nonzero for `P¹_A ⟶ Spec A`. Only the weaker,
globally-generated form is available, and the package is not reworked around it
here.

The clause is a clause of [Stacks, Tag 0EX3], not of [Stacks, Tag 0E7I]: it says that the
*comparison morphism* is invertible, where the tag asserts that a *different* morphism, the
canonical map out of the structure sheaf of the base, is surjective. The clause alone does not
give the tag's conclusion — the surjectivity over `Y` is needed too — and the tag's conclusion
does not give the clause, which also asserts injectivity. What this file supplies is the
compatibility of the two morphisms; granted the clause, it transports the surjectivity over `Y`
to every base change, by the right exactness of pullback.

## Implementation notes

`𝒪_X` is `AlgebraicGeometry.Scheme.unitModule X`, which unfolds to the
`SheafOfModules.unit X.ringCatSheaf` of `ContractingRationalCurves.lean`; the canonical maps
`𝒪_Y ⟶ f_* 𝒪_X` and `g^* 𝒪_Y ≅ 𝒪_{Y'}` are
`AlgebraicGeometry.Scheme.Modules.unitToPushforwardUnit` and
`AlgebraicGeometry.Scheme.Modules.pullbackUnitIso`, and the degree-zero base-change map is
`Stacks.AlgebraicGeometry.FlatBaseChange.pushforwardBaseChange`. All three are stated at that
spelling, so this file uses it throughout.

The compatibility is proved by transposing both sides under `g^* ⊣ g_*`, where the two
`pullbackUnitIso`s become the canonical maps `𝒪 ⟶ h_* 𝒪` by
`AlgebraicGeometry.Scheme.Modules.pullbackUnitIso_homEquiv` and the whole identity reduces to
`AlgebraicGeometry.Scheme.Modules.unitToPushforwardUnit_comp` applied to the two sides
`g' ≫ f` and `f' ≫ g` of the square.

A base change of `f` is taken to be `pullback.snd f g`, as in the degree-one clause of
`ContractingRationalCurves.lean`; `IsProper` of that morphism is not needed here.

## References

* [Stacks Project, Tag 0E7I](https://stacks.math.columbia.edu/tag/0E7I)
* [Stacks Project, Tag 0E7H](https://stacks.math.columbia.edu/tag/0E7H)
* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
* [Stacks Project, Tag 01FF](https://stacks.math.columbia.edu/tag/01FF)
* [Stacks Project, Tag 02N7](https://stacks.math.columbia.edu/tag/02N7)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.FlatBaseChange

universe u

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

noncomputable section

/-- `f_* 𝒪_X`, the direct image of the structure sheaf. -/
abbrev directImageStructureSheaf {X Y : Scheme.{u}} (f : X ⟶ Y) : Y.Modules :=
  (Scheme.Modules.pushforward f).obj (Scheme.unitModule X)

/-- **The canonical comparison `g^* (f_* 𝒪_X) ⟶ f'_* 𝒪_{X'}`** for the base change of
`f : X ⟶ Y` along `g : Y' ⟶ Y`. It is the degree-zero base-change map of [Stacks, Tag 02N7]
at the structure sheaf, followed by the identification of `(g')^* 𝒪_X` with `𝒪_{X'}`. -/
def directImageStructureSheafBaseChangeMap {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) :
    (Scheme.Modules.pullback g).obj (directImageStructureSheaf f) ⟶
      directImageStructureSheaf (pullback.snd f g) :=
  pushforwardBaseChange (pullback.condition (f := f) (g := g)) (Scheme.unitModule X) ≫
    (Scheme.Modules.pushforward (pullback.snd f g)).map
      (Scheme.Modules.pullbackUnitIso (pullback.fst f g)).hom

/-- Transporting the canonical map `𝒪 ⟶ h_* 𝒪` along an equality of morphisms of schemes. -/
private theorem unitToPushforwardUnit_congr {X S : Scheme.{u}} {h₁ h₂ : X ⟶ S} (e : h₁ = h₂) :
    Scheme.Modules.unitToPushforwardUnit h₁ ≫
        (Scheme.Modules.pushforwardCongr e).hom.app (Scheme.unitModule X) =
      Scheme.Modules.unitToPushforwardUnit h₂ := by
  subst e
  ext U
  simp
  rfl

/-- **The degree-zero base-change comparison is compatible with the canonical maps out of the
structure sheaves.** For a commuting square `g' ≫ f = f' ≫ g`, the canonical map
`𝒪_{S'} ⟶ f'_* (g')^* 𝒪_X` obtained by pulling `𝒪_S ⟶ f_* 𝒪_X` back along `g` and applying
the comparison is the canonical map `𝒪_{S'} ⟶ f'_* 𝒪_{S'}` read through `(g')^* 𝒪_X ≅ 𝒪_{X'}`.

Both sides are transposed under `g^* ⊣ g_*`; the left-hand side becomes
`𝒪_S ⟶ g_* 𝒪_{S'} ⟶ g_* f'_* 𝒪_{X'}` and the right-hand side
`𝒪_S ⟶ f_* 𝒪_X ⟶ f_* g'_* 𝒪_{X'}`, and the two agree because both compute the canonical map
of the composite morphism `g' ≫ f = f' ≫ g`. -/
theorem unitToPushforwardUnit_comp_pushforwardBaseChange {X X' S S' : Scheme.{u}} {f : X ⟶ S}
    {g : S' ⟶ S} {f' : X' ⟶ S'} {g' : X' ⟶ X} (w : g' ≫ f = f' ≫ g) :
    (Scheme.Modules.pullbackUnitIso g).hom ≫
        Scheme.Modules.unitToPushforwardUnit f' ≫
          (Scheme.Modules.pushforward f').map
            (Scheme.Modules.pullbackUnitIso g').inv =
      (Scheme.Modules.pullback g).map (Scheme.Modules.unitToPushforwardUnit f) ≫
        pushforwardBaseChange w (Scheme.unitModule X) := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _).injective
  have hu : (Scheme.Modules.pullbackPushforwardAdjunction g').unit.app (Scheme.unitModule X) =
      Scheme.Modules.unitToPushforwardUnit g' ≫
        (Scheme.Modules.pushforward g').map (Scheme.Modules.pullbackUnitIso g').inv := by
    rw [← Scheme.Modules.pullbackUnitIso_homEquiv g', Adjunction.homEquiv_unit,
      Category.assoc, ← Functor.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id]
    simp
  have hL : Scheme.Modules.unitToPushforwardUnit g ≫
        (Scheme.Modules.pushforward g).map (Scheme.Modules.unitToPushforwardUnit f') =
      Scheme.Modules.unitToPushforwardUnit (f' ≫ g) ≫
        (Scheme.Modules.pushforwardComp f' g).inv.app (Scheme.unitModule X') := by
    rw [← Scheme.Modules.unitToPushforwardUnit_comp f' g]
    simp
  have n1 := ((Scheme.Modules.pushforwardComp f' g).inv.naturality
    (Scheme.Modules.pullbackUnitIso g').inv).symm
  have n2 := (Scheme.Modules.pushforwardComp g' f).hom.naturality
    (Scheme.Modules.pullbackUnitIso g').inv
  have n3 := (Scheme.Modules.pushforwardCongr w).hom.naturality
    (Scheme.Modules.pullbackUnitIso g').inv
  rw [Adjunction.homEquiv_naturality_left, homEquiv_pushforwardBaseChange,
    Adjunction.homEquiv_naturality_right, Scheme.Modules.pullbackUnitIso_homEquiv,
    pushforwardBaseChangeUnit, hu]
  simp only [Functor.comp_map] at n1 n2 n3
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hL, n1, reassoc_of% n2,
    reassoc_of% (Scheme.Modules.unitToPushforwardUnit_comp g' f), reassoc_of% n3,
    ← Category.assoc (Scheme.Modules.unitToPushforwardUnit (g' ≫ f)),
    unitToPushforwardUnit_congr w]

/-- The compatibility at the canonical base change `pullback.snd f g` of `f` along `g`: the map
`𝒪_{Y'} ⟶ f'_* 𝒪_{X'}` is the pullback along `g` of `𝒪_Y ⟶ f_* 𝒪_X` followed by the
comparison `directImageStructureSheafBaseChangeMap`. -/
theorem unitToPushforwardUnit_comp_directImageStructureSheafBaseChangeMap
    {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) :
    (Scheme.Modules.pullbackUnitIso g).hom ≫
        Scheme.Modules.unitToPushforwardUnit (pullback.snd f g) =
      (Scheme.Modules.pullback g).map (Scheme.Modules.unitToPushforwardUnit f) ≫
        directImageStructureSheafBaseChangeMap f g := by
  rw [directImageStructureSheafBaseChangeMap, ← Category.assoc,
    ← unitToPushforwardUnit_comp_pushforwardBaseChange
      (pullback.condition (f := f) (g := g)), Category.assoc, Category.assoc,
    ← Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id]
  simp

/-- **The base-change clause of [Stacks, Tag 0EX3] (b) in degree zero for the structure
sheaf**: the canonical comparison `g^* (f_* 𝒪_X) ⟶ f'_* 𝒪_{X'}` is invertible for every
`g : Y' ⟶ Y`, so that formation of `f_* 𝒪_X` commutes with arbitrary base change.

This is the degree-zero companion of `FirstDirectImageCommutesBaseChange`. It holds under the
hypotheses of `DirectImageStructureSheafCommutesBaseChangeOfFibreDimensionOne` below, by the
Eilenberg-Watts argument recorded in this file's module documentation, but it is not proved in
this development: of [Stacks, Tag 0EX3] only conclusion (a) is proved, in
`BaseChangeVanishing.lean`, and conclusion (c) is open, see `BaseChangeMapDegenerate.lean`. -/
abbrev DirectImageStructureSheafCommutesBaseChange {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  ∀ ⦃Y' : Scheme.{u}⦄ (g : Y' ⟶ Y), IsIso (directImageStructureSheafBaseChangeMap f g)

/-- The same clause, as a statement about every proper morphism all of whose fibres have
dimension at most one and vanishing first cohomology — the hypotheses under which
[Stacks, Tag 0E7D] makes [Stacks, Tag 0EX3] available. This is the shape
`GloballyGeneratedVanishing.lean` uses for the degree-one clause. -/
abbrev DirectImageStructureSheafCommutesBaseChangeOfFibreDimensionOne : Prop :=
  ∀ ⦃X₀ Y₀ : Scheme.{u}⦄ (h : X₀ ⟶ Y₀), IsProper h →
    (∀ s : Y₀, topologicalKrullDim (h.fiber s) ≤ ((1 : ℕ) : WithBot ℕ∞)) →
      (∀ s : Y₀, IsZero (firstCohomologyStructureSheaf (h.fiber s))) →
        DirectImageStructureSheafCommutesBaseChange h

end

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
