module

public import StacksFrontier.AlgebraicGeometry.AmplePowers.Basic
public import StacksFrontier.AlgebraicGeometry.AmplePullbackPart1.TensorPowerTensor
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjChartCocycle
public import StacksFrontier.AlgebraicGeometry.Descent.SectionsPullbackComparison.PullbackSection
public import StacksFrontier.AlgebraicGeometry.InvertiblePullback.Basic
public import StacksFrontier.AlgebraicGeometry.NonvanishingPullback.Nonvanishing
public import StacksFrontier.AlgebraicGeometry.RelativeVeryAmple.TensorPower
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The ratio of two sections of an invertible module commutes with pullback

Let `L` be an invertible module on a scheme `Y`, let `t` and `x` be global sections of the `n`-th
tensor power of `L`, and let `V ⊆ Y` be an open on which `t` does not vanish. The ratio

  `x / t ∈ Γ(Y, V)`

is `Stacks.AlgebraicGeometry.ProjChartCocycle.ratioOf`: the unique function on `V` with
`x|_V = (x/t) · t|_V`, which exists because `t` trivializes `L ^⊗ n` over `V`. This file proves
that forming it commutes with pulling back along an arbitrary morphism of schemes `j : Y' ⟶ Y`:
the ratio of the pullbacks is the pullback of the ratio.

The pullback of a global section of `L ^⊗ n` is a global section of `(j^*L) ^⊗ n` only after the
comparison `(j^*L) ^⊗ n ≅ j^*(L ^⊗ n)`, which is Stacks Tag 01CD iterated
(`Stacks.RelativeVeryAmple.pullbackTensorPowModuleIso`) read at the left-iterated powers
`Stacks.TensorPowers.natTensorPow` that the ratio is stated over; the composite is
`pullbackNatTensorPowIso` and the transported section is `pullSection`.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjChartRatioPullback.pullbackNatTensorPowIso`: the comparison
  `(j^*L) ^⊗ n ≅ j^*(L ^⊗ n)`.
* `Stacks.AlgebraicGeometry.ProjChartRatioPullback.pullSection`: the pullback of a global section
  of `L ^⊗ n`, read through that comparison as a global section of `(j^*L) ^⊗ n`.

## Main results

* `Stacks.AlgebraicGeometry.ProjChartRatioPullback.nonvanishingOpen_pullSection`: **the
  nonvanishing open of a pulled-back section is the preimage of the nonvanishing open**, so a
  denominator that trivializes over `V` trivializes over any open inside `j^{-1}(V)`. This is
  Stacks Tag 0H78 together with the invariance of a nonvanishing locus under an isomorphism of
  modules.
* `Stacks.AlgebraicGeometry.ProjChartRatioPullback.ratioOf_pullback`: **the ratio commutes with
  pullback.** For `V' ≤ j^{-1}(V)`,

  `(x/t)|_{V'} = (j^*x) / (j^*t)`,

  the left side being the image of `x/t` under `AlgebraicGeometry.Scheme.Hom.appLE`.

## Implementation notes

The ratio is characterized by `x|_V = (x/t) · t|_V` and the uniqueness of that scalar
(`Stacks.AlgebraicGeometry.ProjChartCocycle.ratioOf_eq_of_resTop_eq`), so the proof is the
defining identity pushed along pullback of sections: `AlgebraicGeometry.pullbackSectionHom` is
semilinear over `AlgebraicGeometry.Scheme.Hom.appLE`, and the comparison isomorphism acts on
sections `𝒪_{Y'}`-linearly, which turns the identity over `V` into the identity over `V'`. No
property of the ratio beyond its characterization is used, and in particular the invertibility of
`L ^⊗ n` enters only through the trivialization that makes the ratio exist.

`j` is an **arbitrary** morphism of schemes rather than an open immersion: the pullback of an
invertible module is invertible with no hypothesis on the morphism (Stacks Tag 0B8L), and nothing
below needs the morphism to be injective or flat. The open-immersion case is the one a comparison
of charts over two nested opens of a base consumes, with `j` the morphism
`AlgebraicGeometry.Scheme.homOfLE` of an inclusion of opens; it is this statement at that `j`.

Two spellings of the module pullback are in play. `Stacks.Ample.IsInvertibleModule` of a pullback
is an instance only at `RingedSpaceModuleAdjunction.modulePullback`, while
`Stacks.TensorPowers.natTensorPow` elaborates only against `AlgebraicGeometry.Scheme.Modules`;
the two functors are equal by `rfl` but their discrimination-tree keys differ, so
`isInvertibleModule_schemeModulesPullback` restates the instance at the second spelling. For the
same reason the proofs below are `exact` chains rather than `rw` sequences wherever a goal
mentions both the pullback presheaf and the unit of the pullback-pushforward adjunction: the two
types involved are definitionally equal but not type-correct at `implicit` transparency, which is
the discipline the implementation notes of
`StacksFrontier/AlgebraicGeometry/Descent/SectionsPullbackComparison/PullbackSection.lean` record.

## References

* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
* [Stacks Project, Tag 0H78](https://stacks.math.columbia.edu/tag/0H78)
* [Stacks Project, Tag 0B8L](https://stacks.math.columbia.edu/tag/0B8L)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry RingedSpaceModuleAdjunction
open Stacks.Ample (IsInvertibleModule nonvanishingLocus)
open Stacks.TensorPowers (natTensorPow)
open Stacks.TensorPowerTrivialize (resTop)
open Stacks.NonvanishingOpen (nonvanishingOpen)
open Stacks.AlgebraicGeometry.ProjChartCocycle (ratioOf ratioOf_eq_of_resTop_eq
  resTop_eq_ratioOf_smul)

universe u

namespace Stacks.AlgebraicGeometry.ProjChartRatioPullback

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

/-- **Stacks Tag 0B8L at the `AlgebraicGeometry.Scheme.Modules.pullback` spelling**: the pullback
of an invertible module along a morphism of schemes is invertible. The instance
`Stacks.InvertiblePullback.isInvertibleModule_pullback` is stated for
`RingedSpaceModuleAdjunction.modulePullback`, which is the same functor but is not found by
instance search from this spelling. -/
instance isInvertibleModule_schemeModulesPullback {X S : Scheme.{u}} (f : X ⟶ S) (M : S.Modules)
    [IsInvertibleModule S M] :
    IsInvertibleModule X ((Scheme.Modules.pullback f).obj M) :=
  Stacks.InvertiblePullback.isInvertibleModule_pullback f M

variable {Y Y' : Scheme.{u}} (j : Y' ⟶ Y)

/-! ### Pulling a global section back -/

/-- The preimage of the largest open is the largest open, as the hypothesis that
`AlgebraicGeometry.pullbackSectionHom` takes on global sections. Named so that the same proof
term appears in every statement below. -/
theorem top_le_preimage_top : (⊤ : Y'.Opens) ≤ j ⁻¹ᵁ (⊤ : Y.Opens) := by simp

/-- **A morphism of modules commutes with restriction, on sections.** The naturality of the
underlying morphism of presheaves of abelian groups, applied to a section. -/
theorem app_map {A B : Y'.Modules} (φ : A ⟶ B) {U U' : Y'.Opens} (i : U' ⟶ U) (a : Γ(A, U)) :
    φ.app U' (A.presheaf.map i.op a) = B.presheaf.map i.op (φ.app U a) := by
  have h := φ.mapPresheaf.naturality i.op
  simpa using DFunLike.congr_fun (congrArg ConcreteCategory.hom h) a

/-- **Restricting the pullback of a section further is pulling it back to the smaller open.**
Both sides are the unit of the pullback-pushforward adjunction followed by one restriction map,
and the two restriction maps agree because the homomorphisms of a poset are unique. -/
theorem map_pullbackSectionHom (M : Y.Modules) (U : Y.Opens) (V V' : Y'.Opens) (i : V' ⟶ V)
    (h : V ≤ j ⁻¹ᵁ U) (h' : V' ≤ j ⁻¹ᵁ U) (a : Γ(M, U)) :
    ((Scheme.Modules.pullback j).obj M).presheaf.map i.op (pullbackSectionHom j M U V h a)
      = pullbackSectionHom j M U V' h' a :=
  (PresheafOfModules.map_comp_apply ((Scheme.Modules.pullback j).obj M).val
      (homOfLE h).op i.op _).symm.trans
    (PresheafOfModules.congr_map_apply _ (Subsingleton.elim _ _) _)

/-- On global sections, pulling a section back is the unit of the pullback-pushforward
adjunction, which is the form the nonvanishing-locus comparison of Stacks Tag 0H78 is stated
in. -/
theorem pullbackSectionHom_top (M : Y.Modules) (t : Γ(M, ⊤)) :
    pullbackSectionHom j M ⊤ ⊤ (top_le_preimage_top j) t
      = Stacks.NonvanishingPullback.pullbackGlobalSection j M t := by
  change ((Scheme.Modules.pullback j).obj M).presheaf.map _ _ = _
  rw [show (homOfLE (top_le_preimage_top j)).op = 𝟙 _ from Subsingleton.elim _ _]
  simp
  rfl

variable (L : Y.Modules) [IsInvertibleModule Y L]

/-- **The comparison `(j^*L) ^⊗ n ≅ j^*(L ^⊗ n)`** at the left-iterated tensor powers
`Stacks.TensorPowers.natTensorPow`: the two readings of the integer tensor powers agree in
nonnegative degree, and between them the comparison is Stacks Tag 01CD iterated,
`Stacks.RelativeVeryAmple.pullbackTensorPowModuleIso`. -/
def pullbackNatTensorPowIso (n : ℕ) :
    (natTensorPow ((Scheme.Modules.pullback j).obj L) n : Y'.Modules) ≅
      (Scheme.Modules.pullback j).obj (natTensorPow L n) :=
  Stacks.AmplePullbackPart1.natTensorPowIsoTensorPowModule Y'
      ((Scheme.Modules.pullback j).obj L) n ≪≫
    (Stacks.RelativeVeryAmple.pullbackTensorPowModuleIso j L n).symm ≪≫
    (Scheme.Modules.pullback j).mapIso
      (Stacks.AmplePullbackPart1.natTensorPowIsoTensorPowModule Y L n).symm

/-- **The pullback of a global section of `L ^⊗ n`**, as a global section of `(j^*L) ^⊗ n`: the
pullback of the section, read through `pullbackNatTensorPowIso`. -/
def pullSection (n : ℕ) (x : Γ(natTensorPow L n, ⊤)) :
    Γ(natTensorPow ((Scheme.Modules.pullback j).obj L) n, ⊤) :=
  (pullbackNatTensorPowIso j L n).inv.app ⊤
    (pullbackSectionHom j (natTensorPow L n) ⊤ ⊤ (top_le_preimage_top j) x)

/-- **The nonvanishing open of a pulled-back section is the preimage of the nonvanishing open.**
Stacks Tag 0H78 computes the nonvanishing locus of the pullback of the section, and the
nonvanishing locus is unchanged by transporting a section along an isomorphism of modules, which
disposes of the comparison `pullbackNatTensorPowIso`. -/
@[ega "II 4.6.13.1" "more general"]
theorem nonvanishingOpen_pullSection (n : ℕ) (t : Γ(natTensorPow L n, ⊤)) :
    nonvanishingOpen Y' (natTensorPow ((Scheme.Modules.pullback j).obj L) n)
        (pullSection j L n t)
      = j ⁻¹ᵁ nonvanishingOpen Y (natTensorPow L n) t := by
  refine TopologicalSpace.Opens.ext ?_
  change nonvanishingLocus _ (pullSection j L n t) = _
  rw [pullSection,
    show (pullbackNatTensorPowIso j L n).inv
      = (pullbackNatTensorPowIso j L n).symm.hom from rfl,
    Stacks.Ample.nonvanishingLocus_congr, pullbackSectionHom_top]
  exact (Stacks.NonvanishingPullback.preimage_nonvanishingLocus j (natTensorPow L n) t).symm

/-- The restriction to `V'` of the pullback of a global section is the pullback of its
restriction to `V`, for `V' ≤ j^{-1}(V)`, read through the comparison isomorphism. -/
theorem resTop_pullSection {n : ℕ} {V : Y.Opens} {V' : Y'.Opens} (hVV' : V' ≤ j ⁻¹ᵁ V)
    (x : Γ(natTensorPow L n, ⊤)) :
    resTop (natTensorPow ((Scheme.Modules.pullback j).obj L) n) (pullSection j L n x) V'
      = (pullbackNatTensorPowIso j L n).inv.app V'
          (pullbackSectionHom j (natTensorPow L n) V V' hVV'
            (resTop (natTensorPow L n) x V)) :=
  ((app_map (pullbackNatTensorPowIso j L n).inv (homOfLE (le_top : V' ≤ ⊤)) _).symm.trans
    (congrArg (fun z => (pullbackNatTensorPowIso j L n).inv.app V' z)
      ((map_pullbackSectionHom j (natTensorPow L n) ⊤ ⊤ V' (homOfLE (le_top : V' ≤ ⊤))
          (top_le_preimage_top j) (le_top.trans (top_le_preimage_top j)) x).trans
        (pullbackSectionHom_map j (natTensorPow L n) ⊤ V le_top V' hVV'
          (le_top.trans (top_le_preimage_top j)) x).symm)))

/-- **The ratio of two sections commutes with pullback.** For a morphism of schemes
`j : Y' ⟶ Y`, an invertible module `L` on `Y`, global sections `t` and `x` of `L ^⊗ n` with `t`
nonvanishing on `V`, and an open `V' ≤ j^{-1}(V)`, the ratio `(j^*x)/(j^*t)` over `V'` is the
restriction along `j` of the ratio `x/t` over `V`.

The ratio is the unique function with `x|_V = (x/t) · t|_V`, so it suffices to push that identity
along pullback of sections: pulling a section back is semilinear over
`AlgebraicGeometry.Scheme.Hom.appLE`, and the comparison isomorphism acts linearly on sections. -/
theorem ratioOf_pullback {n : ℕ} {V : Y.Opens} (t : Γ(natTensorPow L n, ⊤))
    (hV : V ≤ nonvanishingOpen Y (natTensorPow L n) t) (x : Γ(natTensorPow L n, ⊤))
    {V' : Y'.Opens} (hVV' : V' ≤ j ⁻¹ᵁ V)
    (hV' : V' ≤ nonvanishingOpen Y' (natTensorPow ((Scheme.Modules.pullback j).obj L) n)
      (pullSection j L n t)) :
    ratioOf ((Scheme.Modules.pullback j).obj L) (pullSection j L n t) hV' (pullSection j L n x)
      = j.appLE V V' hVV' (ratioOf L t hV x) := by
  refine ratioOf_eq_of_resTop_eq _ _ hV' ?_
  rw [resTop_pullSection j L hVV', resTop_pullSection j L hVV',
    resTop_eq_ratioOf_smul L t hV x, pullbackSectionHom_smul, Scheme.Modules.Hom.app_smul]

end Stacks.AlgebraicGeometry.ProjChartRatioPullback

end
