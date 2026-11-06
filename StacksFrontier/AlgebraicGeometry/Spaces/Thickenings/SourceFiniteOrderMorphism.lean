module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningMorphism.SourceFiniteOrder
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallyUnramifiedEtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallyUnramifiedEtaleDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeSpaceDifferentialsVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.FiniteOrderMorphismEtaleLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.FiniteOrderMorphismRelativeDimension

/-!
# Cartesian morphisms of thickenings of algebraic spaces with a finite-order source

Let

```
X --f--→ Y
|        |
↓        ↓
X' -f'-→ Y'
```

be a commutative square of algebraic spaces over a scheme `S` in which `X ⊂ X'` and `Y ⊂ Y'`
are thickenings, the thickening `X ⊂ X'` is of finite order, and the square identifies `X` with
`Y ×_{Y'} X'`. This is exactly the situation of Stacks 09ZZ, and nothing is assumed about the
order of `Y ⊂ Y'`. This file proves the parts of Stacks 09ZZ which are étale local, (2), (3),
(4), (5) and (6): local finite type, local quasi-finiteness, local finite type of relative
dimension `d`, vanishing of the sheaf of differentials and unramifiedness.

## The reduction

Choose a surjective étale chart `V' → Y'` and a surjective étale chart `U' → X' ×_{Y'} V'`, and
base change both along the two inclusions. The resulting square of schemes `(U ⊂ U') → (V ⊂ V')`
is cartesian, its left vertical map is a finite-order thickening because the order of a
thickening of algebraic spaces is read on étale charts, and its right vertical map is a closed
immersion. For a cartesian square of schemes of that shape
`Stacks.Thickenings.exists_isFiniteOrderThickening_factorization` replaces `V'` by the closed
subscheme `V(I ^ (n + 1))`, through which `U' → V'` factors, and reduces to Stacks 09ZW, whose
finite-order hypothesis is on the target. This is the step the source's proof alludes to with
"by induction on the order of the thickening we may assume that `Y ⊂ Y'` is a first order
thickening": the order of `Y ⊂ Y'` is not bounded in general, but it may be replaced by one which
is.

## Main definitions

* `AlgebraicGeometry.Space.CartesianSourceFiniteOrderMorphismOfThickenings` packages the two
  thickenings, the finite order of the source one, their morphism and the cartesian condition.

## Main results

* `exists_cartesian_surjectiveEtaleCharts`, in the namespace
  `AlgebraicGeometry.Space.CartesianSourceFiniteOrderMorphismOfThickenings`: compatible
  surjective étale charts whose square of schemes is a cartesian morphism of thickenings with
  finite-order source and closed-immersion target.
* `holdsOnEveryEtaleChart_iff_of_cartesianSourceFiniteOrderMorphismOfThickenings`, in the
  namespace `AlgebraicGeometry.Space`: the étale-local engine.
* Parts (2), (3), (4), (5) and (6) of Stacks 09ZZ:
  `isLocallyOfFiniteType_iff`, `isLocallyQuasiFinite_iff`,
  `isLocallyOfFiniteType_and_hasRelativeDimension_iff`, `isZero_sheafOfDifferentials_iff` and
  `isUnramified_iff`, all in the namespace
  `AlgebraicGeometry.Space.CartesianSourceFiniteOrderMorphismOfThickenings`.

## Implementation notes

The structure differs from `AlgebraicGeometry.Space.CartesianFiniteOrderMorphismOfThickenings`
in carrying the finite order of the *source* thickening, as Stacks 09ZZ does, instead of the
target one; by Stacks 09ZX the latter implies the former, so the conversion
`toCartesianSourceFiniteOrderMorphismOfThickenings` in the namespace of that structure makes
every result here apply in that situation too.

The vanishing of `Ω_{X/Y}` in part (5) is that of the sheaf of differentials
`AlgebraicGeometry.Space.sheafOfDifferentials` of Stacks 04CT, translated into formal
unramifiedness by Stacks 04G9. Formal unramifiedness of a morphism of algebraic spaces is read on
a single surjective étale chart, so part (5) uses the charts directly rather than the engine.

## References

* [Stacks Project, Tag 09ZZ](https://stacks.math.columbia.edu/tag/09ZZ)
* [Stacks Project, Tag 09ZW](https://stacks.math.columbia.edu/tag/09ZW)
* [Stacks Project, Tag 09ZX](https://stacks.math.columbia.edu/tag/09ZX)
* [Stacks Project, Tag 04G9](https://stacks.math.columbia.edu/tag/04G9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Thickenings

universe u

namespace AlgebraicGeometry.Space

/-- A cartesian morphism of thickenings of algebraic spaces over `S` whose source thickening is
of finite order: the situation of Stacks 09ZZ. -/
structure CartesianSourceFiniteOrderMorphismOfThickenings
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) where
  /-- The ambient source algebraic space `X'`. -/
  X' : AlgebraicSpaces B S hS
  /-- The ambient target algebraic space `Y'`. -/
  Y' : AlgebraicSpaces B S hS
  /-- The smaller source algebraic space `X ⊂ X'`. -/
  X : Subfunctor X'.1
  /-- The smaller target algebraic space `Y ⊂ Y'`. -/
  Y : Subfunctor Y'.1
  /-- The source inclusion is a thickening of finite order. -/
  sourceFiniteOrder : IsFiniteOrderThickening B S hS X' X
  /-- The target inclusion is a thickening. -/
  targetThickening : IsThickening B S hS Y' Y
  /-- The commutative square `(f, f')` between the two thickenings. -/
  morphism : Arrow.mk X.ι ⟶ Arrow.mk Y.ι
  /-- The square identifies `X` with `Y ×_{Y'} X'`. -/
  cartesian : IsPullback morphism.left X.ι Y.ι morphism.right

/-- A cartesian morphism of thickenings whose target thickening is of finite order has a source
thickening of finite order, by Stacks 09ZX. -/
def CartesianFiniteOrderMorphismOfThickenings.toCartesianSourceFiniteOrderMorphismOfThickenings
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    (M : CartesianFiniteOrderMorphismOfThickenings B S hS) :
    CartesianSourceFiniteOrderMorphismOfThickenings B S hS where
  X' := M.X'
  Y' := M.Y'
  X := M.X
  Y := M.Y
  sourceFiniteOrder := M.sourceFiniteOrder
  targetThickening := M.targetThickening
  morphism := M.morphism
  cartesian := M.cartesian

namespace CartesianSourceFiniteOrderMorphismOfThickenings

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The map `f : X ⟶ Y` between the smaller algebraic spaces. -/
abbrev f (M : CartesianSourceFiniteOrderMorphismOfThickenings B S hS) :
    M.X.toFunctor ⟶ M.Y.toFunctor := M.morphism.left

/-- The map `f' : X' ⟶ Y'` between the ambient algebraic spaces. -/
abbrev f' (M : CartesianSourceFiniteOrderMorphismOfThickenings B S hS) :
    M.X'.1 ⟶ M.Y'.1 := M.morphism.right

/-- The source inclusion is a thickening: a finite-order thickening is one. -/
theorem sourceThickening (M : CartesianSourceFiniteOrderMorphismOfThickenings B S hS) :
    IsThickening B S hS M.X' M.X :=
  M.sourceFiniteOrder.choose_spec.1

/-- The smaller source, as an algebraic space over `S`. -/
abbrev sourceSpace (M : CartesianSourceFiniteOrderMorphismOfThickenings B S hS) :
    AlgebraicSpaces B S hS :=
  ⟨M.X.toFunctor, M.sourceThickening.1.1⟩

/-- The smaller target, as an algebraic space over `S`. -/
abbrev targetSpace (M : CartesianSourceFiniteOrderMorphismOfThickenings B S hS) :
    AlgebraicSpaces B S hS :=
  ⟨M.Y.toFunctor, M.targetThickening.1.1⟩

/-- The morphism of smaller spaces, as a morphism of algebraic spaces. -/
abbrev smallHom (M : CartesianSourceFiniteOrderMorphismOfThickenings B S hS) :
    M.sourceSpace ⟶ M.targetSpace :=
  ObjectProperty.homMk M.f

/-- The ambient morphism, as a morphism of algebraic spaces. -/
abbrev ambientHom (M : CartesianSourceFiniteOrderMorphismOfThickenings B S hS) : M.X' ⟶ M.Y' :=
  ObjectProperty.homMk M.f'

/-- **Compatible étale charts.** A cartesian morphism of thickenings of algebraic spaces with
finite-order source thickening has a surjective étale chart `(u, v, g)` of `f` and a surjective
étale chart `(u', v', g')` of `f'` related by maps of schemes `iU : U ⟶ U'` and `iV : V ⟶ V'`
such that `(iU, g, g', iV)` is a cartesian square of schemes, `iU` is a finite-order thickening
and `iV` is a closed immersion.

The ambient charts are a surjective étale chart `v'` of `Y'` and a surjective étale chart of
`X' ×_{Y'} V'`, and the smaller ones are their base changes along the two inclusions. -/
theorem exists_cartesian_surjectiveEtaleCharts
    (M : CartesianSourceFiniteOrderMorphismOfThickenings B S hS) :
    ∃ (U V U' V' : BigFppfOver B S hS) (u : yoneda.obj U ⟶ M.X.toFunctor)
      (v : yoneda.obj V ⟶ M.Y.toFunctor) (u' : yoneda.obj U' ⟶ M.X'.1)
      (v' : yoneda.obj V' ⟶ M.Y'.1) (g : U ⟶ V) (g' : U' ⟶ V') (iU : U ⟶ U') (iV : V ⟶ V'),
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf u ∧
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf v ∧
      (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf u ∧
      (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf v ∧
      yoneda.map g ≫ v = u ≫ M.f ∧
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf u' ∧
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf v' ∧
      (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf u' ∧
      (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf v' ∧
      yoneda.map g' ≫ v' = u' ≫ M.f' ∧
      Stacks.Thickenings.IsFiniteOrderThickening ((BigFppfOver.toScheme B S hS).map iU) ∧
      _root_.AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map iV) ∧
      IsPullback ((BigFppfOver.toScheme B S hS).map iU) ((BigFppfOver.toScheme B S hS).map g)
        ((BigFppfOver.toScheme B S hS).map g') ((BigFppfOver.toScheme B S hS).map iV) := by
  let F := BigFppfOver.toScheme B S hS
  let Psurjective :=
    MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u}) F
  let Petale := MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u}) F
  have : Psurjective.IsStableUnderComposition :=
    inverseImage_isStableUnderComposition B S hS surjective_isStableUnderComposition.{u}
  have : Petale.IsStableUnderComposition :=
    inverseImage_isStableUnderComposition B S hS etale_isStableUnderComposition.{u}
  have : Psurjective.IsStableUnderBaseChange :=
    inverseImage_isStableUnderBaseChange B S hS inferInstance
  have : Petale.IsStableUnderBaseChange :=
    inverseImage_isStableUnderBaseChange B S hS Etale.etale_isStableUnderBaseChange
  have : Psurjective.presheaf.IsStableUnderComposition :=
    MorphismProperty.relative_isStableUnderComposition Psurjective
  have : Petale.presheaf.IsStableUnderComposition :=
    MorphismProperty.relative_isStableUnderComposition Petale
  have : Psurjective.presheaf.IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange Psurjective
  have : Petale.presheaf.IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange Petale
  obtain ⟨V', v', hv'_surjective, hv'_etale⟩ := M.Y'.property.exists_atlas
  obtain ⟨U', u', hu'_surjective, hu'_etale⟩ := (isAlgebraicSpace_pullback B S hS M.f' v'
    M.X'.property (isAlgebraicSpace_yoneda B S hS V') M.Y'.property).exists_atlas
  have hPullP : IsPullback (pullback.fst M.f' v') (pullback.snd M.f' v') M.f' v' :=
    IsPullback.of_hasPullback _ _
  let uambient := u' ≫ pullback.fst M.f' v'
  have huambient_etale : Petale.presheaf uambient :=
    MorphismProperty.comp_mem _ _ _ hu'_etale
      (MorphismProperty.IsStableUnderBaseChange.of_isPullback hPullP.flip hv'_etale)
  have huambient_surjective : Psurjective.presheaf uambient :=
    MorphismProperty.comp_mem _ _ _ hu'_surjective
      (MorphismProperty.IsStableUnderBaseChange.of_isPullback hPullP.flip hv'_surjective)
  obtain ⟨V, iV, v, target_pullback, hiV⟩ : ∃ (V : BigFppfOver B S hS) (iV : V ⟶ V')
      (v : yoneda.obj V ⟶ M.Y.toFunctor), IsPullback v (yoneda.map iV) M.Y.ι v' ∧
        _root_.AlgebraicGeometry.IsClosedImmersion (F.map iV) :=
    ⟨M.targetThickening.1.2.rep.pullback v', M.targetThickening.1.2.rep.snd v',
      M.targetThickening.1.2.rep.fst v', M.targetThickening.1.2.rep.isPullback v',
      M.targetThickening.1.2.property v' _ _ (M.targetThickening.1.2.rep.isPullback v')⟩
  obtain ⟨U, iU, u, source_pullback, hiU⟩ :=
    exists_finiteOrderThickening_chart_pullback B S hS M.sourceFiniteOrder U' uambient
      huambient_etale
  have hv_etale : Petale.presheaf v :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback target_pullback.flip hv'_etale
  have hv_surjective : Psurjective.presheaf v :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback target_pullback.flip hv'_surjective
  have hu_etale : Petale.presheaf u :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback source_pullback.flip huambient_etale
  have hu_surjective : Psurjective.presheaf u :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback source_pullback.flip
      huambient_surjective
  -- The two horizontal maps of the square of charts, as morphisms of the site.
  let g' := yoneda.preimage (u' ≫ pullback.snd M.f' v')
  have ambient_compat : yoneda.map g' = u' ≫ pullback.snd M.f' v' := by simp [g']
  have hambientComm : yoneda.map g' ≫ v' = uambient ≫ M.f' := by
    rw [ambient_compat]
    simp only [uambient, Category.assoc]
    exact congrArg (fun q => u' ≫ q) hPullP.w.symm
  have hmor : M.f ≫ M.Y.ι = M.X.ι ≫ M.f' := M.morphism.w
  have hsrcw : u ≫ M.X.ι = yoneda.map iU ≫ uambient := source_pullback.w
  have hcomp : (u ≫ M.f) ≫ M.Y.ι = yoneda.map (iU ≫ g') ≫ v' := by
    calc
      (u ≫ M.f) ≫ M.Y.ι = u ≫ M.X.ι ≫ M.f' := by
        rw [Category.assoc, hmor]
      _ = (u ≫ M.X.ι) ≫ M.f' := (Category.assoc _ _ _).symm
      _ = (yoneda.map iU ≫ uambient) ≫ M.f' := by rw [hsrcw]
      _ = yoneda.map iU ≫ yoneda.map g' ≫ v' := by
        rw [Category.assoc, hambientComm]
      _ = yoneda.map (iU ≫ g') ≫ v' := by
        simp only [Functor.map_comp, Category.assoc]
  let g_pre := target_pullback.lift (u ≫ M.f) (yoneda.map (iU ≫ g')) hcomp
  let g := yoneda.preimage g_pre
  have small_compat : u ≫ M.f = yoneda.map g ≫ v := by
    simp [g, g_pre]
  have hg_snd : yoneda.map g ≫ yoneda.map iV = yoneda.map iU ≫ yoneda.map g' := by
    simp [g, g_pre]
  -- Cartesianness of the square of charts, proved in the presheaf category.
  have hUtoY : IsPullback (yoneda.map g ≫ v) (yoneda.map iU) M.Y.ι (yoneda.map g' ≫ v') := by
    rw [← small_compat, hambientComm]
    exact IsPullback.paste_horiz source_pullback M.cartesian
  have hFinalSite : IsPullback g iU iV g' :=
    IsPullback.of_map yoneda (yoneda.map_injective (by simp only [Functor.map_comp]; exact hg_snd))
      (IsPullback.of_right hUtoY hg_snd target_pullback)
  exact ⟨U, V, U', V', u, v, uambient, v', g, g', iU, iV, hu_etale, hv_etale, hu_surjective,
    hv_surjective, small_compat.symm, huambient_etale, hv'_etale, huambient_surjective,
    hv'_surjective, hambientComm, hiU, hiV, (IsPullback.map F hFinalSite).flip⟩

end CartesianSourceFiniteOrderMorphismOfThickenings

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 09ZZ, the étale-local cases.** A property of morphisms of schemes which is étale
local on the source and target holds on every étale chart of the morphism of smaller spaces of a
cartesian morphism of thickenings of algebraic spaces with finite-order source thickening exactly
when it holds on every étale chart of the ambient morphism, as soon as it is invariant under
every cartesian square of schemes whose source vertical map is a finite-order thickening and
whose target vertical map is a closed immersion. -/
theorem holdsOnEveryEtaleChart_iff_of_cartesianSourceFiniteOrderMorphismOfThickenings
    (M : CartesianSourceFiniteOrderMorphismOfThickenings B S hS) (P : MorphismProperty Scheme.{u})
    (hP : IsEtaleLocalOnSourceAndTarget P)
    (hSchemes : ∀ {U U' V V' : Scheme.{u}} (iU : U ⟶ U') (iV : V ⟶ V')
      (g : U ⟶ V) (g' : U' ⟶ V'), Stacks.Thickenings.IsFiniteOrderThickening iU →
      _root_.AlgebraicGeometry.IsClosedImmersion iV → IsPullback iU g g' iV → (P g ↔ P g')) :
    HoldsOnEveryEtaleChart B S hS P M.f ↔ HoldsOnEveryEtaleChart B S hS P M.f' := by
  obtain ⟨U, V, U', V', u, v, u', v', g, g', iU, iV, hu, hv, hus, -, hc, hu', hv', hus', -, hc',
    hiU, hiV, hsq⟩ := M.exists_cartesian_surjectiveEtaleCharts
  have hsmall : HoldsOnEveryEtaleChart B S hS P M.f ↔
      P ((BigFppfOver.toScheme B S hS).map g) :=
    ⟨fun h => h U V u v g hu hv hc, fun hp => (holdsOnEveryEtaleChart_iff_surjectiveChart B S hS P
      hP M.sourceThickening.1.1 M.targetThickening.1.1 M.f).mpr
        ⟨U, V, u, v, g, hu, hv, hus, hc, hp⟩⟩
  have hambient : HoldsOnEveryEtaleChart B S hS P M.f' ↔
      P ((BigFppfOver.toScheme B S hS).map g') :=
    ⟨fun h => h U' V' u' v' g' hu' hv' hc', fun hp => (holdsOnEveryEtaleChart_iff_surjectiveChart
      B S hS P hP M.X'.property M.Y'.property M.f').mpr
        ⟨U', V', u', v', g', hu', hv', hus', hc', hp⟩⟩
  exact hsmall.trans ((hSchemes _ _ _ _ hiU hiV hsq).trans hambient.symm)

namespace CartesianSourceFiniteOrderMorphismOfThickenings

variable {B S hS}

/-- **Stacks 09ZZ, part (2).** In a cartesian morphism of thickenings of algebraic spaces whose
source thickening is of finite order, the map between the smaller spaces is locally of finite
type exactly when the map between the ambient spaces is. -/
@[stacks 09ZZ "part (2): f is locally of finite type iff f' is"]
theorem isLocallyOfFiniteType_iff (M : CartesianSourceFiniteOrderMorphismOfThickenings B S hS) :
    IsLocallyOfFiniteType B S hS M.f ↔ IsLocallyOfFiniteType B S hS M.f' :=
  holdsOnEveryEtaleChart_iff_of_cartesianSourceFiniteOrderMorphismOfThickenings B S hS M
    (@LocallyOfFiniteType.{u}) LocallyOfFiniteType.isEtaleLocalOnSourceAndTarget
    fun iU iV g g' hiU hiV hcart =>
      locallyOfFiniteType_iff_of_isFiniteOrderThickening_source iU iV g g' hiU hiV hcart

/-- **Stacks 09ZZ, part (3).** In a cartesian morphism of thickenings of algebraic spaces whose
source thickening is of finite order, the map between the smaller spaces is locally quasi-finite
exactly when the map between the ambient spaces is. -/
@[stacks 09ZZ "part (3): f is locally quasi-finite iff f' is"]
theorem isLocallyQuasiFinite_iff (M : CartesianSourceFiniteOrderMorphismOfThickenings B S hS) :
    IsLocallyQuasiFinite B S hS M.f ↔ IsLocallyQuasiFinite B S hS M.f' :=
  holdsOnEveryEtaleChart_iff_of_cartesianSourceFiniteOrderMorphismOfThickenings B S hS M _
    locallyOfFiniteType_inf_locallyQuasiFinite_isEtaleLocalOnSourceAndTarget
    fun iU iV g g' hiU hiV hcart =>
      locallyQuasiFinite_iff_of_isFiniteOrderThickening_source iU iV g g' hiU hiV hcart

/-- **Stacks 09ZZ, part (6).** In a cartesian morphism of thickenings of algebraic spaces whose
source thickening is of finite order, the map between the smaller spaces is unramified exactly
when the map between the ambient spaces is. -/
@[stacks 09ZZ "part (6): f is unramified iff f' is"]
theorem isUnramified_iff (M : CartesianSourceFiniteOrderMorphismOfThickenings B S hS) :
    IsUnramified B S hS M.f ↔ IsUnramified B S hS M.f' :=
  holdsOnEveryEtaleChart_iff_of_cartesianSourceFiniteOrderMorphismOfThickenings B S hS M _
    unramified_isEtaleLocalOnSourceAndTarget
    fun iU iV g g' hiU hiV hcart =>
      unramified_iff_of_isFiniteOrderThickening_source iU iV g g' hiU hiV hcart

/-- In a cartesian morphism of thickenings of algebraic spaces whose ambient morphism `f'` is
locally of finite type, `f` has relative dimension `d` exactly when `f'` does: at corresponding
points the two relative dimensions agree by Stacks 04NS, and every point of `X'` comes from a
point of `X`. -/
theorem hasRelativeDimension_iff_of_isLocallyOfFiniteType
    (M : CartesianSourceFiniteOrderMorphismOfThickenings B S hS) (d : ℕ)
    (hf' : IsLocallyOfFiniteType B S hS M.f') :
    HasRelativeDimension d B S hS M.f ↔ HasRelativeDimension d B S hS M.f' := by
  have key (x : points B S hS M.X.toFunctor) :
      HasRelativeDimensionAt (d : ℕ∞) B S hS M.f'
          (pointsMap B S hS M.X.toFunctor M.X.ι x) ↔
        HasRelativeDimensionAt (d : ℕ∞) B S hS M.f x :=
    hasRelativeDimensionAt_iff_of_isPullback B S hS M.cartesian.flip M.X'.property
      M.targetThickening.1.1 M.Y'.property hf' x (d : ℕ∞)
  refine ⟨fun h y => ?_, fun h x => (key x).mp (h _)⟩
  obtain ⟨x, rfl⟩ := (bijective_pointsMap_ι_of_isThickening B S hS M.sourceThickening).2 y
  exact (key x).mpr (h x)

/-- **Stacks 09ZZ, part (4).** In a cartesian morphism of thickenings of algebraic spaces whose
source thickening is of finite order, the map between the smaller spaces is locally of finite
type of relative dimension `d` exactly when the map between the ambient spaces is. -/
@[stacks 09ZZ "part (4): f is locally of finite type of relative dimension d iff f' is, the \
property being the conjunction of local finite type and relative dimension d"]
theorem isLocallyOfFiniteType_and_hasRelativeDimension_iff
    (M : CartesianSourceFiniteOrderMorphismOfThickenings B S hS) (d : ℕ) :
    (IsLocallyOfFiniteType B S hS M.f ∧ HasRelativeDimension d B S hS M.f) ↔
      (IsLocallyOfFiniteType B S hS M.f' ∧ HasRelativeDimension d B S hS M.f') :=
  (and_congr_left' M.isLocallyOfFiniteType_iff).trans
    (and_congr_right (M.hasRelativeDimension_iff_of_isLocallyOfFiniteType d))

/-- In a cartesian morphism of thickenings of algebraic spaces whose source thickening is of
finite order, `f` is formally unramified exactly when `f'` is. Both are read on the compatible
surjective étale charts of `exists_cartesian_surjectiveEtaleCharts`, where they agree by the
scheme case. -/
theorem formallyUnramified_iff (M : CartesianSourceFiniteOrderMorphismOfThickenings B S hS) :
    FormallyUnramified M.f ↔ FormallyUnramified M.f' := by
  obtain ⟨U, V, U', V', u, v, u', v', g, g', iU, iV, hu, hv, hus, hvs, hc, hu', hv', hus', hvs',
    hc', hiU, hiV, hsq⟩ := M.exists_cartesian_surjectiveEtaleCharts
  have hscheme := formallyUnramified_iff_of_isFiniteOrderThickening_source _ _ _ _ hiU hiV hsq
  constructor
  · intro hf
    exact formallyUnramified_of_surjectiveEtaleChart B S hS M.X'.property M.f'
      ⟨U', V', u', v', g', hu', hv', hus', hvs', hc',
        hscheme.mp (holdsOnEveryEtaleChart_of_formallyUnramified B S hS M.f hf U V u v g hu hv
          hc)⟩
  · intro hf'
    exact formallyUnramified_of_surjectiveEtaleChart B S hS M.sourceThickening.1.1 M.f
      ⟨U, V, u, v, g, hu, hv, hus, hvs, hc,
        hscheme.mpr (holdsOnEveryEtaleChart_of_formallyUnramified B S hS M.f' hf' U' V' u' v' g'
          hu' hv' hc')⟩

/-- **Stacks 09ZZ, part (5).** In a cartesian morphism of thickenings of algebraic spaces whose
source thickening is of finite order, the sheaf of differentials `Ω_{X/Y}` of the map between
the smaller spaces vanishes exactly when the sheaf of differentials `Ω_{X'/Y'}` of the map
between the ambient spaces does.

By Stacks 04G9 each vanishing is formal unramifiedness of the corresponding morphism, and
`formallyUnramified_iff` compares those. -/
@[stacks 09ZZ "part (5): Ω_{X/Y} = 0 iff Ω_{X'/Y'} = 0, for the sheaves of differentials of \
Tag 04CT"]
theorem isZero_sheafOfDifferentials_iff
    (M : CartesianSourceFiniteOrderMorphismOfThickenings B S hS) :
    IsZero (sheafOfDifferentials B S hS M.smallHom) ↔
      IsZero (sheafOfDifferentials B S hS M.ambientHom) :=
  (formallyUnramified_iff_isZero_sheafOfDifferentials' B S hS M.smallHom).symm.trans
    (M.formallyUnramified_iff.trans
      (formallyUnramified_iff_isZero_sheafOfDifferentials' B S hS M.ambientHom))

end CartesianSourceFiniteOrderMorphismOfThickenings

end AlgebraicGeometry.Space

end
