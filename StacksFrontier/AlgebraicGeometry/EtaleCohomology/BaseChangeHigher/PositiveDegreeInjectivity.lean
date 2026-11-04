module

public import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.BaseChangeCondition

/-!
# Base change for higher direct images in a positive degree

Let `f : X ⟶ S` be a morphism of schemes and let `n` be an integer, as in the condition
`BC(f, n, q₀)` of [Stacks, Tag 0F02]. [Stacks, Tag 0F03] assumes `BC(f, n, q - 1)` for some
`q ≥ 1` and considers a commutative diagram

```
X  ←--  X'  ←-h-  Y
|f      |f'       |e
S  ←--  S'  ←-g-  T
```

with `X' = X ×_S S'` and `Y = X' ×_{S'} T` and `g` quasi-compact and quasi-separated. For an
abelian sheaf `F` on the small étale site of `T` annihilated by `n` it asserts three things:

1. the base change map `(f')⁻¹ R^q g_* F ⟶ R^q h_* e⁻¹ F` is injective;
2. if `F ⊂ G` with `G` on `T_étale` annihilated by `n`, then the cokernel of the base change
   map of `F` is a subsheaf of the cokernel of the base change map of `G`;
3. if moreover `G` is an injective sheaf of `ℤ/nℤ`-modules, then the cokernel of the base
   change map of `F` is a subsheaf of `R^q h_* e⁻¹ G`.

The source proves all three from one diagram. Choose a short exact sequence
`0 → F → I → Q → 0` with `I` an injective sheaf of `ℤ/nℤ`-modules and consider

```
(f')⁻¹R^{q-1}g_* I ──→ (f')⁻¹R^{q-1}g_* Q ──→ (f')⁻¹R^q g_* F ──→ 0
      |≅                     |≅                    |
R^{q-1}h_* e⁻¹I  ──→ R^{q-1}h_* e⁻¹Q  ──→ R^q h_* e⁻¹F ──→ R^q h_* e⁻¹I
```

whose rows are pieces of the long exact sequences of higher direct images, whose two left
vertical maps are isomorphisms by `BC(f, n, q - 1)`, and whose upper right entry vanishes
because `I` is injective. The four lemma applied to the two left squares gives (1); the
right square identifies the cokernel of the base change map of `F` with a subsheaf of
`R^q h_* e⁻¹ I`, which is (3); and (2) follows by choosing `F ⊂ G ⊂ I`.

This file carries out the three diagram chases of that argument. The degrees are written `q`
and `q + 1` rather than `q - 1` and `q`, so that the source's standing hypothesis `q ≥ 1` is
automatic and the condition appearing is `BC(f, n, q)`; this is a reindexing of the source,
not a restriction of it. The two rows of the diagram, their exactness, and the commutativity
of its right-hand square are bundled as
`Stacks.EtaleCohomology.HigherBaseChangeLadder`, a *hypothesis* of each of the three results.
The commutativity of the left square is not assumed: it is the naturality of the base change
map of [Stacks, Tag 0F02].

In the source the ladder is not a hypothesis — it is built inside the proof from `F` alone.
Nothing here builds one, so **no declaration in this file carries the tag 0F03**; the three
results below are the chases that the tag's proof runs once the ladder is available, and
`Stacks.Cohomology.BaseChange` holds them in the generality in which they are true. What a
construction of the ladder still needs is listed under **What is missing** below.

## Main definitions

* `Stacks.EtaleCohomology.higherBaseChangeSource` and
  `Stacks.EtaleCohomology.higherBaseChangeTarget` — the two functors
  `(f')⁻¹ R^q g_*` and `R^q h_* e⁻¹` the base change map of [Stacks, Tag 0F02] goes between.
* `Stacks.EtaleCohomology.HigherBaseChangeLadder` — the comparison diagram above, for a short
  exact sequence `0 → F → I → Q → 0` of abelian sheaves on the small étale site of `T`.

## Main results

* `Stacks.Cohomology.BaseChange.mono_of_ladder`,
  `Stacks.Cohomology.BaseChange.exact_of_ladder`,
  `Stacks.Cohomology.BaseChange.mono_cokernelDesc_of_ladder` and
  `Stacks.Cohomology.BaseChange.mono_cokernelMap_of_mono_cokernelDesc` — the three diagram
  chases, in an abstract abelian category.
* `Stacks.EtaleCohomology.mono_higherBaseChangeMapAb_app` — part (1) of
  [Stacks, Tag 0F03] given a ladder: the base change map in degree `q + 1` is a
  monomorphism.
* `Stacks.EtaleCohomology.higherBaseChangeMapAb_app_comp_map_eq_zero` — the composite of the
  base change map of `F` with `R^{q+1} h_* e⁻¹ (F ⟶ I)` vanishes, so that the cokernel of the
  base change map of `F` maps canonically to `R^{q+1} h_* e⁻¹ I`.
* `Stacks.EtaleCohomology.mono_cokernelDesc_higherBaseChangeMapAb_app` — part (3) of
  [Stacks, Tag 0F03] given a ladder: that canonical map is a monomorphism.
* `Stacks.EtaleCohomology.mono_cokernelMap_higherBaseChangeMapAb_app` — part (2) of
  [Stacks, Tag 0F03] given two ladders: for `F ⊂ G` the induced map on the cokernels of the
  two base change maps is a monomorphism.

## Implementation notes

The inclusions `⊂` of the source are formalized as monomorphisms, and the two cokernels are
Mathlib's `CategoryTheory.Limits.cokernel`. In part (2) the map between them is
`CategoryTheory.Limits.cokernel.map` applied to the naturality square of the base change map,
and in part (3) the map to `R^{q+1} h_* e⁻¹ G` is `CategoryTheory.Limits.cokernel.desc`
applied to `R^{q+1} h_* e⁻¹ (F ⟶ G)`; both are the canonical maps the source's `⊂` refers to.

The diagram chases are done once and for all in an abstract abelian category, in the section
`Stacks.Cohomology.BaseChange`, and only then instantiated at the sheaf categories: a lemma
whose statement mentions a concrete sheaf category is expensive to elaborate.

Part (2) is proved after part (3), the source deducing the former from the latter.

## What is missing

`HigherBaseChangeLadder` stands for the two rows of the source's diagram together with the
commutativity of its right-hand square. Building one from `BC(f, n, q)`, the two cartesian
squares, quasi-compactness and quasi-separatedness of `g` and the annihilation of `F` by `n`
— which is what the tag asserts — needs the following, none of which this library has.

* `δsource`, `δtarget`, `zero_source`, `zero_target`, `zero_target_comp`, `exact_target` and
  `exact_target_comp` are the connecting maps of the long exact sequences of higher direct
  images and the exactness of the two rows. This is the statement that the higher direct
  images `R^i g_*` form a universal `δ`-functor, the second half of [Stacks, Tag 071F]; this
  library has 071F only in its first half, the computation of `R^i g_*` from a chosen
  injective resolution, recorded against
  `CategoryTheory.InjectiveResolution.isoRightDerivedObj`.
* `epi_δsource` is the surjectivity of the upper connecting map, which holds because
  `R^{q+1} g_* I` vanishes for `I` an injective sheaf of `ℤ/nℤ`-modules. Vanishing of the
  higher direct images of an injective *abelian* sheaf is
  `CategoryTheory.Functor.isZero_rightDerived_obj_injective_succ`; passing between injective
  `ℤ/nℤ`-module sheaves and abelian sheaves is [Stacks, Tag 03FD], the agreement of the two
  cohomologies, which this library has for cohomology but not for higher direct images.
* `comm` is the compatibility of the base change map of [Stacks, Tag 0F02] with the
  connecting maps of the two long exact sequences. The source elides it; it carries no tag.
  It expresses that the derived base change comparison
  `Stacks.EtaleCohomology.smallEtaleDerivedBaseChangeAb` is a morphism of triangulated
  functors, and
  `StacksFrontier/Topology/Sheaves/Cohomology/HigherDirectImage/AbelianBaseChangeMap.lean` has
  `mate`, `derived` and `derived_fac` but no such compatibility.

The short exact sequence `0 → F → I → Q → 0` itself is a further input. It is
[Stacks, Tag 01DU] for the ringed site `(T_étale, ℤ/nℤ)` — this library has 01DU in the shape
`CategoryTheory.IsGrothendieckAbelian.enoughInjectives` — together with the identification of
the abelian sheaves annihilated by `n` with the sheaves of `ℤ/nℤ`-modules, and with
`IsGrothendieckAbelian` for `ℤ/nℤ`-module valued sheaves on the small étale site, whose module
universe `u + 1` does not match the universe of `ℤ/nℤ`, so that Mathlib's
`ModuleCat.isGrothendieckAbelian` does not apply as it stands.

## References

* [Stacks Project, Tag 0F03](https://stacks.math.columbia.edu/tag/0F03)
* [Stacks Project, Tag 0F02](https://stacks.math.columbia.edu/tag/0F02)
* [Stacks Project, Tag 071F](https://stacks.math.columbia.edu/tag/071F)
* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.Cohomology.BaseChange

/-! ### Two diagram lemmas for a comparison ladder

The diagram of [Stacks, Tag 0F03] is a map of three-term complexes

```
A₁ ──a──→ A₂ ──du──→ A₃
|t₁        |t₂        |t₃
B₁ ──b──→ B₂ ──dl──→ B₃ ──c──→ B₄
```

in one abelian category, whose bottom row is exact at `B₂` and at `B₃` and whose upper
connecting map `du` is an epimorphism. The lemmas below extract the two consequences the
source uses: `t₃` is a monomorphism, and the cokernel of `t₃` embeds into `B₄`. -/

section Ladder

variable {A : Type*} [Category* A] [Abelian A]

/-- **The four lemma for a comparison ladder.** If the bottom row `b, dl` is exact, the upper
connecting map `du` is an epimorphism, `t₁` is an epimorphism and `t₂` is a monomorphism, then
the right-hand vertical map `t₃` is a monomorphism. -/
public theorem mono_of_ladder {A₁ A₂ A₃ B₁ B₂ B₃ : A} {a : A₁ ⟶ A₂} {du : A₂ ⟶ A₃}
    {b : B₁ ⟶ B₂} {dl : B₂ ⟶ B₃} {t₁ : A₁ ⟶ B₁} {t₂ : A₂ ⟶ B₂} {t₃ : A₃ ⟶ B₃}
    (hza : a ≫ du = 0) (hzb : b ≫ dl = 0)
    (hsq₁ : t₁ ≫ b = a ≫ t₂) (hsq₂ : t₂ ≫ dl = du ≫ t₃)
    (hbot : (ShortComplex.mk b dl hzb).Exact) (hdu : Epi du)
    (h₁ : Epi t₁) (h₂ : Mono t₂) : Mono t₃ :=
  ShortComplex.mono_of_epi_of_epi_of_mono
    (R₁ := ShortComplex.mk a du hza) (R₂ := ShortComplex.mk b dl hzb)
    { τ₁ := t₁, τ₂ := t₂, τ₃ := t₃, comm₁₂ := hsq₁, comm₂₃ := hsq₂ } hbot hdu h₁ h₂

/-- In a comparison ladder with `du` an epimorphism, the right-hand vertical map `t₃` composed
with the next map `c` of the bottom row vanishes, because `dl ≫ c` does. -/
public theorem ladder_comp_eq_zero {A₂ A₃ B₂ B₃ B₄ : A} {du : A₂ ⟶ A₃} {dl : B₂ ⟶ B₃}
    {c : B₃ ⟶ B₄} {t₂ : A₂ ⟶ B₂} {t₃ : A₃ ⟶ B₃} (hzc : dl ≫ c = 0)
    (hsq : t₂ ≫ dl = du ≫ t₃) [Epi du] : t₃ ≫ c = 0 := by
  rw [← cancel_epi du, ← Category.assoc, ← hsq, Category.assoc, hzc, comp_zero, comp_zero]

/-- In a comparison ladder whose bottom row is exact at `B₃` and whose maps `du` and `t₂` are
epimorphisms, the pair `t₃, c` is exact: the image of `t₃` is the image of `dl`, since
`du ≫ t₃ = t₂ ≫ dl` with `du` and `t₂` epimorphisms. -/
public theorem exact_of_ladder {A₂ A₃ B₂ B₃ B₄ : A} {du : A₂ ⟶ A₃} {dl : B₂ ⟶ B₃}
    {c : B₃ ⟶ B₄} {t₂ : A₂ ⟶ B₂} {t₃ : A₃ ⟶ B₃} (hzc : dl ≫ c = 0)
    (hsq : t₂ ≫ dl = du ≫ t₃) (hbot : (ShortComplex.mk dl c hzc).Exact) [Epi du] [Epi t₂] :
    (ShortComplex.mk t₃ c (ladder_comp_eq_zero hzc hsq)).Exact := by
  have hz₀ : (t₂ ≫ dl) ≫ c = 0 := by simp [hzc]
  have h₀ : (ShortComplex.mk (t₂ ≫ dl) c hz₀).Exact :=
    (ShortComplex.exact_iff_of_epi_of_isIso_of_mono
      (S₁ := ShortComplex.mk (t₂ ≫ dl) c hz₀) (S₂ := ShortComplex.mk dl c hzc)
      { τ₁ := t₂, τ₂ := 𝟙 _, τ₃ := 𝟙 _, comm₁₂ := by simp, comm₂₃ := by simp }).2 hbot
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono
    (S₁ := ShortComplex.mk (t₂ ≫ dl) c hz₀)
    (S₂ := ShortComplex.mk t₃ c (ladder_comp_eq_zero hzc hsq))
    { τ₁ := du, τ₂ := 𝟙 _, τ₃ := 𝟙 _, comm₁₂ := by simpa using hsq.symm,
      comm₂₃ := by simp }).1 h₀

/-- In a comparison ladder as in `exact_of_ladder`, the cokernel of the right-hand vertical
map `t₃` embeds into the target `B₄` of the next map of the bottom row. -/
public theorem mono_cokernelDesc_of_ladder {A₂ A₃ B₂ B₃ B₄ : A} {du : A₂ ⟶ A₃} {dl : B₂ ⟶ B₃}
    {c : B₃ ⟶ B₄} {t₂ : A₂ ⟶ B₂} {t₃ : A₃ ⟶ B₃} (hzc : dl ≫ c = 0)
    (hsq : t₂ ≫ dl = du ≫ t₃) (hbot : (ShortComplex.mk dl c hzc).Exact) [Epi du] [Epi t₂] :
    Mono (cokernel.desc t₃ c (ladder_comp_eq_zero hzc hsq)) :=
  (exact_of_ladder hzc hsq hbot).mono_cokernelDesc

/-- If the cokernel of `t₃` embeds into `B₄` through a map which factors through the cokernel
of `t₃'`, then the induced map from the cokernel of `t₃` to the cokernel of `t₃'` is a
monomorphism. -/
public theorem mono_cokernelMap_of_mono_cokernelDesc {A₃ A₃' B₃ B₃' B₄ : A}
    {t₃ : A₃ ⟶ B₃} {t₃' : A₃' ⟶ B₃'} {u : A₃ ⟶ A₃'} {v : B₃ ⟶ B₃'}
    {wF : B₃ ⟶ B₄} {wG : B₃' ⟶ B₄} (hcomm : t₃ ≫ v = u ≫ t₃')
    (hw : v ≫ wG = wF) (hzF : t₃ ≫ wF = 0) (hzG : t₃' ≫ wG = 0)
    (hmono : Mono (cokernel.desc t₃ wF hzF)) :
    Mono (cokernel.map t₃ t₃' u v hcomm) := by
  have key : cokernel.map t₃ t₃' u v hcomm ≫ cokernel.desc t₃' wG hzG =
      cokernel.desc t₃ wF hzF := by
    refine (cancel_epi (cokernel.π t₃)).1 ?_
    simp [hw]
  have : Mono (cokernel.map t₃ t₃' u v hcomm ≫ cokernel.desc t₃' wG hzG) := key ▸ hmono
  exact mono_of_mono _ (cokernel.desc t₃' wG hzG)

end Ladder

end Stacks.Cohomology.BaseChange

namespace Stacks.EtaleCohomology

/-- The source `(f')⁻¹ R^q g_*` of the base change map of [Stacks, Tag 0F02] in degree `q`. -/
public abbrev higherBaseChangeSource {X' S' T : Scheme.{u}} (f' : X' ⟶ S') (g : T ⟶ S')
    (q : ℕ) :
    Sheaf (smallEtaleTopology T) Ab.{u + 1} ⥤ Sheaf (smallEtaleTopology X') Ab.{u + 1} :=
  (smallEtalePushforwardAb g).rightDerived q ⋙ smallEtalePullbackAb f'

/-- The target `R^q h_* e⁻¹` of the base change map of [Stacks, Tag 0F02] in degree `q`. -/
public abbrev higherBaseChangeTarget {X' Y T : Scheme.{u}} (h : Y ⟶ X') (e : Y ⟶ T) (q : ℕ) :
    Sheaf (smallEtaleTopology T) Ab.{u + 1} ⥤ Sheaf (smallEtaleTopology X') Ab.{u + 1} :=
  smallEtalePullbackAb e ⋙ (smallEtalePushforwardAb h).rightDerived q

/-- **The comparison diagram of [Stacks, Tag 0F03]** attached to a short exact sequence
`0 → F → I → Q → 0` of abelian sheaves on the small étale site of `T`, for a commutative
square `h ≫ f' = e ≫ g`, in degrees `q` and `q + 1`:

```
(f')⁻¹R^q g_* I ──→ (f')⁻¹R^q g_* Q ──δsource──→ (f')⁻¹R^{q+1} g_* F
      |                   |                            |
R^q h_* e⁻¹I  ──→  R^q h_* e⁻¹Q  ──δtarget──→ R^{q+1}h_* e⁻¹F ──→ R^{q+1}h_* e⁻¹I
```

Its horizontal maps are those of the long exact sequences of higher direct images attached to
the short exact sequence, its vertical maps are the base change maps of [Stacks, Tag 0F02],
and `epi_δsource` records the vanishing of `R^{q+1} g_* I`. The commutativity of the left
square is the naturality of the base change map and is not part of the data. -/
public structure HigherBaseChangeLadder {X' S' T Y : Scheme.{u}} (f' : X' ⟶ S') (g : T ⟶ S')
    (h : Y ⟶ X') (e : Y ⟶ T) (w : h ≫ f' = e ≫ g) (q : ℕ)
    {F I Q : Sheaf (smallEtaleTopology T) Ab.{u + 1}} (α : F ⟶ I) (γ : I ⟶ Q) where
  /-- The connecting map `(f')⁻¹R^q g_* Q ⟶ (f')⁻¹R^{q+1} g_* F` of the upper row. -/
  δsource : (higherBaseChangeSource f' g q).obj Q ⟶ (higherBaseChangeSource f' g (q + 1)).obj F
  /-- The connecting map `R^q h_* e⁻¹Q ⟶ R^{q+1}h_* e⁻¹F` of the lower row. -/
  δtarget : (higherBaseChangeTarget h e q).obj Q ⟶ (higherBaseChangeTarget h e (q + 1)).obj F
  /-- The upper row is a complex at `(f')⁻¹R^q g_* Q`. -/
  zero_source : (higherBaseChangeSource f' g q).map γ ≫ δsource = 0
  /-- The lower row is a complex at `R^q h_* e⁻¹Q`. -/
  zero_target : (higherBaseChangeTarget h e q).map γ ≫ δtarget = 0
  /-- The lower row is a complex at `R^{q+1}h_* e⁻¹F`. -/
  zero_target_comp : δtarget ≫ (higherBaseChangeTarget h e (q + 1)).map α = 0
  /-- The lower row is exact at `R^q h_* e⁻¹Q`. -/
  exact_target :
    (ShortComplex.mk ((higherBaseChangeTarget h e q).map γ) δtarget zero_target).Exact
  /-- The lower row is exact at `R^{q+1}h_* e⁻¹F`. -/
  exact_target_comp :
    (ShortComplex.mk δtarget ((higherBaseChangeTarget h e (q + 1)).map α)
      zero_target_comp).Exact
  /-- The upper connecting map is surjective, `R^{q+1} g_* I` vanishing. -/
  epi_δsource : Epi δsource
  /-- The base change maps commute with the two connecting maps. -/
  comm : (higherBaseChangeMapAb f' g h e w q).app Q ≫ δtarget =
    δsource ≫ (higherBaseChangeMapAb f' g h e w (q + 1)).app F

section Results

variable {X S S' X' T Y : Scheme.{u}} (f : X ⟶ S) (n : ℤ) (q : ℕ)
  (s : S' ⟶ S) (p : X' ⟶ X) (f' : X' ⟶ S') (g : T ⟶ S') (h : Y ⟶ X') (e : Y ⟶ T)

/-- **The cokernel of the base change map of `F` maps to `R^{q+1} h_* e⁻¹ I`.** Given a
comparison diagram of [Stacks, Tag 0F03] for a short exact sequence `0 → F → I → Q → 0`, the
composite of the base change map `(f')⁻¹R^{q+1} g_* F ⟶ R^{q+1}h_* e⁻¹F` with
`R^{q+1}h_* e⁻¹(α)` vanishes, because the upper connecting map is surjective and the lower
row is a complex. -/
public theorem higherBaseChangeMapAb_app_comp_map_eq_zero (sq : IsPullback h e f' g)
    {F I Q : Sheaf (smallEtaleTopology T) Ab.{u + 1}} (α : F ⟶ I) (γ : I ⟶ Q)
    (L : HigherBaseChangeLadder f' g h e sq.w q α γ) :
    (higherBaseChangeMapAb f' g h e sq.w (q + 1)).app F ≫
      (higherBaseChangeTarget h e (q + 1)).map α = 0 := by
  have := L.epi_δsource
  exact Stacks.Cohomology.BaseChange.ladder_comp_eq_zero L.zero_target_comp L.comm

/-- **Part (1) of [Stacks, Tag 0F03], given the comparison diagram of its proof.** With
`f : X ⟶ S` and `n` as in [Stacks, Tag 0F02], assume `BC(f, n, q)`. Consider a commutative
diagram

```
X  ←--  X'  ←-h-  Y
|f      |f'       |e
S  ←--  S'  ←-g-  T
```

with `X' = X ×_S S'` and `Y = X' ×_{S'} T` and `g` quasi-compact and quasi-separated, and let
`F` be an abelian sheaf on the small étale site of `T` annihilated by `n`. Then the base
change map `(f')⁻¹ R^{q+1} g_* F ⟶ R^{q+1} h_* e⁻¹ F` is injective.

The extra hypothesis is the comparison diagram for a short exact sequence `0 → F → I → Q → 0`
whose outer terms are annihilated by `n`. The source builds one rather than assuming it, so
this is weaker than the tag and carries no tag attribute; see the module docstring for what a
construction still needs. Given the diagram, the conclusion is the four lemma applied to the
two left squares, the left vertical maps being isomorphisms by `BC(f, n, q)` and the
commutativity of the first square being the naturality of the base change map. -/
public theorem mono_higherBaseChangeMapAb_app (hbc : BaseChangeHolds f n (q : ℤ))
    (sq₁ : IsPullback p f' f s) (sq : IsPullback h e f' g)
    [QuasiCompact g] [QuasiSeparated g]
    {F I Q : Sheaf (smallEtaleTopology T) Ab.{u + 1}} (α : F ⟶ I) (γ : I ⟶ Q)
    (_hF : ∀ (U : T.Etale) (x : F.obj.obj (Opposite.op U)), n • x = 0)
    (hI : ∀ (U : T.Etale) (x : I.obj.obj (Opposite.op U)), n • x = 0)
    (hQ : ∀ (U : T.Etale) (x : Q.obj.obj (Opposite.op U)), n • x = 0)
    (L : HigherBaseChangeLadder f' g h e sq.w q α γ) :
    Mono ((higherBaseChangeMapAb f' g h e sq.w (q + 1)).app F) := by
  have h₁ : IsIso ((higherBaseChangeMapAb f' g h e sq.w q).app I) :=
    hbc s p f' sq₁ g h e sq I hI q le_rfl
  have h₂ : IsIso ((higherBaseChangeMapAb f' g h e sq.w q).app Q) :=
    hbc s p f' sq₁ g h e sq Q hQ q le_rfl
  exact Stacks.Cohomology.BaseChange.mono_of_ladder L.zero_source L.zero_target
    ((higherBaseChangeMapAb f' g h e sq.w q).naturality γ).symm L.comm
    L.exact_target L.epi_δsource inferInstance inferInstance

/-- **Part (3) of [Stacks, Tag 0F03], given the comparison diagram of its proof.** In the
situation of part (1), if `F ⊂ G` with `G` an injective sheaf of `ℤ/nℤ`-modules, then

`Coker((f')⁻¹ R^{q+1} g_* F ⟶ R^{q+1} h_* e⁻¹ F) ⊂ R^{q+1} h_* e⁻¹ G`.

Here `G` is the middle term `I` of the short exact sequence `0 → F → I → Q → 0` of the
comparison diagram, the injectivity of `G` entering through the surjectivity of the upper
connecting map; the inclusion is the canonical map induced by `R^{q+1} h_* e⁻¹(α)`, which
`higherBaseChangeMapAb_app_comp_map_eq_zero` shows is defined. The conclusion holds because
the image of the base change map of `F` is the image of the lower connecting map, the upper
connecting map and the base change map of `Q` being surjective. The comparison diagram is a
hypothesis rather than a construction, so this carries no tag attribute. -/
public theorem mono_cokernelDesc_higherBaseChangeMapAb_app (hbc : BaseChangeHolds f n (q : ℤ))
    (sq₁ : IsPullback p f' f s) (sq : IsPullback h e f' g)
    [QuasiCompact g] [QuasiSeparated g]
    {F I Q : Sheaf (smallEtaleTopology T) Ab.{u + 1}} (α : F ⟶ I) (γ : I ⟶ Q)
    (_hF : ∀ (U : T.Etale) (x : F.obj.obj (Opposite.op U)), n • x = 0)
    (_hI : ∀ (U : T.Etale) (x : I.obj.obj (Opposite.op U)), n • x = 0)
    (hQ : ∀ (U : T.Etale) (x : Q.obj.obj (Opposite.op U)), n • x = 0)
    (L : HigherBaseChangeLadder f' g h e sq.w q α γ) :
    Mono (cokernel.desc ((higherBaseChangeMapAb f' g h e sq.w (q + 1)).app F)
      ((higherBaseChangeTarget h e (q + 1)).map α)
      (higherBaseChangeMapAb_app_comp_map_eq_zero q f' g h e sq α γ L)) := by
  have h₂ : IsIso ((higherBaseChangeMapAb f' g h e sq.w q).app Q) :=
    hbc s p f' sq₁ g h e sq Q hQ q le_rfl
  have := L.epi_δsource
  exact Stacks.Cohomology.BaseChange.mono_cokernelDesc_of_ladder L.zero_target_comp L.comm
    L.exact_target_comp

/-- **Part (2) of [Stacks, Tag 0F03], given the comparison diagrams of its proof.** In the
situation of part (1), if `F ⊂ G` with `G` an abelian sheaf on the small étale site of `T`
annihilated by `n`, then

`Coker((f')⁻¹R^{q+1}g_* F → R^{q+1}h_* e⁻¹F) ⊂ Coker((f')⁻¹R^{q+1}g_* G → R^{q+1}h_* e⁻¹G)`,

the inclusion being the map induced on cokernels by the naturality square of the base change
map. As in the source, the hypotheses transcribe the choice `F ⊂ G ⊂ I` with `I` an injective
sheaf of `ℤ/nℤ`-modules: the two comparison diagrams are those of the short exact sequences
`0 → F → I → Q_F → 0` and `0 → G → I → Q_G → 0`, with the same middle term `I`, and the
inclusion of `F` in `I` is the composite of `i : F ⟶ G` with `k : G ⟶ I`. The conclusion
follows from part (3) for `F ⊂ I`, since that embedding of the cokernel of the base change map
of `F` into `R^{q+1} h_* e⁻¹ I` factors through the cokernel of the base change map of `G`.
The two comparison diagrams are hypotheses rather than constructions, so this carries no tag
attribute. -/
public theorem mono_cokernelMap_higherBaseChangeMapAb_app (hbc : BaseChangeHolds f n (q : ℤ))
    (sq₁ : IsPullback p f' f s) (sq : IsPullback h e f' g)
    [QuasiCompact g] [QuasiSeparated g]
    {F G I QF QG : Sheaf (smallEtaleTopology T) Ab.{u + 1}} (i : F ⟶ G) (k : G ⟶ I)
    (γF : I ⟶ QF) (γG : I ⟶ QG) (_hi : Mono i)
    (_hF : ∀ (U : T.Etale) (x : F.obj.obj (Opposite.op U)), n • x = 0)
    (_hG : ∀ (U : T.Etale) (x : G.obj.obj (Opposite.op U)), n • x = 0)
    (_hI : ∀ (U : T.Etale) (x : I.obj.obj (Opposite.op U)), n • x = 0)
    (hQF : ∀ (U : T.Etale) (x : QF.obj.obj (Opposite.op U)), n • x = 0)
    (_hQG : ∀ (U : T.Etale) (x : QG.obj.obj (Opposite.op U)), n • x = 0)
    (LF : HigherBaseChangeLadder f' g h e sq.w q (i ≫ k) γF)
    (LG : HigherBaseChangeLadder f' g h e sq.w q k γG) :
    Mono (cokernel.map ((higherBaseChangeMapAb f' g h e sq.w (q + 1)).app F)
      ((higherBaseChangeMapAb f' g h e sq.w (q + 1)).app G)
      ((higherBaseChangeSource f' g (q + 1)).map i)
      ((higherBaseChangeTarget h e (q + 1)).map i)
      ((higherBaseChangeMapAb f' g h e sq.w (q + 1)).naturality i).symm) := by
  have hw : (higherBaseChangeTarget h e (q + 1)).map i ≫
      (higherBaseChangeTarget h e (q + 1)).map k =
      (higherBaseChangeTarget h e (q + 1)).map (i ≫ k) :=
    ((higherBaseChangeTarget h e (q + 1)).map_comp i k).symm
  refine Stacks.Cohomology.BaseChange.mono_cokernelMap_of_mono_cokernelDesc _ hw
    (higherBaseChangeMapAb_app_comp_map_eq_zero q f' g h e sq (i ≫ k) γF LF)
    (higherBaseChangeMapAb_app_comp_map_eq_zero q f' g h e sq k γG LG) ?_
  exact mono_cokernelDesc_higherBaseChangeMapAb_app f n q s p f' g h e hbc sq₁ sq (i ≫ k) γF
    _hF _hI hQF LF

end Results

end Stacks.EtaleCohomology

end
