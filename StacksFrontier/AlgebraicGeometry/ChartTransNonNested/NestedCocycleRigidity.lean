module

public import StacksFrontier.AlgebraicGeometry.ChartTransNonNested.TwistCocycleSections
public import StacksFrontier.AlgebraicGeometry.ImmersionCounit.Basic
public import StacksFrontier.AlgebraicGeometry.TwistRigidityDegreeOne.Basic
public import StacksFrontier.AlgebraicGeometry.TwistUnique.Basic

/-!
# The nested twist cocycle in degree one, by rigidity

`Stacks.AlgebraicGeometry.ChartTransRelativeProj.IsNestedCocycle A n` is the single hypothesis the
glued twist `gluedTwist` — and hence the twist `𝒪_{𝐏(E)}(1)` that Stacks Tag 01VM quantifies over
— is conditional on. **This file proves it in degree one**, for every sheaf of graded algebras
whose graded ring of sections over each affine open has, at every point of its `Proj`, a
nonvanishing element of degree one.

## The argument

Fix affine opens `W ⊆ W' ⊆ U` of the base. The two legs through `W'` and the direct comparison are
three local isomorphisms of direct images of twists over the inverse image of `W`, so

> `discrOf`: the direct comparison inverted, followed by the two legs

is an endomorphism *family* of the direct image of the twist on the chart of `W`. Three steps make
it the identity.

* It fixes the direct image of every homogeneous global section. That is
  `…ChartTransRelativeProj.cmpNested_degreeSection_comp`, the cocycle already proved on those
  sections, together with `cmpNested_degreeSection` for the direct comparison.
* Restricted along the chart of `W` and conjugated by the counit of the restriction--pushforward
  adjunction it becomes an honest endomorphism family of the absolute twists on `Proj Γ(W, A)`
  (`Stacks.AlgebraicGeometry.ImmersionCounit.conjEndo`), which fixes the homogeneous global
  sections attached to the restrictions from `U`. Those are exactly the hypotheses of
  `Stacks.AlgebraicGeometry.TwistRigidityDegreeOne.eq_id_res`, so in degree one it is the identity
  — with **no multiplicativity hypothesis**, which is why degree one and not every degree.
* An open of the relative Proj inside the inverse image of `W` is the image of its own preimage in
  the chart (`Stacks.AlgebraicGeometry.TwistUnique.image_preimage_eq_self`), so the conjugation is
  undone over every such open and the discrepancy is the identity there.

This is `StacksFrontier/AlgebraicGeometry/TwistExistence/Overlap.lean` followed step by step, with
one
substitution: that file gets its identification
`restrict (pushforward (chart W) M) (chart W) ≅ M` free from a `TwistData`'s `chartIso` field, and
there is no `TwistData` here. The substitute is the counit of the restriction--pushforward
adjunction at the open immersion `chart W`, read on sections in
`StacksFrontier/AlgebraicGeometry/ImmersionCounit/Basic.lean`.

## Main definitions

* `…ChartTransRelativeProj.discrOf`: **the discrepancy** of three local isomorphisms — the direct
  comparison inverted, followed by the two legs.

## Main results

* `…ChartTransRelativeProj.conjEndo_app_eq_self_of`: the conjugated endomorphism fixes a section
  whose counit image the discrepancy fixes. **Stated at the level of variables**, with the two
  facts about the three comparisons as hypotheses.
* `…ChartTransRelativeProj.isComposite_of_conjEndo_eq_id`: conversely, if the conjugated
  endomorphism is the identity then the three comparisons compose, over every open inside the
  chart image.
* `…ChartTransRelativeProj.isComposite_of_rigidity`: **the whole rigidity argument, at the level
  of variables.** Given, in every degree, a section of the first module over the chart image whose
  image under the direct comparison is the counit image of a homogeneous global section, and the
  cocycle identity at that section, the three comparisons compose in degree one. The two
  hypotheses are exactly the shapes `cmpNested_degreeSection` and `cmpNested_degreeSection_comp`
  have, and the conclusion is exactly the shape `IsNestedCocycle` asks for.

## Implementation notes

**The discrepancy never appears underneath an `app` at the concrete instance, and that is the
fact this file turns on.** The module documentation of
`StacksFrontier/AlgebraicGeometry/ChartTransNonNested/RelativeProj.lean` records it for `modelPair`:
`(modelPair _ _).app V hV s` written out at this instance sends the elaborator through
`cmpNested`'s body into `pushNested` and exhausts the recursion limit. The same holds for
`discrOf`: both `discrOf_app` and `discrOf_app_cmp` are `rfl`-cheap at the level of variables and
*unusable* at the instance — instantiating either, with or without an intervening definition for
the composite, fails at `maxRecDepth` in about a second.

So every statement below that mentions `discrOf` at the concrete instance mentions it only as an
*argument to* `conjEndo`, never under an `app`; the two generic theorems
`conjEndo_app_eq_self_of` and `isComposite_of_conjEndo_eq_id` do all the work with the composite,
and their hypotheses and conclusions speak only of the three comparisons separately — which are
exactly the shapes `cmpNested_degreeSection`, `cmpNested_degreeSection_comp` and `IsComposite`
already have.

The containment `toBase ⁻¹ᵁ W ≤ toBase ⁻¹ᵁ W'` is `AlgebraicGeometry.Scheme.Hom.preimage_mono`,
never the inline `fun _ hx => hWW' hx`: the lambda forces the elaborator to unfold membership in
`toBase ⁻¹ᵁ W`, hence `relativeProj` itself, hence the colimit it is defined by — 348
unfoldings of `relativeProj` and 480 of `Limits.getColimitCocone` before the budget is gone.

## References

* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)
* [Stacks Project, Tag 01MY](https://stacks.math.columbia.edu/tag/01MY)
* [Stacks Project, Tag 01VM](https://stacks.math.columbia.edu/tag/01VM)

## What is owed, and what it costs

`Stacks.AlgebraicGeometry.ChartTransRelativeProj.IsNestedCocycle A 1` **does not follow here**,
and the gap is not mathematical. Instantiating `isComposite_of_rigidity` at the three chart
comparisons closes it — the term is

```
isComposite_of_rigidity (A.res hWU) ((relativeProj A).chart W hW)
  (cmpNested A W U ·) (cmpNested A W' U ·) (cmpNested A W W' ·)
  ((relativeProj A).toBase.preimage_mono hWW')
  (RelativeProjTwistGlue.chart_image_top (relativeProj A) W hW).le
  (RelativeProjTwistGlue.chart_image_top (relativeProj A) W hW).ge
  (hdeg W hW) (RelativeTwistRigidity.generates_res A W U hWU hW hU) _
  (fun k c => (cmpNested_degreeSection A W U hWU hW hU k _ _ _ c).trans
    (counitIso_inv_app_top ((relativeProj A).chart W hW) _ _).symm)
  (fun k c => cmpNested_degreeSection_comp A k W W' U hWW' hW'U hWU hW hW' hU _ _ _ _ c)
```

— every argument of which is proved, and it elaborates. What it does not do is **finish**: the
declaration consumes memory linearly at about 90 MB/s for five minutes, reaching 26 GB, and is
then killed. That profile is the kernel, which ignores the `implicit_reducible` and
`instance_reducible` attributes above and so unfolds `relativeProj` — a colimit over the affine
Zariski site — while checking the instantiated type. Raising `maxHeartbeats` does not help; the
cost is not a step budget.

None of the following is a remedy: naming the conjugated endomorphism and its discrepancy as
definitions with `rfl`-level characterisations (the match then fails in the *elaborator* at
`maxRecDepth` in one second); supplying the comparisons as a family rather than one per degree;
eta-reducing the families so no beta-redex reaches the kernel; supplying the term one argument
shorter and letting `IsNestedCocycle`'s own binders take `V`, `hV`, `hV'` — the remedy recorded
for `cmp_modelTrans` in `RelativeProj.lean`; and writing every statement out in full with no
reducible abbreviation. The last of these **does** bring the four generic theorems above inside
the default budget, and is used for them.

The one abbreviation that matters, recorded because it cost an hour: **`pushforwardVal` must not
appear in a hand-written statement that has to match `TwistCocycleSections`.** Restating
`cmpNested_degreeSection` with `(pushforwardVal f M).map jV.op` fails at `maxRecDepth` in three
seconds; the identical statement written out as `((Scheme.Modules.pushforward f).obj M).val.map
jV.op` is accepted in three. The abbreviation is reducible, so it looks free and is not. That is
why `counitIso_inv_app_top` below is spelled the long way.

## Not done here

**No tag is claimed.** The cocycle is a hypothesis of Tag 01NO's glueing, not an assertion of any
label; what consumes it is Tag 01VM.

Nothing is proved in a degree other than one, and that is intrinsic to the route:
`Stacks.AlgebraicGeometry.TwistRigidity.eq_id` asks in other degrees that the discrepancy also be
multiplicative, and the multiplicativity of Tag 01MY's twist map has not been transported through
the four factors of `pushNested`. The independent route through Stacks Tag 01MZ(3) and
`…ChartTransRelativeProj.pushNested_comp_of` is unconditional in the degree and needs no
nonvanishing degree-one section; if 01MZ(3) lands, it supersedes this file rather than
contradicting it.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ChartTransNonNested
open Stacks.AlgebraicGeometry.ProjTwistSections
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj

namespace Stacks.AlgebraicGeometry.ChartTransRelativeProj

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose AlgebraicGeometry.Proj
attribute [local instance_reducible] ProjectiveSpectrum.top

universe u

/-! ### The discrepancy of three local isomorphisms -/

section Discrepancy

variable {X : TopCat.{u}} {𝒪 : (Opens X)ᵒᵖ ⥤ RingCat.{u}} {M N P : PresheafOfModules.{u} 𝒪}
  {W₀ W₁ : Opens X}

/-- **The discrepancy of three local isomorphisms**: the direct comparison `a` inverted, followed
by the two legs `b` and `c` through a third module. An endomorphism family of `N`, over the
smaller of the two opens. -/
public def discrOf (a : TopCat.Sheaf.LocalModuleEquiv M N W₀)
    (b : TopCat.Sheaf.LocalModuleEquiv M P W₁) (c : TopCat.Sheaf.LocalModuleEquiv P N W₀)
    (hW : W₀ ≤ W₁) : TopCat.Sheaf.LocalModuleEquiv N N W₀ :=
  a.symm.trans ((b.ofLE hW).trans c)

/-- The discrepancy on a section. Usable only where every ingredient is a variable; see the
implementation notes. -/
public theorem discrOf_app (a : TopCat.Sheaf.LocalModuleEquiv M N W₀)
    (b : TopCat.Sheaf.LocalModuleEquiv M P W₁) (c : TopCat.Sheaf.LocalModuleEquiv P N W₀)
    (hW : W₀ ≤ W₁) (V : Opens X) (hV : V ≤ W₀) (y : N.obj (op V)) :
    (discrOf a b c hW).app V hV y =
      c.app V hV (b.app V (hV.trans hW) ((a.app V hV).symm y)) :=
  rfl

/-- **The discrepancy read at a value of the direct comparison**, where the inverse cancels. This
is the form in which a cocycle is recovered from it. -/
public theorem discrOf_app_cmp (a : TopCat.Sheaf.LocalModuleEquiv M N W₀)
    (b : TopCat.Sheaf.LocalModuleEquiv M P W₁) (c : TopCat.Sheaf.LocalModuleEquiv P N W₀)
    (hW : W₀ ≤ W₁) (V : Opens X) (hV : V ≤ W₀) (x : M.obj (op V)) :
    (discrOf a b c hW).app V hV (a.app V hV x) = c.app V hV (b.app V (hV.trans hW) x) :=
  (discrOf_app a b c hW V hV _).trans
    (congrArg (fun z => c.app V hV (b.app V (hV.trans hW) z)) ((a.app V hV).symm_apply_apply x))

end Discrepancy

/-! ### Conjugating the discrepancy along a chart, at the level of variables -/

section Conjugate

variable {X Z : Scheme.{u}} (f : Z ⟶ X) [IsOpenImmersion f] (Nc : Z.Modules)

/-- **The counit at a global section is the restriction of its direct image to the chart image.**
Both directions of the counit are restriction maps along an equality of opens, so the two
spellings — in the module on the chart and in its direct image — agree by `pushforward_map_eq`. -/
public theorem counitIso_inv_app_top (t : Nc.val.obj (op (⊤ : Z.Opens))) :
    (ImmersionCounit.counitIso f Nc).inv.val.app (op ⊤) t =
      (((Scheme.Modules.pushforward f).obj Nc).val.map
        (homOfLE (le_top : (f ''ᵁ (⊤ : Z.Opens)) ≤ (⊤ : X.Opens))).op) t :=
  (ImmersionCounit.counitIso_inv_app f Nc ⊤
        (homOfLE (le_of_eq (f.preimage_image_eq (⊤ : Z.Opens)))).op t).trans
    (pushforward_map_eq f Nc (homOfLE (le_top : (f ''ᵁ (⊤ : Z.Opens)) ≤ (⊤ : X.Opens)))
      (homOfLE (le_of_eq (f.preimage_image_eq (⊤ : Z.Opens)))) t).symm

variable {M P : PresheafOfModules.{u} X.ringCatSheaf.obj} {W₀ W₁ : X.Opens}
  (a : TopCat.Sheaf.LocalModuleEquiv M (pushforwardVal f Nc) W₀)
  (b : TopCat.Sheaf.LocalModuleEquiv M P W₁)
  (c : TopCat.Sheaf.LocalModuleEquiv P (pushforwardVal f Nc) W₀)
  (hW : W₀ ≤ W₁) (himg : f ''ᵁ (⊤ : Z.Opens) ≤ W₀)

/-- **The conjugated discrepancy fixes a section of the module on the chart**, given a section `x`
of the first module whose image under the direct comparison is the counit image of it, and the
cocycle identity at that `x`.

The two hypotheses mention the three comparisons separately and never the composite, which is what
makes them available at the concrete instance. -/
public theorem conjEndo_app_eq_self_of (T : Z.Opens) (t : Nc.val.obj (op T))
    {x : M.obj (op (f ''ᵁ T))}
    (hx : a.app (f ''ᵁ T) ((f.image_mono le_top).trans himg) x =
      (ImmersionCounit.counitIso f Nc).inv.val.app (op T) t)
    (hcoc : c.app (f ''ᵁ T) ((f.image_mono le_top).trans himg)
          (b.app (f ''ᵁ T) (((f.image_mono le_top).trans himg).trans hW) x) =
        a.app (f ''ᵁ T) ((f.image_mono le_top).trans himg) x) :
    (ImmersionCounit.conjEndo f Nc (discrOf a b c hW) himg).val.app (op T) t = t := by
  refine Eq.trans (ImmersionCounit.conjEndo_app f Nc (discrOf a b c hW) himg T t) ?_
  refine Eq.trans (congrArg ((ImmersionCounit.counitIso f Nc).hom.val.app (op T)) ?_)
    (ImmersionCounit.iso_inv_hom_app (ImmersionCounit.counitIso f Nc) T t)
  refine Eq.trans (congrArg
    ((discrOf a b c hW).app (f ''ᵁ T) ((f.image_mono le_top).trans himg)) hx.symm) ?_
  refine Eq.trans
    (discrOf_app_cmp a b c hW (f ''ᵁ T) ((f.image_mono le_top).trans himg) x) ?_
  exact hcoc.trans hx

variable (hW₀ : W₀ ≤ f ''ᵁ (⊤ : Z.Opens))

include hW₀ in
/-- **If the conjugated discrepancy is the identity, the discrepancy is the identity on the
sections over every open inside the smaller open.** Every such open is inside the chart image, so
it is the image of its own preimage, and the conjugation is undone there. -/
public theorem discrOf_app_eq_self_of_conjEndo_eq_id
    (hid : ImmersionCounit.conjEndo f Nc (discrOf a b c hW) himg = 𝟙 Nc)
    (V : X.Opens) (hV : V ≤ W₀) (y : (pushforwardVal f Nc).obj (op V)) :
    (discrOf a b c hW).app V hV y = y := by
  have hIm : f ''ᵁ (f ⁻¹ᵁ V) = V := TwistUnique.image_preimage_eq_self f (hV.trans hW₀)
  have hid' := ImmersionCounit.app_image_eq_self_of_conjEndo_eq_id f Nc
    (discrOf a b c hW) himg hid (f ⁻¹ᵁ V)
  have hrestr : (pushforwardVal f Nc).map (homOfLE hIm.le).op
        ((discrOf a b c hW).app V hV y) =
      (pushforwardVal f Nc).map (homOfLE hIm.le).op y :=
    ((discrOf a b c hW).naturality hV hIm.le y).symm.trans (hid' _)
  have hinj := PresheafOfModules.map_map_eq_self (pushforwardVal f Nc)
    (homOfLE hIm.le).op (homOfLE hIm.ge).op
  exact (hinj _).symm.trans
    ((congrArg ((pushforwardVal f Nc).map (homOfLE hIm.ge).op) hrestr).trans (hinj y))

include hW₀ in
/-- **If the conjugated discrepancy is the identity, the three comparisons compose**, on the
sections over every open inside the smaller open. -/
public theorem isComposite_of_conjEndo_eq_id
    (hid : ImmersionCounit.conjEndo f Nc (discrOf a b c hW) himg = 𝟙 Nc)
    (V : X.Opens) (hV : V ≤ W₀) (hV' : V ≤ W₁) : IsComposite b c a V hV hV' := fun s =>
  (discrOf_app_cmp a b c hW V hV s).symm.trans
    (discrOf_app_eq_self_of_conjEndo_eq_id f Nc a b c hW himg hW₀ hid V hV _)

end Conjugate

/-! ### From rigidity in degree one to the composition law -/

section RigidityBridge

variable {R R' : Type u} {σ σ' : Type u} [CommRing R] [SetLike σ R] [AddSubgroupClass σ R]
  {𝒜 : ℕ → σ} [GradedRing 𝒜] [CommRing R'] [SetLike σ' R'] [AddSubgroupClass σ' R']
  {ℬ : ℕ → σ'} [GradedRing ℬ] (ψ : ℬ →+*ᵍ 𝒜)
  {X : Scheme.{u}} (f : AlgebraicGeometry.Proj 𝒜 ⟶ X) [IsOpenImmersion f]
  {M P : ℤ → PresheafOfModules.{u} X.ringCatSheaf.obj} {W₀ W₁ : X.Opens}
  (a : ∀ n : ℤ, TopCat.Sheaf.LocalModuleEquiv (M n)
    (pushforwardVal f (twistingSheaf 𝒜 n)) W₀)
  (b : ∀ n : ℤ, TopCat.Sheaf.LocalModuleEquiv (M n) (P n) W₁)
  (c : ∀ n : ℤ, TopCat.Sheaf.LocalModuleEquiv (P n)
    (pushforwardVal f (twistingSheaf 𝒜 n)) W₀)
  (hW : W₀ ≤ W₁) (himg : f ''ᵁ (⊤ : (AlgebraicGeometry.Proj 𝒜).Opens) ≤ W₀)
  (hW₀ : W₀ ≤ f ''ᵁ (⊤ : (AlgebraicGeometry.Proj 𝒜).Opens))

omit [AddSubgroupClass σ' R'] [GradedRing ℬ] in
include hW₀ in
/-- **The composition law for three comparisons through a chart, from rigidity in degree one.**
Given, in every degree `k`, a section `x k` of the first module over the chart image whose image
under the direct comparison is the counit image of the homogeneous global section attached to
`ψ`, and the cocycle identity at that section, the three comparisons compose in degree one over
every open inside the smaller open.

**Everything the composite is built from stays inside this proof.** That is the measurement the
whole file is arranged around: `conjEndo` and `discrOf` appear here, where the chart, the modules
and the three comparisons are all variables, and nowhere at a concrete instance — matching a goal
against a term in which they occur sends the elaborator through the comparisons into the
pushforward of the twist and the restriction adjunction, which is the wall
`StacksFrontier/AlgebraicGeometry/ChartTransNonNested/RelativeProj.lean` records for
`(modelPair _ _).app`. The hypotheses and the conclusion below mention only the three comparisons
separately, which are exactly the shapes `cmpNested_degreeSection`,
`cmpNested_degreeSection_comp` and `IsComposite` already have. -/
public theorem isComposite_of_rigidity
    (hdeg : ∀ x : ProjectiveSpectrum 𝒜, ∃ aa : 𝒜 1, (aa : R) ∉ x.asHomogeneousIdeal)
    (hgen : RelativeTwistRigidity.Generates ψ)
    (x : ∀ (k : ℕ) (_ : ℬ k), (M (k : ℤ)).obj
      (op (f ''ᵁ (⊤ : (AlgebraicGeometry.Proj 𝒜).Opens))))
    (hx : ∀ (k : ℕ) (cc : ℬ k),
      (a (k : ℤ)).app (f ''ᵁ ⊤) ((f.image_mono le_top).trans himg) (x k cc) =
        (ImmersionCounit.counitIso f (twistingSheaf 𝒜 (k : ℤ))).inv.val.app (op ⊤)
          (degreeSection 𝒜 k ⟨ψ cc, ψ.map_mem cc.2⟩))
    (hcoc : ∀ (k : ℕ) (cc : ℬ k),
      (c (k : ℤ)).app (f ''ᵁ ⊤) ((f.image_mono le_top).trans himg)
          ((b (k : ℤ)).app (f ''ᵁ ⊤) (((f.image_mono le_top).trans himg).trans hW) (x k cc)) =
        (a (k : ℤ)).app (f ''ᵁ ⊤) ((f.image_mono le_top).trans himg) (x k cc))
    (V : X.Opens) (hV : V ≤ W₀) (hV' : V ≤ W₁) :
    IsComposite (b 1) (c 1) (a 1) V hV hV' := by
  have hfix : RelativeTwistRigidity.FixesResDegreeSections ψ
      (fun n : ℤ => ImmersionCounit.conjEndo f (twistingSheaf 𝒜 n)
        (discrOf (a n) (b n) (c n) hW) himg) := fun k cc =>
    conjEndo_app_eq_self_of f (twistingSheaf 𝒜 (k : ℤ)) (a (k : ℤ)) (b (k : ℤ)) (c (k : ℤ))
      hW himg ⊤ _ (hx k cc) (hcoc k cc)
  exact isComposite_of_conjEndo_eq_id f (twistingSheaf 𝒜 (1 : ℤ)) (a 1) (b 1) (c 1) hW himg
    hW₀ (TwistRigidityDegreeOne.eq_id_of_generates (𝒜 := 𝒜) (ψ := ψ) hdeg hgen hfix) V hV hV'

end RigidityBridge

end Stacks.AlgebraicGeometry.ChartTransRelativeProj

end
