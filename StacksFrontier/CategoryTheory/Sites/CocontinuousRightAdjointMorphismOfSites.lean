module

public import StacksFrontier.CategoryTheory.Sites.Localization.PushforwardAdjunction
public import StacksFrontier.CategoryTheory.Sites.Topos.MorphismOfTopoi

/-!
# A cocontinuous functor whose right adjoint is continuous comes from a morphism of sites

Let `(C, J)` and `(D, K)` be sites, let `u : C ⥤ D` be cocontinuous and let `v : D ⥤ C` be a
right adjoint of `u`. Then `u` induces a morphism of topoi `g : Sh(C) → Sh(D)` (Stacks 00XO),
with pushforward `g_* = {}_su` and inverse image `g^{-1} = (u^p-)^#`, and Stacks 00XX computes
both of them through `v`: `(g_*F)(V) = F(v(V))` and `g^{-1}G = (v_pG)^#`.

If `v` is moreover continuous then `v_s = (v_p-)^# = g^{-1}` is exact, so `v` is the continuous
functor underlying a morphism of sites `f : C → D` in the sense of Stacks 00X1, and `f = g`:
its pushforward `f_* = v^s` is restriction along `v`, which is `g_*` by Stacks 00XX (1), and the
inverse images then agree as well, being left adjoint to isomorphic functors.

## Main definitions

* `morphismOfTopoiPushforwardIso`: the identification `f_* ≅ g_*`, i.e. the morphism of topoi
  attached to the morphism of sites given by `v` is the morphism of topoi attached to the
  cocontinuous functor `u`.

## Implementation notes

The morphism of topoi `g` of Stacks 00XO is not bundled as a `MorphismOfTopoi`, so it enters
only through its pushforward `g_* = {}_su`, Mathlib's
`CategoryTheory.Functor.sheafPushforwardCocontinuous`, which exists exactly because `u` is
cocontinuous. Accordingly `f = g` is recorded as an isomorphism of pushforwards, the invertible
2-morphism of Stacks 04IA. Nothing is lost: an isomorphism of right adjoints transports uniquely
to an isomorphism of the left adjoints, so it also carries the identity `f^{-1} = v_s = g^{-1}`
that the source's proof displays.

That a continuous `v` admitting a left adjoint does define a morphism of sites is a statement
about `v` alone — a right adjoint is representably flat, so Stacks 00X5 applies, no cocontinuity
of `u` needed — and is proved separately as
`CategoryTheory.Adjunction.isMorphismOfSites_of_isLeftAdjoint`. It is therefore a hypothesis
here, in the bundled form `h : v.IsMorphismOfSites K J`, so that the left-hand side of the
isomorphism is literally the pushforward of the morphism of topoi of `f` (Stacks 00XC) and not
merely a functor defined by the same formula; that pushforward is by construction the restriction
`v^s`, `CategoryTheory.Functor.sheafPushforwardContinuous`. Continuity of `v`, the source's "in
addition" hypothesis, is a field of `h`; it is in any case automatic, a right adjoint of a
cocontinuous functor being continuous
(`CategoryTheory.Adjunction.isContinuous_of_isCocontinuous`). Continuity of `u` is never used.

Continuity of `v` is `CategoryTheory.Functor.IsContinuous`, the condition that restriction along
`v` take sheaves to sheaves, and not the source's Definition 00WV, which asks that `v` take
coverings to coverings and preserve the fibre products occurring in a covering — the notion
recorded here as `StacksContinuousFunctor.IsContinuous`. The latter implies the former (Stacks
00WW), and the former is what a morphism of sites asks for, so the hypothesis here is the weaker
one. Hence there is no conflict with the source's Example 0H6Z, which exhibits a cocontinuous
`u` whose right adjoint fails to be continuous *in the sense of 00WV*.

Sheaves of sets on small sites in one universe are the setting of Stacks 00X1 and of
`CategoryTheory.Functor.IsMorphismOfSites`, and are what the source's `Sh(C)` means, so the
topoi here are `Sheaf J (Type u)` and `Sheaf K (Type u)`. The identification of `{}_su` with
`v^s` on which the proof rests, `CategoryTheory.Adjunction.sheafPushforwardCocontinuousIso`,
holds for arbitrary coefficients.

## References

* [Stacks 00XY](https://stacks.math.columbia.edu/tag/00XY), in the section "Cocontinuous
  functors which have a right adjoint" (Stacks 00XW); the computation of `g_*` and `g^{-1}` is
  Stacks 00XX, the notion of a morphism of sites is Stacks 00X1, and the morphism of topoi of a
  cocontinuous functor is Stacks 00XO.
-/

@[expose] public section

open CategoryTheory

universe u

/-- **Stacks 00XY.** Let `(C, J)` and `(D, K)` be sites, let `u : C ⥤ D` be cocontinuous with
right adjoint `v : D ⥤ C`, and let `g : Sh(C) → Sh(D)` be the morphism of topoi attached to `u`
(Stacks 00XO), so that `g_* = {}_su` is `u.sheafPushforwardCocontinuous`.

If `v` is continuous it defines a morphism of sites `f : C → D` (Stacks 00X1), the hypothesis
`h`, and the morphism of topoi attached to `f` (Stacks 00XC) is `g`: the two pushforwards
`f_* = v^s` and `g_*` are isomorphic. -/
@[no_expose, stacks 00XY "Equality of the two morphisms of topoi is recorded as an isomorphism
  of their pushforwards; that the continuous right adjoint `v` does define a morphism of sites
  is the hypothesis `h`."]
public noncomputable def morphismOfTopoiPushforwardIso
    {C : Type u} [SmallCategory C] {D : Type u} [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {u : C ⥤ D} {v : D ⥤ C} (adj : u ⊣ v) [u.IsCocontinuous J K]
    (h : v.IsMorphismOfSites K J) :
    h.morphismOfTopoi.pushforward ≅ u.sheafPushforwardCocontinuous (Type u) J K :=
  haveI := h.isContinuous
  (adj.sheafPushforwardCocontinuousIso (Type u)).symm
