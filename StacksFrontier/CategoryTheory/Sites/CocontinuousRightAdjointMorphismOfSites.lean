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

* `morphismOfTopoiPushforwardIso`: the identification `f_* ≅ g_*` of the pushforward of the
  morphism of topoi of a morphism of sites `h : v.IsMorphismOfSites K J`, supplied by the caller,
  with the pushforward of the morphism of topoi of `u`.

The complete statement of Stacks 00XY — the morphism of sites constructed from the continuity of
`v`, and the two morphisms of topoi identified through their pushforwards, their inverse images
and their adjunctions — is in
`StacksFrontier.CategoryTheory.Sites.CocontinuousRightAdjointMorphismOfTopoi`.

## Implementation notes

The two pushforwards are not literally equal functors: `f_* = v^s` is restriction along `v`
(`CategoryTheory.Functor.sheafPushforwardContinuous`) while `g_* = {}_su` is the right Kan
extension along `u` (Mathlib's `CategoryTheory.Functor.sheafPushforwardCocontinuous`), and
Stacks 00XX identifies them by the canonical bijection `(g_*F)(V) = F(v(V))`. The equality
`f = g` of the source is therefore the identification of the two morphisms of topoi by this
canonical isomorphism of pushforwards together with the conjugate isomorphism of inverse
images (`f^{-1} = v_s = g^{-1}` in the source's proof), which by construction transports the
adjunction of `f` to that of `g`. This is an invertible 2-morphism of topoi (Stacks 04IA)
whose inverse-image component is the one induced by the adjunctions.

Continuity of `v` is `CategoryTheory.Functor.IsContinuous`, the condition that restriction along
`v` take sheaves to sheaves, and not the source's Definition 00WV, which asks that `v` take
coverings to coverings and preserve the fibre products occurring in a covering — the notion
recorded here as `StacksContinuousFunctor.IsContinuous`. The latter implies the former (Stacks
00WW), and the former is what a morphism of sites asks for, so the hypothesis here is the weaker
one. Hence there is no conflict with the source's Example 0H6Z, which exhibits a cocontinuous
`u` whose right adjoint fails to be continuous *in the sense of 00WV*. Continuity of `u` is
never used.

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

/-- Let `(C, J)` and `(D, K)` be sites, let `u : C ⥤ D` be cocontinuous with right adjoint
`v : D ⥤ C`, and let `g : Sh(C) → Sh(D)` be the morphism of topoi attached to `u` (Stacks 00XO),
so that `g_* = {}_su` is `u.sheafPushforwardCocontinuous`. Given a morphism of sites
`h : v.IsMorphismOfSites K J`, the pushforward `f_* = v^s` of its morphism of topoi (Stacks 00XC)
is isomorphic to `g_*`.

The morphism of sites `h` always exists once `v` is continuous
(`CategoryTheory.Adjunction.isMorphismOfSites_of_isLeftAdjoint`); the complete statement of
Stacks 00XY, with `h` constructed and the inverse images and adjunctions identified as well, is
`CategoryTheory.Adjunction.morphismOfTopoiPushforwardIsoOfIsCocontinuous`,
`CategoryTheory.Adjunction.morphismOfTopoiInverseImageIsoOfIsCocontinuous` and
`CategoryTheory.Adjunction.morphismOfTopoi_adj_compatible_of_isCocontinuous`. -/
@[no_expose]
public noncomputable def morphismOfTopoiPushforwardIso
    {C : Type u} [SmallCategory C] {D : Type u} [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {u : C ⥤ D} {v : D ⥤ C} (adj : u ⊣ v) [u.IsCocontinuous J K]
    (h : v.IsMorphismOfSites K J) :
    h.morphismOfTopoi.pushforward ≅ u.sheafPushforwardCocontinuous (Type u) J K :=
  haveI := h.isContinuous
  (adj.sheafPushforwardCocontinuousIso (Type u)).symm
