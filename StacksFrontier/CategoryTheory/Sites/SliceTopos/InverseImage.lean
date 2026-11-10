module

public import StacksFrontier.CategoryTheory.Adjunction.Mates
public import StacksFrontier.CategoryTheory.Sites.SliceTopos.OverFunctorIso
public import StacksFrontier.CategoryTheory.Sites.SlicePost.Pushforward
public import StacksFrontier.CategoryTheory.Sites.SlicePost.MorphismOfSites
public import StacksFrontier.CategoryTheory.Sites.Localization.ToposComparison
public import StacksFrontier.CategoryTheory.Sites.Continuous.PullbackOfRepresentable
public import StacksFrontier.CategoryTheory.Sites.SlicePost.MorphismOfSitesGeneral

/-!
# The square of topoi of Stacks 03CF, and the description of `(f')⁻¹`

Let `u : C ⥤ D` be a continuous functor of sites, `V : C` and `U = u.obj V`; then
`u' = Over.post u : Over V ⥤ Over U` is again continuous and Stacks 03CF asserts four things about
the resulting morphism of topoi `f'`.  Clause (d), `f'_* j_U⁻¹ = j_V⁻¹ f_*`, is a strict equality
and is `sheafPushforwardContinuous_overPost_eq` in `Sites/SlicePost/Pushforward.lean`; the
isomorphism `(f')⁻¹ j_{U!} ≅ j_{V!} f⁻¹` obtained from it by uniqueness of left adjoints is
`sheafPullbackOverPostIso` there.  This file settles the remaining two:

* **clause (c)**, the description of `(f')⁻¹` through the identifications `Sh(C/V) = Sh(C)/h_V^#`
  and `Sh(D/U) = Sh(D)/h_U^#` of Stacks 00Y1, is `sheafFunctorToOverCompOverPostIso`;
* **clause (b)**, the commutativity of the square of topoi `(f')⁻¹ j_V⁻¹ = j_U⁻¹ f⁻¹`, is
  `overPullbackCompSheafPullbackOverPostIso`.

## Why clause (c) is not circular

An earlier assessment held clause (c) unreachable: it reduces to needing `(f')⁻¹⊤ ≅ ⊤`, which is
part of the exactness that Stacks *derives* from clause (c).  The assessment is wrong, and there
are two separate reasons.

First, the shape of the obligation. Write `Φ_V`, `Φ_U` for 00Y1's equivalences onto the slices.
Both sides of clause (c) are functors into `Over h_U^#`, and after `Over.forget` they are
isomorphic *for free*: `Φ_U ⋙ Over.forget ≅ j_{U!}` (00Y1) turns the left side into
`(f')⁻¹ j_{U!}`, which `sheafPullbackOverPostIso` identifies with `j_{V!} f⁻¹`, which is the right
side. This is `underlyingIso`, and it uses no exactness — `sheafPullbackOverPostIso` comes from
clause (d) by uniqueness of left adjoints. Since `Over.forget` is faithful but not full, what is
left is a *triangle*: that `underlyingIso` respects the two structure maps into `h_U^#`. By
`Over.comp_hom_of_terminal` that triangle only has to be checked at the terminal sheaf, so the
entire residual obligation is a single equation between two morphisms. Nothing here is an exactness
statement.

Second, discharging that equation.  Two routes are available.  One may prove it for 04D3's
identification `f⁻¹h_V^# ≅ h_U^#` — a computation with `Adjunction.leftAdjointUniq`, not carried out
here.  Or one may *define* the identification so that the equation holds, which is what `yonedaIso`
does; for that the defined morphism has to be invertible, and that is where `(f')⁻¹⊤ ≅ ⊤` is used.
`(f')⁻¹⊤ ≅ ⊤` is available *independently* of clause (c), from clause (a)
(`Functor.isMorphismOfSites_overPost_of_isMorphismOfSites`), so the route is not circular; that is
`isIso_hom_sheafFunctorToOver_sheafPullback_terminal`.  Stacks instead derives exactness of
`(f')⁻¹` *from* clause (c), and in that order the first route would be needed; clause (a) is proved
here by a different argument (Stacks 00Y1 for continuity, and the terminal object and fibre
products separately for exactness), which is what keeps this route open.

## What the identification `f⁻¹ h_V^# ≅ h_U^#` is here

Clause (c) reads `(f')⁻¹(H ⟶ h_V^#) = (f⁻¹H ⟶ h_U^#)`, and the target of the second arrow is
literally `f⁻¹h_V^#`; Stacks silently identifies it with `h_U^#` by Lemma 04D3.  Here that
identification is `yonedaIso`, and it is forced: given `underlyingIso`, the triangle at the
terminal sheaf determines it uniquely.  What is *not* proved is that `yonedaIso` coincides with
04D3's `sheafPullbackSheafifyYonedaIso`.  That single equation is this file's whole residue, and
`sheafFunctorToOverCompOverPostIso_of_eq` isolates it: from it, clause (c) with 04D3's
identification follows at once, and with it Stacks 04IU and 04IW.  Clause (b) does not mention the
identification at all, so it is unconditional.

## The hypotheses, and why they are 03CF's own

Throughout, the single hypothesis is `u.IsMorphismOfSites J K`, which is 03CF's own: 03CF takes a
morphism of sites and asserts that the localized functor is one again.  Earlier these clauses were
proved under the much stronger hypotheses of Stacks 03EF — `[HasFiniteLimits C]`,
`[HasFiniteLimits D]`, `[PreservesFiniteLimits u]` — because `(f')⁻¹` was known to be left exact
only under them.  Those three are needed in exactly two places, and in both only to obtain left
exactness of an inverse image:

* `isIso_hom_sheafFunctorToOver_sheafPullback_terminal` needs `(f')⁻¹` left exact, which is clause
  (a), `Functor.isMorphismOfSites_overPost_of_isMorphismOfSites`, available from
  `u.IsMorphismOfSites J K` alone;
* `toOverCompOverPostIso` needs `f⁻¹` left exact for binary products, which is the
  `preservesFiniteLimits` field of that same hypothesis.

So the whole triple is replaced by `u.IsMorphismOfSites J K`, which is strictly weaker: 03EF's
hypotheses imply it by Stacks 00X6 (`Functor.isMorphismOfSites_of_preservesFiniteLimits`), so every
statement below is a weakening of what it was and every former call site still typechecks.  The
continuity of `Over.post u`, which the type of `(f')⁻¹` needs before any of this, is clause (a)'s
continuity half `Functor.isContinuous_overPost_of_isContinuous`, taken here as a `local instance`
in place of the 03EF-flavoured global instance `Functor.isContinuous_overPost`.

## What Stacks 04IH's site clauses need, and why clause (b) *is* it

Stacks 04IH (3) says the localized morphism of ringed sites
(`AlgebraicGeometry.RingedSite.Hom.localized`, Stacks 04J0) is locally ringed, and its proof is
"`(f')^♯` is just the restriction of `f^♯`; the defining diagram for `f'` is the restriction of the
one for `f`, and restriction is exact".  The units square of `f'` has its upper-left corner at
`(f')⁻¹ j_V⁻¹ O'^*` and `j_U⁻¹` of the units square of `f` has it at `j_U⁻¹ f⁻¹ O'^*`, so an
isomorphism between the two routes is needed, and the structure map says which one: `(f')^♯` is the
transpose across `(f')⁻¹ ⊣ f'_*` of `j_V⁻¹(f^♯)`, so the bottom edges of the two squares match
through the **Beck–Chevalley mate** of clause (d) and through no other map.

Clause (b) *is* the mate
(`overPullbackCompSheafPullbackOverPostIso_hom`, registered on Stacks 03CF), and the mate is
therefore an isomorphism (`isIso_overPullbackCompSheafPullbackOverPostMate`); both are below, and
they are the two facts stated for Stacks 04J0.  The
mate of `StacksFrontier/AlgebraicGeometry/Recovery04IH/LocalizedSiteStructureMap.lean`, which is the
one `AlgebraicGeometry.RingedSite.Hom.fSharpSet_localized` actually uses, is the same
transformation on the nose, and its invertibility is
`CategoryTheory.SliceTopos.isIso_localizedInverseImageMate` of
`StacksFrontier/AlgebraicGeometry/Recovery04IH/LocalizedMateInvertible.lean`.

So what 04IH (3) still owes is only the transport itself: that the units square of `f'` is the
image under `j_U⁻¹` of the units square of `f`.  Three facts about it hold:
the mate's component is well typed with clause
(d) accepted as `rfl` and no `eqToHom` inserted; its naturality in `G` follows from naturality of
the unit by injectivity of the two `Adjunction.homEquiv`s; and restriction to a slice commutes with
`CategoryTheory.sheafCompose` on the nose, so `(X.over U).O` and the units subsheaves need no
comparison at all.  The obstacle there is not mathematics but `implicit` transparency:
any statement relating `f'_*(j_U⁻¹ H)` to `j_V⁻¹(f_* H)` is type-
correct only at default transparency, so `rw`/`simp` refuse it, and the fix is to carry clause (d)
as an explicit `eqToIso` through the statements rather than to lean on the `rfl`.

## Main results

* `CategoryTheory.SliceTopos.underlyingIso`: `j_{U!}(f')⁻¹ ≅ f⁻¹ j_{V!}`, read through 00Y1.
* `CategoryTheory.SliceTopos.yonedaIso`: the identification `f⁻¹ h_V^# ≅ h_U^#`.
* `CategoryTheory.SliceTopos.sheafFunctorToOverCompOverPostIso` (Stacks 03CF (c)).
* `CategoryTheory.SliceTopos.overPullbackCompSheafPullbackOverPostIso` (Stacks 03CF (b)).
* `CategoryTheory.SliceTopos.sheafFunctorToOverCompOverPostIso_of_eq`: clause (c) with 04D3's
  identification, from the one equation this file does not prove.
* `CategoryTheory.SliceTopos.overPullbackCompSheafPullbackOverPostMate`: the Beck-Chevalley mate of
  clause (d), a *computable* 2-cell of the shape of clause (b), and
  `CategoryTheory.SliceTopos.overPullbackCompSheafPullbackOverPostMate_comp_counit`, the equation
  that determines it.
* `CategoryTheory.SliceTopos.overPullbackCompSheafPullbackOverPostIso_hom`: clause (b) *is* that
  mate.  This is what gives clause (b) computable components, and conversely what makes the mate
  invertible.
* `CategoryTheory.SliceTopos.overPullbackCompSheafPullbackOverPostIso_hom_app_comp_counit`: the
  resulting description of clause (b) at a direct image, in terms of the two counits.
-/

@[expose] public section

namespace CategoryTheory.SliceTopos

open Limits MonoidalCategory CartesianMonoidalCategory OverShriek

universe u

attribute [local instance] Functor.isContinuous_overPost_of_isContinuous

variable {C : Type u} [SmallCategory C] {D : Type u} [SmallCategory D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) (u : C ⥤ D) (V : C)
  [u.IsContinuous J K]

noncomputable section

/-- **The underlying isomorphism of Stacks 03CF's clause (c).**

Composing both sides of clause (c) with `Over.forget h_U^#` gives `(f')⁻¹ j_{U!}` and `j_{V!} f⁻¹`,
which `sheafPullbackOverPostIso` identifies; the two ends are rewritten by
`OverShriek.sheafFunctorToOverForgetIso`, which says that the sheaf underlying `Φ_U G` is
`j_{U!}G`. -/
def underlyingIso :
    (Over.post (X := V) u).sheafPullback (Type u) (J.over V) (K.over (u.obj V)) ⋙
        sheafFunctorToOver (U := u.obj V) K ⋙ Over.forget _ ≅
      sheafFunctorToOver (U := V) J ⋙ Over.forget _ ⋙ u.sheafPullback (Type u) J K :=
  Functor.isoWhiskerLeft _ (sheafFunctorToOverForgetIso (U := u.obj V) K) ≪≫
    sheafPullbackOverPostIso J K u V (Type u) ≪≫
    Functor.isoWhiskerRight (sheafFunctorToOverForgetIso (U := V) J).symm _

/-- `Φ_V` is an equivalence, hence carries the terminal sheaf on `C/V` to a terminal object of
`Sh(C)/h_V^#`, whose structure map is therefore an isomorphism `j_{V!}⊤ ≅ h_V^#`. -/
lemma isIso_hom_sheafFunctorToOver_terminal :
    IsIso ((sheafFunctorToOver (U := V) J).obj (⊤_ (Sheaf (J.over V) (Type u)))).hom :=
  Over.isIso_hom_of_isTerminal (IsTerminal.isTerminalObj _ _ terminalIsTerminal)

/-- **`(f')⁻¹` preserves the terminal object, and this is a consequence of clause (a), not of
clause (c).**  By clause (a) `Over.post u` is a morphism of sites
(`Functor.isMorphismOfSites_overPost_of_isMorphismOfSites`), so `(f')⁻¹` is left exact; hence
`(f')⁻¹⊤` is terminal, and `Φ_U` being an equivalence carries it to a terminal object of
`Sh(D)/h_U^#`, whose structure map is an isomorphism. -/
lemma isIso_hom_sheafFunctorToOver_sheafPullback_terminal (hu : u.IsMorphismOfSites J K) :
    IsIso ((sheafFunctorToOver (U := u.obj V) K).obj
      (((Over.post (X := V) u).sheafPullback (Type u) (J.over V)
        (K.over (u.obj V))).obj (⊤_ (Sheaf (J.over V) (Type u))))).hom :=
  have := (Functor.isMorphismOfSites_overPost_of_isMorphismOfSites J K u V
    hu).preservesFiniteLimits
  Over.isIso_hom_of_isTerminal
    (IsTerminal.isTerminalObj _ _ (IsTerminal.isTerminalObj _ _ terminalIsTerminal))

/-- **The identification `f⁻¹ h_V^# ≅ h_U^#` used in Stacks 03CF's clause (c).**

It is forced: the triangle expressing clause (c) lives at the terminal sheaf
(`Over.comp_hom_of_terminal`), and this is the unique isomorphism making that triangle commute,
namely the composite
`f⁻¹h_V^# ≅ f⁻¹ j_{V!}⊤ ≅ j_{U!}(f')⁻¹⊤ ≅ h_U^#`
of the two terminal-object structure maps with `underlyingIso`.

Stacks reaches the same identification from Lemma 04D3, as `f⁻¹h_V^# = h_{u(V)}^#`; that
`yonedaIso` agrees with `sheafPullbackSheafifyYonedaIso` is *not* proved here. -/
def yonedaIso (hu : u.IsMorphismOfSites J K) :
    (u.sheafPullback (Type u) J K).obj ((presheafToSheaf J (Type u)).obj (yoneda.obj V)) ≅
      (presheafToSheaf K (Type u)).obj (yoneda.obj (u.obj V)) :=
  haveI := isIso_hom_sheafFunctorToOver_terminal J V
  haveI := isIso_hom_sheafFunctorToOver_sheafPullback_terminal J K u V hu
  (asIso ((u.sheafPullback (Type u) J K).map
        ((sheafFunctorToOver (U := V) J).obj (⊤_ (Sheaf (J.over V) (Type u)))).hom)).symm ≪≫
    ((underlyingIso J K u V).app (⊤_ (Sheaf (J.over V) (Type u)))).symm ≪≫
    asIso ((sheafFunctorToOver (U := u.obj V) K).obj
      (((Over.post (X := V) u).sheafPullback (Type u) (J.over V)
        (K.over (u.obj V))).obj (⊤_ (Sheaf (J.over V) (Type u))))).hom

/-- **Stacks 03CF, clause (c).**  Under the identifications `Sh(C/V) = Sh(C)/h_V^#` and
`Sh(D/U) = Sh(D)/h_U^#` of Stacks 00Y1, the inverse image `(f')⁻¹` is "apply `f⁻¹` to the sheaf and
to its structure map":
```
  (f')⁻¹ (H ⟶ h_V^#) = (f⁻¹H ⟶ f⁻¹h_V^# ≅ h_U^#) .
```
The two sides agree after `Over.forget` by `underlyingIso`, and by `Over.comp_hom_of_terminal` the
remaining triangle need only be checked at the terminal sheaf, where `yonedaIso` was defined to
make it commute. -/
@[stacks 03CF "Clause (c): under 00Y1's identifications `(f')⁻¹` sends `(H ⟶ h_V^#)` to
  `(f⁻¹H ⟶ h_U^#)`. Proved in 03CF's own generality, from `u.IsMorphismOfSites` alone, and with
  the identification `f⁻¹h_V^# ≅ h_U^#` given by `yonedaIso`, which is NOT proved equal to 04D3's
  `sheafPullbackSheafifyYonedaIso`."]
def sheafFunctorToOverCompOverPostIso (hu : u.IsMorphismOfSites J K) :
    (Over.post (X := V) u).sheafPullback (Type u) (J.over V) (K.over (u.obj V)) ⋙
        sheafFunctorToOver (U := u.obj V) K ≅
      sheafFunctorToOver (U := V) J ⋙ Over.post (u.sheafPullback (Type u) J K) ⋙
        Over.map (yonedaIso J K u V hu).hom :=
  haveI := isIso_hom_sheafFunctorToOver_terminal J V
  haveI := isIso_hom_sheafFunctorToOver_sheafPullback_terminal J K u V hu
  Over.natIsoOfForgetIsoTerminal (underlyingIso J K u V) (by
    have h : ((sheafFunctorToOver (U := V) J ⋙ Over.post (u.sheafPullback (Type u) J K) ⋙
          Over.map (yonedaIso J K u V hu).hom).obj (⊤_ (Sheaf (J.over V) (Type u)))).hom =
        (u.sheafPullback (Type u) J K).map
            ((sheafFunctorToOver (U := V) J).obj (⊤_ (Sheaf (J.over V) (Type u)))).hom ≫
          (yonedaIso J K u V hu).hom := rfl
    rw [h, yonedaIso]
    simp only [Functor.comp_obj, Iso.trans_hom, asIso_hom, Iso.symm_hom, asIso_inv,
      IsIso.hom_inv_id_assoc]
    exact Iso.hom_inv_id_assoc ((underlyingIso J K u V).app
      (⊤_ (Sheaf (J.over V) (Type u)))) _)

set_option backward.isDefEq.respectTransparency false in
/-- `f⁻¹` turns a product with `h_V^#` into a product with `h_U^#`:
`f⁻¹G × h_U^# ≅ f⁻¹(G × h_V^#)`, compatibly with the projections to the second factor.

This is the one place where exactness of `f⁻¹` is used, and it is used only for binary products.
Together with Stacks 04IQ it is what turns clause (c) into clause (b). -/
def toOverCompOverPostIso (hu : u.IsMorphismOfSites J K) :
    u.sheafPullback (Type u) J K ⋙
        toOver ((presheafToSheaf K (Type u)).obj (yoneda.obj (u.obj V))) ≅
      toOver ((presheafToSheaf J (Type u)).obj (yoneda.obj V)) ⋙
        Over.post (u.sheafPullback (Type u) J K) ⋙ Over.map (yonedaIso J K u V hu).hom :=
  haveI := hu.preservesFiniteLimits
  letI : (u.sheafPullback (Type u) J K).Monoidal :=
    Functor.Monoidal.ofChosenFiniteProducts _
  NatIso.ofComponents
    (fun G => Over.isoMk
      (whiskerLeftIso _ (yonedaIso J K u V hu).symm ≪≫
        Functor.Monoidal.μIso (u.sheafPullback (Type u) J K) G
          ((presheafToSheaf J (Type u)).obj (yoneda.obj V)))
      (by
        change (_ ≫ Functor.LaxMonoidal.μ _ _ _) ≫
          (u.sheafPullback (Type u) J K).map (snd _ _) ≫ (yonedaIso J K u V hu).hom = snd _ _
        rw [Category.assoc, ← Category.assoc (Functor.LaxMonoidal.μ _ _ _),
          Functor.Monoidal.μ_snd, ← Category.assoc, whiskerLeftIso_hom, whiskerLeft_snd,
          Category.assoc, Iso.symm_hom, Iso.inv_hom_id, Category.comp_id]))
    (fun {G G'} g => Over.OverMorphism.ext (by
      change (_ ▷ _) ≫ _ ≫ Functor.LaxMonoidal.μ _ _ _ =
        (_ ≫ Functor.LaxMonoidal.μ _ _ _) ≫ (u.sheafPullback (Type u) J K).map (_ ▷ _)
      simp only [whiskerLeftIso_hom]
      rw [Category.assoc, ← Functor.LaxMonoidal.μ_natural_left, ← Category.assoc,
        ← Category.assoc, whisker_exchange]))

/-- **Stacks 03CF, clause (b): the square of topoi commutes.**
```
  (f')⁻¹ j_V⁻¹ = j_U⁻¹ f⁻¹ .
```
Unlike clause (d) this pairs *two inverse images*, so it is not a statement about right adjoints
and does not follow from `sheafPushforwardContinuous_overPost_eq`. It follows from clause (c)
instead: `Φ_U` is fully faithful, so it is enough to prove the square after applying it, and there
Stacks 04IQ (`OverShriek.overPullbackCompSheafFunctorToOverIso`) turns both `j_V⁻¹ Φ_V` and
`j_U⁻¹ Φ_U` into `toOver`, i.e. into "product with `h_V^#`" and "product with `h_U^#`". What is
left is `toOverCompOverPostIso`, that `f⁻¹` carries one product to the other.

The statement does not mention the identification `f⁻¹h_V^# ≅ h_U^#`, so — unlike clause (c) — it
does not depend on which identification is used. -/
@[stacks 03CF "Clause (b): the square of topoi commutes, `(f')⁻¹ j_V⁻¹ ≅ j_U⁻¹ f⁻¹`. Proved in
  03CF's own generality, from `u.IsMorphismOfSites` alone. Clause (a) is
  `Functor.isMorphismOfSites_overPost_of_isMorphismOfSites`; clause (d) is
  `sheafPushforwardContinuous_overPost_eq`."]
def overPullbackCompSheafPullbackOverPostIso (hu : u.IsMorphismOfSites J K) :
    J.overPullback (Type u) V ⋙
        (Over.post (X := V) u).sheafPullback (Type u) (J.over V) (K.over (u.obj V)) ≅
      u.sheafPullback (Type u) J K ⋙ K.overPullback (Type u) (u.obj V) :=
  Functor.fullyFaithfulCancelRight (sheafFunctorToOver (U := u.obj V) K)
    (Functor.isoWhiskerLeft (J.overPullback (Type u) V)
        (sheafFunctorToOverCompOverPostIso J K u V hu) ≪≫
      Functor.isoWhiskerRight (overPullbackCompSheafFunctorToOverIso (U := V) J)
        (Over.post (u.sheafPullback (Type u) J K) ⋙ Over.map (yonedaIso J K u V hu).hom) ≪≫
      (toOverCompOverPostIso J K u V hu).symm ≪≫
      Functor.isoWhiskerLeft (u.sheafPullback (Type u) J K)
        (overPullbackCompSheafFunctorToOverIso (U := u.obj V) K).symm)

/-- **Clause (c) with Stacks 04D3's identification, from the file's residue.**

Stacks writes clause (c) using `f⁻¹h_V^# = h_{u(V)}^#` of Lemma 04D3.  Given that 04D3's
isomorphism is the one forced by the triangle at the terminal sheaf — the single equation
`yonedaIso = sheafPullbackSheafifyYonedaIso` that this file does not prove — clause (c) holds in
Stacks' own formulation, and Stacks 04IU and 04IW follow from it together with 04IQ and 04IS.

This is stated to make the residue machine-checkable and reusable rather than only described. -/
def sheafFunctorToOverCompOverPostIso_of_eq (hu : u.IsMorphismOfSites J K)
    (h : yonedaIso J K u V hu = sheafPullbackSheafifyYonedaIso u J K V) :
    (Over.post (X := V) u).sheafPullback (Type u) (J.over V) (K.over (u.obj V)) ⋙
        sheafFunctorToOver (U := u.obj V) K ≅
      sheafFunctorToOver (U := V) J ⋙ Over.post (u.sheafPullback (Type u) J K) ⋙
        Over.map (sheafPullbackSheafifyYonedaIso u J K V).hom :=
  h ▸ sheafFunctorToOverCompOverPostIso J K u V hu

/-! ### Clause (b) as a Beck–Chevalley mate

Clause (d) is a *strict* identity of the two right-adjoint composites,
`f'_* j_U^{-1} = j_V^{-1} f_*`.  Its Beck–Chevalley mate with respect to the adjunctions
`(f')^{-1} ⊣ f'_*` and `f^{-1} ⊣ f_*` is a 2-cell with exactly the shape of clause (b), and unlike
`overPullbackCompSheafPullbackOverPostIso` it is computable: its component at `A` is the adjunct of
`j_V^{-1}` applied to the unit of `f^{-1} ⊣ f_*`.  What is recorded here is the equation that pins
it down: under the bijection `j_{U!} ⊣ j_U^{-1}` the mate becomes the comparison
`(f')^{-1}j_{U!} ≅ j_{V!}f^{-1}` of the proof of Stacks 03CF followed by `f^{-1}` of the counit of
`j_{V!} ⊣ j_V^{-1}`.  Since that bijection is injective, the equation *determines* the mate. -/

/-- **The Beck–Chevalley mate of Stacks 03CF's clause (d)**, a 2-cell of the shape of clause (b),
`(f')^{-1} j_V^{-1} ⟶ j_U^{-1} f^{-1}`.

Its component at a sheaf `A` is the adjunct, under `(f')^{-1} ⊣ f'_*`, of `j_V^{-1}` applied to the
unit of `f^{-1} ⊣ f_*`; the target typechecks because clause (d) is a strict equality of functors.
This is the computable candidate for clause (b): `overPullbackCompSheafPullbackOverPostIso` is
produced by `Functor.fullyFaithfulCancelRight` from Stacks 00Y1's equivalence, so nothing describes
its components, whereas this transformation is an explicit unit/counit composite. -/
noncomputable def overPullbackCompSheafPullbackOverPostMate :
    J.overPullback (Type u) V ⋙
        (Over.post (X := V) u).sheafPullback (Type u) (J.over V) (K.over (u.obj V)) ⟶
      u.sheafPullback (Type u) J K ⋙ K.overPullback (Type u) (u.obj V) :=
  (mateEquiv (u.sheafAdjunctionContinuous (Type u) J K)
      ((Over.post (X := V) u).sheafAdjunctionContinuous (Type u) (J.over V)
        (K.over (u.obj V)))).symm
    (eqToHom (sheafPushforwardContinuous_overPost_eq J K u V (Type u)).symm)

/-- **The equation that pins the mate down.**  Applying `j_{U!}` to the mate of clause (d) and
composing with the counit of `j_{U!} ⊣ j_U^{-1}` gives the comparison
`j_{U!}(f')^{-1} ≅ f^{-1}j_{V!}` of the proof of Stacks 03CF — itself obtained from clause (d) by
uniqueness of left adjoints — followed by `f^{-1}` of the counit of `j_{V!} ⊣ j_V^{-1}`.

The left-hand side is the image of the mate's component under the bijection
`Hom((f')^{-1}j_V^{-1}A, j_U^{-1}f^{-1}A) ≃ Hom(j_{U!}(f')^{-1}j_V^{-1}A, f^{-1}A)`, so this
equation determines the mate completely.  It is an instance of the general
`Stacks.CategoryTheory.mateEquiv_symm_eqToHom_comp_counit`: the two further edges of the square,
`j_V^{-1}` and `j_U^{-1}`, have left adjoints `j_{V!}` and `j_{U!}`, and the two triangle
identities do the rest. -/
theorem overPullbackCompSheafPullbackOverPostMate_comp_counit (A : Sheaf J (Type u)) :
    ((Over.forget (u.obj V)).sheafPullback (Type u) (K.over (u.obj V)) K).map
          ((overPullbackCompSheafPullbackOverPostMate J K u V).app A) ≫
        ((Over.forget (u.obj V)).sheafAdjunctionContinuous (Type u) (K.over (u.obj V))
            K).counit.app ((u.sheafPullback (Type u) J K).obj A) =
      (sheafPullbackOverPostIso J K u V (Type u)).hom.app ((J.overPullback (Type u) V).obj A) ≫
        (u.sheafPullback (Type u) J K).map
          (((Over.forget V).sheafAdjunctionContinuous (Type u) (J.over V) J).counit.app A) :=
  Stacks.CategoryTheory.mateEquiv_symm_eqToHom_comp_counit
    (u.sheafAdjunctionContinuous (Type u) J K)
    ((Over.post (X := V) u).sheafAdjunctionContinuous (Type u) (J.over V) (K.over (u.obj V)))
    ((Over.forget V).sheafAdjunctionContinuous (Type u) (J.over V) J)
    ((Over.forget (u.obj V)).sheafAdjunctionContinuous (Type u) (K.over (u.obj V)) K) _ A

/-! ### Clause (b) *is* the mate

Clause (b) is produced by `Functor.fullyFaithfulCancelRight` out of Stacks 00Y1's equivalence, so
nothing describes its components; the mate of clause (d) is an explicit unit/counit composite but
is not, on its face, invertible.  The two agree, so each gains what the other has: clause (b)
acquires computable components and the mate acquires invertibility.

Since `j_{U!} ⊣ j_U^{-1}` is a bijection it is enough to compare the two adjuncts, and the mate's
is `overPullbackCompSheafPullbackOverPostMate_comp_counit`.  The adjunct of clause (b) is computed
below by unwinding, one factor at a time, the isomorphism that clause (b) is cancelled from. -/

/-- The components of `underlyingIso`: the two whiskerings contribute Stacks 00Y1's identification
of the sheaf underlying `Φ G` with `j_!G` at the two ends of `sheafPullbackOverPostIso`. -/
theorem underlyingIso_hom_app (G : Sheaf (J.over V) (Type u)) :
    (underlyingIso J K u V).hom.app G =
      (sheafFunctorToOverForgetIso (U := u.obj V) K).hom.app
          (((Over.post (X := V) u).sheafPullback (Type u) (J.over V)
            (K.over (u.obj V))).obj G) ≫
        (sheafPullbackOverPostIso J K u V (Type u)).hom.app G ≫
          (u.sheafPullback (Type u) J K).map
            ((sheafFunctorToOverForgetIso (U := V) J).inv.app G) :=
  rfl

/-- `Over.forget` of clause (c) is `underlyingIso`.  `Over.natIsoOfForgetIso` builds its
components with `Over.isoMk`, whose underlying map is the given one. -/
theorem left_sheafFunctorToOverCompOverPostIso_hom_app (hu : u.IsMorphismOfSites J K)
    (G : Sheaf (J.over V) (Type u)) :
    ((sheafFunctorToOverCompOverPostIso J K u V hu).hom.app G).left =
      (underlyingIso J K u V).hom.app G :=
  rfl

/-- A product comparison undone, whiskered by a map on the second factor and followed by the
projection to the first factor, is the image of that projection.

Stated for an arbitrary monoidal functor between cartesian monoidal categories, because the two
sides of `left_toOverCompOverPostIso_inv_app_comp_fst` are type-correct only at default
transparency: there one of them is a map between the sheaves underlying objects of a slice
category, so the rewriting has to happen in a context where the product is visible. -/
private theorem inv_μIso_whiskerLeft_comp_fst {S : Type*} [Category* S] {T : Type*} [Category* T]
    [CartesianMonoidalCategory S] [CartesianMonoidalCategory T] (F : S ⥤ T) [mF : F.Monoidal]
    (X Y : S) {Z : T} (e : F.obj Y ⟶ Z) :
    (Functor.Monoidal.μIso F X Y).inv ≫ (F.obj X ◁ e) ≫ fst (F.obj X) Z = F.map (fst X Y) := by
  rw [whiskerLeft_fst]
  exact (Iso.inv_comp_eq _).2 (Functor.Monoidal.μ_fst _ _ _).symm

/-- `toOverCompOverPostIso` undone, followed by the projection to the first factor, is `f⁻¹` of
that projection: the component is a product comparison, and `whiskerLeft_fst` together with
`Functor.Monoidal.μ_fst` strips its two factors. -/
theorem left_toOverCompOverPostIso_inv_app_comp_fst (hu : u.IsMorphismOfSites J K)
    (A : Sheaf J (Type u)) :
    ((toOverCompOverPostIso J K u V hu).inv.app A).left ≫
        fst ((u.sheafPullback (Type u) J K).obj A)
          ((presheafToSheaf K (Type u)).obj (yoneda.obj (u.obj V))) =
      (u.sheafPullback (Type u) J K).map
        (fst A ((presheafToSheaf J (Type u)).obj (yoneda.obj V))) := by
  have := hu.preservesFiniteLimits
  exact inv_μIso_whiskerLeft_comp_fst (mF := .ofChosenFiniteProducts _)
    (u.sheafPullback (Type u) J K) A _ (yonedaIso J K u V hu).hom

/-- **The adjunct of Stacks 03CF's clause (b).**  Applying `j_{U!}` to the comparison of clause
(b) and composing with the counit of `j_{U!} ⊣ j_U^{-1}` gives the comparison
`j_{U!}(f')^{-1} ≅ f^{-1}j_{V!}` of the proof of Stacks 03CF followed by `f^{-1}` of the counit of
`j_{V!} ⊣ j_V^{-1}` — the same value that
`overPullbackCompSheafPullbackOverPostMate_comp_counit` gives for the mate.

Both sides are maps out of the sheaf underlying `Φ_U((f')^{-1}j_V^{-1}A)`, so they may be compared
after Stacks 00Y1's identification of that sheaf with `j_{U!}(f')^{-1}j_V^{-1}A`.  There the left
side becomes the composite of the four factors clause (b) is cancelled from, read through
`Over.forget`: clause (c) contributes `underlyingIso`, the middle two contribute `f^{-1}` of the
projection `j_{V!}j_V^{-1}A × h_V^# ⟶ j_{V!}j_V^{-1}A`, the last cancels against Stacks 04IQ at
`u(V)`, and 04IQ at `V` turns that projection into the counit. -/
theorem shriek_overPullbackCompSheafPullbackOverPostIso_hom_app_comp_counit
    (hu : u.IsMorphismOfSites J K) (A : Sheaf J (Type u)) :
    ((Over.forget (u.obj V)).sheafPullback (Type u) (K.over (u.obj V)) K).map
          ((overPullbackCompSheafPullbackOverPostIso J K u V hu).hom.app A) ≫
        ((Over.forget (u.obj V)).sheafAdjunctionContinuous (Type u) (K.over (u.obj V))
            K).counit.app ((u.sheafPullback (Type u) J K).obj A) =
      (sheafPullbackOverPostIso J K u V (Type u)).hom.app ((J.overPullback (Type u) V).obj A) ≫
        (u.sheafPullback (Type u) J K).map
          (((Over.forget V).sheafAdjunctionContinuous (Type u) (J.over V) J).counit.app A) := by
  -- The four factors clause (b) is cancelled from, with the last cancelled against 04IQ at `u(V)`.
  have hcomp : (sheafFunctorToOver (U := u.obj V) K).map
          ((overPullbackCompSheafPullbackOverPostIso J K u V hu).hom.app A) ≫
        (overPullbackCompSheafFunctorToOverIso (U := u.obj V) K).hom.app
          ((u.sheafPullback (Type u) J K).obj A) =
      (sheafFunctorToOverCompOverPostIso J K u V hu).hom.app ((J.overPullback (Type u) V).obj A) ≫
        (Over.post (u.sheafPullback (Type u) J K) ⋙
            Over.map (yonedaIso J K u V hu).hom).map
          ((overPullbackCompSheafFunctorToOverIso (U := V) J).hom.app A) ≫
        (toOverCompOverPostIso J K u V hu).inv.app A := by
    have hmap : (sheafFunctorToOver (U := u.obj V) K).map
          ((overPullbackCompSheafPullbackOverPostIso J K u V hu).hom.app A) =
        (sheafFunctorToOverCompOverPostIso J K u V hu).hom.app
            ((J.overPullback (Type u) V).obj A) ≫
          (Over.post (u.sheafPullback (Type u) J K) ⋙
              Over.map (yonedaIso J K u V hu).hom).map
            ((overPullbackCompSheafFunctorToOverIso (U := V) J).hom.app A) ≫
          ((toOverCompOverPostIso J K u V hu).inv.app A ≫
            (overPullbackCompSheafFunctorToOverIso (U := u.obj V) K).inv.app
              ((u.sheafPullback (Type u) J K).obj A)) :=
      (sheafFunctorToOver (U := u.obj V) K).map_preimage _
    rw [hmap]
    simp only [Category.assoc, Functor.comp_obj, Iso.inv_hom_id_app, Category.comp_id]
  -- Stacks 00Y1's identification is natural in the comparison of clause (b).
  have hnat : (sheafFunctorToOverForgetIso (U := u.obj V) K).hom.app
          (((Over.post (X := V) u).sheafPullback (Type u) (J.over V)
            (K.over (u.obj V))).obj ((J.overPullback (Type u) V).obj A)) ≫
        ((Over.forget (u.obj V)).sheafPullback (Type u) (K.over (u.obj V)) K).map
          ((overPullbackCompSheafPullbackOverPostIso J K u V hu).hom.app A) =
      ((sheafFunctorToOver (U := u.obj V) K).map
          ((overPullbackCompSheafPullbackOverPostIso J K u V hu).hom.app A)).left ≫
        (sheafFunctorToOverForgetIso (U := u.obj V) K).hom.app
          ((K.overPullback (Type u) (u.obj V)).obj ((u.sheafPullback (Type u) J K).obj A)) :=
    ((sheafFunctorToOverForgetIso (U := u.obj V) K).hom.naturality _).symm
  -- 04IQ at `V` turns the first projection into the counit of `j_{V!} ⊣ j_V^{-1}`.
  have hcounitV : (sheafFunctorToOverForgetIso (U := V) J).inv.app
          ((J.overPullback (Type u) V).obj A) ≫
        (((overPullbackCompSheafFunctorToOverIso (U := V) J).hom.app A).left ≫
          fst A ((presheafToSheaf J (Type u)).obj (yoneda.obj V))) =
      ((Over.forget V).sheafAdjunctionContinuous (Type u) (J.over V) J).counit.app A := by
    rw [left_overPullbackCompSheafFunctorToOverIso_hom_app_comp_fst (U := V) J A,
      ← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
  -- The two middle factors, read through `Over.forget` and followed by the first projection.
  have hmid : (u.sheafPullback (Type u) J K).map
          (((overPullbackCompSheafFunctorToOverIso (U := V) J).hom.app A).left) ≫
        (((toOverCompOverPostIso J K u V hu).inv.app A).left ≫
          fst ((u.sheafPullback (Type u) J K).obj A)
            ((presheafToSheaf K (Type u)).obj (yoneda.obj (u.obj V)))) =
      (u.sheafPullback (Type u) J K).map
        ((((overPullbackCompSheafFunctorToOverIso (U := V) J).hom.app A).left ≫
          fst A ((presheafToSheaf J (Type u)).obj (yoneda.obj V)))) :=
    (congrArg _ (left_toOverCompOverPostIso_inv_app_comp_fst J K u V hu A)).trans
      (Functor.map_comp _ _ _).symm
  -- The two ends of `underlyingIso` cancel the two copies of Stacks 00Y1's identification at `V`.
  have hunder : (underlyingIso J K u V).hom.app ((J.overPullback (Type u) V).obj A) ≫
        (u.sheafPullback (Type u) J K).map
          ((((overPullbackCompSheafFunctorToOverIso (U := V) J).hom.app A).left ≫
            fst A ((presheafToSheaf J (Type u)).obj (yoneda.obj V)))) =
      (sheafFunctorToOverForgetIso (U := u.obj V) K).hom.app
          (((Over.post (X := V) u).sheafPullback (Type u) (J.over V)
            (K.over (u.obj V))).obj ((J.overPullback (Type u) V).obj A)) ≫
        (sheafPullbackOverPostIso J K u V (Type u)).hom.app
            ((J.overPullback (Type u) V).obj A) ≫
          (u.sheafPullback (Type u) J K).map
            (((Over.forget V).sheafAdjunctionContinuous (Type u) (J.over V) J).counit.app A) := by
    rw [underlyingIso_hom_app, Category.assoc, Category.assoc, ← Functor.map_comp, hcounitV]
  -- The adjunct of clause (b), read through 00Y1 and 04IQ at `u(V)`.
  have hnat2 : ((sheafFunctorToOver (U := u.obj V) K).map
          ((overPullbackCompSheafPullbackOverPostIso J K u V hu).hom.app A) ≫
        (overPullbackCompSheafFunctorToOverIso (U := u.obj V) K).hom.app
          ((u.sheafPullback (Type u) J K).obj A)).left ≫
      fst ((u.sheafPullback (Type u) J K).obj A)
        ((presheafToSheaf K (Type u)).obj (yoneda.obj (u.obj V))) =
    (sheafFunctorToOverForgetIso (U := u.obj V) K).hom.app
          (((Over.post (X := V) u).sheafPullback (Type u) (J.over V)
            (K.over (u.obj V))).obj ((J.overPullback (Type u) V).obj A)) ≫
        ((Over.forget (u.obj V)).sheafPullback (Type u) (K.over (u.obj V)) K).map
            ((overPullbackCompSheafPullbackOverPostIso J K u V hu).hom.app A) ≫
          ((Over.forget (u.obj V)).sheafAdjunctionContinuous (Type u) (K.over (u.obj V))
              K).counit.app ((u.sheafPullback (Type u) J K).obj A) := by
    change ((sheafFunctorToOver (U := u.obj V) K).map
          ((overPullbackCompSheafPullbackOverPostIso J K u V hu).hom.app A)).left ≫
        (((overPullbackCompSheafFunctorToOverIso (U := u.obj V) K).hom.app
            ((u.sheafPullback (Type u) J K).obj A)).left ≫
          fst ((u.sheafPullback (Type u) J K).obj A)
            ((presheafToSheaf K (Type u)).obj (yoneda.obj (u.obj V)))) = _
    rw [left_overPullbackCompSheafFunctorToOverIso_hom_app_comp_fst (U := u.obj V) K
      ((u.sheafPullback (Type u) J K).obj A), ← Category.assoc, ← hnat, Category.assoc]
  -- The same adjunct, read through the four factors clause (b) is cancelled from.
  have hleft : ((sheafFunctorToOver (U := u.obj V) K).map
          ((overPullbackCompSheafPullbackOverPostIso J K u V hu).hom.app A) ≫
        (overPullbackCompSheafFunctorToOverIso (U := u.obj V) K).hom.app
          ((u.sheafPullback (Type u) J K).obj A)).left ≫
      fst ((u.sheafPullback (Type u) J K).obj A)
        ((presheafToSheaf K (Type u)).obj (yoneda.obj (u.obj V))) =
    (sheafFunctorToOverForgetIso (U := u.obj V) K).hom.app
          (((Over.post (X := V) u).sheafPullback (Type u) (J.over V)
            (K.over (u.obj V))).obj ((J.overPullback (Type u) V).obj A)) ≫
        (sheafPullbackOverPostIso J K u V (Type u)).hom.app
            ((J.overPullback (Type u) V).obj A) ≫
          (u.sheafPullback (Type u) J K).map
            (((Over.forget V).sheafAdjunctionContinuous (Type u) (J.over V) J).counit.app A) := by
    rw [hcomp]
    change ((sheafFunctorToOverCompOverPostIso J K u V hu).hom.app
          ((J.overPullback (Type u) V).obj A)).left ≫
        ((u.sheafPullback (Type u) J K).map
            (((overPullbackCompSheafFunctorToOverIso (U := V) J).hom.app A).left) ≫
          (((toOverCompOverPostIso J K u V hu).inv.app A).left ≫
            fst ((u.sheafPullback (Type u) J K).obj A)
              ((presheafToSheaf K (Type u)).obj (yoneda.obj (u.obj V))))) = _
    exact (congrArg (fun z => ((sheafFunctorToOverCompOverPostIso J K u V hu).hom.app
      ((J.overPullback (Type u) V).obj A)).left ≫ z) hmid).trans hunder
  exact (Iso.cancel_iso_hom_left ((sheafFunctorToOverForgetIso (U := u.obj V) K).app
    (((Over.post (X := V) u).sheafPullback (Type u) (J.over V) (K.over (u.obj V))).obj
      ((J.overPullback (Type u) V).obj A))) _ _).1 (hnat2.symm.trans hleft)

/-- **Stacks 03CF's clause (b) is the Beck–Chevalley mate of its clause (d).**

The comparison `(f')^{-1}j_V^{-1} ≅ j_U^{-1}f^{-1}` built from Stacks 00Y1 coincides with the mate
of the strict identity `f'_*j_U^{-1} = j_V^{-1}f_*`.  Since `j_{U!} ⊣ j_U^{-1}` is a bijection the
two transformations may be compared through their adjuncts, and those agree by
`shriek_overPullbackCompSheafPullbackOverPostIso_hom_app_comp_counit` and
`overPullbackCompSheafPullbackOverPostMate_comp_counit`.

This is what gives clause (b) computable components: every statement about the comparison can now
be read off the unit and counit composite defining the mate. -/
@[stacks 03CF "Clause (b) is the Beck-Chevalley mate of clause (d), which is what makes its
  components computable."]
theorem overPullbackCompSheafPullbackOverPostIso_hom (hu : u.IsMorphismOfSites J K) :
    (overPullbackCompSheafPullbackOverPostIso J K u V hu).hom =
      overPullbackCompSheafPullbackOverPostMate J K u V := by
  refine NatTrans.ext (funext fun A => ?_)
  refine (((Over.forget (u.obj V)).sheafAdjunctionContinuous (Type u) (K.over (u.obj V))
    K).homEquiv _ ((u.sheafPullback (Type u) J K).obj A)).symm.injective ?_
  rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit,
    shriek_overPullbackCompSheafPullbackOverPostIso_hom_app_comp_counit J K u V hu,
    overPullbackCompSheafPullbackOverPostMate_comp_counit]

/-- **The mate of Stacks 03CF's clause (d), composed with the counit of `f^{-1} ⊣ f_*`.**

At a direct image `f_*B` the comparison of clause (b), followed by `j_U^{-1}` of the counit of
`f^{-1} ⊣ f_*`, is the counit of `(f')^{-1} ⊣ f'_*` at `j_U^{-1}B`.

This is the second of the two equations the mates correspondence attaches to clause (d) — the
first being `overPullbackCompSheafPullbackOverPostMate_comp_counit` — and it is the form in which
the square of ringed topoi of Stacks 04J0 uses clause (b) on structure sheaves. -/
theorem overPullbackCompSheafPullbackOverPostIso_hom_app_comp_counit
    (hu : u.IsMorphismOfSites J K) (B : Sheaf K (Type u)) :
    (overPullbackCompSheafPullbackOverPostIso J K u V hu).hom.app
          ((u.sheafPushforwardContinuous (Type u) J K).obj B) ≫
        (K.overPullback (Type u) (u.obj V)).map
          ((u.sheafAdjunctionContinuous (Type u) J K).counit.app B) =
      ((Over.post (X := V) u).sheafAdjunctionContinuous (Type u) (J.over V)
          (K.over (u.obj V))).counit.app
        ((K.overPullback (Type u) (u.obj V)).obj B) := by
  -- Clause (d) is a strict identity, so the 2-cell it is the mate of has identity components.
  have hid : ((Over.post (X := V) u).sheafPullback (Type u) (J.over V) (K.over (u.obj V))).map
        ((eqToHom (sheafPushforwardContinuous_overPost_eq J K u V (Type u)).symm).app B) =
      𝟙 _ :=
    CategoryTheory.Functor.map_id _ _
  rw [overPullbackCompSheafPullbackOverPostIso_hom J K u V hu]
  refine (CategoryTheory.mateEquiv_counit_symm (u.sheafAdjunctionContinuous (Type u) J K)
      ((Over.post (X := V) u).sheafAdjunctionContinuous (Type u) (J.over V)
        (K.over (u.obj V)))
      (eqToHom (sheafPushforwardContinuous_overPost_eq J K u V (Type u)).symm) B).symm.trans ?_
  exact (congrArg (fun z => z ≫ ((Over.post (X := V) u).sheafAdjunctionContinuous (Type u)
    (J.over V) (K.over (u.obj V))).counit.app
      ((K.overPullback (Type u) (u.obj V)).obj B)) hid).trans (Category.id_comp _)

/-- The mate of Stacks 03CF's clause (d) is an isomorphism: it is clause (b). -/
theorem isIso_overPullbackCompSheafPullbackOverPostMate (hu : u.IsMorphismOfSites J K) :
    IsIso (overPullbackCompSheafPullbackOverPostMate J K u V) :=
  overPullbackCompSheafPullbackOverPostIso_hom J K u V hu ▸
    inferInstanceAs (IsIso (overPullbackCompSheafPullbackOverPostIso J K u V hu).hom)

end

end CategoryTheory.SliceTopos
