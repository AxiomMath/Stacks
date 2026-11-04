module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.PullbackTube

/-!
# Proper base change for the Zariski comparison: the surjective half

Let `S` be a locally quasi-compact Zariski situation, let `f : X ⟶ Y` be a morphism of its site
with underlying continuous map `g`, and let `F` be a sheaf of sets on the small Zariski site of
`X`. By `isIso_properDirectImageComparison_iff` the base-change map

`π_Y^{-1} g_* ⟶ f_{Zar,*} π_X^{-1}`

is an isomorphism exactly when the counit of the `Y`-side comparison adjunction is invertible at
every `f_{Zar,*} π_X^{-1} F`. `ProperBaseChange.lean` proves that counit objectwise **injective**
for a closed `g`; this file proves it objectwise **surjective** for a proper `g`, which completes
the proper direct image clause of Stacks 0DCU.

## The argument

A section `c` of `f_{Zar,*}π_X^{-1}F` over an object `Z` of `LC_Zar/Y` is a section of
`π_X^{-1}F` over the fibre product `Z ×_Y X`. Fix a point `z` of `Z` and write `y = Z.hom z`.

* `exists_tube_section` localizes `c` at each point of `Z ×_Y X` with coordinates `z` and a point
  `x` of the fibre `g^{-1}(y)`. Localization (`exists_opens_comparison_section_eq`) writes `c` as
  pulled back from a section `t` of `F` over an open subset of `X` on *some* open neighbourhood of
  that point, and the tube lemma (`exists_tube_of_mem`) shrinks that neighbourhood to a **tube**
  `V ×_Y W`. The tube is what makes the data usable: it says that `c` is the pullback of `t` along
  *every* arrow into `Z ×_Y X` whose two coordinates land in `V` and in `W`, and in particular
  along arrows through a *third* point of the fibre. That is the predicate `IsTubeSection`.
* `exists_opens_tube_section_eq` makes two tube sections of the same `c` over a common `z` agree
  near every point of the fibre lying in both tubes: the two tubes meet in a tube, `c` is the
  pullback of both local sections there, and germ detection
  (`exists_opens_eq_of_comparison_section_eq`) turns that into agreement of the two sections of
  `F` on an open neighbourhood.
* The fibre is quasi-compact, so finitely many tubes cover it and the intersection `V♯` of their
  bases is an open neighbourhood of `z`. Restricted to those finitely many tubes, the previous
  item is exactly the hypothesis of `exists_opens_preimage_glue_fibre`, which produces an open
  `W₀ ∋ y` and a section `r` of `F` over `g^{-1}W₀` agreeing with one of the local sections near
  every point of the fibre.
* `properBaseChange_map_eq_of_tube_cover` identifies the section of
  `π_Y^{-1}π_{Y,*}f_{Zar,*}π_X^{-1}F` built from `r` with `c` after a further shrinking of `V♯`:
  closedness of `g` turns the union of the opens on which `r` agrees with a local section into the
  preimage of an open `W₁ ∋ y`, and over `V♯ ∩ Z.hom^{-1}(W₀ ∩ W₁)` those opens pull back to a
  cover of the fibre product, on which the two sections agree. Equality of sections is local, so
  the sheaf condition for `π_X^{-1}F` finishes.
* `surjective_properBaseChangeCounit_app` globalizes. The arrows along which `c` is in the image
  of the counit form a sieve, covering by the previous step; the chosen preimages form a
  compatible family because the counit is **injective** (this is where the separated half is
  used); and the amalgamation has the right image because `f_{Zar,*}π_X^{-1}F` is separated.

## Main results

* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.IsTubeSection`: the predicate above.
* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.exists_tube_section`: every section is a
  tube section near a point of a fibre.
* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.exists_opens_tube_section_eq`: two tube
  sections of one section agree near every point of the fibre they share.
* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.exists_opens_counit_app_eq`: local
  surjectivity of the counit.
* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.surjective_properBaseChangeCounit_app` and
  `isIso_properBaseChangeCounit`: **proper base change for the Zariski comparison on sheaves of
  sets.**
* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.properDirectImageComparisonIsoOfProperMap`:
  **the proper direct image clause of Stacks 0DCU.**

## Implementation notes

Nothing here describes `π_X^{-1}` or `π_Y^{-1}`, which is what keeps the argument available at the
three independent universes of Stacks 0DCU: everything goes through the counit,
`exists_opens_comparison_section_eq`, `counit_app_comparisonSectionsIso` and germ detection. The
only input about the topology of a fibre product of the site is the tube lemma of
`PullbackTube.lean`; no properness, closedness or quasi-compactness of a base change of `g` is
used, and `exists_opens_preimage_glue_fibre` is applied to `g` itself.

`properDirectImageComparisonIsoOfProperMap` carries the tag for clause (7a) of Stacks 0DCU. It
is the unconditional form: its only hypothesis is the properness the source assumes, where
`properDirectImageComparisonIso` of `ProperDirectImage.lean`, which it specializes, instead
assumes the invertibility of the `Y`-side counit that properness is there to supply.

## References

* [Stacks Project, Section 21.31 (Tag 09WY)](https://stacks.math.columbia.edu/tag/09WY)
* [Stacks Project, Tag 0DCU](https://stacks.math.columbia.edu/tag/0DCU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace Stacks.Topology.LocallyQuasiCompactZariskiSituation

universe u w v

variable {S₀ : Set LocallyQuasiCompactHausdorff.{u}} {Bound : Cardinal.{u} → Cardinal.{u}}
variable (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound)

/-- The open subobject of `Z` cut out by an open subset of `Z.left`. -/
abbrev opensOver {T : S.category} (Z : Over T) (V : Opens Z.left.obj) : Over T :=
  Over.mk ((((S.opensToSlice Z.left).1.obj V).hom) ≫ Z.hom)

/-- The inclusion of an open subobject of `Z` into `Z`. -/
abbrev opensOverι {T : S.category} (Z : Over T) (V : Opens Z.left.obj) :
    opensOver S Z V ⟶ Z :=
  Over.homMk (((S.opensToSlice Z.left).1.obj V).hom)

/-- The preimage in `Z.left` of an open subset of `T`. -/
abbrev preimageOpens {T : S.category} (Z : Over T) (M : Opens T.obj) : Opens Z.left.obj :=
  (Opens.map ((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).map Z.hom)).obj M

/-- Membership in the preimage of an open subset of `T`. -/
theorem mem_preimageOpens {T : S.category} {Z : Over T} {M : Opens T.obj} {p : Z.left.obj} :
    p ∈ preimageOpens S Z M ↔ (Z.hom : Z.left.obj → T.obj) p ∈ M := Iff.rfl

/-- A composite of morphisms over `T`, read on a point. -/
theorem over_hom_comp_left_apply {T : S.category} {A B C : Over T} (α : A ⟶ B) (β : B ⟶ C)
    (a : A.left.obj) :
    ((α ≫ β).left : A.left.obj → C.left.obj) a =
      (β.left : B.left.obj → C.left.obj) ((α.left : A.left.obj → B.left.obj) a) := rfl

/-- The structure morphism of an open subobject of `Z`, read on a point. -/
theorem opensOver_hom_apply {T : S.category} (Z : Over T) (V : Opens Z.left.obj)
    (e : (opensOver S Z V).left.obj) :
    ((opensOver S Z V).hom : (opensOver S Z V).left.obj → T.obj) e =
      (Z.hom : Z.left.obj → T.obj)
        ((((S.opensToSlice Z.left).1.obj V).hom : _ → Z.left.obj) e) := rfl

variable {X Y : S.category} (f : X ⟶ Y)

/-- `over_pullback_map_left_fst`, read on a point. -/
theorem over_pullback_map_fst_apply {P Z : Over Y} (m : P ⟶ Z)
    (ρ : ((Over.pullback f).obj P).left.obj) :
    (Limits.pullback.fst Z.hom f : _ → _)
        ((((Over.pullback f).map m).left : ((Over.pullback f).obj P).left.obj → _) ρ) =
      (m.left : P.left.obj → Z.left.obj) ((Limits.pullback.fst P.hom f : _ → _) ρ) :=
  congrArg (fun k : ((Over.pullback f).obj P).left ⟶ Z.left => (k : _ → Z.left.obj) ρ)
    (over_pullback_map_left_fst S f m)

/-- A section `c` of `π_X^{-1}F` over `Z ×_Y X` **is the tube section of `t`** on the tube
`V ×_Y W`: along every arrow of the localized site over `X` into `Z ×_Y X` whose image has first
coordinate in `V` and second coordinate in `W`, the section `c` restricts to the pullback of `t`.

The two coordinate conditions are what the gluing argument of the surjective half of proper base
change needs, and the tube lemma `exists_tube_of_mem` is what produces them. -/
def IsTubeSection (F : Sheaf (Opens.grothendieckTopology X.obj) (Type (max (u + 1) v)))
    {Z : Over Y}
    (c : ((S.comparisonInverseImage.{u, w, max (u + 1) v} X).obj F).obj.obj
      (op ((Over.pullback f).obj Z)))
    (V : Opens Z.left.obj) (W : Opens X.obj) (t : F.obj.obj (op W)) : Prop :=
  ∀ (E : Over X) (κ : E ⟶ (Over.pullback f).obj Z),
    (∀ e : E.left.obj,
      (Limits.pullback.fst Z.hom f : _ → _) ((κ.left : E.left.obj → _) e) ∈ V) →
    (∀ e : E.left.obj,
      (Limits.pullback.snd Z.hom f : _ → _) ((κ.left : E.left.obj → _) e) ∈ W) →
    ∀ μ : E ⟶ (S.opensToSlice X).1.obj W,
      ((S.comparisonInverseImage.{u, w, max (u + 1) v} X).obj F).obj.map κ.op c =
        ((S.comparisonInverseImage.{u, w, max (u + 1) v} X).obj F).obj.map μ.op
          ((comparisonSectionsIso.{u, w, max (u + 1) v} S X F W).hom t)

/-- Shrinking the base of a tube preserves the tube-section property. -/
theorem IsTubeSection.mono_left
    {F : Sheaf (Opens.grothendieckTopology X.obj) (Type (max (u + 1) v))} {Z : Over Y}
    {c : ((S.comparisonInverseImage.{u, w, max (u + 1) v} X).obj F).obj.obj
      (op ((Over.pullback f).obj Z))}
    {V V' : Opens Z.left.obj} {W : Opens X.obj} {t : F.obj.obj (op W)}
    (h : IsTubeSection.{u, w, v} S f F c V W t) (hV : V' ≤ V) :
    IsTubeSection.{u, w, v} S f F c V' W t :=
  fun E κ hκV hκW μ => h E κ (fun e => hV (hκV e)) hκW μ

/-- Restricting the localization of a section of `F` to a smaller open `W'` along `μ` is the
localization of the section along `μ` followed by the inclusion of `W'` into `W`. -/
private theorem comparison_map_sectionsIso_hom_restrict
    (F : Sheaf (Opens.grothendieckTopology X.obj) (Type (max (u + 1) v)))
    {W W' : Opens X.obj} (h : W' ≤ W) (t : F.obj.obj (op W)) {E : Over X}
    (μ : E ⟶ (S.opensToSlice X).1.obj W') :
    ((S.comparisonInverseImage.{u, w, max (u + 1) v} X).obj F).obj.map μ.op
        ((comparisonSectionsIso.{u, w, max (u + 1) v} S X F W').hom
          (F.obj.map (homOfLE h).op t)) =
      ((S.comparisonInverseImage.{u, w, max (u + 1) v} X).obj F).obj.map
        (μ ≫ (S.opensToSlice X).1.map (homOfLE h)).op
        ((comparisonSectionsIso.{u, w, max (u + 1) v} S X F W).hom t) := by
  rw [← presheaf_map_op_comp_apply, comparisonSectionsIso_hom_naturality.{u, w, v} S X F h]

/-- **Every section of `π_X^{-1}F` over `Z ×_Y X` is a tube section near a point of a fibre.**
Localizing `c` at the point of `Z ×_Y X` with coordinates `z` and `x` writes it as pulled back
from a section of `F` over an open subset of `X` on an open neighbourhood, and the tube lemma
shrinks that neighbourhood to a tube. -/
theorem exists_tube_section
    (F : Sheaf (Opens.grothendieckTopology X.obj) (Type (max (u + 1) v)))
    {Z : Over Y}
    (c : ((S.comparisonInverseImage.{u, w, max (u + 1) v} X).obj F).obj.obj
      (op ((Over.pullback f).obj Z)))
    (z : Z.left.obj) (x : X.obj)
    (hzx : (Z.hom : Z.left.obj → Y.obj) z = (f : X.obj → Y.obj) x) :
    ∃ (V : Opens Z.left.obj) (W : Opens X.obj) (_ : z ∈ V) (_ : x ∈ W)
      (t : F.obj.obj (op W)), IsTubeSection.{u, w, v} S f F c V W t := by
  classical
  obtain ⟨ξ, hξ1, hξ2⟩ := exists_site_pullback_point S f Z.hom z x hzx
  obtain ⟨N, hξN, W₂, cm, b, heq⟩ :=
    exists_opens_comparison_section_eq.{u, w, v} S X F c ξ
  obtain ⟨V, W', hzV, hxW', htube⟩ := exists_tube_of_mem S f Z.hom N hξN
  rw [hξ1] at hzV
  rw [hξ2] at hxW'
  have hxW₂ : x ∈ W₂ := hξ2 ▸ opensToSlice_mem_of_over_hom S cm hξN
  obtain ⟨t₂, hb⟩ : ∃ t₂ : F.obj.obj (op W₂),
      b = (comparisonSectionsIso.{u, w, max (u + 1) v} S X F W₂).hom t₂ :=
    ⟨(comparisonSectionsIso.{u, w, max (u + 1) v} S X F W₂).inv b,
      (type_iso_hom_inv_apply _ b).symm⟩
  refine ⟨V, W₂ ⊓ W', hzV, ⟨hxW₂, hxW'⟩,
    F.obj.map (homOfLE (inf_le_left : W₂ ⊓ W' ≤ W₂)).op t₂, ?_⟩
  intro E κ hκV hκW μ
  have hκN : ∀ e : E.left.obj, (κ.left : E.left.obj → _) e ∈ N :=
    fun e => htube _ (hκV e) (hκW e).2
  obtain ⟨θ, hθ⟩ := exists_over_hom_opensToSlice_factor S κ N hκN
  rw [← hθ, ← presheaf_map_op_comp_apply, heq, presheaf_map_op_comp_apply,
    over_hom_opensToSlice_ext S (θ ≫ cm)
      (μ ≫ (S.opensToSlice X).1.map (homOfLE (inf_le_left : W₂ ⊓ W' ≤ W₂))), hb,
    comparison_map_sectionsIso_hom_restrict S F inf_le_left]

/-- **Two tube sections of the same `c` agree near every point of the fibre they share.** The
two tubes over a common point `z` of `Z` meet in a tube, and `c` is pulled back from both local
sections there, so germ detection (`exists_opens_eq_of_comparison_section_eq`) makes the two
local sections agree on an open neighbourhood of the point. -/
theorem exists_opens_tube_section_eq
    (F : Sheaf (Opens.grothendieckTopology X.obj) (Type (max (u + 1) v)))
    {Z : Over Y}
    (c : ((S.comparisonInverseImage.{u, w, max (u + 1) v} X).obj F).obj.obj
      (op ((Over.pullback f).obj Z)))
    {z : Z.left.obj} {x : X.obj}
    (hzx : (Z.hom : Z.left.obj → Y.obj) z = (f : X.obj → Y.obj) x)
    {V₁ V₂ : Opens Z.left.obj} {W₁ W₂ : Opens X.obj}
    {t₁ : F.obj.obj (op W₁)} {t₂ : F.obj.obj (op W₂)}
    (h₁ : IsTubeSection.{u, w, v} S f F c V₁ W₁ t₁)
    (h₂ : IsTubeSection.{u, w, v} S f F c V₂ W₂ t₂)
    (hz₁ : z ∈ V₁) (hz₂ : z ∈ V₂) (hx₁ : x ∈ W₁) (hx₂ : x ∈ W₂) :
    ∃ (M : Opens X.obj) (_ : x ∈ M) (g₁ : M ≤ W₁) (g₂ : M ≤ W₂),
      F.obj.map (homOfLE g₁).op t₁ = F.obj.map (homOfLE g₂).op t₂ := by
  classical
  obtain ⟨ξ, hξ1, hξ2⟩ := exists_site_pullback_point S f Z.hom z x hzx
  let T : Opens ((Over.pullback f).obj Z).left.obj :=
    ⟨{q | (Limits.pullback.fst Z.hom f : _ → _) q ∈ V₁ ⊓ V₂ ∧
        (Limits.pullback.snd Z.hom f : _ → _) q ∈ W₁ ⊓ W₂},
      ((V₁ ⊓ V₂).isOpen.preimage (by fun_prop)).inter
        ((W₁ ⊓ W₂).isOpen.preimage (by fun_prop))⟩
  have hξT : ξ ∈ T := ⟨hξ1 ▸ ⟨hz₁, hz₂⟩, hξ2 ▸ ⟨hx₁, hx₂⟩⟩
  have hTmem : ∀ e : (opensOver S ((Over.pullback f).obj Z) T).left.obj,
      ((((S.opensToSlice ((Over.pullback f).obj Z).left).1.obj T).hom) :
        _ → ((Over.pullback f).obj Z).left.obj) e ∈ T :=
    opensToSlice_hom_mem S T
  obtain ⟨μ⟩ := nonempty_over_hom_opensToSlice S
    (opensOver S ((Over.pullback f).obj Z) T) (W₁ ⊓ W₂) (fun e => (hTmem e).2)
  have key₁ := h₁ _ (opensOverι S ((Over.pullback f).obj Z) T)
    (fun e => (hTmem e).1.1) (fun e => (hTmem e).2.1)
    (μ ≫ (S.opensToSlice X).1.map (homOfLE (inf_le_left : W₁ ⊓ W₂ ≤ W₁)))
  have key₂ := h₂ _ (opensOverι S ((Over.pullback f).obj Z) T)
    (fun e => (hTmem e).1.2) (fun e => (hTmem e).2.2)
    (μ ≫ (S.opensToSlice X).1.map (homOfLE (inf_le_right : W₁ ⊓ W₂ ≤ W₂)))
  have hps : ((S.comparisonInverseImage.{u, w, max (u + 1) v} X).obj F).obj.map μ.op
        ((comparisonSectionsIso.{u, w, max (u + 1) v} S X F (W₁ ⊓ W₂)).hom
          (F.obj.map (homOfLE (inf_le_left : W₁ ⊓ W₂ ≤ W₁)).op t₁)) =
      ((S.comparisonInverseImage.{u, w, max (u + 1) v} X).obj F).obj.map μ.op
        ((comparisonSectionsIso.{u, w, max (u + 1) v} S X F (W₁ ⊓ W₂)).hom
          (F.obj.map (homOfLE (inf_le_right : W₁ ⊓ W₂ ≤ W₂)).op t₂)) := by
    rw [comparison_map_sectionsIso_hom_restrict S F inf_le_left,
      comparison_map_sectionsIso_hom_restrict S F inf_le_right, ← key₁, ← key₂]
  obtain ⟨p, hp⟩ := exists_opensToSlice_preimage S
    (Z := (Over.pullback f).obj Z) T hξT
  obtain ⟨M, hxM, hMW, heqM⟩ :=
    exists_opens_eq_of_comparison_section_eq.{u, w, v} S X F μ _ _ p hps
  have hpx : ((opensOver S ((Over.pullback f).obj Z) T).hom : _ → X.obj) p = x := by
    rwa [opensOver_hom_apply, hp]
  rw [hpx] at hxM
  refine ⟨M, hxM, hMW.trans inf_le_left, hMW.trans inf_le_right, ?_⟩
  rwa [← opens_map_op_comp_apply F.obj (homOfLE hMW)
      (homOfLE (inf_le_left : W₁ ⊓ W₂ ≤ W₁)) (homOfLE (hMW.trans inf_le_left)) t₁,
    ← opens_map_op_comp_apply F.obj (homOfLE hMW)
      (homOfLE (inf_le_right : W₁ ⊓ W₂ ≤ W₂)) (homOfLE (hMW.trans inf_le_right)) t₂]

/-- The sections isomorphism of `π_{Y,*}f_{Zar,*}π_X^{-1}F`, read as a section of `π_X^{-1}F`
over the fibre product: the two are related by `zariskiOpenPullbackIso`. -/
theorem properBaseChangeSectionsIso_hom_map
    (F : Sheaf (Opens.grothendieckTopology X.obj) (Type (max (u + 1) v)))
    {P : Over Y} {W : Opens Y.obj} (d : P ⟶ (S.opensToSlice Y).1.obj W)
    (r : F.obj.obj (op ((Opens.map
      ((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).map f)).obj W))) :
    (properBaseChangeSheaf.{u, w, v} S f F).obj.map d.op
        ((properBaseChangeSectionsIso.{u, w, v} S f F W).hom r) =
      ((S.comparisonInverseImage.{u, w, max (u + 1) v} X).obj F).obj.map
        ((Over.pullback f).map d ≫ ((zariskiOpenPullbackIso S f).app W).inv).op
        ((comparisonSectionsIso.{u, w, max (u + 1) v} S X F _).hom r) := by
  rw [op_comp, Functor.map_comp, types_comp_apply]
  rfl

/-- Restriction in `f_{Zar,*}π_X^{-1}F` is restriction in `π_X^{-1}F` along the base change. -/
theorem properBaseChangeSheaf_map_eq
    (F : Sheaf (Opens.grothendieckTopology X.obj) (Type (max (u + 1) v)))
    {Z Z' : Over Y} (k : Z' ⟶ Z)
    (c : (properBaseChangeSheaf.{u, w, v} S f F).obj.obj (op Z)) :
    (properBaseChangeSheaf.{u, w, v} S f F).obj.map k.op c =
      ((S.comparisonInverseImage.{u, w, max (u + 1) v} X).obj F).obj.map
        ((Over.pullback f).map k).op c :=
  rfl

/-- **The local comparison of a tube section with a section of `F`.** If a section `r` of `F`
over `g^{-1}W₀` agrees with the local section `ti` of a tube on an open `M`, then along any arrow
into `Z ×_Y X` landing in the tube and mapping into `M`, the section `c` restricts to the
pullback of `r`. -/
theorem IsTubeSection.map_eq_of_restrict_eq
    {F : Sheaf (Opens.grothendieckTopology X.obj) (Type (max (u + 1) v))}
    {Z : Over Y}
    {c : ((S.comparisonInverseImage.{u, w, max (u + 1) v} X).obj F).obj.obj
      (op ((Over.pullback f).obj Z))}
    {Vi : Opens Z.left.obj} {Wi : Opens X.obj} {ti : F.obj.obj (op Wi)}
    (htube : IsTubeSection.{u, w, v} S f F c Vi Wi ti)
    {W₀ : Opens Y.obj}
    {r : F.obj.obj (op ((Opens.map
      ((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).map f)).obj W₀))}
    {M : Opens X.obj} (hMWi : M ≤ Wi)
    (hMg : M ≤ (Opens.map
      ((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).map f)).obj W₀)
    (hr : F.obj.map (homOfLE hMg).op r = F.obj.map (homOfLE hMWi).op ti)
    (E : Over X) (κ : E ⟶ (Over.pullback f).obj Z)
    (hκV : ∀ e : E.left.obj,
      (Limits.pullback.fst Z.hom f : _ → _) ((κ.left : E.left.obj → _) e) ∈ Vi)
    (hκM : ∀ e : E.left.obj, (E.hom : E.left.obj → X.obj) e ∈ M)
    (lam : E ⟶ (S.opensToSlice X).1.obj ((Opens.map
      ((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).map f)).obj W₀)) :
    ((S.comparisonInverseImage.{u, w, max (u + 1) v} X).obj F).obj.map κ.op c =
      ((S.comparisonInverseImage.{u, w, max (u + 1) v} X).obj F).obj.map lam.op
        ((comparisonSectionsIso.{u, w, max (u + 1) v} S X F _).hom r) := by
  obtain ⟨μ⟩ := nonempty_over_hom_opensToSlice S E M hκM
  have hsnd : ∀ e : E.left.obj,
      (Limits.pullback.snd Z.hom f : _ → _) ((κ.left : E.left.obj → _) e) ∈ Wi := by
    intro e
    have hw : (Limits.pullback.snd Z.hom f : _ → _) ((κ.left : E.left.obj → _) e) =
        (E.hom : E.left.obj → X.obj) e :=
      congrArg (fun k : E.left ⟶ X => (k : E.left.obj → X.obj) e) (Over.w κ)
    rw [hw]
    exact hMWi (hκM e)
  rw [htube E κ hκV hsnd (μ ≫ (S.opensToSlice X).1.map (homOfLE hMWi)),
    ← comparison_map_sectionsIso_hom_restrict S F hMWi, ← hr,
    comparison_map_sectionsIso_hom_restrict S F hMg,
    over_hom_opensToSlice_ext S (μ ≫ (S.opensToSlice X).1.map (homOfLE hMg)) lam]

/-- **The comparison of a section of `F` over `g^{-1}W₀` with a section of `π_X^{-1}F`, from
local tube data.** If every point of `P ×_Y X` has an open neighbourhood in `X` on which `r`
agrees with the local section of a tube containing all of `P`, then `c` restricted to `P ×_Y X`
is the pullback of `r`.

Equality of sections is local, so this is the sheaf condition for `π_X^{-1}F` on the covering
sieve generated by the preimages in `P ×_Y X` of those open subsets of `X`. -/
theorem properBaseChange_map_eq_of_tube_cover
    (F : Sheaf (Opens.grothendieckTopology X.obj) (Type (max (u + 1) v)))
    {Z : Over Y}
    (c : ((S.comparisonInverseImage.{u, w, max (u + 1) v} X).obj F).obj.obj
      (op ((Over.pullback f).obj Z)))
    {P : Over Y} (m : P ⟶ Z) {V : Opens Z.left.obj}
    (hmV : ∀ p : P.left.obj, (m.left : P.left.obj → Z.left.obj) p ∈ V)
    {W₀ : Opens Y.obj}
    (r : F.obj.obj (op ((Opens.map
      ((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).map f)).obj W₀)))
    (lam : (Over.pullback f).obj P ⟶ (S.opensToSlice X).1.obj ((Opens.map
      ((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).map f)).obj W₀))
    (hloc : ∀ ρ : ((Over.pullback f).obj P).left.obj,
      ∃ (M : Opens X.obj) (_ : (((Over.pullback f).obj P).hom :
          ((Over.pullback f).obj P).left.obj → X.obj) ρ ∈ M)
        (Wi : Opens X.obj) (ti : F.obj.obj (op Wi))
        (_ : IsTubeSection.{u, w, v} S f F c V Wi ti) (hMWi : M ≤ Wi)
        (hMg : M ≤ (Opens.map
          ((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).map f)).obj W₀),
        F.obj.map (homOfLE hMg).op r = F.obj.map (homOfLE hMWi).op ti) :
    ((S.comparisonInverseImage.{u, w, max (u + 1) v} X).obj F).obj.map
        ((Over.pullback f).map m).op c =
      ((S.comparisonInverseImage.{u, w, max (u + 1) v} X).obj F).obj.map lam.op
        ((comparisonSectionsIso.{u, w, max (u + 1) v} S X F _).hom r) := by
  classical
  let Rs : Sieve ((Over.pullback f).obj P) :=
    { arrows := fun T k =>
        ((S.comparisonInverseImage.{u, w, max (u + 1) v} X).obj F).obj.map k.op
            (((S.comparisonInverseImage.{u, w, max (u + 1) v} X).obj F).obj.map
              ((Over.pullback f).map m).op c) =
          ((S.comparisonInverseImage.{u, w, max (u + 1) v} X).obj F).obj.map k.op
            (((S.comparisonInverseImage.{u, w, max (u + 1) v} X).obj F).obj.map lam.op
              ((comparisonSectionsIso.{u, w, max (u + 1) v} S X F _).hom r))
      downward_closed := by
        intro T T' k hk k'
        rw [← presheaf_map_op_comp_apply, ← presheaf_map_op_comp_apply, hk] }
  have hcover : ∀ ρ : ((Over.pullback f).obj P).left.obj,
      ∃ O : Opens ((Over.pullback f).obj P).left.obj, ρ ∈ O ∧
        Rs.arrows (opensOverι S ((Over.pullback f).obj P) O) := by
    intro ρ
    obtain ⟨M, hρM, Wi, ti, htube, hMWi, hMg, hr⟩ := hloc ρ
    refine ⟨preimageOpens S ((Over.pullback f).obj P) M, hρM, ?_⟩
    have hkey := htube.map_eq_of_restrict_eq S f hMWi hMg hr
      (opensOver S ((Over.pullback f).obj P) (preimageOpens S ((Over.pullback f).obj P) M))
      (opensOverι S ((Over.pullback f).obj P) (preimageOpens S ((Over.pullback f).obj P) M) ≫
        (Over.pullback f).map m)
      (fun e => by
        rw [over_hom_comp_left_apply, over_pullback_map_fst_apply]
        exact hmV _)
      (fun e => opensToSlice_hom_mem S _ e)
      (opensOverι S ((Over.pullback f).obj P) (preimageOpens S ((Over.pullback f).obj P) M) ≫
        lam)
    exact (presheaf_map_op_comp_apply _ _ _ c).trans
      (hkey.trans (presheaf_map_op_comp_apply _ _ _ _).symm)
  choose O hρO hOR using hcover
  have hR : Rs ∈ (S.zariskiTopology.over X) ((Over.pullback f).obj P) :=
    mem_zariskiTopology_over_of_opens_cover S O (fun ρ => ⟨ρ, hρO ρ⟩) Rs hOR
  exact ((isSheaf_iff_isSheaf_of_type _ _).1
    ((S.comparisonInverseImage.{u, w, max (u + 1) v} X).obj F).property _ hR).isSeparatedFor.ext
      (fun _ k hk => hk)

/-- **The local sections of `F` on a cover of a fibre by tubes glue over a neighbourhood of the
base point.** For a proper `g` the fibre over `y = Z.hom z` is quasi-compact, so finitely many of
the tubes of `exists_tube_section` cover it and the intersection `V` of their bases is an open
neighbourhood of `z`; two of the local sections agree near every point of the fibre they share
(`exists_opens_tube_section_eq`), so `exists_opens_preimage_glue_fibre` glues them into a section
`r` of `F` over `g^{-1}W₀` which near every point of the fibre agrees with the local section of a
tube whose base contains `V`. -/
theorem exists_opens_glued_tube_section
    (hp : _root_.IsProperMap
      (((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).map f) : X.obj → Y.obj))
    (F : Sheaf (Opens.grothendieckTopology X.obj) (Type (max (u + 1) v)))
    {Z : Over Y} (c : (properBaseChangeSheaf.{u, w, v} S f F).obj.obj (op Z))
    (z : Z.left.obj) :
    ∃ (V : Opens Z.left.obj) (_ : z ∈ V) (W₀ : Opens Y.obj)
      (_ : (Z.hom : Z.left.obj → Y.obj) z ∈ W₀)
      (r : F.obj.obj (op ((Opens.map
        ((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).map f)).obj W₀))),
      ∀ i : {x : X.obj //
        (((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).map f) : X.obj → Y.obj) x =
          (Z.hom : Z.left.obj → Y.obj) z},
        ∃ (M : Opens X.obj) (_ : i.1 ∈ M) (Wi : Opens X.obj) (ti : F.obj.obj (op Wi))
          (_ : IsTubeSection.{u, w, v} S f F (Z := Z) c V Wi ti) (hMWi : M ≤ Wi)
          (hMg : M ≤ (Opens.map
            ((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).map f)).obj W₀),
          F.obj.map (homOfLE hMg).op r = F.obj.map (homOfLE hMWi).op ti := by
  classical
  choose Vt Wt hzVt hxWt tt htt using fun i : {x : X.obj //
      (((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).map f) : X.obj → Y.obj) x =
        (Z.hom : Z.left.obj → Y.obj) z} =>
    exists_tube_section.{u, w, v} S f F (Z := Z) c z i.1 i.2.symm
  have hK : IsCompact
      ((((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).map f) : X.obj → Y.obj) ⁻¹'
        {(Z.hom : Z.left.obj → Y.obj) z}) :=
    hp.isCompact_preimage isCompact_singleton
  obtain ⟨tfin, htfin⟩ := hK.elim_finite_subcover (fun i => (Wt i : Set X.obj))
    (fun i => (Wt i).isOpen)
    (fun x hx => Set.mem_iUnion.2 ⟨⟨x, hx⟩, hxWt ⟨x, hx⟩⟩)
  let Vsharp : Opens Z.left.obj :=
    ⟨⋂ i ∈ (tfin : Set _), (Vt i : Set Z.left.obj),
      tfin.finite_toSet.isOpen_biInter (fun i _ => (Vt i).isOpen)⟩
  have hVsharpLe : ∀ i, i ∈ tfin → Vsharp ≤ Vt i :=
    fun i hi _ hmem => Set.mem_iInter₂.1 hmem i hi
  obtain ⟨W₀, hyW₀, -, r, hr⟩ := exists_opens_preimage_glue_fibre S f
    hp.isClosedMap F hK ⊤ trivial
    (fun i : {i : {x : X.obj //
      (((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).map f) : X.obj → Y.obj) x =
        (Z.hom : Z.left.obj → Y.obj) z} // i ∈ tfin} => Wt i.1) (fun i => tt i.1)
    (fun x hx => by
      obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.1 (htfin hx)
      exact ⟨⟨i, hi⟩, hxi⟩)
    (fun i j x hx hxi hxj => by
      obtain ⟨M, hxM, g₁, g₂, heq⟩ :=
        exists_opens_tube_section_eq.{u, w, v} S f F (Z := Z) c hx.symm
          (htt i.1) (htt j.1) (hzVt i.1) (hzVt j.1) hxi hxj
      exact ⟨M, hxM, homOfLE g₁, homOfLE g₂, heq⟩)
  refine ⟨Vsharp, Set.mem_biInter fun i _ => hzVt i, W₀, hyW₀, r, fun i => ?_⟩
  obtain ⟨j, M, hxM, iM₀, iMj, heq⟩ := hr i.1 i.2
  refine ⟨M, hxM, Wt j.1, tt j.1, (htt j.1).mono_left S f (hVsharpLe j.1 j.2), iMj.le, iM₀.le, ?_⟩
  rwa [Subsingleton.elim (homOfLE iM₀.le) iM₀, Subsingleton.elim (homOfLE iMj.le) iMj]

/-- **Local surjectivity of the counit at `f_{Zar,*}π_X^{-1}F`.** For a proper `g`, every section
`c` of `f_{Zar,*}π_X^{-1}F` over an object `Z` of the localized site is, on an open neighbourhood
of every point `z` of `Z`, the image under the counit of a section of
`π_Y^{-1}π_{Y,*}f_{Zar,*}π_X^{-1}F`.

The proof is the classical one. The local sections of `F` on a cover of the fibre of `g` over
`y = Z.hom z` by tubes glue into a section `r` over `g^{-1}W₀`
(`exists_opens_glued_tube_section`), and the glued section is compared with `c` over the preimage
of a smaller neighbourhood, chosen using closedness of `g` so that every point of the fibre
product above it lies in one of the opens on which the comparison is known
(`properBaseChange_map_eq_of_tube_cover`). -/
theorem exists_opens_counit_app_eq
    (hp : _root_.IsProperMap
      (((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).map f) : X.obj → Y.obj))
    (F : Sheaf (Opens.grothendieckTopology X.obj) (Type (max (u + 1) v)))
    {Z : Over Y} (c : (properBaseChangeSheaf.{u, w, v} S f F).obj.obj (op Z))
    (z : Z.left.obj) :
    ∃ (V : Opens Z.left.obj) (_ : z ∈ V)
      (a : (properBaseChangeUnitSheaf.{u, w, v} S f F).obj.obj (op (opensOver S Z V))),
      (properBaseChangeCounit.{u, w, v} S f F).hom.app (op (opensOver S Z V)) a =
        (properBaseChangeSheaf.{u, w, v} S f F).obj.map (opensOverι S Z V).op c := by
  classical
  obtain ⟨V, hzV, W₀, hyW₀, r, hglue⟩ :=
    exists_opens_glued_tube_section.{u, w, v} S f hp F (Z := Z) c z
  choose Mg hMgmem Wg tg htg hMgW hMgg hMgeq using hglue
  obtain ⟨W₁, hW₁open, hyW₁, hW₁sub⟩ :=
    Stacks.Topology.exists_isOpen_preimage_subset_of_isClosedMap hp.isClosedMap
      (y := (Z.hom : Z.left.obj → Y.obj) z)
      (W := ((⨆ i, Mg i : Opens X.obj) : Set X.obj)) (⨆ i, Mg i).isOpen
      (fun x hx => Opens.mem_iSup.2 ⟨⟨x, hx⟩, hMgmem ⟨x, hx⟩⟩)
  let V' : Opens Z.left.obj :=
    V ⊓ preimageOpens S Z W₀ ⊓ preimageOpens S Z ⟨W₁, hW₁open⟩
  obtain ⟨d⟩ := nonempty_over_hom_opensToSlice S (opensOver S Z V') W₀
    (fun e => (opensToSlice_hom_mem S V' e).1.2)
  refine ⟨V', ⟨⟨hzV, hyW₀⟩, hyW₁⟩,
    (properBaseChangeUnitSheaf.{u, w, v} S f F).obj.map d.op
      ((comparisonSectionsIso.{u, w, max (u + 1) v} S Y
        ((S.comparisonDirectImage Y (Type (max (u + 1) v))).obj
          (properBaseChangeSheaf.{u, w, v} S f F)) W₀).hom
        ((properBaseChangeSectionsIso.{u, w, v} S f F W₀).hom r)), ?_⟩
  rw [properBaseChangeCounit_naturality_apply, counit_app_comparisonSectionsIso,
    properBaseChangeSectionsIso_hom_map, properBaseChangeSheaf_map_eq]
  refine (properBaseChange_map_eq_of_tube_cover S f F (Z := Z) c (opensOverι S Z V')
    (fun p => opensToSlice_hom_mem S V' p) r
    ((Over.pullback f).map d ≫ ((zariskiOpenPullbackIso S f).app W₀).inv) ?_).symm
  intro ρ
  have hρ : ((opensOver S Z V').hom : (opensOver S Z V').left.obj → Y.obj)
      ((Limits.pullback.fst (opensOver S Z V').hom f : _ → _) ρ) ∈ W₁ :=
    (opensToSlice_hom_mem S V' _).2
  rw [← site_pullback_condition_apply S f ρ] at hρ
  obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (hW₁sub hρ)
  exact ⟨Mg i, hi, Wg i, tg i, (htg i).mono_left S f (inf_le_left.trans inf_le_left),
    hMgW i, hMgg i, hMgeq i⟩

/-- **Surjectivity of the counit at `f_{Zar,*}π_X^{-1}F`**, for a proper `g`. Surjectivity is
local on `Z` because the counit is injective: the arrows along which a section of
`f_{Zar,*}π_X^{-1}F` is in the image of the counit form a sieve, which is covering by
`exists_opens_counit_app_eq`, the chosen preimages are a compatible family because two of them
with the same counit image agree, and the amalgamation has the right counit image because
`f_{Zar,*}π_X^{-1}F` is separated for that sieve. -/
theorem surjective_properBaseChangeCounit_app
    (hp : _root_.IsProperMap
      (((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).map f) : X.obj → Y.obj))
    (F : Sheaf (Opens.grothendieckTopology X.obj) (Type (max (u + 1) v))) (Z : Over Y) :
    Function.Surjective ((properBaseChangeCounit.{u, w, v} S f F).hom.app (op Z)) := by
  classical
  intro c
  let Rs : Sieve Z :=
    { arrows := fun T k => ∃ a : (properBaseChangeUnitSheaf.{u, w, v} S f F).obj.obj (op T),
        (properBaseChangeCounit.{u, w, v} S f F).hom.app (op T) a =
          (properBaseChangeSheaf.{u, w, v} S f F).obj.map k.op c
      downward_closed := by
        intro T T' k hk k'
        obtain ⟨a, ha⟩ := hk
        refine ⟨(properBaseChangeUnitSheaf.{u, w, v} S f F).obj.map k'.op a, ?_⟩
        rw [properBaseChangeCounit_naturality_apply, ha, presheaf_map_op_comp_apply] }
  have hloc : ∀ z : Z.left.obj, ∃ V : Opens Z.left.obj, z ∈ V ∧
      Rs.arrows (opensOverι S Z V) := fun z =>
    let ⟨V, hzV, a, ha⟩ := exists_opens_counit_app_eq.{u, w, v} S f hp F c z
    ⟨V, hzV, a, ha⟩
  choose V hzV hVR using hloc
  have hR : Rs ∈ (S.zariskiTopology.over Y) Z :=
    mem_zariskiTopology_over_of_opens_cover S V (fun x => ⟨x, hzV x⟩) Rs hVR
  have hsheaf := (isSheaf_iff_isSheaf_of_type _ _).1
    (properBaseChangeUnitSheaf.{u, w, v} S f F).property _ hR
  let fam : Presieve.FamilyOfElements
      (properBaseChangeUnitSheaf.{u, w, v} S f F).obj Rs.arrows := fun _ _ hk => hk.choose
  have hfam : ∀ {T : Over Y} (k : T ⟶ Z) (hk : Rs.arrows k),
      (properBaseChangeCounit.{u, w, v} S f F).hom.app (op T) (fam k hk) =
        (properBaseChangeSheaf.{u, w, v} S f F).obj.map k.op c :=
    fun _ hk => hk.choose_spec
  have hcompat : fam.Compatible := by
    intro T₁ T₂ T g₁ g₂ k₁ k₂ h₁ h₂ hcomm
    refine injective_properBaseChangeCounit_app S f hp.isClosedMap F T ?_
    rw [properBaseChangeCounit_naturality_apply, properBaseChangeCounit_naturality_apply,
      hfam k₁ h₁, hfam k₂ h₂, presheaf_map_op_comp_apply, presheaf_map_op_comp_apply, hcomm]
  refine ⟨hsheaf.amalgamate fam hcompat, ?_⟩
  refine ((isSheaf_iff_isSheaf_of_type _ _).1
    (properBaseChangeSheaf.{u, w, v} S f F).property _ hR).isSeparatedFor.ext
      (fun T k hk => ?_)
  rw [← properBaseChangeCounit_naturality_apply, hsheaf.valid_glue hcompat k hk, hfam k hk]

/-- **Proper base change for the Zariski comparison, on sheaves of sets.** For a proper `g` the
counit of the `Y`-side comparison adjunction is invertible at `f_{Zar,*}π_X^{-1}F`: it is
objectwise injective by `injective_properBaseChangeCounit_app` and objectwise surjective by
`surjective_properBaseChangeCounit_app`, and `sheafToPresheaf` reflects isomorphisms. -/
theorem isIso_properBaseChangeCounit
    (hp : _root_.IsProperMap
      (((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).map f) : X.obj → Y.obj))
    (F : Sheaf (Opens.grothendieckTopology X.obj) (Type (max (u + 1) v))) :
    IsIso (properBaseChangeCounit.{u, w, v} S f F) := by
  rw [← isIso_iff_of_reflects_iso _
      (sheafToPresheaf (S.zariskiTopology.over Y) (Type (max (u + 1) v))),
    NatTrans.isIso_iff_isIso_app]
  intro Z
  rw [isIso_iff_bijective]
  exact ⟨injective_properBaseChangeCounit_app S f hp.isClosedMap F Z.unop,
    surjective_properBaseChangeCounit_app.{u, w, v} S f hp F Z.unop⟩

/-- **Stacks 0DCU, clause (7a): the proper direct image clause.** For a proper morphism `f` of
the locally quasi-compact Zariski site, ordinary direct image of sheaves of sets along the
underlying continuous map commutes with inverse image along the comparison morphisms to the
Zariski slice topoi:

`π_Y^{-1} ∘ f_* ≅ f_{Zar,*} ∘ π_X^{-1}`.

Properness is the only hypothesis. This is `properDirectImageComparisonIso`, whose hypothesis
on the `Y`-side counit is discharged by `isIso_properBaseChangeCounit`, which is proper base
change for sheaves of sets, Stacks 0D90, in the form the Zariski comparison needs. -/
@[stacks 0DCU "proper_direct_image"]
def properDirectImageComparisonIsoOfProperMap
    (hf : StacksDraft.Topology.IsProperMap.{u, u, u}
      (((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).map f) : X.obj → Y.obj)) :
    TopCat.Sheaf.pushforward (Type (max (u + 1) v))
        ((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).map f) ⋙
      S.comparisonInverseImage.{u, w, max (u + 1) v} Y ≅
    S.comparisonInverseImage.{u, w, max (u + 1) v} X ⋙
      (zariskiSliceMorphism.{u, w, max (u + 1) v} S f).pushforward :=
  properDirectImageComparisonIso.{u, w, max (u + 1) v} S f
    (fun F => isIso_properBaseChangeCounit.{u, w, v} S f (isProperMap_site S f hf) F)

end Stacks.Topology.LocallyQuasiCompactZariskiSituation

end
