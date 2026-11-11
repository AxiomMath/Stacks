module

public import Mathlib.CategoryTheory.ConcreteCategory.ReflectsIso
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.Topology.Sheaves.Stalks
public import StacksFrontier.Topology.Sheaves.AlgebraicStructure.Defs
public import StacksFrontier.Topology.Sheaves.ClosedImmersion.Pushforward

/-!
# Pushforward along the inclusion of a closed subset (Stacks 00AH)

Let `X` be a topological space, `Z ⊆ X` a closed subset and `i : Z → X` the
inclusion. Let `(C, F)` be a *type of algebraic structure* in the sense of
Stacks 007L: a category `C` together with a faithful functor `F : C ⥤ Type`
that preserves limits and filtered colimits and reflects isomorphisms. Assume
moreover that `(C, F)` has a *final object* `0`: a terminal object of `C` whose
image `F 0` is a singleton. Then the pushforward

  `i_* : Sh(Z, C) ⥤ Sh(X, C)`

is fully faithful, and a sheaf `G ∈ Sh(X, C)` lies in its essential image
exactly when `G_x ≅ 0` for every `x ∈ X \ Z`.

## The shared 007L vocabulary

`AlgebraicStructureType` and its companion `AlgebraicStructureType.WithFinal`
are the project's single encoding of Stacks 007L;
`StacksFrontier/Topology/Sheaves/OpenImmersion/ExtensionByInitialAlgStruct.lean`
states the open-inclusion counterpart of this lemma over the same structure. The
bundle carries `F.ReflectsIsomorphisms`, which is 007L's requirement that a
morphism `a → b` be an isomorphism as soon as `F a → F b` is bijective.

## Modelling choices

* Sheaves valued in `C` on `X : TopCat` are `TopCat.Sheaf C X`, with underlying
  presheaf `(Opens X)ᵒᵖ ⥤ C`; the stalk of `G` at `y` is
  `TopCat.Presheaf.stalk G.obj y` and the pushforward along `f : Y ⟶ X` is
  `TopCat.Sheaf.pushforward C f`, acting by `(f_* G)(U) = G(f⁻¹ U)`.
* Stacks 007L asks only for filtered colimits in `C`, and that is all the main
  statements use: the stalk `G_x` is written as the filtered colimit
  `colimit ((OpenNhds.inclusion x).op ⋙ G.obj)`, which is the definition of Mathlib's
  `TopCat.Presheaf.stalk` without that API's `HasColimits C` requirement.
* The objects of `C` live in a universe `w` independent of the universe `u` of `X` (the
  homs of `C` live in `u`), so that `CommRingCat.{u}`, `Ab.{u}`, … on `X : TopCat.{u}`
  are covered. The older statements `full_and_faithful_pushforward_subsetInclusion` and
  `essImage_pushforward_subsetInclusion_iff` take `AlgebraicStructureType.{u, u}` with
  `HasColimits C`; such a `C` is small and complete, hence thin, so they only cover a
  degenerate case and are kept as corollaries.
* "Fully faithful" is the conjunction of `Functor.Full` and `Functor.Faithful`,
  and the essential image is `Functor.essImage`.
* Full faithfulness (`full_and_faithful_sheafPushforward_subsetInclusion`) needs no
  hypothesis on `Z` at all — it holds for an arbitrary subset, because the only
  input is that `Opens.map i` is surjective on opens and cover-dense. Closedness
  of `Z` is used only for the essential-image description, where it makes `Zᶜ`
  open and hence a neighbourhood of every point outside `Z`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace TopCat
universe u v w

/-- A type of algebraic structure `(C, F)` *has a final object `0`* if `C` has a
terminal object whose image under `F` is a singleton. No assumption is made that
`0` is initial.

Declared outside `namespace Stacks` on purpose: the name has to be
`AlgebraicStructureType.WithFinal` for dot notation `S.WithFinal` to resolve against
`S : AlgebraicStructureType`, and inside the namespace it would be
`Stacks.AlgebraicStructureType.WithFinal`. -/
structure AlgebraicStructureType.WithFinal (S : AlgebraicStructureType) where
  /-- The chosen terminal/final object of `C`. -/
  zero : S.C
  /-- Witness that `zero` is terminal in `C`. -/
  isTerminal : IsTerminal zero
  /-- Witness that `F.obj zero` is a singleton (has a unique element). -/
  fZeroUnique : Unique (S.F.obj zero)

namespace Stacks


/-! ### Cover-density of the inclusion on opens -/

private lemma opensMap_surjective (X : TopCat.{u}) (Z : Set X) :
    Function.Surjective (Opens.map (subsetInclusion X Z)).obj := by
  intro V
  obtain ⟨U, hU, hVU⟩ := isOpen_induced_iff.mp V.2
  exact ⟨⟨U, hU⟩, Opens.ext hVU⟩

private instance instIsCoverDense (X : TopCat.{u}) (Z : Set X) :
    (Opens.map (subsetInclusion X Z)).IsCoverDense
      (Opens.grothendieckTopology ↑(TopCat.of Z)) := by
  constructor
  intro V x hx
  obtain ⟨W, hW⟩ := opensMap_surjective X Z V
  refine ⟨V, 𝟙 V, ?_, hx⟩
  change Presieve.coverByImage (Opens.map (subsetInclusion X Z)) V (𝟙 V)
  exact ⟨⟨W, eqToHom hW.symm, eqToHom hW, by simp⟩⟩

private instance instIsLocallyFull (X : TopCat.{u}) (Z : Set X) :
    (Opens.map (subsetInclusion X Z)).IsLocallyFull
      (Opens.grothendieckTopology ↑(TopCat.of Z)) := by
  constructor
  intro U V f x hx
  let G := Opens.map (subsetInclusion X Z)
  refine ⟨G.obj (U ⊓ V), G.map (homOfLE inf_le_left), ?_, ⟨hx, leOfHom f hx⟩⟩
  change
    ∃ (Z' : _) (g : Z' ⟶ U) (_ : G.obj (U ⊓ V) ⟶ G.obj Z'),
      (G.imageSieve f).arrows g ∧ G.map (homOfLE inf_le_left) = _ ≫ G.map g
  exact ⟨U ⊓ V, homOfLE inf_le_left, 𝟙 _, ⟨homOfLE inf_le_right, Subsingleton.elim _ _⟩,
    by simp⟩

private instance instIsLocallyFaithful (X : TopCat.{u}) (Z : Set X) :
    (Opens.map (subsetInclusion X Z)).IsLocallyFaithful
      (Opens.grothendieckTopology ↑(TopCat.of Z)) := by
  constructor
  intro U V f₁ f₂ _
  obtain rfl : f₁ = f₂ := Subsingleton.elim _ _
  have htop : Sieve.equalizer f₁ f₁ = ⊤ := by
    ext W g
    simp [Sieve.equalizer]
  rw [htop, Sieve.functorPushforward_top]
  exact (Opens.grothendieckTopology _).top_mem _

private lemma coverPreserving_opensMap_subsetInclusion (X : TopCat.{u}) (Z : Set X) :
    CoverPreserving (Opens.grothendieckTopology ↑X) (Opens.grothendieckTopology ↑(TopCat.of Z))
      (Opens.map (subsetInclusion X Z)) := by
  constructor
  intro U S hS x hx
  obtain ⟨V, f, hf, hxV⟩ := hS x.val hx
  refine
    ⟨(Opens.map (subsetInclusion X Z)).obj V, (Opens.map (subsetInclusion X Z)).map f, ?_,
      (hxV : x.val ∈ V)⟩
  change
    ∃ (Z' : _) (g : Z' ⟶ U) (_ :
      (Opens.map (subsetInclusion X Z)).obj V ⟶ (Opens.map (subsetInclusion X Z)).obj Z'),
      S.arrows g ∧
        (Opens.map (subsetInclusion X Z)).map f = _ ≫ (Opens.map (subsetInclusion X Z)).map g
  exact ⟨V, f, 𝟙 _, hf, by simp⟩

private instance instIsContinuous (X : TopCat.{u}) (Z : Set X) :
    (Opens.map (subsetInclusion X Z)).IsContinuous (Opens.grothendieckTopology ↑X)
      (Opens.grothendieckTopology ↑(TopCat.of Z)) :=
  Functor.IsCoverDense.isContinuous _ _ _ (coverPreserving_opensMap_subsetInclusion X Z)

/-- **Stacks 00AH, part 1, in its general form.** For `X : TopCat.{u}`, any subset
`Z ⊆ X` with inclusion `i : Z ↪ X`, and any type of algebraic structure `(C, F)`
whose objects live in an arbitrary universe `w` (so that `CommRingCat.{u}`, `Ab.{u}`,
… are instances), the pushforward functor `i_* : Sh(Z, C) ⥤ Sh(X, C)` is full and
faithful. The proof only uses that `Opens.map i` is surjective on opens, so `Z` may
be an arbitrary subset (Stacks takes `Z` closed); closedness is needed only for
`essImage_sheafPushforward_subsetInclusion_iff`. -/
@[stacks 00AH "fully faithful part; holds for any subset `Z`"]
theorem full_and_faithful_sheafPushforward_subsetInclusion (X : TopCat.{u}) (Z : Set X)
    (S : AlgebraicStructureType.{u, w}) :
    (TopCat.Sheaf.pushforward S.C (subsetInclusion X Z)).Full ∧
      (TopCat.Sheaf.pushforward S.C (subsetInclusion X Z)).Faithful :=
  ⟨Functor.IsCoverDense.full_sheafPushforwardContinuous _ _ _,
    Functor.IsCoverDense.faithful_sheafPushforwardContinuous _ _ _⟩

/-- The special case of `full_and_faithful_sheafPushforward_subsetInclusion` for an
`AlgebraicStructureType.{u, u}` with all colimits. Objects and homs of `C` both live in
`Type u` here, so by Freyd's theorem `C` is thin; the statement therefore covers only a
degenerate case, and cannot be applied to `CommRingCat` or `Ab`. Stacks 00AH itself is
`full_and_faithful_sheafPushforward_subsetInclusion`. -/
theorem full_and_faithful_pushforward_subsetInclusion (X : TopCat.{u}) (Z : Set X)
    (S : AlgebraicStructureType.{u, u}) [HasColimits S.C] :
    (TopCat.Sheaf.pushforward S.C (subsetInclusion X Z)).Full ∧
      (TopCat.Sheaf.pushforward S.C (subsetInclusion X Z)).Faithful :=
  ⟨Functor.IsCoverDense.full_sheafPushforwardContinuous _ _ _,
    Functor.IsCoverDense.faithful_sheafPushforwardContinuous _ _ _⟩

/-- The stalk of `i_* F` at a point outside the closed subset `Z` is terminal.
Since `Z` is closed, `Zᶜ` is an open neighbourhood of `x`, and every open
`U ⊆ Zᶜ` has `i⁻¹ U = ⊥`, so `(i_* F)(U) = F(⊥)` is terminal by the sheaf
condition on the empty cover. Such `U` are cofinal among the open neighbourhoods
of `x`, so the filtered colimit computing the stalk is terminal too. -/
private noncomputable def isTerminalStalkPushforwardOfNotMem (X : TopCat.{u}) (Z : Set X)
    (hZ : IsClosed Z) (S : AlgebraicStructureType.{u, w})
    (F : TopCat.Sheaf S.C (TopCat.of Z)) (x : ↑X) (hx : x ∉ Z) :
    IsTerminal
      (colimit ((OpenNhds.inclusion x).op ⋙
        ((Sheaf.pushforward S.C (subsetInclusion X Z)).obj F).obj)) := by
  set P := ((Sheaf.pushforward S.C (subsetInclusion X Z)).obj F).obj
  set D := (OpenNhds.inclusion x).op ⋙ P with hD_def
  have hZc_open : IsOpen (Zᶜ : Set X) := hZ.isOpen_compl
  set U₀ : Opens X := ⟨Zᶜ, hZc_open⟩
  have hxU₀ : x ∈ U₀ := hx
  have hpreimage_sub_bot :
    ∀ (V : Opens X), (V : Set X) ⊆ Zᶜ → (Opens.map (subsetInclusion X Z)).obj V = ⊥ :=
    fun V hV => le_bot_iff.mp fun ⟨_, hz⟩ hmem => absurd hz (hV hmem)
  have hFbot_terminal : IsTerminal (F.obj.obj (Opposite.op ⊥)) := Sheaf.isTerminalOfEqEmpty F rfl
  have hPU₀_terminal : IsTerminal (D.obj (Opposite.op ⟨U₀, hxU₀⟩)) := by
    simp only [D, P, Functor.comp_obj, Functor.op_obj, OpenNhds.inclusion_obj,
      TopCat.Sheaf.pushforward_obj_val, TopCat.Presheaf.pushforward_obj_obj]
    rw [hpreimage_sub_bot U₀ (le_refl _)]
    exact hFbot_terminal
  have hD_sub_terminal :
    ∀ (V : OpenNhds x), (V.1 : Set X) ⊆ Zᶜ → IsTerminal (D.obj (Opposite.op V)) := by
    intro V hV
    simp only [D, P, Functor.comp_obj, Functor.op_obj, TopCat.Sheaf.pushforward_obj_val,
      TopCat.Presheaf.pushforward_obj_obj]
    rw [hpreimage_sub_bot ((OpenNhds.inclusion x).obj V) hV]
    exact hFbot_terminal
  have hD_inf_terminal :
    ∀ (V : OpenNhds x), IsTerminal (D.obj (Opposite.op ⟨V.1 ⊓ U₀, ⟨V.2, hxU₀⟩⟩)) :=
    fun V => hD_sub_terminal ⟨V.1 ⊓ U₀, ⟨V.2, hxU₀⟩⟩ inf_le_right
  apply IsTerminal.ofIso hPU₀_terminal
  symm
  let term_cocone : Cocone D :=
    Cocone.mk (D.obj (Opposite.op ⟨U₀, hxU₀⟩))
      { app := fun j => hPU₀_terminal.from _
        naturality := fun _ _ _ => hPU₀_terminal.hom_ext _ _ }
  refine ⟨colimit.desc D term_cocone, colimit.ι D (Opposite.op ⟨U₀, hxU₀⟩), ?_,
    hPU₀_terminal.hom_ext _ _⟩
  apply colimit.hom_ext
  intro j
  change
    colimit.ι D j ≫ (colimit.desc D term_cocone ≫ colimit.ι D (Opposite.op ⟨U₀, hxU₀⟩)) =
      colimit.ι D j ≫ 𝟙 _
  rw [Category.comp_id]
  conv_lhs => rw [← Category.assoc, colimit.ι_desc]
  let V : OpenNhds x := ⟨j.unop.1 ⊓ U₀, ⟨j.unop.2, hxU₀⟩⟩
  have hι_j_factor :
    colimit.ι D j =
      D.map (Quiver.Hom.op (homOfLE (show V.1 ≤ j.unop.1 from inf_le_left))) ≫
        colimit.ι D (Opposite.op V) :=
    (colimit.w D _).symm
  have hι_U₀_factor :
    colimit.ι D (Opposite.op ⟨U₀, hxU₀⟩) =
      D.map (Quiver.Hom.op (homOfLE (show V.1 ≤ U₀ from inf_le_right))) ≫
        colimit.ι D (Opposite.op V) :=
    (colimit.w D _).symm
  rw [hι_U₀_factor, ← Category.assoc, hι_j_factor]
  exact congrArg (· ≫ _) ((hD_inf_terminal j.unop).hom_ext _ _)

/-- If every stalk of `G` at a point of an open `W` is isomorphic to the final
object, then `G(W)` is terminal. The argument transports the question to the
sheaf of sets `G ⋙ F` — legitimate because `F` reflects isomorphisms, hence
terminal objects — where it is the unique-gluing characterisation of a sheaf all
of whose stalks are singletons. -/
private noncomputable def isTerminalSectionsOfIsTerminalStalks (X : TopCat.{u})
    (S : AlgebraicStructureType.{u, w}) (Sfinal : S.WithFinal)
    (G : TopCat.Sheaf S.C X) (W : Opens X)
    (hW : ∀ x : X, x ∈ W →
      Nonempty (colimit ((OpenNhds.inclusion x).op ⋙ G.obj) ≅ Sfinal.zero)) :
    IsTerminal (G.obj.obj (Opposite.op W)) := by
  haveI : ReflectsLimit (Functor.empty S.C) S.F := reflectsLimit_of_reflectsIsomorphisms _ _
  refine IsTerminal.isTerminalOfObj S.F _ ?_
  have hH : Presheaf.IsSheaf (Opens.grothendieckTopology X) (G.obj ⋙ S.F) :=
    Presheaf.isSheaf_comp_of_isSheaf _ _ _ G.property
  set H := G.obj ⋙ S.F
  have hStalk (x : X) (hxW : x ∈ W) : Unique (Presheaf.stalk H x) :=
    @Equiv.unique _ _ Sfinal.fZeroUnique
      ((preservesColimitIso S.F ((OpenNhds.inclusion x).op ⋙ G.obj)).symm ≪≫
        S.F.mapIso (Classical.choice (hW x hxW))).toEquiv
  refine (Types.isTerminalEquivUnique _).invFun ?_
  have hSub : ∀ V : Opens X, V ≤ W → Subsingleton (H.obj (Opposite.op V)) := fun V hV =>
    ⟨fun a b => Presheaf.section_ext ⟨H, hH⟩ V a b fun x hx =>
      @Subsingleton.elim _ (hStalk x (hV hx)).instSubsingleton _ _⟩
  have hNe : Nonempty (H.obj (Opposite.op W)) := by
    have hLocal :
      ∀ p : W, ∃ (V : Opens X) (_ : (p : X) ∈ V) (_ : V ≤ W), Nonempty (H.obj (Opposite.op V)) := by
      intro ⟨x, hxW⟩
      obtain ⟨⟨V, hxV⟩, s, _⟩ :=
        Types.jointly_surjective_of_isColimit (colimit.isColimit ((OpenNhds.inclusion x).op ⋙ H))
          (hStalk x hxW).default
      exact ⟨V ⊓ W, ⟨hxV, hxW⟩, inf_le_right, ⟨H.map (homOfLE inf_le_left).op s⟩⟩
    choose V hxV hVW hNe' using hLocal
    have sf : ∀ p : W, H.obj (Opposite.op (V p)) := fun p => (hNe' p).some
    obtain ⟨s, _, _⟩ := (Presheaf.isSheaf_iff_isSheafUniqueGluing_types H).mp hH V sf
      fun i j => (hSub _ (inf_le_left.trans (hVW i))).elim _ _
    have hSupV : iSup V = W :=
      le_antisymm (iSup_le hVW) fun x hxW => le_iSup V ⟨x, hxW⟩ (hxV ⟨x, hxW⟩)
    rw [← hSupV]
    exact ⟨s⟩
  exact @Unique.mk _ (Classical.choice (hNe.map Inhabited.mk)) fun _ => (hSub W le_rfl).elim _ _

/-- The restriction `G(U ⊔ W) → G(U)` is an isomorphism as soon as `G(W)` and
`G(U ⊓ W)` are terminal: the sheaf square for the cover `{U, W}` of `U ⊔ W` is a
pullback, and a pullback of `𝟙` along a map of terminal objects is an
isomorphism. Applied with `W = Zᶜ`. -/
private theorem isIsoResOfIsTerminal (X : TopCat.{u}) (S : AlgebraicStructureType.{u, w})
    (G : TopCat.Sheaf S.C X) (U : Opens X) (W : Opens X)
    (hW_term : IsTerminal (G.obj.obj (Opposite.op W)))
    (hUW_term : IsTerminal (G.obj.obj (Opposite.op (U ⊓ W)))) :
    IsIso (G.obj.map (homOfLE (le_sup_left : U ≤ U ⊔ W)).op) := by
  have hpb : IsLimit (G.interUnionPullbackCone U W) := G.isLimitPullbackCone U W
  let cone :
    PullbackCone (G.obj.map (homOfLE inf_le_left : (U ⊓ W) ⟶ U).op)
      (G.obj.map (homOfLE inf_le_right : (U ⊓ W) ⟶ W).op) :=
    PullbackCone.mk (𝟙 _) (hW_term.from _) (hUW_term.hom_ext _ _)
  let lift := hpb.lift cone
  have h1 : lift ≫ (G.interUnionPullbackCone U W).fst = 𝟙 _ := hpb.fac cone WalkingCospan.left
  suffices h2 : (G.interUnionPullbackCone U W).fst ≫ lift = 𝟙 _ from ⟨⟨lift, h2, h1⟩⟩
  have hfst_lift_eq :
      (G.interUnionPullbackCone U W).fst ≫ lift = hpb.lift (G.interUnionPullbackCone U W) :=
    hpb.uniq (G.interUnionPullbackCone U W) ((G.interUnionPullbackCone U W).fst ≫ lift)
      fun j => by
        match j with
        | WalkingCospan.left =>
          exact
            (Category.assoc _ _ _).trans
              (((G.interUnionPullbackCone U W).fst ≫= h1).trans (Category.comp_id _))
        | WalkingCospan.right => exact hW_term.hom_ext _ _
        | WalkingCospan.one => exact hUW_term.hom_ext _ _
  rw [hfst_lift_eq, hpb.lift_self]

/-- The hard direction of the essential-image description: from the vanishing of
the stalks of `G` outside `Z` we build a sheaf `F` on `Z` with `i_* F ≅ G`. The
sheaf is `F(V) = G(W ⊔ Zᶜ)` for any open `W ⊆ X` with `i⁻¹ W = V`; this is
well defined because `W ⊔ Zᶜ` does not depend on the choice of `W`, and it is a
sheaf because `V ↦ W ⊔ Zᶜ` preserves meets and nonempty sups and sends `⊥` to
`Zᶜ`, where `G` has terminal sections. -/
private lemma essImage_of_stalks_vanish (X : TopCat.{u}) (Z : Set X) (hZ : IsClosed Z)
    (S : AlgebraicStructureType.{u, w}) (Sfinal : S.WithFinal)
    (G : TopCat.Sheaf S.C X)
    (hstalk : ∀ x : X, x ∉ Z →
      Nonempty (colimit ((OpenNhds.inclusion x).op ⋙ G.obj) ≅ Sfinal.zero)) :
    (TopCat.Sheaf.pushforward S.C (subsetInclusion X Z)).essImage G := by
  set i := subsetInclusion X Z
  set Gi := Opens.map i
  have hZc_open : IsOpen (Zᶜ : Set X) := hZ.isOpen_compl
  set Zc : Opens X := ⟨Zᶜ, hZc_open⟩
  -- G(W) is terminal for any open W ⊆ Zᶜ
  have hGterm : ∀ (W : Opens X), (W : Set X) ⊆ Zᶜ → IsTerminal (G.obj.obj (Opposite.op W)) :=
    fun W hW => isTerminalSectionsOfIsTerminalStalks X S Sfinal G W (fun x hx => hstalk x (hW hx))
  -- The restriction G(U ⊔ Zc) → G(U) is an iso for all U
  have hRestrIso : ∀ U : Opens X, IsIso (G.obj.map (homOfLE (le_sup_left : U ≤ U ⊔ Zc)).op) :=
    fun U => isIsoResOfIsTerminal X S G U Zc (hGterm Zc (le_refl _)) (hGterm (U ⊓ Zc) inf_le_right)
  have hsurj := opensMap_surjective X Z
  -- Key lemma: `W₁ ⊔ Zc` only depends on `Gi.obj W₁`, monotonically
  have sup_Zc_le_of_opensMap_le :
    ∀ (W₁ W₂ : Opens X), Gi.obj W₁ ≤ Gi.obj W₂ → W₁ ⊔ Zc ≤ W₂ ⊔ Zc := by
    intro W₁ W₂ hle x hx
    rcases hx with hx1 | hx2
    · by_cases hxZ : x ∈ Z
      · left
        exact hle (show (⟨x, hxZ⟩ : Z) ∈ (Gi.obj W₁ : Set (TopCat.of Z)) from hx1)
      · right; exact hxZ
    · right; exact hx2
  -- Define s on objects: s(V) = (choose preimage of V) ⊔ Zc
  let sObj : Opens (TopCat.of Z) → Opens X := fun V => (Classical.choose (hsurj V)) ⊔ Zc
  -- sObj V = W ⊔ Zc for any W with Gi.obj W = V
  have hsObj_eq : ∀ (V : Opens (TopCat.of Z)) (W : Opens X), Gi.obj W = V → sObj V = W ⊔ Zc := by
    intro V W hW
    have hchoose := Classical.choose_spec (hsurj V)
    exact le_antisymm (sup_Zc_le_of_opensMap_le _ _ (hchoose.trans hW.symm).le)
      (sup_Zc_le_of_opensMap_le _ _ (hchoose.trans hW.symm).ge)
  -- Gi.obj (sObj V) = V
  have hsObj_section : ∀ V : Opens (TopCat.of Z), Gi.obj (sObj V) = V := by
    intro V
    have hchoose := Classical.choose_spec (hsurj V)
    ext ⟨x, hxZ⟩
    constructor
    · intro hx
      rcases hx with hx1 | hx2
      · have : (⟨x, hxZ⟩ : Z) ∈ (Gi.obj (Classical.choose (hsurj V)) : Set (TopCat.of Z)) := hx1
        rw [hchoose] at this; exact this
      · exact absurd hxZ hx2
    · intro hx
      left
      have : (⟨x, hxZ⟩ : Z) ∈ (V : Set (TopCat.of Z)) := hx
      rw [← hchoose] at this; exact this
  -- sObj is monotone
  have hsObj_mono : ∀ (V₁ V₂ : Opens (TopCat.of Z)), V₁ ≤ V₂ → sObj V₁ ≤ sObj V₂ := by
    intro V₁ V₂ hle
    refine sup_Zc_le_of_opensMap_le _ _ ?_
    rw [Classical.choose_spec (hsurj V₁), Classical.choose_spec (hsurj V₂)]
    exact hle
  -- Build s as a functor
  let s : Opens (TopCat.of Z) ⥤ Opens X :=
    { obj := sObj
      map := fun {V₁ V₂} f => homOfLE (hsObj_mono V₁ V₂ (leOfHom f))
      map_id := fun _ => rfl
      map_comp := fun _ _ => rfl }
  -- s.obj (Gi.obj U) = U ⊔ Zc for all U
  have hs_left : ∀ U : Opens X, s.obj (Gi.obj U) = U ⊔ Zc := fun U => hsObj_eq (Gi.obj U) U rfl
  -- membership of a point of `Z` in `s.obj V` is membership in `V`
  have hs_mem : ∀ (V : Opens (TopCat.of Z)) (x : X) (hxZ : x ∈ Z),
      x ∈ s.obj V ↔ (⟨x, hxZ⟩ : Z) ∈ V := fun V x hxZ =>
    SetLike.ext_iff.mp (hsObj_section V) ⟨x, hxZ⟩
  -- Define F as the presheaf s.op ⋙ G.val on Z
  let Fpre : (Opens (TopCat.of Z))ᵒᵖ ⥤ S.C := s.op ⋙ G.obj
  -- `Fpre` is a sheaf
  have hFsheaf : Presheaf.IsSheaf (Opens.grothendieckTopology (TopCat.of Z)) Fpre := by
    -- Step 1: Reduce to Type-valued sheaves via isSheaf_of_isSheaf_comp
    have : ReflectsLimitsOfSize.{u, u} S.F := reflectsLimits_of_reflectsIsomorphisms
    apply Presheaf.isSheaf_of_isSheaf_comp (s := S.F)
    -- Step 2: Use unique gluing characterization for Type-valued sheaves
    set H : (Opens X)ᵒᵖ ⥤ Type u := G.obj ⋙ S.F
    have hH_sheaf : Presheaf.IsSheaf (Opens.grothendieckTopology X) H :=
      Presheaf.isSheaf_comp_of_isSheaf _ _ _ G.property
    have hH_UG := (Presheaf.isSheaf_iff_isSheafUniqueGluing_types H).mp hH_sheaf
    apply (Presheaf.isSheaf_iff_isSheafUniqueGluing_types (X := TopCat.of Z) (s.op ⋙ H)).mpr
    -- Step 3: Prove unique gluing for s.op ⋙ H
    -- Key sub-facts:
    -- (a) s preserves meets: s.obj(V₁ ⊓ V₂) = s.obj V₁ ⊓ s.obj V₂
    have hsMeet : ∀ V₁ V₂ : Opens (TopCat.of Z), s.obj V₁ ⊓ s.obj V₂ = s.obj (V₁ ⊓ V₂) := by
      intro V₁ V₂; apply le_antisymm
      · intro x ⟨hx1, hx2⟩
        by_cases hxZ : x ∈ Z
        · exact (hs_mem _ x hxZ).mpr ⟨(hs_mem _ x hxZ).mp hx1, (hs_mem _ x hxZ).mp hx2⟩
        · exact (le_sup_right : Zc ≤ s.obj (V₁ ⊓ V₂)) hxZ
      · exact le_inf (s.map (homOfLE inf_le_left)).le (s.map (homOfLE inf_le_right)).le
    -- (b) s preserves sups for nonempty families
    have hsSupNonempty :
      ∀ {ι : Type u} [Nonempty ι] (U : ι → Opens (TopCat.of Z)),
        s.obj (iSup U) = iSup (s.obj ∘ U) := by
      intro ι _ U; apply le_antisymm
      · intro x hx
        by_cases hxZ : x ∈ Z
        · obtain ⟨i, hi⟩ := Opens.mem_iSup.mp ((hs_mem _ x hxZ).mp hx)
          exact le_iSup (s.obj ∘ U) i ((hs_mem _ x hxZ).mpr hi)
        · exact
            le_iSup (s.obj ∘ U) (Classical.arbitrary ι)
              ((le_sup_right : Zc ≤ s.obj (U (Classical.arbitrary ι))) hxZ)
      · exact iSup_le (fun i => hsObj_mono (U i) (iSup U) (le_iSup U i))
    -- (c) s.obj ⊥ = Zc (hence H(op(s.obj ⊥)) is a singleton)
    have hsBot : s.obj ⊥ = Zc := by
      apply le_antisymm
      · intro x hx
        by_cases hxZ : x ∈ Z
        · exact ((hs_mem _ x hxZ).mp hx).elim
        · exact (show x ∈ (Zc : Set X) from hxZ)
      · exact (le_sup_right : Zc ≤ s.obj ⊥)
    -- Now prove IsSheafUniqueGluing
    intro U sf sections_sf hcompat_sf
    -- Case split on whether ι is empty or nonempty
    by_cases hne : Nonempty U
    · -- Nonempty case: use sup and meet preservation
      have hSupEq : s.obj (iSup sf) = iSup (s.obj ∘ sf) := hsSupNonempty sf
      -- The family sections_sf gives sections in H(op(s.obj(sf i))) for each i
      -- These are compatible w.r.t. the H-sheaf condition on X
      -- because s preserves meets
      have hcompat_X : Presheaf.IsCompatible H (s.obj ∘ sf) sections_sf := by
        intro i j
        have hcij := hcompat_sf i j
        have hmeq := hsMeet (sf i) (sf j)
        have hleft :
          (Opens.infLELeft (s.obj (sf i)) (s.obj (sf j))) =
            (eqToHom hmeq ≫ s.map (Opens.infLELeft (sf i) (sf j))) :=
          Subsingleton.elim _ _
        have hright :
          (Opens.infLERight (s.obj (sf i)) (s.obj (sf j))) =
            (eqToHom hmeq ≫ s.map (Opens.infLERight (sf i) (sf j))) :=
          Subsingleton.elim _ _
        simp only [Function.comp, hleft, hright, op_comp, Functor.map_comp, eqToHom_op,
          eqToHom_map]
        exact congrArg _ hcij
      -- Apply hH_UG to get the unique section on ⨆ s.obj(sf i) = s.obj(iSup sf)
      obtain ⟨t, ht_glue, ht_unique⟩ := hH_UG (s.obj ∘ sf) sections_sf hcompat_X
      -- Transport t to a section on s.obj(iSup sf) using hSupEq
      let t' : (s.op ⋙ H).obj (Opposite.op (iSup sf)) := H.map (eqToHom hSupEq).op t
      refine ⟨t', fun i => ?_, fun t'' ht''_glue => ?_⟩
      · -- Gluing condition for t'
        have heq_op :
          (eqToHom hSupEq).op ≫ (s.map (Opens.leSupr sf i)).op =
            (Opens.leSupr (s.obj ∘ sf) i).op := by
          apply Quiver.Hom.unop_inj; exact Subsingleton.elim _ _
        simp only [t', Functor.comp_map, Functor.op_map, Quiver.Hom.unop_op]
        simp only [←
            types_comp_apply (H.map (eqToHom hSupEq).op) (H.map (s.map (Opens.leSupr sf i)).op),
          ← H.map_comp, heq_op]
        exact ht_glue i
      · -- Uniqueness for t'
        have ht''_X :
          Presheaf.IsGluing H (s.obj ∘ sf) sections_sf (H.map (eqToHom hSupEq.symm).op t'') := by
          intro i
          have heq_op :
            (eqToHom hSupEq.symm).op ≫ (Opens.leSupr (s.obj ∘ sf) i).op =
              (s.map (Opens.leSupr sf i)).op := by
            apply Quiver.Hom.unop_inj; exact Subsingleton.elim _ _
          simp only [←
              types_comp_apply (H.map (eqToHom hSupEq.symm).op)
                (H.map (Opens.leSupr (s.obj ∘ sf) i).op),
            ← H.map_comp, heq_op]
          exact ht''_glue i
        have heq := ht_unique (H.map (eqToHom hSupEq.symm).op t'') ht''_X
        -- heq : H.map (eqToHom hSupEq.symm).op t'' = t
        -- Goal: t'' = t' = H.map (eqToHom hSupEq).op t
        symm; dsimp only [t']
        rw [← heq]
        -- Goal: H.map (eqToHom hSupEq).op (H.map (eqToHom hSupEq.symm).op t'') = t''
        -- This is H.map (comp) t'' where comp = (eqToHom .symm).op ≫ (eqToHom).op = id
        have hid :
          (eqToHom hSupEq.symm).op ≫ (eqToHom hSupEq).op = 𝟙 (Opposite.op (s.obj (iSup sf))) := by
          simp [eqToHom_op, eqToHom_trans]
        simp only [← types_comp_apply (H.map (eqToHom hSupEq.symm).op) (H.map (eqToHom hSupEq).op),
          ← H.map_comp, hid, H.map_id]
        rfl
    · -- Empty case: ι is empty, iSup sf = ⊥
      have : IsEmpty U := not_nonempty_iff.mp hne
      have hiSup_bot : iSup sf = ⊥ := iSup_of_empty sf
      -- s.obj ⊥ = Zc, and G(Zc) is terminal, so H(op(s.obj ⊥)) is a singleton
      have hterm : IsTerminal (G.obj.obj (Opposite.op (s.obj ⊥))) := by
        rw [hsBot]; exact hGterm Zc (le_of_eq (show (Zc : Set X) = Zᶜ from rfl))
      have hU : Unique (H.obj (Opposite.op (s.obj (iSup sf)))) := by
        rw [hiSup_bot]
        exact (Types.isTerminalEquivUnique _).toFun (hterm.isTerminalObj S.F _)
      exact ⟨hU.default, fun i => IsEmpty.elim inferInstance i, fun _ _ => Subsingleton.elim _ _⟩
  let F : TopCat.Sheaf S.C (TopCat.of Z) := ⟨Fpre, hFsheaf⟩
  -- Construct the natural iso between (i_*F).val and G.val
  -- (i_*F).val.obj (op U) = G.val.obj (op (s.obj (Gi.obj U))) = G.val.obj (op (U ⊔ Zc))
  -- Component iso at U: G(s.obj(Gi.obj U)) ≅ G(U ⊔ Zc) ≅ G(U)
  let natIso : ((Sheaf.pushforward S.C i).obj F).obj ≅ G.obj := by
    refine NatIso.ofComponents (fun U => ?_) (fun {U V} f => ?_)
    · -- Component at U
      have heq : s.obj (Gi.obj U.unop) = U.unop ⊔ Zc := hs_left U.unop
      have := hRestrIso U.unop
      exact
        (G.obj.mapIso (eqToIso heq).op).symm ≪≫
          asIso (G.obj.map (homOfLE (le_sup_left : U.unop ≤ U.unop ⊔ Zc)).op)
    · -- Naturality: follows from functoriality of G.val
      change
        G.obj.map (s.map (Gi.map f.unop)).op ≫
            G.obj.map (eqToIso _).op.inv ≫ G.obj.map (homOfLE _).op =
          (G.obj.map (eqToIso _).op.inv ≫ G.obj.map (homOfLE _).op) ≫ G.obj.map f
      simp only [Category.assoc, ← G.obj.map_comp]
      exact congr_arg G.obj.map (Subsingleton.elim _ _)
  exact ⟨F, ⟨(Sheaf.forget S.C X).preimageIso natIso⟩⟩

/-- **Stacks 00AH, part 2, in its general form.** Let `X : TopCat.{u}`, let `Z ⊆ X`
be closed with inclusion `i : Z ↪ X`, and let `(C, F)` be a type of algebraic structure
with a final object `0`, whose objects live in an arbitrary universe `w` (so that
`CommRingCat.{u}`, `Ab.{u}`, … are instances). A sheaf `G ∈ Sh(X, C)` lies in the
essential image of `i_* : Sh(Z, C) ⥤ Sh(X, C)` exactly when its stalk `G_x` at every
point `x ∉ Z` is isomorphic in `C` to `0`.

The stalk `G_x` is written as the colimit of `G` over the open neighbourhoods of `x`,
which is a filtered colimit and so exists by 007L. This is literally the definition of
Mathlib's `TopCat.Presheaf.stalk G.obj x`; that API is not used directly because it
requires `HasColimits C`, more than 007L provides. Whenever `C` has all colimits the two
are definitionally equal (see `essImage_pushforward_subsetInclusion_iff`). -/
@[stacks 00AH "essential image part"]
theorem essImage_sheafPushforward_subsetInclusion_iff (X : TopCat.{u}) (Z : Set X)
    (hZ : IsClosed Z) (S : AlgebraicStructureType.{u, w}) (Sfinal : S.WithFinal)
    (G : TopCat.Sheaf S.C X) :
    (TopCat.Sheaf.pushforward S.C (subsetInclusion X Z)).essImage G ↔
      ∀ x : X, x ∉ Z →
        Nonempty (colimit ((OpenNhds.inclusion x).op ⋙ G.obj) ≅ Sfinal.zero) := by
  refine ⟨fun ⟨F, ⟨iso⟩⟩ x hx => ?_, essImage_of_stalks_vanish X Z hZ S Sfinal G⟩
  have stalk_iso :
      colimit ((OpenNhds.inclusion x).op ⋙ G.obj) ≅
        colimit ((OpenNhds.inclusion x).op ⋙
          ((Sheaf.pushforward S.C (subsetInclusion X Z)).obj F).obj) :=
    HasColimit.isoOfNatIso
      (Functor.isoWhiskerLeft (OpenNhds.inclusion x).op ((Sheaf.forget S.C X).mapIso iso).symm)
  exact ⟨((isTerminalStalkPushforwardOfNotMem X Z hZ S F x hx).ofIso
    stalk_iso.symm).uniqueUpToIso Sfinal.isTerminal⟩

/-- The special case of `essImage_sheafPushforward_subsetInclusion_iff` for an
`AlgebraicStructureType.{u, u}` with all colimits, phrased with `TopCat.Presheaf.stalk`.
Objects and homs of `C` both live in `Type u` here, so by Freyd's theorem `C` is thin;
the statement therefore covers only a degenerate case, and cannot be applied to
`CommRingCat` or `Ab`. Stacks 00AH itself is
`essImage_sheafPushforward_subsetInclusion_iff`. -/
theorem essImage_pushforward_subsetInclusion_iff (X : TopCat.{u}) (Z : Set X) (hZ : IsClosed Z)
    (S : AlgebraicStructureType.{u, u}) [HasColimits S.C] (Sfinal : S.WithFinal)
    (G : TopCat.Sheaf S.C X) :
    (TopCat.Sheaf.pushforward S.C (subsetInclusion X Z)).essImage G ↔
      ∀ x : X, x ∉ Z → Nonempty (TopCat.Presheaf.stalk G.obj x ≅ Sfinal.zero) :=
  essImage_sheafPushforward_subsetInclusion_iff X Z hZ S Sfinal G

end Stacks
