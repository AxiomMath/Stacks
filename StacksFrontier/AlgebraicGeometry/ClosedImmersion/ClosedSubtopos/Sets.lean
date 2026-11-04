module

public import StacksFrontier.CategoryTheory.Sites.Subtopos.Closed
public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
public import Mathlib.Topology.Sheaves.Stalks

/-!
# The image of `i_*` on sheaves of sets is a closed subtopos

Let `i : Z ⟶ X` be a closed embedding of topological spaces and let `U = X \ i(Z)` be the open
complement of its image.  A sheaf of sets `G` on `X` is the direct image of a sheaf on `Z`
exactly when its sections over every open contained in `U` form a singleton.  Together with the
observation that the sheaf `V ↦ {∗ | V ⊆ U}` is a subsheaf of the final sheaf whose closed
complement in the sense of Stacks 08LY consists of precisely those `G`, this exhibits the
essential image of `i_*` as a *closed* subtopos of `Sh(X)` in the sense of Stacks 08LZ.

The substance is the second description of the essential image.  One direction is immediate:
`Γ(i_* F, V) = Γ(F, i⁻¹V) = Γ(F, ∅)`, which is a singleton for a sheaf `F`.  For the other,
the sheaf on `Z` to produce is the *naive* inverse image `W ↦ Γ(G, U(W))`, where `U(W)` is the
largest open of `X` with preimage `W` — the right adjoint of `Opens.map i` supplied by
`Topology.IsInducing.functorObj`.  Two facts drive the argument, and both come from the
singleton hypothesis through the sheaf condition on `G`:

* restricting sections of `G` along an inclusion `V ≤ T` of opens with `T ⊆ V ∪ U` is bijective
  (`Stacks.ClosedSubtopos.bijective_map_of_le_sup_offRange`), because the overlap of `V` with
  the rest of `T` lies in `U`, where `G` has a unique section;
* `U ⊆ U(W)` for *every* open `W` of `Z`, so a cover `W = ⋃ Wⱼ` of an open of `Z` makes
  `{U(Wⱼ)}` a cover of `U(W)` as soon as the index set is nonempty.

The second fact is what makes the naive inverse image a sheaf, and the first identifies its
direct image with `G`, the comparison at `V` being restriction along `V ≤ U(i⁻¹V)`.

## Main definitions

* `Stacks.ClosedSubtopos.opensSheaf`: the subterminal sheaf of sets cut out by an open.
* `Stacks.ClosedSubtopos.offRange`: the open complement of the image of a closed embedding.
* `Stacks.ClosedSubtopos.IsTerminalBelow`: the property of a sheaf of sets that its sections
  over every open contained in a given open form a singleton.
* `Stacks.ClosedSubtopos.naivePullback`: the naive inverse image `W ↦ Γ(G, U(W))`.

## Main results

* `Stacks.ClosedSubtopos.isIso_prod_fst_iff`: binary products of sheaves of sets are
  sectionwise, so `F ⨯ G ⟶ F` is invertible exactly when it is so on sections.
* `Stacks.ClosedSubtopos.closedComplement_opensSheaf_iff`: the closed complement of the
  subterminal sheaf of an open `U` consists of the sheaves with singleton sections below `U`.
* `Stacks.ClosedSubtopos.essImage_pushforward_iff`: a sheaf of sets on `X` lies in the essential
  image of `i_*` exactly when it has singleton sections below `X \ i(Z)`.
* `Stacks.ClosedSubtopos.isClosedSubtopos_essImage_pushforward`: consequently that essential
  image is a closed subtopos of `Sh(X)`.

## Implementation notes

Two developments in this library overlap with parts of this file and neither is reusable here,
which is recorded so that a consolidation pass can see the shape of the duplication.

* `StacksFrontier.CategoryTheory.Sites.Subtopos.Subtopoi` proves, for an *arbitrary* sheaf `F` on
  an arbitrary site, that `closedComplement F G` holds exactly when `G` has one section over
  every object over which `F` has one.  That subsumes
  `Stacks.ClosedSubtopos.closedComplement_opensSheaf_iff` and with it the three product lemmas
  it rests on.  It is `private` there, and reaching it would import that file, whose import
  list runs to thirty unrelated Mathlib modules; so the sectionwise description of
  `prod.fst : E ⨯ G ⟶ E` is proved again here, in the form that names the two factors' sections
  rather than morphisms out of arbitrary sheaves.
* `StacksFrontier.Topology.Sheaves.Functors.Module.ExactSupportSections` carries the same
  construction for sheaves of *modules*: its `opensComplRange` is
  `Stacks.ClosedSubtopos.offRange`, its `opensFunctor_opensMap_le_sup` is the inclusion that
  makes `Stacks.ClosedSubtopos.pushforwardNaiveHom` invertible, and its
  `isSheaf_opensFunctor_op_comp` is `Stacks.ClosedSubtopos.isSheaf_naivePullback`.  It is
  stated for `AddCommGrpCat`-valued presheaves on a closed quotient morphism of ringed spaces,
  with "terminal sections" in the shape "every section vanishes", so neither statement
  specialises to the other; the common generalisation would be a sheaf-condition lemma for
  `Topology.IsInducing.functor` over any concrete category with terminal sections off the
  image.

## References

* [Stacks Project, Tag 08LZ](https://stacks.math.columbia.edu/tag/08LZ)
* [Stacks Project, Tag 08LY](https://stacks.math.columbia.edu/tag/08LY)
* [Stacks Project, Tag 00AE](https://stacks.math.columbia.edu/tag/00AE)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite Topology

universe w v u

namespace Stacks.ClosedSubtopos

/-! ### Binary products of sheaves of sets are sectionwise -/

section Site

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- A morphism of sheaves of sets is an isomorphism exactly when it is an isomorphism on
sections over every object. -/
lemma isIso_iff_app {E G : Sheaf J (Type w)} (f : E ⟶ G) :
    IsIso f ↔ ∀ V : Cᵒᵖ, IsIso (((sheafToPresheaf J (Type w)).map f).app V) := by
  refine ⟨fun _ V => inferInstance, fun h => ?_⟩
  have := h
  have : IsIso ((sheafToPresheaf J (Type w)).map f) := NatIso.isIso_of_isIso_app _
  exact isIso_of_reflects_iso f (sheafToPresheaf J (Type w))

/-- The projection `E ⨯ G ⟶ E` of sheaves of sets is, on sections over an object `V`, the
projection `E(V) × G(V) ⟶ E(V)`: binary products of sheaves of sets are sectionwise. -/
lemma isIso_app_prod_fst_iff (E G : Sheaf J (Type w)) (V : Cᵒᵖ) :
    IsIso (((sheafToPresheaf J (Type w)).map (prod.fst : E ⨯ G ⟶ E)).app V) ↔
      Function.Bijective (Prod.fst : E.obj.obj V × G.obj.obj V → E.obj.obj V) := by
  set S := sheafToPresheaf J (Type w)
  set ev := (evaluation Cᵒᵖ (Type w)).obj V
  have h1 : prodComparison S E G ≫ (prod.fst : S.obj E ⨯ S.obj G ⟶ S.obj E) =
      S.map (prod.fst : E ⨯ G ⟶ E) := prodComparison_fst S E G
  have h2 : prodComparison ev (S.obj E) (S.obj G) ≫
      (prod.fst : E.obj.obj V ⨯ G.obj.obj V ⟶ E.obj.obj V) =
      ev.map (prod.fst : S.obj E ⨯ S.obj G ⟶ S.obj E) :=
    prodComparison_fst ev (S.obj E) (S.obj G)
  have h3 := Types.binaryProductIso_hom_comp_fst (E.obj.obj V) (G.obj.obj V)
  have key : (S.map (prod.fst : E ⨯ G ⟶ E)).app V =
      ((prodComparison S E G).app V ≫ prodComparison ev (S.obj E) (S.obj G) ≫
        (Types.binaryProductIso (E.obj.obj V) (G.obj.obj V)).hom) ≫ ↾Prod.fst := by
    have h2' : (prod.fst : S.obj E ⨯ S.obj G ⟶ S.obj E).app V =
        ev.map (prod.fst : S.obj E ⨯ S.obj G ⟶ S.obj E) := rfl
    rw [← h1, NatTrans.comp_app, h2', ← h2]
    simp only [Category.assoc, h3]
  have hiso : IsIso ((S.map (prod.fst : E ⨯ G ⟶ E)).app V) ↔
      IsIso (↾Prod.fst : E.obj.obj V × G.obj.obj V ⟶ E.obj.obj V) := by
    rw [key]
    exact ⟨fun _ => IsIso.of_isIso_comp_left
      ((prodComparison S E G).app V ≫ prodComparison ev (S.obj E) (S.obj G) ≫
        (Types.binaryProductIso (E.obj.obj V) (G.obj.obj V)).hom) _,
      fun _ => inferInstance⟩
  exact hiso.trans (isIso_iff_bijective _)

/-- The projection `E ⨯ G ⟶ E` of sheaves of sets is an isomorphism exactly when it is bijective
on sections over every object. -/
lemma isIso_prod_fst_iff (E G : Sheaf J (Type w)) :
    IsIso (prod.fst : E ⨯ G ⟶ E) ↔
      ∀ V : Cᵒᵖ, Function.Bijective (Prod.fst : E.obj.obj V × G.obj.obj V → E.obj.obj V) :=
  (isIso_iff_app _).trans (forall_congr' fun V => isIso_app_prod_fst_iff E G V)

/-- A product projection off a subsingleton factor is bijective exactly when the other factor
is a singleton whenever the first is nonempty. -/
lemma bijective_fst_uliftPLift {p : Prop} {B : Type w} :
    Function.Bijective (Prod.fst : ULift.{w} (PLift p) × B → ULift.{w} (PLift p)) ↔
      (p → Nonempty B ∧ Subsingleton B) := by
  constructor
  · intro h hp
    refine ⟨⟨(h.2 ⟨⟨hp⟩⟩).choose.2⟩, ⟨fun b b' => ?_⟩⟩
    exact congrArg Prod.snd (h.1 (rfl : (Prod.fst (⟨⟨hp⟩⟩, b)) = Prod.fst (⟨⟨hp⟩⟩, b')))
  · intro h
    refine ⟨fun x y hxy => ?_, fun a => ?_⟩
    · exact Prod.ext hxy ((h x.1.down.down).2.elim _ _)
    · obtain ⟨b⟩ := (h a.down.down).1
      exact ⟨(a, b), rfl⟩

end Site

/-! ### The subterminal sheaf cut out by an open -/

section Opens

variable {X : TopCat.{u}}

/-- The subterminal sheaf of sets cut out by an open `U` of `X`: its sections over `V` form a
singleton when `V ≤ U` and are empty otherwise.

Equivalently this is the sheaf represented by `U` in the lattice of opens; a family of opens
covering `V` is contained in `U` exactly when `V` is, which is the sheaf condition. -/
def opensSheaf (U : Opens X) : Sheaf (Opens.grothendieckTopology X) (Type u) where
  obj :=
    { obj := fun V => ULift.{u} (PLift (V.unop ≤ U))
      map := fun f => ↾fun h => ⟨⟨le_trans (leOfHom f.unop) h.down.down⟩⟩ }
  property := by
    refine (TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing (X := X) _).2 ?_
    intro ι W sf _
    refine ⟨⟨⟨iSup_le fun j => (sf j).down.down⟩⟩, fun _ => ?_, fun _ _ => ?_⟩ <;>
      exact Subsingleton.elim _ _

/-- Sections of `Stacks.ClosedSubtopos.opensSheaf U` over a fixed open are all equal. -/
lemma opensSheaf_eq (U : Opens X) (V : (Opens X)ᵒᵖ) (a b : (opensSheaf U).obj.obj V) : a = b := by
  obtain ⟨⟨a⟩⟩ := a
  obtain ⟨⟨b⟩⟩ := b
  rfl

/-- **Stacks 08LY, the subsheaf condition.** The sheaf `Stacks.ClosedSubtopos.opensSheaf U` is a
subsheaf of the terminal sheaf, its sections over any open forming a subsingleton. -/
lemma mono_terminal_from_opensSheaf (U : Opens X) :
    Mono (terminal.from (opensSheaf U)) := by
  apply (sheafToPresheaf (Opens.grothendieckTopology X) (Type u)).mono_of_mono_map
  rw [NatTrans.mono_iff_mono_app]
  exact fun V => (mono_iff_injective _).2 fun a b _ => opensSheaf_eq U V a b

/-- Two sections of a sheaf of sets over the same open agree as soon as their germs agree at
every point of that open. -/
lemma section_eq_of_germ_eq (G : Sheaf (Opens.grothendieckTopology X) (Type u)) (A : Opens X)
    (s t : G.obj.obj (op A))
    (h : ∀ (x : X) (hx : x ∈ A), TopCat.Presheaf.germ G.obj A x hx s =
      TopCat.Presheaf.germ G.obj A x hx t) :
    s = t :=
  TopCat.Presheaf.section_ext (C := Type u) (X := X) G A s t h

/-- A sheaf of sets `G` on `X` *has singleton sections below `U`* when `Γ(G, V)` is a singleton
for every open `V ≤ U`, that is, when `Γ(G, V)` is a terminal object of `Type u`. -/
def IsTerminalBelow (U : Opens X) (G : Sheaf (Opens.grothendieckTopology X) (Type u)) : Prop :=
  ∀ V : Opens X, V ≤ U → Nonempty (G.obj.obj (op V)) ∧ Subsingleton (G.obj.obj (op V))

/-- **Stacks 08LY.** The closed complement of the subterminal sheaf cut out by an open `U`
consists of exactly the sheaves of sets with singleton sections below `U`. -/
lemma closedComplement_opensSheaf_iff (U : Opens X)
    (G : Sheaf (Opens.grothendieckTopology X) (Type u)) :
    closedComplement (opensSheaf U) G ↔ IsTerminalBelow U G := by
  refine (isIso_prod_fst_iff (opensSheaf U) G).trans ⟨fun h V hVU => ?_, fun h V => ?_⟩
  · exact bijective_fst_uliftPLift.1 (h (op V)) hVU
  · exact bijective_fst_uliftPLift.2 (h V.unop)

end Opens

/-! ### The open complement of a closed subset -/

section OffRange

variable {Z X : TopCat.{u}} {i : Z ⟶ X}

/-- The open complement of the image of a closed embedding `i : Z ⟶ X`. -/
def offRange (hi : IsClosedEmbedding (ConcreteCategory.hom i)) : Opens X :=
  ⟨(Set.range (ConcreteCategory.hom i))ᶜ, hi.isClosed_range.isOpen_compl⟩

/-- A point lies off the image of `i` exactly when it lies in
`Stacks.ClosedSubtopos.offRange`. -/
lemma mem_offRange_iff (hi : IsClosedEmbedding (ConcreteCategory.hom i)) {x : X} :
    x ∈ offRange hi ↔ x ∉ Set.range (ConcreteCategory.hom i) :=
  Iff.rfl

/-- An open of `X` is contained in the complement of the image of `i` exactly when its preimage
under `i` is empty. -/
lemma le_offRange_iff (hi : IsClosedEmbedding (ConcreteCategory.hom i)) {V : Opens X} :
    V ≤ offRange hi ↔ (Opens.map i).obj V = ⊥ := by
  constructor
  · exact fun h => le_antisymm
      (fun z hz => absurd (Set.mem_range_self z) ((mem_offRange_iff hi).1 (h hz))) bot_le
  · intro h x hx
    refine (mem_offRange_iff hi).2 ?_
    rintro ⟨z, rfl⟩
    have hz : z ∈ (Opens.map i).obj V := hx
    rwa [h] at hz

/-- A point of `X` off `Stacks.ClosedSubtopos.offRange` is in the image of `i`. -/
private lemma exists_eq_of_notMem_offRange (hi : IsClosedEmbedding (ConcreteCategory.hom i))
    {x : X} (hx : x ∉ offRange hi) : ∃ z, ConcreteCategory.hom i z = x :=
  not_not.1 ((mem_offRange_iff hi).not.1 hx)

/-- The complement of the image of `i` is contained in the largest open of `X` whose preimage is
a given open `W` of `Z`: that preimage is unchanged by adjoining a set disjoint from the
image. -/
lemma offRange_le_functorObj (hi : IsClosedEmbedding (ConcreteCategory.hom i)) (W : Opens Z) :
    offRange hi ≤ hi.isInducing.functorObj W :=
  hi.isInducing.le_functorObj_iff.mpr
    (le_of_eq ((le_offRange_iff hi).1 le_rfl) |>.trans bot_le)

end OffRange

/-! ### Restriction along an inclusion whose complement misses the image -/

section Restriction

variable {Z X : TopCat.{u}} {i : Z ⟶ X} (hi : IsClosedEmbedding (ConcreteCategory.hom i))
  {G : Sheaf (Opens.grothendieckTopology X) (Type u)}

/-- Sections of `G` over an open disjoint from the image of `i` are all equal. -/
lemma sections_eq_of_le_offRange {G : Sheaf (Opens.grothendieckTopology X) (Type u)}
    (hG : IsTerminalBelow (offRange hi) G) {A : Opens X} (hA : A ≤ offRange hi)
    (a b : G.obj.obj (op A)) : a = b :=
  (hG A hA).2.elim a b

/-- A family of sections of `G` indexed by opens whose pairwise intersections miss the image of
`i` is automatically compatible: off the image `G` has a unique section, and the two restrictions
of a single index agree because the lattice of opens is thin. -/
lemma isCompatible_of_pairwise_le_offRange {G : Sheaf (Opens.grothendieckTopology X) (Type u)}
    (hG : IsTerminalBelow (offRange hi) G) {ι : Type*} (A : ι → Opens X)
    (sf : ∀ j, G.obj.obj (op (A j)))
    (h : ∀ j k, j ≠ k → A j ⊓ A k ≤ offRange hi) :
    TopCat.Presheaf.IsCompatible G.obj A sf := by
  intro j k
  by_cases hjk : j = k
  · subst hjk
    rw [Subsingleton.elim ((A j).infLELeft (A j)) ((A j).infLERight (A j))]
  · exact sections_eq_of_le_offRange hi hG (h j k hjk) _ _

/-- **The restriction lemma.** Let `G` have singleton sections below the complement `U` of the
image of a closed embedding `i`, and let `V ≤ T` be opens of `X` with `T ⊆ V ∪ U`.  Then
restriction `Γ(G, T) ⟶ Γ(G, V)` is bijective.

Indeed `{V, T ⊓ U}` covers `T`, and `G` has a unique section over `T ⊓ U` and over
`V ⊓ T ⊓ U`, so gluing a section over `V` with that unique section is possible in exactly one
way. -/
lemma bijective_map_of_le_sup_offRange {G : Sheaf (Opens.grothendieckTopology X) (Type u)}
    (hG : IsTerminalBelow (offRange hi) G)
    {V T : Opens X} (hVT : V ≤ T) (hTV : T ≤ V ⊔ offRange hi) :
    Function.Bijective (G.obj.map (homOfLE hVT).op) := by
  have hWT : ∀ b : Bool, (cond b V (T ⊓ offRange hi) : Opens X) ≤ T := by
    intro b
    cases b
    exacts [inf_le_left, hVT]
  have hcov : T ≤ iSup fun b : Bool => (cond b V (T ⊓ offRange hi) : Opens X) := by
    intro p hp
    rcases hTV hp with h | h
    · exact Opens.mem_iSup.2 ⟨true, h⟩
    · exact Opens.mem_iSup.2 ⟨false, ⟨hp, h⟩⟩
  have main : ∀ (t : G.obj.obj (op V)) (u₀ : G.obj.obj (op (T ⊓ offRange hi))),
      ∃! s : G.obj.obj (op T), G.obj.map (homOfLE hVT).op s = t ∧
        G.obj.map (homOfLE (inf_le_left : T ⊓ offRange hi ≤ T)).op s = u₀ := by
    intro t u₀
    have hc : TopCat.Presheaf.IsCompatible G.obj
        (fun b : Bool => (cond b V (T ⊓ offRange hi) : Opens X))
        (fun b => Bool.rec u₀ t b) := by
      refine isCompatible_of_pairwise_le_offRange hi hG _ _ fun b b' hbb => ?_
      cases b <;> cases b'
      · exact absurd rfl hbb
      · exact inf_le_left.trans inf_le_right
      · exact inf_le_right.trans inf_le_right
      · exact absurd rfl hbb
    have hequiv : ∀ s : G.obj.obj (op T),
        (∀ b : Bool, G.obj.map (homOfLE (hWT b)).op s = Bool.rec u₀ t b) ↔
          (G.obj.map (homOfLE hVT).op s = t ∧
            G.obj.map (homOfLE (inf_le_left : T ⊓ offRange hi ≤ T)).op s = u₀) := by
      intro s
      refine ⟨fun h => ⟨h true, h false⟩, fun h b => ?_⟩
      cases b
      exacts [h.2, h.1]
    exact (existsUnique_congr hequiv).1
      (TopCat.Sheaf.existsUnique_gluing' (C := Type u) (X := X) G _ T
        (fun b => homOfLE (hWT b)) hcov _ hc)
  refine ⟨fun s s' h => ?_, fun t => ?_⟩
  · obtain ⟨s₀, -, huniq⟩ := main (G.obj.map (homOfLE hVT).op s)
      (G.obj.map (homOfLE (inf_le_left : T ⊓ offRange hi ≤ T)).op s)
    rw [huniq s ⟨rfl, rfl⟩,
      huniq s' ⟨h.symm, sections_eq_of_le_offRange hi hG inf_le_right _ _⟩]
  · obtain ⟨u₀⟩ := (hG (T ⊓ offRange hi) inf_le_right).1
    obtain ⟨s, hs, -⟩ := main t u₀
    exact ⟨s, hs.1⟩

end Restriction

/-! ### The naive inverse image along a closed embedding -/

section NaiveDefs

variable {Z X : TopCat.{u}} {i : Z ⟶ X}

/-- The *naive inverse image* of a sheaf of sets `G` on `X` along an inducing map `i : Z ⟶ X`:
the presheaf `W ↦ Γ(G, U(W))` on `Z`, where `U(W) = ` `Topology.IsInducing.functorObj` `W` is the
largest open of `X` with preimage `W`.

For a closed embedding and a sheaf `G` with singleton sections off the image this is a sheaf
(`Stacks.ClosedSubtopos.isSheaf_naivePullback`) whose direct image is `G`. -/
def naivePullback (hi : IsClosedEmbedding (ConcreteCategory.hom i))
    (G : Sheaf (Opens.grothendieckTopology X) (Type u)) : (Opens Z)ᵒᵖ ⥤ Type u :=
  hi.isInducing.functor.op ⋙ G.obj

/-- The sections of the naive inverse image over `W` are the sections of `G` over `U(W)`. -/
lemma naivePullback_obj (hi : IsClosedEmbedding (ConcreteCategory.hom i))
    (G : Sheaf (Opens.grothendieckTopology X) (Type u)) (W : (Opens Z)ᵒᵖ) :
    (naivePullback hi G).obj W = G.obj.obj (op (hi.isInducing.functorObj W.unop)) :=
  rfl

/-- The comparison `i_*(naive inverse image of `G`) ⟶ G` on underlying presheaves: over `V` it
is restriction of sections of `G` along `V ≤ U(i⁻¹V)`.

Naturality holds because both composites are `G.obj.map` of a morphism of the thin category of
opens, and any two such morphisms with the same source and target are equal. -/
def pushforwardNaiveHom (hi : IsClosedEmbedding (ConcreteCategory.hom i))
    (G : Sheaf (Opens.grothendieckTopology X) (Type u)) :
    ((Opens.map i).op ⋙ naivePullback hi G) ⟶ G.obj where
  app V := G.obj.map (homOfLE (hi.isInducing.le_functorObj_iff.mpr
    (le_refl ((Opens.map i).obj V.unop)))).op
  naturality _ _ _ :=
    ((G.obj.map_comp _ _).symm.trans
      (congrArg G.obj.map (Subsingleton.elim _ _))).trans (G.obj.map_comp _ _)

end NaiveDefs

section NaivePullback

variable {Z X : TopCat.{u}} {i : Z ⟶ X} (hi : IsClosedEmbedding (ConcreteCategory.hom i))
  {G : Sheaf (Opens.grothendieckTopology X) (Type u)}

/-- Compatibility of a family of sections of the naive inverse image transfers to the family of
opens `U(Wⱼ)` of `X`.

Over a point off the image of `i` both restrictions land in a singleton; over a point `i z` of
the image the germ at `i z` of either restriction is the germ of the original section, which the
hypothesis compares inside `Γ(G, U(Wⱼ ⊓ Wₖ))`. -/
lemma isCompatible_functorObj (hG : IsTerminalBelow (offRange hi) G) {ι : Type*}
    (W : ι → Opens Z) (sf : ∀ j, G.obj.obj (op (hi.isInducing.functorObj (W j))))
    (hsf : TopCat.Presheaf.IsCompatible (naivePullback hi G) W sf) :
    TopCat.Presheaf.IsCompatible G.obj (fun j => hi.isInducing.functorObj (W j)) sf := by
  intro j k
  dsimp only
  refine section_eq_of_germ_eq G _ _ _ fun x hx => ?_
  rw [TopCat.Presheaf.germ_res_apply (C := Type u) (X := X) G.obj _ x hx,
    TopCat.Presheaf.germ_res_apply (C := Type u) (X := X) G.obj _ x hx]
  have key : ∀ {B : Opens X} (f : B ⟶ hi.isInducing.functorObj (W j))
      (g : B ⟶ hi.isInducing.functorObj (W k)) (hxB : x ∈ B),
      G.obj.map f.op (sf j) = G.obj.map g.op (sf k) →
      TopCat.Presheaf.germ G.obj _ x (f.le hxB) (sf j) =
        TopCat.Presheaf.germ G.obj _ x (g.le hxB) (sf k) := by
    intro B f g hxB h
    rw [← TopCat.Presheaf.germ_res_apply (C := Type u) (X := X) G.obj f x hxB,
      ← TopCat.Presheaf.germ_res_apply (C := Type u) (X := X) G.obj g x hxB, h]
  by_cases hxU : x ∈ offRange hi
  · -- near a point off the image both sections restrict into a singleton
    exact key (homOfLE (inf_le_left.trans inf_le_left))
      (homOfLE (inf_le_left.trans inf_le_right)) (B := (_ ⊓ _) ⊓ offRange hi) ⟨hx, hxU⟩
      (sections_eq_of_le_offRange hi hG inf_le_right _ _)
  · -- at a point of the image the hypothesis applies over `U(Wⱼ ⊓ Wₖ)`
    obtain ⟨z, rfl⟩ := exists_eq_of_notMem_offRange hi hxU
    exact key (hi.isInducing.functor.map ((W j).infLELeft (W k)))
      (hi.isInducing.functor.map ((W j).infLERight (W k)))
      ((hi.isInducing.mem_functorObj_iff (W j ⊓ W k)).2
        ⟨(hi.isInducing.mem_functorObj_iff (W j)).1 hx.1,
          (hi.isInducing.mem_functorObj_iff (W k)).1 hx.2⟩) (hsf j k)

/-- **The naive inverse image is a sheaf.** If `G` has singleton sections over every open
disjoint from the image of the closed embedding `i`, the presheaf `W ↦ Γ(G, U(W))` on `Z`
satisfies the sheaf condition.

For a nonempty cover `W = ⋃ Wⱼ` the opens `U(Wⱼ)` already cover `U(W)`: a point of `U(W)` off
the image of `i` lies in every `U(Wⱼ)`, and a point `i z` has `z ∈ Wⱼ` for some `j`.  So the
unique gluing for `G` over that cover is the unique gluing required.  For an empty cover the
open `U(⊥)` is disjoint from the image, where `G` has a unique section. -/
lemma isSheaf_naivePullback (hG : IsTerminalBelow (offRange hi) G) :
    Presheaf.IsSheaf (Opens.grothendieckTopology Z) (naivePullback hi G) := by
  refine (TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing (X := Z) _).2 ?_
  intro ι W sf hsf
  have hmap : (Opens.map i).obj (hi.isInducing.functorObj (iSup W)) = iSup W :=
    hi.isInducing.map_functorObj _
  rcases isEmpty_or_nonempty ι with hι | hι
  · have hbot : hi.isInducing.functorObj (iSup W) ≤ offRange hi := by
      refine (le_offRange_iff hi).2 ?_
      rw [hmap, iSup_of_empty]
    obtain ⟨s⟩ := (hG _ hbot).1
    exact ⟨s, isEmptyElim,
      fun y _ => sections_eq_of_le_offRange hi hG hbot y s⟩
  · have hVT : ∀ j, hi.isInducing.functorObj (W j) ≤ hi.isInducing.functorObj (iSup W) :=
      fun j => leOfHom (hi.isInducing.functor.map (homOfLE (le_iSup W j)))
    have hcov : hi.isInducing.functorObj (iSup W) ≤
        iSup fun j => hi.isInducing.functorObj (W j) := by
      intro p hp
      by_cases hpU : p ∈ offRange hi
      · obtain ⟨j⟩ := hι
        exact Opens.mem_iSup.2 ⟨j, offRange_le_functorObj hi (W j) hpU⟩
      · obtain ⟨z, rfl⟩ := exists_eq_of_notMem_offRange hi hpU
        have hz : z ∈ iSup W := by
          have : z ∈ (Opens.map i).obj (hi.isInducing.functorObj (iSup W)) := hp
          rwa [hmap] at this
        obtain ⟨j, hj⟩ := Opens.mem_iSup.1 hz
        exact Opens.mem_iSup.2 ⟨j, (hi.isInducing.mem_functorObj_iff (W j)).2 hj⟩
    exact TopCat.Sheaf.existsUnique_gluing' (C := Type u) (X := X) G _ _
      (fun j => homOfLE (hVT j)) hcov sf (isCompatible_functorObj hi hG W sf hsf)

/-- The naive inverse image, as a sheaf on `Z`. -/
def naivePullbackSheaf (hG : IsTerminalBelow (offRange hi) G) :
    Sheaf (Opens.grothendieckTopology Z) (Type u) :=
  ⟨naivePullback hi G, isSheaf_naivePullback hi hG⟩

/-- **The comparison is an isomorphism.** Over `V` it is restriction along `V ≤ U(i⁻¹V)`, and
`U(i⁻¹V) ⊆ V ∪ U`: a point of `U(i⁻¹V)` either lies off the image of `i`, hence in `U`, or is
`i z` with `z ∈ i⁻¹V`, hence lies in `V`.  So the restriction lemma applies. -/
lemma isIso_pushforwardNaiveHom (hG : IsTerminalBelow (offRange hi) G) :
    IsIso (pushforwardNaiveHom hi G) := by
  have happ : ∀ V : (Opens X)ᵒᵖ, IsIso ((pushforwardNaiveHom hi G).app V) := by
    intro V
    refine (isIso_iff_bijective _).2 ?_
    refine bijective_map_of_le_sup_offRange hi hG _ fun p hp => ?_
    by_cases hpU : p ∈ offRange hi
    · exact Or.inr hpU
    · obtain ⟨z, rfl⟩ := exists_eq_of_notMem_offRange hi hpU
      exact Or.inl ((hi.isInducing.mem_functorObj_iff ((Opens.map i).obj V.unop)).1 hp)
  have := happ
  exact NatIso.isIso_of_isIso_app _

/-- **The direct image of the naive inverse image is `G`.** Its sections over `V` are
`Γ(G, U(i⁻¹V))`, and restriction along `V ≤ U(i⁻¹V)` is bijective by the restriction lemma. -/
noncomputable def pushforwardNaivePullbackIso (hG : IsTerminalBelow (offRange hi) G) :
    (TopCat.Sheaf.pushforward (Type u) i).obj (naivePullbackSheaf hi hG) ≅ G :=
  (fullyFaithfulSheafToPresheaf (Opens.grothendieckTopology X) (Type u)).preimageIso
    (@asIso _ _ _ _ (pushforwardNaiveHom hi G) (isIso_pushforwardNaiveHom hi hG))

end NaivePullback

/-! ### The essential image of `i_*` -/

section Main

variable {Z X : TopCat.{u}} {i : Z ⟶ X} (hi : IsClosedEmbedding (ConcreteCategory.hom i))

/-- **Stacks 00AE, read off on sections.** A direct image `i_* F` along a closed embedding has
singleton sections over every open disjoint from the image of `i`: there `Γ(i_* F, V)` is
`Γ(F, ∅)`, which is terminal because `F` is a sheaf. -/
lemma isTerminalBelow_of_essImage {G : Sheaf (Opens.grothendieckTopology X) (Type u)}
    (hG : (TopCat.Sheaf.pushforward (Type u) i).essImage G) :
    IsTerminalBelow (offRange hi) G := by
  obtain ⟨F, ⟨e⟩⟩ := hG
  intro V hVU
  have hT : IsTerminal (G.obj.obj (op V)) :=
    IsTerminal.ofIso (TopCat.Sheaf.isTerminalOfEqEmpty F ((le_offRange_iff hi).1 hVU))
      (((sheafToPresheaf (Opens.grothendieckTopology X) (Type u)).mapIso e).app (op V))
  have hu := Types.isTerminalEquivUnique _ hT
  exact ⟨⟨hu.default⟩, ⟨fun a b => (hu.uniq a).trans (hu.uniq b).symm⟩⟩

/-- **The essential image of `i_*` on sheaves of sets, for `i` a closed embedding.** A sheaf of
sets on `X` is the direct image of a sheaf on `Z` exactly when its sections over every open
disjoint from the image of `i` form a singleton. -/
theorem essImage_pushforward_iff (G : Sheaf (Opens.grothendieckTopology X) (Type u)) :
    (TopCat.Sheaf.pushforward (Type u) i).essImage G ↔ IsTerminalBelow (offRange hi) G :=
  ⟨isTerminalBelow_of_essImage hi,
    fun hG => ⟨naivePullbackSheaf hi hG, ⟨pushforwardNaivePullbackIso hi hG⟩⟩⟩

/-- The essential image of `i_*` is the closed complement, in the sense of Stacks 08LY, of the
subterminal sheaf cut out by the complement of the image of `i`. -/
theorem closedComplement_opensSheaf_offRange_eq_essImage :
    closedComplement (opensSheaf (offRange hi)) =
      (TopCat.Sheaf.pushforward (Type u) i).essImage := by
  ext G
  rw [closedComplement_opensSheaf_iff, essImage_pushforward_iff hi]

/-- **The image of `i_*` on sheaves of sets is a closed subtopos.** For a closed embedding of
topological spaces `i : Z ⟶ X`, the essential image of the direct image functor on sheaves of
sets is a closed subtopos of `Sh(X)` in the sense of Stacks 08LZ: it is the closed complement of
the subterminal sheaf cut out by the open complement of `i(Z)`. -/
theorem isClosedSubtopos_essImage_pushforward
    (hi : IsClosedEmbedding (ConcreteCategory.hom i)) :
    IsClosedSubtopos (Opens.grothendieckTopology X)
      (TopCat.Sheaf.pushforward (Type u) i).essImage :=
  ⟨opensSheaf (offRange hi), mono_terminal_from_opensSheaf _,
    closedComplement_opensSheaf_offRange_eq_essImage hi⟩

end Main

end Stacks.ClosedSubtopos

end
