module

public import StacksFrontier.CategoryTheory.Sites.InverseSystem.CohomologyOfColimitOfFiniteSites
public import Mathlib.CategoryTheory.Sites.CoversTop.Basic

/-! # Global sections of a colimit of sheaves on a colimit of sites (the Cech step of 09YQ)

Stacks 09YN, in the weak-system form of
`InverseSystemOfFiniteSites.sections_colimit_pullback_of_colimit`, computes the sections of
`G = colim f_i^{-1}F_i` **over an object** `u_i(X)` of the colimit site as the filtered colimit
of the sections `F_j(u_a(X))`. Stacks 09YQ needs the same statement for the
sections over the *terminal sheaf* — the global sections of the site — because the small affine
etale site of a quasi-compact quasi-separated scheme has no terminal object, so its global
cohomology is not the cohomology over any object of it.

This file performs that passage in degree zero: it is the Cech / Mayer-Vietoris descent step of
Stacks 09YQ for `p = 0`, carried out purely on the side of sites, with no geometry. The input is
a *finite one-hypercover of the terminal sheaf* at one level of the system together with its
transition images, i.e. finitely many objects `W k` which jointly cover the terminal sheaf and,
for each pair `(k, l)`, finitely many objects `P k l m` through which any two morphisms into
`W k` and `W l` locally factor. The pair `(W, P)` plays the role of a finite affine cover of a
level together with finite affine covers of its pairwise intersections; it is exactly the data
that makes the sheaf condition over the terminal sheaf a *finite* limit of sections over objects,
which is what lets the filtered colimit pass through it.

## Main definitions

* `IsTopOneHypercover`: the finite one-hypercover of the terminal sheaf described above.
  `IsTopOneHypercover.of_isTerminal` shows the notion is not vacuous — a terminal object is one —
  and `IsTopOneHypercover.of_iso` transports it along isomorphisms of the data, which is what a
  geometric instantiation needs, the transition image of an object of a site being determined
  only up to isomorphism.

## Main results

* `existsUnique_sections_of_matching` and `sections_eq_of_eq_on_topOneHypercover`: the sheaf
  condition over the terminal sheaf, read off a finite one-hypercover. A family of sections of a
  sheaf of sets over the `W k` which matches on the `P k l m` comes from a unique global
  section, and a global section is determined by its values on the `W k`.
* `objectSections_jointlySurjective_and_separated`: the object-level colimit statement of Stacks
  09YN, in the transport-free form in which the two results below consume it. This is what makes
  those two results implications from a theorem of the library rather than from an assumption.
* `globalSections_jointlySurjective` and `globalSections_separated`: **the Cech step of Stacks
  09YQ in degree zero.** Given the object-level colimit statement of Stacks 09YN as hypotheses
  (`hsurj` and `hsep`), the global sections of `G` are the filtered colimit of the global sections
  of the `F_j`: every global section of `G` comes from a global section of some `F_n`, and two
  global sections of `F_n` with the same image agree after passing to a further level.
* `globalSections_colimit_pullback_of_colimit`: the two clauses together.

## Implementation notes

The object-level statement is a *hypothesis* (`hsurj`, `hsep`) rather than a reconstruction of
Stacks 09YN inside this file: what is proved here is precisely the implication "the colimit
statement over the objects of the one-hypercover implies the colimit statement over the terminal
sheaf", which is the step Stacks 09YQ's two-line proof passes over in silence. Both hypotheses
are clauses of
`InverseSystemOfFiniteSites.sections_colimit_pullback_of_colimit`, and that is proved here, in
`objectSections_jointlySurjective_and_separated`; they are written in a form free of
transports: `hsurj` and `hsep` speak of `s.val (op ((u j).obj ((D.u a).obj X)))` rather than of
`s.val (op ((u i).obj X))` transported along `hu`, these being sections of `G` over objects that
are equal. Neither is an instance of the conclusion of this file: they are statements about
sections over an *object*, the conclusion is about sections over the *terminal sheaf*, and for a
site with no terminal object the latter is not an instance of the former at all.

The map `ρ` on global sections is quantified over and pinned by `hρ` to the map induced by the
legs `ι`, exactly as `sections_colimit_pullback_of_colimit` quantifies over its canonical maps
`ρ` on sections over an object: `∀ ρ, ρ = e → P ρ` and `P e` are the same statement, and here
there is no closed form for `e` to be written as, a global section being determined by its
restrictions rather than given by a formula. `hρ` does determine `ρ` uniquely, by
`sections_eq_of_eq_on_topOneHypercover`.

Finiteness of the two index types `κ'` and `ν'` is what the proof uses, through
`CategoryTheory.IsCofiltered.wideCospan`: each of the finitely many matching conditions holds at
some level of the system, and a finite family of arrows into a fixed index of a cofiltered
category is dominated by a single arrow. This is the only place finiteness enters, and it is the
reason Stacks 09YQ needs the levels quasi-compact and quasi-separated: quasi-compactness makes
the cover finite, quasi-separatedness makes the covers of the pairwise intersections finite.

## References

* [Stacks 09YQ](https://stacks.math.columbia.edu/tag/09YQ)
* [Stacks 09YN](https://stacks.math.columbia.edu/tag/09YN)
* [Stacks 09YP](https://stacks.math.columbia.edu/tag/09YP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Sites.InverseSystem

universe u₁ u₂ w

namespace Stacks.WeakSites.ColimitGlobalSections

variable {C : Type w} [SmallCategory C] (J : GrothendieckTopology C)

/-- **A finite one-hypercover of the terminal sheaf.** The objects `W k` jointly cover the
terminal sheaf, and any two morphisms into members of the family factor, locally on the source,
through one of the objects `P k l m`. Think of the `W k` as a finite affine cover of a
quasi-compact scheme and of the `P k l m` as a finite affine cover of the intersection of `W k`
and `W l`, which exists when the scheme is quasi-separated; the `P k l m` stand in for a fibre
product `W k × W l`, which a site of affine objects need not contain. -/
structure IsTopOneHypercover {κ ν : Type*} (W : κ → C) (P : κ → κ → ν → C)
    (p₁ : ∀ k l m, P k l m ⟶ W k) (p₂ : ∀ k l m, P k l m ⟶ W l) : Prop where
  /-- The objects `W k` jointly cover the terminal sheaf. -/
  coversTop : J.CoversTop W
  /-- Any two morphisms into members of the family locally factor through some `P k l m`. -/
  locally_factors : ∀ (Z : C) (k l : κ) (f : Z ⟶ W k) (g : Z ⟶ W l),
    ∃ S : Sieve Z, S ∈ J Z ∧ ∀ ⦃V : C⦄ (q : V ⟶ Z), S.arrows q →
      ∃ (m : ν) (r : V ⟶ P k l m),
        q ≫ f = r ≫ p₁ k l m ∧ q ≫ g = r ≫ p₂ k l m

namespace IsTopOneHypercover

/-- **A terminal object is a one-hypercover of the terminal sheaf**, with the terminal object
itself in both roles. This is the instantiation at a site which does have a terminal object, so
the notion above is not vacuous; for such a site the conclusions of this file say that the
sections over the terminal object are the filtered colimit of the sections over the terminal
objects of the levels, which is the object-level statement at that object. -/
theorem of_isTerminal {T : C} (hT : IsTerminal T) :
    IsTopOneHypercover J (fun _ : Unit => T) (fun _ _ _ : Unit => T)
      (fun _ _ _ => 𝟙 T) (fun _ _ _ => 𝟙 T) where
  coversTop := by
    refine (J.coversTop_iff_of_isTerminal T hT _).2 (J.superset_covering ?_ (J.top_mem T))
    intro Z f _
    exact ⟨(), ⟨hT.from Z⟩⟩
  locally_factors Z _ _ f g := by
    refine ⟨⊤, J.top_mem Z, fun V q _ => ⟨(), q ≫ f, by simp, ?_⟩⟩
    rw [Category.comp_id, hT.hom_ext g f]

variable {J} {κ ν : Type*} {W W' : κ → C} {P P' : κ → κ → ν → C}
  {p₁ : ∀ k l m, P k l m ⟶ W k} {p₂ : ∀ k l m, P k l m ⟶ W l}
  {p₁' : ∀ k l m, P' k l m ⟶ W' k} {p₂' : ∀ k l m, P' k l m ⟶ W' l}

/-- **Transport along isomorphisms of the data.** A geometric instantiation produces the objects
of a level only up to isomorphism — the transition image of an object of a site is a base change,
pinned by a pullback square rather than by an equality — so this is the form in which the
hypotheses below are to be checked. -/
theorem of_iso (h : IsTopOneHypercover J W P p₁ p₂)
    (eW : ∀ k, W k ≅ W' k) (eP : ∀ k l m, P k l m ≅ P' k l m)
    (h₁ : ∀ k l m, p₁' k l m = (eP k l m).inv ≫ p₁ k l m ≫ (eW k).hom)
    (h₂ : ∀ k l m, p₂' k l m = (eP k l m).inv ≫ p₂ k l m ≫ (eW l).hom) :
    IsTopOneHypercover J W' P' p₁' p₂' where
  coversTop Z := by
    refine J.superset_covering ?_ (h.coversTop Z)
    rintro Y f ⟨k, ⟨b⟩⟩
    exact ⟨k, ⟨b ≫ (eW k).hom⟩⟩
  locally_factors Z k l f g := by
    obtain ⟨S, hS, hfac⟩ := h.locally_factors Z k l (f ≫ (eW k).inv) (g ≫ (eW l).inv)
    refine ⟨S, hS, fun V q hq => ?_⟩
    obtain ⟨m, r, e₁, e₂⟩ := hfac q hq
    refine ⟨m, r ≫ (eP k l m).hom, ?_, ?_⟩
    · rw [h₁, Category.assoc, Iso.hom_inv_id_assoc, ← Category.assoc, ← e₁]
      simp
    · rw [h₂, Category.assoc, Iso.hom_inv_id_assoc, ← Category.assoc, ← e₂]
      simp

end IsTopOneHypercover

/-! ### The sheaf condition over the terminal sheaf -/

section Sheaf

variable {J} {F : Cᵒᵖ ⥤ Type w}

/-- A family of elements indexed by objects is compatible as soon as any two morphisms into
members of the family agree locally after being pulled back: a sheaf is separated for a covering
sieve. -/
theorem isCompatible_of_locallyFactors
    (hF : Presheaf.IsSheaf J F) {κ : Type*} {Y : κ → C}
    (x : Presheaf.FamilyOfElementsOnObjects F Y)
    (h : ∀ (Z : C) (k l : κ) (f : Z ⟶ Y k) (g : Z ⟶ Y l),
      ∃ S : Sieve Z, S ∈ J Z ∧ ∀ ⦃V : C⦄ (p : V ⟶ Z), S.arrows p →
        F.map (p ≫ f).op (x k) = F.map (p ≫ g).op (x l)) :
    x.IsCompatible := by
  intro Z k l f g
  obtain ⟨S, hS, hagree⟩ := h Z k l f g
  refine (((isSheaf_iff_isSheaf_of_type _ _).1 hF).isSeparated _ hS).ext ?_
  intro V p hp
  have := hagree p hp
  simpa using this

variable {κ ν : Type*} {W : κ → C} {P : κ → κ → ν → C}
  {p₁ : ∀ k l m, P k l m ⟶ W k} {p₂ : ∀ k l m, P k l m ⟶ W l}

/-- **The sheaf condition over the terminal sheaf.** A family of sections over the `W k` which
matches on the `P k l m` is the restriction of a unique global section. Note that the matching
condition is a *finite* system of equations when the index types are finite, which is what makes
the global sections a finite limit of sections over objects. -/
theorem existsUnique_sections_of_matching (h : IsTopOneHypercover J W P p₁ p₂)
    (hF : Presheaf.IsSheaf J F) (x : ∀ k, F.obj (op (W k)))
    (hx : ∀ k l m, F.map (p₁ k l m).op (x k) = F.map (p₂ k l m).op (x l)) :
    ∃! s : F.sections, ∀ k, s.val (op (W k)) = x k := by
  have hcomp : Presheaf.FamilyOfElementsOnObjects.IsCompatible (F := F) (Y := W) x := by
    refine isCompatible_of_locallyFactors hF _ fun Z k l f g => ?_
    obtain ⟨S, hS, hfac⟩ := h.locally_factors Z k l f g
    refine ⟨S, hS, fun V q hq => ?_⟩
    obtain ⟨m, r, h₁, h₂⟩ := hfac q hq
    rw [h₁, h₂]
    simp only [op_comp, Functor.map_comp_apply]
    exact congrArg (F.map r.op) (hx k l m)
  obtain ⟨s, hs, -⟩ := hcomp.existsUnique_section h.coversTop hF
  refine ⟨s, hs, fun s' hs' => h.coversTop.sections_ext ⟨F, hF⟩ fun k => ?_⟩
  rw [hs' k, hs k]

/-- A global section of a sheaf of sets is determined by its values on the objects of a
one-hypercover of the terminal sheaf. -/
theorem sections_eq_of_eq_on_topOneHypercover (h : IsTopOneHypercover J W P p₁ p₂)
    (hF : Presheaf.IsSheaf J F) {s s' : F.sections}
    (hss : ∀ k, s.val (op (W k)) = s'.val (op (W k))) : s = s' :=
  h.coversTop.sections_ext ⟨F, hF⟩ hss

/-- Cancelling a transport along an equality of objects against a global section: a section of a
presheaf over equal objects is the same element. -/
private theorem eq_sections_of_map_eqToHom {H : Cᵒᵖ ⥤ Type w} (s : H.sections) {A B : C}
    (h : A = B) (z : H.obj (op A)) (hz : H.map (eqToHom (congrArg op h)) z = s.val (op B)) :
    z = s.val (op A) := by
  subst h
  simpa using hz

end Sheaf

/-! ### The object-level hypotheses are the content of Stacks 09YN -/

section Objectwise

/-- **The two object-level hypotheses of this file are exactly Stacks 09YN.** In the situation of
Stacks 0A34 with the functors `u i` exhibiting `C` as the colimit of the sites of the system and
`K` the coverings of Stacks 09YL, and with `G = colim f_i^{-1}F_i` presented by `ι`, `hι`, `hG`:
every section of `G` over an object `u_i(X)` comes, as the image under `ι` of a section of some
`F_j` over `u_a(X)`, from a level below `i`, and two sections of `F_j` over `u_a(X)` with the same
image under `ι` agree after applying `ψ b` for some `b : k ⟶ j`.

These are the hypotheses `hsurj` and `hsep` of `globalSections_jointlySurjective` and
`globalSections_separated`, so those theorems are implications from a theorem of the library and
not from an assumption: the only transports in the two clauses have been cancelled against the
section `s`, the objects `u_j(u_a(X))` and `u_i(X)` being equal. -/
theorem objectSections_jointlySurjective_and_separated
    (D : InverseSystemOfFiniteSites.{u₁, u₂, w}) (u : ∀ i, D.C i ⥤ C)
    (hu : ∀ {i j : D.I} (a : i ⟶ j), D.u a ⋙ u i = u j)
    (hobj : ∀ X : C, ∃ (i : D.I) (Y : D.C i), (u i).obj Y = X)
    (hhom : ∀ (i : D.I) (X Y : D.C i) (f : (u i).obj X ⟶ (u i).obj Y),
      ∃ (j : D.I) (a : j ⟶ i) (g : (D.u a).obj X ⟶ (D.u a).obj Y),
        (u j).map g = eqToHom (Functor.congr_obj (hu a) X) ≫ f ≫
          eqToHom (Functor.congr_obj (hu a) Y).symm)
    (hhom_inj : ∀ (i : D.I) (X Y : D.C i) (g₁ g₂ : X ⟶ Y),
      (u i).map g₁ = (u i).map g₂ → ∃ (j : D.I) (a : j ⟶ i), (D.u a).map g₁ = (D.u a).map g₂)
    (K : Precoverage C)
    (hK : ∀ (X : C) (R : Presieve X), R ∈ K X ↔
      ∃ (i : D.I) (Y : D.C i) (h : (u i).obj Y = X) (S : Presieve Y),
        S ∈ (D.J i).toPrecoverage Y ∧ S ∈ Precoverage.finite (D.C i) Y ∧
          R = h ▸ S.map (u i))
    (Fs : ∀ i, Sheaf (D.J i) (Type w))
    (ψ : ∀ {i j : D.I} (a : j ⟶ i), (Fs i).obj ⟶ (D.u a).op ⋙ (Fs j).obj)
    (hψ : ∀ {i j k : D.I} (a : j ⟶ i) (b : k ⟶ j) (V : D.C i) (x : (Fs i).obj.obj (op V)),
      (ψ (b ≫ a)).app (op V) x =
        (Fs k).obj.map (eqToHom (congrArg op (Functor.congr_obj (D.comp b a) V).symm))
          ((ψ b).app (op ((D.u a).obj V)) ((ψ a).app (op V) x)))
    (G : Sheaf K.toGrothendieck (Type w)) (ι : ∀ i, (Fs i).obj ⟶ (u i).op ⋙ G.obj)
    (hι : ∀ {i j : D.I} (a : j ⟶ i) (V : D.C i) (x : (Fs i).obj.obj (op V)),
      (ι i).app (op V) x =
        G.obj.map (eqToHom (congrArg op (Functor.congr_obj (hu a) V)))
          ((ι j).app (op ((D.u a).obj V)) ((ψ a).app (op V) x)))
    (hG : ∀ (H : Sheaf K.toGrothendieck (Type w)) (g : ∀ i, (Fs i).obj ⟶ (u i).op ⋙ H.obj),
      (∀ {i j : D.I} (a : j ⟶ i) (V : D.C i) (x : (Fs i).obj.obj (op V)),
          (g i).app (op V) x =
            H.obj.map (eqToHom (congrArg op (Functor.congr_obj (hu a) V)))
              ((g j).app (op ((D.u a).obj V)) ((ψ a).app (op V) x))) →
        ∃! h : G ⟶ H, ∀ (i : D.I) (V : D.C i) (x : (Fs i).obj.obj (op V)),
          (g i).app (op V) x = h.hom.app (op ((u i).obj V)) ((ι i).app (op V) x)) :
    (∀ (i : D.I) (X : D.C i) (s : G.obj.sections),
        ∃ (j : D.I) (a : j ⟶ i) (t : (Fs j).obj.obj (op ((D.u a).obj X))),
          (ι j).app (op ((D.u a).obj X)) t = s.val (op ((u j).obj ((D.u a).obj X)))) ∧
      ∀ (i : D.I) (X : D.C i) (j : D.I) (a : j ⟶ i)
        (t t' : (Fs j).obj.obj (op ((D.u a).obj X))),
        (ι j).app (op ((D.u a).obj X)) t = (ι j).app (op ((D.u a).obj X)) t' →
          ∃ (k : D.I) (b : k ⟶ j),
            (ψ b).app (op ((D.u a).obj X)) t = (ψ b).app (op ((D.u a).obj X)) t' := by
  have main : ∀ (i : D.I) (X : D.C i), _ ∧ _ := fun i X =>
    InverseSystemOfFiniteSites.sections_colimit_pullback_of_colimit D u hu hobj hhom hhom_inj
      K hK Fs ψ hψ G ι hι hG i X
      (fun {j} a t => G.obj.map (eqToHom (congrArg op (Functor.congr_obj (hu a) X)))
        ((ι j).app (op ((D.u a).obj X)) t)) (fun a t => rfl)
  refine ⟨fun i X s => ?_, fun i X j a t t' h => ?_⟩
  · obtain ⟨j, a, t, ht⟩ := (main i X).1 (s.val (op ((u i).obj X)))
    exact ⟨j, a, t, eq_sections_of_map_eqToHom s (Functor.congr_obj (hu a) X) _ ht⟩
  · exact (main i X).2 j a t t' (congrArg _ h)

end Objectwise

/-! ### The colimit statement for global sections -/

section Main

variable {J}
variable (D : InverseSystemOfFiniteSites.{u₁, u₂, w}) (u : ∀ i, D.C i ⥤ C)
  (hu : ∀ {i j : D.I} (a : i ⟶ j), D.u a ⋙ u i = u j)
  (Fs : ∀ i, Sheaf (D.J i) (Type w))
  (ψ : ∀ {i j : D.I} (a : j ⟶ i), (Fs i).obj ⟶ (D.u a).op ⋙ (Fs j).obj)
  (G : Sheaf J (Type w)) (ι : ∀ i, (Fs i).obj ⟶ (u i).op ⋙ G.obj)

/-- Transporting an identity "`ι` of a section of a level is the given global section" along an
equality of objects of that level. -/
private theorem app_eq_sections_of_objEq {n : D.I} {A B : D.C n} (h : A = B)
    (z : (Fs n).obj.obj (op A)) (s : G.obj.sections)
    (hz : (ι n).app (op A) z = s.val (op ((u n).obj A))) :
    (ι n).app (op B) ((Fs n).obj.map (eqToHom (congrArg op h)) z) =
      s.val (op ((u n).obj B)) := by
  subst h
  simpa using hz

/-- Finitely many equalities, each holding after applying `ψ` along some arrow, hold after
applying `ψ` along a single arrow, by cofilteredness of the index category. -/
private theorem exists_psi_eq_of_forall_exists {n : D.I} {α : Type*} [Finite α] {V : α → D.C n}
    (hψ : ∀ {i j k : D.I} (a : j ⟶ i) (b : k ⟶ j) (V : D.C i) (x : (Fs i).obj.obj (op V)),
      (ψ (b ≫ a)).app (op V) x =
        (Fs k).obj.map (eqToHom (congrArg op (Functor.congr_obj (D.comp b a) V).symm))
          ((ψ b).app (op ((D.u a).obj V)) ((ψ a).app (op V) x)))
    (x x' : ∀ c, (Fs n).obj.obj (op (V c)))
    (h : ∀ c, ∃ (m : D.I) (b : m ⟶ n), (ψ b).app (op (V c)) (x c) = (ψ b).app (op (V c)) (x' c)) :
    ∃ (m : D.I) (b : m ⟶ n), ∀ c, (ψ b).app (op (V c)) (x c) = (ψ b).app (op (V c)) (x' c) := by
  classical
  choose mm bb hbb using h
  obtain ⟨m, b, g, hg⟩ := IsCofiltered.wideCospan bb
  exact ⟨m, b, fun c => by rw [← hg c, hψ (bb c) (g c), hψ (bb c) (g c), hbb c]⟩

variable
  (hψ : ∀ {i j k : D.I} (a : j ⟶ i) (b : k ⟶ j) (V : D.C i) (x : (Fs i).obj.obj (op V)),
    (ψ (b ≫ a)).app (op V) x =
      (Fs k).obj.map (eqToHom (congrArg op (Functor.congr_obj (D.comp b a) V).symm))
        ((ψ b).app (op ((D.u a).obj V)) ((ψ a).app (op V) x)))
  (hι : ∀ {i j : D.I} (a : j ⟶ i) (V : D.C i) (x : (Fs i).obj.obj (op V)),
    (ι i).app (op V) x =
      G.obj.map (eqToHom (congrArg op (Functor.congr_obj (hu a) V)))
        ((ι j).app (op ((D.u a).obj V)) ((ψ a).app (op V) x)))
  (hsurj : ∀ (i : D.I) (X : D.C i) (s : G.obj.sections),
    ∃ (j : D.I) (a : j ⟶ i) (t : (Fs j).obj.obj (op ((D.u a).obj X))),
      (ι j).app (op ((D.u a).obj X)) t = s.val (op ((u j).obj ((D.u a).obj X))))
  (hsep : ∀ (i : D.I) (X : D.C i) (j : D.I) (a : j ⟶ i)
    (t t' : (Fs j).obj.obj (op ((D.u a).obj X))),
    (ι j).app (op ((D.u a).obj X)) t = (ι j).app (op ((D.u a).obj X)) t' →
      ∃ (k : D.I) (b : k ⟶ j),
        (ψ b).app (op ((D.u a).obj X)) t = (ψ b).app (op ((D.u a).obj X)) t')
  {κ' ν' : Type} [Finite κ'] [Finite ν'] (i₀ : D.I) (W₀ : κ' → D.C i₀)
  (P₀ : κ' → κ' → ν' → D.C i₀)
  (q₁ : ∀ k l m, P₀ k l m ⟶ W₀ k) (q₂ : ∀ k l m, P₀ k l m ⟶ W₀ l)
  (hlev : ∀ {n : D.I} (a : n ⟶ i₀), IsTopOneHypercover (D.J n)
    (fun k => (D.u a).obj (W₀ k)) (fun k l m => (D.u a).obj (P₀ k l m))
    (fun k l m => (D.u a).map (q₁ k l m)) (fun k l m => (D.u a).map (q₂ k l m)))
  (hC : IsTopOneHypercover J (fun k => (u i₀).obj (W₀ k))
    (fun k l m => (u i₀).obj (P₀ k l m)) (fun k l m => (u i₀).map (q₁ k l m))
    (fun k l m => (u i₀).map (q₂ k l m)))
  (ρ : ∀ {n : D.I} (_ : n ⟶ i₀), (Fs n).obj.sections → G.obj.sections)
  (hρ : ∀ {n : D.I} (a : n ⟶ i₀) (t : (Fs n).obj.sections) (Y : D.C n),
    (ρ a t).val (op ((u n).obj Y)) = (ι n).app (op Y) (t.val (op Y)))

omit [Finite ν'] in
include hψ hsep hρ in
/-- **Separatedness of the colimit of global sections.** Two global sections of `F n` with the
same image in the global sections of `G` have the same image in the global sections of `F m` for
some further level `m`: by `existsUnique_sections_of_matching` a global section of `F m` is
determined by its values on the one-hypercover, and those values agree. -/
theorem globalSections_separated (n : D.I) (a : n ⟶ i₀) (t t' : (Fs n).obj.sections)
    (h : ρ a t = ρ a t') :
    ∃ (m : D.I) (b : m ⟶ n), ∀ k : κ',
      (ψ b).app (op ((D.u a).obj (W₀ k))) (t.val (op ((D.u a).obj (W₀ k)))) =
        (ψ b).app (op ((D.u a).obj (W₀ k))) (t'.val (op ((D.u a).obj (W₀ k)))) := by
  refine exists_psi_eq_of_forall_exists D Fs ψ hψ _ _ fun k => ?_
  refine hsep i₀ (W₀ k) n a _ _ ?_
  rw [← hρ a t ((D.u a).obj (W₀ k)), ← hρ a t' ((D.u a).obj (W₀ k)), h]

include hu hψ hι hsurj hsep hlev hC hρ in
/-- **Joint surjectivity of the colimit of global sections: the Cech step of Stacks 09YQ in
degree zero.** Every global section of `G = colim f_i^{-1}F_i` is the image of a global section
of `F n` for some level `n` below `i₀`.

The proof is the Cech descent along the one-hypercover, carried out at the level of sections.
Each of the finitely many restrictions of `s` to the objects `u_{i₀}(W k)` descends to a level by
the object-level statement `hsurj`; a single level dominating those finitely many is found by
`CategoryTheory.IsCofiltered.wideCospan`; the finitely many matching conditions on the
`u_{i₀}(P k l m)` hold in `G`, because `s` is a global section, so by the object-level
separatedness `hsep` they hold at a further single level, again by `wideCospan`; and there the
matching family glues, by `existsUnique_sections_of_matching`. Finiteness of the index types is
used exactly at the two applications of `wideCospan`. -/
theorem globalSections_jointlySurjective (s : G.obj.sections) :
    ∃ (n : D.I) (a : n ⟶ i₀) (t : (Fs n).obj.sections), ρ a t = s := by
  classical
  have step0 : ∀ k : κ', ∃ (j : D.I) (a : j ⟶ i₀)
      (t : (Fs j).obj.obj (op ((D.u a).obj (W₀ k)))),
      (ι j).app (op ((D.u a).obj (W₀ k))) t =
        s.val (op ((u j).obj ((D.u a).obj (W₀ k)))) := fun k => hsurj i₀ (W₀ k) s
  choose jj aa tt htt using step0
  obtain ⟨n₁, a, e, he⟩ := IsCofiltered.wideCospan aa
  have step1 : ∀ k : κ', ∃ z : (Fs n₁).obj.obj (op ((D.u a).obj (W₀ k))),
      (ι n₁).app (op ((D.u a).obj (W₀ k))) z =
        s.val (op ((u n₁).obj ((D.u a).obj (W₀ k)))) := by
    intro k
    have hobj : (D.u (e k)).obj ((D.u (aa k)).obj (W₀ k)) = (D.u a).obj (W₀ k) :=
      (Functor.congr_obj (D.comp (e k) (aa k)) (W₀ k)).symm.trans
        (Functor.congr_obj (congrArg (fun h : n₁ ⟶ i₀ => D.u h) (he k)) (W₀ k))
    refine ⟨(Fs n₁).obj.map (eqToHom (congrArg op hobj))
      ((ψ (e k)).app (op ((D.u (aa k)).obj (W₀ k))) (tt k)), ?_⟩
    refine app_eq_sections_of_objEq D u Fs G ι hobj _ s ?_
    refine eq_sections_of_map_eqToHom s
      (Functor.congr_obj (hu (e k)) ((D.u (aa k)).obj (W₀ k))) _ ?_
    rw [← hι (e k) ((D.u (aa k)).obj (W₀ k)) (tt k), htt k]
  choose zz hzz using step1
  have hnat : ∀ (Y : D.C i₀) (k : κ') (f : (D.u a).obj Y ⟶ (D.u a).obj (W₀ k)),
      (ι n₁).app (op ((D.u a).obj Y)) ((Fs n₁).obj.map f.op (zz k)) =
        s.val (op ((u n₁).obj ((D.u a).obj Y))) := by
    intro Y k f
    rw [NatTrans.naturality_apply (ι n₁) f.op (zz k), hzz k]
    exact s.2 ((u n₁).map f).op
  have key : ∀ x : κ' × κ' × ν', ∃ (k' : D.I) (b : k' ⟶ n₁),
      (ψ b).app (op ((D.u a).obj (P₀ x.1 x.2.1 x.2.2)))
          ((Fs n₁).obj.map ((D.u a).map (q₁ x.1 x.2.1 x.2.2)).op (zz x.1)) =
        (ψ b).app (op ((D.u a).obj (P₀ x.1 x.2.1 x.2.2)))
          ((Fs n₁).obj.map ((D.u a).map (q₂ x.1 x.2.1 x.2.2)).op (zz x.2.1)) :=
    fun x => hsep i₀ (P₀ x.1 x.2.1 x.2.2) n₁ a _ _ ((hnat _ _ _).trans (hnat _ _ _).symm)
  obtain ⟨n, b, key2⟩ := exists_psi_eq_of_forall_exists D Fs ψ hψ
    (fun x : κ' × κ' × ν' => (Fs n₁).obj.map ((D.u a).map (q₁ x.1 x.2.1 x.2.2)).op (zz x.1))
    (fun x => (Fs n₁).obj.map ((D.u a).map (q₂ x.1 x.2.1 x.2.2)).op (zz x.2.1)) key
  have hlevn := hlev (b ≫ a)
  rw [D.comp b a] at hlevn
  simp only [Functor.comp_obj, Functor.comp_map] at hlevn
  have hmatch : ∀ (k l : κ') (m : ν'),
      (Fs n).obj.map ((D.u b).map ((D.u a).map (q₁ k l m))).op
          ((ψ b).app (op ((D.u a).obj (W₀ k))) (zz k)) =
        (Fs n).obj.map ((D.u b).map ((D.u a).map (q₂ k l m))).op
          ((ψ b).app (op ((D.u a).obj (W₀ l))) (zz l)) := by
    intro k l m
    have e₁ := NatTrans.naturality_apply (ψ b) ((D.u a).map (q₁ k l m)).op (zz k)
    have e₂ := NatTrans.naturality_apply (ψ b) ((D.u a).map (q₂ k l m)).op (zz l)
    simp only [Functor.comp_map, Functor.op_map, Quiver.Hom.unop_op] at e₁ e₂
    rw [← e₁, ← e₂]
    exact key2 (k, l, m)
  obtain ⟨t, ht, -⟩ := existsUnique_sections_of_matching hlevn (Fs n).2
    (fun k => (ψ b).app (op ((D.u a).obj (W₀ k))) (zz k)) hmatch
  refine ⟨n, b ≫ a, t, sections_eq_of_eq_on_topOneHypercover hC G.2 fun k => ?_⟩
  have hob : (u n).obj ((D.u (b ≫ a)).obj (W₀ k)) = (u i₀).obj (W₀ k) :=
    Functor.congr_obj (hu (b ≫ a)) (W₀ k)
  rw [← hob, hρ (b ≫ a) t ((D.u (b ≫ a)).obj (W₀ k))]
  have hco : (D.u (b ≫ a)).obj (W₀ k) = (D.u b).obj ((D.u a).obj (W₀ k)) :=
    Functor.congr_obj (D.comp b a) (W₀ k)
  rw [hco, ht k]
  refine eq_sections_of_map_eqToHom s (Functor.congr_obj (hu b) ((D.u a).obj (W₀ k))) _ ?_
  rw [← hι b ((D.u a).obj (W₀ k)) (zz k), hzz k]

include hu hψ hι hsurj hsep hlev hC hρ in
/-- **The Cech / Mayer-Vietoris step of Stacks 09YQ in degree zero.** Let the functors `u i`
exhibit `C` as the colimit of the sites of an inverse system of sites with finite coverings, let
`F i` be a system of sheaves of sets with transition maps `ψ`, and let `G` be the colimit
`colim f_i^{-1}F_i` with legs `ι`. Assume the object-level colimit statement of Stacks 09YN
(`hsurj`, `hsep`) and assume that a level `i₀` carries a finite one-hypercover of the terminal
sheaf whose transition images (`hlev`) and whose image in the colimit site (`hC`) are again such.
Then the global sections of `G` are the filtered colimit of the global sections of the `F n` over
the arrows `n ⟶ i₀`: the canonical maps `ρ` are jointly surjective, and two global sections of a
level with the same image agree, on the one-hypercover, after passing to a further level — hence,
by `existsUnique_sections_of_matching`, have the same image at that level.

This is the step that Stacks 09YQ's proof passes over: for a quasi-compact quasi-separated level
`X_i` the terminal object of its own small affine etale site does not exist, so the global
sections of that site are not the sections over any object of it, and Stacks 09YN does not apply
to them directly. What replaces the terminal object is the one-hypercover above, which a finite
affine cover of `X_i` together with finite affine covers of its pairwise intersections
supplies. -/
theorem globalSections_colimit_pullback_of_colimit :
    (∀ s : G.obj.sections, ∃ (n : D.I) (a : n ⟶ i₀) (t : (Fs n).obj.sections), ρ a t = s) ∧
      ∀ (n : D.I) (a : n ⟶ i₀) (t t' : (Fs n).obj.sections), ρ a t = ρ a t' →
        ∃ (m : D.I) (b : m ⟶ n), ∀ k : κ',
          (ψ b).app (op ((D.u a).obj (W₀ k))) (t.val (op ((D.u a).obj (W₀ k)))) =
            (ψ b).app (op ((D.u a).obj (W₀ k))) (t'.val (op ((D.u a).obj (W₀ k)))) :=
  ⟨globalSections_jointlySurjective D u hu Fs ψ G ι hψ hι hsurj hsep i₀ W₀ P₀ q₁ q₂ hlev hC ρ hρ,
    fun n a t t' h => globalSections_separated D u Fs ψ G ι hψ hsep i₀ W₀ ρ hρ n a t t' h⟩

end Main

end Stacks.WeakSites.ColimitGlobalSections

end
