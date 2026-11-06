module

public import StacksFrontier.CategoryTheory.Sites.InverseSystem.GlobalSectionsOfColimitOfFiniteSites
public import StacksFrontier.CategoryTheory.Sites.InverseSystem.GlobalSectionsOfColimitOfFiniteSitesHypercover

/-! # The sheaf condition over an object, from a finite one-hypercover of that object

`Stacks.WeakSites.ColimitGlobalSections.IsTopOneHypercoverOn` is a finite one-hypercover of the
*terminal sheaf* of a site, and
`Stacks.WeakSites.ColimitGlobalSections.existsUnique_sections_of_matching` reads the sheaf
condition off it: the global sections of a sheaf of sets are its matching families on the
hypercover. That is what the degree-zero statement of [Stacks, Tag 09YQ] needs at a level, whose
small affine étale site has no terminal object.

The Čech step of Tag 09YQ needs the same description of the sections over a quasi-compact
*separated* étale object `V`, and `V` is likewise not an object of the small affine étale site
unless it is affine. This file supplies the notion and the sheaf condition in that relative form:
a finite family `W k ⟶ V` covering `V`, together with objects `P k l m` through which two
morphisms into `W k` and `W l` agreeing over `V` locally factor.

## Main definitions

* `IsOneHypercoverOf`: the relative notion. `IsOneHypercoverOf.ofTop` shows it generalises
  `IsTopOneHypercoverOn` on the nose at a terminal object, so nothing is lost by moving to it.

## Main results

* `existsUnique_sectionOver_of_matching`: **the sheaf condition over `V`.** A family of sections
  over the `W k` matching on the `P k l m` is the restriction of a unique section over `V`.
* `sectionOver_eq_of_eq_on_oneHypercoverOf`: a section over `V` is determined by its restrictions
  to the `W k`.
* `matchingFamilyOfSectionOver` and `sectionOverEquivMatchingFamily`: the sections over `V` **are**
  the matching families of
  `Stacks.WeakSites.ColimitGlobalSections.MatchingFamily`, which is the form in which
  `Stacks.WeakSites.ColimitGlobalSections.matchingFamiliesIsColimit_of_finite` computes them as a
  filtered colimit. Finiteness of the index types is what makes that description a finite limit,
  and it is why the object has to be quasi-compact and the covers of the pairwise overlaps finite.
* `sectionOverEquivMatchingFamilyRestrict`: the same identification read two categories away from
  the datum — the datum lives in one category, a functor carries it to a second, another functor
  carries it on to the site where it covers `V`, and the sheaf there restricts to a given presheaf
  on the second. This is the shape both sides of the statement below need.
* `sectionOver_colimit_of_oneHypercoverOf`: **the Čech step of [Stacks, Tag 09YQ] in degree zero
  over an object neither the levels nor the colimit site contain.** The sections of
  `𝒢 = colim f_i^{-1}F_i` over `V` are the filtered colimit of the sections of the `F_n` over the
  `V_n`, given one finite datum of objects of a level which covers `V_n` at every level and `V` at
  the colimit. `exists_sectionOver_map_of_oneHypercoverOf` exhibits the map between the two sides,
  so the statement is not vacuous, and `levelSectionEquiv` and `colimitSectionEquiv` are the two
  instantiations of `sectionOverEquivMatchingFamilyRestrict` it is proved from.

## Implementation notes

The covering clause is stated for the sieve *generated* by the family, which is what a
Grothendieck topology has members of; `CategoryTheory.Presieve.isSheafFor_iff_generate` turns it
into the sheaf condition for the family itself, and
`CategoryTheory.Presieve.isSheafFor_arrows_iff` turns that into the explicit description of the
sections over `V` used here. No fibre products of the site are needed anywhere: the `P k l m` are
what replaces `W k ×_V W l`, exactly as in the absolute case, and a site of affine objects over a
non-separated base does not contain those fibre products.

## References

* [Stacks 09YQ](https://stacks.math.columbia.edu/tag/09YQ)
* [Stacks 09YN](https://stacks.math.columbia.edu/tag/09YN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Sites.InverseSystem

universe w u₁ u₂ v₁ v₂ v₃ v₄ v₅ v₆ t₁ t₂

namespace Stacks.WeakSites.ColimitGlobalSections

section OverAnObject

variable {C : Type v₁} [Category.{v₂} C] (J : GrothendieckTopology C)

/-- **A finite one-hypercover of an object `V`.** The morphisms `f k : W k ⟶ V` generate a
covering sieve of `V`, the two projections of each `P k l m` agree over `V`, and any two morphisms
into `W k` and `W l` which agree over `V` factor, locally on their source, through some
`P k l m`.

Think of `V` as a quasi-compact separated scheme étale over the base, of the `W k` as a finite
affine open cover of it and of the `P k l m` as a finite affine cover of the overlap of `W k` and
`W l`. The `P k l m` stand in for the fibre product `W k ×_V W l`, which a site of affine objects
need not contain.

`Stacks.WeakSites.ColimitGlobalSections.IsTopOneHypercoverOn` is the case of the terminal sheaf:
`IsOneHypercoverOf.ofTop` derives this notion from it at a terminal object. -/
structure IsOneHypercoverOf {κ ν : Type t₁} (V : C) (W : κ → C) (f : ∀ k, W k ⟶ V)
    (P : κ → κ → ν → C) (p₁ : ∀ k l m, P k l m ⟶ W k)
    (p₂ : ∀ k l m, P k l m ⟶ W l) : Prop where
  /-- The family `f k : W k ⟶ V` generates a covering sieve of `V`. -/
  covers : Sieve.generate (Presieve.ofArrows W f) ∈ J V
  /-- The two projections of a second-layer object agree over `V`. -/
  comm : ∀ k l m, p₁ k l m ≫ f k = p₂ k l m ≫ f l
  /-- Two morphisms into members of the family which agree over `V` locally factor through some
  second-layer object. -/
  locally_factors : ∀ (Z : C) (k l : κ) (g : Z ⟶ W k) (h : Z ⟶ W l), g ≫ f k = h ≫ f l →
    ∃ S : Sieve Z, S ∈ J Z ∧ ∀ ⦃T : C⦄ (q : T ⟶ Z), S.arrows q →
      ∃ (m : ν) (r : T ⟶ P k l m),
        q ≫ g = r ≫ p₁ k l m ∧ q ≫ h = r ≫ p₂ k l m

namespace IsOneHypercoverOf

variable {J}

/-- **A one-hypercover of the terminal sheaf is a one-hypercover of a terminal object.** The
covering clause is `CoversTop` read at the terminal object, and the factorisation clause is the
absolute one, the hypothesis that the two morphisms agree over the terminal object being
vacuous. -/
theorem ofTop {κ ν : Type t₁} {W : κ → C} {P : κ → κ → ν → C}
    {p₁ : ∀ k l m, P k l m ⟶ W k} {p₂ : ∀ k l m, P k l m ⟶ W l}
    (h : IsTopOneHypercoverOn J W P p₁ p₂) {V : C} (hV : IsTerminal V) :
    IsOneHypercoverOf J V W (fun k => hV.from (W k)) P p₁ p₂ where
  covers := by
    have he : Sieve.generate (Presieve.ofArrows W (fun k => hV.from (W k))) =
        Sieve.ofObjects W V :=
      Sieve.ofArrows_eq_ofObjects hV W _
    rw [he]
    exact h.coversTop V
  comm _ _ _ := hV.hom_ext _ _
  locally_factors Z k l g g' _ := h.locally_factors Z k l g g'

section Transport

variable {κ ν : Type t₁} {V : C} {W W' : κ → C} {f : ∀ k, W k ⟶ V} {f' : ∀ k, W' k ⟶ V}
  {P P' : κ → κ → ν → C} {p₁ : ∀ k l m, P k l m ⟶ W k} {p₂ : ∀ k l m, P k l m ⟶ W l}
  {p₁' : ∀ k l m, P' k l m ⟶ W' k} {p₂' : ∀ k l m, P' k l m ⟶ W' l}

/-- **Transport along isomorphisms of the data.** A geometric instantiation produces the objects
of a level only up to isomorphism — the transition image of an object of a site is a base change,
pinned by a pullback square rather than by an equality — so this is the form in which the
hypothesis is to be checked.

This is the relative counterpart of
`Stacks.WeakSites.ColimitGlobalSections.IsTopOneHypercoverOn.of_iso`, with one clause more: the
legs to `V` are part of the datum here, so the transported legs are required to be the old ones
read through the isomorphisms. That is no constraint on a consumer, the legs of the transported
datum being its own to choose; what it does is make the covering clause and the agreement clause
follow from the old ones with no computation. -/
theorem of_iso (h : IsOneHypercoverOf J V W f P p₁ p₂)
    (eW : ∀ k, W k ≅ W' k) (eP : ∀ k l m, P k l m ≅ P' k l m)
    (hf : ∀ k, f' k = (eW k).inv ≫ f k)
    (h₁ : ∀ k l m, p₁' k l m = (eP k l m).inv ≫ p₁ k l m ≫ (eW k).hom)
    (h₂ : ∀ k l m, p₂' k l m = (eP k l m).inv ≫ p₂ k l m ≫ (eW l).hom) :
    IsOneHypercoverOf J V W' f' P' p₁' p₂' where
  covers := by
    refine J.superset_covering ?_ h.covers
    rintro Y g ⟨Z, a, b, ⟨k⟩, rfl⟩
    refine ⟨W' k, a ≫ (eW k).hom, f' k, ⟨k⟩, ?_⟩
    rw [hf, Category.assoc, Iso.hom_inv_id_assoc]
  comm k l m := by
    rw [h₁, h₂, hf, hf]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [h.comm k l m]
  locally_factors Z k l g g' hgg := by
    obtain ⟨S, hS, hfac⟩ := h.locally_factors Z k l (g ≫ (eW k).inv) (g' ≫ (eW l).inv) (by
      rw [Category.assoc, Category.assoc, ← hf, ← hf, hgg])
    refine ⟨S, hS, fun T q hq => ?_⟩
    obtain ⟨m, r, e₁, e₂⟩ := hfac q hq
    refine ⟨m, r ≫ (eP k l m).hom, ?_, ?_⟩
    · rw [h₁, Category.assoc, Iso.hom_inv_id_assoc, ← Category.assoc, ← e₁]
      simp
    · rw [h₂, Category.assoc, Iso.hom_inv_id_assoc, ← Category.assoc, ← e₂]
      simp

/-- **Re-indexing a one-hypercover of an object along equivalences of the index types.** The
notion depends on the index types only through the families, so a bijective change of index
carries a one-hypercover to a one-hypercover.

The relative counterpart of
`Stacks.WeakSites.ColimitGlobalSections.IsTopOneHypercoverOn.reindex`, and needed for the same
reason: the consumers bind the index types in `Type` — universe zero, finite — while a datum
produced from geometry is indexed in the universe of the schemes. -/
theorem reindex {κ₀ ν₀ : Type t₁} {κ₁ ν₁ : Type t₂} {V : C} {W₀ : κ₀ → C}
    {f₀ : ∀ k, W₀ k ⟶ V} {P₀ : κ₀ → κ₀ → ν₀ → C} {q₁ : ∀ k l m, P₀ k l m ⟶ W₀ k}
    {q₂ : ∀ k l m, P₀ k l m ⟶ W₀ l} (h : IsOneHypercoverOf J V W₀ f₀ P₀ q₁ q₂)
    (eκ : κ₁ ≃ κ₀) (eν : ν₁ ≃ ν₀) :
    IsOneHypercoverOf J V (fun k => W₀ (eκ k)) (fun k => f₀ (eκ k))
      (fun k l m => P₀ (eκ k) (eκ l) (eν m))
      (fun k l m => q₁ (eκ k) (eκ l) (eν m)) (fun k l m => q₂ (eκ k) (eκ l) (eν m)) where
  covers := by
    refine J.superset_covering ?_ h.covers
    rintro Y g ⟨Z, a, b, ⟨k⟩, rfl⟩
    obtain ⟨k', rfl⟩ := eκ.surjective k
    exact ⟨_, a, _, ⟨k'⟩, rfl⟩
  comm k l m := h.comm _ _ _
  locally_factors Z k l g g' hgg := by
    obtain ⟨T, hT, hfac⟩ := h.locally_factors Z (eκ k) (eκ l) g g' hgg
    refine ⟨T, hT, fun V' q hq => ?_⟩
    obtain ⟨m, r, e₁, e₂⟩ := hfac q hq
    obtain ⟨m', rfl⟩ := eν.surjective m
    exact ⟨m', r, e₁, e₂⟩

end Transport

end IsOneHypercoverOf

variable {J} {κ ν : Type t₁} {V : C} {W : κ → C} {f : ∀ k, W k ⟶ V} {P : κ → κ → ν → C}
  {p₁ : ∀ k l m, P k l m ⟶ W k} {p₂ : ∀ k l m, P k l m ⟶ W l} {F : Cᵒᵖ ⥤ Type w}

/-- Two composites of restriction maps agree when the underlying composites of morphisms do. -/
private theorem map_op_map_op_eq_of_comp_eq {X Y Y' Z : C} {a : X ⟶ Y} {b : Y ⟶ Z} {c : X ⟶ Y'}
    {d : Y' ⟶ Z} (h : a ≫ b = c ≫ d) (x : F.obj (op Z)) :
    F.map a.op (F.map b.op x) = F.map c.op (F.map d.op x) := by
  rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp, h]

/-- **The sheaf condition over `V`.** A family of sections of a sheaf of sets over the objects
`W k` of a one-hypercover of `V` which matches on the objects `P k l m` is the restriction of a
unique section over `V`.

When the two index types are finite the matching condition is a finite system of equations, so
this exhibits the sections over `V` as a *finite* limit of sections over objects of the site; that
is what lets a filtered colimit pass through it in
`Stacks.WeakSites.ColimitGlobalSections.matchingFamiliesIsColimit_of_finite`. -/
theorem existsUnique_sectionOver_of_matching (h : IsOneHypercoverOf J V W f P p₁ p₂)
    (hF : Presheaf.IsSheaf J F) (x : ∀ k, F.obj (op (W k)))
    (hx : ∀ k l m, F.map (p₁ k l m).op (x k) = F.map (p₂ k l m).op (x l)) :
    ∃! s : F.obj (op V), ∀ k, F.map (f k).op s = x k := by
  have hFt : Presieve.IsSheaf J F := (isSheaf_iff_isSheaf_of_type J F).1 hF
  have hsf : (Presieve.ofArrows W f).IsSheafFor F :=
    (Presieve.isSheafFor_iff_generate _).2 (hFt _ h.covers)
  rw [Presieve.isSheafFor_arrows_iff] at hsf
  refine hsf x fun k l Z g g' hcomm => ?_
  obtain ⟨S, hS, hfac⟩ := h.locally_factors Z k l g g' hcomm
  refine ((hFt.isSeparated _ hS).ext fun T q hq => ?_)
  obtain ⟨m, r, h₁, h₂⟩ := hfac q hq
  rw [map_op_map_op_eq_of_comp_eq h₁, map_op_map_op_eq_of_comp_eq h₂, hx k l m]

/-- **A section over `V` is determined by its restrictions to a one-hypercover of `V`.** The
separatedness half of the sheaf condition above. -/
theorem sectionOver_eq_of_eq_on_oneHypercoverOf (h : IsOneHypercoverOf J V W f P p₁ p₂)
    (hF : Presheaf.IsSheaf J F) {s s' : F.obj (op V)}
    (hss : ∀ k, F.map (f k).op s = F.map (f k).op s') : s = s' := by
  have hFt : Presieve.IsSheaf J F := (isSheaf_iff_isSheaf_of_type J F).1 hF
  refine (hFt.isSeparated _ h.covers).ext fun T q hq => ?_
  obtain ⟨T', a, b, ⟨k⟩, rfl⟩ := hq
  rw [op_comp, Functor.map_comp_apply, Functor.map_comp_apply, hss k]

/-- **The matching family of a section over `V`**: its restrictions to the objects of a
one-hypercover of `V`. -/
def matchingFamilyOfSectionOver (h : IsOneHypercoverOf J V W f P p₁ p₂) (s : F.obj (op V)) :
    MatchingFamily F W P p₁ p₂ where
  val k := F.map (f k).op s
  matching k l m := by
    rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp, h.comm k l m]

/-- The component of `matchingFamilyOfSectionOver h s` at `k` is the restriction of `s` along
`f k`. -/
@[simp]
theorem matchingFamilyOfSectionOver_val (h : IsOneHypercoverOf J V W f P p₁ p₂)
    (s : F.obj (op V)) (k : κ) :
    (matchingFamilyOfSectionOver h s).val k = F.map (f k).op s :=
  rfl

/-- **The sections of a sheaf of sets over `V` ARE its matching families on a one-hypercover of
`V`.** This is the identification that makes the colimit statement for matching families,
`Stacks.WeakSites.ColimitGlobalSections.matchingFamiliesIsColimit_of_finite`, a statement about
sections over `V`. -/
def sectionOverEquivMatchingFamily (h : IsOneHypercoverOf J V W f P p₁ p₂)
    (hF : Presheaf.IsSheaf J F) : F.obj (op V) ≃ MatchingFamily F W P p₁ p₂ where
  toFun := matchingFamilyOfSectionOver h
  invFun y := (existsUnique_sectionOver_of_matching h hF y.val y.matching).choose
  left_inv s := sectionOver_eq_of_eq_on_oneHypercoverOf h hF
    (existsUnique_sectionOver_of_matching h hF _
      (matchingFamilyOfSectionOver h s).matching).choose_spec.1
  right_inv y := MatchingFamily.ext (funext fun k =>
    (existsUnique_sectionOver_of_matching h hF y.val y.matching).choose_spec.1 k)

end OverAnObject

/-! ### The sections over an object, two categories away from the datum -/

section Restrict

variable {A₁ : Type v₁} [Category.{v₂} A₁] {A₂ : Type v₃} [Category.{v₄} A₂]
  {A₃ : Type v₅} [Category.{v₆} A₃] {κ ν : Type t₁}

/-- **The sections of a sheaf over an object `V`, as the matching families of a datum two
categories away.** The datum `(W, P, q₁, q₂)` lives in `A₁`; a functor `U : A₁ ⥤ A₂` carries it
to `A₂`, a functor `T : A₂ ⥤ A₃` carries it on to the site `(A₃, K)` where it is a
one-hypercover of `V`, and `eF` identifies the restriction of the sheaf `F` along `T` with a
presheaf `H` on `A₂`. The conclusion is that the sections of `F` over `V` are the matching
families on `(W, P, q₁, q₂)` of the restriction of `H` along `U`.

This is the one identification both sides of the degree-zero statement of [Stacks, Tag 09YQ] over
a quasi-compact separated object need, and they need it in exactly this shape. At a level of the
system `A₁` is the level `i₀`, `A₂` the level `n`, `U` the transition functor, `A₃` the ambient
site of the level — its small étale site, of which the level's small affine étale site is a dense
subsite — `T` that inclusion, `F` the sheaf on the ambient site, `H` the sheaf of the level and
`eF` Stacks 04HR. At the colimit `A₂` is the colimit site, `U` the functor from the level `i₀`,
and the rest is the same with the limit in place of a level.

Three transports do the work and none of them is avoidable: `MatchingFamily.comp` twice, because
restricting a presheaf along a functor and then evaluating on a datum is evaluating on the image
datum — definitionally, but not at the same type, `MatchingFamily` being an inductive type whose
arguments must match; and `MatchingFamily.mapIso`, because an equivalence of categories of sheaves
pins the presheaf only up to a natural isomorphism. -/
def sectionOverEquivMatchingFamilyRestrict (U : A₁ ⥤ A₂) (T : A₂ ⥤ A₃)
    {K : GrothendieckTopology A₃} {F : A₃ᵒᵖ ⥤ Type w} (hF : Presheaf.IsSheaf K F)
    {H : A₂ᵒᵖ ⥤ Type w} (eF : T.op ⋙ F ≅ H)
    {V : A₃} {W : κ → A₁} {P : κ → κ → ν → A₁}
    {q₁ : ∀ k l m, P k l m ⟶ W k} {q₂ : ∀ k l m, P k l m ⟶ W l}
    {fV : ∀ k, T.obj (U.obj (W k)) ⟶ V}
    (hV : IsOneHypercoverOf K V (fun k => T.obj (U.obj (W k))) fV
      (fun k l m => T.obj (U.obj (P k l m)))
      (fun k l m => T.map (U.map (q₁ k l m))) (fun k l m => T.map (U.map (q₂ k l m)))) :
    F.obj (op V) ≃ MatchingFamily (U.op ⋙ H) W P q₁ q₂ :=
  (sectionOverEquivMatchingFamily hV hF).trans
    ((((MatchingFamily.comp (W := fun k => U.obj (W k))
            (P := fun k l m => U.obj (P k l m))
            (p₁ := fun k l m => U.map (q₁ k l m))
            (p₂ := fun k l m => U.map (q₂ k l m)) T F).symm.trans
          (MatchingFamily.mapIso eF)).trans
        (MatchingFamily.comp (p₁ := q₁) (p₂ := q₂) U H).symm))

/-- The component at `k` of the matching family attached to `s` by
`sectionOverEquivMatchingFamilyRestrict` is the image under `eF` of the restriction of `s` along
`fV k`. -/
@[simp]
theorem sectionOverEquivMatchingFamilyRestrict_apply_val (U : A₁ ⥤ A₂) (T : A₂ ⥤ A₃)
    {K : GrothendieckTopology A₃} {F : A₃ᵒᵖ ⥤ Type w} (hF : Presheaf.IsSheaf K F)
    {H : A₂ᵒᵖ ⥤ Type w} (eF : T.op ⋙ F ≅ H)
    {V : A₃} {W : κ → A₁} {P : κ → κ → ν → A₁}
    {q₁ : ∀ k l m, P k l m ⟶ W k} {q₂ : ∀ k l m, P k l m ⟶ W l}
    {fV : ∀ k, T.obj (U.obj (W k)) ⟶ V}
    (hV : IsOneHypercoverOf K V (fun k => T.obj (U.obj (W k))) fV
      (fun k l m => T.obj (U.obj (P k l m)))
      (fun k l m => T.map (U.map (q₁ k l m))) (fun k l m => T.map (U.map (q₂ k l m))))
    (s : F.obj (op V)) (k : κ) :
    (sectionOverEquivMatchingFamilyRestrict U T hF eF hV s).val k =
      eF.hom.app (op (U.obj (W k))) (F.map (fV k).op s) :=
  rfl

end Restrict

/-! ### Stacks 09YQ in degree zero over an object the sites need not contain -/

section ColimitOverAnObject

variable {C : Type w} [SmallCategory C] {J : GrothendieckTopology C}
  (D : InverseSystemOfFiniteSites.{u₁, u₂, w}) (u : ∀ i, D.C i ⥤ C)
  (hu : ∀ {i j : D.I} (a : i ⟶ j), D.u a ⋙ u i = u j)
  (Fs : ∀ i, Sheaf (D.J i) (Type w))
  (ψ : ∀ {i j : D.I} (a : j ⟶ i), (Fs i).obj ⟶ (D.u a).op ⋙ (Fs j).obj)
  (G : Sheaf J (Type w)) (ι : ∀ i, (Fs i).obj ⟶ (u i).op ⋙ G.obj)
  (hψ : ∀ {i j k : D.I} (a : j ⟶ i) (b : k ⟶ j) (Y : D.C i) (x : (Fs i).obj.obj (op Y)),
    (ψ (b ≫ a)).app (op Y) x =
      (Fs k).obj.map (eqToHom (congrArg op (Functor.congr_obj (D.comp b a) Y).symm))
        ((ψ b).app (op ((D.u a).obj Y)) ((ψ a).app (op Y) x)))
  (hι : ∀ {i j : D.I} (a : j ⟶ i) (Y : D.C i) (x : (Fs i).obj.obj (op Y)),
    (ι i).app (op Y) x =
      G.obj.map (eqToHom (congrArg op (Functor.congr_obj (hu a) Y)))
        ((ι j).app (op ((D.u a).obj Y)) ((ψ a).app (op Y) x)))
  (hsurjObj : ∀ (i : D.I) (Y : D.C i) (z : G.obj.obj (op ((u i).obj Y))),
    ∃ (j : D.I) (a : j ⟶ i) (t : (Fs j).obj.obj (op ((D.u a).obj Y))),
      G.obj.map (eqToHom (congrArg op (Functor.congr_obj (hu a) Y)))
        ((ι j).app (op ((D.u a).obj Y)) t) = z)
  (hsep : ∀ (i : D.I) (Y : D.C i) (j : D.I) (a : j ⟶ i)
    (t t' : (Fs j).obj.obj (op ((D.u a).obj Y))),
    (ι j).app (op ((D.u a).obj Y)) t = (ι j).app (op ((D.u a).obj Y)) t' →
      ∃ (k : D.I) (b : k ⟶ j),
        (ψ b).app (op ((D.u a).obj Y)) t = (ψ b).app (op ((D.u a).obj Y)) t')
  {κ' ν' : Type} (i₀ : D.I) (W₀ : κ' → D.C i₀) (P₀ : κ' → κ' → ν' → D.C i₀)
  (q₁ : ∀ k l m, P₀ k l m ⟶ W₀ k) (q₂ : ∀ k l m, P₀ k l m ⟶ W₀ l)
  (σ : ∀ {n : D.I} (a : n ⟶ i₀),
    MatchingFamily ((D.u a).op ⋙ (Fs n).obj) W₀ P₀ q₁ q₂ →
      MatchingFamily ((u i₀).op ⋙ G.obj) W₀ P₀ q₁ q₂)
  (hσ : ∀ {n : D.I} (a : n ⟶ i₀) (t : MatchingFamily ((D.u a).op ⋙ (Fs n).obj) W₀ P₀ q₁ q₂)
    (k : κ'), (σ a t).val k =
      G.obj.map (eqToHom (congrArg op (Functor.congr_obj (hu a) (W₀ k))))
        ((ι n).app (op ((D.u a).obj (W₀ k))) (t.val k)))
  {A₀ : Type v₁} [Category.{v₂} A₀] {K₀ : GrothendieckTopology A₀} (w₀ : C ⥤ A₀)
  (G' : Sheaf K₀ (Type w)) (e₀ : w₀.op ⋙ G'.obj ≅ G.obj)
  {V : A₀} {fV : ∀ k, w₀.obj ((u i₀).obj (W₀ k)) ⟶ V}
  (hV : IsOneHypercoverOf K₀ V (fun k => w₀.obj ((u i₀).obj (W₀ k))) fV
    (fun k l m => w₀.obj ((u i₀).obj (P₀ k l m)))
    (fun k l m => w₀.map ((u i₀).map (q₁ k l m)))
    (fun k l m => w₀.map ((u i₀).map (q₂ k l m))))
  {A : D.I → Type v₃} [∀ n, Category.{v₄} (A n)] {K : ∀ n, GrothendieckTopology (A n)}
  (wn : ∀ n, D.C n ⥤ A n) (Hs : ∀ n, Sheaf (K n) (Type w))
  (en : ∀ n, (wn n).op ⋙ (Hs n).obj ≅ (Fs n).obj)
  {Vn : ∀ {n : D.I}, (n ⟶ i₀) → A n}
  {fVn : ∀ {n : D.I} (a : n ⟶ i₀) (k : κ'), (wn n).obj ((D.u a).obj (W₀ k)) ⟶ Vn a}
  (hVn : ∀ {n : D.I} (a : n ⟶ i₀), IsOneHypercoverOf (K n) (Vn a)
    (fun k => (wn n).obj ((D.u a).obj (W₀ k))) (fVn a)
    (fun k l m => (wn n).obj ((D.u a).obj (P₀ k l m)))
    (fun k l m => (wn n).map ((D.u a).map (q₁ k l m)))
    (fun k l m => (wn n).map ((D.u a).map (q₂ k l m))))

/-- **The identification of the sections of `F_n` over `V_n` with the matching families of the
datum at the level `i₀`.** `sectionOverEquivMatchingFamilyRestrict` at a level: the transition
functor `D.u a` carries the datum to the level `n`, the inclusion `wn n` carries it on to the
ambient site of that level, where it is a one-hypercover of `V_n`, and `en n` identifies the
restriction of the ambient sheaf with the sheaf of the level. -/
def levelSectionEquiv {n : D.I} (a : n ⟶ i₀) :
    (Hs n).obj.obj (op (Vn a)) ≃ MatchingFamily ((D.u a).op ⋙ (Fs n).obj) W₀ P₀ q₁ q₂ :=
  sectionOverEquivMatchingFamilyRestrict (D.u a) (wn n) (Hs n).property (en n) (hVn a)

/-- The component at `k` of the matching family attached to `t` by `levelSectionEquiv` is the
image under `en n` of the restriction of `t` along `fVn a k`. -/
@[simp]
theorem levelSectionEquiv_apply_val {n : D.I} (a : n ⟶ i₀)
    (t : (Hs n).obj.obj (op (Vn a))) (k : κ') :
    (levelSectionEquiv D Fs i₀ W₀ P₀ q₁ q₂ wn Hs en hVn a t).val k =
      (en n).hom.app (op ((D.u a).obj (W₀ k))) ((Hs n).obj.map (fVn a k).op t) :=
  rfl

/-- **The identification of the sections of `𝒢` over `V` with the matching families of the datum
at the level `i₀`.** The same construction as `levelSectionEquiv`, with the colimit site in place
of a level and `𝒢` in place of `F_n`. -/
def colimitSectionEquiv :
    G'.obj.obj (op V) ≃ MatchingFamily ((u i₀).op ⋙ G.obj) W₀ P₀ q₁ q₂ :=
  sectionOverEquivMatchingFamilyRestrict (u i₀) w₀ G'.property e₀ hV

/-- The component at `k` of the matching family attached to `s` by `colimitSectionEquiv` is the
image under `e₀` of the restriction of `s` along `fV k`. -/
@[simp]
theorem colimitSectionEquiv_apply_val (s : G'.obj.obj (op V)) (k : κ') :
    (colimitSectionEquiv D u G i₀ W₀ P₀ q₁ q₂ w₀ G' e₀ hV s).val k =
      e₀.hom.app (op ((u i₀).obj (W₀ k))) (G'.obj.map (fV k).op s) :=
  rfl

include hu σ hσ hV hVn in
/-- **The restriction map `F_n(V_n) → 𝒢(V)` exists**, and is pinned by its effect on the
restrictions to the objects of the datum: the restriction to `W₀ k` of the image of `t` is the
image under the leg `ι n` of the restriction of `t`.

This exhibits the map `ρ` of `sectionOver_colimit_of_oneHypercoverOf`, so that statement is not
vacuous. It is a hypothesis there rather than this construction for the reason recorded on
`Stacks.WeakSites.ColimitGlobalSections.globalSections_colimit_pullback_of_colimit`: a section
over `V` is determined by its restrictions rather than given by a formula, so there is no closed
form for `ρ` to be compared against, and `∀ ρ, ρ = e → Q ρ` and `Q e` are the same statement.
`hρ` does determine `ρ` uniquely, by `sectionOver_eq_of_eq_on_oneHypercoverOf`. -/
theorem exists_sectionOver_map_of_oneHypercoverOf :
    ∃ ρ : ∀ (n : D.I) (a : n ⟶ i₀), (Hs n).obj.obj (op (Vn a)) → G'.obj.obj (op V),
      ∀ (n : D.I) (a : n ⟶ i₀) (t : (Hs n).obj.obj (op (Vn a))) (k : κ'),
        e₀.hom.app (op ((u i₀).obj (W₀ k))) (G'.obj.map (fV k).op (ρ n a t)) =
          G.obj.map (eqToHom (congrArg op (Functor.congr_obj (hu a) (W₀ k))))
            ((ι n).app (op ((D.u a).obj (W₀ k)))
              ((en n).hom.app (op ((D.u a).obj (W₀ k)))
                ((Hs n).obj.map (fVn a k).op t))) := by
  refine ⟨fun n a t =>
    (colimitSectionEquiv D u G i₀ W₀ P₀ q₁ q₂ w₀ G' e₀ hV).symm
      (σ a (levelSectionEquiv D Fs i₀ W₀ P₀ q₁ q₂ wn Hs en hVn a t)), fun n a t k => ?_⟩
  rw [← colimitSectionEquiv_apply_val D u G i₀ W₀ P₀ q₁ q₂ w₀ G' e₀ hV, Equiv.apply_symm_apply,
    hσ a _ k, levelSectionEquiv_apply_val D Fs i₀ W₀ P₀ q₁ q₂ wn Hs en hVn]

include hu hψ hι hsurjObj hsep σ hσ hV hVn in
/-- **Stacks 09YQ in degree zero, over an object neither the levels nor the colimit site need
contain.** Let `(C i, J i)` be an inverse system of sites with finite coverings, let `F_i` be a
system of sheaves of sets on it and let `𝒢 = colim f_i^{-1} F_i` on the colimit site. Let `V` be
an object of an ambient site of the colimit, `V_n` objects of ambient sites of the levels, and let
a single finite datum `(W₀, P₀, q₁, q₂)` of objects of the level `i₀` be — in its image at each
level and at the colimit — a one-hypercover of `V_n` and of `V` respectively. Then the sections of
`𝒢` over `V` are the filtered colimit of the sections of the `F_n` over the `V_n`: every section
of `𝒢` over `V` is the image of a section of some `F_n` over `V_n`, and two sections of `F_n` over
`V_n` with the same image agree, on the objects of the datum, at a further level.

This is the Čech step of Stacks 09YQ in degree zero over a quasi-compact *separated* object,
which is what the Mayer-Vietoris descent of the general case needs: for a scheme `V` étale over a
level, quasi-compact and separated, a finite cover by affine opens together with finite affine
covers of the pairwise overlaps is exactly such a datum, the affine opens being objects of the
small affine étale site of the level while `V` itself is not.

Nothing is assumed about the sections over `V` or the `V_n`. The two sides are computed from the
sheaf conditions over those objects — `existsUnique_sectionOver_of_matching`, through
`levelSectionEquiv` and `colimitSectionEquiv` — and the colimit statement itself is
`Stacks.WeakSites.ColimitGlobalSections.matchingFamiliesIsColimit_of_finite`, i.e. Stacks 09YN
over the objects of the datum, transported along those two identifications. The identifications
are where the two transports of `MatchingFamily` are used: `MatchingFamily.comp` for a restricted
presheaf and `MatchingFamily.mapIso` for the equivalence of sheaf categories of Stacks 04HR,
which pins the ambient sheaf only up to a natural isomorphism.

Finiteness of the two index types is the whole of what the proof of Stacks 09YN over the objects
uses, and it is why the source needs the levels quasi-compact and quasi-separated. -/
theorem sectionOver_colimit_of_oneHypercoverOf [Finite κ'] [Finite ν']
    (ρ : ∀ (n : D.I) (a : n ⟶ i₀), (Hs n).obj.obj (op (Vn a)) → G'.obj.obj (op V))
    (hρ : ∀ (n : D.I) (a : n ⟶ i₀) (t : (Hs n).obj.obj (op (Vn a))) (k : κ'),
      e₀.hom.app (op ((u i₀).obj (W₀ k))) (G'.obj.map (fV k).op (ρ n a t)) =
        G.obj.map (eqToHom (congrArg op (Functor.congr_obj (hu a) (W₀ k))))
          ((ι n).app (op ((D.u a).obj (W₀ k)))
            ((en n).hom.app (op ((D.u a).obj (W₀ k)))
              ((Hs n).obj.map (fVn a k).op t)))) :
    (∀ s : G'.obj.obj (op V), ∃ (n : D.I) (a : n ⟶ i₀) (t : (Hs n).obj.obj (op (Vn a))),
        ρ n a t = s) ∧
      ∀ (n : D.I) (a : n ⟶ i₀) (t t' : (Hs n).obj.obj (op (Vn a))), ρ n a t = ρ n a t' →
        ∃ (m : D.I) (b : m ⟶ n), ∀ k : κ',
          (ψ b).app (op ((D.u a).obj (W₀ k)))
              ((en n).hom.app (op ((D.u a).obj (W₀ k))) ((Hs n).obj.map (fVn a k).op t)) =
            (ψ b).app (op ((D.u a).obj (W₀ k)))
              ((en n).hom.app (op ((D.u a).obj (W₀ k))) ((Hs n).obj.map (fVn a k).op t')) := by
  obtain ⟨hsurjMF, hsepMF⟩ := matchingFamiliesIsColimit_of_finite D u hu Fs ψ G ι
    hψ hι hsurjObj hsep i₀ W₀ P₀ q₁ q₂ σ hσ
  have hinj : ∀ {X : Cᵒᵖ} {z z' : (w₀.op ⋙ G'.obj).obj X},
      e₀.hom.app X z = e₀.hom.app X z' → z = z' := by
    intro X z z' hz
    have h2 : e₀.inv.app X (e₀.hom.app X z) = e₀.inv.app X (e₀.hom.app X z') := by rw [hz]
    simpa using h2
  have hkey : ∀ (n : D.I) (a : n ⟶ i₀) (t : (Hs n).obj.obj (op (Vn a))),
      σ a (levelSectionEquiv D Fs i₀ W₀ P₀ q₁ q₂ wn Hs en hVn a t) =
        colimitSectionEquiv D u G i₀ W₀ P₀ q₁ q₂ w₀ G' e₀ hV (ρ n a t) := by
    intro n a t
    ext k
    rw [hσ a _ k, colimitSectionEquiv_apply_val, hρ n a t k,
      levelSectionEquiv_apply_val D Fs i₀ W₀ P₀ q₁ q₂ wn Hs en hVn]
  refine ⟨fun s => ?_, fun n a t t' h => ?_⟩
  · obtain ⟨n, a, y, hy⟩ :=
      hsurjMF (colimitSectionEquiv D u G i₀ W₀ P₀ q₁ q₂ w₀ G' e₀ hV s)
    refine ⟨n, a, (levelSectionEquiv D Fs i₀ W₀ P₀ q₁ q₂ wn Hs en hVn a).symm y, ?_⟩
    refine sectionOver_eq_of_eq_on_oneHypercoverOf hV G'.property fun k => ?_
    refine hinj ?_
    rw [← colimitSectionEquiv_apply_val D u G i₀ W₀ P₀ q₁ q₂ w₀ G' e₀ hV,
      ← colimitSectionEquiv_apply_val D u G i₀ W₀ P₀ q₁ q₂ w₀ G' e₀ hV,
      ← hkey n a, Equiv.apply_symm_apply]
    exact congrArg (fun z => MatchingFamily.val z k) hy
  · have hfin := hsepMF n a (levelSectionEquiv D Fs i₀ W₀ P₀ q₁ q₂ wn Hs en hVn a t)
      (levelSectionEquiv D Fs i₀ W₀ P₀ q₁ q₂ wn Hs en hVn a t')
      (by
        show σ a (levelSectionEquiv D Fs i₀ W₀ P₀ q₁ q₂ wn Hs en hVn a t) =
          σ a (levelSectionEquiv D Fs i₀ W₀ P₀ q₁ q₂ wn Hs en hVn a t')
        rw [hkey n a t, hkey n a t', h])
    simpa only [levelSectionEquiv_apply_val D Fs i₀ W₀ P₀ q₁ q₂ wn Hs en hVn] using hfin

include hu hψ hι hsurjObj hsep hV hVn in
/-- **(★) for the canonical map on matching families.** `sectionOver_colimit_of_oneHypercoverOf`
with `σ` taken to be `matchingFamilyMap`, which is what a geometric consumer wants: it has the
legs `ι` and no reason to build a map on matching families of its own. -/
theorem sectionOver_colimit_of_oneHypercoverOf' [Finite κ'] [Finite ν']
    (ρ : ∀ (n : D.I) (a : n ⟶ i₀), (Hs n).obj.obj (op (Vn a)) → G'.obj.obj (op V))
    (hρ : ∀ (n : D.I) (a : n ⟶ i₀) (t : (Hs n).obj.obj (op (Vn a))) (k : κ'),
      e₀.hom.app (op ((u i₀).obj (W₀ k))) (G'.obj.map (fV k).op (ρ n a t)) =
        G.obj.map (eqToHom (congrArg op (Functor.congr_obj (hu a) (W₀ k))))
          ((ι n).app (op ((D.u a).obj (W₀ k)))
            ((en n).hom.app (op ((D.u a).obj (W₀ k)))
              ((Hs n).obj.map (fVn a k).op t)))) :
    (∀ s : G'.obj.obj (op V), ∃ (n : D.I) (a : n ⟶ i₀) (t : (Hs n).obj.obj (op (Vn a))),
        ρ n a t = s) ∧
      ∀ (n : D.I) (a : n ⟶ i₀) (t t' : (Hs n).obj.obj (op (Vn a))), ρ n a t = ρ n a t' →
        ∃ (m : D.I) (b : m ⟶ n), ∀ k : κ',
          (ψ b).app (op ((D.u a).obj (W₀ k)))
              ((en n).hom.app (op ((D.u a).obj (W₀ k))) ((Hs n).obj.map (fVn a k).op t)) =
            (ψ b).app (op ((D.u a).obj (W₀ k)))
              ((en n).hom.app (op ((D.u a).obj (W₀ k))) ((Hs n).obj.map (fVn a k).op t')) :=
  sectionOver_colimit_of_oneHypercoverOf D u hu Fs ψ G ι hψ hι hsurjObj hsep i₀ W₀ P₀ q₁ q₂
    (fun {_} a => matchingFamilyMap D u hu Fs G ι i₀ W₀ P₀ q₁ q₂ a)
    (fun a t k => matchingFamilyMap_val D u hu Fs G ι i₀ W₀ P₀ q₁ q₂ a t k)
    w₀ G' e₀ hV wn Hs en hVn ρ hρ

end ColimitOverAnObject

/-! ### Named forms of the hypotheses and of the conclusion

A geometric instantiation of `sectionOver_colimit_of_oneHypercoverOf'` cannot write these out.
On the étale system of [Stacks, Tag 0EYL]: the two object-level hypotheses written out
exhaust the elaborator's 200000 heartbeats in the *signature* of the declaration that derives
them, and the pinning hypothesis `hρ` written out does the same in the signature of the statement
that consumes it, before any proof runs. So each condition is stated once about variables, and a
concrete instance mentions it by name. Each definition is one of the hypotheses or the conclusion
above, verbatim.
-/

section Named

variable {C : Type w} [SmallCategory C] {J : GrothendieckTopology C}

/-- **Every section of `𝒢` over the image of an object of a level comes from some level below**,
named: the hypothesis `hsurjObj` of `sectionOver_colimit_of_oneHypercoverOf'`. -/
def ObjectSectionsSurjective (D : InverseSystemOfFiniteSites.{u₁, u₂, w}) (u : ∀ i, D.C i ⥤ C)
    (hu : ∀ {i j : D.I} (a : i ⟶ j), D.u a ⋙ u i = u j)
    (Fs : ∀ i, Sheaf (D.J i) (Type w)) (G : Sheaf J (Type w))
    (ι : ∀ i, (Fs i).obj ⟶ (u i).op ⋙ G.obj) : Prop :=
  ∀ (i : D.I) (Y : D.C i) (z : G.obj.obj (op ((u i).obj Y))),
    ∃ (j : D.I) (a : j ⟶ i) (t : (Fs j).obj.obj (op ((D.u a).obj Y))),
      G.obj.map (eqToHom (congrArg op (Functor.congr_obj (hu a) Y)))
        ((ι j).app (op ((D.u a).obj Y)) t) = z

/-- **Two sections of a level with the same image agree at a further level**, named: the
hypothesis `hsep` of `sectionOver_colimit_of_oneHypercoverOf'`. -/
def ObjectSectionsSeparated (D : InverseSystemOfFiniteSites.{u₁, u₂, w}) (u : ∀ i, D.C i ⥤ C)
    (Fs : ∀ i, Sheaf (D.J i) (Type w))
    (ψ : ∀ {i j : D.I} (a : j ⟶ i), (Fs i).obj ⟶ (D.u a).op ⋙ (Fs j).obj)
    (G : Sheaf J (Type w)) (ι : ∀ i, (Fs i).obj ⟶ (u i).op ⋙ G.obj) : Prop :=
  ∀ (i : D.I) (Y : D.C i) (j : D.I) (a : j ⟶ i)
    (t t' : (Fs j).obj.obj (op ((D.u a).obj Y))),
    (ι j).app (op ((D.u a).obj Y)) t = (ι j).app (op ((D.u a).obj Y)) t' →
      ∃ (k : D.I) (b : k ⟶ j),
        (ψ b).app (op ((D.u a).obj Y)) t = (ψ b).app (op ((D.u a).obj Y)) t'

/-- **The restriction map `F_n(V_n) → 𝒢(V)` is pinned by its effect on the objects of the
datum**, named: the hypothesis `hρ` of `sectionOver_colimit_of_oneHypercoverOf'`.
`exists_sectionOver_map_of_oneHypercoverOf` exhibits a map satisfying it. -/
def SectionOverMapPinned (D : InverseSystemOfFiniteSites.{u₁, u₂, w}) (u : ∀ i, D.C i ⥤ C)
    (hu : ∀ {i j : D.I} (a : i ⟶ j), D.u a ⋙ u i = u j)
    (Fs : ∀ i, Sheaf (D.J i) (Type w)) (G : Sheaf J (Type w))
    (ι : ∀ i, (Fs i).obj ⟶ (u i).op ⋙ G.obj)
    {κ' : Type} (i₀ : D.I) (W₀ : κ' → D.C i₀)
    {A₀ : Type v₁} [Category.{v₂} A₀] {K₀ : GrothendieckTopology A₀} (w₀ : C ⥤ A₀)
    (G' : Sheaf K₀ (Type w)) (e₀ : w₀.op ⋙ G'.obj ≅ G.obj) (V : A₀)
    (fV : ∀ k, w₀.obj ((u i₀).obj (W₀ k)) ⟶ V)
    {A : D.I → Type v₃} [∀ n, Category.{v₄} (A n)] {K : ∀ n, GrothendieckTopology (A n)}
    (wn : ∀ n, D.C n ⥤ A n) (Hs : ∀ n, Sheaf (K n) (Type w))
    (en : ∀ n, (wn n).op ⋙ (Hs n).obj ≅ (Fs n).obj)
    (Vn : ∀ n : D.I, (n ⟶ i₀) → A n)
    (fVn : ∀ (n : D.I) (a : n ⟶ i₀) (k : κ'), (wn n).obj ((D.u a).obj (W₀ k)) ⟶ Vn n a)
    (ρ : ∀ (n : D.I) (a : n ⟶ i₀), (Hs n).obj.obj (op (Vn n a)) → G'.obj.obj (op V)) : Prop :=
  ∀ (n : D.I) (a : n ⟶ i₀) (t : (Hs n).obj.obj (op (Vn n a))) (k : κ'),
    e₀.hom.app (op ((u i₀).obj (W₀ k))) (G'.obj.map (fV k).op (ρ n a t)) =
      G.obj.map (eqToHom (congrArg op (Functor.congr_obj (hu a) (W₀ k))))
        ((ι n).app (op ((D.u a).obj (W₀ k)))
          ((en n).hom.app (op ((D.u a).obj (W₀ k))) ((Hs n).obj.map (fVn n a k).op t)))

/-- **The sections over `V` are the filtered colimit of the sections over the `V_n`**, named: the
conclusion of `sectionOver_colimit_of_oneHypercoverOf'`. -/
def SectionOverIsColimit (D : InverseSystemOfFiniteSites.{u₁, u₂, w}) (_u : ∀ i, D.C i ⥤ C)
    (Fs : ∀ i, Sheaf (D.J i) (Type w))
    (ψ : ∀ {i j : D.I} (a : j ⟶ i), (Fs i).obj ⟶ (D.u a).op ⋙ (Fs j).obj)
    {κ' : Type} (i₀ : D.I) (W₀ : κ' → D.C i₀)
    {A₀ : Type v₁} [Category.{v₂} A₀] {K₀ : GrothendieckTopology A₀}
    (G' : Sheaf K₀ (Type w)) (V : A₀)
    {A : D.I → Type v₃} [∀ n, Category.{v₄} (A n)] {K : ∀ n, GrothendieckTopology (A n)}
    (wn : ∀ n, D.C n ⥤ A n) (Hs : ∀ n, Sheaf (K n) (Type w))
    (en : ∀ n, (wn n).op ⋙ (Hs n).obj ≅ (Fs n).obj)
    (Vn : ∀ n : D.I, (n ⟶ i₀) → A n)
    (fVn : ∀ (n : D.I) (a : n ⟶ i₀) (k : κ'), (wn n).obj ((D.u a).obj (W₀ k)) ⟶ Vn n a)
    (ρ : ∀ (n : D.I) (a : n ⟶ i₀), (Hs n).obj.obj (op (Vn n a)) → G'.obj.obj (op V)) : Prop :=
  (∀ s : G'.obj.obj (op V), ∃ (n : D.I) (a : n ⟶ i₀) (t : (Hs n).obj.obj (op (Vn n a))),
      ρ n a t = s) ∧
    ∀ (n : D.I) (a : n ⟶ i₀) (t t' : (Hs n).obj.obj (op (Vn n a))), ρ n a t = ρ n a t' →
      ∃ (m : D.I) (b : m ⟶ n), ∀ k : κ',
        (ψ b).app (op ((D.u a).obj (W₀ k)))
            ((en n).hom.app (op ((D.u a).obj (W₀ k))) ((Hs n).obj.map (fVn n a k).op t)) =
          (ψ b).app (op ((D.u a).obj (W₀ k)))
            ((en n).hom.app (op ((D.u a).obj (W₀ k))) ((Hs n).obj.map (fVn n a k).op t'))

end Named

end Stacks.WeakSites.ColimitGlobalSections

end
