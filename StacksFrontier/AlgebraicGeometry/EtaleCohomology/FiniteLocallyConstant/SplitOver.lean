module

public import Mathlib.AlgebraicGeometry.Sites.MorphismProperty
public import StacksFrontier.AlgebraicGeometry.Etale.FiniteEtaleLocal

/-!
# Sheets of a morphism which is a trivial covering over a base

Let `f : X ⟶ S` be a morphism of schemes and let `q : V ⟶ S` be a scheme over `S`. Saying
that `X ×_S V` is a finite disjoint union of copies of `V` can be repackaged as data about
the `V`-points of `X`: finitely many *sheets* `V ⟶ X` over `S` such that every `V`-point of
`X` factors through a sheet locally on its source, and such that two distinct sheets never
agree on a nonempty scheme.

This repackaging is what the sheaf-theoretic argument consumes, and unlike the isomorphism
`X ×_S V ≅ ∐ V` it is trivially stable under base change `V' ⟶ V`: the sheets are composed
with the base change, the factorizations are pulled back along it, and no compatibility of
coproducts with fibre products is needed.

## Main definitions

* `Stacks.Etale.IsSplitOver` — the sheet data described above.

## Main results

* `Stacks.Etale.IsSplitOver.comp` — sheet data base changes along any `V' ⟶ V`.
* `Stacks.Etale.isSplitOverOfIso` — an isomorphism `X ×_S V ≅ ∐_{i : ι} V` over `V` gives
  sheet data; the sheets are the images of the components of the coproduct.
* `Stacks.Etale.exists_isSplitOver` — **Stacks 04HN** in this language: a finite étale `f`
  has sheet data over an étale neighbourhood of any point of any `S`-scheme `V`.

## References

* [Stacks Project, Tag 04HN](https://stacks.math.columbia.edu/tag/04HN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.Etale

/-- **Sheet data** for `f : X ⟶ S` over an `S`-scheme `q : V ⟶ S`: finitely many sections
`V ⟶ X` of `f` over `S` through which every `V`-point of `X` factors locally on its source,
and which are pairwise disjoint in the strong sense that two distinct sheets agree only on an
empty scheme. This is the content of `X ×_S V ≅ ∐_{i : ι} V` that survives base change. -/
public structure IsSplitOver {X S : Scheme.{u}} (f : X ⟶ S) {V : Scheme.{u}} (q : V ⟶ S) where
  /-- The index type of the sheets. -/
  I : Type u
  /-- There are finitely many sheets. -/
  finite_I : Finite I
  /-- The sheets. -/
  sheet : I → (V ⟶ X)
  /-- Each sheet is a section of `f` over `S`. -/
  sheet_comp : ∀ i, sheet i ≫ f = q
  /-- Every `V`-point of `X` agrees with a sheet on each member of an open covering of its
  source. -/
  exists_openCover : ∀ {Z : Scheme.{u}} (z : Z ⟶ V) (b : Z ⟶ X), b ≫ f = z ≫ q →
    ∃ (κ : Type u) (Y : κ → Scheme.{u}) (p : ∀ k, Y k ⟶ Z) (_ : ∀ k, IsOpenImmersion (p k))
      (i : κ → I), (∀ x : Z, ∃ k, x ∈ Set.range (p k)) ∧
        ∀ k, p k ≫ b = p k ≫ z ≫ sheet (i k)
  /-- Two distinct sheets agree only on an empty scheme. -/
  isEmpty_of_sheet_eq : ∀ {Z : Scheme.{u}} (z : Z ⟶ V) {i j : I}, i ≠ j →
    z ≫ sheet i = z ≫ sheet j → IsEmpty Z

namespace IsSplitOver

/-- Sheet data base changes along an arbitrary morphism of the base: the sheets of `f` over
`V' ⟶ V ⟶ S` are the composites of `V' ⟶ V` with the sheets over `V`. -/
public def comp {X S V V' : Scheme.{u}} {f : X ⟶ S} {q : V ⟶ S} (h : IsSplitOver f q)
    (g : V' ⟶ V) : IsSplitOver f (g ≫ q) where
  I := h.I
  finite_I := h.finite_I
  sheet i := g ≫ h.sheet i
  sheet_comp i := by rw [Category.assoc, h.sheet_comp]
  exists_openCover := by
    intro Z z b hb
    obtain ⟨κ, Y, p, hp, i, hcov, hfac⟩ :=
      h.exists_openCover (z ≫ g) b (by rw [hb, Category.assoc])
    exact ⟨κ, Y, p, hp, i, hcov, fun k ↦ by simpa only [Category.assoc] using hfac k⟩
  isEmpty_of_sheet_eq := by
    intro Z z i j hij hz
    exact h.isEmpty_of_sheet_eq (z ≫ g) hij (by simpa only [Category.assoc] using hz)

end IsSplitOver

section OfSplitCover

variable {X S V : Scheme.{u}} (f : X ⟶ S) (q : V ⟶ S) {ι : Type u}
  (e : pullback f q ≅ ∐ fun _ : ι ↦ V)
  (he : e.hom ≫ Limits.Sigma.desc (fun _ ↦ 𝟙 V) = pullback.snd f q)

/-- The sheet attached to a component of a trivialization `X ×_S V ≅ ∐_{i : ι} V`. -/
public def sheetOfIso (i : ι) : V ⟶ X :=
  Sigma.ι (fun _ : ι ↦ V) i ≫ e.inv ≫ pullback.fst f q

include he in
/-- A component of the coproduct, followed by the trivialization, is a section of the
projection to the base. -/
public theorem ι_inv_comp_snd (i : ι) :
    Sigma.ι (fun _ : ι ↦ V) i ≫ e.inv ≫ pullback.snd f q = 𝟙 V := by
  rw [← he, Iso.inv_hom_id_assoc, Sigma.ι_comp_desc]

include he in
/-- Each sheet of a trivialization is a section of `f` over `S`. -/
public theorem sheetOfIso_comp (i : ι) : sheetOfIso f q e i ≫ f = q := by
  calc sheetOfIso f q e i ≫ f
      = Sigma.ι (fun _ : ι ↦ V) i ≫ e.inv ≫ pullback.fst f q ≫ f := by
        simp only [sheetOfIso, Category.assoc]
    _ = (Sigma.ι (fun _ : ι ↦ V) i ≫ e.inv ≫ pullback.snd f q) ≫ q := by
        simp only [pullback.condition, Category.assoc]
    _ = q := by rw [ι_inv_comp_snd f q e he i, Category.id_comp]

include he in
/-- An isomorphism `X ×_S V ≅ ∐_{i : ι} V` over `V` is sheet data: the sheets are the images
of the components of the coproduct, every `V`-point of `X` lies on one of them over each
member of the open covering of its source pulled back from the coproduct, and distinct
components have disjoint images. -/
public def isSplitOverOfIso [Finite ι] : IsSplitOver f q where
  I := ι
  finite_I := ‹Finite ι›
  sheet := sheetOfIso f q e
  sheet_comp := sheetOfIso_comp f q e he
  exists_openCover := by
    intro Z z b hb
    set c : Z ⟶ pullback f q := pullback.lift b z hb with hc
    have hcb : c ≫ pullback.fst f q = b := pullback.lift_fst b z hb
    have hcz : c ≫ pullback.snd f q = z := pullback.lift_snd b z hb
    refine ⟨ι, fun k ↦ pullback (c ≫ e.hom) (Sigma.ι (fun _ : ι ↦ V) k),
      fun k ↦ pullback.fst _ _, fun k ↦ inferInstance, id, fun x ↦ ?_, fun k ↦ ?_⟩
    · obtain ⟨k, y, hy⟩ := (sigmaOpenCover (fun _ : ι ↦ V)).exists_eq ((c ≫ e.hom) x)
      exact ⟨k, Scheme.IsJointlySurjectivePreserving.exists_preimage_fst_triplet_of_prop
        (P := @IsOpenImmersion) (g := Sigma.ι (fun _ : ι ↦ V) k) inferInstance x y hy.symm⟩
    · change pullback.fst (c ≫ e.hom) (Sigma.ι (fun _ : ι ↦ V) k) ≫ b =
        pullback.fst (c ≫ e.hom) (Sigma.ι (fun _ : ι ↦ V) k) ≫ z ≫ sheetOfIso f q e k
      have hfac : pullback.fst (c ≫ e.hom) (Sigma.ι (fun _ : ι ↦ V) k) ≫ c =
          pullback.snd (c ≫ e.hom) (Sigma.ι (fun _ : ι ↦ V) k) ≫
            Sigma.ι (fun _ : ι ↦ V) k ≫ e.inv := by
        rw [← Category.assoc, ← pullback.condition]
        simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
      have hz' : pullback.fst (c ≫ e.hom) (Sigma.ι (fun _ : ι ↦ V) k) ≫ z =
          pullback.snd (c ≫ e.hom) (Sigma.ι (fun _ : ι ↦ V) k) := by
        rw [← hcz, ← Category.assoc, hfac]
        simp only [Category.assoc]
        rw [ι_inv_comp_snd f q e he k, Category.comp_id]
      rw [← Category.assoc, hz', ← hcb, ← Category.assoc, hfac]
      simp only [sheetOfIso, Category.assoc]
  isEmpty_of_sheet_eq := by
    intro Z z i j hij hz
    have h₁ : z ≫ Sigma.ι (fun _ : ι ↦ V) i ≫ e.inv =
        z ≫ Sigma.ι (fun _ : ι ↦ V) j ≫ e.inv := by
      refine pullback.hom_ext ?_ ?_
      · simp only [Category.assoc]
        exact hz
      · simp only [Category.assoc]
        rw [ι_inv_comp_snd f q e he i, ι_inv_comp_snd f q e he j]
    have h₂ : z ≫ Sigma.ι (fun _ : ι ↦ V) i = z ≫ Sigma.ι (fun _ : ι ↦ V) j := by
      rw [← cancel_mono e.inv, Category.assoc, Category.assoc, h₁]
    exact isEmpty_of_commSq_sigmaι_of_ne ⟨h₂⟩ hij

end OfSplitCover

/-- Sheet data from a split covering: unpacking `Stacks.Etale.IsSplitCover` gives a
trivialization of `X ×_S V` over `V`, hence sheets. -/
public def isSplitOverOfIsSplitCover {X S V : Scheme.{u}} (f : X ⟶ S) (q : V ⟶ S)
    (h : IsSplitCover (pullback.snd f q)) : IsSplitOver f q :=
  have : Finite h.choose := h.choose_spec.choose
  isSplitOverOfIso f q h.choose_spec.choose_spec.choose
    h.choose_spec.choose_spec.choose_spec

/-- **Stacks 04HN**, in terms of sheets. Let `f : X ⟶ S` be finite étale and let `q : V ⟶ S`
be any scheme over `S`. Every point of `V` has an étale neighbourhood `g : W ⟶ V` over which
`f` has sheet data. -/
@[stacks 04HN "sheets over an étale neighbourhood"]
public theorem exists_isSplitOver {X S : Scheme.{u}} (f : X ⟶ S) [IsFinite f] [Etale f]
    {V : Scheme.{u}} (q : V ⟶ S) (v : V) :
    ∃ (W : Scheme.{u}) (g : W ⟶ V) (_ : Etale g) (w : W) (_ : g w = v),
      Nonempty (IsSplitOver f (g ≫ q)) := by
  obtain ⟨W, g, hg, w, hw, hsplit⟩ := exists_etale_isSplitCover (pullback.snd f q) v
  exact ⟨W, g, hg, w, hw,
    ⟨isSplitOverOfIsSplitCover f (g ≫ q) ((isSplitCover_pullback_snd_comp f q g).mp hsplit)⟩⟩

end Stacks.Etale
