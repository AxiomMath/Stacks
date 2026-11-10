module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.SplitOver
public import StacksFrontier.AlgebraicGeometry.Spaces.FieldPointGaloisDescent

/-!
# Sheets as a clopen decomposition of the base change

Let `p : P ⟶ S` be a morphism with sheet data over an `S`-scheme `g : N ⟶ S`, and let
`a : T ⟶ P`, `b : T ⟶ N` exhibit `T` as the base change `P ×_S N`. Each sheet `N ⟶ P` lifts
uniquely to a section of `b`, which is an open immersion when `p` is étale. For `p` étale the
ranges of those sections decompose `T` into finitely many pairwise disjoint opens, each mapping
isomorphically to `N`. A finite étale morphism has sheet data over a quasi-compact étale
neighbourhood of any point of the base.

## Main definitions

* `Stacks.Etale.IsSplitOver.sectionOfIsPullback` — the section of `b` attached to a sheet.

## Main results

* `Stacks.Etale.IsSplitOver.isOpenImmersion_sectionOfIsPullback` — that section is an open
  immersion when `p` is étale.
* `Stacks.Etale.IsSplitOver.exists_disjoint_opens_of_isPullback` — the decomposition of the base
  change into pairwise disjoint opens, each carried isomorphically onto the base.
* `Stacks.Etale.exists_compactSpace_etale_isSplitOver` — a finite étale morphism has sheet data
  over a quasi-compact étale neighbourhood of any point of the base.

## References

* [Stacks Project, Tag 04HN](https://stacks.math.columbia.edu/tag/04HN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.Etale

namespace IsSplitOver

variable {P S N T : Scheme.{u}} {p : P ⟶ S} {g : N ⟶ S} {a : T ⟶ P} {b : T ⟶ N}

/-- The section of the base change `b : T ⟶ N` determined by a sheet: the morphism `N ⟶ T`
induced by the sheet `N ⟶ P` and `𝟙 N`. -/
public def sectionOfIsPullback (h : IsSplitOver p g) (hab : IsPullback a b p g) (i : h.I) :
    N ⟶ T :=
  hab.lift (h.sheet i) (𝟙 N) (by rw [h.sheet_comp, Category.id_comp])

/-- The section attached to a sheet, followed by `a : T ⟶ P`, is the sheet. -/
@[simp]
public theorem sectionOfIsPullback_comp_fst (h : IsSplitOver p g) (hab : IsPullback a b p g)
    (i : h.I) : h.sectionOfIsPullback hab i ≫ a = h.sheet i :=
  hab.lift_fst _ _ _

/-- The section attached to a sheet is a section of `b : T ⟶ N`. -/
@[simp]
public theorem sectionOfIsPullback_comp_snd (h : IsSplitOver p g) (hab : IsPullback a b p g)
    (i : h.I) : h.sectionOfIsPullback hab i ≫ b = 𝟙 N :=
  hab.lift_snd _ _ _

/-- The base change of an étale morphism along the second projection is étale. -/
public theorem etale_snd_of_isPullback [Etale p] (hab : IsPullback a b p g) : Etale b :=
  MorphismProperty.of_isPullback hab inferInstance

/-- The section attached to a sheet is an open immersion when `p` is étale. -/
public theorem isOpenImmersion_sectionOfIsPullback [Etale p] (h : IsSplitOver p g)
    (hab : IsPullback a b p g) (i : h.I) :
    IsOpenImmersion (h.sectionOfIsPullback hab i) :=
  have := etale_snd_of_isPullback hab
  AlgebraicGeometry.isOpenImmersion_of_section_of_etale b (h.sectionOfIsPullback hab i)
    (h.sectionOfIsPullback_comp_snd hab i)

/-- Every point of the base change lies in the range of the section attached to some sheet. -/
public theorem exists_mem_range_sectionOfIsPullback (h : IsSplitOver p g)
    (hab : IsPullback a b p g) (x : T) :
    ∃ i, x ∈ Set.range (h.sectionOfIsPullback hab i) := by
  obtain ⟨κ, Y, pr, hpr, idx, hcov, hfac⟩ := h.exists_openCover b a hab.w
  obtain ⟨k, y, hy⟩ := hcov x
  have hk : pr k = pr k ≫ b ≫ h.sectionOfIsPullback hab (idx k) := by
    refine hab.hom_ext ?_ ?_
    · rw [Category.assoc, Category.assoc, sectionOfIsPullback_comp_fst]
      exact hfac k
    · rw [Category.assoc, Category.assoc, sectionOfIsPullback_comp_snd, Category.comp_id]
  refine ⟨idx k, (pr k ≫ b) y, ?_⟩
  calc h.sectionOfIsPullback hab (idx k) ((pr k ≫ b) y)
      = (pr k ≫ b ≫ h.sectionOfIsPullback hab (idx k)) y := by
        simp only [Scheme.Hom.comp_apply]
    _ = (pr k) y := by rw [← hk]
    _ = x := hy

/-- A scheme `Z` with a morphism to `T` which factors through the sections attached to two
distinct sheets is empty. -/
public theorem isEmpty_of_mem_two_sections (h : IsSplitOver p g) (hab : IsPullback a b p g)
    {i j : h.I} (hij : i ≠ j) {Z : Scheme.{u}} (z : Z ⟶ T)
    (ci : Z ⟶ N) (hci : ci ≫ h.sectionOfIsPullback hab i = z)
    (cj : Z ⟶ N) (hcj : cj ≫ h.sectionOfIsPullback hab j = z) : IsEmpty Z := by
  have key (k : h.I) (c : Z ⟶ N) (hc : c ≫ h.sectionOfIsPullback hab k = z) :
      (z ≫ b) ≫ h.sheet k = z ≫ a := by
    have hcb : c = z ≫ b := by
      rw [← hc, Category.assoc, sectionOfIsPullback_comp_snd, Category.comp_id]
    rw [← hcb, ← sectionOfIsPullback_comp_fst h hab k, ← Category.assoc, hc]
  exact h.isEmpty_of_sheet_eq (z ≫ b) hij ((key i ci hci).trans (key j cj hcj).symm)

/-- Sheet data decomposes the base change into finitely many pairwise disjoint open subschemes,
each of which is carried isomorphically onto the base by the second projection. -/
public theorem exists_disjoint_opens_of_isPullback [Etale p] (h : IsSplitOver p g)
    (hab : IsPullback a b p g) :
    ∃ (ι : Type u) (_ : Finite ι) (W : ι → T.Opens),
      iSup W = ⊤ ∧ Pairwise (fun i j => Disjoint (W i) (W j)) ∧
        ∀ i, IsIso ((W i).ι ≫ b) := by
  let (i : h.I) := isOpenImmersion_sectionOfIsPullback h hab i
  refine ⟨h.I, h.finite_I, fun i ↦ (h.sectionOfIsPullback hab i).opensRange, ?_, ?_, ?_⟩
  · exact eq_top_iff.2 fun x _ ↦
      TopologicalSpace.Opens.mem_iSup.mpr (exists_mem_range_sectionOfIsPullback h hab x)
  · intro i j hij
    set V : T.Opens := (h.sectionOfIsPullback hab i).opensRange ⊓
      (h.sectionOfIsPullback hab j).opensRange with hV
    have hsub (k : h.I) (hle : V ≤ (h.sectionOfIsPullback hab k).opensRange) :
        Set.range V.ι.base ⊆ Set.range (h.sectionOfIsPullback hab k).base := by
      rwa [Scheme.Opens.range_ι]
    have hempty := isEmpty_of_mem_two_sections h hab hij V.ι
      (IsOpenImmersion.lift _ _ (hsub i inf_le_left))
      (IsOpenImmersion.lift_fac _ _ (hsub i inf_le_left))
      (IsOpenImmersion.lift _ _ (hsub j inf_le_right))
      (IsOpenImmersion.lift_fac _ _ (hsub j inf_le_right))
    rw [disjoint_iff, ← hV, eq_bot_iff]
    exact fun x hx ↦ (hempty.false ⟨x, hx⟩).elim
  · intro i
    have hk : (h.sectionOfIsPullback hab i).opensRange.ι ≫ b =
        (h.sectionOfIsPullback hab i).isoOpensRange.inv := by
      rw [← cancel_epi (h.sectionOfIsPullback hab i).isoOpensRange.hom, Iso.hom_inv_id,
        ← Category.assoc, Scheme.Hom.isoOpensRange_hom_ι, sectionOfIsPullback_comp_snd]
    rw [hk]
    infer_instance

end IsSplitOver

/-- A finite étale morphism has sheet data over an étale neighbourhood of any point of the base
whose underlying scheme is quasi-compact. -/
public theorem exists_compactSpace_etale_isSplitOver {X S : Scheme.{u}} (f : X ⟶ S)
    [IsFinite f] [Etale f] (s : S) :
    ∃ (N : Scheme.{u}) (g : N ⟶ S) (_ : Etale g) (_ : CompactSpace N) (n : N) (_ : g n = s),
      Nonempty (IsSplitOver f g) := by
  obtain ⟨W, g, hg, w, hw, ⟨hsp⟩⟩ := exists_isSplitOver f (𝟙 S) s
  rw [Category.comp_id] at hsp
  obtain ⟨i, y, hy⟩ := W.affineOpenCover.openCover.exists_eq w
  have : IsAffine (W.affineOpenCover.openCover.X i) := Scheme.isAffine_affineCover W i
  have : CompactSpace (W.affineOpenCover.openCover.X i) := Scheme.compactSpace_of_isAffine _
  have : IsOpenImmersion (W.affineOpenCover.openCover.f i) :=
    W.affineOpenCover.openCover.map_prop i
  refine ⟨W.affineOpenCover.openCover.X i, W.affineOpenCover.openCover.f i ≫ g,
    inferInstance, inferInstance, y, ?_, ⟨hsp.comp _⟩⟩
  change g (W.affineOpenCover.openCover.f i y) = s
  rw [hy, hw]

end Stacks.Etale

end
