module

public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.DimensionLayerCycleFromCycles

/-!
# A locally finite direct sum is one summand near a point

A direct sum `⨁_{j} F_j` of `𝒪_X`-modules whose supports form a locally finite family of closed
sets can be read, near a point `x` lying in only one of those supports, as that single summand:
the inclusion `F_{j₀} ⟶ ⨁_j F_j` becomes an isomorphism after restriction to a small enough open
neighbourhood of `x`. This is the only way a statement about an infinite direct sum of coherent
modules gets tested at a point, and it is what replaces, in the non-quasi-compact case, the
finite induction a Noetherian scheme would allow.

The two ingredients are elementary. All summands other than `F_{j₀}` restrict to zero on a
neighbourhood of `x`, by local finiteness and the closedness of the supports; and the inclusion
of one summand of a coproduct all of whose other summands are zero objects is an isomorphism.

## Main results

* `Stacks.Chow.coproductSigmaIso` — the direct sum over a sigma type is the direct sum of the
  direct sums over the fibres.
* `Stacks.Chow.isIso_sigmaι_of_isZero` — the inclusion of one summand of a coproduct is an
  isomorphism as soon as every other summand is a zero object.
* `Stacks.Chow.exists_isIso_restrict_sigmaι` — **a locally finite direct sum is one summand near
  a point**: the inclusion of the summand indexed by `j₀` is invertible after restriction to
  some open neighbourhood of a point lying outside the supports of all the others.

## Implementation notes

The inverse of the inclusion of one summand is `Sigma.desc` of the family that is the identity at
`j₀` — through the `eqToHom` of the index equation, since the family is total — and zero
elsewhere. The index type therefore has to carry decidable equality, which is supplied
classically at each use.

The neighbourhood is produced by removing, from a neighbourhood meeting only finitely many of the
supports, the finitely many of those supports that do not contain the point. That the result is
open is where the supports being closed enters; a coherent module on a locally Noetherian scheme
has closed support, but the statement takes the closed sets as data so that the coarser bound
`supp F_j ⊆ closure {j}` can be used instead.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### Invertibility of a composite under a functor -/

/-- A functor carries a composite of two morphisms it makes invertible to an invertible
morphism. Stated for an abstract functor so that no definition of the category of modules on a
scheme has to be unfolded. -/
theorem isIso_map_comp {D E : Type*} [Category D] [Category E] (F : D ⥤ E) {A B G : D}
    (g : A ⟶ B) (h : B ⟶ G) (hg : IsIso (F.map g)) (hh : IsIso (F.map h)) :
    IsIso (F.map (g ≫ h)) := by
  rw [F.map_comp]
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ hg hh

/-- If a functor makes a morphism `g` and a composite `g ≫ h` invertible, it makes `h`
invertible. -/
theorem isIso_map_of_comp {D E : Type*} [Category D] [Category E] (F : D ⥤ E) {A B G : D}
    (g : A ⟶ B) (h : B ⟶ G) (c : A ⟶ G) (hc : g ≫ h = c) (hg : IsIso (F.map g))
    (hcc : IsIso (F.map c)) : IsIso (F.map h) := by
  subst hc
  rw [F.map_comp] at hcc
  exact @IsIso.of_isIso_comp_left _ _ _ _ _ _ _ hg hcc

/-! ### Coproducts over a sigma type -/

/-- **The direct sum over a sigma type is the direct sum of the direct sums over the fibres.** -/
def coproductSigmaIso {D : Type*} [Category D] {J : Type*} {K : J → Type*}
    (F : (Σ j, K j) → D) [HasCoproduct F] [∀ j, HasCoproduct fun a : K j ↦ F ⟨j, a⟩]
    [HasCoproduct fun j ↦ ∐ fun a : K j ↦ F ⟨j, a⟩] :
    (∐ fun j ↦ ∐ fun a : K j ↦ F ⟨j, a⟩) ≅ ∐ F where
  hom := Sigma.desc fun j ↦ Sigma.desc fun a ↦ Sigma.ι F ⟨j, a⟩
  inv := Sigma.desc fun p ↦
    Sigma.ι (fun a : K p.1 ↦ F ⟨p.1, a⟩) p.2 ≫ Sigma.ι (fun j ↦ ∐ fun a : K j ↦ F ⟨j, a⟩) p.1
  hom_inv_id := by
    refine Sigma.hom_ext _ _ fun j ↦ Sigma.hom_ext _ _ fun a ↦ ?_
    simp
  inv_hom_id := by
    refine Sigma.hom_ext _ _ fun p ↦ ?_
    simp

/-! ### The support of a finite direct sum -/

/-- **The support of a finite direct sum of `𝒪_X`-modules is contained in the union of the
supports of the summands.** This is `Stacks.Chow.supp_sigma_subset_iUnion_supp` for an index type
which is finite rather than of the scheme's own universe. -/
theorem supp_coproduct_subset_of_finite {X : Scheme.{u}} {J : Type*} [Finite J]
    (F : J → X.Modules) :
    SheafOfModules.supp (∐ F) ⊆ ⋃ j, SheafOfModules.supp (F j) := by
  intro x hx
  by_contra hn
  have hz : ∀ j, IsZero ((SheafOfModules.stalkFunctor X.ringCatSheaf x).obj (F j)) := by
    intro j
    refine ModuleCat.isZero_iff_subsingleton.mpr ⟨fun a b ↦ ?_⟩
    have hj : x ∉ SheafOfModules.supp (F j) := fun h ↦ hn (Set.mem_iUnion.2 ⟨j, h⟩)
    have h0 : ∀ a : (SheafOfModules.stalkFunctor X.ringCatSheaf x).obj (F j), a = 0 := fun a ↦ by
      by_contra ha
      exact hj ⟨a, ha⟩
    exact (h0 a).trans (h0 b).symm
  have hzero : IsZero (∐ fun j ↦ (SheafOfModules.stalkFunctor X.ringCatSheaf x).obj (F j)) :=
    (IsZero.iff_id_eq_zero _).2 (Sigma.hom_ext _ _ fun j ↦ (hz j).eq_of_src _ _)
  have hs := (PreservesCoproduct.iso (SheafOfModules.stalkFunctor X.ringCatSheaf x) F).isZero_iff
  obtain ⟨a, ha⟩ := hx
  exact ha ((ModuleCat.isZero_iff_subsingleton.mp (hs.mpr hzero)).elim _ _)

/-! ### One summand of a coproduct of zero objects -/

/-- **The inclusion of one summand of a coproduct is an isomorphism** as soon as every other
summand is a zero object. -/
theorem isIso_sigmaι_of_isZero {D : Type*} [Category D] [HasZeroMorphisms D] {J : Type*}
    (F : J → D) [HasCoproduct F] (j₀ : J)
    (h : ∀ j, j ≠ j₀ → IsZero (F j)) : IsIso (Sigma.ι F j₀) := by
  classical
  refine ⟨Sigma.desc fun j ↦ if hj : j = j₀ then eqToHom (congrArg F hj) else 0, ?_, ?_⟩
  · simp
  · refine Sigma.hom_ext _ _ fun j ↦ ?_
    by_cases hj : j = j₀
    · subst hj
      simp
    · simp only [Sigma.ι_desc_assoc, hj, ↓reduceDIte, zero_comp, Category.comp_id]
      exact ((h j hj).eq_of_src _ _).symm

/-! ### A locally finite direct sum near a point -/

/-- An open neighbourhood of `x` meeting none of the sets `Zc j` for `j ≠ j₀`: a neighbourhood
meeting only finitely many of them, with the finitely many that do not contain `x` removed. -/
private theorem exists_isOpen_disjoint_of_locallyFinite {X : Type*} [TopologicalSpace X]
    {J : Type*} (Zc : J → Set X) (hclosed : ∀ j, IsClosed (Zc j)) (hLF : LocallyFinite Zc)
    (x : X) (j₀ : J) (hx : ∀ j, j ≠ j₀ → x ∉ Zc j) :
    ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ ∀ j, j ≠ j₀ → Disjoint V (Zc j) := by
  classical
  obtain ⟨W, hW, hfin⟩ := hLF x
  obtain ⟨W₀, hW₀W, hW₀, hxW₀⟩ := mem_nhds_iff.mp hW
  set T : Finset J := hfin.toFinset with hT
  set E : Set X := ⋃ j ∈ (T.erase j₀ : Finset J), Zc j with hE
  have hEclosed : IsClosed E :=
    Set.Finite.isClosed_biUnion (T.erase j₀).finite_toSet fun j _ ↦ hclosed j
  refine ⟨W₀ \ E, hW₀.sdiff hEclosed, ⟨hxW₀, ?_⟩, ?_⟩
  · intro hmem
    obtain ⟨j, hjT, hj⟩ := Set.mem_iUnion₂.mp hmem
    exact hx j (Finset.ne_of_mem_erase hjT) hj
  · intro j hj
    refine Set.disjoint_left.mpr fun y hy hyZ ↦ ?_
    have hyW₀ : y ∈ W₀ := hy.1
    have hyE : y ∉ E := hy.2
    by_cases hjT : j ∈ T
    · exact hyE (Set.mem_biUnion (Finset.mem_erase.2 ⟨hj, hjT⟩) hyZ)
    · exact hjT (hfin.mem_toFinset.mpr ⟨y, hyZ, hW₀W hyW₀⟩)

/-- **A locally finite direct sum is one summand near a point.** Let `F` be a family of
`𝒪_X`-modules whose supports are contained in a locally finite family of closed sets, and let `x`
be a point lying in none of those sets except possibly the one indexed by `j₀`. Then the
inclusion of the `j₀`-th summand into `⨁_j F_j` is an isomorphism after restriction to some open
neighbourhood of `x`. -/
theorem exists_isIso_restrict_sigmaι {X : Scheme.{u}} {J : Type u} (F : J → X.Modules)
    (Zc : J → Set X) (hsupp : ∀ j, SheafOfModules.supp (F j) ⊆ Zc j)
    (hclosed : ∀ j, IsClosed (Zc j)) (hLF : LocallyFinite Zc) (x : X) (j₀ : J)
    (hx : ∀ j, j ≠ j₀ → x ∉ Zc j) :
    ∃ V : X.Opens, x ∈ V ∧
      IsIso ((Scheme.Modules.restrictFunctor V.ι).map (Sigma.ι F j₀)) := by
  classical
  obtain ⟨V₀, hV₀, hxV, hdisj₀⟩ := exists_isOpen_disjoint_of_locallyFinite Zc hclosed hLF x j₀ hx
  set V : X.Opens := ⟨V₀, hV₀⟩ with hVdef
  have hdisj : ∀ j, j ≠ j₀ → Disjoint (V : Set X) (Zc j) := hdisj₀
  refine ⟨V, hxV, ?_⟩
  have hzero : ∀ j, j ≠ j₀ →
      IsZero ((Scheme.Modules.restrictFunctor V.ι).obj (F j)) := fun j hj ↦
    isZero_restrictFunctor_obj_of_disjoint_supp (F j) V ((hdisj j hj).mono_right (hsupp j))
  have hι : IsIso (Sigma.ι (fun j ↦ (Scheme.Modules.restrictFunctor V.ι).obj (F j)) j₀) :=
    isIso_sigmaι_of_isZero _ j₀ hzero
  have heq : (Scheme.Modules.restrictFunctor V.ι).map (Sigma.ι F j₀) =
      Sigma.ι (fun j ↦ (Scheme.Modules.restrictFunctor V.ι).obj (F j)) j₀ ≫
        sigmaComparison (Scheme.Modules.restrictFunctor V.ι) F :=
    (ι_comp_sigmaComparison (Scheme.Modules.restrictFunctor V.ι) F j₀).symm
  rw [heq]
  exact IsIso.comp_isIso' hι inferInstance

end Stacks.Chow

end
