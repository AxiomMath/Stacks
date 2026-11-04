module

public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.CategoryTheory.CofilteredSystem
public import StacksFrontier.Algebra.Homology.InverseLimit
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.WholeSpaceEnvelope

/-!
# The inverse limit over the `p`-adic levels, and [Stacks, Tag 07LF] from the level-wise
identification alone

The proof of [Stacks, Tag 07LF] in the source has exactly two halves.  At a fixed `p`-adic level
`e` it applies [Stacks, Tag 07LA] to the cosimplicial `D(*)`-module `M(•)_e` with the tensor
product *uncompleted*, which makes the level-`e` Moore complex `M(0)_e → M(1)_e → ⋯` acyclic;
that half is `...SmallSite.isZero_homology_levelCosimplicialSections_of_iso` of
`SmallSite/WholeSpaceEnvelope.lean`.  It then passes to the inverse limit over `e`, using that
the transition maps `M(n)_{e + 1} → M(n)_e` are surjective.  **This file is the second half**,
and with it the only input [Stacks, Tag 07LF] still needs is the level-`e` identification itself.

The limit half is [Stacks, Tag 0AAT].  `Stacks.acyclic_limit_of_acyclic_of_surjective` of
`StacksFrontier/Algebra/Homology/InverseLimit.lean` states it for `ℤ`-graded cochain complexes of
`AddCommGrpCat.{u}` indexed by an ordinal, and the complexes here are `ℕ`-graded, valued in
`AddCommGrpCat.{u + 1}` and indexed by `ℕᵒᵖ`.  Rather than re-index that statement — which would
need `ℕ` lifted into `Type (u + 1)` and the `ℕ`-graded complexes extended by zero to `ℤ`-graded
ones — the re-indexing is done through [Stacks, Tag 070E],
`Stacks.isIso_comparisonHomologyLimit_of_isMittagLeffler` of the same module, which is already
stated for towers indexed by `ℕᵒᵖ` and for abelian groups in an arbitrary universe.  The window
`A^{-2} → A^{-1} → A^0 → A^1` that [Stacks, Tag 070E] asks for is four consecutive terms of the
Moore complex of the cosimplicial object of *towers* whose degreewise limit is `M(•)`; the
Mittag-Leffler hypotheses on `A^{-2}` and `A^{-1}` come from the surjectivity of the transitions,
and the essential constancy of the tower of `H^{-1}`'s is free because level-wise acyclicity makes
that tower pointwise zero.

## What is and is not proved

**[Stacks, Tag 07LF] is not proved and no tag attribute is placed in this file.**  What is proved
is that the tag follows from the level-`e` identification alone.  Precisely,
`...SmallSite.vanishing07LF_of_levelCosimplicialSectionsIso` carries exactly one hypothesis,
quantified over `F` satisfying hypotheses (1) and (2) of [Stacks, Tag 07JN], over `i > 0` and
over the level `e`: a cosimplicial `D(*)`-module `L_*` and an isomorphism of cosimplicial abelian
groups `M(•)_e ≅ L_* ⊗_{D(*)} Ω^i_{D(*)}`, with the tensor product **uncompleted**.  No
acyclicity is assumed, and the surjectivity of the level transitions is *not* assumed either: it
is derived from hypothesis (2) through
`...SmallSite.hasSurjectiveWholeSpaceTransitions_tensorDifferentialFormsSheaf`.

This note invalidates a claim made elsewhere, and records what it said.  The module documentation
of `SmallSite/WholeSpaceEnvelope.lean` says that using [Stacks, Tag 0AAT] on the `ℕ`-graded
complexes of `AddCommGrpCat.{u + 1}` indexed by `ℕᵒᵖ` "needs a re-indexing that is not written",
and that "nothing here re-indexes [Stacks, Tag 0AAT]".  The re-indexing is
`Stacks.TowerAcyclicity.isZero_homology_lim` below, so the first claim is **no longer true**; the
second remains true of that file, the re-indexing being here.

What that same module says about the *completed* reduction
`...SmallSite.vanishing07LF_of_cosimplicialSectionsIso` — that it is "sound but is not what the
source proves" — remains true, and is the reason this file exists.  The source's footnote on its
proof of [Stacks, Tag 07LF] records that `lim_e M(n)_e ⊗_{D(n)} Ω^i_{D(n)}` is not the `p`-adic
completion of `M(n) ⊗_{D(n)} Ω^i_{D(n)}`, because the hypotheses of [Stacks, Tag 07JN] do not
give `M(n)_e = M(n)_{e + 1}/p^e M(n)_{e + 1}`; they do when `F` is a crystal, which is the
hypothesis of [Stacks, Tag 07LG].  So the completed form is the target for that tag, and
`vanishing07LF_of_levelCosimplicialSectionsIso` below is the reduction for this one.

What is **still** owed, and is not supplied here, is the level-`e` identification: the sections
of `F ⊗_{𝒪_{X/S}} Ω^i_{X/S}` over `(X, T(n)_e, δ(n))` as `M(n)_e ⊗_{D(n)} Ω^i_{D(n)}`.  That is
item 6 of the gap list of `SmallSite/AffineCohomology.lean`, read at a finite level.

## Main results

In the namespace `Stacks.TowerAcyclicity`, for a cosimplicial object `Y` of the category of
towers of abelian groups:

* `isZero_homology_lim` — **[Stacks, Tag 0AAT] in the shape this chapter needs**: if the Moore
  complex of every level of `Y` is acyclic and the transition maps of every tower `Y(n)` are
  surjective, the Moore complex of the tower of limits is acyclic.
* `isMittagLeffler_of_surjective_succ` — a tower of abelian groups whose successor transitions
  are surjective is Mittag-Leffler.
* `isEssentiallyConstantPro_of_isZero` — a pointwise zero tower is essentially constant.

In the namespace `Crystalline.GlobalCrystallineSituation.SmallSite`:

* `surjective_wholeSpaceSystem_level_map_of_abelian` — the level transitions
  `Γ((X, T(n)_{e + 1}, δ(n)), G) ⟶ Γ((X, T(n)_e, δ(n)), G)` of the system of [Stacks, Tag 07JN]
  are surjective for every abelian sheaf `G` satisfying the abelian form
  `...SmallSite.HasSurjectiveWholeSpaceTransitions` of hypothesis (2).
* `isZero_homology_sectionsComplex_of_isZero_homology_level` — **the limit half of the source's
  proof**: level-wise acyclicity plus surjective level transitions make
  `M(0) → M(1) → M(2) → ⋯` acyclic.
* `vanishing07LF_of_levelCosimplicialSectionsIso` — **[Stacks, Tag 07LF] from the level-`e`
  identification alone.**

## References

* [Stacks Project, Tag 07LF](https://stacks.math.columbia.edu/tag/07LF)
* [Stacks Project, Tag 07LG](https://stacks.math.columbia.edu/tag/07LG)
* [Stacks Project, Tag 07JN](https://stacks.math.columbia.edu/tag/07JN)
* [Stacks Project, Tag 07LA](https://stacks.math.columbia.edu/tag/07LA)
* [Stacks Project, Tag 0AAT](https://stacks.math.columbia.edu/tag/0AAT)
* [Stacks Project, Tag 070E](https://stacks.math.columbia.edu/tag/070E)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open AlgebraicTopology Opposite Simplicial
open scoped ZeroObject

universe u v

noncomputable section

namespace Stacks.TowerAcyclicity

/-! ### Preliminaries on towers of abelian groups -/

/-- **The limit functor on towers of abelian groups is additive**: a limit cone is computed
componentwise and `limMap` of a sum is the sum of the `limMap`s. -/
instance limAdditive : (lim : (ℕᵒᵖ ⥤ AddCommGrpCat.{v}) ⥤ AddCommGrpCat.{v}).Additive where
  map_add := by
    intro A B f g
    exact limit.hom_ext fun n => by simp [Preadditive.comp_add]

/-- **An additive functor commutes with the differential of the Moore complex of
[Stacks, Tag 019I]**, that differential being the alternating sum of the cofaces. -/
theorem objD_comp {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    (F : C ⥤ D) [F.Additive] (Y : CosimplicialObject C) (n : ℕ) :
    AlternatingCofaceMapComplex.objD (Y ⋙ F) n = F.map (AlternatingCofaceMapComplex.objD Y n) := by
  simp only [AlternatingCofaceMapComplex.objD, F.map_sum, F.map_zsmul]
  rfl

/-- **The limit of a diagram of abelian groups all of whose values are zero is zero.** -/
theorem isZero_limit {J : Type*} [Category J] (F : J ⥤ AddCommGrpCat.{v}) [HasLimit F]
    (h : ∀ j, IsZero (F.obj j)) : IsZero (limit F) := by
  rw [IsZero.iff_id_eq_zero]
  exact limit.hom_ext fun j => by
    rw [Category.id_comp, Limits.zero_comp, ← (h j).eq_zero_of_tgt (limit.π F j)]

/-- **A tower of abelian groups that is pointwise zero is essentially constant** in the sense of
clause (2) of [Stacks, Tag 05PU], the witnessing cone being the zero cone: every map into a zero
group is the zero map, so the retraction and cofinality clauses are automatic. -/
theorem isEssentiallyConstantPro_of_isZero (M : ℕᵒᵖ ⥤ AddCommGrpCat.{v})
    (h : ∀ i, IsZero (M.obj i)) :
    EssentiallyConstantPro.IsEssentiallyConstantPro M := by
  refine ⟨⟨0, { app := fun _ => 0, naturality := by intros; simp }⟩, op 0, 0, ?_, ?_⟩
  · exact (isZero_zero AddCommGrpCat.{v}).eq_of_tgt _ _
  · intro j
    exact ⟨j, (homOfLE (Nat.zero_le j.unop)).op, 𝟙 j, (h j).eq_of_tgt _ _⟩

/-- **Every transition map of a tower is surjective as soon as the successor ones are**, every
morphism `op (n + k) ⟶ op n` of `ℕᵒᵖ` being a composite of `k` successor steps. -/
theorem surjective_map_of_surjective_succ (A : ℕᵒᵖ ⥤ AddCommGrpCat.{v})
    (h : ∀ e : ℕ, Function.Surjective
      (ConcreteCategory.hom (A.map ((homOfLE (Nat.le_succ e)).op : op (e + 1) ⟶ op e))))
    (n k : ℕ) (f : (op (n + k) : ℕᵒᵖ) ⟶ op n) :
    Function.Surjective (ConcreteCategory.hom (A.map f)) := by
  induction k with
  | zero =>
    have hf : f = 𝟙 _ := Subsingleton.elim _ _
    rw [hf, A.map_id]
    exact fun y => ⟨y, rfl⟩
  | succ k ih =>
    have hf : f = ((homOfLE (Nat.le_succ (n + k))).op : op (n + k + 1) ⟶ op (n + k)) ≫
        (homOfLE (Nat.le_add_right n k)).op := Subsingleton.elim _ _
    rw [hf, A.map_comp]
    intro y
    obtain ⟨z, hz⟩ := ih (homOfLE (Nat.le_add_right n k)).op y
    obtain ⟨w, hw⟩ := h (n + k) z
    exact ⟨w, by rw [ConcreteCategory.comp_apply, hw, hz]⟩

/-- **A tower of abelian groups whose successor transition maps are surjective is
Mittag-Leffler**, the eventual range of each term being the whole of it. -/
theorem isMittagLeffler_of_surjective_succ (A : ℕᵒᵖ ⥤ AddCommGrpCat.{v})
    (h : ∀ e : ℕ, Function.Surjective
      (ConcreteCategory.hom (A.map ((homOfLE (Nat.le_succ e)).op : op (e + 1) ⟶ op e)))) :
    (A ⋙ forget AddCommGrpCat.{v}).IsMittagLeffler := by
  refine Functor.isMittagLeffler_of_surjective _ fun {a b} f => ?_
  obtain ⟨m⟩ := a
  obtain ⟨n⟩ := b
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (leOfHom f.unop : n ≤ m)
  exact surjective_map_of_surjective_succ A h n k f

/-! ### The four-term window of [Stacks, Tag 070E] -/

variable (Y : CosimplicialObject (ℕᵒᵖ ⥤ AddCommGrpCat.{v}))

/-- **The differential of the Moore complex of [Stacks, Tag 019I] in degree `n` is the alternating
sum of the cofaces**, the complex being built with `CochainComplex.of`. -/
theorem d_eq_objD {C : Type*} [Category C] [Preadditive C] (Z : CosimplicialObject C) (n : ℕ) :
    ((alternatingCofaceMapComplex C).obj Z).d n (n + 1) =
      AlternatingCofaceMapComplex.objD Z n := by
  simp [alternatingCofaceMapComplex, AlternatingCofaceMapComplex.obj]

/-- **Two consecutive Moore differentials of a cosimplicial object of towers compose to zero at
each level of the towers.** -/
theorem objD_app_comp (n : ℕ) :
    ∀ i, (AlternatingCofaceMapComplex.objD Y n).app i ≫
        (AlternatingCofaceMapComplex.objD Y (n + 1)).app i = 0 := by
  intro i
  rw [← NatTrans.comp_app, AlternatingCofaceMapComplex.d_squared]
  rfl

/-- **[Stacks, Tag 070E] in the form used below**: for a four-term complex of towers of abelian
groups whose first two terms are Mittag-Leffler and whose homology at the second and third terms
vanishes at every level, the homology of the limit short complex at the third term vanishes.

The essential constancy that [Stacks, Tag 070E] asks of the tower of `H^{-1}`'s is supplied by
`isEssentiallyConstantPro_of_isZero` from the hypothesis `hz₁`, and the limit of the tower of
`H^0`'s is zero by `isZero_limit` from `hz₀`; the comparison between the two is an isomorphism by
the tag, so the source of that comparison is zero as well. -/
theorem isZero_homology_window
    {A₂ A₁ A₀ A₃ : ℕᵒᵖ ⥤ AddCommGrpCat.{v}} (d₂ : A₂ ⟶ A₁) (d₁ : A₁ ⟶ A₀) (d₀ : A₀ ⟶ A₃)
    (h₁ : ∀ i, d₂.app i ≫ d₁.app i = 0) (h₀ : ∀ i, d₁.app i ≫ d₀.app i = 0)
    (hML₂ : (A₂ ⋙ forget AddCommGrpCat.{v}).IsMittagLeffler)
    (hML₁ : (A₁ ⋙ forget AddCommGrpCat.{v}).IsMittagLeffler)
    (hz₁ : ∀ i, IsZero ((invSystemShortComplex d₂ d₁ h₁ i).homology))
    (hz₀ : ∀ i, IsZero ((invSystemShortComplex d₁ d₀ h₀ i).homology)) :
    IsZero ((limitShortComplexOfInvSystem d₁ d₀ h₀).homology) := by
  have hEC := isEssentiallyConstantPro_of_isZero (homologyInvSystem d₂ d₁ h₁) hz₁
  have hiso := isIso_comparisonHomologyLimit_of_isMittagLeffler A₂ A₁ A₀ A₃ d₂ d₁ d₀ h₁ h₀
    hML₂ hML₁ hEC
  exact (isZero_limit _ hz₀).of_iso (asIso (comparisonHomologyLimit d₁ d₀ h₀))

/-- **The homology of a cochain complex of abelian groups read on an explicit window**: it
vanishes in degree `j` exactly when the short complex on the three indices `i`, `j`, `k` has
vanishing homology, provided `i` is the predecessor and `k` the successor of `j`. -/
theorem isZero_homology_iff_sc' (K : CochainComplex AddCommGrpCat.{v} ℕ) {i j k : ℕ}
    (hi : (ComplexShape.up ℕ).prev j = i) (hk : (ComplexShape.up ℕ).next j = k) :
    IsZero (K.homology j) ↔ IsZero ((K.sc' i j k).homology) := by
  rw [← HomologicalComplex.exactAt_iff_isZero_homology, K.exactAt_iff' i j k hi hk,
    ShortComplex.exact_iff_isZero_homology]

/-- A cochain complex has vanishing homology at `j` iff any short complex isomorphic to its window
around `j` has vanishing homology. -/
private theorem isZero_homology_iff_of_iso_sc' (K : CochainComplex AddCommGrpCat.{v} ℕ)
    {i j k : ℕ} (hi : (ComplexShape.up ℕ).prev j = i) (hk : (ComplexShape.up ℕ).next j = k)
    {S : ShortComplex AddCommGrpCat.{v}} (e : K.sc' i j k ≅ S) :
    IsZero (K.homology j) ↔ IsZero S.homology :=
  (isZero_homology_iff_sc' K hi hk).trans
    ⟨fun h => h.of_iso ((ShortComplex.homologyFunctor AddCommGrpCat.{v}).mapIso e.symm),
      fun h => h.of_iso ((ShortComplex.homologyFunctor AddCommGrpCat.{v}).mapIso e)⟩

/-- **The zero endomorphism of `Y(0)` composes with the first Moore differential to zero.**  This
is the left-hand map of the window at degree `0`, where the Moore complex has no incoming
differential. -/
theorem zero_app_comp :
    ∀ i, (0 : Y.obj ⦋0⦌ ⟶ Y.obj ⦋0⦌).app i ≫ (AlternatingCofaceMapComplex.objD Y 0).app i = 0 := by
  intro i
  rw [NatTrans.app_zero, Limits.zero_comp]

/-- **The identity of `Y(0)` composes with the zero endomorphism of `Y(0)` to zero.**  This is the
outer map of the window at degree `0`, chosen to be an isomorphism so that the window's homology
at its second term vanishes. -/
theorem id_app_comp :
    ∀ i, NatTrans.app (𝟙 (Y.obj ⦋0⦌)) i ≫ NatTrans.app (0 : Y.obj ⦋0⦌ ⟶ Y.obj ⦋0⦌) i = 0 := by
  intro i
  rw [NatTrans.app_zero, Limits.comp_zero]

/-- **The window at `n + 1` of the Moore complex of the tower of limits is the limit of the
window.**  Both short complexes have the same objects, and the differentials agree because `lim`
is additive, `objD_comp`. -/
def scIsoLimitWindow (n : ℕ) :
    ((alternatingCofaceMapComplex AddCommGrpCat.{v}).obj (Y ⋙ lim)).sc' n (n + 1) (n + 2) ≅
      limitShortComplexOfInvSystem (AlternatingCofaceMapComplex.objD Y n)
        (AlternatingCofaceMapComplex.objD Y (n + 1)) (objD_app_comp Y n) :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by
      simp only [Iso.refl_hom, HomologicalComplex.shortComplexFunctor'_obj_f,
        limitShortComplexOfInvSystem_f]
      exact ((d_eq_objD (Y ⋙ lim) n).trans (objD_comp lim Y n)).symm)
    (by
      simp only [Iso.refl_hom, HomologicalComplex.shortComplexFunctor'_obj_g,
        limitShortComplexOfInvSystem_g]
      exact ((d_eq_objD (Y ⋙ lim) (n + 1)).trans (objD_comp lim Y (n + 1))).symm)

/-- **The window at `0` of the Moore complex of the tower of limits is the limit of the window**
whose incoming map is the zero endomorphism of `Y(0)`: the Moore complex has no differential into
degree `0`, and `lim` carries the zero map to the zero map. -/
def scIsoLimitWindowZero :
    ((alternatingCofaceMapComplex AddCommGrpCat.{v}).obj (Y ⋙ lim)).sc' 0 0 1 ≅
      limitShortComplexOfInvSystem (0 : Y.obj ⦋0⦌ ⟶ Y.obj ⦋0⦌)
        (AlternatingCofaceMapComplex.objD Y 0) (zero_app_comp Y) :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by
      refine (Category.id_comp (limMap (0 : Y.obj ⦋0⦌ ⟶ Y.obj ⦋0⦌))).trans
        (Eq.trans ?_ (Category.comp_id _).symm)
      exact (lim.map_zero (Y.obj ⦋0⦌) (Y.obj ⦋0⦌)).trans
        (((alternatingCofaceMapComplex AddCommGrpCat.{v}).obj
          (Y ⋙ lim)).shape 0 0 (by simp)).symm)
    (by
      simp only [Iso.refl_hom, HomologicalComplex.shortComplexFunctor'_obj_g,
        limitShortComplexOfInvSystem_g]
      exact ((d_eq_objD (Y ⋙ lim) 0).trans (objD_comp lim Y 0)).symm)

/-- **The window at `n + 1` of the Moore complex of the level `e` of `Y` is the level `e` of the
window.**  Evaluation at a fixed index is additive, so it commutes with the Moore differential by
`objD_comp`. -/
def scIsoLevelWindow (e : ℕᵒᵖ) (n : ℕ) :
    ((alternatingCofaceMapComplex AddCommGrpCat.{v}).obj
        (Y ⋙ (evaluation ℕᵒᵖ AddCommGrpCat.{v}).obj e)).sc' n (n + 1) (n + 2) ≅
      invSystemShortComplex (AlternatingCofaceMapComplex.objD Y n)
        (AlternatingCofaceMapComplex.objD Y (n + 1)) (objD_app_comp Y n) e :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by
      simp only [Iso.refl_hom, HomologicalComplex.shortComplexFunctor'_obj_f,
        invSystemShortComplex_f]
      exact ((d_eq_objD _ n).trans
        (objD_comp ((evaluation ℕᵒᵖ AddCommGrpCat.{v}).obj e) Y n)).symm)
    (by
      simp only [Iso.refl_hom, HomologicalComplex.shortComplexFunctor'_obj_g,
        invSystemShortComplex_g]
      exact ((d_eq_objD _ (n + 1)).trans
        (objD_comp ((evaluation ℕᵒᵖ AddCommGrpCat.{v}).obj e) Y (n + 1))).symm)

/-- **The window at `0` of the Moore complex of the level `e` of `Y` is the level `e` of the
window** whose incoming map is the zero endomorphism of `Y(0)`. -/
def scIsoLevelWindowZero (e : ℕᵒᵖ) :
    ((alternatingCofaceMapComplex AddCommGrpCat.{v}).obj
        (Y ⋙ (evaluation ℕᵒᵖ AddCommGrpCat.{v}).obj e)).sc' 0 0 1 ≅
      invSystemShortComplex (0 : Y.obj ⦋0⦌ ⟶ Y.obj ⦋0⦌)
        (AlternatingCofaceMapComplex.objD Y 0) (zero_app_comp Y) e :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by
      simp only [Iso.refl_hom, HomologicalComplex.shortComplexFunctor'_obj_f,
        invSystemShortComplex_f, NatTrans.app_zero]
      exact (((alternatingCofaceMapComplex AddCommGrpCat.{v}).obj
        (Y ⋙ (evaluation ℕᵒᵖ AddCommGrpCat.{v}).obj e)).shape 0 0 (by simp)).symm)
    (by
      simp only [Iso.refl_hom, HomologicalComplex.shortComplexFunctor'_obj_g,
        invSystemShortComplex_g]
      exact ((d_eq_objD _ 0).trans
        (objD_comp ((evaluation ℕᵒᵖ AddCommGrpCat.{v}).obj e) Y 0)).symm)

/-- **The window `Y(0) --id--> Y(0) --0--> Y(0)` has vanishing homology at every level**, its
first map being an isomorphism. -/
theorem isZero_homology_invSystemShortComplex_id :
    ∀ i, IsZero ((invSystemShortComplex (𝟙 (Y.obj ⦋0⦌))
      (0 : Y.obj ⦋0⦌ ⟶ Y.obj ⦋0⦌) (id_app_comp Y) i).homology) := by
  intro i
  rw [← ShortComplex.exact_iff_isZero_homology, ShortComplex.ab_exact_iff]
  intro x _
  exact ⟨x, rfl⟩

/-- **Level-wise acyclicity gives the vanishing of the homology of the degree-`0` window at every
level**, that window being the degree-`0` window of the level's Moore complex. -/
theorem isZero_homology_levelWindowZero
    (hz : ∀ (e : ℕᵒᵖ) (j : ℕ), IsZero (((alternatingCofaceMapComplex AddCommGrpCat.{v}).obj
      (Y ⋙ (evaluation ℕᵒᵖ AddCommGrpCat.{v}).obj e)).homology j)) :
    ∀ i, IsZero ((invSystemShortComplex (0 : Y.obj ⦋0⦌ ⟶ Y.obj ⦋0⦌)
      (AlternatingCofaceMapComplex.objD Y 0) (zero_app_comp Y) i).homology) := fun i =>
  (isZero_homology_iff_of_iso_sc' _ (by simp) (by simp) (scIsoLevelWindowZero Y i)).mp (hz i 0)

/-- **Level-wise acyclicity gives the vanishing of the homology of the degree-`n + 1` window at
every level**, that window being the degree-`n + 1` window of the level's Moore complex. -/
theorem isZero_homology_levelWindow
    (hz : ∀ (e : ℕᵒᵖ) (j : ℕ), IsZero (((alternatingCofaceMapComplex AddCommGrpCat.{v}).obj
      (Y ⋙ (evaluation ℕᵒᵖ AddCommGrpCat.{v}).obj e)).homology j)) (n : ℕ) :
    ∀ i, IsZero ((invSystemShortComplex (AlternatingCofaceMapComplex.objD Y n)
      (AlternatingCofaceMapComplex.objD Y (n + 1)) (objD_app_comp Y n) i).homology) := fun i =>
  (isZero_homology_iff_of_iso_sc' _ (by simp) (by simp) (scIsoLevelWindow Y i n)).mp
    (hz i (n + 1))

/-- **[Stacks, Tag 0AAT] for a cosimplicial object of towers of abelian groups.**  If the Moore
complex of every level of `Y` is acyclic and the successor transition maps of every tower `Y(n)`
are surjective, then the Moore complex of the tower of limits `n ↦ lim_e Y(n)_e` is acyclic.

This is the re-indexing of [Stacks, Tag 0AAT] that the chapter needs: the tag is available for
`ℤ`-graded complexes indexed by an ordinal, and these complexes are `ℕ`-graded and indexed by
`ℕᵒᵖ`.  The proof runs [Stacks, Tag 070E] on the four-term window around each degree, in the
three shapes the degree can take — `0`, `1` and `n + 2` — because the Moore complex has no
differential into degree `0`, so the window there has to be completed with the identity of `Y(0)`
on the outside rather than with a Moore differential. -/
theorem isZero_homology_lim
    (hsurj : ∀ n e : ℕ, Function.Surjective (ConcreteCategory.hom
      ((Y.obj ⦋n⦌).map ((homOfLE (Nat.le_succ e)).op : op (e + 1) ⟶ op e))))
    (hz : ∀ (e : ℕᵒᵖ) (j : ℕ), IsZero (((alternatingCofaceMapComplex AddCommGrpCat.{v}).obj
      (Y ⋙ (evaluation ℕᵒᵖ AddCommGrpCat.{v}).obj e)).homology j))
    (j : ℕ) :
    IsZero (((alternatingCofaceMapComplex AddCommGrpCat.{v}).obj (Y ⋙ lim)).homology j) := by
  have hML : ∀ n : ℕ, ((Y.obj ⦋n⦌) ⋙ forget AddCommGrpCat.{v}).IsMittagLeffler :=
    fun n => isMittagLeffler_of_surjective_succ _ (hsurj n)
  obtain _ | _ | n := j
  · exact (isZero_homology_iff_of_iso_sc' _ (by simp) (by simp) (scIsoLimitWindowZero Y)).mpr
      (isZero_homology_window (𝟙 (Y.obj ⦋0⦌)) (0 : Y.obj ⦋0⦌ ⟶ Y.obj ⦋0⦌)
        (AlternatingCofaceMapComplex.objD Y 0) (id_app_comp Y) (zero_app_comp Y) (hML 0) (hML 0)
        (isZero_homology_invSystemShortComplex_id Y) (isZero_homology_levelWindowZero Y hz))
  · exact (isZero_homology_iff_of_iso_sc' _ (by simp) (by simp) (scIsoLimitWindow Y 0)).mpr
      (isZero_homology_window (0 : Y.obj ⦋0⦌ ⟶ Y.obj ⦋0⦌)
        (AlternatingCofaceMapComplex.objD Y 0) (AlternatingCofaceMapComplex.objD Y 1)
        (zero_app_comp Y) (objD_app_comp Y 0) (hML 0) (hML 0)
        (isZero_homology_levelWindowZero Y hz) (isZero_homology_levelWindow Y hz 0))
  · exact (isZero_homology_iff_of_iso_sc' _ (by simp) (by simp) (scIsoLimitWindow Y (n + 1))).mpr
      (isZero_homology_window (AlternatingCofaceMapComplex.objD Y n)
        (AlternatingCofaceMapComplex.objD Y (n + 1)) (AlternatingCofaceMapComplex.objD Y (n + 2))
        (objD_app_comp Y n) (objD_app_comp Y (n + 1)) (hML n) (hML (n + 1))
        (isZero_homology_levelWindow Y hz n) (isZero_homology_levelWindow Y hz (n + 1)))

end Stacks.TowerAcyclicity

/-! ### The limit over the `p`-adic levels for the system of [Stacks, Tag 07JN] -/

namespace Crystalline.GlobalCrystallineSituation.SmallSite

variable {S : GlobalCrystallineSituation.{u}}

/-- **The level transitions of the system `(X, T(n)_e, δ(n))` of [Stacks, Tag 07JN] are surjective
for an abelian coefficient sheaf satisfying the abelian form of hypothesis (2).**  The restriction
map

`Γ((X, T(n)_{e + 1}, δ(n)), G) ⟶ Γ((X, T(n)_e, δ(n)), G)`

is surjective for every `n` and every `e`.

This is `...SmallSite.surjective_wholeSpaceSystem_level_map` of
`SmallSite/LevelRestrictionSurjectivity.lean` with its module-valued hypotheses (1) and (2) of
[Stacks, Tag 07JN] replaced by the abelian predicate
`...SmallSite.HasSurjectiveWholeSpaceTransitions` that they are used only through — which is what
makes it applicable to `...SmallSite.tensorDifferentialFormsSheaf`, a sheafification for which the
module-valued hypothesis (1) `...SmallSite.IsLocallyQuasiCoherent` cannot be written down.

The two inputs are proved and not assumed: the level drops are closed immersions on ambient
schemes by `...SmallSite.isClosedImmersion_targetHom_inverse_map` applied to the ring surjectivity
`Crystalline.surjective_hom_hom_affineLevelSystem_map`, and the objects of the system lie in `𝒞`
by `...SmallSite.isWholeSpaceSystem_wholeSpaceSystem`.  **No tag attribute is placed**: this is a
step inside the proof of [Stacks, Tag 07LF], not a clause of a tag. -/
theorem surjective_wholeSpaceSystem_level_map_of_abelian [IsAffine S.X] [IsAffine S.S.scheme]
    (hp : IsNilpotent (S.p : Γ(S.X, ⊤)))
    (G : Sheaf (smallTopology S) AddCommGrpCat.{u + 1})
    (hG : HasSurjectiveWholeSpaceTransitions G) (n e : ℕ) :
    Function.Surjective (ConcreteCategory.hom (G.val.map
      (((wholeSpaceSystem S hp).obj (op ⦋n⦌)).map (homOfLE (Nat.le_succ e))).op)) :=
  hG _ _ _
    (isClosedImmersion_targetHom_inverse_map hp _
      (_root_.Crystalline.surjective_hom_hom_affineLevelSystem_map _ _ n (Nat.le_succ e)))
    (isWholeSpaceSystem_wholeSpaceSystem S hp n e)
    (isWholeSpaceSystem_wholeSpaceSystem S hp n (e + 1))

/-- **The limit half of the source's proof of [Stacks, Tag 07LF]**: if the Moore complex

`M(0)_e → M(1)_e → M(2)_e → ⋯`

of the sections of `G` at a fixed `p`-adic level is acyclic for every level `e`, and the level
transition maps `M(n)_{e + 1} → M(n)_e` are surjective, then the complex

`M(0) → M(1) → M(2) → ⋯`

of [Stacks, Tag 07JN] — whose degree-`n` term is `M(n) = lim_e M(n)_e` — is acyclic.

This is [Stacks, Tag 0AAT] in the shape this chapter needs,
`Stacks.TowerAcyclicity.isZero_homology_lim`, applied to `...SmallSite.sectionSystem`: the
cosimplicial object of towers whose degreewise limit is `...SmallSite.cosimplicialSections` and
whose degreewise value at `e` is `...SmallSite.levelCosimplicialSections`, both identifications
being definitional.  The system `T` is arbitrary and no property of it is used; its level
transitions enter only through `hsurj`.  **No tag attribute is placed.** -/
theorem isZero_homology_sectionsComplex_of_isZero_homology_level
    (T : SimplicialObject (ℕ ⥤ CrystallineThickening S))
    (G : (CrystallineThickening S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1})
    (hsurj : ∀ n e : ℕ, Function.Surjective (ConcreteCategory.hom
      (G.map (((T.obj (op ⦋n⦌)).map (homOfLE (Nat.le_succ e))).op))))
    (hz : ∀ e j : ℕ, IsZero (((alternatingCofaceMapComplex AddCommGrpCat.{u + 1}).obj
      (levelCosimplicialSections T G e)).homology j))
    (j : ℕ) :
    IsZero ((sectionsComplex T G).homology j) :=
  Stacks.TowerAcyclicity.isZero_homology_lim (sectionSystem T G) hsurj
    (fun e k => hz e.unop k) j

section Affine

variable [IsAffine S.X] [IsAffine S.S.scheme]

/-- **[Stacks, Tag 07LF] from the level-`e` identification alone.**  The conclusion

`H^j(Cris(X/S), F ⊗_{𝒪_{X/S}} Ω^i_{X/S}) = 0`  for `i > 0` and `j ≥ 0`

of [Stacks, Tag 07LF], in the form `...SmallSite.Vanishing07LF` states it, follows from the
existence — for every sheaf of `𝒪_{X/S}`-modules `F` satisfying hypotheses (1) and (2) of
[Stacks, Tag 07JN], every `i > 0` and every `p`-adic level `e` — of a cosimplicial module `L_*`
over the situation's own `D(*)` and an isomorphism of cosimplicial abelian groups

`M(•)_e  ≅  L_* ⊗_{D(*)} Ω^i_{D(*)}`,

the tensor product being **uncompleted**.

This is the reduction the source's own proof makes, and it is not the completed one of
`...SmallSite.vanishing07LF_of_cosimplicialSectionsIso`: the source's footnote on this proof says
that `lim_e M(n)_e ⊗_{D(n)} Ω^i_{D(n)}` is not the `p`-adic completion of
`M(n) ⊗_{D(n)} Ω^i_{D(n)}`, because the hypotheses of [Stacks, Tag 07JN] do not give
`M(n)_e = M(n)_{e + 1}/p^e M(n)_{e + 1}`, and that they do give it when `F` is a crystal — which
is the hypothesis of [Stacks, Tag 07LG].

Nothing beyond the hypothesis is assumed.  The level-`e` acyclicity is proved from
[Stacks, Tag 07LA] at `...SmallSite.wholeSpaceEnvelope` by
`...SmallSite.isZero_homology_levelCosimplicialSections_of_iso`; the passage to the limit is
`isZero_homology_sectionsComplex_of_isZero_homology_level` above, whose surjectivity input is
discharged from hypothesis (2) by
`...SmallSite.hasSurjectiveWholeSpaceTransitions_tensorDifferentialFormsSheaf` through
`surjective_wholeSpaceSystem_level_map_of_abelian`; and the two remaining inputs of
`...SmallSite.vanishing07LF_of_isZero_homology_sectionsComplex` are closed unconditionally in
`SmallSite/TensorRestrictionVanishing.lean` and `SmallSite/TensorSheafGlobalSections.lean`.  The
nilpotence of `p` on `Γ(X, ⊤)` is not a hypothesis but is discharged from `IsAffine S.X` by
`...isNilpotent_prime_sections_of_isAffine`, and the two affineness instances are carried as
`...SmallSite.Vanishing07LF` quantifies over them anyway.

**No tag attribute is placed**, this statement carrying `hiso` as a hypothesis; the point of it
is that exactly one input is left, and that it is the one the source's proof actually uses.  That
input is supplied by `...SmallSite.levelCosimplicialSectionsFormsIso` of
`SmallSite/LevelFormsCosimplicialIso.lean`, where [Stacks, Tag 07LF] is proved and tagged. -/
theorem vanishing07LF_of_levelCosimplicialSectionsIso
    (hiso : ∀ F : SheafOfModules.{u} (structureSheaf S), IsLocallyQuasiCoherent F →
      CohomologyRestriction.IsSurjectiveComparison F.val → ∀ i : ℕ, 0 < i → ∀ e : ℕ,
        ∃ L : _root_.Crystalline.CosimplicialModule
            (wholeSpaceEnvelopeRing (isNilpotent_prime_sections_of_isAffine S)),
          Nonempty (levelCosimplicialSections
              (wholeSpaceSystem S (isNilpotent_prime_sections_of_isAffine S))
              (tensorDifferentialFormsSheaf F i).obj e ≅
            (_root_.Crystalline.cosimplicialModuleForget
                  (wholeSpaceEnvelopeRing (isNilpotent_prime_sections_of_isAffine S))).obj
                (L ⊗ (_root_.Crystalline.exteriorPowerFunctor
                      (wholeSpaceEnvelopeRing (isNilpotent_prime_sections_of_isAffine S))
                      i).functor.obj
                  (wholeSpaceEnvelopeDifferentials
                    (isNilpotent_prime_sections_of_isAffine S))) ⋙
              AddCommGrpCat.uliftFunctor.{u + 1, u})) :
    Vanishing07LF S := by
  refine vanishing07LF_of_isZero_homology_sectionsComplex' fun F hF hM i hi j ↦ ?_
  refine isZero_homology_sectionsComplex_of_isZero_homology_level _ _
    (fun n e => surjective_wholeSpaceSystem_level_map_of_abelian _
      (tensorDifferentialFormsSheaf F i)
      (hasSurjectiveWholeSpaceTransitions_tensorDifferentialFormsSheaf F i hF hM) n e)
    (fun e k => ?_) j
  obtain ⟨L, ⟨ε⟩⟩ := hiso F hF hM i hi e
  exact isZero_homology_levelCosimplicialSections_of_iso
    (isNilpotent_prime_sections_of_isAffine S) _ _ e L hi ε k

end Affine

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
