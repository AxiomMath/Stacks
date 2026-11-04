module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import StacksFrontier.AlgebraicGeometry.AffineCohomologyVanishing.Basic
public import StacksFrontier.AlgebraicGeometry.Cohomology.AffineCoverVanishing.CoveringNumber
public import StacksFrontier.Cotangent.CohomologyPresheaf.SiteSectionsComparison
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.SectionsOverAnOpen
import Mathlib.CategoryTheory.Sites.SheafCohomology.MayerVietoris
import Mathlib.Topology.Sheaves.MayerVietoris

/-!
# The affine covering number and cohomological vanishing

The affine covering number of an open subscheme is the least number of affine opens needed to
cover it. If a scheme with affine diagonal is covered by `t` affine open subschemes, then the
cohomology of every quasi-coherent module vanishes in all degrees at least `t`; for a
quasi-compact scheme with affine diagonal this gives vanishing above the affine covering number.
That `X` has affine diagonal is expressed by the diagonal of `terminal.from X` being affine.

## Main definitions

* `minimalAffineCoverCardinality` is the least cardinality of a finite affine open cover of an
  open subscheme.
* `FiniteAffineCoversWithBound` packages chosen finite affine covers of a quasi-compact base and
  of the inverse images of their members along a quasi-compact quasi-separated morphism, and
  `FiniteAffineCoversWithBound.localBound` and `FiniteAffineCoversWithBound.bound` are the local
  and common numerical bounds those covers determine.

## Main results

* `exists_fin_affine_cover_of_isCompact`: a quasi-compact open of a scheme admits a finite affine
  open cover indexed by a `Fin`.
* `isZero_cohomologyPresheaf_of_finset_affine_cover`: vanishing above the size of a finite family
  of opens covering a given open, all of whose nonempty finite intersections are affine.
* `isZero_cohomology_of_finite_affine_cover`: quasi-coherent cohomology vanishes above the size
  of a finite affine cover, [Stacks, Tag 01XI].
* `isZero_cohomologyPresheaf_of_affineCoveringNumber_le`: quasi-coherent cohomology vanishes in
  degrees at least the affine covering number, [Stacks, Tag 01XI].

## References

* [Stacks Project, Tag 01X8](https://stacks.math.columbia.edu/tag/01X8)
* [Stacks Project, Tag 01XI](https://stacks.math.columbia.edu/tag/01XI)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Abelian Limits Opposite TopologicalSpace
open AlgebraicGeometry

namespace Stacks.AlgebraicGeometry.AffineCoveringNumber

universe w v u

/-! ### The affine covering number -/

/-- The least number of affine opens in a finite affine open cover of `U`; it is zero if `U` has
no finite affine open cover. -/
noncomputable def minimalAffineCoverCardinality {X : Scheme.{u}} (U : X.Opens) : ℕ :=
  sInf {n : ℕ | ∃ V : Fin n → X.Opens, (∀ i, IsAffineOpen (V i)) ∧ iSup V = U}

/-- Chosen finite affine covers for a quasi-compact, quasi-separated morphism over a
quasi-compact base. -/
structure FiniteAffineCoversWithBound where
  /-- The source scheme. -/
  X : Scheme.{u}
  /-- The base scheme. -/
  S : Scheme.{u}
  /-- The morphism being covered. -/
  f : X ⟶ S
  /-- The morphism is quasi-compact. -/
  quasiCompact : QuasiCompact f
  /-- The morphism is quasi-separated. -/
  quasiSeparated : QuasiSeparated f
  /-- The base is quasi-compact. -/
  compactSpace : CompactSpace S
  /-- The number of members of the chosen affine cover of the base. -/
  baseCard : ℕ
  /-- The base cover is nonempty. -/
  baseCard_pos : 0 < baseCard
  /-- The chosen affine opens of the base. -/
  baseOpen : Fin baseCard → S.Opens
  /-- Every member of the base cover is affine. -/
  baseOpen_isAffine : ∀ j, IsAffineOpen (baseOpen j)
  /-- The chosen base opens cover the base. -/
  iSup_baseOpen : iSup baseOpen = ⊤
  /-- The number of members covering the inverse image of each base open. -/
  fiberCard : Fin baseCard → ℕ
  /-- The chosen affine opens above each member of the base cover. -/
  fiberOpen : ∀ j, Fin (fiberCard j) → X.Opens
  /-- Every member of every fiber cover is affine. -/
  fiberOpen_isAffine : ∀ j i, IsAffineOpen (fiberOpen j i)
  /-- Above each base open, the chosen fiber opens cover its inverse image. -/
  iSup_fiberOpen : ∀ j, iSup (fiberOpen j) = f ⁻¹ᵁ baseOpen j

namespace FiniteAffineCoversWithBound

/-- The bound attached to one member of the affine cover of the base. -/
noncomputable def localBound (C : FiniteAffineCoversWithBound) (j : Fin C.baseCard) : ℕ :=
  Finset.univ.powerset.sup fun I ↦
    I.card + minimalAffineCoverCardinality
      ((C.f ⁻¹ᵁ C.baseOpen j) ⊓ I.inf fun i ↦ C.fiberOpen j i)

/-- The common bound obtained by taking the maximum of all the local bounds. -/
noncomputable def bound (C : FiniteAffineCoversWithBound) : ℕ :=
  Finset.univ.sup C.localBound

end FiniteAffineCoversWithBound

/-- A quasi-compact open of a scheme is covered by finitely many affine opens, indexed by a
`Fin`. -/
alias exists_fin_affine_cover_of_isCompact :=
  _root_.AlgebraicGeometry.exists_fin_affine_cover_of_isCompact

/-! ### Vanishing above the size of a finite affine cover -/

section Vanishing

variable {X : Scheme.{u}}

/-- Over a nonempty finite index set, intersecting a fixed open with each member of a family
commutes with taking the intersection of the family. -/
private lemma inf_finsetInf {ι : Type v} (c : X.Opens) (V : ι → X.Opens) {J : Finset ι}
    (hJ : J.Nonempty) : (J.inf fun i ↦ c ⊓ V i) = c ⊓ J.inf V := by
  obtain ⟨j, hj⟩ := hJ
  exact le_antisymm
    (le_inf ((Finset.inf_le hj).trans inf_le_left)
      (Finset.le_inf fun i hi ↦ (Finset.inf_le hi).trans inf_le_right))
    (Finset.le_inf fun i hi ↦ le_inf inf_le_left (inf_le_right.trans (Finset.inf_le hi)))

/-- On a scheme with affine diagonal, a nonempty finite intersection of affine opens is
affine. -/
private lemma isAffineOpen_finsetInf [IsAffineHom (pullback.diagonal (terminal.from X))]
    {ι : Type v} {U : ι → X.Opens} (hU : ∀ i, IsAffineOpen (U i)) {J : Finset ι}
    (hJ : J.Nonempty) : IsAffineOpen (J.inf U) := by
  classical
  rw [Finset.inf_eq_iInf]
  exact IsAffineOpen.biInf (ι := ι) (U := U) (J : Set ι) (J : Set ι).toFinite
    (by simpa using hJ) fun i _ ↦ hU i

/-- Cohomology over an open, in the `Ext`-group model, is the right-derived functor of sections
over that open applied to the underlying abelian sheaf. -/
private noncomputable def cohomologyIsoHgroup (U : X.Opens) (F : X.Modules) (n : ℕ) :
    Sheaf.H'.{u, u, u} ((SheafOfModules.toSheaf X.ringCatSheaf).obj F) n U ≅
      Hgroup X.ringCatSheaf U n F :=
  Stacks.Cohomology.SiteSections.cohomologyIsoRightDerivedSections _ _ _ _ ≪≫
    ((Stacks.Cohomology.ModuleComparison.underlyingSectionsIso X.ringCatSheaf U n).app F).symm

/-- Cohomology of a quasi-coherent module over the empty open vanishes in every degree. -/
private lemma isZero_hgroup_bot (F : X.Modules) [F.IsQuasicoherent] (n : ℕ) :
    IsZero (Hgroup X.ringCatSheaf (⊥ : X.Opens) n F) := by
  cases n with
  | zero =>
    have hlex : PreservesFiniteLimits (secF X.ringCatSheaf (⊥ : X.Opens)) := by
      show PreservesFiniteLimits (SheafOfModules.evaluation X.ringCatSheaf (op (⊥ : X.Opens)) ⋙
        forget₂ (ModuleCat.{u} (X.ringCatSheaf.obj.obj (op (⊥ : X.Opens)))) AddCommGrpCat.{u})
      infer_instance
    have hterm : IsTerminal
        (((SheafOfModules.toSheaf X.ringCatSheaf).obj F).obj.obj (op (⊥ : X.Opens))) :=
      TopCat.Sheaf.isTerminalOfEmpty ((SheafOfModules.toSheaf X.ringCatSheaf).obj F)
    exact IsZero.of_iso hterm.isZero
      ((secF X.ringCatSheaf (⊥ : X.Opens)).rightDerivedZeroIsoSelf.app F)
  | succ k =>
    exact Stacks.Cohomology.Cech.isZero_hgroup_of_isAffineOpen X F ⊥
      (isAffineOpen_bot X) (k + 1) (Nat.succ_pos k)

/-- Vanishing of cohomology in the morphism universe of the site of opens implies vanishing in an
arbitrary `Ext`-universe. -/
private lemma isZero_cohomology_chgUniv
    [HasExt.{w} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]
    (G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (n : ℕ) (U : X.Opens)
    (h : IsZero (Sheaf.H'.{u, u, u} G n U)) : IsZero (Sheaf.H'.{w, u, u} G n U) := by
  let A := (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
    (yoneda.obj U ⋙ AddCommGrpCat.free)
  have hsmall : Subsingleton (Ext.{u} A G n) :=
    AddCommGrpCat.isZero_iff_subsingleton.mp (h : IsZero ((extFunctorObj.{u} A n).obj G))
  exact AddCommGrpCat.isZero_iff_subsingleton.mpr
    (Ext.chgUniv.{w, u} (X := A) (Y := G) (n := n)).symm.injective.subsingleton

/-- **Vanishing above the size of a finite cover with affine intersections.** If the open
`I.sup V` is covered by the members `V i`, `i ∈ I`, of a family all of whose nonempty finite
subintersections are affine, then the cohomology of a quasi-coherent module over `I.sup V`
vanishes in every degree at least the number of members. -/
private lemma isZero_cohomologyPresheaf_of_finset_affine_cover_aux {ι : Type v}
    (F : X.Modules) [F.IsQuasicoherent] (V : ι → X.Opens) (I : Finset ι) (n : ℕ)
    (hV : ∀ J : Finset ι, J.Nonempty → J ⊆ I → IsAffineOpen (J.inf V)) (hn : I.card ≤ n) :
    IsZero (Sheaf.H'.{u, u, u} ((SheafOfModules.toSheaf X.ringCatSheaf).obj F) n (I.sup V)) := by
  classical
  induction I using Finset.induction_on generalizing V n with
  | empty =>
    simp only [Finset.sup_empty]
    exact IsZero.of_iso (isZero_hgroup_bot F n) (cohomologyIsoHgroup (⊥ : X.Opens) F n)
  | @insert a I ha ih =>
    have hcard : I.card + 1 ≤ n := by
      rwa [Finset.card_insert_of_notMem ha] at hn
    have hBaff : IsAffineOpen (V a) := by
      simpa using hV {a} ⟨a, by simp⟩ (by simp)
    have hA : IsZero
        (Sheaf.H'.{u, u, u} ((SheafOfModules.toSheaf X.ringCatSheaf).obj F) n (I.sup V)) :=
      ih V n (fun J hJ hJI ↦ hV J hJ (hJI.trans (Finset.subset_insert a I))) (by omega)
    have hBcoh : IsZero
        (Sheaf.H'.{u, u, u} ((SheafOfModules.toSheaf X.ringCatSheaf).obj F) n (V a)) :=
      IsZero.of_iso (Stacks.Cohomology.Cech.isZero_hgroup_of_isAffineOpen X F (V a) hBaff n
        (by omega)) (cohomologyIsoHgroup (V a) F n)
    have hinter : (I.sup fun i ↦ V a ⊓ V i) = I.sup V ⊓ V a := by
      rw [← Finset.sup_inf_distrib_left, inf_comm]
    have hIcoh : IsZero (Sheaf.H'.{u, u, u} ((SheafOfModules.toSheaf X.ringCatSheaf).obj F)
        (n - 1) (I.sup V ⊓ V a)) := by
      rw [← hinter]
      refine ih (fun i ↦ V a ⊓ V i) (n - 1) (fun J hJ hJI ↦ ?_) (by omega)
      rw [inf_finsetInf (V a) V hJ, ← Finset.inf_insert]
      exact hV (insert a J) ⟨a, by simp⟩ (Finset.insert_subset_insert a hJI)
    have hz := (((Opens.mayerVietorisSquare (I.sup V) (V a)).sequence_exact
      ((SheafOfModules.toSheaf X.ringCatSheaf).obj F) (n - 1) n (by omega)).exact 2)
        |>.isZero_of_both_isZero hIcoh ((biprod_isZero_iff _ _).2 ⟨hA, hBcoh⟩)
    rw [Finset.sup_insert, sup_comm]
    show IsZero (((SheafOfModules.toSheaf X.ringCatSheaf).obj F).H'.{u, u, u} n
      (Opens.mayerVietorisSquare (I.sup V) (V a)).X₄)
    simpa [ComposableArrows.Precomp.obj, ComposableArrows.obj',
      ComposableArrows.mk₄, ComposableArrows.mk₃, ComposableArrows.mk₂] using hz

/-- **Vanishing above the size of a finite cover with affine intersections.** If the open
`I.sup V` is covered by the members `V i`, `i ∈ I`, of a family all of whose nonempty finite
subintersections are affine, then the cohomology of a quasi-coherent module over `I.sup V`
vanishes in every degree at least the number of members. -/
lemma isZero_cohomologyPresheaf_of_finset_affine_cover
    [HasExt.{w} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})] {ι : Type v}
    (F : X.Modules) [F.IsQuasicoherent] (V : ι → X.Opens) (I : Finset ι) (n : ℕ)
    (hV : ∀ J : Finset ι, J.Nonempty → J ⊆ I → IsAffineOpen (J.inf V)) (hn : I.card ≤ n) :
    IsZero ((((SheafOfModules.toSheaf X.ringCatSheaf).obj F).cohomologyPresheaf n).obj
      (op (I.sup V))) :=
  isZero_cohomology_chgUniv _ n _
    (isZero_cohomologyPresheaf_of_finset_affine_cover_aux F V I n hV hn)

/-- On a scheme with affine diagonal covered by `t ≤ n` affine opens, the cohomology of a
quasi-coherent module vanishes in degree `n`. -/
private lemma isZero_H'_top_of_finite_affine_cover
    [IsAffineHom (pullback.diagonal (terminal.from X))] {t : ℕ}
    (U : Fin t → X.Opens) (hU : ∀ i, IsAffineOpen (U i)) (hUcover : iSup U = ⊤)
    (F : X.Modules) [F.IsQuasicoherent] (n : ℕ) (hn : t ≤ n) :
    IsZero (Sheaf.H'.{u, u, u} ((SheafOfModules.toSheaf X.ringCatSheaf).obj F) n ⊤) := by
  classical
  have h := isZero_cohomologyPresheaf_of_finset_affine_cover_aux F U Finset.univ n
    (fun _ hJ _ ↦ isAffineOpen_finsetInf hU hJ) (by simpa using hn)
  rwa [show (Finset.univ : Finset (Fin t)).sup U = ⊤ by
    simpa [Finset.sup_eq_iSup] using hUcover] at h

variable (X) in
/-- **[Stacks, Tag 01XI].** If `X` has affine diagonal and is covered by `t` affine opens, then
the cohomology of a quasi-coherent `O_X`-module vanishes in every degree at least `t`. -/
theorem isZero_cohomology_of_finite_affine_cover
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    {t : ℕ} (U : Fin t → X.Opens) (hU : ∀ i, IsAffineOpen (U i))
    (hUcover : ⨆ i, U i = ⊤) (F : SheafOfModules X.ringCatSheaf) [F.IsQuasicoherent]
    (n : ℕ) (hn : t ≤ n) :
    IsZero (((SheafOfModules.toSheaf X.ringCatSheaf ⋙
      (sheafSections (Opens.grothendieckTopology X) AddCommGrpCat).obj
        (op (⊤ : X.Opens))).rightDerived n).obj F) := by
  exact IsZero.of_iso (isZero_H'_top_of_finite_affine_cover U hU hUcover F n hn)
    (cohomologyIsoHgroup (⊤ : X.Opens) F n).symm

variable (X) in
/-- **[Stacks, Tag 01XI].** If `X` is quasi-compact with affine diagonal, then the cohomology of
a quasi-coherent `O_X`-module vanishes in every degree at least the minimum number of affine
opens needed to cover `X`. -/
theorem isZero_cohomologyPresheaf_of_affineCoveringNumber_le [CompactSpace X]
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    [HasExt.{w} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]
    (F : X.Modules) [F.IsQuasicoherent] (n : ℕ)
    (hn : minimalAffineCoverCardinality (⊤ : X.Opens) ≤ n) :
    IsZero
      (((((SheafOfModules.toSheaf X.ringCatSheaf).obj F).cohomologyPresheaf n).obj
        (op (⊤ : X.Opens)))) := by
  classical
  have hnon : {q : ℕ | ∃ V : Fin q → X.Opens,
      (∀ i, IsAffineOpen (V i)) ∧ iSup V = (⊤ : X.Opens)}.Nonempty :=
    exists_fin_affine_cover_of_isCompact (⊤ : X.Opens)
      (by simpa using (isCompact_univ : IsCompact (Set.univ : Set X)))
  obtain ⟨U, hU, hUcover⟩ : ∃ U : Fin (minimalAffineCoverCardinality (⊤ : X.Opens)) → X.Opens,
      (∀ i, IsAffineOpen (U i)) ∧ iSup U = (⊤ : X.Opens) := by
    simpa [minimalAffineCoverCardinality] using Nat.sInf_mem hnon
  exact isZero_cohomology_chgUniv _ n _
    (isZero_H'_top_of_finite_affine_cover U hU hUcover F n hn)

end Vanishing

end Stacks.AlgebraicGeometry.AffineCoveringNumber
