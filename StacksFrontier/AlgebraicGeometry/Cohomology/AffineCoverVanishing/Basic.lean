module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.CategoryTheory.Sites.SheafCohomology.MayerVietoris
public import Mathlib.Topology.Sheaves.MayerVietoris
public import StacksFrontier.AlgebraicGeometry.AffineCohomologyVanishing.Basic
public import StacksFrontier.AlgebraicGeometry.Cohomology.AffineCoverVanishing.CoveringNumber
public import StacksFrontier.AlgebraicGeometry.Cohomology.Cech.AffineVanishing
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.CohomologyPresheafComparison

/-!
# Cohomological vanishing above the size of an affine cover

Let `X` be a scheme whose diagonal is affine — for instance a separated scheme — and suppose `X`
is covered by `t` affine open subschemes. Then the cohomology of every quasi-coherent
`𝒪_X`-module vanishes in all degrees `n ≥ t`. In particular, if `X` is quasi-compact the
cohomology vanishes in degrees at least the affine covering number of `X`.

## Main results

* `Stacks.Cohomology.AffineCover.isZero_cohomologyPresheaf_of_infClosed_cover`: vanishing over an
  open covered by `t` opens of an intersection-stable family of affine opens, in degrees `≥ t`.
* `Stacks.Cohomology.AffineCover.isZero_cohomology_of_finite_affine_cover`: vanishing above the
  size of a given finite affine cover.
* `Stacks.Cohomology.AffineCover.isZero_cohomologyPresheaf_of_affineCoveringNumber_le`: the same
  for the affine covering number of a quasi-compact scheme, in Mathlib's cohomology presheaf.

## Implementation notes

Two models of cohomology appear. Serre vanishing on an affine open is stated for the
derived-functor model `Hgroup` of sections in the category of module sheaves, while the
Mayer--Vietoris sequence is Mathlib's, for the `Ext`-theoretic cohomology presheaf of the
underlying abelian sheaf. The two are interchanged by
`Stacks.Cohomology.ModuleComparison.isZero_rightDerivedSections_iff_isZero_cohomologyPresheaf`.

The affine-diagonal hypothesis is expressed by asking the diagonal of the structure morphism to
the terminal scheme to be affine; it is used only through the resulting affineness of an
intersection of two affine opens.

The `Ext` universe of the cohomology presheaf is a parameter of Mathlib's definition, while the
comparison with derived sections is available in the morphism universe of the site; vanishing is
carried across the universe change by `CategoryTheory.Abelian.Ext.chgUniv`.

## References

* [Stacks Project, Tag 01XI](https://stacks.math.columbia.edu/tag/01XI)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry RingedSpaceModuleAdjunction

namespace Stacks.Cohomology.AffineCover

universe u w

variable {X : Scheme.{u}}

section Comparison

variable [HasExt.{u} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]

/-- Cohomology over an open `U`, derived in module sheaves, vanishes exactly when Mathlib's
sheaf cohomology of `U` with values in the underlying abelian sheaf does. -/
theorem isZero_hgroup_iff_isZero_cohomologyPresheaf (U : X.Opens) (F : X.Modules) (n : ℕ) :
    IsZero (Hgroup X.ringCatSheaf U n F) ↔
      IsZero ((((SheafOfModules.toSheaf X.ringCatSheaf).obj F).cohomologyPresheaf n).obj
        (op U)) :=
  ModuleComparison.isZero_rightDerivedSections_iff_isZero_cohomologyPresheaf
    (Opens.grothendieckTopology X) X.ringCatSheaf U n F

end Comparison

section Vanishing

/-- The cohomology of a quasi-coherent `𝒪_X`-module over the empty open vanishes in every
degree. -/
theorem isZero_hgroup_bot (F : X.Modules) [F.IsQuasicoherent] (n : ℕ) :
    IsZero (Hgroup X.ringCatSheaf (⊥ : X.Opens) n F) := by
  cases n with
  | zero =>
    let S := SheafOfModules.toSheaf X.ringCatSheaf ⋙
      (sheafSections (Opens.grothendieckTopology X) AddCommGrpCat).obj (op (⊥ : X.Opens))
    let E := SheafOfModules.evaluation
      (structureSheafRing X.toLocallyRingedSpace.toRingedSpace) (op (⊥ : X.Opens))
    let G := forget₂ (ModuleCat
      ((structureSheafRing X.toLocallyRingedSpace.toRingedSpace).obj.obj (op (⊥ : X.Opens))))
      AddCommGrpCat
    have _ : PreservesFiniteLimits S := by
      change PreservesFiniteLimits (E ⋙ G)
      infer_instance
    have hterm : IsTerminal
        (((SheafOfModules.toSheaf X.ringCatSheaf).obj F).obj.obj (op (⊥ : X.Opens))) :=
      TopCat.Sheaf.isTerminalOfEmpty ((SheafOfModules.toSheaf X.ringCatSheaf).obj F)
    have hsec : IsZero (S.obj F) :=
      (isZero_zero AddCommGrpCat).of_iso
        ((isZero_zero AddCommGrpCat).isoIsTerminal hterm).symm
    change IsZero ((S.rightDerived 0).obj F)
    exact hsec.of_iso (S.rightDerivedZeroIsoSelf.app F)
  | succ k =>
    exact Stacks.Cohomology.Cech.isZero_hgroup_of_isAffineOpen X F ⊥ (isAffineOpen_bot X) (k + 1)
      (Nat.succ_pos k)

variable [HasExt.{u} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]

/-- The cohomology presheaf of a quasi-coherent `𝒪_X`-module vanishes over an affine open in
positive degrees. -/
private theorem isZero_cohomologyPresheaf_of_isAffineOpen {U : X.Opens} (hU : IsAffineOpen U)
    (F : X.Modules) [F.IsQuasicoherent] {n : ℕ} (hn : 0 < n) :
    IsZero ((((SheafOfModules.toSheaf X.ringCatSheaf).obj F).cohomologyPresheaf n).obj (op U)) :=
  (isZero_hgroup_iff_isZero_cohomologyPresheaf U F n).mp
    (Stacks.Cohomology.Cech.isZero_hgroup_of_isAffineOpen X F U hU n hn)

/-- Let `P` be a property of opens of `X` that is stable under intersection and implies
affineness, and let an open `W` be covered by `t` opens with property `P`. Then the cohomology of
a quasi-coherent `𝒪_X`-module over `W` vanishes in every degree at least `t`. -/
theorem isZero_cohomologyPresheaf_of_infClosed_cover (P : X.Opens → Prop)
    (hPinf : ∀ V W, P V → P W → P (V ⊓ W)) (hPaff : ∀ V, P V → IsAffineOpen V)
    {t : ℕ} (U : Fin t → X.Opens) (hU : ∀ i, P (U i))
    (W : X.Opens) (hcover : ⨆ i, U i = W) (F : X.Modules) [F.IsQuasicoherent]
    (n : ℕ) (hn : t ≤ n) :
    IsZero ((((SheafOfModules.toSheaf X.ringCatSheaf).obj F).cohomologyPresheaf n).obj
      (op W)) := by
  classical
  induction t using Nat.strong_induction_on generalizing W n with
  | h t ih =>
    match t with
    | 0 =>
      have hW : W = ⊥ := by simpa using hcover.symm
      refine (isZero_hgroup_iff_isZero_cohomologyPresheaf W F n).mp ?_
      rw [hW]
      exact isZero_hgroup_bot F n
    | 1 =>
      have hU0 : U 0 = W := by simpa using hcover
      rw [← hU0]
      exact isZero_cohomologyPresheaf_of_isAffineOpen (hPaff _ (hU 0)) F (by omega)
    | (m + 2) =>
      let B := U 0
      let V : Fin (m + 1) → X.Opens := fun i ↦ U i.succ
      let A := ⨆ i, V i
      have hsplit : (⨆ i : Fin (m + 2), U i) = A ⊔ B := by
        refine le_antisymm (iSup_le fun i ↦ Fin.cases le_sup_right
          (fun j ↦ le_sup_of_le_left (le_iSup V j)) i) (sup_le ?_ ?_)
        · exact iSup_le fun i ↦ le_iSup_of_le i.succ (by simp [V])
        · exact le_iSup_of_le 0 (by simp [B])
      have hVP : ∀ i, P (V i) := fun i ↦ hU i.succ
      have hBP : P B := hU 0
      have hAcoh := ih (m + 1) (by omega) V hVP A rfl n (by omega)
      have hIcoh := ih (m + 1) (by omega) (fun i ↦ B ⊓ V i)
        (fun i ↦ hPinf _ _ hBP (hVP i)) (B ⊓ A) (inf_iSup_eq B V).symm (n - 1) (by omega)
      have hBcoh := isZero_cohomologyPresheaf_of_isAffineOpen (hPaff _ hBP) F (n := n) (by omega)
      let S := Opens.mayerVietorisSquare A B
      have hsum : IsZero (((SheafOfModules.toSheaf X.ringCatSheaf).obj F).H' n S.X₂ ⊞
          ((SheafOfModules.toSheaf X.ringCatSheaf).obj F).H' n S.X₃) :=
        (biprod_isZero_iff _ _).2 ⟨by simpa [S, A] using hAcoh, by simpa [S, B] using hBcoh⟩
      have hInter : IsZero
          (((SheafOfModules.toSheaf X.ringCatSheaf).obj F).H' (n - 1) S.X₁) := by
        simpa [S, Opens.mayerVietorisSquare, inf_comm] using hIcoh
      have hseq := S.sequence_exact ((SheafOfModules.toSheaf X.ringCatSheaf).obj F)
        (n - 1) n (by omega)
      have hz := (hseq.exact 2).isZero_of_both_isZero hInter hsum
      rw [show W = S.X₄ by
        rw [hcover.symm.trans hsplit]
        simp [S, Opens.mayerVietorisSquare]]
      simpa [ComposableArrows.Precomp.obj, ComposableArrows.obj',
        ComposableArrows.mk₄, ComposableArrows.mk₃, ComposableArrows.mk₂] using hz

/-- Vanishing over `⊤` in degrees at least the size of a finite affine cover. -/
private theorem isZero_cohomologyPresheaf_top_of_affine_cover
    [IsAffineHom (pullback.diagonal (terminal.from X))] {t : ℕ} (U : Fin t → X.Opens)
    (hU : ∀ i, IsAffineOpen (U i)) (hUcover : ⨆ i, U i = ⊤) (F : X.Modules)
    [F.IsQuasicoherent] {n : ℕ} (hn : t ≤ n) :
    IsZero ((((SheafOfModules.toSheaf X.ringCatSheaf).obj F).cohomologyPresheaf n).obj
      (op (⊤ : X.Opens))) :=
  isZero_cohomologyPresheaf_of_infClosed_cover IsAffineOpen
    (fun _ _ hV hW ↦ hV.inf hW) (fun _ h ↦ h) U hU ⊤ hUcover F n hn

end Vanishing

/-- If `X` has affine diagonal and is covered by `t` affine opens, then the
cohomology of a quasi-coherent `𝒪_X`-module vanishes in every degree at least `t`. -/
@[stacks 01XI "finite-cover form"]
theorem isZero_cohomology_of_finite_affine_cover (X : Scheme.{u})
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    {t : ℕ} (U : Fin t → X.Opens) (hU : ∀ i, IsAffineOpen (U i))
    (hUcover : ⨆ i, U i = ⊤) (F : X.Modules) [F.IsQuasicoherent] (n : ℕ) (hn : t ≤ n) :
    IsZero (Hgroup X.ringCatSheaf (⊤ : X.Opens) n F) := by
  let _ : HasExt.{u} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) := inferInstance
  exact (isZero_hgroup_iff_isZero_cohomologyPresheaf (⊤ : X.Opens) F n).mpr
    (isZero_cohomologyPresheaf_top_of_affine_cover U hU hUcover F hn)

/-- If `X` is quasi-compact with affine diagonal — for example if `X` is
separated — then the cohomology of a quasi-coherent `𝒪_X`-module vanishes in every degree at
least the least number of affine opens needed to cover `X`. -/
@[stacks 01XI "minimal-cover form"]
theorem isZero_cohomologyPresheaf_of_affineCoveringNumber_le (X : Scheme.{u}) [CompactSpace X]
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    [HasExt.{w} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]
    (F : X.Modules) [F.IsQuasicoherent] (n : ℕ)
    (hn : minimalAffineCoverCardinality (⊤ : X.Opens) ≤ n) :
    IsZero ((((SheafOfModules.toSheaf X.ringCatSheaf).obj F).cohomologyPresheaf n).obj
      (op (⊤ : X.Opens))) := by
  classical
  let _ : HasExt.{u} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) := inferInstance
  obtain ⟨U, hU, hUcover⟩ := exists_affine_cover_card_eq (⊤ : X.Opens)
    (by simpa using (isCompact_univ : IsCompact (Set.univ : Set X)))
  have hExtU := isZero_cohomologyPresheaf_top_of_affine_cover U hU hUcover F hn
  let A := (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
    (yoneda.obj (⊤ : X.Opens) ⋙ AddCommGrpCat.free)
  let H := (SheafOfModules.toSheaf X.ringCatSheaf).obj F
  have hsubU : Subsingleton (Ext.{u} A H n) := AddCommGrpCat.subsingleton_of_isZero hExtU
  have hsubW : Subsingleton (Ext.{w} A H n) :=
    ⟨fun x y ↦ (Ext.chgUniv.{w, u} (X := A) (Y := H) (n := n)).symm.injective
      (hsubU.elim _ _)⟩
  simpa [A, H, Sheaf.cohomologyPresheaf, Sheaf.cohomologyPresheafFunctor] using
    (AddCommGrpCat.isZero_iff_subsingleton.mpr hsubW)

end Stacks.Cohomology.AffineCover

end
