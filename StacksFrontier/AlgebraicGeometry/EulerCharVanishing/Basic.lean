module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.MayerVietoris
public import StacksFrontier.AlgebraicGeometry.AffineCohomologyVanishing.Basic
public import StacksFrontier.AlgebraicGeometry.EulerCharAdditivity.TwoOutOfThree
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.ModuleCohomologyComparison
public import StacksFrontier.Cotangent.CohomologyPresheaf.SiteSectionsComparison
public import StacksFrontier.Topology.Sheaves.Cohomology.MayerVietoris.LongExactSequence
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.ComparisonAndDegreeZero
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Vanishing of cohomology above a finite affine cover, and Tag 08AA modulo finiteness

[Stacks, Tag 01XI] says that on a quasi-compact scheme with affine diagonal the cohomology of a
quasi-coherent module vanishes in every degree at least the number of affine opens needed to
cover it. This file proves it, and uses it to discharge one of the two facts that make the Euler
characteristic well defined, leaving [Stacks, Tag 08AA] conditional on the other one alone.

Tag 08AA — additivity of `χ` along a short exact sequence of coherent modules on a proper scheme
over a field — is reduced by
`AlgebraicGeometry.eulerCharacteristic_add_of_shortExact_of_outer` to exactly two inputs, for
the outer two modules of the sequence: finite dimensionality of each `Hⁱ(X, ℱ)` over `k`
([Stacks, Tag 02O6]) and the vanishing of all but finitely many of them. **The second is proved
here**, unconditionally, for every quasi-coherent module on a scheme proper over a field:
properness gives quasi-compactness and separatedness, separatedness gives an affine diagonal,
quasi-compactness gives a finite affine cover, and Tag 01XI then bounds the cohomological
degree by the size of that cover — one bound serving every quasi-coherent module at once.

So `AlgebraicGeometry.eulerCharacteristic_add_of_shortExact_of_finiteDimensional` is Tag 08AA
carrying [Stacks, Tag 02O6] and nothing else. It carries no `@[stacks 08AA]` attribute: the tag
sits on `AlgebraicGeometry.eulerCharacteristic_add_of_shortExact`, where Tag 02O6 is supplied
rather than assumed.

## Main results

* `Stacks.Cohomology.FiniteCover.isZero_H'_of_finite_affine_cover`: **[Stacks, Tag 01XI]** in
  Mathlib's `Sheaf.H'` spelling, for an arbitrary open covered by `t` affine opens.
* `Stacks.Cohomology.FiniteCover.isZero_Hgroup_of_finite_affine_cover`: the same in the
  library's `Hgroup` spelling.
* `Stacks.Cohomology.FiniteCover.exists_fin_affine_cover_of_isCompact`: a compact open of a
  scheme admits a finite affine open cover indexed by a `Fin`.
* `AlgebraicGeometry.exists_isZero_cohomologyOverField_of_isProper`: **the vanishing input of
  Tag 0BEJ.** For `X` proper over a field there is a single degree beyond which the cohomology
  of *every* quasi-coherent module on `X` vanishes.
* `AlgebraicGeometry.eulerCharacteristic_add_of_shortExact_of_finiteDimensional`: **Tag 08AA
  with finite dimensionality of cohomology as its only hypothesis.**

## Implementation notes

**Two spellings of sheaf cohomology, and the comparison between them.** Serre vanishing on an
affine open is `Stacks.Cohomology.Cech.isZero_hgroup_of_isAffineOpen`, in the library's `Hgroup`
spelling — the right derived functor of module-valued sections — while the Mayer--Vietoris
sequence is Mathlib's, stated for `Sheaf.H'` of an abelian sheaf. The two are compared once, in
`isZero_Hgroup_iff_isZero_H'`, out of two isomorphisms: [Stacks, Tag 03FD]
(`ModuleSheafCohomology.moduleSheafCohomologyIsoUnderlying`) moves the forgetful functor across
the derived functor, and `Stacks.Cohomology.SiteSections.cohomologyIsoRightDerivedSections`
identifies `Sheaf.H'` with right-derived sections over an object of the site.

## References

* [Stacks Project, Tag 01XI](https://stacks.math.columbia.edu/tag/01XI)
* [Stacks Project, Tag 01XB](https://stacks.math.columbia.edu/tag/01XB)
* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
* [Stacks Project, Tag 08AA](https://stacks.math.columbia.edu/tag/08AA)
* [Stacks Project, Tag 0BEJ](https://stacks.math.columbia.edu/tag/0BEJ)
-/

public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open _root_.AlgebraicGeometry

universe u

namespace Stacks.Cohomology.FiniteCover

variable (X : Scheme.{u})

/-! ### The comparison between the two spellings of sheaf cohomology -/

/-- The right derived functor of sections over `U`, applied to the underlying abelian sheaf of a
module `F`, vanishes exactly when the library's `Hgroup` of `F` over `U` does. -/
private theorem isZero_rightDerived_iff_isZero_Hgroup (F : X.Modules) (U : X.Opens) (n : ℕ) :
    IsZero ((((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      (op U)).rightDerived n).obj ((SheafOfModules.toSheaf X.ringCatSheaf).obj F)) ↔
      IsZero (Hgroup X.ringCatSheaf U n F) := by
  obtain ⟨-, -, hopen⟩ := ModuleSheafCohomology.moduleSheafCohomologyIsoUnderlying
    (Opens.grothendieckTopology X) X.ringCatSheaf
  obtain ⟨eU, -⟩ := hopen U
  exact ((eU n).app F).isZero_iff.symm

/-- The library's cohomology `Hgroup` of a sheaf of modules over an open vanishes exactly when
Mathlib's cohomology `Sheaf.H'` of the underlying abelian sheaf does. This is [Stacks, Tag 03FD]
followed by the identification of `Sheaf.H'` with right-derived sections over an object of the
site. -/
theorem isZero_Hgroup_iff_isZero_H' (F : X.Modules) (U : X.Opens) (n : ℕ) :
    IsZero (Hgroup X.ringCatSheaf U n F) ↔
      IsZero (Sheaf.H'.{u, u, u} ((SheafOfModules.toSheaf X.ringCatSheaf).obj F) n U) :=
  (isZero_rightDerived_iff_isZero_Hgroup X F U n).symm.trans
    (SiteSections.cohomologyIsoRightDerivedSections (Opens.grothendieckTopology X)
      ((SheafOfModules.toSheaf X.ringCatSheaf).obj F) n U).isZero_iff.symm

/-! ### The base cases of the induction -/

/-- **Serre vanishing in Mathlib's spelling**, [Stacks, Tag 01XB] read through
`isZero_Hgroup_iff_isZero_H'`. -/
theorem isZero_H'_of_isAffineOpen (F : X.Modules) [F.IsQuasicoherent]
    (U : X.Opens) (hU : IsAffineOpen U) (n : ℕ) (hn : 0 < n) :
    IsZero (Sheaf.H'.{u, u, u} ((SheafOfModules.toSheaf X.ringCatSheaf).obj F) n U) :=
  (isZero_Hgroup_iff_isZero_H' X F U n).1
    (Stacks.Cohomology.Cech.isZero_hgroup_of_isAffineOpen X F U hU n hn)

/-- The cohomology of a quasi-coherent module over the empty open vanishes in **every** degree,
degree zero included. -/
theorem isZero_H'_bot (F : X.Modules) [F.IsQuasicoherent] (n : ℕ) :
    IsZero
      (Sheaf.H'.{u, u, u} ((SheafOfModules.toSheaf X.ringCatSheaf).obj F) n (⊥ : X.Opens)) := by
  match n with
  | 0 =>
    rw [← isZero_Hgroup_iff_isZero_H']
    have hbot : (⊥ : Sieve (⊥ : X.Opens)) ∈ Opens.grothendieckTopology X (⊥ : X.Opens) :=
      (Opens.mem_grothendieckTopology (T := X) (U := ⊥) (S := ⊥)).2 (by simp)
    have hsec : IsZero ((SheafOfModules.toSheaf X.ringCatSheaf ⋙
        (sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
          (op (⊥ : X.Opens))).obj F) :=
      (Sheaf.isTerminalOfBotCover
        ((SheafOfModules.toSheaf X.ringCatSheaf).obj F) (⊥ : X.Opens) hbot).isZero
    exact IsZero.of_iso hsec
      ((SheafOfModules.toSheaf X.ringCatSheaf ⋙
        (sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
          (op (⊥ : X.Opens))).rightDerivedZeroIsoSelf.app F)
  | (k + 1) =>
    exact isZero_H'_of_isAffineOpen X F ⊥ (isAffineOpen_bot X) (k + 1) (Nat.succ_pos k)

/-! ### Vanishing above the size of a finite affine cover -/

/-- **[Stacks, Tag 01XI] in Mathlib's spelling.** If an open `W` of a scheme with affine diagonal
is covered by `t` affine opens, the cohomology of a quasi-coherent module vanishes over `W` in
every degree at least `t`. -/
theorem isZero_H'_of_finite_affine_cover
    [IsAffineHom (pullback.diagonal (terminal.from X))] (F : X.Modules) [F.IsQuasicoherent] :
    ∀ (t : ℕ) (U : Fin t → X.Opens), (∀ i, IsAffineOpen (U i)) → ∀ W : X.Opens,
      ⨆ i, U i = W → ∀ n : ℕ, t ≤ n →
        IsZero (Sheaf.H'.{u, u, u} ((SheafOfModules.toSheaf X.ringCatSheaf).obj F) n W) := by
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    intro U hU W hcover n hn
    match t with
    | 0 =>
      have hW : W = ⊥ := by simpa using hcover.symm
      exact hW ▸ isZero_H'_bot X F n
    | 1 =>
      have hU0 : U 0 = W := by simpa using hcover
      exact hU0 ▸ isZero_H'_of_isAffineOpen X F (U 0) (hU 0) n (by omega)
    | (m + 2) =>
      set B := U 0 with hB
      set V : Fin (m + 1) → X.Opens := fun i => U i.succ with hV
      set A := ⨆ i, V i with hA
      have hVaff : ∀ i, IsAffineOpen (V i) := fun i => hU i.succ
      have hBaff : IsAffineOpen B := hU 0
      have hsplit : (⨆ i : Fin (m + 2), U i) = A ⊔ B := by
        refine le_antisymm (iSup_le fun i => Fin.cases le_sup_right
          (fun j => le_sup_of_le_left (le_iSup V j)) i) (sup_le ?_ ?_)
        · exact iSup_le fun i => le_iSup_of_le i.succ (by simp [hV])
        · exact le_iSup_of_le 0 (by simp [hB])
      have hWA : W = A ⊔ B := hcover.symm.trans hsplit
      have hvanA : IsZero
          (Sheaf.H'.{u, u, u} ((SheafOfModules.toSheaf X.ringCatSheaf).obj F) n A) :=
        ih (m + 1) (by omega) V hVaff A rfl n (by omega)
      have hvanI : IsZero
          (Sheaf.H'.{u, u, u}
            ((SheafOfModules.toSheaf X.ringCatSheaf).obj F) (n - 1) (A ⊓ B)) :=
        ih (m + 1) (by omega) (fun i => V i ⊓ B) (fun i => (hVaff i).inf hBaff) (A ⊓ B)
          (iSup_inf_eq V B).symm (n - 1) (by omega)
      have hvanB : IsZero
          (Sheaf.H'.{u, u, u} ((SheafOfModules.toSheaf X.ringCatSheaf).obj F) n B) :=
        isZero_H'_of_isAffineOpen X F B hBaff n (by omega)
      have hseq := (Opens.mayerVietorisSquare A B).sequence_exact
        ((SheafOfModules.toSheaf X.ringCatSheaf).obj F) (n - 1) n (by omega)
      have hz := (hseq.exact 2).isZero_of_both_isZero
        (show IsZero ((hseq.sc 2).X₁) from hvanI)
        (show IsZero ((hseq.sc 2).X₃) from (biprod_isZero_iff _ _).2 ⟨hvanA, hvanB⟩)
      rw [hWA]
      exact hz

/-- **[Stacks, Tag 01XI], finite-cover form.** On a scheme with affine diagonal covered by `t`
affine opens, the cohomology of a quasi-coherent module vanishes in every degree at least `t`.

This is the library-spelling counterpart of `isZero_H'_of_finite_affine_cover`. The tag's own
phrasing bounds the degree by the
*minimal* number of affine opens needed to cover the scheme; that follows from this by applying
it to a cover realizing the minimum, and is not stated here because the affine covering number
has no name in the library yet. -/
@[stacks 01XI "finite-cover form"]
theorem isZero_Hgroup_of_finite_affine_cover
    [IsAffineHom (pullback.diagonal (terminal.from X))] (F : X.Modules) [F.IsQuasicoherent]
    {t : ℕ} (U : Fin t → X.Opens) (hU : ∀ i, IsAffineOpen (U i)) (W : X.Opens)
    (hcover : ⨆ i, U i = W) (n : ℕ) (hn : t ≤ n) :
    IsZero (Hgroup X.ringCatSheaf W n F) :=
  (isZero_Hgroup_iff_isZero_H' X F W n).2
    (isZero_H'_of_finite_affine_cover X F t U hU W hcover n hn)

/-! ### Finite affine covers of a compact open -/

/-- A compact open of a scheme admits a finite affine open cover indexed by a `Fin`. -/
theorem exists_fin_affine_cover_of_isCompact (W : X.Opens) (hW : IsCompact (W : Set X)) :
    ∃ (t : ℕ) (U : Fin t → X.Opens), (∀ i, IsAffineOpen (U i)) ∧ ⨆ i, U i = W := by
  classical
  obtain ⟨Us, hUs, hUsfin, hUssup⟩ := X.isBasis_affineOpens.exists_finite_of_isCompact hW
  have : Fintype Us := hUsfin.fintype
  let e := Fintype.equivFin Us
  refine ⟨Fintype.card Us, fun i => (e.symm i).val, fun i => hUs (e.symm i).property, ?_⟩
  rw [hUssup, sSup_eq_iSup]
  exact le_antisymm (iSup_le fun i => le_iSup_of_le (e.symm i).val
      (le_iSup_of_le (e.symm i).property le_rfl))
    (iSup_le fun U' => iSup_le fun hU' => le_iSup_of_le (e ⟨U', hU'⟩) (by simp))

end Stacks.Cohomology.FiniteCover

namespace AlgebraicGeometry

open Stacks.Cohomology

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-! ### The vanishing input of the Euler characteristic -/

/-- Vanishing of the library's `Hgroup` over the whole space gives vanishing of the `k`-vector
space `AlgebraicGeometry.cohomologyOverField`. Restriction of scalars along the structure
morphism and the forgetful functor to abelian groups both leave the underlying set alone; this
is [Stacks, Tag 03FD] and [Stacks, Tag 01F1, part (1)] read on carriers. -/
theorem isZero_cohomologyOverField_of_isZero_Hgroup (F : X.Modules) (n : ℕ)
    (h : IsZero (Hgroup X.ringCatSheaf ⊤ n F)) : IsZero (cohomologyOverField k f F n) := by
  have hderived :=
    (FiniteCover.isZero_rightDerived_iff_isZero_Hgroup X F ⊤ n).2 h
  have hforget : IsZero ((forget₂ (ModuleCat.{u} (X.ringCatSheaf.obj.obj (op (⊤ : X.Opens))))
      AddCommGrpCat.{u}).obj
      (((SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))).rightDerived n).obj F)) :=
    IsZero.of_iso hderived
      ((ModuleComparison.rightDerivedSectionsForgetIso X.ringCatSheaf ⊤ n).app F)
  rw [ModuleCat.isZero_iff_subsingleton]
  exact AddCommGrpCat.subsingleton_of_isZero hforget

/-- **The vanishing input of [Stacks, Tag 0BEJ].** For a scheme proper over a field there is a
single degree beyond which the cohomology of *every* quasi-coherent module vanishes. -/
theorem exists_isZero_cohomologyOverField_of_isProper [IsProper f] :
    ∃ N : ℕ, ∀ F : X.Modules, F.IsQuasicoherent →
      ∀ n : ℕ, N ≤ n → IsZero (cohomologyOverField k f F n) := by
  have : CompactSpace X := (AlgebraicGeometry.quasiCompact_iff_compactSpace f).mp inferInstance
  have hsep : IsSeparated (terminal.from X) := by
    have : IsSeparated (f ≫ terminal.from (Spec (.of k))) := inferInstance
    simpa using this
  have : IsAffineHom (pullback.diagonal (terminal.from X)) := inferInstance
  obtain ⟨t, U, hU, hcover⟩ :=
    FiniteCover.exists_fin_affine_cover_of_isCompact X ⊤ isCompact_univ
  exact ⟨t, fun F _ n hn => isZero_cohomologyOverField_of_isZero_Hgroup k f F n
    (FiniteCover.isZero_Hgroup_of_finite_affine_cover X F U hU ⊤ hcover n hn)⟩

/-! ### Tag 08AA modulo finite dimensionality -/

/-- **[Stacks, Tag 08AA] with finite dimensionality of cohomology as its only hypothesis.** For
a proper scheme over a field and a short exact sequence `0 ⟶ ℱ₁ ⟶ ℱ₂ ⟶ ℱ₃ ⟶ 0` of coherent
modules, `χ(X, ℱ₂) = χ(X, ℱ₁) + χ(X, ℱ₃)`, given only that each `Hⁿ(X, ℱ₁)` and `Hⁿ(X, ℱ₃)` is
finite-dimensional over `k` — the content of [Stacks, Tag 02O6]. -/
@[ega "III 2.5.2" "special case"]
theorem eulerCharacteristic_add_of_shortExact_of_finiteDimensional [IsProper f]
    {S : ShortComplex X.Modules} (hS : S.ShortExact)
    [S.X₁.IsCoherent] [S.X₂.IsCoherent] [S.X₃.IsCoherent]
    (hfin₁ : ∀ n, FiniteDimensional k (cohomologyOverField k f S.X₁ n))
    (hfin₃ : ∀ n, FiniteDimensional k (cohomologyOverField k f S.X₃ n)) :
    eulerCharacteristic k f S.X₂ =
      eulerCharacteristic k f S.X₁ + eulerCharacteristic k f S.X₃ := by
  obtain ⟨N, hN⟩ := exists_isZero_cohomologyOverField_of_isProper k f
  exact eulerCharacteristic_add_of_shortExact_of_outer k f hS N
    (fun n _ => hfin₁ n) (fun n _ => hfin₃ n)
    (fun n hn => hN S.X₁ (isQuasicoherent_of_isCoherent S.X₁) n hn)
    (fun n hn => hN S.X₃ (isQuasicoherent_of_isCoherent S.X₃) n hn)

end AlgebraicGeometry

end
