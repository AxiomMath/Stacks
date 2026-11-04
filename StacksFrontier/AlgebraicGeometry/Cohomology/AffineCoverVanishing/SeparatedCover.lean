module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import StacksFrontier.AlgebraicGeometry.Cohomology.AffineCoverVanishing.Basic

/-!
# Cohomological vanishing from a finite cover by separated opens

Let `X` be a quasi-compact and quasi-separated scheme and let `X = U₁ ∪ … ∪ Uₙ` be an open
covering with every `Uᵢ` quasi-compact and separated — for instance affine. Put
`d = max_{I ⊆ {1, …, n}} (|I| + t(⋂_{i ∈ I} Uᵢ) - 1)`, where `t` is the affine covering number.
Then the cohomology of every quasi-coherent `𝒪_X`-module vanishes in all degrees at least `d`.

## Main results

* `Stacks.Cohomology.AffineCover.isZero_cohomologyPresheaf_of_isSeparated_of_isCompact`: vanishing
  above the affine covering number of a quasi-compact separated open.
* `Stacks.Cohomology.AffineCover.isZero_cohomologyPresheaf_of_finset_separated_cover`:
  vanishing over a finite union of separated opens intersected with an open `T`, given that the
  finite intersections are quasi-compact.
* `Stacks.Cohomology.AffineCover.isZero_cohomologyPresheaf_of_finset_cover`: the same for a
  quasi-separated space, where the intersections are quasi-compact automatically.
* `Stacks.Cohomology.AffineCover.isZero_cohomologyPresheaf_of_finset_cover_of_inter_isCompact`:
  the same under the hypothesis that a quasi-compact open below `T` meets each member of the
  family in a quasi-compact open.
* `Stacks.Cohomology.AffineCover.isZero_cohomology_of_degree_ge_separatedCoverBound`: the bound
  attached to a finite covering by quasi-compact separated opens.

## Implementation notes

The maximum over subsets of the index set is `Finset.univ.sup` over `Finset (Fin n)`, and the
intersection over a subset is the indexed infimum over its membership predicate; inside the
induction the latter is handled as a `Finset.inf`. Vanishing is expressed in Mathlib's cohomology
presheaf, whose `Ext` universe is a free parameter.

## References

* [Stacks Project, Tag 071L](https://stacks.math.columbia.edu/tag/071L)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry RingedSpaceModuleAdjunction

namespace Stacks.Cohomology.AffineCover

universe u w

variable {X : Scheme.{u}}

/-- An open subscheme of a separated open subscheme is separated. -/
theorem isSeparated_inf_right (U V : X.Opens) (hU : Scheme.IsSeparated (U : Scheme)) :
    Scheme.IsSeparated ((U ⊓ V : X.Opens) : Scheme) := by
  let _ : Scheme.IsSeparated (U : Scheme) := hU
  have hcomp : IsSeparated
      (X.homOfLE (inf_le_left : U ⊓ V ≤ U) ≫ terminal.from (U : Scheme)) :=
    IsSeparated.comp_iff.mpr inferInstance
  have heq : X.homOfLE (inf_le_left : U ⊓ V ≤ U) ≫ terminal.from (U : Scheme) =
      terminal.from ((U ⊓ V : X.Opens) : Scheme) := terminal.hom_ext _ _
  exact ⟨heq ▸ hcomp⟩

/-- Two affine opens contained in a separated open subscheme meet in an affine open. -/
theorem isAffineOpen_inf_of_le_isSeparated {U V W : X.Opens}
    (hU : Scheme.IsSeparated (U : Scheme)) (hV : IsAffineOpen V) (hW : IsAffineOpen W)
    (hVU : V ≤ U) (hWU : W ≤ U) : IsAffineOpen (V ⊓ W) := by
  let _ : Scheme.IsSeparated (U : Scheme) := hU
  let _ : IsSeparated (terminal.from (U : Scheme)) :=
    Scheme.IsSeparated.isSeparated_terminal_from
  let _ : IsClosedImmersion (pullback.diagonal (terminal.from (U : Scheme))) :=
    IsSeparated.isClosedImmersion_diagonal
  let _ : IsAffineHom (pullback.diagonal (terminal.from (U : Scheme))) :=
    IsClosedImmersion.instIsAffineHom _
  have hrange : U.ι.opensRange = U := Scheme.Opens.opensRange_ι U
  have himg := ((hV.preimage_of_isOpenImmersion _ (hVU.trans hrange.ge)).inf
    (hW.preimage_of_isOpenImmersion _ (hWU.trans hrange.ge))).image_of_isOpenImmersion U.ι
  have heq : U.ι ''ᵁ (U.ι ⁻¹ᵁ V ⊓ U.ι ⁻¹ᵁ W) = V ⊓ W := by
    rw [show U.ι ⁻¹ᵁ V ⊓ U.ι ⁻¹ᵁ W = U.ι ⁻¹ᵁ (V ⊓ W) from rfl,
      Scheme.Hom.image_preimage_eq_opensRange_inf, hrange]
    exact inf_eq_right.mpr (inf_le_left.trans hVU)
  rwa [heq] at himg

section Vanishing

variable [HasExt.{u} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]

/-- The cohomology of a quasi-coherent `𝒪_X`-module over a quasi-compact separated open `U`
vanishes in every degree at least the least number of affine opens needed to cover `U`. -/
theorem isZero_cohomologyPresheaf_of_isSeparated_of_isCompact (U : X.Opens)
    (hUcompact : IsCompact (U : Set X)) (hUsep : Scheme.IsSeparated (U : Scheme))
    (F : X.Modules) [F.IsQuasicoherent] (p : ℕ)
    (hp : minimalAffineCoverCardinality U ≤ p) :
    IsZero ((((SheafOfModules.toSheaf X.ringCatSheaf).obj F).cohomologyPresheaf p).obj
      (op U)) := by
  classical
  obtain ⟨V, hV, hVcover⟩ := exists_affine_cover_card_eq U hUcompact
  refine isZero_cohomologyPresheaf_of_infClosed_cover
    (fun W ↦ IsAffineOpen W ∧ W ≤ U) ?_ (fun _ h ↦ h.1) V
    (fun i ↦ ⟨hV i, hVcover ▸ le_iSup V i⟩) U hVcover F p hp
  exact fun W W' hW hW' ↦
    ⟨isAffineOpen_inf_of_le_isSeparated hUsep hW.1 hW'.1 hW.2 hW'.2,
      inf_le_left.trans hW.2⟩

end Vanishing

/-- The cohomology groups of a quasi-coherent `𝒪_X`-module over a quasi-compact separated open
`U` vanish in every degree at least the affine covering number of `U`. -/
private lemma isZero_hgroup_of_isSeparated_of_isCompact (U : X.Opens)
    (hUcompact : IsCompact (U : Set X)) (hUsep : Scheme.IsSeparated (U : Scheme))
    (F : X.Modules) [F.IsQuasicoherent] (p : ℕ)
    (hp : minimalAffineCoverCardinality U ≤ p) :
    IsZero (Hgroup X.ringCatSheaf U p F) := by
  let _ : HasExt.{u} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) := inferInstance
  exact (isZero_hgroup_iff_isZero_cohomologyPresheaf U F p).mpr
    (isZero_cohomologyPresheaf_of_isSeparated_of_isCompact U hUcompact hUsep F p hp)

/-- If `T` is quasi-compact and every quasi-compact open below `T` meets each `V i` in a
quasi-compact open, then every `T ⊓ ⋂_{i ∈ J} Vᵢ` is quasi-compact. -/
private lemma isCompact_inf_finsetInf_of_inter (T : X.Opens) (hT : IsCompact (T : Set X))
    {ι : Type*} (V : ι → X.Opens)
    (hinter : ∀ (i : ι) (T' : X.Opens), T' ≤ T → IsCompact (T' : Set X) →
      IsCompact ((T' ⊓ V i : X.Opens) : Set X)) (J : Finset ι) :
    IsCompact ((T ⊓ J.inf V : X.Opens) : Set X) := by
  classical
  induction J using Finset.induction_on with
  | empty => simpa using hT
  | @insert a J _ ih =>
    rw [Finset.inf_insert, ← inf_assoc, inf_right_comm]
    exact hinter a (T ⊓ J.inf V) inf_le_left ih

/-- In a quasi-separated space, a quasi-compact open meets every finite intersection of
quasi-compact opens in a quasi-compact open. -/
private lemma isCompact_inf_finsetInf_of_quasiSeparatedSpace [QuasiSeparatedSpace X]
    (T : X.Opens) (hT : IsCompact (T : Set X)) {ι : Type*} (V : ι → X.Opens)
    (hV : ∀ i, IsCompact (V i : Set X)) (J : Finset ι) :
    IsCompact ((T ⊓ J.inf V : X.Opens) : Set X) :=
  isCompact_inf_finsetInf_of_inter T hT V (fun i T' _ hT' ↦ by
    simpa using QuasiSeparatedSpace.inter_isCompact (T' : Set X) (V i : Set X) T'.2 hT'
      (V i).2 (hV i)) J

section SeparatedCover

variable [HasExt.{w} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]

/-- Vanishing of the cohomology groups of a module over an open implies the vanishing of
Mathlib's cohomology presheaf there in every `Ext` universe. -/
private lemma isZero_cohomologyPresheaf_of_isZero_hgroup (U : X.Opens) (F : X.Modules) (n : ℕ)
    (h : IsZero (Hgroup X.ringCatSheaf U n F)) :
    IsZero ((((SheafOfModules.toSheaf X.ringCatSheaf).obj F).cohomologyPresheaf n).obj
      (op U)) := by
  let _ : HasExt.{u} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) := inferInstance
  have hExtU := (isZero_hgroup_iff_isZero_cohomologyPresheaf U F n).mp h
  let A := (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
    (yoneda.obj U ⋙ AddCommGrpCat.free)
  let H := (SheafOfModules.toSheaf X.ringCatSheaf).obj F
  have hsubU : Subsingleton (Ext.{u} A H n) := AddCommGrpCat.subsingleton_of_isZero hExtU
  have hsubW : Subsingleton (Ext.{w} A H n) :=
    ⟨fun x y ↦ (Ext.chgUniv.{w, u} (X := A) (Y := H) (n := n)).symm.injective
      (hsubU.elim _ _)⟩
  simpa [A, H, Sheaf.cohomologyPresheaf, Sheaf.cohomologyPresheafFunctor] using
    (AddCommGrpCat.isZero_iff_subsingleton.mpr hsubW)

/-- Let `V : ι → X.Opens` be separated opens and let `T` be an open meeting every finite
intersection of the `V i` in a quasi-compact open. If `|J| + t(T ⊓ ⋂_{i ∈ J} Vᵢ) - 1 ≤ d` for
every `J ⊆ I`, where `t` is the affine covering number, then the cohomology of every
quasi-coherent `𝒪_X`-module over `T ⊓ ⋃_{i ∈ I} Vᵢ` vanishes in every degree at least `d`. -/
theorem isZero_cohomologyPresheaf_of_finset_separated_cover {ι : Type*} (V : ι → X.Opens)
    (hVsep : ∀ i, Scheme.IsSeparated (V i : Scheme))
    (F : X.Modules) [F.IsQuasicoherent] (T : X.Opens) (I : Finset ι) (d : ℕ)
    (hc : ∀ J : Finset ι, IsCompact ((T ⊓ J.inf V : X.Opens) : Set X))
    (hd : ∀ J : Finset ι, J ⊆ I →
      J.card + minimalAffineCoverCardinality (T ⊓ J.inf V) - 1 ≤ d)
    (q : ℕ) (hq : d ≤ q) :
    IsZero ((((SheafOfModules.toSheaf X.ringCatSheaf).obj F).cohomologyPresheaf q).obj
      (op (T ⊓ I.sup V))) := by
  classical
  induction I using Finset.induction_on generalizing T d q with
  | empty =>
    refine isZero_cohomologyPresheaf_of_isZero_hgroup _ F q ?_
    rw [show T ⊓ (∅ : Finset ι).sup V = ⊥ by simp]
    exact isZero_hgroup_bot F q
  | @insert a I ha ih =>
    have hsingle : minimalAffineCoverCardinality (T ⊓ V a) ≤ d := by
      simpa using hd {a} (by simp)
    have hBcompact : IsCompact ((T ⊓ V a : X.Opens) : Set X) := by simpa using hc {a}
    have hBsep : Scheme.IsSeparated ((T ⊓ V a : X.Opens) : Scheme) := by
      simpa [inf_comm] using isSeparated_inf_right (V a) T (hVsep a)
    have hB := isZero_cohomologyPresheaf_of_isZero_hgroup (T ⊓ V a) F q
      (isZero_hgroup_of_isSeparated_of_isCompact (T ⊓ V a) hBcompact hBsep F q
        (hsingle.trans hq))
    by_cases hI : I = ∅
    · subst hI
      simpa [Finset.sup_insert, Finset.sup_empty] using hB
    obtain ⟨b, hb⟩ := Finset.nonempty_iff_ne_empty.mpr hI
    have hba : a ≠ b := fun hab ↦ ha (hab ▸ hb)
    have hposd : 1 ≤ d := by
      have h := hd (insert a {b}) (Finset.insert_subset_insert a (by simpa using hb))
      rw [show (insert a ({b} : Finset ι)).card = 2 by simp [hba]] at h
      omega
    have hA := ih T d hc
      (fun J hJ ↦ hd J (hJ.trans (Finset.subset_insert a I))) q hq
    have hc' : ∀ J : Finset ι, IsCompact (((T ⊓ V a) ⊓ J.inf V : X.Opens) : Set X) := by
      intro J
      have h := hc (insert a J)
      rwa [show (insert a J).inf V = V a ⊓ J.inf V by simp, ← inf_assoc] at h
    have hd' : ∀ J : Finset ι, J ⊆ I →
        J.card + minimalAffineCoverCardinality ((T ⊓ V a) ⊓ J.inf V) - 1 ≤ d - 1 := by
      intro J hJ
      have hk := hd (insert a J) (Finset.insert_subset_insert a hJ)
      rw [Finset.card_insert_of_notMem (fun h ↦ ha (hJ h)),
        show (insert a J).inf V = V a ⊓ J.inf V by simp] at hk
      have h : J.card + minimalAffineCoverCardinality (T ⊓ (V a ⊓ J.inf V)) - 1 ≤ d - 1 := by
        omega
      rwa [← inf_assoc] at h
    have hI' := ih (T ⊓ V a) (d - 1) hc' hd' (q - 1) (Nat.sub_le_sub_right hq 1)
    have hInter : IsZero
        ((((SheafOfModules.toSheaf X.ringCatSheaf).obj F).cohomologyPresheaf (q - 1)).obj
          (op ((T ⊓ I.sup V) ⊓ (T ⊓ V a)))) := by
      simpa [inf_assoc, inf_left_comm, inf_comm] using hI'
    let Sq := Opens.mayerVietorisSquare (T ⊓ I.sup V) (T ⊓ V a)
    have hsum : IsZero (((SheafOfModules.toSheaf X.ringCatSheaf).obj F).H' q Sq.X₂ ⊞
        ((SheafOfModules.toSheaf X.ringCatSheaf).obj F).H' q Sq.X₃) :=
      (biprod_isZero_iff _ _).2 ⟨by simpa [Sq] using hA, by simpa [Sq] using hB⟩
    have hseq := Sq.sequence_exact ((SheafOfModules.toSheaf X.ringCatSheaf).obj F)
      (q - 1) q (by omega)
    have hzero := (hseq.exact 2).isZero_of_both_isZero hInter hsum
    rw [show T ⊓ (insert a I).sup V = Sq.X₄ by
      simp [Sq, Opens.mayerVietorisSquare, Finset.sup_insert, inf_sup_left, sup_comm]]
    simpa [ComposableArrows.Precomp.obj, ComposableArrows.obj',
      ComposableArrows.mk₄, ComposableArrows.mk₃, ComposableArrows.mk₂] using hzero

/-- `isZero_cohomologyPresheaf_of_finset_separated_cover` on a quasi-separated space, for a
quasi-compact open `T` and quasi-compact separated opens `V i`. -/
theorem isZero_cohomologyPresheaf_of_finset_cover [QuasiSeparatedSpace X] {ι : Type*}
    (T : X.Opens) (hTcompact : IsCompact (T : Set X)) (V : ι → X.Opens)
    (hVcompact : ∀ i, IsCompact (V i : Set X))
    (hVsep : ∀ i, Scheme.IsSeparated (V i : Scheme))
    (F : X.Modules) [F.IsQuasicoherent] (I : Finset ι) (d : ℕ)
    (hd : ∀ J : Finset ι, J ⊆ I →
      J.card + minimalAffineCoverCardinality (T ⊓ J.inf V) - 1 ≤ d)
    (q : ℕ) (hq : d ≤ q) :
    IsZero ((((SheafOfModules.toSheaf X.ringCatSheaf).obj F).cohomologyPresheaf q).obj
      (op (T ⊓ I.sup V))) :=
  isZero_cohomologyPresheaf_of_finset_separated_cover V hVsep F T I d
    (isCompact_inf_finsetInf_of_quasiSeparatedSpace T hTcompact V hVcompact) hd q hq

/-- `isZero_cohomologyPresheaf_of_finset_separated_cover` for a quasi-compact open `T` such that
every quasi-compact open below `T` meets each `V i` in a quasi-compact open. -/
theorem isZero_cohomologyPresheaf_of_finset_cover_of_inter_isCompact {ι : Type*}
    (T : X.Opens) (hTcompact : IsCompact (T : Set X)) (V : ι → X.Opens)
    (_hVcompact : ∀ i, IsCompact (V i : Set X))
    (hVsep : ∀ i, Scheme.IsSeparated (V i : Scheme))
    (hinter : ∀ (i : ι) (T' : X.Opens), T' ≤ T → IsCompact (T' : Set X) →
      IsCompact ((T' ⊓ V i : X.Opens) : Set X))
    (F : X.Modules) [F.IsQuasicoherent] (I : Finset ι) (d : ℕ)
    (hd : ∀ J : Finset ι, J ⊆ I →
      J.card + minimalAffineCoverCardinality (T ⊓ J.inf V) - 1 ≤ d)
    (q : ℕ) (hq : d ≤ q) :
    IsZero ((((SheafOfModules.toSheaf X.ringCatSheaf).obj F).cohomologyPresheaf q).obj
      (op (T ⊓ I.sup V))) :=
  isZero_cohomologyPresheaf_of_finset_separated_cover V hVsep F T I d
    (isCompact_inf_finsetInf_of_inter T hTcompact V hinter) hd q hq

end SeparatedCover

/-- Let `X` be a quasi-compact quasi-separated scheme and let
`X = U₁ ∪ … ∪ Uₙ` be an open covering by quasi-compact separated opens — for example affine ones.
If `d = max_{I} (|I| + t(⋂_{i ∈ I} Uᵢ) - 1)`, where `t` is the affine covering number, then the
cohomology of every quasi-coherent `𝒪_X`-module vanishes in every degree at least `d`. -/
@[stacks 071L]
theorem isZero_cohomology_of_degree_ge_separatedCoverBound {X : Scheme.{u}} [CompactSpace X]
    [QuasiSeparatedSpace X]
    [HasExt.{w} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]
    {n d : ℕ} (U : Fin n → X.Opens) (hU : ⨆ i, U i = ⊤)
    (hU_compact : ∀ i, IsCompact (U i : Set X))
    (hU_separated : ∀ i, Scheme.IsSeparated (U i : Scheme))
    (hd : d = Finset.univ.sup fun I : Finset (Fin n) ↦
      I.card + minimalAffineCoverCardinality (⨅ i ∈ I, U i) - 1)
    (F : X.Modules) [F.IsQuasicoherent] (p : ℕ) (hp : d ≤ p) :
    IsZero ((((SheafOfModules.toSheaf X.ringCatSheaf).obj F).cohomologyPresheaf p).obj
      (op (⊤ : X.Opens))) := by
  classical
  have hbound : ∀ J : Finset (Fin n), J ⊆ Finset.univ →
      J.card + minimalAffineCoverCardinality (⊤ ⊓ J.inf U) - 1 ≤ d := by
    intro J _
    rw [hd]
    simpa [Finset.inf_eq_iInf] using Finset.le_sup (f := fun I : Finset (Fin n) ↦
      I.card + minimalAffineCoverCardinality (⨅ i ∈ I, U i) - 1) (Finset.mem_univ J)
  have hvan := isZero_cohomologyPresheaf_of_finset_cover (⊤ : X.Opens)
    (by simpa using (isCompact_univ : IsCompact (Set.univ : Set X)))
    U hU_compact hU_separated F Finset.univ d hbound p hp
  have hcover : Finset.univ.sup U = ⊤ := by simpa [Finset.sup_eq_iSup] using hU
  simpa [hcover] using hvan

end Stacks.Cohomology.AffineCover

end
