module

public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.Topology.Sheaves.Abelian
public import Mathlib.Topology.Sheaves.Sheafify
public import Mathlib.Topology.Sheaves.Stalks
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective
public import StacksFrontier.AlgebraicGeometry.AffineCohomologyVanishing.CechReindex
public import StacksFrontier.Topology.Sheaves.Cohomology.CechVanishingCriteria.OnABasis
public import StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.SheafifiedCohomologyPresheaf
public import StacksFrontier.AlgebraicGeometry.Cohomology.Cech.StandardCoverVanishing
public import StacksFrontier.AlgebraicGeometry.Cohomology.Cech.AffineVanishing

/-!
# Cohomology of quasi-coherent modules on affine opens, and affine higher direct images

Let `X` be a scheme and `F` a quasi-coherent `𝒪_X`-module. [Stacks, Tag 01XB] asserts that
`Hᵖ(U, F) = 0` for every affine open `U ⊆ X` and every `p > 0`, and [Stacks, Tag 01XC] deduces
that `Rⁱ f_* F = 0` for `i > 0` whenever `f : X ⟶ S` is an affine morphism.

Tag 01XB is Čech theory. The affine opens of `X` form a basis, every open covering of an
affine open is refined by a covering by basic opens of a finite family of sections generating
the unit ideal, all the intersections occurring in the Čech complex of such a covering are
again affine opens, and the Čech cohomology of such a covering vanishes in positive degrees by
[Stacks, Tag 01X9]. So [Stacks, Tag 01EW] applies.

Tag 01XC is then local on the base. By [Stacks, Tag 01E4] the higher direct image `Rⁱ f_* F`
is the sheafification of the presheaf `V ↦ Hⁱ(f⁻¹(V), F)`. The preimage of an affine open is
affine because `f` is affine, so that presheaf vanishes on the affine opens; the affine opens
being a basis, all its stalks vanish, hence so does its sheafification.

## Main results

* `Stacks.Cohomology.Cech.isZero_hgroup_of_isAffineOpen` is [Stacks, Tag 01XB].
* `isZero_rightDerived_pushforward_of_isAffineHom` is [Stacks, Tag 01XC], and
  `isZero_rightDerivedPlus_pushforward_of_isAffineHom` is the same statement with the degree
  taken to be a natural number.

## Implementation notes

The index type of a `Stacks.Cohomology.Basis.OpenCover` is pinned to the universe of the
space, while [Stacks, Tag 01X9] is stated for a covering indexed by `Fin n`. The two Čech
complexes are compared by
`Stacks.CategoryTheory.CechComplex.isZero_homology_of_ulift`; nothing else is needed, because
the intersection selected by a tuple of lifted indices is the intersection selected by the
underlying tuple.

The vanishing of the sheafification is checked on stalks rather than by exhibiting a section:
`AddCommGrpCat.isZero_iff_subsingleton` turns vanishing of a group object into a
`Subsingleton`, and `TopCat.Presheaf.exists_mem_germ_eq_of_isBasis` writes any germ as the germ
of a section over a basis open.

## References

* [Stacks Project, Tag 01XB](https://stacks.math.columbia.edu/tag/01XB)
* [Stacks Project, Tag 01XC](https://stacks.math.columbia.edu/tag/01XC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry RingedSpaceModuleAdjunction
open scoped ZeroObject

universe u

attribute [local instance] HasDerivedCategory.standard
attribute [local instance]
  CategoryTheory.Limits.preservesBinaryBiproducts_of_preservesBinaryProducts

namespace Stacks.Cohomology.Affine

open Stacks.Cohomology.Basis Stacks.Cohomology.BasisCycles Stacks.Cohomology.Cech
open Stacks.CategoryTheory.CechComplex Stacks.Cohomology.HigherDirectImagePresheaf
open Stacks.RingTheory.CechAcyclicity

/-! ### Serre vanishing on an affine open -/

section Serre

variable {X : Scheme.{u}}

/-- A finite family of sections over an affine open `U` is a standard open covering of
`Spec Γ(X, U)` exactly when the basic opens it defines cover `U`. -/
private theorem isStandardOpenCoverOfSpectrum_iff_iSup_basicOpen_eq {U : X.Opens}
    (hU : IsAffineOpen U) {n : ℕ} (g : Fin n → Γ(X, U)) :
    PrimeSpectrum.IsStandardOpenCoverOfSpectrum g ↔ ⨆ i, X.basicOpen (g i) = U := by
  rw [PrimeSpectrum.IsStandardOpenCoverOfSpectrum, PrimeSpectrum.IsStandardOpenCover,
    PrimeSpectrum.basicOpen_one, PrimeSpectrum.iSup_basicOpen_eq_top_iff,
    ← hU.iSup_basicOpen_eq_self_iff (s := Set.range g), iSup_range']

/-- The covering of an affine open `U` of `X` by the ambient basic opens of a finite family of
sections whose basic opens cover `Spec Γ(X, U)`, packaged as an `OpenCover`. The index type of
an `OpenCover` lies in the universe of the space, so `Fin n` is lifted into it. -/
private noncomputable def standardOpenCover (U : X.Opens) (hU : IsAffineOpen U) {n : ℕ}
    (g : Fin n → Γ(X, U)) (hg : PrimeSpectrum.IsStandardOpenCoverOfSpectrum g) : OpenCover X where
  ι := ULift.{u} (Fin n)
  carrier := U
  obj i := X.basicOpen (g i.down)
  iSup_eq := by
    simpa using (isStandardOpenCoverOfSpectrum_iff_iSup_basicOpen_eq hU g).mp hg

/-- The positive-degree Čech cohomology of a quasi-coherent module vanishes for a standard
covering of an affine open. This is [Stacks, Tag 01X9] read through the universe lift of its
index type. -/
private theorem cechCohomologyIsZero_standardOpenCover (F : X.Modules) [F.IsQuasicoherent]
    (U : X.Opens) (hU : IsAffineOpen U) {n : ℕ} (g : Fin n → Γ(X, U))
    (hg : PrimeSpectrum.IsStandardOpenCoverOfSpectrum g) (q : ℕ) (hq : 0 < q) :
    CechCohomologyIsZero X.ringCatSheaf F (standardOpenCover U hU g hg) q :=
  isZero_homology_of_ulift (fun i ↦ X.basicOpen (g i))
    ((SheafOfModules.toSheaf X.ringCatSheaf).obj F).obj q
    (isZero_cechCohomology_of_isStandardOpenCover X F U hU g hg q hq)

/-- Every open covering of an affine open `V` of `X` is refined by a standard covering of `V`:
each point of `V` lies in a basic open of `V` contained in a member of the covering, and
finitely many of those already cover `V`. -/
private theorem exists_standardOpenCover_refines (V : X.Opens) (hV : IsAffineOpen V)
    (W : OpenCover X) (hWV : W.carrier = V) :
    ∃ (n : ℕ) (g : Fin n → Γ(X, V)) (hg : PrimeSpectrum.IsStandardOpenCoverOfSpectrum g),
      (standardOpenCover V hV g hg).Refines W := by
  classical
  have hlocal : ∀ x : V, ∃ (i : W.ι) (f : Γ(X, V)),
      X.basicOpen f ≤ W.obj i ∧ (x : X) ∈ X.basicOpen f := by
    intro x
    have hxcover : (x : X) ∈ ⨆ i, W.obj i := by
      rw [W.iSup_eq, hWV]
      exact x.2
    obtain ⟨i, hxi⟩ := Opens.mem_iSup.mp hxcover
    obtain ⟨A, hA, hxA, hAW⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open hxi (W.obj i).isOpen
    obtain ⟨A', hA', rfl⟩ := hA
    obtain ⟨f, g, hfg, hxfb⟩ :=
      exists_basicOpen_le_affine_inter hV hA' x.1 ⟨x.2, hxA⟩
    exact ⟨i, f, hfg ▸ (X.basicOpen_le g).trans hAW, hxfb⟩
  choose i₀ f₀ hsub₀ hx₀ using hlocal
  obtain ⟨t, ht⟩ := hV.isCompact.elim_finite_subcover
    (fun x : V ↦ (X.basicOpen (f₀ x) : Set X)) (fun x ↦ (X.basicOpen (f₀ x)).2)
    (fun x hx ↦ Set.mem_iUnion.2 ⟨⟨x, hx⟩, hx₀ ⟨x, hx⟩⟩)
  let e : t ≃ Fin (Fintype.card t) := Fintype.equivFin t
  refine ⟨Fintype.card t, fun j ↦ f₀ (e.symm j), ?_, hWV.symm, fun j ↦ ⟨i₀ (e.symm j.down), ?_⟩⟩
  · refine (isStandardOpenCoverOfSpectrum_iff_iSup_basicOpen_eq hV _).mpr ?_
    refine le_antisymm (iSup_le fun j ↦ X.basicOpen_le _) fun x hx ↦ ?_
    obtain ⟨y, hy, hxy⟩ := ht hx
    obtain ⟨y, rfl⟩ := hy
    obtain ⟨hy, hxy⟩ := Set.mem_iUnion.mp hxy
    exact le_iSup (fun j ↦ X.basicOpen (f₀ (e.symm j))) (e ⟨y, hy⟩) (by simpa using hxy)
  · simpa [standardOpenCover] using hsub₀ (e.symm j.down)

-- Stacks 01XB is `Stacks.Cohomology.Cech.isZero_hgroup_of_isAffineOpen`
-- (Cohomology/Cech/AffineVanishing.lean:304).  This is an alias spelling of that
-- declaration, not a second copy of it.
export Stacks.Cohomology.Cech (isZero_hgroup_of_isAffineOpen)

end Serre

/-! ### Higher direct images along an affine morphism -/

section HigherDirectImage

/-- A presheaf of abelian groups vanishing on a basis has vanishing stalks. -/
public theorem isZero_stalk_of_isZero_on_basis {T : TopCat.{u}} {B : Set (Opens T)}
    (hB : Opens.IsBasis B) (P : TopCat.Presheaf AddCommGrpCat.{u} T)
    (hP : ∀ U ∈ B, IsZero (P.obj (op U))) (x : T) : IsZero (P.stalk x) := by
  refine AddCommGrpCat.isZero_iff_subsingleton.mpr ⟨fun a b ↦ ?_⟩
  have hz (c : P.stalk x) : c = 0 := by
    obtain ⟨V, _hxV, hV, s, hs⟩ := TopCat.Presheaf.exists_mem_germ_eq_of_isBasis hB P x c
    rw [← hs, (AddCommGrpCat.isZero_iff_subsingleton.mp (hP V hV)).elim s 0]
    simp
  rw [hz a, hz b]

/-- A presheaf of abelian groups on a scheme vanishing on all affine opens has vanishing
sheafification. -/
private theorem isZero_sheafification_of_isZero_on_affineOpens {S : Scheme.{u}}
    (P : TopCat.Presheaf AddCommGrpCat.{u} (TopCat.of S))
    (hP : ∀ U ∈ S.affineOpens, IsZero (P.obj (op U))) :
    IsZero ((presheafToSheaf (Opens.grothendieckTopology (TopCat.of S))
      AddCommGrpCat.{u}).obj P) := by
  let J := Opens.grothendieckTopology (TopCat.of S)
  let F := (presheafToSheaf J AddCommGrpCat.{u}).obj P
  let Ftop : TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of S) := ⟨F.1, F.2⟩
  have hTop : IsZero Ftop := by
    rw [TopCat.Sheaf.isZero_iff_stalkFunctor_obj_isZero]
    intro x
    have hUnit : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        ((sheafificationAdjunction J AddCommGrpCat.{u}).unit.app P)) :=
      TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat.{u} P
    exact (isZero_stalk_of_isZero_on_basis S.isBasis_affineOpens P hP x).of_iso
      (asIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        ((sheafificationAdjunction J AddCommGrpCat.{u}).unit.app P))).symm
  have hFtop : ∀ V : (Opens (TopCat.of S))ᵒᵖ, IsZero (Ftop.presheaf.obj V) :=
    (Functor.isZero_iff _).mp
      (Functor.map_isZero (TopCat.Sheaf.forget AddCommGrpCat.{u} (TopCat.of S)) hTop)
  exact IsZero.of_full_of_faithful_of_isZero (sheafToPresheaf J AddCommGrpCat) F
    ((Functor.isZero_iff F.1).2 hFtop)

/-- **[Stacks, Tag 01XC] in a natural degree.** If `f : X ⟶ S` is an affine morphism of schemes
and `F` is a quasi-coherent `𝒪_X`-module, then `Rⁿ f_* F` vanishes for every `n > 0`. -/
theorem isZero_rightDerivedPlus_pushforward_of_isAffineHom {X S : Scheme.{u}} (f : X ⟶ S)
    (F : X.Modules) [IsAffineHom f] [F.IsQuasicoherent] (n : ℕ) (hn : 0 < n) :
    IsZero (((Scheme.Modules.pushforward f).rightDerivedPlus n).obj F) := by
  let RX := X.toLocallyRingedSpace.toRingedSpace
  let RS := S.toLocallyRingedSpace.toRingedSpace
  let g : RX ⟶ RS := f.toLRSHom.toShHom
  let _ : (modulePushforward g).IsRightAdjoint :=
    RingedSpaceModuleAdjunction.modulePushforward_isRightAdjoint g
  let _ : (modulePushforward g).Additive := Functor.additive_of_preservesBinaryBiproducts _
  let _ : (cohFunctor (opensMap g) (structureSheafRing RX) (structureSheafRing RS)
      (structureSheafHom g)).Additive := by
    change (modulePushforward g ⋙ SheafOfModules.forget (structureSheafRing RS)).Additive
    infer_instance
  let Q := ((cohFunctor (opensMap g) (structureSheafRing RX) (structureSheafRing RS)
    (structureSheafHom g)).rightDerived n).obj F
  have hP : ∀ U ∈ S.affineOpens,
      IsZero (((PresheafOfModules.toPresheaf (structureSheafRing RS).obj).obj Q).obj (op U)) := by
    intro U hU
    exact (Stacks.Cohomology.Cech.isZero_hgroup_of_isAffineOpen X F (f ⁻¹ᵁ U) (hU.preimage f) n
      hn).of_iso ((preimageCohomologyPresheaf_evaluation_iso g U n).app F)
  have hModuleSheaf :
      IsZero ((PresheafOfModules.sheafification (𝟙 (structureSheafRing RS).obj)).obj Q) := by
    let M := (PresheafOfModules.sheafification (𝟙 (structureSheafRing RS).obj)).obj Q
    let T := SheafOfModules.toSheaf (structureSheafRing RS)
    have hTM : IsZero (T.obj M) :=
      (isZero_sheafification_of_isZero_on_affineOpens _ hP).of_iso
        ((PresheafOfModules.sheafificationCompToSheaf (𝟙 (structureSheafRing RS).obj)).app Q)
    let z : M ⟶ 0 := (isZero_zero _).from_ M
    have hz : IsIso z :=
      (isIso_iff_of_reflects_iso z T).mp
        (isIso_of_source_target_iso_zero (T.map z) hTM.isoZero
          (T.map_isZero (isZero_zero _)).isoZero)
    exact (isZero_zero _).of_iso (asIso z)
  change IsZero (((modulePushforward g).rightDerivedPlus n).obj F)
  exact hModuleSheaf.of_iso ((higherDirectImage_iso_sheafify_preimageCohomology g n).app F)

/-- **[Stacks, Tag 01XC].** If `f : X ⟶ S` is an affine morphism of schemes and `F` is a
quasi-coherent `𝒪_X`-module, then `Rⁱ f_* F` vanishes for every `i > 0`. -/
@[stacks 01XC]
theorem isZero_rightDerived_pushforward_of_isAffineHom {X S : Scheme.{u}} (f : X ⟶ S)
    (F : X.Modules) [IsAffineHom f] [F.IsQuasicoherent] (i : ℤ) (hi : 0 < i) :
    IsZero (((Scheme.Modules.pushforward f).rightDerivedPlus i).obj F) := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, (n : ℤ) = i := ⟨i.toNat, Int.toNat_of_nonneg hi.le⟩
  exact isZero_rightDerivedPlus_pushforward_of_isAffineHom f F n (by exact_mod_cast hi)

end HigherDirectImage

end Stacks.Cohomology.Affine

end
