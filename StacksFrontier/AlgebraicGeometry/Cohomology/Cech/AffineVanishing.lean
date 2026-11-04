module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Topology.Sheaves.Cohomology.CechVanishingCriteria.OnABasisDegreeOne
public import StacksFrontier.Topology.Sheaves.Cohomology.CechVanishingCriteria.OnABasis
public import StacksFrontier.AlgebraicGeometry.Cohomology.Cech.StandardCoverVanishing

/-!
# Vanishing of the higher cohomology of a quasi-coherent module on an affine open

Let `X` be a scheme and let `F` be a quasi-coherent `𝒪_X`-module. This file proves that
`Hᵖ(U, F) = 0` for every affine open `U` of `X` and every `p > 0`.

The proof applies the basis criterion
`Stacks.Cohomology.BasisCycles.isZero_hgroup_of_cech_isZero_on_basis` to the basis `X.affineOpens`
of affine opens and to the collection `Cov` of those open covers of an affine open `V` that are
given by the ambient basic opens `X.basicOpen (g i)` of a finite family `g` of sections over `V`
whose basic opens cover `Spec Γ(X, V)`. Three things have to be checked. The members of such a
cover, and the finite intersections of its members, are again affine opens: the intersection
selected by a tuple is the basic open of the product of the selected sections, by
`Stacks.Cohomology.Cech.basicOpen_tupleProd`. The collection is cofinal: an arbitrary open cover
of an affine open `V` is refined by one of these, because each point of `V` lies in a basic open
of `V` contained in a member of the given cover, and finitely many of those basic opens already
cover the quasi-compact space `V`. Finally the positive-degree Čech cohomology of such a cover
vanishes, which is `Stacks.Cohomology.Cech.isZero_cechCohomology_of_isStandardOpenCover`.

## Main results

* `Stacks.Cohomology.Cech.isZero_hgroup_of_isAffineOpen`: the positive-degree cohomology of a
  quasi-coherent module on an affine open of a scheme vanishes.

## Implementation notes

Cohomology is the derived-functor model `Stacks.Cohomology.Hgroup`, and vanishing of the
resulting object of `AddCommGrpCat` is expressed by `CategoryTheory.Limits.IsZero`.

An `Stacks.Cohomology.Basis.OpenCover` of a space in `Type u` is indexed by a type in `Type u`,
whereas the standard covers above are indexed by `Fin n`, so the covers fed to the basis
criterion are indexed by `ULift.{u} (Fin n)` and the Čech vanishing has to be transported along
that reindexing. This is done on cochains: the private section below transfers
`Stacks.Cohomology.BasisCycles.CechSurj`, the element form of Čech vanishing, from a family to
its reindexing along `ULift`. `Stacks.Cohomology.BasisCycles.cechSurj_of_uliftFamily` is the
converse transfer, and is stated only for an index type living in the universe of the space,
which `Fin n` does not.

## References

* [Stacks Project, Tag 01XB](https://stacks.math.columbia.edu/tag/01XB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open Stacks.CategoryTheory.CechComplex

universe t t' v u

namespace Stacks.Cohomology.Cech

/-! ### Transporting Čech vanishing along a reindexing by `ULift`

A family of open subsets indexed by `κ` and its reindexing along `ULift.down` have the same
intersections, so a Čech cochain for one is a Čech cochain for the other. This transfers the
element form of Čech vanishing from the family to its reindexing. -/

section ULiftReindex

open Stacks.Cohomology.Basis Stacks.Cohomology.BasisCycles

noncomputable section

variable {T : Type u} [TopologicalSpace T] {κ : Type t} (Y : κ → Opens T)
  (P : (Opens T)ᵒᵖ ⥤ AddCommGrpCat.{v})
  [HasProducts.{t} AddCommGrpCat.{v}] [HasProducts.{max t t'} AddCommGrpCat.{v}]

omit [HasProducts.{t} AddCommGrpCat.{v}] [HasProducts.{max t t'} AddCommGrpCat.{v}] in
/-- If the components of a cochain `s'` for `B` are restrictions of those of a cochain `s` for `A`
along a reindexing `φ`, then the same holds for their Čech differentials. -/
private theorem comp_dd_of_comp_eq {κ₁ : Type*} {κ₂ : Type*}
    [HasProducts.{u_1} AddCommGrpCat.{v}] [HasProducts.{u_2} AddCommGrpCat.{v}]
    {A : κ₁ → Opens T} {B : κ₂ → Opens T}
    (φ : κ₂ → κ₁) (hle : ∀ {m : ℕ} (x : Fin m → κ₂), inter B x ≤ inter A (φ ∘ x)) {q : ℕ}
    (s : Cochain A P q) (s' : Cochain B P q)
    (h : ∀ x, comp B P s' x = res P (hle x) (comp A P s (φ ∘ x))) (x : Fin (q + 2) → κ₂) :
    comp B P (dd B P s') x = res P (hle x) (comp A P (dd A P s) (φ ∘ x)) := by
  rw [comp_dd, comp_dd, res_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [h, res_res, res_zsmul, res_res]
  exact congrArg _ (res_comp_congr A P s rfl _ _)

omit [HasProducts.{t} AddCommGrpCat.{v}] [HasProducts.{max t t'} AddCommGrpCat.{v}] in
/-- A section over the intersection selected by the underlying tuple restricts to the
intersection selected by a tuple of lifted indices. -/
private theorem inter_ulift_le {m : ℕ} (x : Fin m → ULift.{t'} κ) :
    inter (fun i : ULift.{t'} κ => Y i.down) x ≤ inter Y fun a => (x a).down :=
  by rw [inter_eq_iInf, inter_eq_iInf]

omit [HasProducts.{t} AddCommGrpCat.{v}] [HasProducts.{max t t'} AddCommGrpCat.{v}] in
/-- A section over the intersection selected by a tuple of lifted indices restricts to the
intersection selected by the underlying tuple. -/
private theorem le_inter_ulift {m : ℕ} (y : Fin m → κ) :
    inter Y y ≤ inter (fun i : ULift.{t'} κ => Y i.down) fun a => ULift.up (y a) :=
  by rw [inter_eq_iInf, inter_eq_iInf]

/-- The components of a Čech cochain, read as components of a cochain for the reindexed
family. -/
private def liftCochainComp {q : ℕ} (s : Cochain Y P q) (x : Fin (q + 1) → ULift.{t'} κ) :
    ToType (P.obj (op (inter (fun i : ULift.{t'} κ => Y i.down) x))) :=
  res P (inter_ulift_le Y x) (comp Y P s fun a => (x a).down)

/-- The components of a Čech cochain for the reindexed family, read as components of a cochain
for the original family. -/
private def lowerCochainComp {q : ℕ} (s : Cochain (fun i : ULift.{t'} κ => Y i.down) P q)
    (y : Fin (q + 1) → κ) : ToType (P.obj (op (inter Y y))) :=
  res P (le_inter_ulift Y y)
    (comp (fun i : ULift.{t'} κ => Y i.down) P s fun a => ULift.up (y a))

/-- A Čech cochain for the family, read as a Čech cochain for the reindexed family. -/
private def liftCochain {q : ℕ} (s : Cochain Y P q) :
    Cochain (fun i : ULift.{t'} κ => Y i.down) P q :=
  BasisCycles.mk (fun i : ULift.{t'} κ => Y i.down) P (liftCochainComp Y P s)

/-- A Čech cochain for the reindexed family, read as a Čech cochain for the family. -/
private def lowerCochain {q : ℕ} (s : Cochain (fun i : ULift.{t'} κ => Y i.down) P q) :
    Cochain Y P q :=
  BasisCycles.mk Y P (lowerCochainComp Y P s)

/-- The components of a cochain read for the reindexed family. -/
private theorem comp_liftCochain {q : ℕ} (s : Cochain Y P q) (x : Fin (q + 1) → ULift.{t'} κ) :
    comp (fun i : ULift.{t'} κ => Y i.down) P (liftCochain Y P s) x =
      res P (inter_ulift_le Y x) (comp Y P s fun a => (x a).down) :=
  comp_mk (fun i : ULift.{t'} κ => Y i.down) P (liftCochainComp Y P s) x

/-- The components of a cochain for the reindexed family, read back. -/
private theorem comp_lowerCochain {q : ℕ}
    (s : Cochain (fun i : ULift.{t'} κ => Y i.down) P q) (y : Fin (q + 1) → κ) :
    comp Y P (lowerCochain Y P s) y = res P (le_inter_ulift Y y)
      (comp (fun i : ULift.{t'} κ => Y i.down) P s fun a => ULift.up (y a)) :=
  comp_mk Y P (lowerCochainComp Y P s) y

/-- Reading a cochain for the reindexed family back kills the zero cochain. -/
private theorem lowerCochain_zero {q : ℕ} :
    lowerCochain Y P (0 : Cochain (fun i : ULift.{t'} κ => Y i.down) P q) = 0 := by
  refine cochain_ext Y P _ _ fun y => ?_
  rw [comp_lowerCochain, BasisCycles.comp_zero, BasisCycles.comp_zero, res_zero]

/-- Reading a cochain for the reindexed family commutes with the Čech differential. -/
private theorem dd_lowerCochain {q : ℕ}
    (s : Cochain (fun i : ULift.{t'} κ => Y i.down) P q) :
    dd Y P (lowerCochain Y P s)
      = lowerCochain Y P (dd (fun i : ULift.{t'} κ => Y i.down) P s) :=
  cochain_ext Y P _ _ fun y => (comp_dd_of_comp_eq P ULift.up (le_inter_ulift Y) s _
    (comp_lowerCochain Y P s) y).trans (comp_lowerCochain Y P _ y).symm

/-- Reading a cochain for the reindexed family commutes with the Čech differential. -/
private theorem dd_liftCochain {q : ℕ} (s : Cochain Y P q) :
    dd (fun i : ULift.{t'} κ => Y i.down) P (liftCochain Y P s)
      = liftCochain Y P (dd Y P s) :=
  cochain_ext _ P _ _ fun x => (comp_dd_of_comp_eq P ULift.down (inter_ulift_le Y) s _
    (comp_liftCochain Y P s) x).trans (comp_liftCochain Y P _ x).symm

/-- Reading a cochain for the reindexed family back and then forth is the identity. -/
private theorem liftCochain_lowerCochain {q : ℕ}
    (s : Cochain (fun i : ULift.{t'} κ => Y i.down) P q) :
    liftCochain Y P (lowerCochain Y P s) = s := by
  refine cochain_ext (fun i : ULift.{t'} κ => Y i.down) P _ _ fun x => ?_
  rw [comp_liftCochain, comp_lowerCochain, res_res,
    res_comp_congr (fun i : ULift.{t'} κ => Y i.down) P s rfl _
      (le_refl (inter (fun i : ULift.{t'} κ => Y i.down) x)), res_id]

/-- **Čech vanishing is insensitive to reindexing along `ULift`.** If every Čech cocycle for a
family of open subsets is a Čech coboundary, the same holds for the reindexing of that family
along `ULift.down`. -/
private theorem cechSurj_ulift (q : ℕ) (h : CechSurj Y P q) :
    CechSurj (fun i : ULift.{t'} κ => Y i.down) P q := by
  intro s hs
  obtain ⟨b, hb⟩ := h (lowerCochain Y P s) (by rw [dd_lowerCochain, hs, lowerCochain_zero])
  exact ⟨liftCochain Y P b, by rw [dd_liftCochain, hb, liftCochain_lowerCochain]⟩

end

end ULiftReindex

/-! ### The standard covers of an affine open -/

section Vanishing

open Stacks.Cohomology.Basis

variable {X : Scheme.{u}}

/-- The cover of an affine open `U` of `X` by the ambient basic opens `X.basicOpen (g i)` of a
finite family `g` of sections over `U` whose basic opens cover `Spec Γ(X, U)`, indexed by a
universe-lifted copy of `Fin n` so as to be an `Stacks.Cohomology.Basis.OpenCover`. -/
private def standardOpenCover {U : X.Opens} (hU : IsAffineOpen U) {n : ℕ} (g : Fin n → Γ(X, U))
    (hg : PrimeSpectrum.IsStandardOpenCoverOfSpectrum g) : OpenCover X where
  ι := ULift.{u} (Fin n)
  carrier := U
  obj := fun i => X.basicOpen (g i.down)
  iSup_eq := by
    rw [iSup_ulift]
    simpa only [iSup_range'] using (hU.iSup_basicOpen_eq_self_iff (s := Set.range g)).mpr
      (span_range_eq_top_of_isStandardOpenCoverOfSpectrum hg)

/-- The intersection of the basic opens selected by a tuple of sections over an affine open is
again an affine open: it is the basic open of the product of the selected sections. -/
private theorem iInf_basicOpen_isAffineOpen {U : X.Opens} (hU : IsAffineOpen U) {n m : ℕ}
    (g : Fin n → Γ(X, U)) (s : Fin (m + 1) → Fin n) :
    IsAffineOpen (⨅ k, X.basicOpen (g (s k))) := by
  rw [← basicOpen_tupleProd g s]
  exact hU.basicOpen _

/-- The collection of standard covers of the affine opens of `X`: an open cover belongs to it
when it is the cover of an affine open by the ambient basic opens of a finite family of sections
whose basic opens cover the spectrum of the sections over that affine open. -/
private def standardCovers (X : Scheme.{u}) : Set (OpenCover X) :=
  {C | ∃ (V : X.Opens) (hV : IsAffineOpen V) (n : ℕ) (g : Fin n → Γ(X, V))
    (hg : PrimeSpectrum.IsStandardOpenCoverOfSpectrum g), C = standardOpenCover hV g hg}

/-- Every member and every finite intersection of members of a standard cover is an affine
open. -/
private theorem affineOpens_of_mem_standardCovers (C : OpenCover X) (hC : C ∈ standardCovers X) :
    C.carrier ∈ X.affineOpens ∧ (∀ i, C.obj i ∈ X.affineOpens) ∧
      ∀ (q : ℕ) (s : Fin (q + 1) → C.ι), (⨅ k, C.obj (s k)) ∈ X.affineOpens := by
  obtain ⟨V, hV, n, g, hg, rfl⟩ := hC
  refine ⟨hV, fun i => hV.basicOpen _, fun q s => ?_⟩
  exact iInf_basicOpen_isAffineOpen hV g fun k => (s k).down

/-- **The standard covers are cofinal.** Every open cover of an affine open `V` of `X` is refined
by the cover of `V` by the ambient basic opens of a finite family of sections over `V` whose basic
opens cover `Spec Γ(X, V)`.

Each point of `V` lies in a basic open of `V` contained in a member of the given cover, because
the affine opens form a basis and two affine opens meet in a union of basic opens of each; `V` is
quasi-compact, so finitely many of these basic opens already cover `V`. -/
private theorem exists_mem_standardCovers_refines {V : X.Opens} (hV : IsAffineOpen V)
    (W : OpenCover X) (hWV : W.carrier = V) :
    ∃ C ∈ standardCovers X, C.carrier = V ∧ C.Refines W := by
  classical
  have hlocal : ∀ x : V, ∃ (i : W.ι) (f : Γ(X, V)),
      X.basicOpen f ≤ W.obj i ∧ (x : X) ∈ X.basicOpen f := by
    intro x
    obtain ⟨i, hxi⟩ := Opens.mem_iSup.mp (W.iSup_eq ▸ (hWV ▸ x.2 : (x : X) ∈ W.carrier))
    obtain ⟨A, hA, hxA, hAW⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open hxi (W.obj i).isOpen
    obtain ⟨A', hA', rfl⟩ := hA
    obtain ⟨f, g, hfg, hxfb⟩ :=
      exists_basicOpen_le_affine_inter hV hA' x.1 ⟨x.2, hxA⟩
    exact ⟨i, f, hfg ▸ (X.basicOpen_le g).trans hAW, hxfb⟩
  choose i₀ f₀ hsub₀ hx₀ using hlocal
  obtain ⟨t, ht⟩ := hV.isCompact.elim_finite_subcover
    (fun x : V => (X.basicOpen (f₀ x) : Set X)) (fun x => (X.basicOpen (f₀ x)).2)
    (fun x hx => Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hx₀ ⟨x, hx⟩⟩)
  let e : t ≃ Fin (Fintype.card t) := Fintype.equivFin t
  let f : Fin (Fintype.card t) → Γ(X, V) := fun j => f₀ (e.symm j)
  have hcover : (⨆ j, X.basicOpen (f j)) = V := by
    refine le_antisymm (iSup_le fun j => X.basicOpen_le _) fun x hx => ?_
    obtain ⟨y, hy, hxy⟩ := ht hx
    obtain ⟨y, rfl⟩ := hy
    obtain ⟨hy, hxy⟩ := Set.mem_iUnion.mp hxy
    exact (le_iSup (fun j => X.basicOpen (f j)) (e ⟨y, hy⟩)) (by simpa [f] using hxy)
  have hg : PrimeSpectrum.IsStandardOpenCoverOfSpectrum f := by
    change (⨆ j, PrimeSpectrum.basicOpen (f j)) = PrimeSpectrum.basicOpen (1 : Γ(X, V))
    rw [PrimeSpectrum.basicOpen_one]
    exact PrimeSpectrum.iSup_basicOpen_eq_top_iff.mpr
      ((hV.iSup_basicOpen_eq_self_iff (s := Set.range f)).mp (by
        simpa only [iSup_range'] using hcover))
  refine ⟨standardOpenCover hV f hg, ⟨V, hV, Fintype.card t, f, hg, rfl⟩, rfl,
    hWV.symm, fun j => ⟨i₀ (e.symm j.down), ?_⟩⟩
  simpa only [standardOpenCover, f] using hsub₀ (e.symm j.down)

/-- **Čech vanishing for the standard covers, in element form.** Every Čech cocycle of positive
degree for a standard cover of an affine open, with coefficients in a quasi-coherent module, is a
Čech coboundary. -/
private theorem cechSurj_standardOpenCover (F : X.Modules) [F.IsQuasicoherent] {V : X.Opens}
    (hV : IsAffineOpen V) {n : ℕ} (g : Fin n → Γ(X, V))
    (hg : PrimeSpectrum.IsStandardOpenCoverOfSpectrum g) (q : ℕ) :
    Stacks.Cohomology.BasisCycles.CechSurj
      (fun i : ULift.{u} (Fin n) => X.basicOpen (g i.down))
      ((SheafOfModules.toSheaf X.ringCatSheaf).obj F).obj q :=
  cechSurj_ulift (fun i : Fin n => X.basicOpen (g i))
      ((SheafOfModules.toSheaf X.ringCatSheaf).obj F).obj q
    ((Stacks.Cohomology.BasisCycles.cechSurj_iff_isZero_homology
        (fun i : Fin n => X.basicOpen (g i))
        ((SheafOfModules.toSheaf X.ringCatSheaf).obj F).obj q).2
      (isZero_cechCohomology_of_isStandardOpenCover X F V hV g hg (q + 1) (Nat.succ_pos q)))

/-- **Čech vanishing for the standard covers.** The positive-degree Čech cohomology of a
quasi-coherent module vanishes for every standard cover of an affine open. -/
private theorem cechCohomologyIsZero_of_mem_standardCovers (F : X.Modules) [F.IsQuasicoherent]
    (C : OpenCover X) (hC : C ∈ standardCovers X) (q : ℕ) (hq : 0 < q) :
    CechCohomologyIsZero X.ringCatSheaf F C q := by
  obtain ⟨V, hV, n, g, hg, rfl⟩ := hC
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hq.ne'
  exact (Stacks.Cohomology.BasisCycles.cechSurj_iff_isZero_homology
      (fun i : ULift.{u} (Fin n) => X.basicOpen (g i.down))
      ((SheafOfModules.toSheaf X.ringCatSheaf).obj F).obj q).1
    (cechSurj_standardOpenCover F hV g hg q)

/-- **Serre vanishing on affine schemes.** The positive-degree cohomology of a
quasi-coherent module on an affine open of a scheme vanishes. -/
@[stacks 01XB, ega "III 1.3.1" "more general", ega "I 5.1.9.2" "more general", ega "II 5.2.4"]
theorem isZero_hgroup_of_isAffineOpen (X : Scheme.{u}) (F : X.Modules)
    [F.IsQuasicoherent] (U : X.Opens) (hU : IsAffineOpen U) (p : ℕ) (hp : 0 < p) :
    IsZero (Hgroup X.ringCatSheaf U p F) :=
  Stacks.Cohomology.BasisCycles.isZero_hgroup_of_cech_isZero_on_basis X.ringCatSheaf F
    X.affineOpens X.isBasis_affineOpens (standardCovers X)
    affineOpens_of_mem_standardCovers
    (fun _ hV W hWV => exists_mem_standardCovers_refines hV W hWV)
    (cechCohomologyIsZero_of_mem_standardCovers F) U hU p hp

end Vanishing

end Stacks.Cohomology.Cech

end
