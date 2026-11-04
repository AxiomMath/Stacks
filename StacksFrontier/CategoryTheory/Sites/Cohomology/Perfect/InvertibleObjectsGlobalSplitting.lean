module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.InvertibleObjectsGlobalPairing
public import StacksFrontier.Topology.Sheaves.Cohomology.InvertibleDerivedGlobalSplitting
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.UnitFinitePresentationSite

/-!
# A chain-level tensor pairing of finite free summands splits the cohomology, on a ringed site

Let `(C, O)` be a ringed site and let `E`, `F` be bounded complexes of direct summands of finite
free `O`-modules with `Tot(E ⊗ F)` homotopy equivalent to `O[0]`. Then there are finitely many
orthogonal idempotents `f_n` of `R = Γ(C, O)` summing to `1` such that `f_n` acts on `H^k(E)` as
the identity for `k = n` and as zero otherwise, on `H^k(F)` as the identity for `k = -n` and as
zero otherwise, no nonzero local section of `O` annihilates all `H^k(E)`, and
`H^n(E) ⊗ H^{-n}(F)` is the image of `f_n` on `O`.

This is the step of the proof of `(1) ⟹ (2)` of Stacks 0FPY which applies Stacks 0FNT to the
global sections — "By More on Algebra, Lemma 0FNT we find a product decomposition
`R = ∏ R_n` and invertible `R_n`-modules `H^n` such that `M^• ≅ ⨁ H^n[-n]`" — and carries the
result back to the sheaves by Stacks 0FPX.

## References

* [Stacks Project, Tag 0FPY](https://stacks.math.columbia.edu/tag/0FPY)
* [Stacks Project, Tag 0FNT](https://stacks.math.columbia.edu/tag/0FNT)
* [Stacks Project, Tag 0FPX](https://stacks.math.columbia.edu/tag/0FPX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open Opposite Stacks.Cohomology.SiteModules Stacks.SheafOfModules.DerivedMonoidal
open DerivedCategory.Invertible

universe u

namespace AlgebraicGeometry.RingedSite.InvertibleDerived

open Stacks.Cohomology.InvertibleDerived (ActsOnHomology splitObj splitι splitπ splitπ_splitι
  tensorFlipIso mem_ideal_of_tensor mapSplitObjIso)

variable (X : RingedSite.{u, u, u}) [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

variable {X} in
/-- A global section of `O`, read as an element of `GlobalSection`. -/
def toGS (r : GammaRing X) : GlobalSection X where
  val U := r.1 U
  map_val _ _ f := r.2 f

/-- **The ring-level splitting.** -/
theorem exists_ring_splitting
    (E F : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hE : ∀ i, _root_.IsDirectSummandOfFiniteFree _ (E.X i))
    (hF : ∀ i, _root_.IsDirectSummandOfFiniteFree _ (F.X i))
    (a b a' b' : ℤ) (hEz : ∀ i, (i < a ∨ b < i) → IsZero (E.X i))
    (hFz : ∀ i, (i < a' ∨ b' < i) → IsZero (F.X i))
    (h : HomotopyEquiv (HomologicalComplex.mapBifunctor E F
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ))
      ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj (SheafOfModules.unit _))) :
    let P := ((gammaF X).mapHomologicalComplex (ComplexShape.up ℤ)).obj E
    let P' := ((gammaF X).mapHomologicalComplex (ComplexShape.up ℤ)).obj F
    ∃ (S : Finset ℤ) (f : ℤ → GammaRing X), (∀ n, IsIdempotentElem (f n)) ∧
      (∀ n m, n ≠ m → f n * f m = 0) ∧ (∀ n ∉ S, f n = 0) ∧ ∑ n ∈ S, f n = 1 ∧
      ActsOnHomology (fun n => scalarNatTrans (f n)) P ∧
      ActsOnHomology (fun n => scalarNatTrans (f (-n))) P' ∧
      Nonempty (HomotopyEquiv P (CochainComplex.zeroDifferentialComplex fun k => P.homology k)) ∧
      Nonempty (HomotopyEquiv P' (CochainComplex.zeroDifferentialComplex fun k => P'.homology k)) ∧
      ∀ n, Nonempty (P.homology n ⊗ P'.homology (-n) ≅
        splitObj ((scalarNatTrans (f n)).app (ModuleCat.of (GammaRing X) (GammaRing X)))) := by
  intro P P'
  have hPproj : ∀ i, Projective (P.X i) := fun i =>
    (IsProjective.iff_projective (R := GammaRing X) (P := P.X i)).mp
      (gamma_finite_projective X (E.X i) (hE i)).2
  have hP'proj : ∀ i, Projective (P'.X i) := fun i =>
    (IsProjective.iff_projective (R := GammaRing X) (P := P'.X i)).mp
      (gamma_finite_projective X (F.X i) (hF i)).2
  have : CochainComplex.IsStrictlyLE P b :=
    (CochainComplex.isStrictlyLE_iff P b).mpr fun i hi =>
    (gammaF X).map_isZero (hEz i (Or.inr hi))
  have : CochainComplex.IsStrictlyLE P' b' :=
    (CochainComplex.isStrictlyLE_iff P' b').mpr fun i hi =>
    (gammaF X).map_isZero (hFz i (Or.inr hi))
  let hT := gammaTensorHomotopyEquiv X E F hE hF a b hEz h
  let hT' := (HomotopyEquiv.ofIso (tensorFlipIso P' P)).trans hT
  have hinv := isInvertible_Q_of_homotopyEquiv P P' b b' hPproj hP'proj hT
  have hinv' := isInvertible_Q_of_homotopyEquiv P' P b' b hP'proj hPproj hT'
  obtain ⟨S, f, fidem, fortho, fzero, fsum, fact, fhom⟩ := exists_idempotents_of_isInvertible P hinv
  obtain ⟨S', g, gidem, -, gzero, gsum, gact, ghom⟩ := exists_idempotents_of_isInvertible P' hinv'
  obtain ⟨eZ⟩ := nonempty_homotopyEquiv_zeroDifferential P b hPproj f fidem fact
    (fun k => (fhom k).2)
  obtain ⟨eZ'⟩ := nonempty_homotopyEquiv_zeroDifferential P' b' hP'proj g gidem gact
    (fun k => (ghom k).2)
  let hZZ : HomotopyEquiv (CochainComplex.zeroDifferentialComplex (fun k => P.homology k) ⊗
      CochainComplex.zeroDifferentialComplex (fun k => P'.homology k))
      (𝟙_ (CochainComplex (ModuleCat.{u} (GammaRing X)) ℤ)) :=
    (HomologicalComplex.mapBifunctorHomotopyEquiv _ _ eZ.symm eZ'.symm).trans hT
  let Φ := degreeZeroIsoOfHomotopyEquiv _ _ hZZ
  have hgf : ∀ n, g (-n) = f n := eq_neg_of_complete _ _ f g S S' fzero gzero fsum gsum fact gact Φ
  obtain rfl : g = fun n => f (-n) := funext fun n => by rw [← hgf (-n), neg_neg]
  exact ⟨S, f, fidem, fortho, fzero, fsum, fact, gact, ⟨eZ⟩, ⟨eZ'⟩,
    fun n => ⟨tensorIsoSplitObjOfIso _ _ n f fact Φ⟩⟩

/-! ### From the global sections back to the sheaves -/

variable {X}

open Stacks.Cohomology.InvertibleDerived in
omit [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **Global sections carry multiplication by a global section to multiplication by a
scalar.** -/
theorem gammaF_map_smulHom (F : Mod X.O) (r : GammaRing X) :
    (gammaF X).map (smulHom (toGS r) F) = (scalarNatTrans r).app ((gammaF X).obj F) := by
  ext y
  rfl

/-- **`N ↦ N ⊗_R O` is linear over the global sections.** -/
theorem assocF_map_scalarNatTrans (N : ModuleCat.{u} (GammaRing X)) (r : GammaRing X) :
    (assocF X).map ((scalarNatTrans r).app N) = smulHom (toGS r) ((assocF X).obj N) := by
  apply ((assocAdj X).homEquiv N _).injective
  refine ((assocAdj X).homEquiv_unit _ _ _).trans
    (Eq.trans ?_ ((assocAdj X).homEquiv_unit _ _ _).symm)
  exact (((assocAdj X).unit.naturality ((scalarNatTrans r).app N)).symm).trans
    ((scalarNatTrans_naturality r ((assocAdj X).unit.app N)).trans
      (congrArg ((assocAdj X).unit.app N ≫ ·) (gammaF_map_smulHom _ r).symm))

open Stacks.Cohomology.InvertibleDerived in
/-- The cohomology of a complex of finite free summands whose global sections are homotopy
equivalent to a complex with zero differentials. -/
def homologyIsoOfZeroDiff (E : CochainComplex (Mod X.O) ℤ)
    (hE : ∀ i, _root_.IsDirectSummandOfFiniteFree _ (E.X i))
    (H : ℤ → ModuleCat.{u} (GammaRing X))
    (eZ : HomotopyEquiv (((gammaF X).mapHomologicalComplex (ComplexShape.up ℤ)).obj E)
      (CochainComplex.zeroDifferentialComplex H)) (k : ℤ) :
    E.homology k ≅ (assocF X).obj (H k) :=
  ((HomotopyEquiv.ofIso (assocGammaIso X E hE).symm).trans
      ((assocF X).mapHomotopyEquiv eZ)).toHomologyIso k ≪≫
    homologyIsoXOfDEqZero _ (fun _ _ => (assocF X).map_zero _ _) k

/-- Multiplication by a global section on a module isomorphic to an associated sheaf. -/
theorem smulHom_eq_of_iso {G : Mod X.O} {N : ModuleCat.{u} (GammaRing X)}
    (Θ : G ≅ (assocF X).obj N) {r : GammaRing X} {p : Prop} [Decidable p]
    (h : (scalarNatTrans r).app N = if p then 𝟙 _ else 0) :
    smulHom (toGS r) G = if p then 𝟙 _ else 0 := by
  have h1 := smulHom_naturality (toGS r) Θ.hom
  have h2 : smulHom (toGS r) ((assocF X).obj N) = if p then 𝟙 _ else 0 := by
    refine (assocF_map_scalarNatTrans N r).symm.trans ?_
    rw [h]
    split_ifs
    · exact (assocF X).map_id _
    · exact (assocF X).map_zero _ _
  rw [h2] at h1
  rw [← cancel_mono Θ.hom, ← h1]
  split_ifs <;> simp

variable (X) in
/-- `N ↦ N ⊗_R O` carries `R` to the structure sheaf. -/
def assocUnitIso : (assocF X).obj (ModuleCat.of (GammaRing X) (GammaRing X)) ≅
    SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O) :=
  (assocF X).mapIso (globalSectionsUnitIso.{u, u, u} X.O) ≪≫
    @asIso _ _ _ _ _ (isIso_assocAdj_counit X
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      (Stacks.SheafOfModules.isDirectSummandOfFiniteFree_unit
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))

/-- The restriction of a global section of `O` to an object. -/
abbrev globalRes (r : GammaRing X) (W : X.C) : (X.O.obj.obj (op W) : Type u) := r.1 (op W)

open Stacks.Cohomology.InvertibleDerived in
/-- **A linear form on a cohomology module produces a global section killed by every local
section killing the cohomology sheaf.** -/
theorem mul_globalRes_eq_zero (E : CochainComplex (Mod X.O) ℤ)
    (hE : ∀ i, _root_.IsDirectSummandOfFiniteFree _ (E.X i))
    (H : ℤ → ModuleCat.{u} (GammaRing X))
    (eZ : HomotopyEquiv (((gammaF X).mapHomologicalComplex (ComplexShape.up ℤ)).obj E)
      (CochainComplex.zeroDifferentialComplex H)) (k : ℤ) (φ : H k →ₗ[GammaRing X] GammaRing X)
    (x : H k) {W : X.C} (t : (X.O.obj.obj (op W) : Type u))
    (ht : ∀ m : (E.homology k).val.obj (op W), ringSec t • m = 0) :
    t * globalRes (φ x) W = 0 := by
  let Θ := homologyIsoOfZeroDiff E hE H eZ k
  let ψ : E.homology k ⟶ SheafOfModules.unit _ :=
    Θ.hom ≫ ((assocAdj X).homEquiv _ _).symm
      (ModuleCat.ofHom φ ≫ (globalSectionsUnitIso.{u, u, u} X.O).hom)
  let σ := ((gammaF X).map Θ.inv).hom (((assocAdj X).unit.app (H k)).hom x)
  have key : ((gammaF X).map ψ).hom σ = (globalSectionsUnitIso.{u, u, u} X.O).hom.hom (φ x) := by
    change ((gammaF X).map Θ.inv ≫ (gammaF X).map ψ).hom (((assocAdj X).unit.app (H k)).hom x) = _
    rw [← Functor.map_comp, Iso.inv_hom_id_assoc]
    have := congrArg (fun g : H k ⟶ (gammaF X).obj (SheafOfModules.unit _) => g.hom x)
      (((assocAdj X).homEquiv_unit _ _ _).symm.trans
        (((assocAdj X).homEquiv _ _).apply_symm_apply
          (ModuleCat.ofHom φ ≫ (globalSectionsUnitIso.{u, u, u} X.O).hom)))
    exact this
  have hev := congrArg (fun s => s.eval (op W)) key
  have lin : ψ.val.app (op W) (ringSec t • σ.eval (op W)) =
      ringSec t • ψ.val.app (op W) (σ.eval (op W)) := (ψ.val.app _).hom.map_smul _ _
  rw [ht, map_zero] at lin
  exact (congrArg (fun z => ringSec t • z) hev).symm.trans lin.symm

open Stacks.Cohomology.InvertibleDerived in
/-- An idempotent `r` with `M ⊗ N` isomorphic to the image of `r` lies in every ideal containing
the values of all linear forms on `M`. -/
private theorem mem_ideal_of_iso_splitObj {R : Type u} [CommRing R] (I : Ideal R)
    {M N : ModuleCat.{u} R}
    (hM : ∀ (φ : M →ₗ[R] R) (x : M), φ x ∈ I) {r : R}
    (hr : (scalarNatTrans r).app (ModuleCat.of R R) ≫ (scalarNatTrans r).app (ModuleCat.of R R) =
      (scalarNatTrans r).app (ModuleCat.of R R))
    (π : M ⊗ N ≅ splitObj ((scalarNatTrans r).app (ModuleCat.of R R))) : r ∈ I := by
  have hmem := mem_ideal_of_tensor I _ _ hM (π.hom ≫ splitι ((scalarNatTrans r).app _))
    (π.inv.hom ((splitπ hr).hom (1 : R)))
  have e : (π.hom ≫ splitι ((scalarNatTrans r).app (ModuleCat.of R R))).hom
      (π.inv.hom ((splitπ hr).hom (1 : R))) = r := by
    change (splitι ((scalarNatTrans r).app (ModuleCat.of R R))).hom
      (π.hom.hom (π.inv.hom ((splitπ hr).hom (1 : R)))) = r
    rw [Iso.inv_hom_id_apply]
    change (splitπ hr ≫ splitι _).hom (1 : R) = r
    rw [splitπ_splitι, scalarNatTrans_app_apply, smul_eq_mul, mul_one]
  exact e ▸ hmem

variable (X) in
open Stacks.Cohomology.InvertibleDerived in
/-- **A chain-level tensor pairing of finite free summands splits the cohomology sheaves.** -/
theorem exists_sheaf_splitting
    (E F : CochainComplex (Mod X.O) ℤ)
    (hE : ∀ i, _root_.IsDirectSummandOfFiniteFree _ (E.X i))
    (hF : ∀ i, _root_.IsDirectSummandOfFiniteFree _ (F.X i))
    (a b a' b' : ℤ) (hEz : ∀ i, (i < a ∨ b < i) → IsZero (E.X i))
    (hFz : ∀ i, (i < a' ∨ b' < i) → IsZero (F.X i))
    (h : HomotopyEquiv (HomologicalComplex.mapBifunctor E F
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ))
      ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj (SheafOfModules.unit _))) :
    ∃ (S : Finset ℤ) (f : ℤ → GammaRing X), (∀ n, IsIdempotentElem (f n)) ∧
      (∀ n m, n ≠ m → f n * f m = 0) ∧ (∀ n ∉ S, f n = 0) ∧ ∑ n ∈ S, f n = 1 ∧
      (∀ n k, smulHom (toGS (f n)) (E.homology k) = if k = n then 𝟙 _ else 0) ∧
      (∀ n k, smulHom (toGS (f n)) (F.homology k) = if k = -n then 𝟙 _ else 0) ∧
      (∀ {W : X.C} (t : (X.O.obj.obj (op W) : Type u)),
        (∀ k (m : (E.homology k).val.obj (op W)), ringSec t • m = 0) → t = 0) ∧
      ∀ n, Nonempty (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj
          (E.homology n)).obj (F.homology (-n)) ≅
          splitObj (C := Mod X.O) (smulHom (toGS (f n)) (SheafOfModules.unit _))) := by
  obtain ⟨S, f, fidem, fortho, fzero, fsum, fact, gact, ⟨eZ⟩, ⟨eZ'⟩, pair⟩ :=
    exists_ring_splitting X E F hE hF a b a' b' hEz hFz h
  let Θ := homologyIsoOfZeroDiff E hE _ eZ
  let Θ' := homologyIsoOfZeroDiff F hF _ eZ'
  let RR := ModuleCat.of (GammaRing X) (GammaRing X)
  have hidem : ∀ n, (scalarNatTrans (f n)).app RR ≫ (scalarNatTrans (f n)).app RR =
      (scalarNatTrans (f n)).app RR := fun n => by
    rw [← NatTrans.comp_app, scalarNatTrans_comp, (fidem n).eq]
  have faithful : ∀ {W : X.C} (t : (X.O.obj.obj (op W) : Type u)),
      (∀ k (m : (E.homology k).val.obj (op W)), ringSec t • m = 0) → t = 0 := by
    intro W t ht
    let I : Ideal (GammaRing X) :=
      { carrier := {r | t * globalRes r W = 0}
        add_mem' := fun {r s} (hr : t * globalRes r W = 0) (hs : t * globalRes s W = 0) =>
          show t * (globalRes r W + globalRes s W) = 0 by rw [mul_add, hr, hs, add_zero]
        zero_mem' := show t * 0 = 0 from mul_zero t
        smul_mem' := fun c r (hr : t * globalRes r W = 0) =>
          show t * (globalRes c W * globalRes r W) = 0 by
            rw [mul_left_comm, hr, mul_zero] }
    have hM : ∀ k (φ : _ →ₗ[GammaRing X] GammaRing X) x, φ x ∈ I := fun k φ x =>
      mul_globalRes_eq_zero E hE _ eZ k φ x t (ht k)
    have h1 : (1 : GammaRing X) ∈ I := fsum ▸ I.sum_mem fun n _ =>
      mem_ideal_of_iso_splitObj I (hM n) (hidem n) (pair n).some
    exact (mul_one t).symm.trans h1
  refine ⟨S, f, fidem, fortho, fzero, fsum, fun n k => smulHom_eq_of_iso (Θ k) (fact n k),
    fun n k => smulHom_eq_of_iso (Θ' k) (by simpa only [neg_neg] using gact (-n) k),
    faithful, fun n => ?_⟩
  obtain ⟨π⟩ := pair n
  let uI := assocUnitIso X
  have hu : uI.hom ≫ smulHom (toGS (f n)) (SheafOfModules.unit _) =
      smulHom (toGS (f n)) ((assocF X).obj RR) ≫ uI.hom := smulHom_naturality (toGS (f n)) uI.hom
  exact ⟨((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).mapIso (Θ n)).app _ ≪≫
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj _).mapIso (Θ' (-n)) ≪≫
    (assocTensorIso _ _).symm ≪≫ (assocF X).mapIso π ≪≫
    mapSplitObjIso (assocF X) (hidem n) ≪≫
    splitObjCongr (assocF_map_scalarNatTrans RR (f n)) ≪≫
    DerivedCategory.Invertible.splitObjIsoOfIso uI hu⟩

end AlgebraicGeometry.RingedSite.InvertibleDerived

end
