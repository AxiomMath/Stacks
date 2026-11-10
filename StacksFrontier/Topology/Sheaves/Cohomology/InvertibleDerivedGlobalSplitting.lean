module

public import StacksFrontier.Topology.Sheaves.Cohomology.InvertibleDerivedGlobalPairing
public import StacksFrontier.Topology.Sheaves.Cohomology.InvertibleDerivedLocalIdempotents
public import StacksFrontier.Homology.DerivedCategory.Monoidal.InvertibleRingSplitting
public import StacksFrontier.Topology.Sheaves.Cohomology.InvertibleDerivedFactorUnit

/-!
# A chain-level tensor pairing of finite free summands splits the cohomology

Let `(Y, 𝒪_Y)` be a ringed space and let `E`, `F` be bounded complexes of direct summands of
finite free `𝒪_Y`-modules with `Tot(E ⊗ F)` homotopy equivalent to `𝒪_Y[0]`. Then there are
finitely many orthogonal idempotents `f_n` of `Γ(Y, 𝒪_Y)` summing to `1` such that `f_n` acts on
`H^k(E)` as the identity for `k = n` and as zero otherwise, on `H^k(F)` as the identity for
`k = -n` and as zero otherwise, no nonzero local section of `𝒪_Y` annihilates all `H^k(E)`, and
`H^n(E) ⊗ H^{-n}(F)` is the image of `f_n` on `𝒪_Y`.

## References

* [Stacks Project, Tag 0FPG](https://stacks.math.columbia.edu/tag/0FPG)
* [Stacks Project, Tag 0FPF](https://stacks.math.columbia.edu/tag/0FPF)
* [Stacks Project, Tag 0FNT](https://stacks.math.columbia.edu/tag/0FNT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open Opposite TopologicalSpace Stacks.SheafOfModules.DerivedMonoidal Stacks.AssociatedSheaf
open StrictlyPerfect DerivedCategory.Invertible

universe u

namespace Stacks.Cohomology.InvertibleDerived

section Ring

variable {R : Type u} [CommRing R]

/-- The total tensor complex is symmetric up to isomorphism, without signs on the summands. -/
public def tensorFlipIso (P Q : CochainComplex (ModuleCat.{u} R) ℤ) : P ⊗ Q ≅ Q ⊗ P :=
  HomologicalComplex₂.total.mapIso (HomologicalComplex.Hom.isoOfComponents
      (fun p => HomologicalComplex.Hom.isoOfComponents
        (fun q => (TensorProduct.comm R (P.X p) (Q.X q)).toModuleIso)
        (by intros; ext : 1; apply TensorProduct.ext'; intros; rfl))
      (by intros; ext q : 2; apply TensorProduct.ext'; intros; rfl) :
    (((curriedTensor (ModuleCat.{u} R)).mapBifunctorHomologicalComplex
      (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj P).obj Q ≅
      (((curriedTensor (ModuleCat.{u} R)).flip.mapBifunctorHomologicalComplex
      (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj P).obj Q) (ComplexShape.up ℤ) ≪≫
    HomologicalComplex.mapBifunctorFlipIso Q P (curriedTensor (ModuleCat.{u} R)) (ComplexShape.up ℤ)

/-- Every value on a tensor product of a linear map lies in an ideal containing all values of
linear forms on the first factor. -/
public theorem mem_ideal_of_tensor (I : Ideal R) (M N : ModuleCat.{u} R)
    (hM : ∀ (φ : M →ₗ[R] R) (x : M), φ x ∈ I) (L : M ⊗ N ⟶ ModuleCat.of R R)
    (z : TensorProduct R M N) :
    L.hom z ∈ I := by
  induction z using TensorProduct.inductionOn with
  | tmul x y => exact hM (L.hom.comp ((TensorProduct.mk R M N).flip y)) x
  | add z z' hz hz' => exact (map_add L.hom z z').symm ▸ I.add_mem hz hz'

end Ring

variable (Y : RingedSpace.{u, u})

/-- Restricting a global section to the whole space does nothing. -/
public theorem presheaf_map_top (r : GlobalRing Y) :
    (Y.presheaf.map (homOfLE (le_top : (⊤ : Opens Y.carrier) ≤ ⊤)).op).hom r = r := by
  rw [show (homOfLE (le_top : (⊤ : Opens Y.carrier) ≤ ⊤)) = 𝟙 _ from rfl, op_id,
    Y.presheaf.map_id]
  rfl

/-- The global sections, as the global sections of the structure sheaf. -/
public def ringToGamma :
    ModuleCat.of (GlobalRing Y) (GlobalRing Y) ⟶ (gammaF Y).obj (SheafOfModules.unit _) :=
  ModuleCat.ofHom (Y := (gammaF Y).obj (SheafOfModules.unit _))
    { toFun := fun r => r
      map_add' := fun _ _ => rfl
      map_smul' := fun r s => by
        change r * s = (Y.presheaf.map (homOfLE le_top).op).hom r * s
        rw [presheaf_map_top] }

variable {Y}

/-- Multiplication by a global section which is `1` or `0`, on sections. -/
public theorem smul_of_smulHom_eq {G : Mod Y.sheaf} {s : GlobalRing Y} {p : Prop} [Decidable p]
    (h : smulHom s G = if p then 𝟙 _ else 0) {W : Opens Y.carrier} (hW : W ≤ ⊤)
    (m : G.val.obj (op W)) :
    ringSec (U := op W) (resLE hW s) • m = if p then m else 0 := by
  refine (congrArg (fun φ : G ⟶ G => φ.val.app (op W) m) h).trans ?_
  split_ifs <;> rfl

/-- The global sections of a bounded-above complex of direct summands of finite free modules are
degreewise projective and strictly bounded above. -/
private theorem gamma_projective_isStrictlyLE
    (G : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf)) ℤ)
    (hG : ∀ i, IsDirectSummandOfFiniteFree (G.X i)) (c : ℤ) (hz : ∀ i, c < i → IsZero (G.X i)) :
    (∀ i, Projective ((((gammaF Y).mapHomologicalComplex (ComplexShape.up ℤ)).obj G).X i)) ∧
      CochainComplex.IsStrictlyLE
        (((gammaF Y).mapHomologicalComplex (ComplexShape.up ℤ)).obj G) c :=
  ⟨fun i => (IsProjective.iff_projective ((gammaF Y).obj (G.X i))).mp
      (gamma_finite_projective Y (G.X i) (hG i)).2,
    (CochainComplex.isStrictlyLE_iff _ c).mpr fun i hi => (gammaF Y).map_isZero (hz i hi)⟩

variable (Y) in
/-- **The ring-level splitting.** Under the hypotheses of this file, the global sections
`P = Γ(Y, E)` and `P' = Γ(Y, F)` are homotopy equivalent to their cohomology, there are finitely
many orthogonal idempotents `f_n` of `R = Γ(Y, 𝒪_Y)` summing to `1` acting on `H^k(P)` as the
identity for `k = n` and as zero otherwise and on `H^k(P')` as the identity for `k = -n` and as
zero otherwise, and `H^n(P) ⊗_R H^{-n}(P')` is the image of `f_n` on `R`. -/
public theorem exists_ring_splitting
    (E F : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf)) ℤ)
    (hE : ∀ i, IsDirectSummandOfFiniteFree (E.X i)) (hF : ∀ i, IsDirectSummandOfFiniteFree (F.X i))
    (a b a' b' : ℤ) (hEz : ∀ i, (i < a ∨ b < i) → IsZero (E.X i))
    (hFz : ∀ i, (i < a' ∨ b' < i) → IsZero (F.X i))
    (h : HomotopyEquiv (HomologicalComplex.mapBifunctor E F
      (Stacks.SheafOfModules.Tensor.sheafTensor Y.sheaf) (ComplexShape.up ℤ))
      ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj (SheafOfModules.unit _))) :
    let P := ((gammaF Y).mapHomologicalComplex (ComplexShape.up ℤ)).obj E
    let P' := ((gammaF Y).mapHomologicalComplex (ComplexShape.up ℤ)).obj F
    ∃ (S : Finset ℤ) (f : ℤ → GlobalRing Y), (∀ n, IsIdempotentElem (f n)) ∧
      (∀ n m, n ≠ m → f n * f m = 0) ∧ (∀ n ∉ S, f n = 0) ∧ ∑ n ∈ S, f n = 1 ∧
      ActsOnHomology (fun n => scalarNatTrans (f n)) P ∧
      ActsOnHomology (fun n => scalarNatTrans (f (-n))) P' ∧
      Nonempty (HomotopyEquiv P (CochainComplex.zeroDifferentialComplex fun k => P.homology k)) ∧
      Nonempty (HomotopyEquiv P' (CochainComplex.zeroDifferentialComplex fun k => P'.homology k)) ∧
      ∀ n, Nonempty (P.homology n ⊗ P'.homology (-n) ≅
        splitObj ((scalarNatTrans (f n)).app (ModuleCat.of (GlobalRing Y) (GlobalRing Y)))) := by
  intro P P'
  obtain ⟨hPproj, _⟩ := gamma_projective_isStrictlyLE E hE b fun i hi => hEz i (Or.inr hi)
  obtain ⟨hP'proj, _⟩ := gamma_projective_isStrictlyLE F hF b' fun i hi => hFz i (Or.inr hi)
  let hT := gammaTensorHomotopyEquiv Y E F hE hF a b hEz h
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
      (𝟙_ (CochainComplex (ModuleCat.{u} (GlobalRing Y)) ℤ)) :=
    (HomologicalComplex.mapBifunctorHomotopyEquiv _ _ eZ.symm eZ'.symm).trans hT
  let Φ := degreeZeroIsoOfHomotopyEquiv _ _ hZZ
  have hgf : ∀ n, g (-n) = f n := eq_neg_of_complete _ _ f g S S' fzero gzero fsum gsum fact gact Φ
  obtain rfl : g = fun n => f (-n) := funext fun n => by rw [← hgf (-n), neg_neg]
  exact ⟨S, f, fidem, fortho, fzero, fsum, fact, gact, ⟨eZ⟩, ⟨eZ'⟩,
    fun n => ⟨tensorIsoSplitObjOfIso _ _ n f fact Φ⟩⟩

variable (Y) in
/-- The cohomology of a complex of finite free summands whose global sections are homotopy
equivalent to a complex with zero differentials. -/
public def homologyIsoOfZeroDiff (E : CochainComplex (OXMod.{u, u} Y) ℤ)
    (hE : ∀ i, IsDirectSummandOfFiniteFree (E.X i)) (H : ℤ → ModuleCat.{u} (GlobalRing Y))
    (eZ : HomotopyEquiv (((gammaF Y).mapHomologicalComplex (ComplexShape.up ℤ)).obj E)
      (CochainComplex.zeroDifferentialComplex H)) (k : ℤ) :
    E.homology k ≅ (assocR Y).obj (H k) :=
  ((HomotopyEquiv.ofIso (assocGammaIso Y E hE).symm).trans
      ((assocF Y).mapHomotopyEquiv eZ)).toHomologyIso k ≪≫
    homologyIsoXOfDEqZero _ (fun _ _ => (assocF Y).map_zero _ _) k

/-- Multiplication by a global section on a module isomorphic to an associated sheaf. -/
public theorem smulHom_eq_of_iso {G : Mod Y.sheaf} {N : ModuleCat.{u} (GlobalRing Y)}
    (Θ : G ≅ (assocR Y).obj N) {r : GlobalRing Y} {p : Prop} [Decidable p]
    (h : (scalarNatTrans r).app N = if p then 𝟙 _ else 0) :
    smulHom r G = if p then 𝟙 _ else 0 := by
  have h1 := smulHom_naturality r Θ.hom
  have h2 : smulHom r ((assocR Y).obj N) = if p then 𝟙 _ else 0 := by
    refine (assocF_map_scalarNatTrans Y N r).symm.trans ?_
    rw [h]
    split_ifs
    · exact (assocR Y).map_id _
    · exact (assocR Y).map_zero _ _
  rw [h2] at h1
  rw [← cancel_mono Θ.hom, ← h1]
  split_ifs <;> simp

/-- The image of an idempotent depends only on the idempotent. -/
public def splitObjCongr {C : Type*} [Category* C] [Preadditive C] [HasKernels C] {A : C}
    {p q : A ⟶ A} (h : p = q) : splitObj p ≅ splitObj q :=
  eqToIso (congrArg splitObj h)

variable (Y) in
/-- **A linear form on a cohomology module produces a global section killed by every local
section killing the cohomology sheaf.** -/
public theorem mul_globalRes_eq_zero
    (E : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf)) ℤ)
    (hE : ∀ i, IsDirectSummandOfFiniteFree (E.X i)) (H : ℤ → ModuleCat.{u} (GlobalRing Y))
    (eZ : HomotopyEquiv (((gammaF Y).mapHomologicalComplex (ComplexShape.up ℤ)).obj E)
      (CochainComplex.zeroDifferentialComplex H)) (k : ℤ) (φ : H k →ₗ[GlobalRing Y] GlobalRing Y)
    (x : H k) {W : Opens Y.carrier} (t : Y.presheaf.obj (op W))
    (ht : ∀ m : (E.homology k).val.obj (op W), ringSec (U := op W) t • m = 0) :
    t * globalRes (φ x) W = 0 := by
  let Θ := homologyIsoOfZeroDiff Y E hE H eZ k
  let φb : (assocR Y).obj (H k) ⟶
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf) :=
    ((assocAdj Y).homEquiv _ _).symm (ModuleCat.ofHom φ ≫ ringToGamma Y)
  let ψ : E.homology k ⟶ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf) :=
    Θ.hom ≫ φb
  let y := ((assocAdj Y).unit.app (H k)).hom x
  let σ := Θ.inv.val.app (op ⊤) y
  have h1 : Θ.hom.val.app (op ⊤) σ = y :=
    congrArg (fun g : (assocR Y).obj (H k) ⟶ (assocR Y).obj (H k) => g.val.app (op ⊤) y)
      Θ.inv_hom_id
  have h2 : φb.val.app (op ⊤) y = φ x :=
    congrArg (fun g : H k ⟶ (gammaF Y).obj (SheafOfModules.unit _) => g.hom x)
      (((assocAdj Y).homEquiv_unit _ _ φb).symm.trans
        (((assocAdj Y).homEquiv _ _).apply_symm_apply _))
  have key : ψ.val.app (op ⊤) σ = φ x := (congrArg (φb.val.app (op ⊤)) h1).trans h2
  let m := (E.homology k).val.map (homOfLE le_top : W ⟶ ⊤).op σ
  have nat : ψ.val.app (op W) m =
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf)).val.map
        (homOfLE le_top : W ⟶ ⊤).op (ψ.val.app (op ⊤) σ) :=
    PresheafOfModules.naturality_apply ψ.val _ σ
  have lin : ψ.val.app (op W) (ringSec (U := op W) t • m) =
      ringSec (U := op W) t • ψ.val.app (op W) m := (ψ.val.app _).hom.map_smul _ _
  have e1 : ringSec (U := op W) t • ψ.val.app (op W) m = 0 :=
    lin.symm.trans ((congrArg (ψ.val.app (op W)).hom (ht m)).trans (map_zero _))
  have e2 : ψ.val.app (op W) m = globalRes (φ x) W := nat.trans (congrArg _ key)
  exact (congrArg (fun z => ringSec (U := op W) t • z) e2).symm.trans e1

variable (Y) in
/-- **A chain-level tensor pairing of finite free summands splits the cohomology sheaves.** -/
public theorem exists_sheaf_splitting
    (E F : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf)) ℤ)
    (hE : ∀ i, IsDirectSummandOfFiniteFree (E.X i)) (hF : ∀ i, IsDirectSummandOfFiniteFree (F.X i))
    (a b a' b' : ℤ) (hEz : ∀ i, (i < a ∨ b < i) → IsZero (E.X i))
    (hFz : ∀ i, (i < a' ∨ b' < i) → IsZero (F.X i))
    (h : HomotopyEquiv (HomologicalComplex.mapBifunctor E F
      (Stacks.SheafOfModules.Tensor.sheafTensor Y.sheaf) (ComplexShape.up ℤ))
      ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj (SheafOfModules.unit _))) :
    ∃ (S : Finset ℤ) (f : ℤ → GlobalRing Y), (∀ n, IsIdempotentElem (f n)) ∧
      (∀ n m, n ≠ m → f n * f m = 0) ∧ (∀ n ∉ S, f n = 0) ∧ ∑ n ∈ S, f n = 1 ∧
      (∀ n k, smulHom (f n) (E.homology k) = if k = n then 𝟙 _ else 0) ∧
      (∀ n k, smulHom (f n) (F.homology k) = if k = -n then 𝟙 _ else 0) ∧
      (∀ {W : Opens Y.carrier} (t : Y.presheaf.obj (op W)),
        (∀ k (m : (E.homology k).val.obj (op W)), ringSec (U := op W) t • m = 0) → t = 0) ∧
      ∀ n, Nonempty (((Stacks.SheafOfModules.Tensor.sheafTensor Y.sheaf).obj (E.homology n)).obj
        (F.homology (-n)) ≅
          splitObj (C := Mod Y.sheaf) (smulHom (f n) (SheafOfModules.unit _))) := by
  obtain ⟨S, f, fidem, fortho, fzero, fsum, fact, gact, ⟨eZ⟩, ⟨eZ'⟩, pair⟩ :=
    exists_ring_splitting Y E F hE hF a b a' b' hEz hFz h
  let Θ := homologyIsoOfZeroDiff Y E hE _ eZ
  let Θ' := homologyIsoOfZeroDiff Y F hF _ eZ'
  let RR := ModuleCat.of (GlobalRing Y) (GlobalRing Y)
  have hidem : ∀ n, (scalarNatTrans (f n)).app RR ≫ (scalarNatTrans (f n)).app RR =
      (scalarNatTrans (f n)).app RR := fun n => by
    rw [← NatTrans.comp_app, scalarNatTrans_comp, (fidem n).eq]
  have faithful : ∀ {W : Opens Y.carrier} (t : Y.presheaf.obj (op W)),
      (∀ k (m : (E.homology k).val.obj (op W)), ringSec (U := op W) t • m = 0) → t = 0 := by
    intro W t ht
    let I : Ideal (GlobalRing Y) :=
      { carrier := {r | t * globalRes r W = 0}
        add_mem' := fun {r s} (hr : t * globalRes r W = 0) (hs : t * globalRes s W = 0) =>
          show t * globalRes (r + s) W = 0 by rw [globalRes_add, mul_add, hr, hs, add_zero]
        zero_mem' := show t * globalRes 0 W = 0 by rw [globalRes_zero, mul_zero]
        smul_mem' := fun c r (hr : t * globalRes r W = 0) =>
          show t * globalRes (c * r) W = 0 by
            rw [globalRes_mul, mul_left_comm, hr, mul_zero] }
    have hM : ∀ k (φ : _ →ₗ[GlobalRing Y] GlobalRing Y) x, φ x ∈ I := fun k φ x =>
      mul_globalRes_eq_zero Y E hE _ eZ k φ x t (ht k)
    have hf : ∀ n, f n ∈ I := fun n => by
      obtain ⟨π⟩ := pair n
      have hmem := mem_ideal_of_tensor I _ _ (hM n) (π.hom ≫ splitι ((scalarNatTrans (f n)).app RR))
        (π.inv.hom ((splitπ (hidem n)).hom (1 : GlobalRing Y)))
      have e : (π.hom ≫ splitι ((scalarNatTrans (f n)).app RR)).hom
          (π.inv.hom ((splitπ (hidem n)).hom (1 : GlobalRing Y))) = f n := by
        change (splitι ((scalarNatTrans (f n)).app RR)).hom
          (π.hom.hom (π.inv.hom ((splitπ (hidem n)).hom (1 : GlobalRing Y)))) = f n
        rw [Iso.inv_hom_id_apply]
        change (splitπ (hidem n) ≫ splitι _).hom (1 : GlobalRing Y) = f n
        rw [splitπ_splitι, scalarNatTrans_app_apply, smul_eq_mul, mul_one]
      exact e ▸ hmem
    have h1 : (1 : GlobalRing Y) ∈ I := fsum ▸ I.sum_mem fun n _ => hf n
    have h2 : t * globalRes 1 W = 0 := h1
    rwa [globalRes_one, mul_one] at h2
  refine ⟨S, f, fidem, fortho, fzero, fsum, fun n k => smulHom_eq_of_iso (Θ k) (fact n k),
    fun n k => smulHom_eq_of_iso (Θ' k) (by simpa only [neg_neg] using gact (-n) k),
    faithful, fun n => ?_⟩
  obtain ⟨π⟩ := pair n
  let u := associatedSheafUnitIso Y (RingHom.id (GlobalRing Y))
  have hu : u.hom ≫ smulHom (f n) (SheafOfModules.unit _) =
      smulHom (f n) ((assocR Y).obj RR) ≫ u.hom := smulHom_naturality (f n) u.hom
  exact ⟨((Stacks.SheafOfModules.Tensor.sheafTensor Y.sheaf).mapIso (Θ n)).app _ ≪≫
    ((Stacks.SheafOfModules.Tensor.sheafTensor Y.sheaf).obj _).mapIso (Θ' (-n)) ≪≫
    (assocTensorSheafTensorIso Y _ _).symm ≪≫ (assocR Y).mapIso π ≪≫
    mapSplitObjIso (assocR Y) (hidem n) ≪≫
    splitObjCongr (assocF_map_scalarNatTrans Y RR (f n)) ≪≫
    splitObjIsoOfIso u hu⟩

/-- Restricting along the identity does nothing. -/
public theorem resLE_refl {W : Opens Y.carrier} (h : W ≤ W) (t : Y.presheaf.obj (op W)) :
    resLE h t = t := by
  rw [resLE, show (homOfLE h : W ⟶ W) = 𝟙 _ from rfl, op_id, Y.presheaf.map_id,
    ConcreteCategory.id_apply]

variable (Y) in
/-- **A chain-level tensor pairing of finite free summands is a local splitting over the whole
space.** -/
public theorem nonempty_localSplitting_top
    (E F : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf)) ℤ)
    (hE : ∀ i, IsDirectSummandOfFiniteFree (E.X i)) (hF : ∀ i, IsDirectSummandOfFiniteFree (F.X i))
    (a b a' b' : ℤ) (hEz : ∀ i, (i < a ∨ b < i) → IsZero (E.X i))
    (hFz : ∀ i, (i < a' ∨ b' < i) → IsZero (F.X i))
    (h : HomotopyEquiv (HomologicalComplex.mapBifunctor E F
      (Stacks.SheafOfModules.Tensor.sheafTensor Y.sheaf) (ComplexShape.up ℤ))
      ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj (SheafOfModules.unit _))) :
    Nonempty (LocalSplitting E F (⊤ : Opens Y.carrier)) := by
  obtain ⟨S, f, fidem, fortho, fzero, fsum, hsE, hsF, faith, pair⟩ :=
    exists_sheaf_splitting Y E F hE hF a b a' b' hEz hFz h
  refine ⟨⟨S, f, fidem, fortho, fzero, fsum, fun n k W hW m => smul_of_smulHom_eq (hsE n k) hW m,
    fun n k W hW m => smul_of_smulHom_eq (hsF n k) hW m, fun {W} _ t ht => faith t fun k m => by
      simpa only [resLE_refl] using ht k le_rfl m, fun n e _ he => ?_⟩⟩
  obtain rfl : e = f n :=
    (globalRes_top e).symm.trans ((he le_rfl).trans (resLE_refl le_rfl (f n)))
  obtain ⟨π⟩ := pair n
  exact ⟨(restrictModules Y ⊤).mapIso π⟩

end Stacks.Cohomology.InvertibleDerived

end
