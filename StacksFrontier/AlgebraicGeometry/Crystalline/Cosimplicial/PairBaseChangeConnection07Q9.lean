module

public import StacksFrontier.AlgebraicGeometry.Crystalline.CompletedConnectionBaseChangeCompositeIso
public import StacksFrontier.AlgebraicGeometry.Crystalline.CompletedConnectionCurvatureBaseChange
public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial.BaseChangeConnectionsCurvature
public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial.PairBaseChange07Q9

/-!
# The base-change connections of a pulled back cosimplicial module

Let `g : E ⟶ E'` be a morphism of cosimplicial divided power algebras, with completed rings
`D(b)` and `D'(b)`, and let `M(•)` be a cosimplicial module over `D(•)` carrying a completed
connection `∇` on `M(0)` and identifications `β_b : (D(b) ⊗_{D(0)} M(0))^∧ ≃ M(b)` with the base
change along the coprojection `σ_b : ⦋0⦌ ⟶ ⦋b⦌`.  These are the data from which
`Crystalline.CosimplicialCompletedModule.baseChangeConnection` builds the connections of the
double complex of [Stacks, Proposition 60.21.3, Tag 07LG].

This file transports the data along `g`: on the base change
`M'(•) = Crystalline.CosimplicialCompletedModule.pullback07Q9` it builds

* the connection `∇'` on `M'(0) = (D'(0) ⊗_{D(0)} M(0))^∧`, the base change of `∇` along `g_0`
  (`Crystalline.CosimplicialCompletedModule.pullbackNabla07Q9`);
* the identifications `β'_b : (D'(b) ⊗_{D'(0)} M'(0))^∧ ≃ M'(b)`, from `β_b` and the
  associativity of the completed base change
  (`Crystalline.CosimplicialCompletedModule.pullbackBeta07Q9`);

and proves that they satisfy again every hypothesis the double complex asks for, and that the maps
`M(b) → M'(b)`, `m ↦ 1 ⊗ m`, are horizontal for the two families of base-change connections.
This is the morphism of cosimplicial pairs along `g` that the proof of
[Stacks, Lemma 60.22.4, Tag 07Q9] compares the two double complexes with.

## Main results

* `Crystalline.CosimplicialDPAlgebra.Hom.formsMap_differential07Q9` — the forms map of `g`
  carries `d x` to `d (g x)`.
* `Crystalline.CosimplicialCompletedModule.comparisonValues_tensorMap07Q9` — a natural family of
  semilinear maps of cosimplicial modules induces maps of the columns of the double complexes.
* `Crystalline.CosimplicialCompletedModule.pullbackBeta07Q9_tmul` — `β'` satisfies the
  hypothesis `hbeta` of the base-change connections.
* `Crystalline.CosimplicialCompletedModule.baseChangeConnection_pullbackApp07Q9` — **the maps
  `M(b) → M'(b)` are horizontal for the base-change connections.**
* `Crystalline.CosimplicialCompletedModule.pullback07Q9_horizontal_coface` and
  `Crystalline.CosimplicialCompletedModule.pullbackNabla07Q9_integrable` — the coface `δ` is
  horizontal and `∇'` is integrable, given the same for `∇`.
* `Crystalline.CosimplicialCompletedModule.pullbackBaseChangeConnection07Q9_zero` — in degree
  zero the base-change connection of `M'` is `∇'`.

## References

* [Stacks Project, Lemma 60.22.4, Tag 07Q9](https://stacks.math.columbia.edu/tag/07Q9)
* [Stacks Project, Proposition 60.21.3, Tag 07LG](https://stacks.math.columbia.edu/tag/07LG)
* [Stacks Project, Remark 60.17.6, Tag 07KJ](https://stacks.math.columbia.edu/tag/07KJ)
-/

@[expose] public noncomputable section

universe u

open CategoryTheory Simplicial
open scoped TensorProduct

namespace Crystalline

open DividedPowers

/-- **A linear equivalence induces a linear equivalence of adic completions**, linear over the
uncompleted ring (Mathlib's `AdicCompletion.congr` is linear over the completed ring). -/
def adicCompletionCongr07Q9 {R : Type*} [CommRing R] {X Y : Type*} [AddCommGroup X]
    [Module R X] [AddCommGroup Y] [Module R Y] (I : Ideal R) (e : X ≃ₗ[R] Y) :
    AdicCompletion I X ≃ₗ[R] AdicCompletion I Y :=
  LinearEquiv.ofLinear (adicCompletionMapLinear e.toLinearMap I)
    (adicCompletionMapLinear e.symm.toLinearMap I)
    (LinearMap.ext fun x =>
      (adicCompletionMapₛₗ_comp_apply e.symm.toLinearMap e.toLinearMap LinearMap.id
        (le_of_eq (Ideal.map_id I)) (le_of_eq (Ideal.map_id I)) (le_of_eq (Ideal.map_id I))
        (fun y => (e.apply_symm_apply y).symm) x).symm.trans
        (adicCompletionMapₛₗ_id_apply _ (le_of_eq (Ideal.map_id I)) (fun _ => rfl) x))
    (LinearMap.ext fun x =>
      (adicCompletionMapₛₗ_comp_apply e.toLinearMap e.symm.toLinearMap LinearMap.id
        (le_of_eq (Ideal.map_id I)) (le_of_eq (Ideal.map_id I)) (le_of_eq (Ideal.map_id I))
        (fun y => (e.symm_apply_apply y).symm) x).symm.trans
        (adicCompletionMapₛₗ_id_apply _ (le_of_eq (Ideal.map_id I)) (fun _ => rfl) x))

/-- The induced equivalence of adic completions on the canonical image. -/
theorem adicCompletionCongr07Q9_of {R : Type*} [CommRing R] {X Y : Type*} [AddCommGroup X]
    [Module R X] [AddCommGroup Y] [Module R Y] (I : Ideal R) (e : X ≃ₗ[R] Y) (x : X) :
    adicCompletionCongr07Q9 I e (AdicCompletion.of I X x) = AdicCompletion.of I Y (e x) :=
  adicCompletionMapₛₗ_of _ _ x

namespace CosimplicialDPAlgebra.Hom

variable {A : Type u} [CommRing A] {E E' : CosimplicialDPAlgebra.{u, u} A} (g : E.Hom E')
  (p : ℕ)

/-- **The forms map of a morphism of cosimplicial divided power algebras carries the universal
differential to the universal differential**: `g_*(d x) = d (g x)`.  The differential is the
degree-zero de Rham differential at the unit zero-form, and the forms map commutes with the de Rham
differentials and preserves the unit zero-form. -/
theorem formsMap_differential07Q9 (b : ℕ) (x : E.completedRing p b) :
    g.formsMap p b 1 (E.differential p b x) =
      E'.differential p b (g.completedRingMap p b x) := by
  have hunit : g.formsMap p b 0 (E.unitZeroForm p b) = E'.unitZeroForm p b :=
    completedMapDifferentialForms_completedUnitZeroForm p A (E.dividedPowers b)
      (E'.dividedPowers b) (g.app b) (g.isDPMorphism b)
  have hsmul : g.formsMap p b 0 (x • E.unitZeroForm p b) =
      g.completedRingMap p b x • E'.unitZeroForm p b := by
    rw [map_smulₛₗ, hunit]
  have hd := g.formsMap_deRham p b 0 (x • E.unitZeroForm p b)
  rw [E.deRham_zero_smul_unitZeroForm p b x, hsmul, E'.deRham_zero_smul_unitZeroForm] at hd
  exact hd

end CosimplicialDPAlgebra.Hom

namespace CosimplicialCompletedModule

variable {A : Type u} [CommRing A] {E E' : CosimplicialDPAlgebra.{u, u} A} {p : ℕ}

/-- **A natural family of semilinear maps of cosimplicial modules induces maps of the columns of
the double complexes**: the maps `M(b) ⊗̂ Ω^a_{D(b)} → M'(b) ⊗̂ Ω^a_{D'(b)}` they induce commute
with the cosimplicial transitions. -/
theorem comparisonValues_tensorMap07Q9 (g : E.Hom E')
    (W : CosimplicialCompletedModule.{u, u, u} E p)
    (W' : CosimplicialCompletedModule.{u, u, u} E' p)
    (app : ∀ b : ℕ, W.carrier b →ₛₗ[g.completedRingMap p b] W'.carrier b)
    (hnat : ∀ {m n : SimplexCategory} (φ : m ⟶ n) (x : W.carrier m.len),
      app n.len (W.map φ x) = W'.map φ (app m.len x))
    {m n : SimplexCategory} (φ : m ⟶ n) (a : ℕ) (z : W.obj a m.len) :
    CompletedDeRham.comparisonValues p (E.completedRing p n.len) (E'.completedRing p n.len)
        (g.completedRingMap p n.len) (W.carrier n.len) (W'.carrier n.len) (app n.len)
        (fun i => E.forms p i n.len) (fun i => E'.forms p i n.len)
        (fun i => g.formsMap p n.len i) a (W.tensorMap φ a z) =
      W'.tensorMap φ a
        (CompletedDeRham.comparisonValues p (E.completedRing p m.len) (E'.completedRing p m.len)
          (g.completedRingMap p m.len) (W.carrier m.len) (W'.carrier m.len) (app m.len)
          (fun i => E.forms p i m.len) (fun i => E'.forms p i m.len)
          (fun i => g.formsMap p m.len i) a z) := by
  let l := semilinearComp (TensorProduct.map (app n.len) (g.formsMap p n.len a))
    (TensorProduct.map (W.map φ) (E.formsMapCompleted p φ a))
  have h1 := adicCompletionMapₛₗ_comp_apply
    (TensorProduct.map (W.map φ) (E.formsMapCompleted p φ a))
    (TensorProduct.map (app n.len) (g.formsMap p n.len a)) l
    (map_pAdicIdeal_le p _) (map_pAdicIdeal_le p _) (map_pAdicIdeal_le p _) (fun _ => rfl) z
  have h2 := adicCompletionMapₛₗ_comp_apply
    (TensorProduct.map (app m.len) (g.formsMap p m.len a))
    (TensorProduct.map (W'.map φ) (E'.formsMapCompleted p φ a)) l
    (map_pAdicIdeal_le p _) (map_pAdicIdeal_le p _) (map_pAdicIdeal_le p _) (fun y => by
      induction y using TensorProduct.induction_on with
      | zero => simp only [map_zero]
      | tmul y ω =>
        show app n.len (W.map φ y) ⊗ₜ[E'.completedRing p n.len]
            g.formsMap p n.len a (E.formsMap p φ a ω) =
          W'.map φ (app m.len y) ⊗ₜ[E'.completedRing p n.len]
            E'.formsMap p φ a (g.formsMap p m.len a ω)
        rw [hnat, g.formsMap_formsMap]
      | add y z hy hz => simp only [map_add, hy, hz]) z
  exact h1.symm.trans h2

variable (V : CosimplicialCompletedModule.{u, u, u} E p) (g : E.Hom E')
  (nabla : CompletedConnection p (E.completedRing p 0) (E.forms p 1 0) (E.differential p 0)
    (V.carrier 0))
  (beta : ∀ b : ℕ, letI := E.coprojectionAlgebra p b
    CompletedConnection.baseChangeCarrier p (E.completedRing p 0) (E.completedRing p b)
      (V.carrier 0) ≃ₗ[E.completedRing p b] V.carrier b)
  (hbeta : ∀ (b : ℕ) (x : E.completedRing p b) (m : V.carrier 0),
    letI := E.coprojectionAlgebra p b
    beta b (AdicCompletion.of (pAdicIdeal (A := E.completedRing p b) p)
        (E.completedRing p b ⊗[E.completedRing p 0] V.carrier 0) (x ⊗ₜ[E.completedRing p 0] m)) =
      x • V.map (CosimplicialDPAlgebra.coprojection b) m)

/-- The maps `M(b) ⊗̂ Ω^a_{D(b)} → M'(b) ⊗̂ Ω^a_{D'(b)}` induced by `m ↦ 1 ⊗ m` commute with the
cosimplicial transitions. -/
theorem pullbackApp07Q9_tensorMap {m n : SimplexCategory} (φ : m ⟶ n) (a : ℕ)
    (z : V.obj a m.len) :
    CompletedDeRham.comparisonValues p (E.completedRing p n.len) (E'.completedRing p n.len)
        (g.completedRingMap p n.len) (V.carrier n.len) ((V.pullback07Q9 g).carrier n.len)
        (V.pullbackApp07Q9 g n.len) (fun i => E.forms p i n.len) (fun i => E'.forms p i n.len)
        (fun i => g.formsMap p n.len i) a (V.tensorMap φ a z) =
      (V.pullback07Q9 g).tensorMap φ a
        (CompletedDeRham.comparisonValues p (E.completedRing p m.len) (E'.completedRing p m.len)
          (g.completedRingMap p m.len) (V.carrier m.len) ((V.pullback07Q9 g).carrier m.len)
          (V.pullbackApp07Q9 g m.len) (fun i => E.forms p i m.len) (fun i => E'.forms p i m.len)
          (fun i => g.formsMap p m.len i) a z) :=
  comparisonValues_tensorMap07Q9 g V (V.pullback07Q9 g) (V.pullbackApp07Q9 g)
    (fun φ x => V.pullbackApp07Q9_naturality g φ x) φ a z

/-! ### The connection on `M'(0)` -/

/-- **The connection `∇'` on `M'(0) = (D'(0) ⊗_{D(0)} M(0))^∧`**: the base change of `∇` along
`g_0`, the forms being compared by the forms map of `g` ([Stacks, Remark 60.17.6, Tag 07KJ]). -/
def pullbackNabla07Q9 :
    CompletedConnection p (E'.completedRing p 0) (E'.forms p 1 0) (E'.differential p 0)
      ((V.pullback07Q9 g).carrier 0) :=
  letI := g.completedAlgebra07Q9 p 0
  CompletedConnection.baseChange p (E.completedRing p 0) (E'.completedRing p 0) (V.carrier 0)
    (E.forms p 1 0) (E'.forms p 1 0) (E'.differential p 0) (g.formsMap p 0 1) nabla
    (E'.differential_add p 0) (E'.differential_mul p 0) (g.formsMap_differential07Q9 p 0)

/-- **`m ↦ 1 ⊗ m` is horizontal for `∇` and `∇'`.** -/
theorem pullbackNabla07Q9_pullbackApp (x : V.carrier 0) :
    V.pullbackNabla07Q9 g nabla (V.pullbackApp07Q9 g 0 x) =
      CompletedDeRham.comparisonValues p (E.completedRing p 0) (E'.completedRing p 0)
        (g.completedRingMap p 0) (V.carrier 0) ((V.pullback07Q9 g).carrier 0)
        (V.pullbackApp07Q9 g 0) (fun i => E.forms p i 0) (fun i => E'.forms p i 0)
        (fun i => g.formsMap p 0 i) 1 (nabla x) :=
  let := g.completedAlgebra07Q9 p 0
  CompletedConnection.baseChange_inclusion p (E.completedRing p 0) (E'.completedRing p 0)
    (V.carrier 0) (E.forms p 1 0) (E'.forms p 1 0) (E'.differential p 0) (g.formsMap p 0 1) nabla
    (E'.differential_add p 0) (E'.differential_mul p 0) (g.formsMap_differential07Q9 p 0) x

/-- **`∇'` is integrable as soon as `∇` is**: base change preserves vanishing curvature. -/
theorem pullbackNabla07Q9_integrable
    (hint : CompletedDeRham.HasIntegrableConnection p (E.completedRing p 0)
      (fun a => E.forms p a 0) (E.wedge p 0) (E.deRham p 0) (V.carrier 0) nabla
      (E.isGradedLeibniz p 0)) :
    CompletedDeRham.HasIntegrableConnection p (E'.completedRing p 0)
      (fun a => E'.forms p a 0) (E'.wedge p 0) (E'.deRham p 0) ((V.pullback07Q9 g).carrier 0)
      (V.pullbackNabla07Q9 g nabla) (E'.isGradedLeibniz p 0) :=
  let := g.completedAlgebra07Q9 p 0
  CompletedDeRham.isCurvatureZero_baseChange p (E.completedRing p 0) (E'.completedRing p 0)
    (V.carrier 0) (fun a => E.forms p a 0) (fun a => E'.forms p a 0) (fun a => g.formsMap p 0 a)
    (E.wedge p 0) (E'.wedge p 0) (E.deRham p 0) (E'.deRham p 0) (E'.differential p 0) nabla
    (E'.differential_add p 0) (E'.differential_mul p 0) (g.formsMap_differential07Q9 p 0)
    (E.isGradedLeibniz p 0) (E'.isGradedLeibniz p 0) (fun a ω η => g.formsMap_wedge p 0 a ω η)
    (fun a ω => g.formsMap_deRham p 0 a ω) (wedge_one_anticomm 0)
    (E'.deRham_differential p 0) hint

/-! ### The identifications `β'_b` -/

/-- **The identification `β'_b : (D'(b) ⊗_{D'(0)} M'(0))^∧ ≃ M'(b)`.**  It is the composite of
the associativity `((D'(0) ⊗_{D(0)} M(0))^∧ ⊗_{D'(0)} D'(b))^∧ ≃ (D'(b) ⊗_{D(0)} M(0))^∧`, the
inverse associativity along `D(0) → D(b) → D'(b)` (the two composites `D(0) → D'(b)` agree by the
naturality of `g`), and the base change of `β_b` along `g_b`. -/
def pullbackBeta07Q9 (b : ℕ) :
    letI := E'.coprojectionAlgebra p b
    CompletedConnection.baseChangeCarrier p (E'.completedRing p 0) (E'.completedRing p b)
      ((V.pullback07Q9 g).carrier 0) ≃ₗ[E'.completedRing p b] (V.pullback07Q9 g).carrier b :=
  letI := g.completedAlgebra07Q9 p 0
  letI := E'.coprojectionAlgebra p b
  letI : Algebra (E.completedRing p 0) (E'.completedRing p b) :=
    ((E'.completedRingMap p (CosimplicialDPAlgebra.coprojection b)).comp
      (g.completedRingMap p 0)).toAlgebra
  haveI : IsScalarTower (E.completedRing p 0) (E'.completedRing p 0) (E'.completedRing p b) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI := E.coprojectionAlgebra p b
  letI := g.completedAlgebra07Q9 p b
  haveI : IsScalarTower (E.completedRing p 0) (E.completedRing p b) (E'.completedRing p b) :=
    IsScalarTower.of_algebraMap_eq fun x =>
      g.completedRingMap_naturality07Q9 p (CosimplicialDPAlgebra.coprojection b) x
  (CompletedConnection.baseChangeCompositeEquiv p (E.completedRing p 0) (E'.completedRing p 0)
      (E'.completedRing p b) (V.carrier 0)).trans
    ((CompletedConnection.baseChangeCompositeEquiv p (E.completedRing p 0) (E.completedRing p b)
        (E'.completedRing p b) (V.carrier 0)).symm.trans
      (adicCompletionCongr07Q9 (pAdicIdeal (A := E'.completedRing p b) p)
        (LinearEquiv.baseChange (E.completedRing p b) (E'.completedRing p b) _ _ (beta b))))

include hbeta in
/-- `β'_b` carries `1 ⊗ (1 ⊗ m)` to `1 ⊗ M(σ_b) m`. -/
theorem pullbackBeta07Q9_inclusion_inclusion (b : ℕ) (m : V.carrier 0) :
    letI := E'.coprojectionAlgebra p b
    V.pullbackBeta07Q9 g beta b
        (CompletedConnection.baseChangeInclusion p (E'.completedRing p 0) (E'.completedRing p b)
          ((V.pullback07Q9 g).carrier 0) (V.pullbackApp07Q9 g 0 m)) =
      V.pullbackApp07Q9 g b (V.map (CosimplicialDPAlgebra.coprojection b) m) := by
  let := g.completedAlgebra07Q9 p 0
  let := E'.coprojectionAlgebra p b
  let : Algebra (E.completedRing p 0) (E'.completedRing p b) :=
    ((E'.completedRingMap p (CosimplicialDPAlgebra.coprojection b)).comp
      (g.completedRingMap p 0)).toAlgebra
  have : IsScalarTower (E.completedRing p 0) (E'.completedRing p 0) (E'.completedRing p b) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  let := E.coprojectionAlgebra p b
  let := g.completedAlgebra07Q9 p b
  have : IsScalarTower (E.completedRing p 0) (E.completedRing p b) (E'.completedRing p b) :=
    IsScalarTower.of_algebraMap_eq fun x =>
      g.completedRingMap_naturality07Q9 p (CosimplicialDPAlgebra.coprojection b) x
  have h1 := CompletedConnection.baseChangeComposite_inclusion p (E.completedRing p 0)
    (E'.completedRing p 0) (E'.completedRing p b) (V.carrier 0) m
  have h2 := CompletedConnection.baseChangeComposite_inclusion p (E.completedRing p 0)
    (E.completedRing p b) (E'.completedRing p b) (V.carrier 0) m
  have h2' : (CompletedConnection.baseChangeCompositeEquiv p (E.completedRing p 0)
      (E.completedRing p b) (E'.completedRing p b) (V.carrier 0)).symm
        (CompletedConnection.baseChangeInclusion p (E.completedRing p 0) (E'.completedRing p b)
          (V.carrier 0) m) =
      CompletedConnection.baseChangeInclusion p (E.completedRing p b) (E'.completedRing p b)
        (CompletedConnection.baseChangeCarrier p (E.completedRing p 0) (E.completedRing p b)
          (V.carrier 0))
        (CompletedConnection.baseChangeInclusion p (E.completedRing p 0) (E.completedRing p b)
          (V.carrier 0) m) :=
    (LinearEquiv.symm_apply_eq _).mpr h2.symm
  have h3 : beta b (CompletedConnection.baseChangeInclusion p (E.completedRing p 0)
      (E.completedRing p b) (V.carrier 0) m) =
      V.map (CosimplicialDPAlgebra.coprojection b) m := by
    rw [CompletedConnection.baseChangeInclusion_apply, hbeta, one_smul]
  show adicCompletionCongr07Q9 (pAdicIdeal (A := E'.completedRing p b) p)
      (LinearEquiv.baseChange (E.completedRing p b) (E'.completedRing p b) _ _ (beta b))
      ((CompletedConnection.baseChangeCompositeEquiv p (E.completedRing p 0)
        (E.completedRing p b) (E'.completedRing p b) (V.carrier 0)).symm
        (CompletedConnection.baseChangeComposite p (E.completedRing p 0) (E'.completedRing p 0)
          (E'.completedRing p b) (V.carrier 0)
          (CompletedConnection.baseChangeInclusion p (E'.completedRing p 0)
            (E'.completedRing p b) _
            (CompletedConnection.baseChangeInclusion p (E.completedRing p 0)
              (E'.completedRing p 0) (V.carrier 0) m)))) = _
  rw [h1, h2', CompletedConnection.baseChangeInclusion_apply, adicCompletionCongr07Q9_of,
    LinearEquiv.baseChange_tmul, h3]
  rfl

include hbeta in
/-- **`β'` satisfies the hypothesis `hbeta` of the base-change connections**:
`β'_b (x ⊗ m') = x · M'(σ_b) m'`. -/
theorem pullbackBeta07Q9_tmul (b : ℕ) (x : E'.completedRing p b)
    (m : (V.pullback07Q9 g).carrier 0) :
    letI := E'.coprojectionAlgebra p b
    V.pullbackBeta07Q9 g beta b (AdicCompletion.of (pAdicIdeal (A := E'.completedRing p b) p)
        (E'.completedRing p b ⊗[E'.completedRing p 0] (V.pullback07Q9 g).carrier 0)
        (x ⊗ₜ[E'.completedRing p 0] m)) =
      x • (V.pullback07Q9 g).map (CosimplicialDPAlgebra.coprojection b) m := by
  let := E'.coprojectionAlgebra p b
  let := g.completedAlgebra07Q9 p 0
  rw [CompletedConnection.of_tmul_eq_smul_inclusion, map_smul]
  congr 1
  rw [← sub_eq_zero]
  refine eq_zero_of_baseChangeInclusion p
    (E'.completedRingMap p (CosimplicialDPAlgebra.coprojection b))
    (((V.pullbackBeta07Q9 g beta b).toLinearMap.toAddMonoidHom.comp
        (CompletedConnection.baseChangeInclusion p (E'.completedRing p 0) (E'.completedRing p b)
          ((V.pullback07Q9 g).carrier 0)).toAddMonoidHom) -
      ((V.pullback07Q9 g).map (CosimplicialDPAlgebra.coprojection b)).toAddMonoidHom)
    (fun c y => ?_) (fun y => ?_) m
  · show V.pullbackBeta07Q9 g beta b (CompletedConnection.baseChangeInclusion p _ _ _ (c • y)) -
        (V.pullback07Q9 g).map (CosimplicialDPAlgebra.coprojection b) (c • y) =
      E'.completedRingMap p (CosimplicialDPAlgebra.coprojection b) c •
        (V.pullbackBeta07Q9 g beta b (CompletedConnection.baseChangeInclusion p _ _ _ y) -
          (V.pullback07Q9 g).map (CosimplicialDPAlgebra.coprojection b) y)
    have e1 := (CompletedConnection.baseChangeInclusion p (E'.completedRing p 0)
      (E'.completedRing p b) ((V.pullback07Q9 g).carrier 0)).map_smulₛₗ c y
    have e2 := ((V.pullback07Q9 g).map (CosimplicialDPAlgebra.coprojection b)).map_smulₛₗ c y
    exact (congrArg₂ (· - ·) ((congrArg (V.pullbackBeta07Q9 g beta b) e1).trans
      ((V.pullbackBeta07Q9 g beta b).map_smul _ _)) e2).trans (smul_sub _ _ _).symm
  · show V.pullbackBeta07Q9 g beta b (CompletedConnection.baseChangeInclusion p _ _ _
        (CompletedConnection.baseChangeInclusion p _ _ _ y)) -
        (V.pullback07Q9 g).map (CosimplicialDPAlgebra.coprojection b)
          (CompletedConnection.baseChangeInclusion p _ _ _ y) = 0
    have := V.pullbackBeta07Q9_inclusion_inclusion g beta hbeta b y
    have hn := V.pullbackApp07Q9_naturality g (CosimplicialDPAlgebra.coprojection b) y
    rw [sub_eq_zero]
    exact this.trans hn

/-! ### Horizontality of `M(b) → M'(b)` -/

/-- The map `M(b) ⊗̂ Ω^1_{D(b)} → M'(b) ⊗̂ Ω^1_{D'(b)}` induced by `m ↦ 1 ⊗ m` and the forms map
of `g`. -/
abbrev pullbackValues07Q9 (b : ℕ) :
    V.obj 1 b →ₛₗ[g.completedRingMap p b] (V.pullback07Q9 g).obj 1 b :=
  CompletedDeRham.comparisonValues p (E.completedRing p b) (E'.completedRing p b)
    (g.completedRingMap p b) (V.carrier b) ((V.pullback07Q9 g).carrier b)
    (V.pullbackApp07Q9 g b) (fun i => E.forms p i b) (fun i => E'.forms p i b)
    (fun i => g.formsMap p b i) 1

/-- The defect `x ↦ ∇'_b (1 ⊗ x) - (1 ⊗ -)_*(∇_b x)` of the horizontality of `M(b) → M'(b)`. -/
def pullbackDefect07Q9 (b : ℕ) : V.carrier b →+ (V.pullback07Q9 g).obj 1 b :=
  AddMonoidHom.mk' (fun y => (V.pullback07Q9 g).baseChangeConnection
      (V.pullbackNabla07Q9 g nabla) (V.pullbackBeta07Q9 g beta) b (V.pullbackApp07Q9 g b y) -
      V.pullbackValues07Q9 g b (V.baseChangeConnection nabla beta b y))
    (fun y z => by
      simp only [map_add, CompletedConnection.map_add]
      abel)

/-- The horizontality defect of `M(b) → M'(b)`, as a formula. -/
theorem pullbackDefect07Q9_apply (b : ℕ) (y : V.carrier b) :
    V.pullbackDefect07Q9 g nabla beta b y = (V.pullback07Q9 g).baseChangeConnection
      (V.pullbackNabla07Q9 g nabla) (V.pullbackBeta07Q9 g beta) b (V.pullbackApp07Q9 g b y) -
      V.pullbackValues07Q9 g b (V.baseChangeConnection nabla beta b y) :=
  rfl

/-- The map induced on the values carries `x ⊗ d c` to `(1 ⊗ x) ⊗ d (g c)`. -/
theorem pullbackValues07Q9_differential (b : ℕ) (y : V.carrier b) (c : E.completedRing p b) :
    V.pullbackValues07Q9 g b (toCompletedTensor p (E.completedRing p b) (E.forms p 1 b)
        (V.carrier b) (y ⊗ₜ[E.completedRing p b] E.differential p b c)) =
      toCompletedTensor p (E'.completedRing p b) (E'.forms p 1 b)
        ((V.pullback07Q9 g).carrier b)
        (V.pullbackApp07Q9 g b y ⊗ₜ[E'.completedRing p b]
          E'.differential p b (g.completedRingMap p b c)) := by
  refine (CompletedDeRham.comparisonValues_of_tmul p (E.completedRing p b)
    (E'.completedRing p b) (g.completedRingMap p b) (V.carrier b)
    ((V.pullback07Q9 g).carrier b) (V.pullbackApp07Q9 g b) (fun i => E.forms p i b)
    (fun i => E'.forms p i b) (fun i => g.formsMap p b i) 1 y _).trans ?_
  rw [g.formsMap_differential07Q9]

/-- **The horizontality defect of `M(b) → M'(b)` is semilinear over `g_b`**: the two Leibniz
corrections cancel, the forms map of `g` carrying `d` to `d`. -/
theorem pullbackDefect07Q9_smul (b : ℕ) (c : E.completedRing p b) (y : V.carrier b) :
    V.pullbackDefect07Q9 g nabla beta b (c • y) =
      g.completedRingMap p b c • V.pullbackDefect07Q9 g nabla beta b y := by
  have e1 : V.pullbackApp07Q9 g b (c • y) =
      g.completedRingMap p b c • V.pullbackApp07Q9 g b y := map_smulₛₗ _ _ _
  have e2 := ((V.pullback07Q9 g).baseChangeConnection (V.pullbackNabla07Q9 g nabla)
    (V.pullbackBeta07Q9 g beta) b).leibniz (g.completedRingMap p b c)
    (V.pullbackApp07Q9 g b y)
  have e3 := (V.baseChangeConnection nabla beta b).leibniz c y
  rw [pullbackDefect07Q9_apply, pullbackDefect07Q9_apply, e1, e2, e3, map_add, map_smulₛₗ,
    pullbackValues07Q9_differential, smul_sub]
  abel

include hbeta in
/-- **The horizontality defect of `M(b) → M'(b)` vanishes on the image of the coprojection**:
there both connections are computed by the horizontality of the coprojections. -/
theorem pullbackDefect07Q9_coprojection (b : ℕ) (m : V.carrier 0) :
    V.pullbackDefect07Q9 g nabla beta b (V.map (CosimplicialDPAlgebra.coprojection b) m) = 0 := by
  have hbeta' := V.pullbackBeta07Q9_tmul g beta hbeta
  have l1 : V.pullbackApp07Q9 g b (V.map (CosimplicialDPAlgebra.coprojection b) m) =
      (V.pullback07Q9 g).map (CosimplicialDPAlgebra.coprojection b)
        (V.pullbackApp07Q9 g 0 m) :=
    V.pullbackApp07Q9_naturality g _ m
  have l2 : (V.pullback07Q9 g).baseChangeConnection (V.pullbackNabla07Q9 g nabla)
      (V.pullbackBeta07Q9 g beta) b ((V.pullback07Q9 g).map
        (CosimplicialDPAlgebra.coprojection b) (V.pullbackApp07Q9 g 0 m)) =
      (V.pullback07Q9 g).tensorMap (CosimplicialDPAlgebra.coprojection b) 1
        (V.pullbackNabla07Q9 g nabla (V.pullbackApp07Q9 g 0 m)) :=
    (V.pullback07Q9 g).baseChangeConnection_map_coprojection _ _ hbeta' b _
  have l3 := V.pullbackNabla07Q9_pullbackApp g nabla m
  have l4 : V.baseChangeConnection nabla beta b (V.map (CosimplicialDPAlgebra.coprojection b) m) =
      V.tensorMap (CosimplicialDPAlgebra.coprojection b) 1 (nabla m) :=
    V.baseChangeConnection_map_coprojection nabla beta hbeta b m
  have l5 := V.pullbackApp07Q9_tensorMap g (CosimplicialDPAlgebra.coprojection b) 1 (nabla m)
  rw [pullbackDefect07Q9_apply, sub_eq_zero, l1, l2, l3, l4]
  exact l5.symm

include hbeta in
/-- **The maps `M(b) → M'(b)`, `m ↦ 1 ⊗ m`, are horizontal for the base-change connections**:
the base-change connection of `(M', ∇', β')` at `1 ⊗ x` is the image of the base-change
connection of `(M, ∇, β)` at `x`.  This is the field `nabla_app` of
`Crystalline.CosimplicialCompletedPair.Hom`.

The defect of the square is additive and semilinear over `g_b`
(`Crystalline.CosimplicialCompletedModule.pullbackDefect07Q9_smul`); it vanishes on the image of
`M(0)` under the coprojection (`...pullbackDefect07Q9_coprojection`); and `β_b` makes that image
`p`-adically generate `M(b)`. -/
theorem baseChangeConnection_pullbackApp07Q9 (b : ℕ) (x : V.carrier b) :
    (V.pullback07Q9 g).baseChangeConnection (V.pullbackNabla07Q9 g nabla)
        (V.pullbackBeta07Q9 g beta) b (V.pullbackApp07Q9 g b x) =
      CompletedDeRham.comparisonValues p (E.completedRing p b) (E'.completedRing p b)
        (g.completedRingMap p b) (V.carrier b) ((V.pullback07Q9 g).carrier b)
        (V.pullbackApp07Q9 g b) (fun i => E.forms p i b) (fun i => E'.forms p i b)
        (fun i => g.formsMap p b i) 1 (V.baseChangeConnection nabla beta b x) := by
  rw [← sub_eq_zero]
  show V.pullbackDefect07Q9 g nabla beta b x = 0
  let := E.coprojectionAlgebra p b
  rw [← (beta b).apply_symm_apply x]
  exact eq_zero_of_baseChangeInclusion p (g.completedRingMap p b)
    ((V.pullbackDefect07Q9 g nabla beta b).comp (beta b).toLinearMap.toAddMonoidHom)
    (fun c z => by
      show V.pullbackDefect07Q9 g nabla beta b (beta b (c • z)) =
        g.completedRingMap p b c • V.pullbackDefect07Q9 g nabla beta b (beta b z)
      rw [map_smul, pullbackDefect07Q9_smul])
    (fun m => by
      show V.pullbackDefect07Q9 g nabla beta b
        (beta b (CompletedConnection.baseChangeInclusion p _ _ _ m)) = 0
      rw [CompletedConnection.baseChangeInclusion_apply, hbeta, one_smul]
      exact V.pullbackDefect07Q9_coprojection g nabla beta hbeta b m) _

include hbeta in
/-- In degree zero the base-change connection of `(M', ∇', β')` at `1 ⊗ m` is `(1 ⊗ -)_*(∇ m)`. -/
theorem pullbackBaseChangeConnection07Q9_zero_pullbackApp (m : V.carrier 0) :
    (V.pullback07Q9 g).baseChangeConnection (V.pullbackNabla07Q9 g nabla)
        (V.pullbackBeta07Q9 g beta) 0 (V.pullbackApp07Q9 g 0 m) =
      V.pullbackValues07Q9 g 0 (nabla m) :=
  ((V.pullback07Q9 g).baseChangeConnection_zero _ _ (V.pullbackBeta07Q9_tmul g beta hbeta)
    _).trans (V.pullbackNabla07Q9_pullbackApp g nabla m)

include hbeta in
/-- The horizontality defect of the coface `δ` for `(M', ∇', β')` vanishes at `1 ⊗ m`, given
that the coface is horizontal for `(M, ∇, β)`. -/
theorem pullbackHorizontalDefect07Q9_pullbackApp
    (hδ : ∀ x : V.carrier 0,
      V.baseChangeConnection nabla beta 1 (V.map (SimplexCategory.const ⦋0⦌ ⦋1⦌ 1) x) =
        V.tensorMap (SimplexCategory.const ⦋0⦌ ⦋1⦌ 1) 1 (nabla x))
    (m : V.carrier 0) :
    (V.pullback07Q9 g).horizontalDefect (V.pullbackNabla07Q9 g nabla)
      (V.pullbackBeta07Q9 g beta) (SimplexCategory.const ⦋0⦌ ⦋1⦌ 1)
        (V.pullbackApp07Q9 g 0 m) = 0 := by
  have l1 : (V.pullback07Q9 g).map (SimplexCategory.const ⦋0⦌ ⦋1⦌ 1)
      (V.pullbackApp07Q9 g 0 m) =
      V.pullbackApp07Q9 g 1 (V.map (SimplexCategory.const ⦋0⦌ ⦋1⦌ 1) m) :=
    (V.pullbackApp07Q9_naturality g _ m).symm
  have l2 := V.baseChangeConnection_pullbackApp07Q9 g nabla beta hbeta 1
    (V.map (SimplexCategory.const ⦋0⦌ ⦋1⦌ 1) m)
  have l4 : V.pullbackValues07Q9 g 1
        (V.tensorMap (SimplexCategory.const ⦋0⦌ ⦋1⦌ 1) 1 (nabla m)) =
      (V.pullback07Q9 g).tensorMap (SimplexCategory.const ⦋0⦌ ⦋1⦌ 1) 1
        (V.pullbackValues07Q9 g 0 (nabla m)) :=
    V.pullbackApp07Q9_tensorMap g _ 1 (nabla m)
  have hA : (V.pullback07Q9 g).baseChangeConnection (V.pullbackNabla07Q9 g nabla)
      (V.pullbackBeta07Q9 g beta) 1 ((V.pullback07Q9 g).map
        (SimplexCategory.const ⦋0⦌ ⦋1⦌ 1) (V.pullbackApp07Q9 g 0 m)) =
      (V.pullback07Q9 g).tensorMap (SimplexCategory.const ⦋0⦌ ⦋1⦌ 1) 1
        (V.pullbackValues07Q9 g 0 (nabla m)) := by
    rw [l1, l2, hδ m]
    exact l4
  have hB : (V.pullback07Q9 g).tensorMap (SimplexCategory.const ⦋0⦌ ⦋1⦌ 1) 1
        ((V.pullback07Q9 g).baseChangeConnection (V.pullbackNabla07Q9 g nabla)
          (V.pullbackBeta07Q9 g beta) 0 (V.pullbackApp07Q9 g 0 m)) =
      (V.pullback07Q9 g).tensorMap (SimplexCategory.const ⦋0⦌ ⦋1⦌ 1) 1
        (V.pullbackValues07Q9 g 0 (nabla m)) :=
    congrArg ((V.pullback07Q9 g).tensorMap (SimplexCategory.const ⦋0⦌ ⦋1⦌ 1) 1)
      (V.pullbackBaseChangeConnection07Q9_zero_pullbackApp g nabla beta hbeta m)
  rw [horizontalDefect_apply]
  exact sub_eq_zero.mpr (hA.trans hB.symm)

include hbeta in
/-- **The coface `δ : ⦋0⦌ ⟶ ⦋1⦌, 0 ↦ 1` is horizontal for the base-change connections of
`(M', ∇', β')`**, as soon as it is for those of `(M, ∇, β)`: this is the hypothesis `hδ` of the
base-change connections, for `M'`.  The defect is semilinear and vanishes on the image of `M(0)`,
where it is the image of the defect for `M` by the horizontality of `M(b) → M'(b)`. -/
theorem pullback07Q9_horizontal_coface
    (hδ : ∀ x : V.carrier 0,
      V.baseChangeConnection nabla beta 1 (V.map (SimplexCategory.const ⦋0⦌ ⦋1⦌ 1) x) =
        V.tensorMap (SimplexCategory.const ⦋0⦌ ⦋1⦌ 1) 1 (nabla x))
    (x : (V.pullback07Q9 g).carrier 0) :
    (V.pullback07Q9 g).baseChangeConnection (V.pullbackNabla07Q9 g nabla)
        (V.pullbackBeta07Q9 g beta) 1
        ((V.pullback07Q9 g).map (SimplexCategory.const ⦋0⦌ ⦋1⦌ 1) x) =
      (V.pullback07Q9 g).tensorMap (SimplexCategory.const ⦋0⦌ ⦋1⦌ 1) 1
        (V.pullbackNabla07Q9 g nabla x) := by
  have key : (V.pullback07Q9 g).horizontalDefect (V.pullbackNabla07Q9 g nabla)
      (V.pullbackBeta07Q9 g beta) (SimplexCategory.const ⦋0⦌ ⦋1⦌ 1) x = 0 := by
    let := g.completedAlgebra07Q9 p 0
    exact eq_zero_of_baseChangeInclusion p (D := E.completedRing p 0)
      (D' := E'.completedRing p 0) (M := V.carrier 0)
      (E'.completedRingMap p (SimplexCategory.const ⦋0⦌ ⦋1⦌ 1))
      ((V.pullback07Q9 g).horizontalDefect (V.pullbackNabla07Q9 g nabla)
        (V.pullbackBeta07Q9 g beta) (SimplexCategory.const ⦋0⦌ ⦋1⦌ 1))
      (fun c y => (V.pullback07Q9 g).horizontalDefect_smul _ _ _ c y)
      (fun m => V.pullbackHorizontalDefect07Q9_pullbackApp g nabla beta hbeta hδ m) x
  rw [horizontalDefect_apply, sub_eq_zero] at key
  exact key.trans (congrArg _ ((V.pullback07Q9 g).baseChangeConnection_zero _ _
    (V.pullbackBeta07Q9_tmul g beta hbeta) x))

include hbeta in
/-- **In degree zero the base-change connection of `(M', ∇', β')` is `∇'`.**  (For `(M, ∇, β)`
this is `Crystalline.CosimplicialCompletedModule.baseChangeConnection_zero`, from `hbeta`.) -/
theorem pullbackBaseChangeConnection07Q9_zero (y : (V.pullback07Q9 g).carrier 0) :
    (V.pullback07Q9 g).baseChangeConnection (V.pullbackNabla07Q9 g nabla)
        (V.pullbackBeta07Q9 g beta) 0 y =
      V.pullbackNabla07Q9 g nabla y :=
  (V.pullback07Q9 g).baseChangeConnection_zero _ _ (V.pullbackBeta07Q9_tmul g beta hbeta) y

end CosimplicialCompletedModule

end Crystalline

end
