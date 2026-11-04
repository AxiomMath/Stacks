module

public import StacksFrontier.CategoryTheory.FilteredDerived.Perfectness.CharSeries
public import StacksFrontier.CategoryTheory.FilteredDerived.Perfectness.Trace
public import StacksFrontier.LinearAlgebra.Matrix.AdditiveFunctorCharSeries

/-!
# The characteristic series and the traces of a perfect complex through an additive functor

Let `Φ : Mod_R ⥤ Mod_Λ` be an additive functor from modules over a ring `R` to modules over a
commutative ring `Λ`, with `Φ(O)` free over `Λ` for a free `R`-module `O` of rank one, and let
`φ : R →+* M_r(Λ)` be the attached representation `Stacks.CharSeriesTraceDetection.functorRep`.
For a bounded complex `Q` of finite projective `R`-modules with an endomorphism `g`, present each
term `Qⁱ` as a retract of a free module `Fin nᵢ → O` and let `Aᵢ ∈ M_{nᵢ}(R)` be the matrix of the
padded endomorphism `gⁱ`. Then:

* `Φ(Q)` is a bounded complex of finite projective `Λ`-modules;
* `det(1 - Φ(g) T | Φ(Q)) · ∏_{i odd} det(1 - φ(Aᵢ) T) = ∏_{i even} det(1 - φ(Aᵢ) T)`;
* `Tr(g ^ m | Q) = ∑ᵢ (-1)ⁱ Tr(Aᵢ ^ m)` in `R^♮` for `m > 0`.

These are the two sides of the key lemma
`Stacks.CharSeriesTraceDetection.coeff_det_eq_of_trace_pow` for the matrices `A = ⊕_{i even} Aᵢ`
and `B = ⊕_{i odd} Aᵢ`.

## Main results

* `Stacks.CharSeriesTraceDetection.finiteProjectiveComplex_functor`.
* `Stacks.CharSeriesTraceDetection.alternatingCharSeries_functor_mul_prod_odd`.
* `Stacks.CharSeriesTraceDetection.alternatingTrace_eq_sum_trq`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Matrix PowerSeries
open CategoryTheory.FilteredDerived

universe u v v' w

namespace Stacks.CharSeriesTraceDetection

variable {R : Type u} [Ring R] {Λ : Type w} [CommRing Λ]
  (Φ : ModuleCat.{v} R ⥤ ModuleCat.{v'} Λ) [Φ.Additive] {O : ModuleCat.{v} R} (eO : R ≃ₗ[R] O)
  {r : ℕ} (b : Φ.obj O ≃ₗ[Λ] (Fin r → Λ))

/-! ### Presentations of finite projective modules -/

section Presentation

include eO in
/-- A finite projective module is a retract of a free module `Fin n → O`. -/
theorem exists_retract_freeObj (M : ModuleCat.{v} R) (hfin : Module.Finite R M)
    (hproj : Module.Projective R M) :
    ∃ (n : ℕ) (p : freeObj O (Fin n) ⟶ M) (i : M ⟶ freeObj O (Fin n)), i ≫ p = 𝟙 M := by
  obtain ⟨n, f, g, -, -, hfg⟩ := Module.Finite.exists_comp_eq_id_of_projective R M
  refine ⟨n, ModuleCat.ofHom (f ∘ₗ (piRankOne eO (Fin n)).symm.toLinearMap),
    ModuleCat.ofHom ((piRankOne eO (Fin n)).toLinearMap ∘ₗ g), ?_⟩
  ext1
  refine LinearMap.ext fun x => ?_
  have := congrArg (fun h => h x) hfg
  simpa using this

variable (Q : CochainComplex (ModuleCat.{v} R) ℤ) (hQ : finiteProjectiveComplex R Q)

/-- The rank of the chosen free module of which `Qⁱ` is a retract. -/
def degRank (i : ℤ) : ℕ :=
  (exists_retract_freeObj eO (Q.X i) (hQ.2 i).2 (hQ.2 i).1).choose

/-- The chosen projection `(Fin nᵢ → O) ⟶ Qⁱ`. -/
def degProj (i : ℤ) : freeObj O (Fin (degRank eO Q hQ i)) ⟶ Q.X i :=
  (exists_retract_freeObj eO (Q.X i) (hQ.2 i).2 (hQ.2 i).1).choose_spec.choose

/-- The chosen section `Qⁱ ⟶ (Fin nᵢ → O)`. -/
def degIncl (i : ℤ) : Q.X i ⟶ freeObj O (Fin (degRank eO Q hQ i)) :=
  (exists_retract_freeObj eO (Q.X i) (hQ.2 i).2 (hQ.2 i).1).choose_spec.choose_spec.choose

/-- The chosen section followed by the chosen projection is the identity of `Qⁱ`. -/
theorem degIncl_comp_degProj (i : ℤ) : degIncl eO Q hQ i ≫ degProj eO Q hQ i = 𝟙 _ :=
  (exists_retract_freeObj eO (Q.X i) (hQ.2 i).2 (hQ.2 i).1).choose_spec.choose_spec.choose_spec

/-- The matrix `Aᵢ ∈ M_{nᵢ}(R)` of the padded endomorphism `gⁱ`. -/
def degMatrix (g : Q ⟶ Q) (i : ℤ) : Matrix (Fin (degRank eO Q hQ i)) (Fin (degRank eO Q hQ i)) R :=
  endMatrixO eO (degProj eO Q hQ i ≫ g.f i ≫ degIncl eO Q hQ i).hom

end Presentation

/-! ### The complex `Φ(Q)` -/

section Complex

variable (Q : CochainComplex (ModuleCat.{v} R) ℤ) (hQ : finiteProjectiveComplex R Q)

include eO b hQ in
/-- **`Φ(Q)` is a bounded complex of finite projective `Λ`-modules.** -/
theorem finiteProjectiveComplex_functor :
    finiteProjectiveComplex Λ ((Φ.mapHomologicalComplex (ComplexShape.up ℤ)).obj Q) := by
  obtain ⟨⟨⟨lo, hlo⟩, ⟨hi, hhi⟩⟩, -⟩ := id hQ
  refine ⟨⟨⟨lo, (CochainComplex.isStrictlyGE_iff _ lo).mpr fun i hi' => ?_⟩,
    ⟨hi, (CochainComplex.isStrictlyLE_iff _ hi).mpr fun i hi' => ?_⟩⟩, fun i => ⟨?_, ?_⟩⟩
  · exact Φ.map_isZero (Q.isZero_of_isStrictlyGE lo i hi')
  · exact Φ.map_isZero (Q.isZero_of_isStrictlyLE hi i hi')
  · exact functor_obj_projective_of_retract Φ b _ (degProj eO Q hQ i) (degIncl eO Q hQ i)
      (degIncl_comp_degProj eO Q hQ i)
  · exact functor_obj_finite_of_retract Φ b _ (degProj eO Q hQ i) (degIncl eO Q hQ i)
      (degIncl_comp_degProj eO Q hQ i)

/-- The characteristic series of `Φ(gⁱ)` on `Φ(Qⁱ)` is `det(1 - φ(Aᵢ) T)`. -/
theorem coe_charUnitAt_functor (g : Q ⟶ Q) (i : ℤ) :
    (charUnitAt Λ _ (finiteProjectiveComplex_functor Φ eO b Q hQ) i
        (((Φ.mapHomologicalComplex (ComplexShape.up ℤ)).map g).f i) : PowerSeries Λ) =
      (1 - (X : PowerSeries Λ) • (blockMap (functorRep Φ eO b) (Fin (degRank eO Q hQ i))
        (degMatrix eO Q hQ g i)).map (C (R := Λ))).det := by
  have := Module.Finite.of_basis (functorFreeBasis Φ b (O := O) (Fin (degRank eO Q hQ i)))
  have := Module.Projective.of_basis (functorFreeBasis Φ b (O := O) (Fin (degRank eO Q hQ i)))
  have := functor_obj_finite_of_retract Φ b _ (degProj eO Q hQ i) (degIncl eO Q hQ i)
    (degIncl_comp_degProj eO Q hQ i)
  have := functor_obj_projective_of_retract Φ b _ (degProj eO Q hQ i) (degIncl eO Q hQ i)
    (degIncl_comp_degProj eO Q hQ i)
  rw [coe_charUnitAt]
  exact charSeries_functor_map_retract Φ eO b _ (degProj eO Q hQ i) (degIncl eO Q hQ i)
    (degIncl_comp_degProj eO Q hQ i) (g.f i)

/-- **The characteristic series of `Φ(g)` on `Φ(Q)` in terms of the matrices `Aᵢ`.** For a
finite set `S` of degrees outside of which `Q` vanishes,
`det(1 - Φ(g) T | Φ(Q)) · ∏_{i ∈ S odd} det(1 - φ(Aᵢ) T) = ∏_{i ∈ S even} det(1 - φ(Aᵢ) T)`. -/
theorem alternatingCharSeries_functor_mul_prod_odd (g : Q ⟶ Q) (S : Finset ℤ)
    (hS : ∀ i ∉ S, IsZero (Q.X i)) :
    (alternatingCharSeries Λ _ (finiteProjectiveComplex_functor Φ eO b Q hQ)
        ((Φ.mapHomologicalComplex (ComplexShape.up ℤ)).map g) : PowerSeries Λ) *
      ∏ i ∈ S.filter (fun i => ¬ Even i),
        (1 - (X : PowerSeries Λ) • (blockMap (functorRep Φ eO b) (Fin (degRank eO Q hQ i))
          (degMatrix eO Q hQ g i)).map (C (R := Λ))).det =
      ∏ i ∈ S.filter (fun i => Even i),
        (1 - (X : PowerSeries Λ) • (blockMap (functorRep Φ eO b) (Fin (degRank eO Q hQ i))
          (degMatrix eO Q hQ g i)).map (C (R := Λ))).det := by
  classical
  set hΦ := finiteProjectiveComplex_functor Φ eO b Q hQ
  set u : ℤ → (PowerSeries Λ)ˣ := fun i => charUnitAt Λ _ hΦ i
    (((Φ.mapHomologicalComplex (ComplexShape.up ℤ)).map g).f i) with hu
  have hsupp : Function.mulSupport (fun i => if Even i then u i else (u i)⁻¹) ⊆ S := by
    intro i hi
    by_contra hiS
    apply hi
    have h1 : u i = 1 := charUnitAt_eq_one_of_isZero Λ _ hΦ i _ (Φ.map_isZero (hS i hiS))
    simp [h1]
  rw [alternatingCharSeries, finprod_eq_prod_of_mulSupport_subset _ hsupp, Units.coe_prod,
    ← Finset.prod_filter_mul_prod_filter_not S (fun i => Even i), mul_assoc,
    ← Finset.prod_mul_distrib]
  have hodd : ∀ i ∈ S.filter (fun i => ¬ Even i),
      ((if Even i then u i else (u i)⁻¹ : (PowerSeries Λ)ˣ) : PowerSeries Λ) *
        (1 - (X : PowerSeries Λ) • (blockMap (functorRep Φ eO b) (Fin (degRank eO Q hQ i))
          (degMatrix eO Q hQ g i)).map (C (R := Λ))).det = 1 := by
    intro i hi
    rw [if_neg (Finset.mem_filter.1 hi).2, ← coe_charUnitAt_functor Φ eO b Q hQ g i]
    exact Units.inv_mul _
  rw [Finset.prod_congr rfl hodd, Finset.prod_const_one, mul_one]
  refine Finset.prod_congr rfl fun i hi => ?_
  rw [if_pos (Finset.mem_filter.1 hi).2]
  exact coe_charUnitAt_functor Φ eO b Q hQ g i

/-- **The traces of the powers of `g` on `Q` in terms of the matrices `Aᵢ`.** For `m > 0` and
an endomorphism `h` of `Q` that is degreewise the `m`-th power of `g`,
`Tr(h | Q) = ∑_{i ∈ S} (-1)ⁱ Tr(Aᵢ ^ m)` in `R^♮`. -/
theorem alternatingTrace_eq_sum_trq (g h : Q ⟶ Q) {m : ℕ} (hm : 0 < m)
    (hgh : ∀ i, (h.f i).hom = (g.f i).hom ^ m) (S : Finset ℤ)
    (hS : ∀ i ∉ S, IsZero (Q.X i)) :
    alternatingTrace R Q hQ h =
      ∑ i ∈ S, (if Even i then trq _ (degMatrix eO Q hQ g i ^ m)
        else -trq _ (degMatrix eO Q hQ g i ^ m)) := by
  classical
  have hterm : ∀ i, (by
      let : Module.Projective R (Q.X i) := (hQ.2 i).1
      let : Module.Finite R (Q.X i) := (hQ.2 i).2
      exact Stacks.Trace.projectiveModuleTrace R (Q.X i) (h.f i).hom :
        AdditiveCommutatorQuotient R) = trq _ (degMatrix eO Q hQ g i ^ m) := by
    intro i
    let : Module.Projective R (Q.X i) := (hQ.2 i).1
    let : Module.Finite R (Q.X i) := (hQ.2 i).2
    show Stacks.Trace.projectiveModuleTrace R (Q.X i) (h.f i).hom = _
    rw [hgh i]
    exact projectiveModuleTrace_pow_eq_trq eO _ (degProj eO Q hQ i) (degIncl eO Q hQ i)
      (degIncl_comp_degProj eO Q hQ i) (g.f i) hm
  unfold alternatingTrace
  simp only [hterm]
  refine finsum_eq_sum_of_support_subset _ fun i hi => ?_
  by_contra hiS
  apply hi
  have hz : IsZero (Q.X i) := hS i hiS
  have := ModuleCat.subsingleton_of_isZero hz
  have h0 : trq _ (degMatrix eO Q hQ g i ^ m) = 0 := by
    rw [← hterm i]
    let : Module.Projective R (Q.X i) := (hQ.2 i).1
    let : Module.Finite R (Q.X i) := (hQ.2 i).2
    exact projectiveModuleTrace_eq_zero_of_subsingleton R (Q.X i) _
  simp only [h0, neg_zero, ite_self]

end Complex

end Stacks.CharSeriesTraceDetection
