module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RestrictScalarsLinearEquiv
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CoinvariantsMatrixMap
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LaumonAffineLineLinear

/-!
# The coinvariants of a restriction of scalars

For a finite extension `E/F` with basis `b`, a representation `σ : Γ → GL_m(E)` and a subgroup
`H`, the `H`-coinvariants of `Res_b σ` on `F^{m d}` are the `H`-coinvariants of `σ` on `E^m`, read
over `F`, along the identification `F^{m d} ≅ E^m` (`Stacks.EtaleCohomology.restrictScalarsEquiv`).
Under this identification the action of `Γ` is that of `Γ`, and the restriction of scalars of the
scalar matrix `e · 1_m` is multiplication by `e`.

## Main definitions

* `Stacks.EtaleCohomology.restrictScalarsCoinvariantsAddEquiv`: the additive equivalence between
  the coinvariants of `Res_b σ` and those of `σ`.

## Main results

* `Stacks.EtaleCohomology.span_eq_restrictScalars_span_of_smul_mem`: the `F`-span of an
  `E`-stable set is its `E`-span.
* `Stacks.EtaleCohomology.restrictScalarsCoinvariantsAddEquiv_coinvariantsFrobenius`: the
  equivalence carries the action of `φ` to the action of `φ`.
* `Stacks.EtaleCohomology.restrictScalarsCoinvariantsAddEquiv_scalar`: the equivalence carries the
  restriction of scalars of `e · 1_m` to multiplication by `e`.
-/

@[expose] public noncomputable section

open Representation Matrix

namespace Stacks.EtaleCohomology

/-- **The `F`-span of an `E`-stable set is its `E`-span.** -/
theorem span_eq_restrictScalars_span_of_smul_mem (F : Type*) {E M : Type*} [Field F] [Field E]
    [Algebra F E] [AddCommGroup M] [Module E M] [Module F M] [IsScalarTower F E M] {T : Set M}
    (hT : ∀ (e : E), ∀ x ∈ T, e • x ∈ T) :
    Submodule.span F T = (Submodule.span E T).restrictScalars F := by
  refine le_antisymm (Submodule.span_le_restrictScalars F E T) ?_
  let p : Submodule E M :=
    { carrier := Submodule.span F T
      add_mem' := fun ha hb => Submodule.add_mem _ ha hb
      zero_mem' := Submodule.zero_mem _
      smul_mem' := fun e x hx => by
        induction hx using Submodule.span_induction with
        | mem y hy => exact Submodule.subset_span (hT e y hy)
        | zero => simp
        | add y z _ _ hy hz =>
          rw [smul_add]
          exact add_mem hy hz
        | smul c y _ hy =>
          rw [smul_comm]
          exact Submodule.smul_mem _ c hy }
  exact fun x hx => (Submodule.span_le (p := p)).2 (fun y hy => Submodule.subset_span hy) hx

variable {F E : Type*} [Field F] [Field E] [Algebra F E] {d : ℕ} (b : Module.Basis (Fin d) F E)
  {Γ : Type*} [Group Γ] (H : Subgroup Γ) {m : ℕ} (σ : Γ →* GL (Fin m) E)

/-- `F^{m d} ≅ E^m` intertwines the action of `g` through `Res_b σ` with its action through `σ`. -/
theorem restrictScalarsEquiv_matrixRepresentation (g : Γ) (v : Fin (m * d) → F) :
    restrictScalarsEquiv b m (matrixRepresentation (restrictScalarsRep b σ) g v) =
      matrixRepresentation σ g (restrictScalarsEquiv b m v) := by
  rw [matrixRepresentation_apply, matrixRepresentation_apply, restrictScalarsRep_val,
    restrictScalarsEquiv_mulVec]

/-- `F^{m d} ≅ E^m` carries the kernel of the coinvariants of `Res_b σ` to the kernel of the
coinvariants of `σ`, read over `F`. -/
theorem map_restrictScalarsEquiv_coinvariantsKer :
    (Coinvariants.ker ((matrixRepresentation (restrictScalarsRep b σ)).comp H.subtype)).map
        (restrictScalarsEquiv b m).toLinearMap =
      (Coinvariants.ker ((matrixRepresentation σ).comp H.subtype)).restrictScalars F := by
  let T : Set (Fin m → E) := Set.range fun hw : H × (Fin m → E) =>
    ((matrixRepresentation σ).comp H.subtype) hw.1 hw.2 - hw.2
  have himage : (restrictScalarsEquiv b m).toLinearMap ''
      Set.range (fun hv : H × (Fin (m * d) → F) =>
        ((matrixRepresentation (restrictScalarsRep b σ)).comp H.subtype) hv.1 hv.2 - hv.2) =
        T := by
    rw [← Set.range_comp]
    refine Eq.trans ?_ ((Equiv.prodCongr (Equiv.refl H)
      (restrictScalarsEquiv b m).toEquiv).surjective.range_comp _)
    congr 1
    funext ⟨h, v⟩
    change restrictScalarsEquiv b m (matrixRepresentation (restrictScalarsRep b σ) h v - v) = _
    rw [map_sub, restrictScalarsEquiv_matrixRepresentation]
    rfl
  have hT : ∀ (e : E), ∀ x ∈ T, e • x ∈ T := by
    rintro e _ ⟨⟨h, w⟩, rfl⟩
    refine ⟨⟨h, e • w⟩, ?_⟩
    change matrixRepresentation σ (h : Γ) (e • w) - e • w =
      e • (matrixRepresentation σ (h : Γ) w - w)
    rw [map_smul, smul_sub]
  rw [Coinvariants.ker, Coinvariants.ker, Submodule.map_span, himage]
  exact span_eq_restrictScalars_span_of_smul_mem F hT

/-- **The coinvariants of `Res_b σ` are the coinvariants of `σ`**, as additive groups. -/
def restrictScalarsCoinvariantsAddEquiv :
    Coinvariants ((matrixRepresentation (restrictScalarsRep b σ)).comp H.subtype) ≃+
      Coinvariants ((matrixRepresentation σ).comp H.subtype) :=
  ((Submodule.Quotient.equiv _ _ (restrictScalarsEquiv b m)
    (map_restrictScalarsEquiv_coinvariantsKer b H σ)).trans
      (Submodule.Quotient.restrictScalarsEquiv F
        (Coinvariants.ker ((matrixRepresentation σ).comp H.subtype)))).toAddEquiv

/-- `restrictScalarsCoinvariantsAddEquiv` sends the class of `v` to the class of its image in
`E^m`. -/
theorem restrictScalarsCoinvariantsAddEquiv_mk (v : Fin (m * d) → F) :
    restrictScalarsCoinvariantsAddEquiv b H σ (Coinvariants.mk _ v) =
      Coinvariants.mk _ (restrictScalarsEquiv b m v) :=
  rfl

/-- The identification carries the action of `φ` to the action of `φ`. -/
theorem restrictScalarsCoinvariantsAddEquiv_coinvariantsFrobenius [H.Normal] (φ : Γ)
    (y : Coinvariants ((matrixRepresentation (restrictScalarsRep b σ)).comp H.subtype)) :
    restrictScalarsCoinvariantsAddEquiv b H σ
        (coinvariantsFrobenius H (restrictScalarsRep b σ) φ y) =
      coinvariantsFrobenius H σ φ (restrictScalarsCoinvariantsAddEquiv b H σ y) := by
  obtain ⟨v, rfl⟩ := Coinvariants.mk_surjective _ y
  change Coinvariants.mk _
      (restrictScalarsEquiv b m (matrixRepresentation (restrictScalarsRep b σ) φ v)) =
    Coinvariants.mk _ (matrixRepresentation σ φ (restrictScalarsEquiv b m v))
  rw [restrictScalarsEquiv_matrixRepresentation]

/-- **The identification carries the restriction of scalars of `e · 1_m` to multiplication
by `e`.** -/
theorem restrictScalarsCoinvariantsAddEquiv_scalar (e : E)
    (y : Coinvariants ((matrixRepresentation (restrictScalarsRep b σ)).comp H.subtype)) :
    restrictScalarsCoinvariantsAddEquiv b H σ
        (coinvariantsMatrixMap H (restrictScalarsRep b σ) (restrictScalarsScalarAlgHom b m e)
          (restrictScalarsScalarAlgHom_commute b σ e) y) =
      e • restrictScalarsCoinvariantsAddEquiv b H σ y := by
  obtain ⟨v, rfl⟩ := Coinvariants.mk_surjective _ y
  change Coinvariants.mk _ (restrictScalarsEquiv b m
      (restrictScalarsMatrix b (Matrix.scalar (Fin m) e) *ᵥ v)) =
    e • Coinvariants.mk _ (restrictScalarsEquiv b m v)
  rw [restrictScalarsEquiv_mulVec, ← map_smul]
  congr 1
  funext i
  rw [Matrix.scalar_apply, Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul]

end Stacks.EtaleCohomology

end
