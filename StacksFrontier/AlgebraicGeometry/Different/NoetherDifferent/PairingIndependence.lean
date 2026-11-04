module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Different.NoetherDifferent.Pairing
public import StacksFrontier.AlgebraicGeometry.Discriminant.DualizingModuleComparison
public import StacksFrontier.AlgebraicGeometry.Discriminant.NoetherPairingNaturality
public import StacksFrontier.RingTheory.TraceElement.FiniteFlat

/-!
# The Noether pairing does not depend on the factorization

The canonical pairing of the relative dualizing module with the diagonal annihilator is
constructed from a finite-open factorization. This file shows that the pairing is carried along
the canonical comparison of the dualizing modules attached to two factorizations, so that the
map it induces from the diagonal annihilator to the dual of the dualizing module is bijective
for one factorization exactly when it is for any other.

## Main definitions

* `Stacks.Discriminant.diagonalAnnihilatorTargetEquiv` identifies the scalar extension of the
  diagonal annihilator along a map inducing an open immersion on spectra with the diagonal
  annihilator of the target.
* `Stacks.Discriminant.diagonalAnnihilatorBaseChangeEquiv` is its instance for the intermediate
  algebra of a finite-open factorization.

## Main results

* `Stacks.Discriminant.dualizingModule_finite`: the relative dualizing module is finite over the
  target when the base is Noetherian.
* `Stacks.Discriminant.isNoetherPairing_unique`: the contraction formula determines the pairing.
* `Stacks.Discriminant.noetherPairing_selfFactorization_tmul`: for the self factorization of a
  finite algebra the pairing is plain contraction.
* `Stacks.Discriminant.noetherPairing_naturality` of
  `StacksFrontier.AlgebraicGeometry.Discriminant.NoetherPairingNaturality`, re-exported here, is
  the naturality of the pairing in the factorization, with no finiteness hypothesis.
* `Stacks.Discriminant.noetherPairing_flip_bijective_of_factorization`: the induced map from the
  diagonal annihilator to the dual of the dualizing module is bijective for one factorization
  exactly when it is for another.

## Implementation notes

Naturality is reduced to the case of `Stacks.Discriminant.selfFactorization`, the factorization
of a finite algebra through itself. There the comparison of dualizing modules has an explicit
formula on pure tensors, because the intermediate algebra of the self factorization is the
target itself and therefore dominates every other intermediate algebra. This is why the
statements here assume the target finite over the base; that is the situation in which they are
used, where the general quasi-finite case has already been localized to a finite one. Naturality
itself needs no such hypothesis and is taken from
`StacksFrontier.AlgebraicGeometry.Discriminant.NoetherPairingNaturality`, which proves it through a
common refinement of the two factorizations instead; the reduction to the self factorization
below is what
`Stacks.Discriminant.noetherPairing_naturality_selfFactorization` records.

## References

* [Stacks Project, Tag 0BVP](https://stacks.math.columbia.edu/tag/0BVP)
* [Stacks Project, Tag 0BT1](https://stacks.math.columbia.edu/tag/0BT1)
-/

@[expose] public section

open scoped TensorProduct

namespace Stacks.Discriminant

universe u v w x y

attribute [local instance] algebraDualModule

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]

/-- Over a Noetherian base the relative dualizing module is a finite module over the target. -/
theorem dualizingModule_finite [IsNoetherianRing A]
    (F : FiniteOpenFactorization.{u, v, w} A B) :
    Module.Finite B (dualizingModule F) := by
  have : IsScalarTower A F.middle (Module.Dual A F.middle) := ⟨fun a c f => by
    ext x
    simpa [Algebra.smul_def, mul_assoc] using map_smul f a (c * x)⟩
  have : Module.Finite A (Module.Dual A F.middle) := inferInstance
  have : Module.Finite F.middle (Module.Dual A F.middle) :=
    Module.Finite.of_restrictScalars_finite A F.middle _
  let e : dualizingModule F ≃ₗ[B] B ⊗[F.middle] Module.Dual A F.middle :=
    (TensorProduct.comm F.middle (Module.Dual A F.middle) B).toAddEquiv.linearEquiv B
  exact Module.Finite.equiv e.symm

/-- Along a map inducing an open immersion on spectra, the scalar extension of the diagonal
annihilator of the source is the diagonal annihilator of the target. -/
noncomputable def diagonalAnnihilatorTargetEquiv (A : Type u) (B' : Type v) (B : Type w)
    [CommRing A] [CommRing B'] [CommRing B]
    [Algebra A B'] [Algebra B' B] [Algebra A B] [IsScalarTower A B' B]
    [Algebra.FiniteType A B']
    (h : AlgebraicGeometry.IsOpenImmersion (AlgebraicGeometry.Spec.map
      (CommRingCat.ofHom (RingHom.ulift.{max v w, max v w} (algebraMap B' B))))) :
    B ⊗[B'] (↑(diagonalAnnihilator A B')) ≃ₗ[B] ↑(diagonalAnnihilator A B) := by
  let f := diagonalAnnihilatorBaseChange A B' B
  have hRange := range_diagonalAnnihilatorBaseChange A B' B h
  have hInj := diagonalAnnihilatorBaseChange_injective A B' B h
  let fJ : B ⊗[B'] (↑(diagonalAnnihilator A B')) →ₗ[B]
      ↑((diagonalAnnihilator A B).restrictScalars B) :=
    f.codRestrict ((diagonalAnnihilator A B).restrictScalars B) (fun z => by
      rw [← hRange]
      exact ⟨z, rfl⟩)
  refine LinearEquiv.ofBijective fJ ⟨fun a b hab => hInj (congrArg Subtype.val hab), ?_⟩
  intro j
  obtain ⟨z, hz⟩ := (show j.1 ∈ LinearMap.range f by rw [hRange]; exact j.2)
  exact ⟨z, Subtype.ext hz⟩

/-- The equivalence `diagonalAnnihilatorTargetEquiv` sends an element to its image under
`diagonalAnnihilatorBaseChange`. -/
@[simp]
theorem diagonalAnnihilatorTargetEquiv_apply (A : Type u) (B' : Type v) (B : Type w)
    [CommRing A] [CommRing B'] [CommRing B]
    [Algebra A B'] [Algebra B' B] [Algebra A B] [IsScalarTower A B' B]
    [Algebra.FiniteType A B']
    (h : AlgebraicGeometry.IsOpenImmersion (AlgebraicGeometry.Spec.map
      (CommRingCat.ofHom (RingHom.ulift.{max v w, max v w} (algebraMap B' B)))))
    (z : B ⊗[B'] (↑(diagonalAnnihilator A B'))) :
    (diagonalAnnihilatorTargetEquiv A B' B h z : B ⊗[A] B) =
      diagonalAnnihilatorBaseChange A B' B z := rfl

/-- The scalar extension to the target of the diagonal annihilator of the intermediate algebra
is the diagonal annihilator of the target. -/
noncomputable def diagonalAnnihilatorBaseChangeEquiv
    (F : FiniteOpenFactorization.{u, v, w} A B) :
    B ⊗[F.middle] (↑(diagonalAnnihilator A F.middle)) ≃ₗ[B]
      ↑(diagonalAnnihilator A B) :=
  diagonalAnnihilatorTargetEquiv A F.middle B
    (specMap_ulift_isOpenImmersion (algebraMap F.middle B)
      F.isOpenEmbedding_comap F.awayMap_bijective)

/-- The equivalence `diagonalAnnihilatorBaseChangeEquiv` sends an element to its image under
`diagonalAnnihilatorBaseChange`. -/
@[simp]
theorem diagonalAnnihilatorBaseChangeEquiv_apply
    (F : FiniteOpenFactorization.{u, v, w} A B)
    (z : B ⊗[F.middle] (↑(diagonalAnnihilator A F.middle))) :
    (diagonalAnnihilatorBaseChangeEquiv F z : B ⊗[A] B) =
      diagonalAnnihilatorBaseChange A F.middle B z := rfl

/-- Induction on the diagonal annihilator along the surjection from the scalar extension of the
diagonal annihilator of the intermediate algebra. -/
private theorem diagonalAnnihilator_induction_on (F : FiniteOpenFactorization.{u, v, w} A B)
    {P : ↑(diagonalAnnihilator A B) → Prop} (j : ↑(diagonalAnnihilator A B)) (zero : P 0)
    (add : ∀ x y, P x → P y → P (x + y))
    (tmul : ∀ (y : B) (j' : ↑(diagonalAnnihilator A F.middle)),
      P (diagonalAnnihilatorBaseChangeEquiv F (y ⊗ₜ[F.middle] j'))) : P j := by
  obtain ⟨z, rfl⟩ := (diagonalAnnihilatorBaseChangeEquiv F).surjective j
  induction z using TensorProduct.induction_on with
  | zero => rw [LinearEquiv.map_zero]; exact zero
  | add z t hz ht => rw [LinearEquiv.map_add]; exact add _ _ hz ht
  | tmul y j' => exact tmul y j'

/-- The contraction formula determines the pairing: two pairings satisfying it agree. -/
theorem isNoetherPairing_unique
    (F : FiniteOpenFactorization.{u, v, w} A B)
    (p q : dualizingModule F →ₗ[B] (↑(diagonalAnnihilator A B) →ₗ[B] B))
    (hp : IsNoetherPairing F p) (hq : IsNoetherPairing F q) : p = q := by
  refine LinearMap.ext fun ω => ?_
  induction ω using dualizingModule.induction_on with
  | zero => exact (map_zero p).trans (map_zero q).symm
  | add ω η hω hη =>
      exact (map_add p ω η).trans ((congrArg₂ (· + ·) hω hη).trans (map_add q ω η).symm)
  | tmul f b =>
      refine LinearMap.ext fun j => ?_
      induction j using diagonalAnnihilator_induction_on F with
      | zero => rw [map_zero, map_zero]
      | add z t hz ht => rw [map_add, map_add, hz, ht]
      | tmul y j' =>
          exact (hp f b y j' _ rfl).trans (hq f b y j' _ rfl).symm

/-- Contracting against a functional on the target the image of a pure tensor from the finite
model computes the contraction over the intermediate algebra. -/
private theorem tensorContract_diagonalAnnihilatorBaseChange
    (F : FiniteOpenFactorization.{u, v, w} A B)
    (φ : Module.Dual A B) (y : B) (j' : ↑(diagonalAnnihilator A F.middle)) :
    tensorContract A B φ
        (diagonalAnnihilatorBaseChange A F.middle B (y ⊗ₜ[F.middle] j')) =
      y * algebraMap F.middle B (tensorContract A F.middle
        (φ.comp (IsScalarTower.toAlgHom A F.middle B).toLinearMap) j'.1) := by
  set ι : F.middle →ₐ[A] B := IsScalarTower.toAlgHom A F.middle B with hι
  have hM : diagonalAnnihilatorBaseChange A F.middle B (1 ⊗ₜ[F.middle] j') =
      Algebra.TensorProduct.map ι ι j'.1 := by
    simp [diagonalAnnihilatorBaseChange, LinearMap.toSpanSingleton_apply, hι]
  have hmem : Algebra.TensorProduct.map ι ι j'.1 ∈ diagonalAnnihilator A B := by
    rw [← hM]
    exact (diagonalAnnihilatorBaseChangeEquiv F (1 ⊗ₜ[F.middle] j')).2
  have hsmul : diagonalAnnihilatorBaseChange A F.middle B (y ⊗ₜ[F.middle] j') =
      y • Algebra.TensorProduct.map ι ι j'.1 := by
    rw [← hM, ← map_smul]
    congr 1
    rw [TensorProduct.smul_tmul']
    congr 1
    simp
  have hcontract : ∀ z : F.middle ⊗[A] F.middle,
      tensorContract A B φ (Algebra.TensorProduct.map ι ι z) =
        algebraMap F.middle B
          (tensorContract A F.middle (φ.comp ι.toLinearMap) z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp [tensorContract]
    | tmul c d =>
        simp [tensorContract, TensorProduct.lift.tmul, Algebra.TensorProduct.map_tmul,
          Algebra.smul_def, hι, IsScalarTower.algebraMap_apply A F.middle B]
    | add z t hz ht => simp [hz, ht]
  rw [hsmul, tensorContract_smul_diagonal A B φ y ⟨_, hmem⟩, hcontract]

/-- The canonical map from the base change of the diagonal annihilator along the identity is the
identity. -/
private theorem diagonalAnnihilatorBaseChange_self
    (j : ↑(diagonalAnnihilator A B)) :
    (j : B ⊗[A] B) = diagonalAnnihilatorBaseChange A B B (1 ⊗ₜ[B] j) := by
  have hId : IsScalarTower.toAlgHom A B B = AlgHom.id A B := by
    ext x
    rfl
  simp [diagonalAnnihilatorBaseChange, LinearMap.toSpanSingleton_apply, hId,
    Algebra.TensorProduct.map_id]

section SelfFactorization

variable [Module.Finite A B]

/-- The pairing for the self factorization of a finite algebra is plain contraction against the
diagonal annihilator. -/
theorem noetherPairing_selfFactorization_tmul
    (φ : Module.Dual A B) (b : B) (j : ↑(diagonalAnnihilator A B)) :
    noetherPairing (selfFactorization A B)
        (dualizingModule.tmul (selfFactorization A B) φ b) j =
      b * tensorContract A B φ j.1 := by
  refine (noetherPairing_apply_of_eq_baseChange (selfFactorization A B) φ b 1 j j
    (diagonalAnnihilatorBaseChange_self j)).trans ?_
  show b * 1 * algebraMap B B (tensorContract A B φ (j : B ⊗[A] B)) = _
  simp

/-- The canonical comparison out of the self factorization restricts a functional on the target
to the intermediate algebra. -/
private theorem dualizingModuleEquiv_selfFactorization_tmul [IsNoetherianRing A]
    (F : FiniteOpenFactorization.{u, v, w} A B) (φ : Module.Dual A B) (b : B) :
    dualizingModuleEquiv (selfFactorization A B) F
        (dualizingModule.tmul (selfFactorization A B) φ b) =
      dualizingModule.tmul F
        (φ.comp (IsScalarTower.toAlgHom A F.middle B).toLinearMap) b :=
  dualizingModuleEquiv_tmul (selfFactorization A B) F (selfFactorization A B)
    (hH := fun _ _ h => h) (AlgHom.id A B)
    (IsScalarTower.toAlgHom A F.middle B) (fun _ => rfl) (fun _ => rfl) φ b

/-- Naturality of the pairing against the self factorization, on a pure tensor. -/
private theorem noetherPairing_naturality_selfFactorization_tmul [IsNoetherianRing A]
    (F : FiniteOpenFactorization.{u, v, w} A B)
    (φ : Module.Dual A B) (b : B) (j : ↑(diagonalAnnihilator A B)) :
    noetherPairing F (dualizingModuleEquiv (selfFactorization A B) F
        (dualizingModule.tmul (selfFactorization A B) φ b)) j =
      noetherPairing (selfFactorization A B)
        (dualizingModule.tmul (selfFactorization A B) φ b) j := by
  induction j using diagonalAnnihilator_induction_on F with
  | zero => rw [map_zero, map_zero]
  | add z t hz ht => rw [map_add, map_add, hz, ht]
  | tmul y j' =>
      have h1 : dualizingModuleEquiv (selfFactorization A B) F
            (dualizingModule.tmul (selfFactorization A B) φ b) =
          dualizingModule.tmul F
            (φ.comp (IsScalarTower.toAlgHom A F.middle B).toLinearMap) b :=
        dualizingModuleEquiv_selfFactorization_tmul F φ b
      have h2 : noetherPairing (selfFactorization A B)
            (dualizingModule.tmul (selfFactorization A B) φ b)
              (diagonalAnnihilatorBaseChangeEquiv F (y ⊗ₜ[F.middle] j')) =
          b * tensorContract A B φ
            (diagonalAnnihilatorBaseChange A F.middle B (y ⊗ₜ[F.middle] j')) :=
        noetherPairing_selfFactorization_tmul φ b _
      have h3 : noetherPairing F
            (dualizingModule.tmul F
              (φ.comp (IsScalarTower.toAlgHom A F.middle B).toLinearMap) b)
            (diagonalAnnihilatorBaseChangeEquiv F (y ⊗ₜ[F.middle] j')) =
          b * y * algebraMap F.middle B (tensorContract A F.middle
            (φ.comp (IsScalarTower.toAlgHom A F.middle B).toLinearMap) j'.1) :=
        noetherPairing_apply_of_eq_baseChange F _ b y j' _ rfl
      rw [h1, h2, h3, tensorContract_diagonalAnnihilatorBaseChange]
      ring

/-- Naturality of the pairing against the self factorization. -/
private theorem noetherPairing_naturality_selfFactorization [IsNoetherianRing A]
    (F : FiniteOpenFactorization.{u, v, w} A B)
    (ξ : dualizingModule (selfFactorization A B))
    (j : ↑(diagonalAnnihilator A B)) :
    noetherPairing F (dualizingModuleEquiv (selfFactorization A B) F ξ) j =
      noetherPairing (selfFactorization A B) ξ j := by
  induction ξ using dualizingModule.induction_on generalizing j with
  | zero => simp
  | add ξ η hξ hη => simp [hξ, hη]
  | tmul φ b => exact noetherPairing_naturality_selfFactorization_tmul F φ b j

omit [Module.Finite A B] in
/-- The map induced by the canonical pairing is bijective for one finite-open factorization
exactly when it is for another.

Finiteness of the target is not used: the comparison of the two pairings it rests on,
`Stacks.Discriminant.noetherPairing_naturality`, needs no such hypothesis. -/
theorem noetherPairing_flip_bijective_of_factorization [IsNoetherianRing A]
    (F : FiniteOpenFactorization.{u, v, w} A B)
    (G : FiniteOpenFactorization.{u, v, x} A B)
    (hG : Function.Bijective (noetherPairing G).flip) :
    Function.Bijective (noetherPairing F).flip := by
  let eω := dualizingModuleEquiv F G
  let eHom : (dualizingModule F →ₗ[B] B) ≃ₗ[B] (dualizingModule G →ₗ[B] B) :=
    LinearEquiv.arrowCongr eω (LinearEquiv.refl B B)
  have hcompare (j : ↑(diagonalAnnihilator A B)) :
      eHom ((noetherPairing F).flip j) = (noetherPairing G).flip j := by
    refine LinearMap.ext fun ψ => ?_
    show noetherPairing F (eω.symm ψ) j = noetherPairing G ψ j
    simpa [eω] using (noetherPairing_naturality F G (eω.symm ψ) j).symm
  refine ⟨fun j k hjk => hG.1 ?_, fun φ => ?_⟩
  · calc
      (noetherPairing G).flip j = eHom ((noetherPairing F).flip j) := (hcompare j).symm
      _ = eHom ((noetherPairing F).flip k) := congrArg eHom hjk
      _ = (noetherPairing G).flip k := hcompare k
  · obtain ⟨j, hj⟩ := hG.2 (eHom φ)
    exact ⟨j, eHom.injective ((hcompare j).trans hj)⟩

end SelfFactorization

end Stacks.Discriminant

end
