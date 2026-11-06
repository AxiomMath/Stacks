module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Discriminant.TraceElement
public import StacksFrontier.AlgebraicGeometry.Different.NoetherDifferent.Basic
public import StacksFrontier.AlgebraicGeometry.Different.NoetherDifferent.Localization

/-!
# The canonical pairing with the diagonal annihilator

For a finite-open factorization of a commutative algebra, the relative dualizing module pairs
canonically with the diagonal annihilator, the annihilator of the kernel of multiplication. On
the finite intermediate algebra this pairing contracts an `A`-linear functional against the first
tensor factor.

## Main definitions

* `Stacks.Discriminant.tensorContract` contracts the first factor of a tensor against a linear
  functional.
* `Stacks.Discriminant.IsNoetherPairing` records the formula defining the pairing.
* `Stacks.Discriminant.noetherPairingWithFormula` constructs the canonical bilinear pairing
  together with its defining formula.
* `Stacks.Discriminant.noetherPairing` is its underlying linear map.

## Main results

* `Stacks.Discriminant.specMap_ulift_isOpenImmersion`: the ring-theoretic criterion of an open
  embedding on spectra together with bijectivity of the away localizations makes the induced
  morphism of spectra an open immersion.
* `Stacks.Discriminant.noetherPairing_apply_of_eq_baseChange`: the canonical pairing satisfies
  the contraction formula on tensors coming from the finite model.

## Implementation notes

A bilinear pairing is represented as a linear map into a linear-map space. The construction is
returned together with its defining formula, so its value is characterized without unfolding an
opaque choice. The formula is stated for an element of the target annihilator whose underlying
tensor is the canonical base change of an element of the annihilator for the finite model.

## References

* [Stacks Project, Tag 0BVP](https://stacks.math.columbia.edu/tag/0BVP)
-/

@[expose] public section

open scoped TensorProduct

namespace Stacks.Discriminant

universe u v w

section SpecMapProof

open Topology CategoryTheory Opposite

/-- A ring map whose induced map on prime spectra is an open embedding, and whose away
localizations over basic opens inside the image are bijective, induces an open immersion on
spectra after lifting to a common universe. -/
theorem specMap_ulift_isOpenImmersion {C : Type v} {D : Type w}
    [CommRing C] [CommRing D] (f : C →+* D)
    (hopen : Topology.IsOpenEmbedding (PrimeSpectrum.comap f))
    (haway : ∀ g : C,
      (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum C)) ⊆
        Set.range (PrimeSpectrum.comap f) →
      Function.Bijective (Localization.awayMap f g)) :
    AlgebraicGeometry.IsOpenImmersion
      (AlgebraicGeometry.Spec.map
        (CommRingCat.ofHom f.ulift.{max v w, max v w})) := by
  classical
  let eC : ULift.{max v w} C ≃+* C := ULift.ringEquiv
  let eD : ULift.{max v w} D ≃+* D := ULift.ringEquiv
  let hC := PrimeSpectrum.homeomorphOfRingEquiv eC
  let hD := PrimeSpectrum.homeomorphOfRingEquiv eD
  let fU : ULift.{max v w} C →+* ULift.{max v w} D :=
    f.ulift.{max v w, max v w}
  have hcomap (q : PrimeSpectrum (ULift.{max v w} D)) :
      PrimeSpectrum.comap fU q = hC.symm (PrimeSpectrum.comap f (hD q)) := by
    apply PrimeSpectrum.ext
    ext x
    rfl
  have hopenU : Topology.IsOpenEmbedding (PrimeSpectrum.comap fU) := by
    apply Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
    · rw [show PrimeSpectrum.comap fU =
        (fun q => hC.symm (PrimeSpectrum.comap f (hD q))) from funext hcomap]
      exact hC.symm.continuous.comp (hopen.continuous.comp hD.continuous)
    · exact fun q₁ q₂ h => hD.injective (hopen.injective
        (by simpa only [hcomap, hC.apply_symm_apply] using congrArg hC h))
    · rw [show PrimeSpectrum.comap fU =
        (fun q => hC.symm (PrimeSpectrum.comap f (hD q))) from funext hcomap]
      exact hC.symm.isOpenMap.comp (hopen.isOpenMap.comp hD.isOpenMap)
  let _ : Algebra (ULift.{max v w} C) (ULift.{max v w} D) := fU.toAlgebra
  let schemeMap : AlgebraicGeometry.Scheme.Spec.obj
        (op (CommRingCat.of (ULift.{max v w} D))) ⟶
      AlgebraicGeometry.Scheme.Spec.obj
        (op (CommRingCat.of (ULift.{max v w} C))) :=
    AlgebraicGeometry.Spec.map (CommRingCat.ofHom fU)
  refine AlgebraicGeometry.IsOpenImmersion.of_forall_source_exists schemeMap
    (fun _ _ hxy => hopenU.injective hxy) fun q => ?_
  let q₀ := hD q
  let p₀ := PrimeSpectrum.comap f q₀
  obtain ⟨_, ⟨_, ⟨g, rfl⟩, rfl⟩, hp, hg⟩ :=
    PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open
      (show p₀ ∈ Set.range (PrimeSpectrum.comap f) from ⟨q₀, rfl⟩)
      hopen.isOpen_range
  have hfg : f g ∉ q₀.asIdeal := by
    simpa [p₀, PrimeSpectrum.comap_asIdeal] using hp
  let Cg := Localization.Away g
  let Dg := Localization.Away (f g)
  let iC : ULift.{max v w} C →+* ULift.{max v w} Cg :=
    (algebraMap C Cg).ulift.{max v w, max v w}
  let iD : ULift.{max v w} D →+* ULift.{max v w} Dg :=
    (algebraMap D Dg).ulift.{max v w, max v w}
  let fAway : ULift.{max v w} Cg →+* ULift.{max v w} Dg :=
    (Localization.awayMap f g).ulift.{max v w, max v w}
  have awayMap_comp_algebraMap (x : C) :
      Localization.awayMap f g (algebraMap C Cg x) = algebraMap D Dg (f x) := by
    rw [Localization.awayMap, IsLocalization.Away.map, IsLocalization.map_eq]
  let _ : Algebra (ULift.{max v w} C) (ULift.{max v w} Cg) := iC.toAlgebra
  let _ : IsLocalization.Away (ULift.up g) (ULift.{max v w} Cg) := by
    refine IsLocalization.Away.mk (ULift.up g) ?_ ?_ ?_
    · show IsUnit (ULift.up (algebraMap C Cg g))
      exact IsUnit.map (ULift.ringEquiv : ULift.{max v w} Cg ≃+* Cg).symm.toMonoidHom
        (IsLocalization.map_units Cg
          ⟨g, (Submonoid.mem_powers_iff g g).mpr ⟨1, by simp⟩⟩)
    · intro z
      obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj g z.down
      refine ⟨n, ⟨a⟩, ?_⟩
      apply ULift.ext
      simpa [iC, RingHom.algebraMap_toAlgebra] using ha
    · intro a b hab
      have hab' : algebraMap C Cg a.down = algebraMap C Cg b.down :=
        congrArg ULift.down hab
      obtain ⟨n, hn⟩ := IsLocalization.Away.exists_of_eq g hab'
      refine ⟨n, ?_⟩
      apply ULift.ext
      simpa using hn
  let _ : Algebra (ULift.{max v w} D) (ULift.{max v w} Dg) := iD.toAlgebra
  let _ : IsLocalization.Away (ULift.up (f g)) (ULift.{max v w} Dg) := by
    refine IsLocalization.Away.mk (ULift.up (f g)) ?_ ?_ ?_
    · show IsUnit (ULift.up (algebraMap D Dg (f g)))
      exact IsUnit.map (ULift.ringEquiv : ULift.{max v w} Dg ≃+* Dg).symm.toMonoidHom
        (IsLocalization.map_units Dg
          ⟨f g, (Submonoid.mem_powers_iff (f g) (f g)).mpr ⟨1, by simp⟩⟩)
    · intro z
      obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj (f g) z.down
      refine ⟨n, ⟨a⟩, ?_⟩
      apply ULift.ext
      simpa [iD, RingHom.algebraMap_toAlgebra] using ha
    · intro a b hab
      have hab' : algebraMap D Dg a.down = algebraMap D Dg b.down :=
        congrArg ULift.down hab
      obtain ⟨n, hn⟩ := IsLocalization.Away.exists_of_eq (f g) hab'
      refine ⟨n, ?_⟩
      apply ULift.ext
      simpa using hn
  have hCopen : AlgebraicGeometry.IsOpenImmersion
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom iC)) :=
    AlgebraicGeometry.IsOpenImmersion.of_isLocalization (ULift.up g)
  have hDopen : AlgebraicGeometry.IsOpenImmersion
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom iD)) :=
    AlgebraicGeometry.IsOpenImmersion.of_isLocalization (ULift.up (f g))
  have hfAway : Function.Bijective fAway := by
    refine ⟨fun x y hxy => ULift.ext ((haway g hg).injective (congrArg ULift.down hxy)),
      fun z => ?_⟩
    obtain ⟨x, hx⟩ := (haway g hg).surjective z.down
    exact ⟨⟨x⟩, ULift.ext hx⟩
  let _ : IsIso (CommRingCat.ofHom fAway) :=
    (RingEquiv.toCommRingCatIso (RingEquiv.ofBijective fAway hfAway)).isIso_hom
  have hsq :
      AlgebraicGeometry.Spec.map (CommRingCat.ofHom iD) ≫
          AlgebraicGeometry.Spec.map (CommRingCat.ofHom fU) =
        AlgebraicGeometry.Spec.map (CommRingCat.ofHom fAway) ≫
          AlgebraicGeometry.Spec.map (CommRingCat.ofHom iC) := by
    rw [← AlgebraicGeometry.Spec.map_comp, ← AlgebraicGeometry.Spec.map_comp]
    congr 1
    ext x
    show algebraMap D Dg (f x.down) =
      Localization.awayMap f g (algebraMap C Cg x.down)
    exact (awayMap_comp_algebraMap x.down).symm
  have hcomp : AlgebraicGeometry.IsOpenImmersion
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom iD) ≫ schemeMap) := by
    rw [hsq]
    infer_instance
  have hq : q ∈ (AlgebraicGeometry.Spec.map (CommRingCat.ofHom iD)).opensRange := by
    show (q : PrimeSpectrum (ULift.{max v w} D)) ∈ Set.range
      (PrimeSpectrum.comap (algebraMap (ULift.{max v w} D) (ULift.{max v w} Dg)))
    rw [PrimeSpectrum.localization_away_comap_range
      (R := ULift.{max v w} D) (S := ULift.{max v w} Dg)
      (r := ULift.up (f g))]
    show ULift.up (f g) ∉ (q : PrimeSpectrum (ULift.{max v w} D)).asIdeal
    have hnot : f g ∉
        (PrimeSpectrum.comap (eD.symm : D →+* ULift.{max v w} D) q).asIdeal := by
      simpa [q₀, hD, PrimeSpectrum.homeomorphOfRingEquiv] using hfg
    exact hnot
  exact ⟨_, AlgebraicGeometry.Spec.map (CommRingCat.ofHom iD), hDopen, hq, hcomp⟩

end SpecMapProof

/-- Contract the first tensor factor against an `A`-linear functional. -/
def tensorContract (A : Type u) (C : Type v) [CommRing A] [CommRing C]
    [Algebra A C] (f : Module.Dual A C) : C ⊗[A] C →ₗ[A] C :=
  TensorProduct.lift ((LinearMap.lsmul A C).comp f)

/-- The defining formula for the pairing between the relative dualizing module and the
diagonal annihilator. -/
def IsNoetherPairing {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [Algebra A B] (F : FiniteOpenFactorization.{u, v, w} A B)
    (p : dualizingModule F →ₗ[B]
      (↑(diagonalAnnihilator A B) →ₗ[B] B)) : Prop :=
  ∀ (f : Module.Dual A F.middle) (x y : B)
    (j' : ↑(diagonalAnnihilator A F.middle))
    (j : ↑(diagonalAnnihilator A B)),
    j.1 = diagonalAnnihilatorBaseChange A F.middle B
      (y ⊗ₜ[F.middle] j') →
      p (dualizingModule.tmul F f x) j =
        x * y * algebraMap F.middle B (tensorContract A F.middle f j'.1)

/-- Contracting against a scalar multiple of an element of the diagonal annihilator multiplies
the contraction by that scalar. -/
lemma tensorContract_smul_diagonal (A : Type u) (C : Type v)
    [CommRing A] [CommRing C] [Algebra A C] (f : Module.Dual A C) (c : C)
    (j : ↑(diagonalAnnihilator A C)) :
    tensorContract A C f (c • j.1) = c * tensorContract A C f j.1 := by
  let d : C ⊗[A] C := c ⊗ₜ[A] (1 : C) - (1 : C) ⊗ₜ[A] c
  have hd : d ∈ RingHom.ker (Algebra.TensorProduct.lmul' A).toRingHom := by
    show (Algebra.TensorProduct.lmul' A) d = 0
    simp [d, Algebra.TensorProduct.lmul'_apply_tmul]
  have hjann : j.1 ∈
      (RingHom.ker (Algebra.TensorProduct.lmul' A).toRingHom).annihilator := j.2
  have hkill := (Submodule.mem_annihilator.mp hjann) d hd
  have hmul : j.1 * (c ⊗ₜ[A] (1 : C)) =
      j.1 * ((1 : C) ⊗ₜ[A] c) :=
    (sub_eq_zero.mp (by simpa [d, mul_sub] using hkill))
  have heq : (c ⊗ₜ[A] (1 : C)) * j.1 =
      ((1 : C) ⊗ₜ[A] c) * j.1 := by
    simpa [mul_comm] using hmul
  have hright (z : C ⊗[A] C) :
      tensorContract A C f (((1 : C) ⊗ₜ[A] c) * z) =
        c * tensorContract A C f z := by
    induction z using TensorProduct.induction_on with
    | zero => simp [tensorContract]
    | add x y hx hy =>
        calc
          tensorContract A C f (((1 : C) ⊗ₜ[A] c) * (x + y)) =
              tensorContract A C f (((1 : C) ⊗ₜ[A] c) * x) +
                tensorContract A C f (((1 : C) ⊗ₜ[A] c) * y) := by
            rw [mul_add, map_add]
          _ = c * tensorContract A C f x + c * tensorContract A C f y := by rw [hx, hy]
          _ = c * tensorContract A C f (x + y) := by rw [map_add, mul_add]
    | tmul x y =>
        simp [tensorContract, TensorProduct.lift.tmul]
  have hcontract := congrArg (tensorContract A C f) heq
  simpa [Algebra.smul_def, hright] using hcontract

section PairingHelpers

attribute [local instance] algebraDualModule

/-- Contracting against a scalar multiple of a functional multiplies the contraction by that
scalar, when the tensor lies in the diagonal annihilator. -/
lemma tensorContract_smul_functional (A : Type u) (C : Type v)
    [CommRing A] [CommRing C] [Algebra A C] (f : Module.Dual A C) (c : C)
    (j : ↑(diagonalAnnihilator A C)) :
    tensorContract A C (c • f) j.1 = c * tensorContract A C f j.1 := by
  let d : C ⊗[A] C := c ⊗ₜ[A] (1 : C) - (1 : C) ⊗ₜ[A] c
  have hd : d ∈ RingHom.ker (Algebra.TensorProduct.lmul' A).toRingHom := by
    show (Algebra.TensorProduct.lmul' A) d = 0
    simp [d, Algebra.TensorProduct.lmul'_apply_tmul]
  have hjann : j.1 ∈
      (RingHom.ker (Algebra.TensorProduct.lmul' A).toRingHom).annihilator := j.2
  have hkill := (Submodule.mem_annihilator.mp hjann) d hd
  have hmul : j.1 * (c ⊗ₜ[A] (1 : C)) =
      j.1 * ((1 : C) ⊗ₜ[A] c) :=
    (sub_eq_zero.mp (by simpa [d, mul_sub] using hkill))
  have heq : (c ⊗ₜ[A] (1 : C)) * j.1 =
      ((1 : C) ⊗ₜ[A] c) * j.1 := by simpa [mul_comm] using hmul
  have hleft (z : C ⊗[A] C) :
      tensorContract A C (c • f) z =
        tensorContract A C f ((c ⊗ₜ[A] (1 : C)) * z) := by
    induction z using TensorProduct.induction_on with
    | zero => simp [tensorContract]
    | tmul x y =>
        simp [tensorContract, TensorProduct.lift.tmul,
          algebraDualModule_smul_apply]
    | add x y hx hy =>
        rw [map_add, hx, hy, mul_add, map_add]
  have hright :
      tensorContract A C f (((1 : C) ⊗ₜ[A] c) * j.1) =
        c * tensorContract A C f j.1 := by
    induction j.1 using TensorProduct.induction_on with
    | zero => simp [tensorContract]
    | tmul x y =>
        simp [tensorContract, TensorProduct.lift.tmul]
    | add x y hx hy =>
        calc
          tensorContract A C f (((1 : C) ⊗ₜ[A] c) * (x + y)) =
              tensorContract A C f (((1 : C) ⊗ₜ[A] c) * x) +
                tensorContract A C f (((1 : C) ⊗ₜ[A] c) * y) := by
            rw [mul_add, map_add]
          _ = c * tensorContract A C f x + c * tensorContract A C f y := by
            rw [hx, hy]
          _ = c * tensorContract A C f (x + y) := by rw [map_add, mul_add]
  calc
    tensorContract A C (c • f) j.1 =
        tensorContract A C f ((c ⊗ₜ[A] (1 : C)) * j.1) := hleft j.1
    _ = tensorContract A C f (((1 : C) ⊗ₜ[A] c) * j.1) :=
      congrArg (tensorContract A C f) heq
    _ = c * tensorContract A C f j.1 := hright

/-- Contraction is additive in the functional. -/
lemma tensorContract_add (A : Type u) (C : Type v)
    [CommRing A] [CommRing C] [Algebra A C] (f g : Module.Dual A C)
    (z : C ⊗[A] C) :
    tensorContract A C (f + g) z =
      tensorContract A C f z + tensorContract A C g z := by
  induction z using TensorProduct.induction_on with
  | zero => simp [tensorContract]
  | tmul x y => simp [tensorContract, TensorProduct.lift.tmul]
  | add x y hx hy =>
      calc
        tensorContract A C (f + g) (x + y) =
            tensorContract A C (f + g) x + tensorContract A C (f + g) y := map_add _ _ _
        _ = tensorContract A C f x + tensorContract A C g x +
              (tensorContract A C f y + tensorContract A C g y) := by rw [hx, hy]
        _ = tensorContract A C f (x + y) + tensorContract A C g (x + y) := by
          rw [map_add, map_add]
          ac_rfl

/-- Contraction against a fixed functional, as a `C`-linear map on the diagonal annihilator. -/
def tensorContractOnDiagonal (A : Type u) (C : Type v)
    [CommRing A] [CommRing C] [Algebra A C] (f : Module.Dual A C) :
    (↑(diagonalAnnihilator A C) : Type v) →ₗ[C] C where
  toFun j := tensorContract A C f j.1
  map_add' := by intro x y; simp [tensorContract]
  map_smul' := by
    intro c j
    simpa [Algebra.smul_def] using tensorContract_smul_diagonal A C f c j

/-- Contraction against a functional on the finite model, extended to the base change of the
diagonal annihilator along `C → B`. -/
def finiteModelExtendedPairing {A : Type u} {C : Type v} {B : Type w}
    [CommRing A] [CommRing C] [CommRing B] [Algebra A C] [Algebra C B]
    [Algebra A B] [IsScalarTower A C B] (f : Module.Dual A C) :
    B ⊗[C] (↑(diagonalAnnihilator A C)) →ₗ[B] B := by
  let l : (↑(diagonalAnnihilator A C) : Type v) →ₗ[C] B :=
    (Algebra.ofId C B).toLinearMap.comp (tensorContractOnDiagonal A C f)
  let g : B →ₗ[B]
      ((↑(diagonalAnnihilator A C) : Type v) →ₗ[C] B) := {
    toFun := fun b => {
      toFun := fun j => b * l j
      map_add' := by intro x y; simp [mul_add]
      map_smul' := by
        intro c j
        simp [l, Algebra.smul_def, mul_left_comm]
    }
    map_add' := by
      intro b₁ b₂
      ext j
      simp [l, add_mul]
    map_smul' := by
      intro r b
      ext j
      simp [l, mul_assoc]
  }
  exact TensorProduct.AlgebraTensorModule.lift g

/-- The extended pairing on a pure tensor is the contraction scaled by the coefficient. -/
lemma finiteModelExtendedPairing_tmul {A : Type u} {C : Type v} {B : Type w}
    [CommRing A] [CommRing C] [CommRing B] [Algebra A C] [Algebra C B]
    [Algebra A B] [IsScalarTower A C B] (f : Module.Dual A C) (b : B)
    (j : ↑(diagonalAnnihilator A C)) :
    finiteModelExtendedPairing f (b ⊗ₜ[C] j) =
      b * algebraMap C B (tensorContract A C f j.1) := by
  show b * algebraMap C B (tensorContract A C f j.1) = _
  rfl

/-- The extended pairing, as a `C`-linear map in the functional. -/
def dualToFiniteModelPairing {A : Type u} {C : Type v} {B : Type w}
    [CommRing A] [CommRing C] [CommRing B] [Algebra A C] [Algebra C B]
    [Algebra A B] [IsScalarTower A C B] :
    Module.Dual A C →ₗ[C]
      ((B ⊗[C] (↑(diagonalAnnihilator A C))) →ₗ[B] B) where
  toFun := finiteModelExtendedPairing
  map_add' := by
    intro f g
    apply LinearMap.ext
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp [finiteModelExtendedPairing]
    | tmul b j =>
        change b * algebraMap C B (tensorContract A C (f + g) j.1) =
          b * algebraMap C B (tensorContract A C f j.1) +
            b * algebraMap C B (tensorContract A C g j.1)
        rw [tensorContract_add]
        simp [mul_add]
    | add x y hx hy => rw [map_add, hx, hy, map_add]
  map_smul' := by
    intro c f
    apply LinearMap.ext
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp [finiteModelExtendedPairing]
    | tmul b j =>
        simp only [finiteModelExtendedPairing_tmul, LinearMap.smul_apply]
        rw [tensorContract_smul_functional]
        simp [Algebra.smul_def, mul_left_comm]
    | add x y hx hy => rw [map_add, hx, hy, map_add]

/-- Extension of a `C`-linear pairing in the functional to a `B`-linear pairing on the base
change of the dual. -/
def extendDualPairing {A : Type u} {C : Type v} {B : Type w}
    [CommRing A] [CommRing C] [CommRing B] [Algebra A C] [Algebra C B]
    [Algebra A B] [IsScalarTower A C B]
    (q : Module.Dual A C →ₗ[C]
      ((B ⊗[C] (↑(diagonalAnnihilator A C))) →ₗ[B] B)) :
    B ⊗[C] Module.Dual A C →ₗ[B]
      ((B ⊗[C] (↑(diagonalAnnihilator A C))) →ₗ[B] B) := by
  let E := (B ⊗[C] (↑(diagonalAnnihilator A C))) →ₗ[B] B
  let g : B →ₗ[B] (Module.Dual A C →ₗ[C] E) := {
    toFun := fun b => {
      toFun := fun f => b • q f
      map_add' := by
        intro f₁ f₂
        change b • q (f₁ + f₂) = b • q f₁ + b • q f₂
        rw [q.map_add, smul_add]
      map_smul' := by
        intro c f
        change b • q (c • f) = c • (b • q f)
        rw [q.map_smul, smul_comm]
    }
    map_add' := by
      intro b₁ b₂
      change (b₁ + b₂) • q = b₁ • q + b₂ • q
      rw [add_smul]
    map_smul' := by
      intro r b
      change (r * b) • q = r • (b • q)
      rw [mul_smul]
  }
  exact TensorProduct.AlgebraTensorModule.lift g

/-- The extended pairing on a pure tensor rescales the given pairing. -/
lemma extendDualPairing_tmul {A : Type u} {C : Type v} {B : Type w}
    [CommRing A] [CommRing C] [CommRing B] [Algebra A C] [Algebra C B]
    [Algebra A B] [IsScalarTower A C B]
    (q : Module.Dual A C →ₗ[C]
      ((B ⊗[C] (↑(diagonalAnnihilator A C))) →ₗ[B] B))
    (b : B) (f : Module.Dual A C) :
    extendDualPairing q (b ⊗ₜ[C] f) = b • q f := by
  simp [extendDualPairing]

/-- The relative dualizing module of a finite-open factorization, with its tensor factors
commuted. -/
noncomputable def dualizingModuleCommEquiv {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] [Algebra A B]
    (F : FiniteOpenFactorization.{u, v, w} A B) :
    dualizingModule F ≃ₗ[B]
      B ⊗[F.middle] Module.Dual A F.middle := by
  let _ : Module F.middle (Module.Dual A F.middle) :=
    algebraDualModule A F.middle
  let _ : Module B (Module.Dual A F.middle ⊗[F.middle] B) := by
    let : Module B (B ⊗[F.middle] Module.Dual A F.middle) :=
      TensorProduct.leftModule
    exact (TensorProduct.comm F.middle (Module.Dual A F.middle) B).toAddEquiv.module B
  let _ : Module B (B ⊗[F.middle] Module.Dual A F.middle) :=
    TensorProduct.leftModule
  exact (TensorProduct.comm F.middle (Module.Dual A F.middle) B).toAddEquiv.linearEquiv B

end PairingHelpers

/-- **Stacks Project, Tag 0BVP.** The canonical `B`-bilinear pairing between the relative
dualizing module and the annihilator of the kernel of multiplication, together with its defining
contraction formula on a finite-open model. -/
@[stacks 0BVP]
noncomputable def noetherPairingWithFormula {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] [Algebra A B]
    (F : FiniteOpenFactorization.{u, v, w} A B) :
    {p : dualizingModule F →ₗ[B]
      (↑(diagonalAnnihilator A B) →ₗ[B] B) // IsNoetherPairing F p} := by
  classical
  let C := F.middle
  let _ : Module C (Module.Dual A C) := algebraDualModule A C
  let J' := diagonalAnnihilator A C
  let J := diagonalAnnihilator A B
  let _ : Algebra.FiniteType A C := inferInstance
  have hopen := specMap_ulift_isOpenImmersion (algebraMap C B)
    F.isOpenEmbedding_comap F.awayMap_bijective
  let φ := diagonalAnnihilatorBaseChange A C B
  have hRange := range_diagonalAnnihilatorBaseChange A C B hopen
  have hInj := diagonalAnnihilatorBaseChange_injective A C B hopen
  let φJ : B ⊗[C] (↑J') →ₗ[B] (↑J) := φ.codRestrict (J.restrictScalars B) (by
    intro z
    change φ z ∈ J.restrictScalars B
    rw [← hRange]
    exact ⟨z, rfl⟩)
  have hBij : Function.Bijective φJ := by
    refine ⟨fun x y hxy => hInj (congrArg Subtype.val hxy), fun j => ?_⟩
    obtain ⟨z, hz⟩ : j.1 ∈ LinearMap.range φ := by
      rw [hRange]
      exact j.2
    exact ⟨z, Subtype.ext hz⟩
  let e : (B ⊗[C] (↑J')) ≃ₗ[B] (↑J) := LinearEquiv.ofBijective φJ hBij
  let qF := dualToFiniteModelPairing (A := A) (C := C) (B := B)
  let qAll := (extendDualPairing qF).comp
    (dualizingModuleCommEquiv F).toLinearMap
  let p : dualizingModule F →ₗ[B] (↑J →ₗ[B] B) := {
    toFun := fun ω => {
      toFun := fun j => qAll ω (e.symm j)
      map_add' := by intro x y; rw [e.symm.map_add, map_add]
      map_smul' := by intro b x; rw [e.symm.map_smul, LinearMap.map_smul]; rfl
    }
    map_add' := by intro x y; ext j; simp
    map_smul' := by intro b x; ext j; simp
  }
  refine ⟨p, ?_⟩
  intro f x y j' j hj
  have he : e.symm j = y ⊗ₜ[C] j' :=
    e.injective ((e.apply_symm_apply j).trans (Subtype.ext hj))
  change qAll (dualizingModule.tmul F f x) (e.symm j) = _
  rw [he]
  change extendDualPairing qF
      ((dualizingModuleCommEquiv F)
        (dualizingModule.tmul F f x))
      (y ⊗ₜ[C] j') = _
  change extendDualPairing qF (x ⊗ₜ[C] f) (y ⊗ₜ[C] j') = _
  rw [extendDualPairing_tmul]
  change x • finiteModelExtendedPairing f (y ⊗ₜ[C] j') = _
  rw [finiteModelExtendedPairing_tmul]
  simp only [Algebra.smul_def, Algebra.algebraMap_self_apply]
  ac_rfl

/-- The linear map underlying the canonical pairing. -/
noncomputable def noetherPairing {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] [Algebra A B]
    (F : FiniteOpenFactorization.{u, v, w} A B) :
    dualizingModule F →ₗ[B]
      (↑(diagonalAnnihilator A B) →ₗ[B] B) :=
  (noetherPairingWithFormula F).1

/-- The canonical pairing has the contraction formula on tensors from the finite model. -/
lemma noetherPairing_apply_of_eq_baseChange {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] [Algebra A B]
    (F : FiniteOpenFactorization.{u, v, w} A B)
    (f : Module.Dual A F.middle) (x y : B)
    (j' : ↑(diagonalAnnihilator A F.middle))
    (j : ↑(diagonalAnnihilator A B))
    (hj : j.1 = diagonalAnnihilatorBaseChange A F.middle B
      (y ⊗ₜ[F.middle] j')) :
    noetherPairing F (dualizingModule.tmul F f x) j =
      x * y * algebraMap F.middle B (tensorContract A F.middle f j'.1) :=
  (noetherPairingWithFormula F).2 f x y j' j hj

end Stacks.Discriminant
