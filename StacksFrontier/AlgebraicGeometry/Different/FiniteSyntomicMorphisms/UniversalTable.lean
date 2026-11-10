module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Pullbacks
public import StacksFrontier.AlgebraicGeometry.Different.FiniteSyntomicMorphisms.AlgebraAxioms
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.Basic
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.FiniteFreeAlgebra.OfBasis

/-!
# Multiplication tables of the universal finite free family

The universal finite free family `pi_d : Y_d ⟶ X_d` of rank `d` (Tag 0FKZ) is affine, and the
global sections of `Y_d` are free of rank `d` over those of `X_d` on a basis whose first vector
is the unit. The multiplication table of that basis is the identity point of `X_d` under the
representability of Tag 05YM, and the table of the basis obtained by base change along a
morphism `T ⟶ X_d` of affine schemes is the point `T ⟶ X_d` itself.

## Main definitions

* `AlgebraicGeometry.universalTotalGammaBasis` is the basis of `Γ(Y_d)` over `Γ(X_d)`.
* `AlgebraicGeometry.affinePullbackGammaBasis` transports a basis of an affine family to a base
  change of that family.

## Main results

* `AlgebraicGeometry.FiniteFreeAlgebra.ofBasis_eq_of_algEquiv` and
  `AlgebraicGeometry.FiniteFreeAlgebra.ofBasis_map`: a multiplication table is unchanged by an
  algebra equivalence matching the bases, and is compatible with base change.
* `AlgebraicGeometry.universalTotalGammaBasis_structure`: the table of the basis of `Γ(Y_d)` is
  the identity point of `X_d`.
* `AlgebraicGeometry.affinePullbackGammaBasis_structure_of_map`: the table of a base-changed
  basis is the point along which the base change is taken.

## Implementation notes

Global sections of a pullback of affine schemes are a tensor product, which is
`AlgebraicGeometry.affinePullbackΓTensorEquiv`; a basis of one factor over the base gives a
basis of the tensor product over the other factor, and that is how a basis is transported along
a base change.

The free carrier `B_d` of the universal family carries its algebra structure as a parameter
rather than as instances, so a basis of it has to be produced by hand from the coordinate
isomorphism; `AlgebraicGeometry.universalCarrierGammaBasis` is that basis, over the global
sections of `X_d` rather than over the universal coefficient ring itself.

## References

* [Stacks Project, Tag 0FKZ](https://stacks.math.columbia.edu/tag/0FKZ)
* [Stacks Project, Tag 05YM](https://stacks.math.columbia.edu/tag/05YM)
* [Stacks Project, Tag 05YQ](https://stacks.math.columbia.edu/tag/05YQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
  AlgebraicGeometry.FiniteFreeAlgebra

universe u v w

namespace AlgebraicGeometry

open scoped BigOperators
open scoped TensorProduct

/-- Two multiplication tables with the same coefficients are equal. -/
theorem FiniteFreeAlgebra.ext_coeff {R : Type*} [CommRing R] {d : ℕ}
    [NeZero d] {m n : FiniteFreeAlgebra R d}
    (h : ∀ i j k, m.coeff i j k = n.coeff i j k) : m = n := by
  cases m with
  | mk mc ma mm mu =>
    cases n with
    | mk nc na nm nu =>
      have hc : mc = nc := funext fun i => funext fun j => funext fun k => h i j k
      cases hc
      rfl

/-- An algebra equivalence carrying one basis to another carries one multiplication table to the
other. -/
theorem FiniteFreeAlgebra.ofBasis_eq_of_algEquiv {R B C : Type w} [CommRing R]
    [CommRing B] [CommRing C] [Algebra R B] [Algebra R C] {d : ℕ} [NeZero d]
    (e : B ≃ₐ[R] C) (b : Module.Basis (Fin d) R B) (c : Module.Basis (Fin d) R C)
    (hb : b 0 = 1) (hc : c 0 = 1) (hbc : ∀ i, e (b i) = c i) :
    ofBasis b hb = ofBasis c hc := by
  apply ext_coeff
  intro i j k
  change (b.repr (b i * b j)) k = (c.repr (c i * c j)) k
  have hre : b.repr = c.repr.comp e.toLinearMap := by
    apply b.ext
    intro l
    simp [hbc l]
  have hm : c i * c j = e (b i * b j) := by
    rw [← hbc i, ← hbc j, ← map_mul]
  rw [hm]
  exact congrArg (fun z : Fin d →₀ R => z k)
    (congrArg (fun f : B →ₗ[R] (Fin d →₀ R) => f (b i * b j)) hre)

/-- Two algebras that are free of rank `d` on bases whose first vectors are their units, with the
same multiplication table, are isomorphic by the map carrying one basis to the other. -/
noncomputable def FiniteFreeAlgebra.algEquivOfBasisEq {R B C : Type w} [CommRing R]
    [CommRing B] [CommRing C] [Algebra R B] [Algebra R C] {d : ℕ} [NeZero d]
    (b : Module.Basis (Fin d) R B) (c : Module.Basis (Fin d) R C)
    (hb : b 0 = 1) (hc : c 0 = 1) (h : ofBasis b hb = ofBasis c hc) : B ≃ₐ[R] C := by
  refine (algEquivCarrierOfBasis b hb).trans ?_
  rw [h]
  exact (algEquivCarrierOfBasis c hc).symm

/-- The multiplication table of a basis is compatible with base change: a ring map of base rings
and a compatible ring map of algebras carrying one basis to another carries the extension of
scalars of the first table to the second. -/
theorem FiniteFreeAlgebra.ofBasis_map {R A : Type w} {S C : Type v} [CommRing R] [CommRing S]
    [CommRing A] [CommRing C] [Algebra R A] [Algebra S C] {d : ℕ} [NeZero d]
    (f : R →+* S) (q : A →+* C) (hq : ∀ r,
      q (algebraMap R A r) = algebraMap S C (f r))
    (b : Module.Basis (Fin d) R A) (hb : b 0 = 1)
    (c : Module.Basis (Fin d) S C) (hc : c 0 = 1)
    (hbc : ∀ i, q (b i) = c i) :
    FiniteFreeAlgebra.map f (ofBasis b hb) =
      ofBasis c hc := by
  apply ext_coeff
  intro i j k
  change f ((b.repr (b i * b j)) k) = (c.repr (c i * c j)) k
  have hsum : q (b i * b j) =
      ∑ l, f ((b.repr (b i * b j)) l) • c l := by
    calc
      q (b i * b j) = q (∑ l, (b.repr (b i * b j)) l • b l) := by
        rw [b.sum_repr]
      _ = ∑ l, q ((b.repr (b i * b j)) l • b l) := map_sum q _ _
      _ = ∑ l, f ((b.repr (b i * b j)) l) • c l := by
        apply Finset.sum_congr rfl
        intro l hl
        rw [Algebra.smul_def, Algebra.smul_def, map_mul, hq, hbc]
  have hcoord : c.repr (q (b i * b j)) k = f ((b.repr (b i * b j)) k) := by
    rw [hsum]
    simp [Finsupp.single_apply, smul_eq_mul]
  rw [map_mul, hbc i, hbc j] at hcoord
  exact hcoord.symm

/-- The universal free carrier `B_d` is free of rank `d` over the universal coefficient ring `A_d`,
via its coordinates. -/
noncomputable def universalCarrierLinearEquiv (d : ℕ) [NeZero d] :
    letI := (universalAlgebraStructure d).ring
    letI := (universalAlgebraStructure d).algebra
    UniversalFiniteFreeModule d ≃ₗ[
      universalRing d] (Fin d → universalRing d) := by
  let s := universalAlgebraStructure d
  letI := s.ring
  letI := s.algebra
  refine
    { toFun := fun x => x.coeff
      invFun := fun x => ⟨x⟩
      left_inv := fun x => by cases x; rfl
      right_inv := fun x => rfl
      map_add' := fun x y => by
        funext i
        exact s.add_coeff x y i
      map_smul' := ?_ }
  intro a x
  funext k
  change (a • x).coeff k = a * x.coeff k
  rw [Algebra.smul_def, s.mul_eq]
  simp [universalMultiplication, s.algebraMap_coeff, universalStructureConstant_zero_left]

/-- Two elements of the universal free carrier with the same coordinates are equal. -/
theorem universalCarrier_ext {d : ℕ} [NeZero d] {x y :
    UniversalFiniteFreeModule d}
    (h : ∀ j, x.coeff j = y.coeff j) : x = y := by
  cases x
  cases y
  congr
  exact funext h

/-- The coordinate isomorphism of `B_d`, transported to the lift of `A_d` into the universe of
the test schemes. -/
noncomputable def universalCarrierULiftLinearEquiv (d : ℕ) [NeZero d] :
    let s := universalAlgebraStructure d
    letI := s.ring
    letI := s.algebra
    letI : Algebra (ULift.{u} (universalRing d))
        (UniversalFiniteFreeModule d) :=
      Algebra.compHom _ ULift.ringEquiv.toRingHom
    UniversalFiniteFreeModule d ≃ₗ[
      ULift.{u} (universalRing d)]
      (Fin d → ULift.{u} (universalRing d)) := by
  let s := universalAlgebraStructure d
  letI := s.ring
  letI := s.algebra
  letI : Algebra (ULift.{u} (universalRing d))
      (UniversalFiniteFreeModule d) :=
    Algebra.compHom _ ULift.ringEquiv.toRingHom
  let ρ := ULift.ringEquiv (R := universalRing d)
  let e := universalCarrierLinearEquiv d
  refine
    { toFun := fun x i => ρ.symm (e x i)
      invFun := fun y => e.symm (fun i => ρ (y i))
      map_add' := by
        intro x y
        funext i
        simp [e, ρ]
      map_smul' := by
        intro a x
        have hs : a • x = (ρ a) • x := rfl
        rw [hs, e.map_smul]
        funext i
        simp [e, ρ, Pi.smul_apply]
      left_inv := by
        intro x
        apply universalCarrier_ext
        intro i
        simp [e, ρ]
      right_inv := by
        intro y
        funext i
        simp [e, ρ] }

/-- The coordinate basis of `B_d` over the lifted universal coefficient ring. -/
noncomputable def universalCarrierULiftBasis (d : ℕ) [NeZero d] :
    let s := universalAlgebraStructure d
    letI := s.ring
    letI := s.algebra
    letI : Algebra (ULift.{u} (universalRing d))
        (UniversalFiniteFreeModule d) :=
      Algebra.compHom _ ULift.ringEquiv.toRingHom
    Module.Basis (Fin d) (ULift.{u} (universalRing d))
      (UniversalFiniteFreeModule d) := by
  let s := universalAlgebraStructure d
  letI := s.ring
  letI := s.algebra
  letI : Algebra (ULift.{u} (universalRing d))
      (UniversalFiniteFreeModule d) :=
    Algebra.compHom _ ULift.ringEquiv.toRingHom
  exact (Pi.basisFun (ULift.{u} (universalRing d)) (Fin d)).map
    (universalCarrierULiftLinearEquiv.{u} d).symm

/-- The coordinate basis of `B_d` is the family of distinguished basis vectors. -/
theorem universalCarrierULiftBasis_apply (d : ℕ) [NeZero d] (i : Fin d) :
    let s := universalAlgebraStructure d
    letI := s.ring
    letI := s.algebra
    letI : Algebra (ULift.{u} (universalRing d))
        (UniversalFiniteFreeModule d) :=
      Algebra.compHom _ ULift.ringEquiv.toRingHom
    universalCarrierULiftBasis.{u} d i =
      universalBasisVector d i := by
  let s := universalAlgebraStructure d
  let := s.ring
  let := s.algebra
  let : Algebra (ULift.{u} (universalRing d))
      (UniversalFiniteFreeModule d) :=
    Algebra.compHom _ ULift.ringEquiv.toRingHom
  change (universalCarrierULiftLinearEquiv.{u} d).symm
    (Pi.basisFun (ULift.{u} (universalRing d)) (Fin d) i) = _
  apply universalCarrier_ext
  intro j
  simp [universalCarrierULiftLinearEquiv, universalCarrierLinearEquiv,
    universalBasisVector,
    Pi.basisFun_apply, Pi.single_apply, eq_comm]

/-- The coordinate isomorphism of `B_d`, transported to the global sections of the base `X_d`. -/
noncomputable def universalCarrierGammaLinearEquiv (d : ℕ) [NeZero d] :
    let s := universalAlgebraStructure d
    letI := s.ring
    letI := s.algebra
    letI : Algebra (ULift.{u} (universalRing d))
      (UniversalFiniteFreeModule d) :=
      Algebra.compHom _ ULift.ringEquiv.toRingHom
    let ρ := (Scheme.ΓSpecIso
      (CommRingCat.of (ULift.{u} (universalRing d)))).commRingCatIsoToRingEquiv
    letI : Algebra Γ(scheme.{u} d, ⊤)
      (UniversalFiniteFreeModule d) :=
      Algebra.compHom _ ρ.toRingHom
    UniversalFiniteFreeModule d ≃ₗ[
      Γ(scheme.{u} d, ⊤)]
      (Fin d → Γ(scheme.{u} d, ⊤)) := by
  let s := universalAlgebraStructure d
  letI := s.ring
  letI := s.algebra
  letI : Algebra (ULift.{u} (universalRing d))
      (UniversalFiniteFreeModule d) :=
    Algebra.compHom _ ULift.ringEquiv.toRingHom
  let ρ := (Scheme.ΓSpecIso
    (CommRingCat.of (ULift.{u} (universalRing d)))).commRingCatIsoToRingEquiv
  letI : Algebra Γ(scheme.{u} d, ⊤)
      (UniversalFiniteFreeModule d) :=
    Algebra.compHom _ ρ.toRingHom
  let e := universalCarrierULiftLinearEquiv.{u} d
  refine
    { toFun := fun x i => ρ.symm (e x i)
      invFun := fun y => e.symm (fun i => ρ (y i))
      map_add' := by
        intro x y
        funext i
        simp [e, ρ]
      map_smul' := by
        intro a x
        have hs : a • x = (ρ a) • x := rfl
        rw [hs, e.map_smul]
        funext i
        simp [e, ρ, Pi.smul_apply]
      left_inv := by
        intro x
        apply universalCarrier_ext
        intro i
        simp [e, ρ]
      right_inv := by
        intro y
        funext i
        simp [e, ρ] }

/-- The coordinate basis of `B_d` over the global sections of the base `X_d`. -/
noncomputable def universalCarrierGammaBasis (d : ℕ) [NeZero d] :
    let s := universalAlgebraStructure d
    letI := s.ring
    letI := s.algebra
    letI : Algebra (ULift.{u} (universalRing d))
      (UniversalFiniteFreeModule d) :=
      Algebra.compHom _ ULift.ringEquiv.toRingHom
    let ρ := (Scheme.ΓSpecIso
      (CommRingCat.of (ULift.{u} (universalRing d)))).commRingCatIsoToRingEquiv
    letI : Algebra Γ(scheme.{u} d, ⊤)
      (UniversalFiniteFreeModule d) :=
      Algebra.compHom _ ρ.toRingHom
    Module.Basis (Fin d) Γ(scheme.{u} d, ⊤)
      (UniversalFiniteFreeModule d) := by
  let s := universalAlgebraStructure d
  letI := s.ring
  letI := s.algebra
  letI : Algebra (ULift.{u} (universalRing d))
      (UniversalFiniteFreeModule d) :=
    Algebra.compHom _ ULift.ringEquiv.toRingHom
  let ρ := (Scheme.ΓSpecIso
    (CommRingCat.of (ULift.{u} (universalRing d)))).commRingCatIsoToRingEquiv
  letI : Algebra Γ(scheme.{u} d, ⊤)
      (UniversalFiniteFreeModule d) :=
    Algebra.compHom _ ρ.toRingHom
  exact (Pi.basisFun Γ(scheme.{u} d, ⊤) (Fin d)).map
    (universalCarrierGammaLinearEquiv.{u} d).symm

/-- The coordinate basis over global sections is the family of distinguished basis vectors. -/
theorem universalCarrierGammaBasis_apply (d : ℕ) [NeZero d] (i : Fin d) :
    let s := universalAlgebraStructure d
    letI := s.ring
    letI := s.algebra
    letI : Algebra (ULift.{u} (universalRing d))
      (UniversalFiniteFreeModule d) :=
      Algebra.compHom _ ULift.ringEquiv.toRingHom
    let ρ := (Scheme.ΓSpecIso
      (CommRingCat.of (ULift.{u} (universalRing d)))).commRingCatIsoToRingEquiv
    letI : Algebra Γ(scheme.{u} d, ⊤)
      (UniversalFiniteFreeModule d) :=
      Algebra.compHom _ ρ.toRingHom
    universalCarrierGammaBasis.{u} d i =
      universalBasisVector d i := by
  let s := universalAlgebraStructure d
  let := s.ring
  let := s.algebra
  let : Algebra (ULift.{u} (universalRing d))
      (UniversalFiniteFreeModule d) :=
    Algebra.compHom _ ULift.ringEquiv.toRingHom
  let ρ := (Scheme.ΓSpecIso
    (CommRingCat.of (ULift.{u} (universalRing d)))).commRingCatIsoToRingEquiv
  let : Algebra Γ(scheme.{u} d, ⊤)
      (UniversalFiniteFreeModule d) :=
    Algebra.compHom _ ρ.toRingHom
  change (universalCarrierULiftLinearEquiv.{u} d).symm
    (fun j => ρ ((Pi.basisFun _ (Fin d) i) j)) = _
  rw [show (fun j => ρ ((Pi.basisFun _ (Fin d) i) j)) =
      Pi.basisFun (ULift.{u} (universalRing d)) (Fin d) i from by
        ext j
        simp [Pi.basisFun_apply, Pi.single_apply, eq_comm]]
  change universalCarrierULiftBasis.{u} d i = _
  exact universalCarrierULiftBasis_apply.{u} d i

/-- The map on the universal coefficient ring induced by a point of the base `X_d`. -/
noncomputable def pointRingHom (d : ℕ) [NeZero d] {T : Scheme.{u}}
    (f : T ⟶ scheme.{u} d) :
    universalRing d →+* Γ(T, ⊤) :=
  f.appTop.hom.comp ((Scheme.ΓSpecIso
    (.of (ULift.{u} (universalRing d)))).inv.hom.comp
      ULift.ringEquiv.symm.toRingHom)

/-- The multiplication table that the representability of Tag 05YM attaches to a point of `X_d`
is read off from the universal structure constants by that point's map on global sections. -/
theorem representation_equiv_coeff (d : ℕ) [NeZero d] {T : Scheme.{u}}
    (f : T ⟶ scheme.{u} d) (i j k : Fin d) :
    ((representation.{u} d).equiv T f).coeff i j k =
      pointRingHom d f (universalStructureConstant d i j k) := rfl

/-- A syntomic morphism of affine schemes is a syntomic algebra on global sections. -/
theorem algebraSyntomic_of_affineSyntomic {X Y : Scheme.{u}} [IsAffine X]
    [IsAffine Y] (f : X ⟶ Y)
    (hf : Syntomic f) :
    letI : Algebra Γ(Y, ⊤) Γ(X, ⊤) := f.appTop.hom.toAlgebra
    Algebra.Syntomic Γ(Y, ⊤) Γ(X, ⊤) := by
  have h12 : Syntomic f ↔
      ∀ (U : X.Opens) (_ : IsAffineOpen U) (V : Y.Opens)
        (_ : IsAffineOpen V) (hUV : U ≤ f ⁻¹ᵁ V),
        let : Algebra Γ(Y, V) Γ(X, U) := (f.appLE V U hUV).hom.toAlgebra
        Algebra.Syntomic Γ(Y, V) Γ(X, U) :=
    (syntomic_tfae f).out 1 2
  let e : (⊤ : X.Opens) ≤ f ⁻¹ᵁ (⊤ : Y.Opens) := by simp
  have hmap : (f.appLE (⊤ : Y.Opens) (⊤ : X.Opens) e).hom = f.appTop.hom := by
    have htop : f.appLE ⊤ ⊤ (by simp) = f.appTop := by
      simpa [Scheme.Hom.appLE, Scheme.Hom.appTop] using
        (Category.comp_id (f.app ⊤))
    simpa [e] using congrArg CommRingCat.Hom.hom htop
  rw [← hmap]
  exact h12.mp hf
    ⊤ (isAffineOpen_top X) ⊤ (isAffineOpen_top Y) e

/-- Global sections of a pullback of affine schemes are the tensor product of global sections. -/
noncomputable def affinePullbackΓTensorEquiv
    {X Y S : Scheme.{u}} [IsAffine X] [IsAffine Y] [IsAffine S]
    (f : X ⟶ S) (g : Y ⟶ S) :
    (letI : Algebra Γ(S, ⊤) Γ(X, ⊤) := f.appTop.hom.toAlgebra
     letI : Algebra Γ(S, ⊤) Γ(Y, ⊤) := g.appTop.hom.toAlgebra
     Γ(pullback f g, ⊤) ≃+* Γ(X, ⊤) ⊗[Γ(S, ⊤)] Γ(Y, ⊤)) := by
  letI : Algebra Γ(S, ⊤) Γ(X, ⊤) := f.appTop.hom.toAlgebra
  letI : Algebra Γ(S, ⊤) Γ(Y, ⊤) := g.appTop.hom.toAlgebra
  let hspec : IsPullback
      (pullback.fst f g ≫ X.isoSpec.hom)
      (pullback.snd f g ≫ Y.isoSpec.hom)
      (Spec.map f.appTop) (Spec.map g.appTop) :=
    (IsPullback.of_hasPullback f g).of_iso (Iso.refl _) X.isoSpec Y.isoSpec S.isoSpec
      (by simp) (by simp) (Scheme.isoSpec_hom_naturality f).symm
      (Scheme.isoSpec_hom_naturality g).symm
  have hfmap : CommRingCat.ofHom (algebraMap Γ(S, ⊤) Γ(X, ⊤)) = f.appTop := by
    ext x
    rfl
  have hgmap : CommRingCat.ofHom (algebraMap Γ(S, ⊤) Γ(Y, ⊤)) = g.appTop := by
    ext x
    rfl
  let TT := TensorProduct (Γ(S, ⊤) : CommRingCat).carrier
    (Γ(X, ⊤) : CommRingCat).carrier (Γ(Y, ⊤) : CommRingCat).carrier
  have hspecTensor :
      pullback (Spec.map f.appTop) (Spec.map g.appTop) ≅ Spec (.of TT) :=
    hfmap ▸ hgmap ▸ pullbackSpecIso Γ(S, ⊤) Γ(X, ⊤) Γ(Y, ⊤)
  let φ := hspec.isoIsPullback _ _
      (IsPullback.of_hasPullback (Spec.map f.appTop) (Spec.map g.appTop)) ≪≫ hspecTensor
  have hΓiso : IsIso (Scheme.Γ.map φ.hom.op) := by
    let : IsIso φ.hom := Iso.isIso_hom φ
    infer_instance
  let hΓ : Γ(pullback f g, ⊤) ≅ CommRingCat.of TT :=
    (asIso (Scheme.Γ.map φ.hom.op)).symm ≪≫ Scheme.ΓSpecIso (.of TT)
  exact hΓ.commRingCatIsoToRingEquiv

/-- The identification of global sections of an affine pullback with a tensor product sends a
section pulled back along the second projection to its own right tensor factor. -/
theorem affinePullbackΓTensorEquiv_snd
    {X Y S : Scheme.{u}} [IsAffine X] [IsAffine Y] [IsAffine S]
    (f : X ⟶ S) (g : Y ⟶ S) (y : Γ(Y, ⊤)) :
    letI : Algebra Γ(S, ⊤) Γ(X, ⊤) := f.appTop.hom.toAlgebra
    letI : Algebra Γ(S, ⊤) Γ(Y, ⊤) := g.appTop.hom.toAlgebra
    affinePullbackΓTensorEquiv f g ((pullback.snd f g).appTop.hom y) =
      (1 : Γ(X, ⊤)) ⊗ₜ[Γ(S, ⊤)] y := by
  classical
  let : Algebra Γ(S, ⊤) Γ(X, ⊤) := f.appTop.hom.toAlgebra
  let : Algebra Γ(S, ⊤) Γ(Y, ⊤) := g.appTop.hom.toAlgebra
  let TT := TensorProduct (Γ(S, ⊤) : CommRingCat).carrier
    (Γ(X, ⊤) : CommRingCat).carrier (Γ(Y, ⊤) : CommRingCat).carrier
  let q : Γ(Y, ⊤) →+* TT :=
    (Algebra.TensorProduct.includeRight : Γ(Y, ⊤) →ₐ[Γ(S, ⊤)] TT).toRingHom
  have hspec : IsPullback
      (pullback.fst f g ≫ X.isoSpec.hom)
      (pullback.snd f g ≫ Y.isoSpec.hom)
      (Spec.map f.appTop) (Spec.map g.appTop) :=
    (IsPullback.of_hasPullback f g).of_iso (Iso.refl _) X.isoSpec Y.isoSpec S.isoSpec
      (by simp) (by simp) (Scheme.isoSpec_hom_naturality f).symm
      (Scheme.isoSpec_hom_naturality g).symm
  have hfmap : CommRingCat.ofHom (algebraMap Γ(S, ⊤) Γ(X, ⊤)) = f.appTop := by
    ext x
    rfl
  have hgmap : CommRingCat.ofHom (algebraMap Γ(S, ⊤) Γ(Y, ⊤)) = g.appTop := by
    ext x
    rfl
  have hspec' : IsPullback
      (pullback.fst (Spec.map f.appTop) (Spec.map g.appTop))
      (pullback.snd (Spec.map f.appTop) (Spec.map g.appTop))
      (Spec.map f.appTop) (Spec.map g.appTop) :=
    IsPullback.of_hasPullback _ _
  let hspecTensor : pullback (Spec.map f.appTop) (Spec.map g.appTop) ≅ Spec (.of TT) :=
    hfmap ▸ hgmap ▸ pullbackSpecIso Γ(S, ⊤) Γ(X, ⊤) Γ(Y, ⊤)
  let α := hspec.isoIsPullback _ _ hspec'
  let φ := α ≪≫ hspecTensor
  have htensor : hspecTensor.hom ≫ Spec.map (CommRingCat.ofHom q) =
      pullback.snd (Spec.map f.appTop) (Spec.map g.appTop) := by
    have hh := AlgebraicGeometry.pullbackSpecIso_hom_snd
      Γ(S, ⊤) Γ(X, ⊤) Γ(Y, ⊤)
    convert hh using 1 <;> rfl
  have hφ : φ.hom ≫ Spec.map (CommRingCat.ofHom q) =
      pullback.snd f g ≫ Y.isoSpec.hom := by
    dsimp [φ]
    calc
      _ = α.hom ≫ pullback.snd (Spec.map f.appTop) (Spec.map g.appTop) := by
        simp only [Category.assoc]
        rw [htensor]
      _ = pullback.snd f g ≫ Y.isoSpec.hom :=
        IsPullback.isoIsPullback_hom_snd _ _ hspec hspec'
  let hΓ : Γ(pullback f g, ⊤) ≅ CommRingCat.of TT :=
    (asIso (Scheme.Γ.map φ.hom.op)).symm ≪≫ Scheme.ΓSpecIso (.of TT)
  let e := hΓ.commRingCatIsoToRingEquiv
  change e ((pullback.snd f g).appTop.hom y) = _
  apply e.symm.injective
  have hΓφ : Scheme.Hom.appTop (Spec.map (CommRingCat.ofHom q)) ≫
      Scheme.Hom.appTop φ.hom =
      Scheme.Hom.appTop (Y.isoSpec.hom) ≫ (pullback.snd f g).appTop := by
    have hh := congrArg (fun k => Scheme.Γ.map k.op) hφ
    convert hh using 1 <;> rfl
  simp only [RingEquiv.symm_apply_apply]
  symm
  change ((Scheme.ΓSpecIso (.of TT)).inv ≫ Scheme.Hom.appTop φ.hom)
      ((CommRingCat.ofHom q).hom y) = (pullback.snd f g).appTop.hom y
  rw [← CommRingCat.comp_apply,
    Scheme.ΓSpecIso_inv_naturality_assoc (CommRingCat.ofHom q) (Scheme.Hom.appTop φ.hom), hΓφ,
    Scheme.isoSpec_hom, Scheme.toSpecΓ_appTop,
    ← (show Scheme.ΓSpecIso (.of Γ(Y, ⊤)) = Scheme.ΓSpecIso Γ(Y, ⊤) from rfl),
    Iso.inv_hom_id_assoc]

/-- A basis of an algebra gives a basis of its base change, viewed as an algebra over the ring
being extended to. -/
noncomputable def tensorRightBaseChangeBasis
    {R A B : Type*} {ι : Type*} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B]
    (b : Module.Basis ι R A) :
    letI : Algebra B (A ⊗[R] B) := Algebra.TensorProduct.rightAlgebra
    Module.Basis ι B (A ⊗[R] B) := by
  letI : Algebra B (A ⊗[R] B) := Algebra.TensorProduct.rightAlgebra
  letI : Algebra B (B ⊗[R] A) := Algebra.TensorProduct.leftAlgebra
  have hc (x : B) : (Algebra.TensorProduct.comm R A B)
      (algebraMap B (A ⊗[R] B) x) = algebraMap B (B ⊗[R] A) x := by
    change (Algebra.TensorProduct.comm R A B) (1 ⊗ₜ[R] x) = x ⊗ₜ[R] 1
    rw [Algebra.TensorProduct.comm_tmul]
  let e : A ⊗[R] B ≃ₐ[B] B ⊗[R] A :=
    AlgEquiv.ofRingEquiv (f := (Algebra.TensorProduct.comm R A B).toRingEquiv) hc
  exact (b.baseChange B).map e.toLinearEquiv.symm

/-- The base-change basis consists of the tensors of the original basis vectors with `1`. -/
theorem tensorRightBaseChangeBasis_apply
    {R A B : Type*} {ι : Type*} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B]
    (b : Module.Basis ι R A) (i : ι) :
    letI : Algebra B (A ⊗[R] B) := Algebra.TensorProduct.rightAlgebra
    tensorRightBaseChangeBasis b i = b i ⊗ₜ[R] (1 : B) := by
  let : Algebra B (A ⊗[R] B) := Algebra.TensorProduct.rightAlgebra
  let : Algebra B (B ⊗[R] A) := Algebra.TensorProduct.leftAlgebra
  simp [tensorRightBaseChangeBasis, Module.Basis.baseChange_apply,
    Module.Basis.map_apply, Algebra.TensorProduct.comm_symm_tmul]

/-- The coordinate basis of the global sections of the universal total space `Y_d` over the global
sections of the base `X_d`. -/
noncomputable def universalTotalGammaBasis (d : ℕ) [NeZero d] :
    let s := universalAlgebraStructure d
    letI := s.ring
    letI := s.algebra
    let Y : Scheme.{u} := universalTotalScheme.{u} d s
    let F := universalFamily.{u} d s
    letI : Algebra Γ(scheme.{u} d, ⊤) Γ(Y, ⊤) :=
      F.appTop.hom.toAlgebra
    Module.Basis (Fin d) Γ(scheme.{u} d, ⊤) Γ(Y, ⊤) := by
  let s := universalAlgebraStructure d
  letI := s.ring
  letI := s.algebra
  let Y : Scheme.{u} := universalTotalScheme.{u} d s
  let F := universalFamily.{u} d s
  letI : Algebra Γ(scheme.{u} d, ⊤) Γ(Y, ⊤) :=
    F.appTop.hom.toAlgebra
  let ρ := (Scheme.ΓSpecIso
    (CommRingCat.of (ULift.{u} (universalRing d)))).commRingCatIsoToRingEquiv
  letI : Algebra (ULift.{u} (universalRing d))
      (UniversalFiniteFreeModule d) :=
    Algebra.compHom _ ULift.ringEquiv.toRingHom
  letI : Algebra Γ(scheme.{u} d, ⊤)
      (UniversalFiniteFreeModule d) :=
    Algebra.compHom _ ρ.toRingHom
  let eY := ((Scheme.ΓSpecIso (.of
    (ULift.{u} (UniversalFiniteFreeModule d)))).commRingCatIsoToRingEquiv).trans ULift.ringEquiv
  let e : Γ(Y, ⊤) ≃ₐ[Γ(scheme.{u} d, ⊤)]
      UniversalFiniteFreeModule d :=
    AlgEquiv.ofRingEquiv (f := eY) (by
      intro a
      have hn := congrArg CommRingCat.Hom.hom
        (Scheme.ΓSpecIso_naturality
          (CommRingCat.ofHom (RingHom.ulift
            (algebraMap (universalRing d)
              (UniversalFiniteFreeModule d)))))
      exact congrArg (fun k => k a) (congrArg
        (fun k => ULift.ringEquiv.toRingHom.comp k) hn))
  exact (universalCarrierGammaBasis.{u} d).map e.toLinearEquiv.symm

/-- The first vector of the coordinate basis of `Y_d` is the unit. -/
theorem universalTotalGammaBasis_zero (d : ℕ) [NeZero d] :
    let s := universalAlgebraStructure d
    letI := s.ring
    letI := s.algebra
    let Y : Scheme.{u} := universalTotalScheme.{u} d s
    let F := universalFamily.{u} d s
    letI : Algebra Γ(scheme.{u} d, ⊤) Γ(Y, ⊤) :=
      F.appTop.hom.toAlgebra
    universalTotalGammaBasis.{u} d 0 = 1 := by
  let s := universalAlgebraStructure d
  let := s.ring
  let := s.algebra
  let Y : Scheme.{u} := universalTotalScheme.{u} d s
  let F := universalFamily.{u} d s
  let : Algebra Γ(scheme.{u} d, ⊤) Γ(Y, ⊤) :=
    F.appTop.hom.toAlgebra
  let : Algebra (ULift.{u} (universalRing d))
      (UniversalFiniteFreeModule d) :=
    Algebra.compHom _ ULift.ringEquiv.toRingHom
  let ρ := (Scheme.ΓSpecIso
    (CommRingCat.of (ULift.{u} (universalRing d)))).commRingCatIsoToRingEquiv
  let : Algebra Γ(scheme.{u} d, ⊤)
      (UniversalFiniteFreeModule d) :=
    Algebra.compHom _ ρ.toRingHom
  unfold universalTotalGammaBasis
  rw [Module.Basis.map_apply, universalCarrierGammaBasis_apply.{u}, LinearEquiv.symm_apply_eq,
    AlgEquiv.toLinearEquiv_apply, map_one]
  have hone := s.one_eq
  rw [universalUnit, universalBasisVector] at hone
  simpa [universalBasisVector] using hone.symm

/-- The coordinate basis of `Y_d` consists of the distinguished basis vectors of `B_d`. -/
theorem universalTotalGammaBasis_apply (d : ℕ) [NeZero d] (i : Fin d) :
    let s := universalAlgebraStructure d
    letI := s.ring
    letI := s.algebra
    let Y : Scheme.{u} := universalTotalScheme.{u} d s
    let F := universalFamily.{u} d s
    letI : Algebra Γ(scheme.{u} d, ⊤) Γ(Y, ⊤) :=
      F.appTop.hom.toAlgebra
    universalTotalGammaBasis.{u} d i =
      (Scheme.ΓSpecIso (.of
        (ULift.{u} (UniversalFiniteFreeModule d)))).inv
          (ULift.up (universalBasisVector d i)) := by
  let s := universalAlgebraStructure d
  let := s.ring
  let := s.algebra
  change (Scheme.ΓSpecIso (.of
    (ULift.{u} (UniversalFiniteFreeModule d)))).inv
      (ULift.up (universalCarrierGammaBasis.{u} d i)) = _
  rw [universalCarrierGammaBasis_apply.{u}]

/-- The coordinates of a global section of `Y_d` in the coordinate basis are its coordinates in
`B_d`. -/
theorem universalTotalGammaBasis_repr (d : ℕ) [NeZero d] :
    let s := universalAlgebraStructure d
    letI := s.ring
    letI := s.algebra
    let Y : Scheme.{u} := universalTotalScheme.{u} d s
    let F := universalFamily.{u} d s
    letI : Algebra Γ(scheme.{u} d, ⊤) Γ(Y, ⊤) :=
      F.appTop.hom.toAlgebra
    ∀ (x : Γ(Y, ⊤)) (k : Fin d), (universalTotalGammaBasis.{u} d).repr x k =
      (Scheme.ΓSpecIso (.of (ULift.{u} (universalRing d)))).inv
        (ULift.up (((Scheme.ΓSpecIso (.of
          (ULift.{u} (UniversalFiniteFreeModule d)))).hom x).down.coeff k)) := by
  intros
  rfl

/-- The multiplication table of the coordinate basis of the universal total space is the identity
point of the base `X_d` under the representability of Tag 05YM. -/
theorem universalTotalGammaBasis_structure (d : ℕ) [NeZero d] :
    let s := universalAlgebraStructure d
    letI := s.ring
    letI := s.algebra
    let Y : Scheme.{u} := universalTotalScheme.{u} d s
    let F := universalFamily.{u} d s
    letI : Algebra Γ(scheme.{u} d, ⊤) Γ(Y, ⊤) :=
      F.appTop.hom.toAlgebra
    ofBasis (universalTotalGammaBasis.{u} d)
        (universalTotalGammaBasis_zero d) =
      (representation.{u} d).equiv
        (scheme.{u} d) (𝟙 (scheme.{u} d)) := by
  classical
  let s := universalAlgebraStructure d
  let := s.ring
  let := s.algebra
  let Y : Scheme.{u} := universalTotalScheme.{u} d s
  let F := universalFamily.{u} d s
  let : Algebra Γ(scheme.{u} d, ⊤) Γ(Y, ⊤) :=
    F.appTop.hom.toAlgebra
  apply ext_coeff
  intro i j k
  rw [representation_equiv_coeff]
  change (universalTotalGammaBasis.{u} d).repr
    (universalTotalGammaBasis.{u} d i * universalTotalGammaBasis.{u} d j) k =
      (pointRingHom d (𝟙 (scheme.{u} d)))
        (universalStructureConstant d i j k)
  rw [universalTotalGammaBasis_repr, universalTotalGammaBasis_apply.{u},
    universalTotalGammaBasis_apply.{u}]
  let e := ((Scheme.ΓSpecIso (.of
    (ULift.{u} (UniversalFiniteFreeModule d)))).commRingCatIsoToRingEquiv).trans ULift.ringEquiv
  change (Scheme.ΓSpecIso (.of (ULift.{u} (universalRing d)))).inv
    (ULift.up ((e (e.symm
      (universalBasisVector d i) * e.symm
      (universalBasisVector d j))).coeff k)) = _
  rw [map_mul, e.apply_symm_apply, e.apply_symm_apply, s.mul_eq]
  simp [universalMultiplication,
    universalBasisVector,
    pointRingHom]
  rfl

/-- The coordinate basis of an affine family transported to a base change of that family. -/
noncomputable def affinePullbackGammaBasis
    {X Y S : Scheme.{u}} [IsAffine X] [IsAffine Y] [IsAffine S]
    (f : X ⟶ S) (g : Y ⟶ S) (ι : Type*)
    (b : letI : Algebra Γ(S, ⊤) Γ(X, ⊤) := f.appTop.hom.toAlgebra
      Module.Basis ι Γ(S, ⊤) Γ(X, ⊤)) :
    letI : Algebra Γ(Y, ⊤) Γ(pullback f g, ⊤) :=
      (pullback.snd f g).appTop.hom.toAlgebra
    Module.Basis ι Γ(Y, ⊤) Γ(pullback f g, ⊤) := by
  letI : Algebra Γ(S, ⊤) Γ(X, ⊤) := f.appTop.hom.toAlgebra
  letI : Algebra Γ(S, ⊤) Γ(Y, ⊤) := g.appTop.hom.toAlgebra
  letI : Algebra Γ(Y, ⊤) Γ(pullback f g, ⊤) :=
    (pullback.snd f g).appTop.hom.toAlgebra
  letI : Algebra Γ(Y, ⊤)
      (Γ(X, ⊤) ⊗[Γ(S, ⊤)] Γ(Y, ⊤)) := Algebra.TensorProduct.rightAlgebra
  let e := affinePullbackΓTensorEquiv f g
  let eAlg : Γ(pullback f g, ⊤) ≃ₐ[Γ(Y, ⊤)]
      (Γ(X, ⊤) ⊗[Γ(S, ⊤)] Γ(Y, ⊤)) :=
    AlgEquiv.ofRingEquiv (f := e) (by
      intro y
      change e ((pullback.snd f g).appTop.hom y) = _
      rw [affinePullbackΓTensorEquiv_snd]
      rfl)
  exact (tensorRightBaseChangeBasis b).map eAlg.toLinearEquiv.symm

/-- The distinguished unit basis vector remains the unit after affine base change. -/
theorem affinePullbackGammaBasis_zero
    {X Y S : Scheme.{u}} [IsAffine X] [IsAffine Y] [IsAffine S]
    (f : X ⟶ S) (g : Y ⟶ S) (d : ℕ) [NeZero d]
    (b : letI : Algebra Γ(S, ⊤) Γ(X, ⊤) := f.appTop.hom.toAlgebra
      Module.Basis (Fin d) Γ(S, ⊤) Γ(X, ⊤)) (hb : b 0 = 1) :
    letI : Algebra Γ(Y, ⊤) Γ(pullback f g, ⊤) :=
      (pullback.snd f g).appTop.hom.toAlgebra
    affinePullbackGammaBasis f g (Fin d) b 0 = 1 := by
  let : Algebra Γ(S, ⊤) Γ(X, ⊤) := f.appTop.hom.toAlgebra
  let : Algebra Γ(S, ⊤) Γ(Y, ⊤) := g.appTop.hom.toAlgebra
  let : Algebra Γ(Y, ⊤) Γ(pullback f g, ⊤) :=
    (pullback.snd f g).appTop.hom.toAlgebra
  let : Algebra Γ(Y, ⊤)
      (Γ(X, ⊤) ⊗[Γ(S, ⊤)] Γ(Y, ⊤)) := Algebra.TensorProduct.rightAlgebra
  apply (affinePullbackΓTensorEquiv f g).injective
  simp [affinePullbackGammaBasis, Module.Basis.map_apply,
    tensorRightBaseChangeBasis_apply, hb, ← Algebra.TensorProduct.one_def]

/-- The multiplication table of a basis transported along a base change of an affine family over
the base `X_d` is the point of `X_d` along which the base change is taken, provided the table of
the original basis is the identity point. -/
theorem affinePullbackGammaBasis_structure_of_map
    {d : ℕ} [NeZero d] {Y T : Scheme.{u}} [IsAffine Y] [IsAffine T]
    (F : Y ⟶ scheme.{u} d) (f : T ⟶ scheme.{u} d)
    (b : letI : Algebra Γ(scheme.{u} d, ⊤) Γ(Y, ⊤) := F.appTop.hom.toAlgebra
      Module.Basis (Fin d) Γ(scheme.{u} d, ⊤) Γ(Y, ⊤)) (hb : b 0 = 1)
    (hrep : letI : Algebra Γ(scheme.{u} d, ⊤) Γ(Y, ⊤) := F.appTop.hom.toAlgebra
      ofBasis b hb = (representation.{u} d).equiv (scheme.{u} d) (𝟙 _)) :
    letI : Algebra Γ(T, ⊤) Γ(pullback F f, ⊤) :=
      (pullback.snd F f).appTop.hom.toAlgebra
    ofBasis (affinePullbackGammaBasis F f (Fin d) b)
      (affinePullbackGammaBasis_zero F f d b hb) = (representation.{u} d).equiv T f := by
  classical
  let : Algebra Γ(scheme.{u} d, ⊤) Γ(Y, ⊤) := F.appTop.hom.toAlgebra
  let : Algebra Γ(scheme.{u} d, ⊤) Γ(T, ⊤) := f.appTop.hom.toAlgebra
  let P := pullback F f
  let : Algebra Γ(T, ⊤) Γ(P, ⊤) := (pullback.snd F f).appTop.hom.toAlgebra
  let bT := affinePullbackGammaBasis F f (Fin d) b
  let hbTone := affinePullbackGammaBasis_zero F f d b hb
  let bTensor := tensorRightBaseChangeBasis (B := Γ(T, ⊤)) b
  let : Algebra Γ(T, ⊤) (Γ(Y, ⊤) ⊗[Γ(scheme.{u} d, ⊤)] Γ(T, ⊤)) :=
    Algebra.TensorProduct.rightAlgebra
  let : Algebra Γ(scheme.{u} d, ⊤) (Γ(Y, ⊤) ⊗[Γ(scheme.{u} d, ⊤)] Γ(T, ⊤)) :=
    Algebra.TensorProduct.leftAlgebra
  have hbTensorOne : bTensor 0 = 1 := by
    rw [tensorRightBaseChangeBasis_apply, hb, ← Algebra.TensorProduct.one_def]
  let ePT := affinePullbackΓTensorEquiv F f
  let ePTAlg : Γ(P, ⊤) ≃ₐ[Γ(T, ⊤)]
      (Γ(Y, ⊤) ⊗[Γ(scheme.{u} d, ⊤)] Γ(T, ⊤)) :=
    AlgEquiv.ofRingEquiv (f := ePT) (by
      intro t
      change ePT ((pullback.snd F f).appTop.hom t) = _
      rw [affinePullbackΓTensorEquiv_snd]
      rfl)
  have hTableTensor :
      FiniteFreeAlgebra.map f.appTop.hom (ofBasis b hb) = ofBasis bTensor hbTensorOne := by
    refine ofBasis_map f.appTop.hom Algebra.TensorProduct.includeLeftRingHom ?_
      b hb bTensor hbTensorOne ?_
    · intro r
      change Algebra.TensorProduct.includeLeftRingHom
          ((algebraMap Γ(scheme.{u} d, ⊤) Γ(Y, ⊤)) r) =
        algebraMap Γ(T, ⊤)
          (Γ(Y, ⊤) ⊗[Γ(scheme.{u} d, ⊤)] Γ(T, ⊤)) (f.appTop.hom r)
      rw [Algebra.TensorProduct.algebraMap_eq_includeRight]
      exact congrArg (fun z : Γ(scheme.{u} d, ⊤) →+*
          (Γ(Y, ⊤) ⊗[Γ(scheme.{u} d, ⊤)] Γ(T, ⊤)) => z r)
        Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap
    · intro i
      simp [bTensor, tensorRightBaseChangeBasis_apply]
  have hTablePullback :
      FiniteFreeAlgebra.map f.appTop.hom (ofBasis b hb) = ofBasis bT hbTone := by
    rw [← ofBasis_eq_of_algEquiv ePTAlg.symm bTensor bT hbTensorOne hbTone
      (by intro i; rfl)]
    exact hTableTensor
  calc
    ofBasis bT hbTone =
        FiniteFreeAlgebra.map f.appTop.hom (ofBasis b hb) := hTablePullback.symm
    _ = FiniteFreeAlgebra.map f.appTop.hom
        ((representation.{u} d).equiv (scheme.{u} d) (𝟙 _)) := congrArg _ hrep
    _ = (representation.{u} d).equiv T f := by
      simpa only [Category.comp_id] using
        (representation.{u} d).naturality f (𝟙 (scheme.{u} d))

end AlgebraicGeometry

end
