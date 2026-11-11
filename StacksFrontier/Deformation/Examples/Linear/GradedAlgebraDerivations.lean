module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.Examples.Linear.GradedAlgebrasRimSchlessinger
public import StacksFrontier.Deformation.InfinitesimalAutomorphism.Basic

/-!
# Infinitesimal automorphisms of a graded algebra

Let `P` be a graded `k`-algebra, finite-dimensional in each degree. Its deformation category is
the category of graded algebras, finite projective in each degree, over objects of `𝒞_Λ`,
localized at `(k, P)`. This file identifies the infinitesimal automorphism group of that
deformation category with the additive group of derivations of `P` preserving every homogeneous
component.

An infinitesimal automorphism is an automorphism of a lift of `(k, P)` to the dual numbers
`k[ε]`, over the identity of `k[ε]` and compatible with the reduction to `P`. Choosing
coordinates identifies such a lift with `P[ε]` over `k[ε]`, and then an automorphism over the
identity fixing the reduction is exactly `x + yε ↦ x + (D x + y)ε` for a derivation `D` of `P`;
it preserves the grading exactly when `D` does. Composition of automorphisms corresponds to
addition of derivations.

## Main definitions

* `Deformation.Examples.degreeZeroDerivations`: the derivations preserving each homogeneous
  component.

## Main results

* `infinitesimalAutomorphismGroupEquivDegreeZeroDerivations`, in the namespace
  `Deformation.Examples.ProjectiveGradedAlgebra`: the infinitesimal automorphism group of the
  deformation category of a graded algebra is the group of degree-preserving derivations under
  addition.
* `exists_infinitesimalAutomorphismGroupMulEquiv_pushforward_eq_smul`, in the same namespace:
  the identification `id + εD ↦ D` carries pushforward along a rescaling `ε ↦ cε` of the dual
  numbers to multiplication by `c`, so it is `k`-linear for the natural vector-space structure
  of the infinitesimal automorphisms.

## Implementation notes

The coordinates are produced in two steps. `tensorDualNumberCoordinates` identifies an extension
of scalars `S ⊗_R M` with `P[ε]` from ring identifications `R ≃ k`, `S ≃ k[ε]` and `M ≃ P`
compatible with the structure maps; `gradedHom_coordinates` feeds it the base-change
identification of a morphism of graded algebras, and records that the grading of the target
corresponds to the pair of gradings of the two dual-number coordinates.

Whether the chosen lift reduces to the given object over the residue field is needed in the form
"the first dual-number coordinate is the reduction map", which is
`gradedHom_coordinates_reduction`. That the object over the residue field has bijective reduction
map uses that both base algebras are fields, which makes the morphism between them bijective by
`Deformation.artinianLocalAlgHom_bijective_of_isField`.

## References

* [Stacks Project, Tag 0DVZ](https://stacks.math.columbia.edu/tag/0DVZ)
-/

@[expose] public section

open CategoryTheory

namespace Deformation.Examples

universe u w m

/-- The derivations of a graded algebra which preserve every homogeneous component. -/
public def degreeZeroDerivations {k : Type w} {P : Type (max w m)}
    [Field k] [CommRing P] [Algebra k P]
    (grading : ℕ → Submodule k P) : AddSubgroup (Derivation k P P) where
  carrier := { D | ∀ d x, x ∈ grading d → D x ∈ grading d }
  zero_mem' := by
    intro d x hx
    simp
  add_mem' := by
    intro D E hD hE d x hx
    rw [Derivation.add_apply]
    exact (grading d).add_mem (hD d x hx) (hE d x hx)
  neg_mem' := by
    intro D hD d x hx
    rw [Derivation.neg_apply]
    exact (grading d).neg_mem (hD d x hx)

/-! ### Derivations and automorphisms of the dual numbers -/

/-- The grading of `P[ε]` by pairs homogeneous in both dual-number coordinates. -/
private def dualNumberGrading
    {k : Type w} {P : Type (max w m)} [Field k] [CommRing P] [Algebra k P]
    (grading : ℕ → Submodule k P) (d : ℕ) : Submodule k (DualNumber P) where
  carrier := {x | x.fst ∈ grading d ∧ x.snd ∈ grading d}
  zero_mem' := by simp
  add_mem' hx hy := ⟨(grading d).add_mem hx.1 hy.1, (grading d).add_mem hx.2 hy.2⟩
  smul_mem' r _ hx := ⟨(grading d).smul_mem r hx.1, (grading d).smul_mem r hx.2⟩

/-- The automorphism attached to a derivation preserves the grading of `P[ε]` exactly when the
derivation preserves the grading of `P`. -/
private theorem derivationDualNumberAlgHom_preservesGrading_iff
    {k : Type w} {P : Type (max w m)} [Field k] [CommRing P] [Algebra k P]
    (grading : ℕ → Submodule k P) (D : Derivation k P P) :
    (∀ d z, z ∈ dualNumberGrading grading d →
      derivationDualNumberAlgHom D z ∈ dualNumberGrading grading d) ↔
      ∀ d x, x ∈ grading d → D x ∈ grading d := by
  refine ⟨fun hf d x hx => ?_, fun h d z hz => ?_⟩
  · have hz : TrivSqZeroExt.inl x ∈ dualNumberGrading grading d := by
      change x ∈ grading d ∧ 0 ∈ grading d
      exact ⟨hx, (grading d).zero_mem⟩
    have h := hf d (TrivSqZeroExt.inl x) hz
    change (derivationDualNumberAlgHom D (TrivSqZeroExt.inl x)).fst ∈ grading d ∧
      (derivationDualNumberAlgHom D (TrivSqZeroExt.inl x)).snd ∈ grading d at h
    rw [derivationDualNumberAlgHom_inl] at h
    simpa [TrivSqZeroExt.snd_add] using h.2
  · have hz' : z = TrivSqZeroExt.inl z.fst + TrivSqZeroExt.inr z.snd := by
      apply TrivSqZeroExt.ext <;> simp
    rw [hz', map_add, derivationDualNumberAlgHom_inl, derivationDualNumberAlgHom_inr]
    have hz'' : z.fst ∈ grading d ∧ z.snd ∈ grading d := by
      simpa [dualNumberGrading] using hz
    simpa [dualNumberGrading] using
      (show z.fst ∈ grading d ∧ D z.fst + z.snd ∈ grading d from
        ⟨hz''.1, (grading d).add_mem (h d z.fst hz''.1) hz''.2⟩)

/-! ### Dual-number coordinates for an extension of scalars -/

/-- The square of the dual-number generator, transported along a ring identification, is zero. -/
private theorem symm_eps_mul_self
    {S k : Type*} [CommRing S] [CommRing k] (c : S ≃+* DualNumber k) :
    c.symm DualNumber.eps * c.symm DualNumber.eps = 0 := by
  apply c.injective
  simp

/-- An element of a ring identified with `k[ε]` is the combination of the two coordinates, lifted
along a ring map compatible with the identification, with the generator. -/
private theorem eq_map_add_map_mul_symm_eps
    {R S k F : Type*} [CommRing R] [CommRing S] [CommRing k] [FunLike F R S]
    [RingHomClass F R S] (φ : F) (b : R ≃+* k) (c : S ≃+* DualNumber k)
    (hc : ∀ r, c (φ r) = TrivSqZeroExt.inl (b r)) (s : S) :
    s = φ (b.symm (c s).fst) + φ (b.symm (c s).snd) * c.symm DualNumber.eps := by
  apply c.injective
  rw [map_add, map_mul, hc, hc, b.apply_symm_apply, b.apply_symm_apply]
  ext <;> simp

/-- Dual-number coordinates for an extension of scalars: given ring identifications of the
source base ring with `k`, of the target base ring with `k[ε]` and of the module with `P`,
compatible with the structure maps, the extension of scalars is `P[ε]`, and `s ⊗ x` goes to the
product of the coordinates of `s` with the reduction of `x`. -/
@[sga "3 II 4.7.3" "special case"]
private theorem tensorDualNumberCoordinates
    {R S k M P : Type*} [CommRing R] [CommRing S] [CommRing k]
    [CommRing M] [CommRing P] [Algebra R S] [Algebra R M] [Algebra k P]
    (b : R ≃+* k) (c : S ≃+* DualNumber k)
    (hc : ∀ r, c (algebraMap R S r) = TrivSqZeroExt.inl (b r))
    (a : M ≃+* P) (ha : ∀ r x, a (r • x) = b r • a x) :
    ∃ E : TensorProduct R S M ≃+* DualNumber P,
      (∀ s x, E (s ⊗ₜ[R] x) =
        dualNumberRingHom (algebraMap k P) (c s) * TrivSqZeroExt.inl (a x)) := by
  let : Algebra R k := b.toRingHom.toAlgebra
  let : Algebra R P := ((algebraMap k P).comp b.toRingHom).toAlgebra
  let : IsScalarTower R k P := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let aa : M ≃ₐ[R] P :=
    { a with
      commutes' := fun r => by
        change a (algebraMap R M r) = algebraMap k P (b r)
        simpa [Algebra.smul_def] using ha r 1 }
  let cc : S →ₐ[R] DualNumber P :=
    { (dualNumberRingHom (algebraMap k P)).comp c.toRingHom with
      commutes' := fun r => by
        change dualNumberRingHom (algebraMap k P) (c (algebraMap R S r)) = _
        rw [hc]
        ext <;> simp [dualNumberRingHom, TrivSqZeroExt.algebraMap_eq_inl']
        rfl }
  let h : TensorProduct R S M →ₐ[R] DualNumber P :=
    Algebra.TensorProduct.lift cc
      ((TrivSqZeroExt.inlAlgHom R P P).comp aa.toAlgHom) (fun _ _ => Commute.all _ _)
  let j : P →ₐ[R] TensorProduct R S M :=
    Algebra.TensorProduct.includeRight.comp aa.symm.toAlgHom
  let t : S := c.symm DualNumber.eps
  have ht : t * t = 0 := symm_eps_mul_self c
  let t' : TensorProduct R S M :=
    (Algebra.TensorProduct.includeLeft : S →ₐ[R] TensorProduct R S M) t
  let h' : DualNumber P →ₐ[R] TensorProduct R S M :=
    DualNumber.lift ⟨(j, t'), by
      simpa [t'] using congrArg
        (Algebra.TensorProduct.includeLeft : S →ₐ[R] TensorProduct R S M) ht,
      fun _ => Commute.all _ _⟩
  have h_inl (p : P) : h (j p) = TrivSqZeroExt.inl p := by
    simp [h, j]
  have h_t : h t' = DualNumber.eps := by
    ext <;> simp [h, t', cc, t, dualNumberRingHom]
  have h_right (z : DualNumber P) : h (h' z) = z := by
    simp only [h', DualNumber.lift_apply_apply, map_add, map_mul, h_inl, h_t]
    ext <;> simp
  have h_left : h'.comp h = AlgHom.id R _ := by
    apply Algebra.TensorProduct.ext
    · apply AlgHom.ext
      intro s
      change
        h' (h ((Algebra.TensorProduct.includeLeft : S →ₐ[R] TensorProduct R S M) s)) = _
      rw [show h ((Algebra.TensorProduct.includeLeft : S →ₐ[R] TensorProduct R S M) s) =
          cc s by simp [h]]
      change h' (dualNumberRingHom (algebraMap k P) (c s)) =
        (Algebra.TensorProduct.includeLeft : S →ₐ[R] TensorProduct R S M) s
      have hs := eq_map_add_map_mul_symm_eps (algebraMap R S) b c hc s
      dsimp only [h']
      rw [DualNumber.lift_apply_apply, dualNumberRingHom_fst, dualNumberRingHom_snd]
      change j (algebraMap k P (c s).fst) +
        j (algebraMap k P (c s).snd) * t' = _
      have hj (r : k) : j (algebraMap k P r) =
          (Algebra.TensorProduct.includeLeft : S →ₐ[R] TensorProduct R S M)
            (algebraMap R S (b.symm r)) := by
        calc
          j (algebraMap k P r) = j (algebraMap R P (b.symm r)) := by
            congr 1
            change algebraMap k P r = algebraMap k P (b (b.symm r))
            rw [b.apply_symm_apply]
          _ = algebraMap R (TensorProduct R S M) (b.symm r) := j.commutes _
          _ = (Algebra.TensorProduct.includeLeft : S →ₐ[R] TensorProduct R S M)
              (algebraMap R S (b.symm r)) :=
            ((Algebra.TensorProduct.includeLeft :
              S →ₐ[R] TensorProduct R S M).commutes _).symm
      rw [hj, hj]
      conv_rhs => rw [hs]
      rw [map_add, map_mul]
    · apply AlgHom.ext
      intro x
      simp [h, h', j]
  refine ⟨AlgEquiv.toRingEquiv (AlgEquiv.ofAlgHom h h' (AlgHom.ext h_right) h_left), ?_⟩
  intro s x
  change h (s ⊗ₜ[R] x) = _
  simp [h, cc, aa]

/-! ### Bijectivity of a base change over a field -/

private theorem isBaseChange_map_bijective_of_tensorEquiv
    {R S M N : Type*} [CommSemiring R] [CommSemiring S]
    [AddCommMonoid M] [AddCommMonoid N]
    [Algebra R S] [Module R M] [Module R N] [Module S N]
    [IsScalarTower R S N]
    {f : M →ₗ[R] N} (h : IsBaseChange S f)
    (e : TensorProduct R S M ≃ₗ[R] M)
    (he : ∀ x, e.symm x = TensorProduct.tmul R (M := S) (N := M) (1 : S) x) :
    Function.Bijective f := by
  let F : M ≃ₗ[R] N := e.symm.trans (h.equiv.restrictScalars R)
  have hF : F.toLinearMap = f := by
    ext x
    dsimp [F]
    rw [he x]
    simp [IsBaseChange.equiv_tmul]
  rw [← hF]
  exact F.bijective

/-- Extension of scalars along an isomorphism collapses. -/
private noncomputable def tensorCollapseOfAlgEquiv
    (R S M : Type*) [CommSemiring R] [CommSemiring S] [AddCommMonoid M]
    [Algebra R S] [Module R M] (e : R ≃ₐ[R] S) : TensorProduct R S M ≃ₗ[R] M :=
  (TensorProduct.congr e.toLinearEquiv.symm (LinearEquiv.refl R M)).trans
    (TensorProduct.lid R M)

private theorem tensorCollapseOfAlgEquiv_symm_apply
    (R S M : Type*) [CommSemiring R] [CommSemiring S] [AddCommMonoid M]
    [Algebra R S] [Module R M] (e : R ≃ₐ[R] S) (x : M) :
    (tensorCollapseOfAlgEquiv R S M e).symm x =
      TensorProduct.tmul R (M := S) (N := M) (1 : S) x := by
  apply (tensorCollapseOfAlgEquiv R S M e).injective
  simp [tensorCollapseOfAlgEquiv]

private theorem isBaseChange_map_bijective_of_algEquiv
    {R S M N : Type*} [CommSemiring R] [CommSemiring S]
    [AddCommMonoid M] [AddCommMonoid N]
    [Algebra R S] [Module R M] [Module R N] [Module S N]
    [IsScalarTower R S N]
    {f : M →ₗ[R] N} (h : IsBaseChange S f) (e : R ≃ₐ[R] S) :
    Function.Bijective f :=
  isBaseChange_map_bijective_of_tensorEquiv h (tensorCollapseOfAlgEquiv R S M e)
    (tensorCollapseOfAlgEquiv_symm_apply R S M e)

/-- A morphism of `𝒞_Λ` between objects whose carriers are fields is an algebra equivalence
over its source. -/
private noncomputable def artinianLocalAlgHomAlgEquiv_of_isField
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (A B : ArtinianLocalAlgCat.{u, w, w} Λ k)
    (hA : IsField A) (hB : IsField B) (f : A ⟶ B) :
    letI : Algebra A B := f.hom.toAlgebra
    A ≃ₐ[A] B := by
  let : Field A := hA.toField
  let : Field B := hB.toField
  let : Algebra A B := f.hom.toAlgebra
  let alg : A →ₐ[A] B := {
    toRingHom := f.hom.toRingHom
    commutes' := fun _ ↦ rfl }
  exact AlgEquiv.ofBijective alg (artinianLocalAlgHom_bijective_of_isField A B hA hB f)

namespace ProjectiveGradedAlgebra

/-- The base of the object over the residue field is a field. -/
private theorem isField_residueFieldObject
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k] :
    IsField (residueFieldObject.{u, w, w} Λ k) := by
  change IsField (ULift.{w} k)
  exact MulEquiv.isField (Field.toIsField k) (ULift.ringEquiv : ULift.{w, w} k ≃+* k)

/-! ### Dual-number coordinates for a lift of a graded algebra -/

/-- Over a field fibre, a base-change morphism of graded algebras is bijective on carriers. -/
private theorem gradedHom_map_bijective_of_field_bases
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {X Y : ProjectiveGradedAlgebra.{u, w, w, max w m} Λ k}
    (hX : IsField X.base) (hY : IsField Y.base)
    (f : ProjectiveGradedAlgebra.Hom X Y) : Function.Bijective f.map := by
  let : CommRing (↑X.base) := X.base.commRing
  let : CommRing (↑Y.base) := Y.base.commRing
  let : CommRing X.carrier := X.commRing
  let : CommRing Y.carrier := Y.commRing
  let : Algebra (↑X.base) (↑Y.base) := f.base.hom.toAlgebra
  let : Module (↑X.base) Y.carrier := Module.compHom Y.carrier f.base.hom.toRingHom
  let : IsScalarTower (↑X.base) (↑Y.base) Y.carrier :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  have hbc := f.isBaseChange
  change IsBaseChange (↑Y.base)
    ({ f.map.toAddMonoidHom with map_smul' := f.map_smul } :
      X.carrier →ₗ[↑X.base] Y.carrier) at hbc
  exact isBaseChange_map_bijective_of_algEquiv hbc
    (artinianLocalAlgHomAlgEquiv_of_isField X.base Y.base hX hY f.base)

/-- The preimage of a homogeneous element under a bijective base-change morphism is homogeneous
of the same degree. -/
private theorem gradedHom_map_preimage_mem
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {X Y : ProjectiveGradedAlgebra.{u, w, w, max w m} Λ k}
    (f : ProjectiveGradedAlgebra.Hom X Y)
    (hf : Function.Bijective f.map) (d : ℕ) {y : Y.carrier}
    (hy : y ∈ Y.grading d) :
    ∃ x : X.carrier, x ∈ X.grading d ∧ f.map x = y := by
  obtain ⟨x, rfl⟩ := hf.2 y
  have hp : GradedAlgebra.proj X.grading d x = x := by
    apply hf.1
    rw [← gradedHom_proj_apply, GradedAlgebra.proj_apply,
      DirectSum.decompose_of_mem_same _ hy]
  refine ⟨x, ?_, rfl⟩
  have hx : GradedAlgebra.proj X.grading d x ∈ X.grading d := by
    rw [GradedAlgebra.proj_apply]
    exact ((DirectSum.decomposeAlgEquiv X.grading x) d).property
  simpa [hp] using hx

/-- The reduction map of an object of the deformation category lying over the residue field is
bijective on carriers. -/
private theorem residueFiber_hom_map_bijective
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (P : Type (max w m)) [CommRing P] [Algebra k P]
    (grading : ℕ → Submodule k P) [GradedAlgebra grading]
    [∀ d, Module.Finite k (grading d)]
    {x₀ : (objectsOverFunctor
      (ProjectiveGradedAlgebra.projection.{u, w, w, max w m} (Λ := Λ) (k := k))
      (specialFiber (Λ := Λ) P grading)).Fiber
        (residueFieldObject.{u, w, w} Λ k)} :
    Function.Bijective x₀.1.hom.map := by
  let X := x₀.1.left
  let Y := specialFiber (Λ := Λ) P grading
  have hbase : X.base = residueFieldObject.{u, w, w} Λ k := x₀.2
  have hX : IsField X.base := by
    rw [hbase]
    exact isField_residueFieldObject
  have hY : IsField Y.base := by
    dsimp [Y, specialFiber]
    exact Field.toIsField k
  exact gradedHom_map_bijective_of_field_bases hX hY x₀.1.hom

/-- An identification of a graded algebra with the special fibre, along a morphism to it, sends
homogeneous elements back to homogeneous elements of the same degree. -/
private theorem symm_mem_grading_of_eq_map
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (P : Type (max w m)) [CommRing P] [Algebra k P]
    (grading : ℕ → Submodule k P) [GradedAlgebra grading]
    [∀ d, Module.Finite k (grading d)]
    {X : ProjectiveGradedAlgebra.{u, w, w, max w m} Λ k}
    (h : X ⟶ specialFiber (Λ := Λ) P grading)
    (a : X.carrier ≃+* P) (ha : ∀ x, a x = h.map x) {d : ℕ} {q : P} (hq : q ∈ grading d) :
    a.symm q ∈ X.grading d := by
  have he : h.map = a.toRingHom := RingHom.ext fun x => (ha x).symm
  obtain ⟨x, hx, rfl⟩ := gradedHom_map_preimage_mem h (by rw [he]; exact a.bijective) d hq
  rwa [← ha, a.symm_apply_apply]

/-- Dual-number coordinates for a lift: given a morphism `f : X ⟶ Y` of graded algebras whose
base algebras are identified with `k` and `k[ε]` compatibly, and whose source is identified with
the special fibre `P`, the carrier of `Y` is `P[ε]`, with `s` acting through the coordinates of
`s` and with the grading of `Y` matching the pair of gradings of `P`. -/
private theorem gradedHom_coordinates
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (P : Type (max w m)) [CommRing P] [Algebra k P]
    (grading : ℕ → Submodule k P) [GradedAlgebra grading]
    [∀ d, Module.Finite k (grading d)]
    {X Y : ProjectiveGradedAlgebra.{u, w, w, max w m} Λ k}
    (f : X ⟶ Y) (h : X ⟶ specialFiber (Λ := Λ) P grading)
    (a : X.carrier ≃+* P) (ha : ∀ x, a x = h.map x)
    (b : X.base ≃+* k) (hb : ∀ r, b r = h.base.hom r)
    (c : Y.base ≃+* DualNumber k)
    (hc : ∀ r, c (f.base.hom r) = TrivSqZeroExt.inl (b r)) :
    ∃ E : Y.carrier ≃+* DualNumber P,
      (∀ x, E (f.map x) = TrivSqZeroExt.inl (a x)) ∧
      (∀ s y, E (s • y) = dualNumberRingHom (algebraMap k P) (c s) * E y) ∧
      (∀ d y, y ∈ Y.grading d ↔
        (E y).fst ∈ grading d ∧ (E y).snd ∈ grading d) := by
  let : Algebra X.base Y.base := f.base.hom.toAlgebra
  obtain ⟨T, hT⟩ := tensorDualNumberCoordinates b c hc a
    (fun r x => by
      rw [ha, h.map_smul, ← hb, ← ha]
      rfl)
  let E := (morphismPushoutEquiv f).symm.toRingEquiv.trans T
  have hE (s : Y.base) (x : X.carrier) : E (s • f.map x) =
      dualNumberRingHom (algebraMap k P) (c s) * TrivSqZeroExt.inl (a x) := by
    change T ((morphismPushoutEquiv f).symm (s • f.map x)) = _
    rw [← morphismPushoutEquiv_tmul, AlgEquiv.symm_apply_apply]
    exact hT s x
  have hEf (x : X.carrier) : E (f.map x) = TrivSqZeroExt.inl (a x) := by
    simpa using hE 1 x
  have hEs (s : Y.base) : E (algebraMap Y.base Y.carrier s) =
      dualNumberRingHom (algebraMap k P) (c s) := by
    simpa [Algebra.smul_def] using hE s 1
  have hsmul (s : Y.base) (y : Y.carrier) : E (s • y) =
      dualNumberRingHom (algebraMap k P) (c s) * E y := by
    rw [Algebra.smul_def, map_mul, hEs]
  refine ⟨E, hEf, hsmul, fun d y => ⟨fun hy => ?_, fun hy => ?_⟩⟩
  · obtain ⟨z, hz⟩ := pushout_symm_mem_baseChange f d y hy
    have hcoords : ∀ z : TensorProduct X.base Y.base (X.grading d),
        (T (((X.grading d).subtype.baseChange Y.base) z)).fst ∈ grading d ∧
        (T (((X.grading d).subtype.baseChange Y.base) z)).snd ∈ grading d := by
      intro z
      induction z using TensorProduct.inductionOn with
      | add p q hp hq =>
          simpa only [map_add, TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add] using
            And.intro ((grading d).add_mem hp.1 hq.1) ((grading d).add_mem hp.2 hq.2)
      | tmul s x =>
          simp only [LinearMap.baseChange_tmul, Submodule.coe_subtype, hT]
          have hx : a x ∈ grading d := by
            rw [ha]
            exact h.map_mem d x x.property
          simpa [dualNumberRingHom, DualNumber.snd_mul, ← Algebra.smul_def] using
            And.intro ((grading d).smul_mem (c s).fst hx)
              ((grading d).smul_mem (c s).snd hx)
    change (T ((morphismPushoutEquiv f).symm y)).fst ∈ grading d ∧
      (T ((morphismPushoutEquiv f).symm y)).snd ∈ grading d
    simpa only [hz] using hcoords z
  · let t : Y.base := c.symm DualNumber.eps
    have hinr (q : P) : E (t • f.map (a.symm q)) = TrivSqZeroExt.inr q := by
      rw [hE]
      ext <;> simp [t, dualNumberRingHom]
    have heq : y = f.map (a.symm (E y).fst) + t • f.map (a.symm (E y).snd) := by
      apply E.injective
      rw [map_add, hEf, a.apply_symm_apply, hinr]
      ext <;> simp
    rw [heq]
    exact (Y.grading d).add_mem
      (f.map_mem d _ (symm_mem_grading_of_eq_map P grading h a ha hy.1))
      ((Y.grading d).smul_mem t
        (f.map_mem d _ (symm_mem_grading_of_eq_map P grading h a ha hy.2)))

/-! ### Automorphisms of a lift in dual-number coordinates -/

/-- A grading-preserving algebra automorphism of the carrier, as an endomorphism of the graded
algebra over the identity of its base. -/
private def gradedAlgEquivHom
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (X : ProjectiveGradedAlgebra.{u, w, w, max w m} Λ k)
    (a : X.carrier ≃ₐ[X.base] X.carrier)
    (ha : ∀ d x, x ∈ X.grading d → a x ∈ X.grading d) : X ⟶ X where
  base := 𝟙 X.base
  map := a.toRingEquiv.toRingHom
  map_smul := a.toLinearEquiv.map_smul
  map_mem := ha
  isBaseChange := IsBaseChange.ofEquiv a.toLinearEquiv

/-- Such an automorphism which also fixes the reduction is an automorphism of the object in the
fibre of the deformation category. -/
private def gradedFiberAut
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {Z : ProjectiveGradedAlgebra.{u, w, w, max w m} Λ k}
    {A : ArtinianLocalAlgCat.{u, w, w} Λ k}
    (x : (objectsOverFunctor ProjectiveGradedAlgebra.projection Z).Fiber A)
    (a : x.1.left.carrier ≃ₐ[x.1.left.base] x.1.left.carrier)
    (ha : ∀ d y, a y ∈ x.1.left.grading d ↔ y ∈ x.1.left.grading d)
    (hr : ∀ y, x.1.hom.map (a y) = x.1.hom.map y) : Aut x := by
  let mk (a' : x.1.left.carrier ≃ₐ[x.1.left.base] x.1.left.carrier)
      (ha' : ∀ d y, y ∈ x.1.left.grading d → a' y ∈ x.1.left.grading d)
      (hr' : ∀ y, x.1.hom.map (a' y) = x.1.hom.map y) :
      x ⟶ x := by
    let f := gradedAlgEquivHom x.1.left a' ha'
    have hf : f ≫ x.1.hom = x.1.hom :=
      ProjectiveGradedAlgebra.Hom.ext (Category.id_comp _) (RingHom.ext hr')
    refine ⟨Over.homMk f hf, ?_⟩
    apply IsHomLift.of_fac' _ _ _ x.2 x.2
    simp [f, gradedAlgEquivHom, ProjectiveGradedAlgebra.projection]
  refine ⟨mk a (fun d y hy => (ha d y).2 hy) hr,
    mk a.symm (fun d y hy => (ha d (a.symm y)).1 (by simpa using hy))
      (fun y => by simpa using (hr (a.symm y)).symm), ?_, ?_⟩ <;>
    refine Subtype.ext (Over.OverMorphism.ext (ProjectiveGradedAlgebra.Hom.ext
      (Category.id_comp _) (RingHom.ext ?_)))
  exacts [a.symm_apply_apply, a.apply_symm_apply]

private theorem gradedFiberAut_base
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {Z : ProjectiveGradedAlgebra.{u, w, w, max w m} Λ k}
    {A : ArtinianLocalAlgCat.{u, w, w} Λ k}
    (x : (objectsOverFunctor ProjectiveGradedAlgebra.projection Z).Fiber A) (a : Aut x) :
    a.asIso.hom.val.left.base = 𝟙 x.1.left.base := by
  have := a.asIso.hom.property
  simpa [ProjectiveGradedAlgebra.projection] using
    IsHomLift.fac' (objectsOverFunctor ProjectiveGradedAlgebra.projection Z) (𝟙 A) a.asIso.hom.val

/-- An automorphism in the fibre fixes the image of the base. -/
private theorem gradedFiberAut_map_algebraMap
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {Z : ProjectiveGradedAlgebra.{u, w, w, max w m} Λ k}
    {A : ArtinianLocalAlgCat.{u, w, w} Λ k}
    (x : (objectsOverFunctor ProjectiveGradedAlgebra.projection Z).Fiber A) (a : Aut x)
    (s : x.1.left.base) :
    a.asIso.hom.val.left.map (algebraMap x.1.left.base x.1.left.carrier s) =
      algebraMap x.1.left.base x.1.left.carrier s := by
  have hh := a.asIso.hom.val.left.map_smul s 1
  rw [gradedFiberAut_base x a] at hh
  simpa [Algebra.smul_def] using hh

private theorem gradedFiberAut_ext
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {Z : ProjectiveGradedAlgebra.{u, w, w, max w m} Λ k}
    {A : ArtinianLocalAlgCat.{u, w, w} Λ k}
    {x : (objectsOverFunctor ProjectiveGradedAlgebra.projection Z).Fiber A}
    {a b : Aut x}
    (h : ∀ y, a.asIso.hom.val.left.map y = b.asIso.hom.val.left.map y) : a = b := by
  apply Aut.ext
  apply Iso.ext
  apply Subtype.ext
  apply Over.OverMorphism.ext
  apply ProjectiveGradedAlgebra.Hom.ext
  · rw [gradedFiberAut_base, gradedFiberAut_base]
  · exact RingHom.ext h

/-- In dual-number coordinates the reduction map is the first coordinate. -/
private theorem gradedHom_coordinates_reduction
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (P : Type (max w m)) [CommRing P] [Algebra k P]
    (grading : ℕ → Submodule k P) [GradedAlgebra grading]
    [∀ d, Module.Finite k (grading d)]
    {X Y : ProjectiveGradedAlgebra.{u, w, w, max w m} Λ k}
    (f : X ⟶ Y) (h : X ⟶ specialFiber (Λ := Λ) P grading)
    (q : Y ⟶ specialFiber (Λ := Λ) P grading) (hq : f ≫ q = h)
    (a : X.carrier ≃+* P) (ha : ∀ x, a x = h.map x)
    (b : X.base ≃+* k) (hb : ∀ r, b r = h.base.hom r)
    (c : Y.base ≃+* DualNumber k)
    (hc : ∀ r, c (f.base.hom r) = TrivSqZeroExt.inl (b r))
    (E : Y.carrier ≃+* DualNumber P)
    (hf : ∀ x, E (f.map x) = TrivSqZeroExt.inl (a x))
    (hs : ∀ s y, E (s • y) = dualNumberRingHom (algebraMap k P) (c s) * E y) :
    ∀ y, (E y).fst = q.map y := by
  let qb : Y.base →+* k := q.base.hom.toRingHom
  let qp : Y.carrier →+* P := q.map
  have hbase (r : X.base) : qb (f.base.hom r) = b r := by
    rw [hb]
    exact AlgHom.congr_fun (congrArg (fun v : X ⟶ specialFiber (Λ := Λ) P grading =>
      v.base.hom) hq) r
  let t : Y.base := c.symm DualNumber.eps
  have ht : t * t = 0 := symm_eps_mul_self c
  have hqt : qb t = 0 :=
    mul_self_eq_zero.mp (by simpa only [map_mul, map_zero] using congrArg qb ht)
  have hqbase (s : Y.base) : qb s = (c s).fst := by
    have he := eq_map_add_map_mul_symm_eps f.base.hom b c hc s
    conv_lhs => rw [he]
    rw [map_add, map_mul, hbase, hbase, hqt, mul_zero, add_zero, b.apply_symm_apply]
  let : Algebra X.base Y.base := f.base.hom.toAlgebra
  change ∀ y, (E y).fst = qp y
  intro y
  obtain ⟨z, rfl⟩ := (morphismPushoutEquiv f).surjective y
  induction z using TensorProduct.inductionOn with
  | add z z' hz hz' => simp only [map_add, TrivSqZeroExt.fst_add, hz, hz']
  | tmul s x =>
      have hqs (s : Y.base) (y : Y.carrier) : qp (s • y) = qb s • qp y :=
        q.map_smul s y
      have he : qp (f.map x) = a x := by
        rw [ha]
        exact RingHom.congr_fun (congrArg ProjectiveGradedAlgebra.Hom.map hq) x
      rw [morphismPushoutEquiv_tmul, hs, hf, hqs, hqbase, he]
      simp [dualNumberRingHom, Algebra.smul_def]

/-- Dual-number coordinates for an arbitrary lift of the special fibre along a canonical
dual-number pair. -/
private theorem coordinates_of_lift
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (P : Type (max w m)) [CommRing P] [Algebra k P]
    (grading : ℕ → Submodule k P) [GradedAlgebra grading]
    [∀ d, Module.Finite k (grading d)]
    {Aε : ArtinianLocalAlgCat.{u, w, w} Λ k}
    {x₀ : (objectsOverFunctor ProjectiveGradedAlgebra.projection
      (specialFiber (Λ := Λ) P grading)).Fiber (residueFieldObject.{u, w, w} Λ k)}
    {xε : (objectsOverFunctor ProjectiveGradedAlgebra.projection
      (specialFiber (Λ := Λ) P grading)).Fiber Aε}
    (g : residueFieldObject.{u, w, w} Λ k ⟶ Aε)
    (e : Aε ⟶ residueFieldObject.{u, w, w} Λ k)
    (hpair : IsCanonicalDualNumberPair g e)
    (i : x₀.1 ⟶ xε.1)
    (hi : (objectsOverFunctor ProjectiveGradedAlgebra.projection
      (specialFiber (Λ := Λ) P grading)).IsHomLift g i) :
    ∃ (E : xε.1.left.carrier ≃+* DualNumber P) (c : xε.1.left.base ≃+* DualNumber k),
      (∀ s y, E (s • y) = dualNumberRingHom (algebraMap k P) (c s) * E y) ∧
      (∀ d y, y ∈ xε.1.left.grading d ↔
        (E y).fst ∈ grading d ∧ (E y).snd ∈ grading d) ∧
      (∀ y, (E y).fst = xε.1.hom.map y) ∧
      (∀ t, (c t).fst = xε.1.left.base.residueEquiv (IsLocalRing.residue _ t)) ∧
      (∀ q, ∃ x, E (i.left.map x) = TrivSqZeroExt.inl q) := by
  let a : x₀.1.left.carrier ≃+* P :=
    RingEquiv.ofBijective x₀.1.hom.map (residueFiber_hom_map_bijective P grading)
  have hb₀ : x₀.1.left.base = residueFieldObject.{u, w, w} Λ k := x₀.2
  have hbε : xε.1.left.base = Aε := xε.2
  have hfield : IsField x₀.1.left.base := by
    rw [hb₀]
    exact isField_residueFieldObject
  let b : x₀.1.left.base ≃+* k := RingEquiv.ofBijective x₀.1.hom.base.hom.toRingHom
    (artinianLocalAlgHom_bijective_of_isField _ _ hfield (Field.toIsField k) x₀.1.hom.base)
  obtain ⟨b₀, bε, hg, he, _⟩ := hpair
  let B := (ringEquivOfIso (eqToIso hb₀)).trans b₀.toRingEquiv
  let C := (ringEquivOfIso (eqToIso hbε)).trans bε.toRingEquiv
  have hC (r : x₀.1.left.base) : C (i.left.base.hom r) = TrivSqZeroExt.inl (B r) := by
    have := hi
    have hh := (IsHomLift.commSq
      (objectsOverFunctor ProjectiveGradedAlgebra.projection
        (specialFiber (Λ := Λ) P grading)) g i).w
    have hh' : i.left.base ≫ eqToHom hbε = eqToHom hb₀ ≫ g := hh
    have hh'' := congrArg (fun f : x₀.1.left.base ⟶ Aε => f.hom r) hh'
    change (eqToHom hbε).hom (i.left.base.hom r) = g.hom ((eqToHom hb₀).hom r) at hh''
    change bε ((eqToHom hbε).hom (i.left.base.hom r)) = _
    rw [hh'']
    exact AlgHom.congr_fun hg ((eqToHom hb₀).hom r)
  let c := C.trans (dualNumberRingEquiv (B.symm.trans b))
  have hc (r : x₀.1.left.base) : c (i.left.base.hom r) = TrivSqZeroExt.inl (b r) := by
    change dualNumberRingEquiv (B.symm.trans b) (C (i.left.base.hom r)) = _
    rw [hC]
    ext <;> simp [dualNumberRingEquiv, dualNumberRingHom]
  obtain ⟨E, hf, hs, hm⟩ := gradedHom_coordinates P grading i.left x₀.1.hom
    a (fun _ => rfl) b (fun _ => rfl) c hc
  have hres (t : xε.1.left.base) :
      (c t).fst = xε.1.left.base.residueEquiv (IsLocalRing.residue _ t) := by
    let F : xε.1.left.base ⟶ residueFieldBase Λ k :=
      eqToHom hbε ≫ e ≫ eqToHom hb₀.symm ≫ x₀.1.hom.base
    have hF : (c t).fst = F.hom t := by
      change (dualNumberRingHom (B.symm.trans b).toRingHom (C t)).fst = _
      rw [dualNumberRingHom_fst]
      change b (B.symm (bε ((eqToHom hbε).hom t)).fst) = _
      have he' := AlgHom.congr_fun he ((eqToHom hbε).hom t)
      change b₀ (e.hom ((eqToHom hbε).hom t)) = (bε ((eqToHom hbε).hom t)).fst at he'
      have hB : B.symm (b₀ (e.hom ((eqToHom hbε).hom t))) =
          (eqToHom hb₀.symm).hom (e.hom ((eqToHom hbε).hom t)) := by
        apply B.injective
        rw [RingEquiv.apply_symm_apply]
        change _ = b₀ ((eqToHom hb₀).hom ((eqToHom hb₀.symm).hom (e.hom ((eqToHom hbε).hom t))))
        have hid : ∀ {X Y : ArtinianLocalAlgCat.{u, w, w} Λ k} (h : X = Y) (z : Y),
            (eqToHom h).hom ((eqToHom h.symm).hom z) = z := by
          intro X Y h z
          subst h
          rfl
        rw [hid]
      rw [← he', hB]
      rfl
    rw [hF]
    exact (residueFieldBase_residueEquiv_residue Λ k (F.hom t)).symm.trans (F.residue_comm t)
  exact ⟨E, c, hs, hm, gradedHom_coordinates_reduction P grading i.left x₀.1.hom xε.1.hom i.w
    a (fun _ => rfl) b (fun _ => rfl) c hc E hf hs, hres,
    fun q => ⟨a.symm q, by rw [hf, a.apply_symm_apply]⟩⟩

/-- An identification compatible with scalar multiplication sends the image of a scalar to the
coordinates of that scalar. -/
private theorem map_algebraMap_of_map_smul
    {S C Q : Type*} [CommRing S] [CommRing C] [CommRing Q] [Algebra S C] (E : C ≃+* Q)
    (φ : S → Q) (hs : ∀ s y, E (s • y) = φ s * E y) (s : S) : E (algebraMap S C s) = φ s := by
  simpa [Algebra.smul_def] using hs s 1

/-- The automorphism of a lift attached to a degree-preserving derivation, in dual-number
coordinates. -/
private noncomputable def coordinateDerivationAut
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (P : Type (max w m)) [CommRing P] [Algebra k P]
    (grading : ℕ → Submodule k P) [GradedAlgebra grading]
    [∀ d, Module.Finite k (grading d)]
    {A : ArtinianLocalAlgCat.{u, w, w} Λ k}
    (x : (objectsOverFunctor ProjectiveGradedAlgebra.projection
      (specialFiber (Λ := Λ) P grading)).Fiber A)
    (E : x.1.left.carrier ≃+* DualNumber P)
    (c : x.1.left.base ≃+* DualNumber k)
    (hs : ∀ s y, E (s • y) = dualNumberRingHom (algebraMap k P) (c s) * E y)
    (hm : ∀ d y, y ∈ x.1.left.grading d ↔
      (E y).fst ∈ grading d ∧ (E y).snd ∈ grading d)
    (hr : ∀ y, (E y).fst = x.1.hom.map y)
    (D : degreeZeroDerivations grading) : Aut x := by
  let ar := (E.trans (derivationDualNumberAlgEquiv D.val).toRingEquiv).trans E.symm
  have har (y : x.1.left.carrier) :
      E (ar y) = derivationDualNumberAlgHom D.val (E y) :=
    E.apply_symm_apply _
  let a : x.1.left.carrier ≃ₐ[x.1.left.base] x.1.left.carrier :=
    { ar with
      commutes' := fun s => by
        apply E.injective
        change E (ar (algebraMap _ _ s)) = E (algebraMap _ _ s)
        rw [har, map_algebraMap_of_map_smul E _ hs, derivationDualNumberAlgHom_scalar] }
  apply gradedFiberAut x a
  · intro d y
    rw [hm, hm]
    change (E (ar y)).fst ∈ grading d ∧ (E (ar y)).snd ∈ grading d ↔ _
    rw [har, (derivationDualNumberAlgHom_coordinates D.val _).1,
      (derivationDualNumberAlgHom_coordinates D.val _).2]
    exact ⟨fun hy => ⟨hy.1, ((grading d).add_mem_iff_right (D.property d _ hy.1)).mp hy.2⟩,
      fun hy => ⟨hy.1, (grading d).add_mem (D.property d _ hy.1) hy.2⟩⟩
  · intro y
    rw [← hr, ← hr]
    change (E (ar y)).fst = (E y).fst
    rw [har]
    exact (derivationDualNumberAlgHom_coordinates D.val _).1

private theorem coordinateDerivationAut_apply
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (P : Type (max w m)) [CommRing P] [Algebra k P]
    (grading : ℕ → Submodule k P) [GradedAlgebra grading]
    [∀ d, Module.Finite k (grading d)]
    {A : ArtinianLocalAlgCat.{u, w, w} Λ k}
    (x : (objectsOverFunctor ProjectiveGradedAlgebra.projection
      (specialFiber (Λ := Λ) P grading)).Fiber A)
    (E : x.1.left.carrier ≃+* DualNumber P)
    (c : x.1.left.base ≃+* DualNumber k)
    (hs : ∀ s y, E (s • y) = dualNumberRingHom (algebraMap k P) (c s) * E y)
    (hm : ∀ d y, y ∈ x.1.left.grading d ↔
      (E y).fst ∈ grading d ∧ (E y).snd ∈ grading d)
    (hr : ∀ y, (E y).fst = x.1.hom.map y)
    (D : degreeZeroDerivations grading) (y : x.1.left.carrier) :
    E ((coordinateDerivationAut P grading x E c hs hm hr D).asIso.hom.val.left.map y) =
      derivationDualNumberAlgHom D.val (E y) := E.apply_symm_apply _

/-- Distinct degree-preserving derivations give distinct automorphisms. -/
private theorem coordinateDerivationAut_injective
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (P : Type (max w m)) [CommRing P] [Algebra k P]
    (grading : ℕ → Submodule k P) [GradedAlgebra grading]
    [∀ d, Module.Finite k (grading d)]
    {A : ArtinianLocalAlgCat.{u, w, w} Λ k}
    (x : (objectsOverFunctor ProjectiveGradedAlgebra.projection
      (specialFiber (Λ := Λ) P grading)).Fiber A)
    (E : x.1.left.carrier ≃+* DualNumber P)
    (c : x.1.left.base ≃+* DualNumber k)
    (hs : ∀ s y, E (s • y) = dualNumberRingHom (algebraMap k P) (c s) * E y)
    (hm : ∀ d y, y ∈ x.1.left.grading d ↔
      (E y).fst ∈ grading d ∧ (E y).snd ∈ grading d)
    (hr : ∀ y, (E y).fst = x.1.hom.map y) :
    Function.Injective (coordinateDerivationAut P grading x E c hs hm hr) := by
  intro D D' he
  apply Subtype.ext
  apply Derivation.ext
  intro p
  have he' := congrArg (fun a : Aut x =>
    (E (a.asIso.hom.val.left.map (E.symm (TrivSqZeroExt.inl p)))).snd) he
  change (E ((coordinateDerivationAut P grading x E c hs hm hr D).asIso.hom.val.left.map _)).snd =
    (E ((coordinateDerivationAut P grading x E c hs hm hr D').asIso.hom.val.left.map _)).snd at he'
  rw [coordinateDerivationAut_apply, coordinateDerivationAut_apply,
    E.apply_symm_apply, derivationDualNumberAlgHom_inl,
    derivationDualNumberAlgHom_inl] at he'
  simpa using he'

/-- Every automorphism of a lift over the identity fixing the reduction comes from a
degree-preserving derivation. -/
private theorem exists_coordinateDerivationAut_eq
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (P : Type (max w m)) [CommRing P] [Algebra k P]
    (grading : ℕ → Submodule k P) [GradedAlgebra grading]
    [∀ d, Module.Finite k (grading d)]
    {A : ArtinianLocalAlgCat.{u, w, w} Λ k}
    (x : (objectsOverFunctor ProjectiveGradedAlgebra.projection
      (specialFiber (Λ := Λ) P grading)).Fiber A)
    (E : x.1.left.carrier ≃+* DualNumber P)
    (c : x.1.left.base ≃+* DualNumber k)
    (hs : ∀ s y, E (s • y) = dualNumberRingHom (algebraMap k P) (c s) * E y)
    (hm : ∀ d y, y ∈ x.1.left.grading d ↔
      (E y).fst ∈ grading d ∧ (E y).snd ∈ grading d)
    (hr : ∀ y, (E y).fst = x.1.hom.map y) (a : Aut x) :
    ∃ D, coordinateDerivationAut P grading x E c hs hm hr D = a := by
  let fr : DualNumber P →+* DualNumber P :=
    E.toRingHom.comp (a.asIso.hom.val.left.map.comp E.symm.toRingHom)
  have hbase (s : x.1.left.base) : fr (dualNumberRingHom (algebraMap k P) (c s)) =
      dualNumberRingHom (algebraMap k P) (c s) := by
    rw [← map_algebraMap_of_map_smul E _ hs]
    change E (a.asIso.hom.val.left.map (E.symm (E (algebraMap _ _ s)))) = _
    rw [E.symm_apply_apply, gradedFiberAut_map_algebraMap x a]
  let f : DualNumber P →ₐ[k] DualNumber P :=
    { fr with
      commutes' := fun r => by
        simpa [dualNumberRingHom, TrivSqZeroExt.algebraMap_eq_inl'] using
          hbase (c.symm (TrivSqZeroExt.inl r)) }
  have heps : f DualNumber.eps = DualNumber.eps := by
    have hh' : dualNumberRingHom (algebraMap k P) (c (c.symm DualNumber.eps)) =
        DualNumber.eps := by ext <;> simp [dualNumberRingHom]
    change fr DualNumber.eps = DualNumber.eps
    simpa only [hh'] using hbase (c.symm DualNumber.eps)
  have hared (y : x.1.left.carrier) :
      x.1.hom.map (a.asIso.hom.val.left.map y) = x.1.hom.map y :=
    RingHom.congr_fun (congrArg ProjectiveGradedAlgebra.Hom.map a.asIso.hom.val.w) y
  have hred (p : P) : (f (TrivSqZeroExt.inl p)).fst = p := by
    change (E (a.asIso.hom.val.left.map (E.symm (TrivSqZeroExt.inl p)))).fst = p
    rw [hr, hared, ← hr, E.apply_symm_apply]
    rfl
  let D := derivationOfDualNumberAlgHom f hred
  have hD : derivationDualNumberAlgHom D = f :=
    derivationDualNumberAlgHom_derivationOfDualNumberAlgHom f hred heps
  have hdegree : D ∈ degreeZeroDerivations grading := by
    apply (derivationDualNumberAlgHom_preservesGrading_iff grading D).mp
    intro d z hz
    rw [hD]
    change (E (a.asIso.hom.val.left.map (E.symm z))).fst ∈ grading d ∧
      (E (a.asIso.hom.val.left.map (E.symm z))).snd ∈ grading d
    apply (hm d _).mp
    apply a.asIso.hom.val.left.map_mem
    apply (hm d _).mpr
    change z.fst ∈ grading d ∧ z.snd ∈ grading d at hz
    simpa only [E.apply_symm_apply] using hz
  refine ⟨⟨D, hdegree⟩, gradedFiberAut_ext fun y => E.injective ?_⟩
  change E ((coordinateDerivationAut P grading x E c hs hm hr
    ⟨D, hdegree⟩).asIso.hom.val.left.map y) = _
  rw [coordinateDerivationAut_apply, hD]
  change E (a.asIso.hom.val.left.map (E.symm (E y))) = _
  rw [E.symm_apply_apply]

/-- In dual-number coordinates, the automorphisms of a lift over the identity which fix the
reduction are exactly the degree-preserving derivations, with composition corresponding to
addition. -/
private noncomputable def coordinateAutEquiv
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (P : Type (max w m)) [CommRing P] [Algebra k P]
    (grading : ℕ → Submodule k P) [GradedAlgebra grading]
    [∀ d, Module.Finite k (grading d)]
    {A : ArtinianLocalAlgCat.{u, w, w} Λ k}
    (x : (objectsOverFunctor ProjectiveGradedAlgebra.projection
      (specialFiber (Λ := Λ) P grading)).Fiber A)
    (E : x.1.left.carrier ≃+* DualNumber P)
    (c : x.1.left.base ≃+* DualNumber k)
    (hs : ∀ s y, E (s • y) = dualNumberRingHom (algebraMap k P) (c s) * E y)
    (hm : ∀ d y, y ∈ x.1.left.grading d ↔
      (E y).fst ∈ grading d ∧ (E y).snd ∈ grading d)
    (hr : ∀ y, (E y).fst = x.1.hom.map y) :
    Multiplicative (degreeZeroDerivations grading) ≃* Aut x := by
  let F : Multiplicative (degreeZeroDerivations grading) →* Aut x :=
    { toFun := fun D => coordinateDerivationAut P grading x E c hs hm hr D.toAdd
      map_one' := by
        refine gradedFiberAut_ext fun y => E.injective ?_
        rw [coordinateDerivationAut_apply]
        change derivationDualNumberAlgHom (0 : Derivation k P P) (E y) = E y
        rw [derivationDualNumberAlgHom_zero]
        rfl
      map_mul' := fun D D' => by
        refine gradedFiberAut_ext fun y => E.injective ?_
        change E ((coordinateDerivationAut P grading x E c hs hm hr
            (D.toAdd + D'.toAdd)).asIso.hom.val.left.map y) =
          E ((coordinateDerivationAut P grading x E c hs hm hr D.toAdd).asIso.hom.val.left.map
            ((coordinateDerivationAut P grading x E c hs hm hr
              D'.toAdd).asIso.hom.val.left.map y))
        rw [coordinateDerivationAut_apply, coordinateDerivationAut_apply,
          coordinateDerivationAut_apply]
        exact AlgHom.congr_fun
          (derivationDualNumberAlgHom_add D.toAdd.val D'.toAdd.val) _ }
  refine MulEquiv.ofBijective F ⟨fun D D' he => ?_, fun a => ?_⟩
  · exact Multiplicative.toAdd.injective
      (coordinateDerivationAut_injective P grading x E c hs hm hr he)
  · obtain ⟨D, hD⟩ := exists_coordinateDerivationAut_eq P grading x E c hs hm hr a
    exact ⟨Multiplicative.ofAdd D, hD⟩

/-- **Pushing forward along a rescaling `ε ↦ λε` multiplies the derivation by `λ`.** Let `j` be
an endomorphism of a lift over an endomorphism `s` of its base which, in dual-number coordinates,
fixes the constants `P` and multiplies the maximal ideal of the base by an element of residue `λ`.
Then pushing the automorphism `id + εD` forward along `j` gives `id + ελD`. -/
private theorem coordinateDerivationAut_pushforward
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (P : Type (max w m)) [CommRing P] [Algebra k P]
    (grading : ℕ → Submodule k P) [GradedAlgebra grading]
    [∀ d, Module.Finite k (grading d)]
    {A : ArtinianLocalAlgCat.{u, w, w} Λ k}
    (x : (objectsOverFunctor ProjectiveGradedAlgebra.projection
      (specialFiber (Λ := Λ) P grading)).Fiber A)
    (E : x.1.left.carrier ≃+* DualNumber P)
    (c : x.1.left.base ≃+* DualNumber k)
    (hs : ∀ s y, E (s • y) = dualNumberRingHom (algebraMap k P) (c s) * E y)
    (hm : ∀ d y, y ∈ x.1.left.grading d ↔
      (E y).fst ∈ grading d ∧ (E y).snd ∈ grading d)
    (hr : ∀ y, (E y).fst = x.1.hom.map y)
    (hres : ∀ t, (c t).fst = x.1.left.base.residueEquiv (IsLocalRing.residue _ t))
    (s : A ⟶ A) (j : x.1 ⟶ x.1)
    (hj : (objectsOverFunctor ProjectiveGradedAlgebra.projection
      (specialFiber (Λ := Λ) P grading)).IsHomLift s j)
    (lam : k) (c' : x.1.left.base)
    (hc' : x.1.left.base.residueEquiv (IsLocalRing.residue _ c') = lam)
    (hjbase : ∀ t ∈ IsLocalRing.maximalIdeal x.1.left.base, j.left.base.hom t = c' * t)
    (hjinl : ∀ q, E (j.left.map (E.symm (TrivSqZeroExt.inl q))) = TrivSqZeroExt.inl q)
    (D D' : degreeZeroDerivations grading) (hD' : D'.val = lam • D.val) :
    pushforwardAutomorphismHom
        (isDeformationCategory_deformationCategory P grading).predeformation.cofibered s j hj
        (coordinateDerivationAut P grading x E c hs hm hr D) =
      coordinateDerivationAut P grading x E c hs hm hr D' := by
  let J : DualNumber P → DualNumber P := fun z => E (j.left.map (E.symm z))
  let t₀ : x.1.left.base := c.symm DualNumber.eps
  have ht₀ : t₀ ∈ IsLocalRing.maximalIdeal x.1.left.base := by
    rw [← IsLocalRing.residue_eq_zero_iff]
    apply (ArtinianLocalAlgCat.residueEquiv x.1.left.base).injective
    rw [← hres, map_zero]
    change (c (c.symm DualNumber.eps)).fst = 0
    rw [RingEquiv.apply_symm_apply]
    rfl
  have hEeps : E (algebraMap _ _ t₀) = DualNumber.eps := by
    rw [map_algebraMap_of_map_smul E _ hs, RingEquiv.apply_symm_apply]
    ext <;> simp [dualNumberRingHom]
  have hfst : (c c').fst = lam := (hres c').trans hc'
  have hJeps : E (j.left.map (algebraMap _ _ t₀)) =
      TrivSqZeroExt.inr (algebraMap k P lam) := by
    have hmap : j.left.map (algebraMap _ _ t₀) = algebraMap _ _ (j.left.base.hom t₀) := by
      simpa [Algebra.smul_def] using j.left.map_smul t₀ 1
    rw [hmap, map_algebraMap_of_map_smul E _ hs, hjbase t₀ ht₀, map_mul,
      RingEquiv.apply_symm_apply]
    ext <;> simp [dualNumberRingHom, hfst]
  have hJ : ∀ z, J z = TrivSqZeroExt.inl z.fst + TrivSqZeroExt.inr (lam • z.snd) := by
    intro z
    have hz : E.symm z = E.symm (TrivSqZeroExt.inl z.fst) +
        E.symm (TrivSqZeroExt.inl z.snd) * algebraMap _ _ t₀ := by
      apply E.injective
      rw [map_add, map_mul, hEeps, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply,
        RingEquiv.apply_symm_apply]
      ext <;> simp
    change E (j.left.map (E.symm z)) = _
    rw [hz]
    simp only [map_add, map_mul]
    rw [hJeps, hjinl, hjinl]
    ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl, Algebra.smul_def, mul_comm]
  have hJE : ∀ y, E (j.left.map y) = J (E y) := fun y => by
    simp only [J, RingEquiv.symm_apply_apply]
  let a := coordinateDerivationAut P grading x E c hs hm hr D
  let b := coordinateDerivationAut P grading x E c hs hm hr D'
  let p := objectsOverFunctor
    (ProjectiveGradedAlgebra.projection.{u, w, w, max w m} (Λ := Λ) (k := k))
    (specialFiber (Λ := Λ) P grading)
  let hp := (isDeformationCategory_deformationCategory (Λ := Λ) P grading).predeformation
  apply Aut.ext
  apply Iso.ext
  apply Functor.Fiber.hom_ext
  change pushforwardEndomorphism hp.cofibered s j hj a = b.asIso.hom.val
  let := hj
  let := isStronglyCocartesian_of_isCofiberedInGroupoids hp.cofibered s j hj
  have : p.IsHomLift (𝟙 A) b.asIso.hom.val := b.asIso.hom.2
  apply Functor.IsStronglyCocartesian.ext p s j (𝟙 A)
  rw [← hom_comp_eq_comp_pushforwardEndomorphism hp.cofibered s j hj a]
  apply Over.OverMorphism.ext
  apply ProjectiveGradedAlgebra.Hom.ext
  · change a.asIso.hom.val.left.base ≫ j.left.base = j.left.base ≫ b.asIso.hom.val.left.base
    rw [gradedFiberAut_base, gradedFiberAut_base, Category.id_comp, Category.comp_id]
  · apply RingHom.ext
    intro y
    change j.left.map (a.asIso.hom.val.left.map y) = b.asIso.hom.val.left.map (j.left.map y)
    apply E.injective
    rw [hJE, coordinateDerivationAut_apply, coordinateDerivationAut_apply, hJE, hJ, hJ]
    obtain ⟨h1, h2⟩ := derivationDualNumberAlgHom_coordinates D.val (E y)
    obtain ⟨h3, h4⟩ := derivationDualNumberAlgHom_coordinates D'.val
      (TrivSqZeroExt.inl (E y).fst + TrivSqZeroExt.inr (lam • (E y).snd))
    apply TrivSqZeroExt.ext
    · rw [h3, h1]
      simp
    · rw [h4, h2, hD']
      simp [smul_add]

/-- The infinitesimal automorphism group of the deformation category of a graded algebra is the
additive group of degree-preserving derivations. -/
@[stacks 0DVZ "graded_inf_derivations"]
public noncomputable def infinitesimalAutomorphismGroupEquivDegreeZeroDerivations
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (P : Type (max w m)) [CommRing P] [Algebra k P]
    (grading : ℕ → Submodule k P) [GradedAlgebra grading]
    [∀ d, Module.Finite k (grading d)]
    {Aε : ArtinianLocalAlgCat.{u, w, w} Λ k}
    {x₀ : (objectsOverFunctor
      (ProjectiveGradedAlgebra.projection.{u, w, w, max w m} (Λ := Λ) (k := k))
      (specialFiber (Λ := Λ) P grading)).Fiber
        (residueFieldObject.{u, w, w} Λ k)}
    {xε : (objectsOverFunctor
      (ProjectiveGradedAlgebra.projection.{u, w, w, max w m} (Λ := Λ) (k := k))
      (specialFiber (Λ := Λ) P grading)).Fiber Aε}
    (g : residueFieldObject.{u, w, w} Λ k ⟶ Aε)
    (e : Aε ⟶ residueFieldObject.{u, w, w} Λ k)
    (hpair : IsCanonicalDualNumberPair g e)
    (i : x₀.1 ⟶ xε.1)
    (hi : (objectsOverFunctor
      (ProjectiveGradedAlgebra.projection.{u, w, w, max w m} (Λ := Λ) (k := k))
      (specialFiber (Λ := Λ) P grading)).IsHomLift g i) :
    infinitesimalAutomorphismGroup
      (isDeformationCategory_deformationCategory P grading).predeformation
      g e hpair i hi ≃*
      Multiplicative (degreeZeroDerivations grading) := by
  classical
  exact Classical.choice <| by
    obtain ⟨E, c, hs, hm, hr, -, -⟩ := coordinates_of_lift P grading g e hpair i hi
    have htop := infinitesimalAutomorphisms_eq_top
      (isDeformationCategory_deformationCategory P grading).predeformation
      x₀ xε g e hpair i hi
    exact ⟨((MulEquiv.subgroupCongr htop).trans
        (Subgroup.topEquiv (G := Aut xε))).trans
      (coordinateAutEquiv P grading xε E c hs hm hr).symm⟩

/-- **The identification `Inf(Def_P) = Der_k(P, P)` is `k`-linear (Stacks 0DVZ).** At every lift
`i : x₀ ⟶ xε` of the special fibre along a canonical dual-number pair there is a group isomorphism
`Φ` from the infinitesimal automorphisms to the degree-preserving derivations, `id + εD ↦ D` in
dual-number coordinates, which carries pushforward along a rescaling `ε ↦ cε` to multiplication
by `c`: for every endomorphism `s` of `Aε` which is `ε ↦ cε` in a dual-number coordinate of `Aε`
compatible with its residue field, and every arrow `j : xε ⟶ xε` over `s` fixing `i`, the
pushforward `b` of `a` along `j` satisfies `Φ b = c • Φ a`. -/
public theorem exists_infinitesimalAutomorphismGroupMulEquiv_pushforward_eq_smul
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (P : Type (max w m)) [CommRing P] [Algebra k P]
    (grading : ℕ → Submodule k P) [GradedAlgebra grading]
    [∀ d, Module.Finite k (grading d)]
    {Aε : ArtinianLocalAlgCat.{u, w, w} Λ k}
    {x₀ : (objectsOverFunctor
      (ProjectiveGradedAlgebra.projection.{u, w, w, max w m} (Λ := Λ) (k := k))
      (specialFiber (Λ := Λ) P grading)).Fiber
        (residueFieldObject.{u, w, w} Λ k)}
    {xε : (objectsOverFunctor
      (ProjectiveGradedAlgebra.projection.{u, w, w, max w m} (Λ := Λ) (k := k))
      (specialFiber (Λ := Λ) P grading)).Fiber Aε}
    (g : residueFieldObject.{u, w, w} Λ k ⟶ Aε)
    (e : Aε ⟶ residueFieldObject.{u, w, w} Λ k)
    (hpair : IsCanonicalDualNumberPair g e)
    (i : x₀.1 ⟶ xε.1)
    (hi : (objectsOverFunctor
      (ProjectiveGradedAlgebra.projection.{u, w, w, max w m} (Λ := Λ) (k := k))
      (specialFiber (Λ := Λ) P grading)).IsHomLift g i) :
    ∃ Φ : infinitesimalAutomorphismGroup
        (isDeformationCategory_deformationCategory P grading).predeformation
        g e hpair i hi ≃* Multiplicative (degreeZeroDerivations grading),
      ∀ (c : k) (s : Aε ⟶ Aε),
        (∃ φ : Aε ≃ₐ[Λ] DualNumber k,
          (∀ t : Aε, (φ t).1 = Aε.residueEquiv (IsLocalRing.residue Aε t)) ∧
          (∀ t : k, φ (s.hom (φ.symm (TrivSqZeroExt.inl t))) = TrivSqZeroExt.inl t) ∧
          φ (s.hom (φ.symm DualNumber.eps)) = c • DualNumber.eps) →
        ∀ (j : xε.1 ⟶ xε.1) (hj : (objectsOverFunctor
            (ProjectiveGradedAlgebra.projection.{u, w, w, max w m} (Λ := Λ) (k := k))
            (specialFiber (Λ := Λ) P grading)).IsHomLift s j),
          i ≫ j = i →
          ∀ a, ∃ b, b.val = pushforwardAutomorphismHom
              (isDeformationCategory_deformationCategory P grading).predeformation.cofibered
              s j hj a.val ∧
            (Multiplicative.toAdd (Φ b)).val = c • (Multiplicative.toAdd (Φ a)).val := by
  obtain ⟨E, cc, hs, hm, hr, hres, hinl⟩ := coordinates_of_lift P grading g e hpair i hi
  have htop := infinitesimalAutomorphisms_eq_top
    (isDeformationCategory_deformationCategory P grading).predeformation
    x₀ xε g e hpair i hi
  let K := coordinateAutEquiv P grading xε E cc hs hm hr
  let Φ := ((MulEquiv.subgroupCongr htop).trans (Subgroup.topEquiv (G := Aut xε))).trans K.symm
  have hΦ : ∀ a, K (Φ a) = a.val := fun a => K.apply_symm_apply _
  refine ⟨Φ, fun c s ⟨φ, h1, h2, h3⟩ j hj hij a => ?_⟩
  have hsm : ∀ y ∈ IsLocalRing.maximalIdeal Aε,
      s.hom y = φ.symm (TrivSqZeroExt.inl c) * y := by
    intro y hy
    have hy0 : TrivSqZeroExt.fst (φ y) = 0 :=
      (h1 y).trans (by rw [(IsLocalRing.residue_eq_zero_iff y).2 hy, map_zero])
    have hye : φ y = TrivSqZeroExt.inl (TrivSqZeroExt.snd (φ y)) * DualNumber.eps := by
      ext <;> simp [hy0]
    apply φ.injective
    have hsy : s.hom y = s.hom (φ.symm (TrivSqZeroExt.inl (TrivSqZeroExt.snd (φ y)))) *
        s.hom (φ.symm DualNumber.eps) := by
      rw [← map_mul, ← map_mul, ← hye, AlgEquiv.symm_apply_apply]
    rw [hsy, map_mul, h2, h3, map_mul, AlgEquiv.apply_symm_apply, hye]
    ext <;> simp
  have hbε : xε.1.left.base = Aε := xε.2
  have hw : j.left.base ≫ eqToHom hbε = eqToHom hbε ≫ s := by
    have := hj
    exact (IsHomLift.commSq (objectsOverFunctor ProjectiveGradedAlgebra.projection
      (specialFiber (Λ := Λ) P grading)) s j).w
  have key : ∀ {B : ArtinianLocalAlgCat.{u, w, w} Λ k} (h : B = Aε) (f : B ⟶ B),
      f ≫ eqToHom h = eqToHom h ≫ s →
      ∃ c' : B, B.residueEquiv (IsLocalRing.residue _ c') = c ∧
        ∀ t ∈ IsLocalRing.maximalIdeal B, f.hom t = c' * t := by
    intro B h f hf
    subst h
    simp only [eqToHom_refl, Category.comp_id, Category.id_comp] at hf
    subst hf
    refine ⟨φ.symm (TrivSqZeroExt.inl c), ?_, hsm⟩
    rw [← h1, AlgEquiv.apply_symm_apply]
    rfl
  obtain ⟨c', hc', hjbase⟩ := key hbε j.left.base hw
  have hjinl : ∀ q, E (j.left.map (E.symm (TrivSqZeroExt.inl q))) = TrivSqZeroExt.inl q := by
    intro q
    obtain ⟨y, hy⟩ := hinl q
    rw [← hy, E.symm_apply_apply]
    have hy' := congrArg (fun f : x₀.1 ⟶ xε.1 => f.left.map y) hij
    change j.left.map (i.left.map y) = i.left.map y at hy'
    rw [hy']
  let D := Multiplicative.toAdd (Φ a)
  have ha : a.val = coordinateDerivationAut P grading xε E cc hs hm hr D := (hΦ a).symm
  let D' : degreeZeroDerivations grading := ⟨c • D.val, fun d y hy => by
    rw [Derivation.smul_apply]
    exact (grading d).smul_mem c (D.2 d y hy)⟩
  have hpush := coordinateDerivationAut_pushforward P grading xε E cc hs hm hr hres s j hj
    c c' hc' hjbase hjinl D D' rfl
  refine ⟨⟨pushforwardAutomorphismHom
    (isDeformationCategory_deformationCategory P grading).predeformation.cofibered s j hj a.val,
      (Subgroup.eq_top_iff' _).1 htop _⟩, rfl, ?_⟩
  have hb : Φ ⟨pushforwardAutomorphismHom
      (isDeformationCategory_deformationCategory P grading).predeformation.cofibered s j hj a.val,
        (Subgroup.eq_top_iff' _).1 htop _⟩ = Multiplicative.ofAdd D' := by
    apply K.injective
    rw [hΦ]
    change _ = coordinateDerivationAut P grading xε E cc hs hm hr D'
    rw [ha, hpush]
  rw [hb]
  rfl

end ProjectiveGradedAlgebra

end Deformation.Examples
