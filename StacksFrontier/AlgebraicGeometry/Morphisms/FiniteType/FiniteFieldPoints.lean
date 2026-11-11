module

public import StacksFrontier.AlgebraicGeometry.Curves.BombieriStepanov.PointComparison
public import StacksFrontier.AlgebraicGeometry.Morphisms.FieldPointPurelyInseparable

/-!
# Points with values in a finite field of a scheme of finite type over a ring

Let `X` be a scheme which is quasi-compact and locally of finite type over `Spec R`, and let `F`
be a finite field which is an `R`-algebra. Then `X` has only finitely many `F`-valued points over
`Spec R`: the map `R → F` factors through the finite field `k = R / ker(R → F)`, every such point
factors through the base change `X_k`, a scheme quasi-compact and locally of finite type over the
finite field `k`, and those have finitely many points with values in a finite field.

We also record that precomposition with `Spec F ⟶ Spec κ`, for a field extension `κ → F`, is
injective on morphisms `Spec κ ⟶ X`: such a morphism is a point of `X` together with an embedding
of its residue field into `κ`, and composing that embedding with the injective map `κ → F` loses
nothing.

## Main results

* `AlgebraicGeometry.finite_sections_of_finite`: finiteness of the `F`-valued points over `R`.
* `AlgebraicGeometry.specMap_comp_injective_of_field`: injectivity of precomposition with
  `Spec F ⟶ Spec κ`.
-/

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry

/-- **A scheme quasi-compact and locally of finite type over `Spec R` has finitely many points
with values in a finite field `F` over `R`.** The map `R → F` factors through the finite field
`R / ker(R → F)`, and every such point factors uniquely through the base change of `X` to it,
whose points with values in `F` are finitely many. -/
theorem finite_sections_of_finite {R : Type u} [CommRing R] {X : Scheme.{u}}
    (h : X ⟶ Spec (.of R)) [LocallyOfFiniteType h] [QuasiCompact h]
    (F : Type u) [Field F] [Finite F] [Algebra R F] :
    Finite {p : Spec (.of F) ⟶ X // p ≫ h = Spec.map (CommRingCat.ofHom (algebraMap R F))} := by
  set I := RingHom.ker (algebraMap R F)
  have : Finite (R ⧸ I) := Finite.of_injective _ (RingHom.kerLift_injective (algebraMap R F))
  have : I.IsPrime := RingHom.ker_isPrime _
  have : IsDomain (R ⧸ I) := Ideal.Quotient.isDomain I
  have : I.IsMaximal := Ideal.Quotient.maximal_of_isField I (Finite.isDomain_to_isField _)
  let := Ideal.Quotient.field I
  let : Algebra (R ⧸ I) F := (RingHom.kerLift (algebraMap R F)).toAlgebra
  let π : Spec (.of (R ⧸ I)) ⟶ Spec (.of R) := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
  have hfac : Spec.map (CommRingCat.ofHom (algebraMap R F)) =
      Spec.map (CommRingCat.ofHom (algebraMap (R ⧸ I) F)) ≫ π := by
    rw [← Spec.map_comp]
    congr 1
  have hfin := Stacks.BombieriStepanov.finite_fieldValuedPoints (pullback.snd h π) F
  let Φ : {p : Spec (.of F) ⟶ X // p ≫ h = Spec.map (CommRingCat.ofHom (algebraMap R F))} →
      Stacks.EtaleCohomology.fieldValuedPoints (pullback.snd h π) F := fun p =>
    ⟨pullback.lift p.1 (Spec.map (CommRingCat.ofHom (algebraMap (R ⧸ I) F))) (by rw [p.2, hfac]),
      pullback.lift_snd _ _ _⟩
  refine @Finite.of_injective _ _ hfin Φ ?_
  intro p q hpq
  apply Subtype.ext
  have hfst := congrArg (fun r : Stacks.EtaleCohomology.fieldValuedPoints (pullback.snd h π) F =>
    r.1 ≫ pullback.fst h π) hpq
  calc p.1 = (Φ p).1 ≫ pullback.fst h π := (pullback.lift_fst (f := h) (g := π) p.1 _ _).symm
    _ = (Φ q).1 ≫ pullback.fst h π := hfst
    _ = q.1 := pullback.lift_fst (f := h) (g := π) q.1 _ _

/-- **Precomposition with `Spec F ⟶ Spec κ` is injective on `κ`-valued points**, for a field
homomorphism `κ → F`. Two morphisms `Spec κ ⟶ X` with equal composites have the same image
point `x`, so they are given by two embeddings `κ(x) ⟶ κ`, which agree after composition with
the injective map `κ → F`. -/
theorem specMap_comp_injective_of_field {X : Scheme.{u}} {κ F : Type u} [Field κ]
    [Field F] (φ : κ →+* F) :
    Function.Injective (fun p : Spec (.of κ) ⟶ X => Spec.map (CommRingCat.ofHom φ) ≫ p) := by
  intro p q hpq
  simp only at hpq
  have hpt : q.base (IsLocalRing.closedPoint κ) = p.base (IsLocalRing.closedPoint κ) := by
    have h1 : Spec.map (CommRingCat.ofHom φ) (IsLocalRing.closedPoint F) =
        IsLocalRing.closedPoint κ := Subsingleton.elim (α := PrimeSpectrum κ) _ _
    have hF := congrArg (fun r : Spec (.of F) ⟶ X => r (IsLocalRing.closedPoint F)) hpq
    calc q (IsLocalRing.closedPoint κ)
        = q (Spec.map (CommRingCat.ofHom φ) (IsLocalRing.closedPoint F)) := by rw [h1]
      _ = (Spec.map (CommRingCat.ofHom φ) ≫ q) (IsLocalRing.closedPoint F) := rfl
      _ = (Spec.map (CommRingCat.ofHom φ) ≫ p) (IsLocalRing.closedPoint F) := hF.symm
      _ = p (Spec.map (CommRingCat.ofHom φ) (IsLocalRing.closedPoint F)) := rfl
      _ = p (IsLocalRing.closedPoint κ) := by rw [h1]
  obtain ⟨a, ha⟩ := exists_specMap_fromSpecResidueField_eq (K := κ) (α := p) rfl
  obtain ⟨b, hb⟩ := exists_specMap_fromSpecResidueField_eq (K := κ) (α := q) hpt
  rw [← ha, ← hb] at hpq ⊢
  rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp, cancel_mono,
    Spec.map_inj] at hpq
  congr 2
  ext t
  exact φ.injective (congrArg (fun g => g t) (congrArg CommRingCat.Hom.hom hpq))

end AlgebraicGeometry
