module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FrobeniusSplitting.LocalFrobeniusAction
public import StacksFrontier.AlgebraicGeometry.Curves.WeilBound.FixedFieldPoints
public import StacksFrontier.AlgebraicGeometry.Curves.BombieriStepanov.PointComparison

/-!
# Points of a finite étale cover above a point whose Frobenius acts trivially

Let `A` be a finite étale cover of a connected scheme `X` and `x` a closed point of `X` with finite
residue field at which some Frobenius element of `π₁(X, base)` acts trivially on the fibre of `A`
at the base point. Then `x` splits completely in `A`: the lifts `Spec κ(x) ⟶ A` of the canonical
point `Spec κ(x) ⟶ X` are as many as the points of the geometric fibre of `A`. Indeed every lift
`Spec Ω ⟶ A` of the geometric point above `x` is fixed by the Frobenius of `Ω / κ(x)`
(`AlgebraicGeometry.FrobeniusData.specMap_frobenius_comp_eq`), and the fixed lifts are those
coming from `κ(x)`, the fixed field of the Frobenius
(`AlgebraicGeometry.fixedFieldValuedPointsEquiv`, applied to the fibre `A ×_X Spec κ(x)`).

Consequently a `K`-valued point of `X` above such a point `x` has at least `d` lifts to `A`, `d`
the degree of the geometric fibre, and if every `K`-valued point of a scheme `X` over `k` lies
above such a point, `#A(K) ≥ d · #X(K)`.

## Main definitions

* `AlgebraicGeometry.FiniteEtaleOver.lifts`: the lifts `Spec K ⟶ A` of a point `Spec K ⟶ X`.

## Main results

* `AlgebraicGeometry.FrobeniusData.natCard_lifts_fromSpecResidueField`: the lifts of the canonical
  point at `x` are as many as the points of the fibre at the base point.
* `AlgebraicGeometry.FrobeniusSplitting.card_mul_le_natCard_fieldValuedPoints`:
  `d · #X(K) ≤ #A(K)`.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry

open Stacks.EtaleCohomology

/-- The lifts `Spec K ⟶ A` of a point `t : Spec K ⟶ X` to a finite étale cover `A` of `X`. -/
def FiniteEtaleOver.lifts {X : Scheme.{u}} (A : FiniteEtaleOver X) {K : Type u} [Field K]
    (t : Spec (.of K) ⟶ X) : Type u :=
  {a : Spec (.of K) ⟶ A.left // a ≫ A.hom = t}

/-- Precomposition with the spectrum of a field homomorphism is injective on field-valued
points. -/
theorem specMap_comp_injective {Y : Scheme.{u}} {K L : Type u} [Field K] [Field L]
    (φ : K →+* L) :
    Function.Injective (fun a : Spec (.of K) ⟶ Y => Spec.map (CommRingCat.ofHom φ) ≫ a) := by
  intro a b hab
  have h := congrArg (Scheme.SpecToEquivOfField L Y) hab
  simp only [Scheme.SpecToEquivOfField_specMap_comp] at h
  obtain ⟨e, he⟩ := Scheme.SpecToEquivOfField_eq_iff.1 h
  have hJ : Mono (CommRingCat.ofHom φ) := ConcreteCategory.mono_of_injective _ φ.injective
  apply (Scheme.SpecToEquivOfField K Y).injective
  refine Scheme.SpecToEquivOfField_eq_iff.2 ⟨e, (cancel_mono (CommRingCat.ofHom φ)).1 ?_⟩
  rwa [Category.assoc]

section Fibre

variable {X : Scheme.{u}} (A : FiniteEtaleOver X) {κ : Type u} [Field κ]
  (j : Spec (.of κ) ⟶ X)

/-- The lifts of `Spec L ⟶ Spec κ ⟶ X` to `A` are the `L`-valued points of the fibre
`A ×_X Spec κ` over `κ`. -/
def liftsEquivFieldValuedPoints (L : Type u) [Field L] [Algebra κ L] :
    A.lifts (Spec.map (CommRingCat.ofHom (algebraMap κ L)) ≫ j) ≃
      fieldValuedPoints (pullback.snd A.hom j) L where
  toFun a := ⟨pullback.lift a.1 (Spec.map (CommRingCat.ofHom (algebraMap κ L))) a.2,
    pullback.lift_snd _ _ _⟩
  invFun b := ⟨b.1 ≫ pullback.fst A.hom j, by
    rw [Category.assoc, pullback.condition, ← Category.assoc, b.2]⟩
  left_inv a := Subtype.ext (pullback.lift_fst _ _ _)
  right_inv b := Subtype.ext <| pullback.hom_ext (pullback.lift_fst _ _ _)
    ((pullback.lift_snd _ _ _).trans b.2.symm)

/-- The lift corresponding to an `L`-valued point `b` of the fibre `A ×_X Spec κ` is `b` followed
by the first projection `A ×_X Spec κ ⟶ A`. -/
theorem liftsEquivFieldValuedPoints_symm_apply (L : Type u) [Field L] [Algebra κ L]
    (b : fieldValuedPoints (pullback.snd A.hom j) L) :
    ((liftsEquivFieldValuedPoints A j L).symm b).1 = b.1 ≫ pullback.fst A.hom j :=
  rfl

/-- **Lifts over a finite field from Frobenius-fixed geometric lifts.** Let `κ` be a finite
field, `Ω` an algebraically closed extension and `j : Spec κ ⟶ X`. If every lift to `A` of the
geometric point `Spec Ω ⟶ Spec κ ⟶ X` is fixed by the Frobenius of `Ω / κ`, then the lifts of `j`
are as many as the lifts of the geometric point. -/
theorem natCard_lifts_eq_of_forall_fixed [Fintype κ] (Ω : Type u) [Field Ω] [Algebra κ Ω]
    [IsAlgClosed Ω] [Algebra.IsAlgebraic κ Ω]
    (hfix : ∀ q : A.lifts (Spec.map (CommRingCat.ofHom (algebraMap κ Ω)) ≫ j),
      Spec.map (CommRingCat.ofHom
        (FiniteField.frobeniusAlgEquivOfAlgebraic κ Ω : Ω →+* Ω)) ≫ q.1 = q.1) :
    Nat.card (A.lifts j) =
      Nat.card (A.lifts (Spec.map (CommRingCat.ofHom (algebraMap κ Ω)) ≫ j)) := by
  set φ := FiniteField.frobeniusAlgEquivOfAlgebraic κ Ω
  have hκκ : Spec.map (CommRingCat.ofHom (algebraMap κ κ)) ≫ j = j := by
    rw [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]
  have e1 : A.lifts j ≃ fieldValuedPoints (pullback.snd A.hom j) κ :=
    (Equiv.subtypeEquivRight (fun a => by rw [hκκ])).trans (liftsEquivFieldValuedPoints A j κ)
  have hj : ∀ a : κ, φ (Algebra.ofId κ Ω a) = Algebra.ofId κ Ω a := φ.commutes
  have hτ : ∀ a : Ω, φ.toAlgHom a = a → a ∈ Set.range (Algebra.ofId κ Ω) := fun a ha =>
    mem_range_of_pow_card_eq (algebraMap κ Ω) (a := a) ha
  have e2 := fixedFieldValuedPointsEquiv (pullback.snd A.hom j) (Algebra.ofId κ Ω) φ.toAlgHom hj hτ
  have hall : ∀ t : fieldValuedPoints (pullback.snd A.hom j) Ω,
      fieldValuedPointsPrecomp (pullback.snd A.hom j) φ.toAlgHom t = t := by
    intro t
    set q := (liftsEquivFieldValuedPoints A j Ω).symm t
    rw [← (liftsEquivFieldValuedPoints A j Ω).apply_symm_apply t]
    refine Subtype.ext (pullback.hom_ext ?_ ?_)
    · show (Spec.map _ ≫ pullback.lift q.1 _ _) ≫ pullback.fst A.hom j =
        pullback.lift q.1 _ _ ≫ pullback.fst A.hom j
      rw [Category.assoc, pullback.lift_fst]
      exact hfix q
    · show (Spec.map _ ≫ pullback.lift q.1 _ _) ≫ pullback.snd A.hom j =
        pullback.lift q.1 _ _ ≫ pullback.snd A.hom j
      rw [Category.assoc, pullback.lift_snd, ← Spec.map_comp]
      congr 2
      ext a
      exact φ.commutes a
  exact Nat.card_congr (e1.trans (e2.trans ((Equiv.subtypeUnivEquiv hall).trans
    (liftsEquivFieldValuedPoints A j Ω).symm)))

end Fibre

namespace FrobeniusData

variable {X : Scheme.{u}} [ConnectedSpace X] {base : GeometricPoint X} {x : closedPoints X}

/-- **A point at which a Frobenius element acts trivially splits completely.** If the Frobenius
element `c.element` acts trivially on the fibre of `A` at the base point, then the lifts
`Spec κ(x) ⟶ A` of the canonical point `Spec κ(x) ⟶ X` are as many as the points of that fibre. -/
theorem natCard_lifts_fromSpecResidueField (c : FrobeniusData base x) (A : FiniteEtaleOver X)
    (h : ∀ z : (finiteEtaleFiberFunctor base).obj A, ((c.element.app A).hom z) = z) :
    Nat.card (A.lifts (X.fromSpecResidueField x.1)) =
      Nat.card ((finiteEtaleFiberFunctor base).obj A) := by
  have : Finite (X.residueField x.1) := c.finite_residueField
  let _ : Fintype (X.residueField x.1) := Fintype.ofFinite _
  exact (natCard_lifts_eq_of_forall_fixed (κ := X.residueField x.1) A
    (X.fromSpecResidueField x.1) c.closure
    (fun q => specMap_frobenius_comp_eq c A h ⟨q.1, q.2⟩)).trans
    (Nat.card_congr (c.path.app A).toEquiv)

end FrobeniusData

namespace FrobeniusSplitting

variable {k : Type u} [Field k] [Finite k] {X : Scheme.{u}} [ConnectedSpace X]
  (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] [QuasiCompact f]
  {base : GeometricPoint X} (A : FiniteEtaleOver X)

omit [Finite k] [ConnectedSpace X] [LocallyOfFiniteType f] [QuasiCompact f] in
/-- A lift of a `K`-valued point of `X` to `A` is a `K`-valued point of `A`, and distinct lifts
of distinct points are distinct. -/
theorem injective_sigmaLifts (K : Type u) [Field K] [Algebra k K] :
    Function.Injective (fun b : Σ t : fieldValuedPoints f K, A.lifts t.1 =>
      (⟨b.2.1, (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ f) b.2.2).trans b.1.2)⟩ :
        fieldValuedPoints (A.hom ≫ f) K)) := by
  rintro ⟨t, a⟩ ⟨t', a'⟩ h
  have h1 : a.1 = a'.1 := congrArg Subtype.val h
  obtain rfl : t = t' := Subtype.ext (a.2.symm.trans ((congrArg (· ≫ A.hom) h1).trans a'.2))
  exact Sigma.ext rfl (heq_of_eq (Subtype.ext h1))

/-- **Counting points of a cover in which every point splits.** Let `A` be a finite étale cover of
`X` with geometric fibres of cardinality `d` and `K` a finite extension of `k`. Suppose that every
`K`-valued point of `X` lies above a closed point `x` at which some Frobenius element acts
trivially on the fibre of `A` at the base point. Then `d · #X(K) ≤ #A(K)`. -/
theorem card_mul_le_natCard_fieldValuedPoints [IsFinite A.hom] (K : Type u) [Field K]
    [Algebra k K] [Finite K]
    (hsplit : ∀ t : fieldValuedPoints f K, ∃ hx : IsClosed
      ({(Scheme.SpecToEquivOfField K X t.1).1} : Set X),
      ∃ c : FrobeniusData base ⟨_, hx⟩,
        ∀ z : (finiteEtaleFiberFunctor base).obj A, ((c.element.app A).hom z) = z) :
    Nat.card ((finiteEtaleFiberFunctor base).obj A) * Nat.card (fieldValuedPoints f K) ≤
      Nat.card (fieldValuedPoints (A.hom ≫ f) K) := by
  have : Finite (fieldValuedPoints f K) := Stacks.BombieriStepanov.finite_fieldValuedPoints f K
  have hfinA : Finite (fieldValuedPoints (A.hom ≫ f) K) :=
    Stacks.BombieriStepanov.finite_fieldValuedPoints (A.hom ≫ f) K
  have : Finite (Σ t : fieldValuedPoints f K, A.lifts t.1) :=
    @Finite.of_injective _ _ hfinA _ (injective_sigmaLifts f A K)
  have : ∀ t : fieldValuedPoints f K, Finite (A.lifts t.1) := fun t =>
    Finite.of_injective (fun a : A.lifts t.1 => (⟨t, a⟩ : Σ t : fieldValuedPoints f K, A.lifts t.1))
      (fun a b hab => eq_of_heq (Sigma.mk.inj hab).2)
  have := Fintype.ofFinite (fieldValuedPoints f K)
  refine le_trans ?_ (@Nat.card_le_card_of_injective _ _ hfinA _ (injective_sigmaLifts f A K))
  rw [Nat.card_sigma]
  calc Nat.card ((finiteEtaleFiberFunctor base).obj A) * Nat.card (fieldValuedPoints f K)
      = ∑ _t : fieldValuedPoints f K, Nat.card ((finiteEtaleFiberFunctor base).obj A) := by
        rw [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, smul_eq_mul,
          mul_comm]
    _ ≤ _ := Finset.sum_le_sum fun t _ => ?_
  obtain ⟨hx, c, hc⟩ := hsplit t
  set xι := Scheme.SpecToEquivOfField K X t.1
  have ht : Spec.map xι.2 ≫ X.fromSpecResidueField xι.1 = t.1 := by
    rw [← Scheme.SpecToEquivOfField_symm_apply, Equiv.symm_apply_apply]
  rw [← FrobeniusData.natCard_lifts_fromSpecResidueField c A hc]
  exact Nat.card_le_card_of_injective
    (fun b => ⟨Spec.map xι.2 ≫ b.1, (Category.assoc _ _ _).trans ((congrArg _ b.2).trans ht)⟩)
    fun a b hab => Subtype.ext <|
      specMap_comp_injective (Y := A.left) xι.2.hom (congrArg Subtype.val hab)

end FrobeniusSplitting

end AlgebraicGeometry

end
