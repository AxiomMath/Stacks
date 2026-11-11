module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ClassicalRealization
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.RealizationWeilData

/-!
# Isomorphisms of classical Weil cohomology theories and of realizations

The two sides of Stacks 0FH3, up to isomorphism.

* An isomorphism of classical Weil cohomology theories `H^*`, `H'^*` (Stacks 0FGV) is a family
  of isomorphisms of graded `F`-algebras `H^*(X) ≅ H'^*(X)`, natural in the smooth projective
  variety `X` for pullbacks, carrying the cycle class maps and the trace maps of `H^*` to those
  of `H'^*` (`Stacks.WeilCohomology.ClassicalWeilCohomologyTheory.Iso`).
* An isomorphism of realizations `(G, F[2] ≅ G(𝟏(1)))`, `(G', F[2] ≅ G'(𝟏(1)))` is a monoidal
  natural isomorphism `G ≅ G'` carrying the first isomorphism `F[2] ≅ G(𝟏(1))` to the second
  (`Stacks.WeilCohomology.ClassicalMotiveRealization.Iso`).

## Main definitions

* `Stacks.WeilCohomology.ClassicalWeilCohomologyTheory.Iso`,
  `Stacks.WeilCohomology.ClassicalWeilCohomologyTheory.isoSetoid`.
* `Stacks.WeilCohomology.ClassicalMotiveRealization.Iso`,
  `Stacks.WeilCohomology.ClassicalMotiveRealization.isoSetoid`.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u v w t

namespace Stacks.WeilCohomology

variable {k : Type u} [Field k] [IsAlgClosed k] {F : Type v} [Field F] [CharZero F]

namespace ClassicalWeilCohomologyTheory

variable {Ch : ChowCycleData.{u, t} k}

/-- The dimensions of a smooth projective variety recorded by two classical Weil cohomology
theories agree: both are the dimension of the underlying space. -/
theorem dimension_eq_dimension (T T' : ClassicalWeilCohomologyTheory.{u, v, w, t} k F Ch)
    (X : (SmoothProjective k).FullSubcategory) : T.dimension X = T'.dimension X := by
  have h := (T.dimension_eq X).symm.trans (T'.dimension_eq X)
  exact_mod_cast h

/-- **An isomorphism of classical Weil cohomology theories**: isomorphisms `H^n(X) ≅ H'^n(X)`
for every smooth projective variety `X`, commuting with pullbacks, with the cup product and the
unit, carrying `γ` to `γ'` and `∫'_X` back to `∫_X`. -/
structure Iso (T T' : ClassicalWeilCohomologyTheory.{u, v, w, t} k F Ch) where
  /-- The isomorphisms `H^n(X) ≅ H'^n(X)`. -/
  equiv : ∀ (X : (SmoothProjective k).FullSubcategory) (n : ℤ),
    (T.H X).piece n ≃ₗ[F] (T'.H X).piece n
  /-- They commute with pullbacks. -/
  equiv_pullback : ∀ {X Y : (SmoothProjective k).FullSubcategory} (f : X ⟶ Y) (n : ℤ)
    (a : (T.H Y).piece n), equiv X n (T.pullback f n a) = T'.pullback f n (equiv Y n a)
  /-- They send the unit to the unit. -/
  equiv_one : ∀ X, equiv X 0 (T.H X).one = (T'.H X).one
  /-- They commute with the cup product. -/
  equiv_mul : ∀ X (i j : ℤ) (a : (T.H X).piece i) (b : (T.H X).piece j),
    equiv X (i + j) ((T.H X).mul i j a b) = (T'.H X).mul i j (equiv X i a) (equiv X j b)
  /-- They carry the cycle class maps to the cycle class maps. -/
  equiv_cycleClass : ∀ X (r : ℤ) (α : Ch.group X r),
    equiv X (2 * r) (T.cycleClass X r α) = T'.cycleClass X r α
  /-- They carry the trace maps to the trace maps. -/
  integration_equiv : ∀ X (a : (T.H X).piece (2 * (T.dimension X : ℤ))),
    T'.integration X (ExternallyGraded.degreeCast (R := F) (X := (T'.H X).piece)
      (by rw [dimension_eq_dimension T T' X]) (equiv X _ a)) = T.integration X a

namespace Iso

variable {T T' T'' : ClassicalWeilCohomologyTheory.{u, v, w, t} k F Ch}

/-- A degree cast commutes with linear maps defined in every degree. -/
theorem degreeCast_naturality {A B : ℤ → Type*} [∀ n, AddCommGroup (A n)] [∀ n, Module F (A n)]
    [∀ n, AddCommGroup (B n)] [∀ n, Module F (B n)] (φ : ∀ n, A n →ₗ[F] B n) {i j : ℤ}
    (h : i = j) (a : A i) :
    φ j (ExternallyGraded.degreeCast (R := F) (X := A) h a) =
      ExternallyGraded.degreeCast (R := F) (X := B) h (φ i a) := by
  subst h
  rfl

/-- A degree cast commutes with linear equivalences defined in every degree. -/
theorem degreeCast_linearEquiv {A B : ℤ → Type*} [∀ n, AddCommGroup (A n)]
    [∀ n, Module F (A n)] [∀ n, AddCommGroup (B n)] [∀ n, Module F (B n)]
    (φ : ∀ n, A n ≃ₗ[F] B n) {i j : ℤ} (hij : i = j) (a : A i) :
    φ j (ExternallyGraded.degreeCast (R := F) (X := A) hij a) =
      ExternallyGraded.degreeCast (R := F) (X := B) hij (φ i a) := by
  subst hij
  rfl

/-- Two degree casts compose to a degree cast. -/
theorem degreeCast_degreeCast {A : ℤ → Type*} [∀ n, AddCommGroup (A n)] [∀ n, Module F (A n)]
    {i j l : ℤ} (h : i = j) (h' : j = l) (a : A i) :
    ExternallyGraded.degreeCast (R := F) (X := A) h'
        (ExternallyGraded.degreeCast (R := F) (X := A) h a) =
      ExternallyGraded.degreeCast (R := F) (X := A) (h.trans h') a := by
  subst h h'
  rfl

/-- A degree cast along `rfl` is the identity. -/
theorem degreeCast_rfl {A : ℤ → Type*} [∀ n, AddCommGroup (A n)] [∀ n, Module F (A n)] {i : ℤ}
    (h : i = i) (a : A i) : ExternallyGraded.degreeCast (R := F) (X := A) h a = a :=
  rfl

/-- The identity isomorphism. -/
def refl (T : ClassicalWeilCohomologyTheory.{u, v, w, t} k F Ch) : Iso T T where
  equiv _ _ := LinearEquiv.refl F _
  equiv_pullback _ _ _ := rfl
  equiv_one _ := rfl
  equiv_mul _ _ _ _ _ := rfl
  equiv_cycleClass _ _ _ := rfl
  integration_equiv _ _ := rfl

/-- The inverse isomorphism. -/
def symm (e : Iso T T') : Iso T' T where
  equiv X n := (e.equiv X n).symm
  equiv_pullback f n a := by
    apply (e.equiv _ n).injective
    rw [LinearEquiv.apply_symm_apply, e.equiv_pullback, LinearEquiv.apply_symm_apply]
  equiv_one X := by
    apply (e.equiv X 0).injective
    rw [LinearEquiv.apply_symm_apply, e.equiv_one]
  equiv_mul X i j a b := by
    apply (e.equiv X (i + j)).injective
    rw [LinearEquiv.apply_symm_apply, e.equiv_mul, LinearEquiv.apply_symm_apply,
      LinearEquiv.apply_symm_apply]
  equiv_cycleClass X r α := by
    apply (e.equiv X (2 * r)).injective
    rw [LinearEquiv.apply_symm_apply, e.equiv_cycleClass]
  integration_equiv X a := by
    have h := e.integration_equiv X (ExternallyGraded.degreeCast (R := F) (X := (T.H X).piece)
      (by rw [dimension_eq_dimension T T' X])
      ((e.equiv X (2 * (T'.dimension X : ℤ))).symm a))
    rw [degreeCast_linearEquiv (fun n ↦ e.equiv X n), LinearEquiv.apply_symm_apply,
      degreeCast_degreeCast, degreeCast_rfl] at h
    exact h.symm

/-- The composite isomorphism. -/
def trans (e : Iso T T') (e' : Iso T' T'') : Iso T T'' where
  equiv X n := (e.equiv X n).trans (e'.equiv X n)
  equiv_pullback f n a := by
    simp only [LinearEquiv.trans_apply, e.equiv_pullback, e'.equiv_pullback]
  equiv_one X := by
    simp only [LinearEquiv.trans_apply, e.equiv_one, e'.equiv_one]
  equiv_mul X i j a b := by
    simp only [LinearEquiv.trans_apply, e.equiv_mul, e'.equiv_mul]
  equiv_cycleClass X r α := by
    simp only [LinearEquiv.trans_apply, e.equiv_cycleClass, e'.equiv_cycleClass]
  integration_equiv X a := by
    rw [← e.integration_equiv X a, ← e'.integration_equiv X, LinearEquiv.trans_apply,
      degreeCast_linearEquiv (fun n ↦ e'.equiv X n), degreeCast_degreeCast]

end Iso

variable (k F Ch) in
/-- **Isomorphism of classical Weil cohomology theories**, as a setoid. -/
def isoSetoid : Setoid (ClassicalWeilCohomologyTheory.{u, v, w, t} k F Ch) where
  r T T' := Nonempty (Iso T T')
  iseqv := ⟨fun T ↦ ⟨Iso.refl T⟩, fun ⟨e⟩ ↦ ⟨e.symm⟩, fun ⟨e⟩ ⟨e'⟩ ↦ ⟨e.trans e'⟩⟩

end ClassicalWeilCohomologyTheory

namespace ClassicalMotiveRealization

open ChowMotiveCat

section

/- The monoidal structure of `M_k` is that of the twisted Karoubi envelope it is built as; it is
named through the generic instances, as in `StacksDraft.AlgebraicGeometry.WeilCohomology.Concrete`
(comparing morphisms of motives over the two instance paths makes `isDefEq` unfold
correspondences). -/
attribute [-instance] ChowMotiveCat.monoidalCategory ChowMotiveCat.braidedCategory
  ChowMotiveCat.symmetricCategory GradedCategory.TwistedKaroubi.monoidalCategoryStruct
  CorrespondenceCategory.monoidalCategoryStruct GradedCategory.TwistedKaroubi.symmetricCategory

attribute [local instance] WeilRealization.braidedTK WeilRealization.monoidalTK

/-- **An isomorphism of realizations `(G, F[2] ≅ G(𝟏(1)))`**: a monoidal natural isomorphism
`θ : G ≅ G'` carrying `F[2] ≅ G(𝟏(1))` to `F[2] ≅ G'(𝟏(1))`. -/
structure Iso (R R' : ClassicalMotiveRealization k F) where
  /-- The natural isomorphism `θ : G ≅ G'`. -/
  iso : R.toWeilRealization.functor ≅ R'.toWeilRealization.functor
  /-- `θ` is monoidal. -/
  isMonoidal : NatTrans.IsMonoidal iso.hom
  /-- `θ` carries the isomorphism `F[2] ≅ G(𝟏(1))` to `F[2] ≅ G'(𝟏(1))`. -/
  tateIso_hom_comp : R.tateIso.hom ≫ iso.hom.app (tate k 1) = R'.tateIso.hom

namespace Iso

variable {R R' R'' : ClassicalMotiveRealization k F}

/-- The identity isomorphism. -/
def refl (R : ClassicalMotiveRealization k F) : Iso R R where
  iso := CategoryTheory.Iso.refl _
  isMonoidal := inferInstanceAs (NatTrans.IsMonoidal (𝟙 R.toWeilRealization.functor))
  tateIso_hom_comp := Category.comp_id _

/-- The inverse isomorphism. -/
def symm (e : Iso R R') : Iso R' R where
  iso := e.iso.symm
  isMonoidal := by
    have := e.isMonoidal
    exact inferInstanceAs (NatTrans.IsMonoidal e.iso.inv)
  tateIso_hom_comp :=
    (CategoryTheory.Iso.comp_inv_eq (e.iso.app (tate k 1))).2 e.tateIso_hom_comp.symm

/-- The composite isomorphism. -/
def trans (e : Iso R R') (e' : Iso R' R'') : Iso R R'' where
  iso := e.iso ≪≫ e'.iso
  isMonoidal := by
    have := e.isMonoidal
    have := e'.isMonoidal
    exact inferInstanceAs (NatTrans.IsMonoidal (e.iso.hom ≫ e'.iso.hom))
  tateIso_hom_comp := (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ e'.iso.hom.app (tate k 1)) e.tateIso_hom_comp).trans e'.tateIso_hom_comp)

end Iso

end

variable (k F) in
/-- **Isomorphism of realizations `(G, F[2] ≅ G(𝟏(1)))`**, as a setoid. -/
def isoSetoid : Setoid (ClassicalMotiveRealization k F) where
  r R R' := Nonempty (Iso R R')
  iseqv := ⟨fun R ↦ ⟨Iso.refl R⟩, fun ⟨e⟩ ↦ ⟨e.symm⟩, fun ⟨e⟩ ⟨e'⟩ ↦ ⟨e.trans e'⟩⟩

end ClassicalMotiveRealization

end Stacks.WeilCohomology

end
