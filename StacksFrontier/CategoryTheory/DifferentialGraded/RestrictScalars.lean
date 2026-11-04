module

public import StacksFrontier.CategoryTheory.DifferentialGraded.ConeSituation
public import StacksFrontier.CategoryTheory.DifferentialGraded.ExactFunctor

/-!
# Restriction of scalars for a differential graded category

A differential graded category is indexed by the commutative ring over which its Hom modules are
linear, and `CategoryTheory.DGCategory.DGFunctor` relates two differential graded categories
over *one* ring. For a ring homomorphism `σ : R₀ →+* R₁` this file restricts a differential
graded category over `R₁` to one over `R₀`, and restricts along `σ` every structure built on it:
differential graded functors, axiom (B), and the cone situation. Restriction to `ℤ` puts
categories of sheaf differential graded modules over two different ringed sites — as for
`ℳ ↦ f^*ℳ ⊗_𝒜 𝒩` of [Stacks, Tag 0FTE](https://stacks.math.columbia.edu/tag/0FTE) or the
pushforward of [Stacks, Tag 0FTS](https://stacks.math.columbia.edu/tag/0FTS) — over one ring.

## Main definitions

* `CategoryTheory.DGCategory.restrictScalars` is the restricted differential graded category.
* `CategoryTheory.DGCategory.DGFunctor.restrictScalars`,
  `CategoryTheory.DGCategory.ShiftAxiomB.restrictScalars` and
  `CategoryTheory.DGCategory.ConeSituation.restrictScalars` restrict a functor, axiom (B) and
  the cone situation.

## Main results

* `CategoryTheory.DGCategory.restrictScalars_K`, `...restrictScalars_Comp`,
  `...restrictScalars_cocycle` and `...onK_restrictScalars`: restriction of scalars changes
  nothing outside the module structure — the homotopy category, the category of complexes, the
  cocycles and the functor induced on homotopy categories are the ones of the original category,
  by reflexivity.
* `CategoryTheory.DGCategory.ShiftAxiomB.isStrictKShift_restrictScalars`: it preserves
  strictness of the translation, which is the hypothesis of Tag 0FQF.

## Implementation notes

**Only the `module` field moves.** `Obj`, `Hom`, `addCommGroup`, `d`, `comp` and `id` are the
fields of the original category unchanged, so every construction that does not mention the
module structure — `DGCategory.Comp`, `DGCategory.K`, `DGCategory.Cocycle`,
`DGCategory.Homotopic`, `DGCategory.homotopySetoid`, `DGCategory.GradedSplitShortExact`,
`DGCategory.IsDistinguishedTriangle` and the `CategoryTheory.Pretriangulated` instance built
from a cone situation — is *definitionally* the one of the original category.

The scalar-dependent axioms transport because a ring homomorphism preserves `-1` and powers:
the sign `(-1 : R₀) ^ k` of the Leibniz rule and of `toShift_d` acts through `σ` as the sign
`(-1 : R₁) ^ k` of the original category. The `R`-linear equivalences `toShift` of axiom (B)
restrict by `LinearEquiv.restrictScalars`, which keeps the underlying function, so the
connecting cocycle of an admissible short exact sequence is also unchanged.

## References

* [Stacks Project, Tag 09L5](https://stacks.math.columbia.edu/tag/09L5)
* [Stacks Project, Tag 09L6](https://stacks.math.columbia.edu/tag/09L6)
* [Stacks Project, Tag 09QJ](https://stacks.math.columbia.edu/tag/09QJ)
-/

@[expose] public section

namespace DGCategory

open CategoryTheory

universe u v w₀ w₁

variable {R₀ : Type w₀} [CommRing R₀] {R₁ : Type w₁} [CommRing R₁] (σ : R₀ →+* R₁)

/-- The restricted scalar action on a Hom group: `r` acts as `σ r`. -/
theorem restrictedSmul (A : DGCategory.{v, u} R₁) (x y : A.Obj) (n : ℤ) (r : R₀)
    (f : A.Hom x y n) :
    letI : Module R₀ (A.Hom x y n) :=
      @Module.compHom R₁ R₀ (A.Hom x y n) _ (A.addCommGroup x y n).toAddCommMonoid
        (A.module x y n) _ σ
    r • f = σ r • f :=
  rfl

/-- **A differential graded category over `R₁`, read over `R₀` along a ring homomorphism
`σ : R₀ →+* R₁`.** The objects, the Hom groups, the differential, the composition and the
identities are those of the original category; only the module structure on the Hom groups
changes, a scalar `r` acting as `σ r`. -/
@[instance_reducible]
def restrictScalars (A : DGCategory.{v, u} R₁) : DGCategory.{v, u} R₀ where
  Obj := A.Obj
  Hom := A.Hom
  addCommGroup := A.addCommGroup
  module x y n :=
    @Module.compHom R₁ R₀ (A.Hom x y n) _ (A.addCommGroup x y n).toAddCommMonoid
      (A.module x y n) _ σ
  d := A.d
  d_add := A.d_add
  d_smul r f := A.d_smul (σ r) f
  d_d := A.d_d
  comp := A.comp
  comp_add_left := A.comp_add_left
  comp_add_right := A.comp_add_right
  comp_smul_left h r g f := A.comp_smul_left h (σ r) g f
  comp_smul_right h r g f := A.comp_smul_right h (σ r) g f
  leibniz := fun {_x _y _z m n k} h g f => by
    have hs : σ ((-1 : R₀) ^ m.natAbs) = (-1 : R₁) ^ m.natAbs := by
      rw [map_pow, map_neg, map_one]
    change A.d (A.comp h g f) =
      A.comp (show m + 1 + n = k + 1 by lia) (A.d g) f +
        σ ((-1 : R₀) ^ m.natAbs) • A.comp (show m + (n + 1) = k + 1 by lia) g (A.d f)
    rw [hs]
    exact A.leibniz h g f
  assoc := A.assoc
  id := A.id
  id_comp := A.id_comp
  comp_id := A.comp_id
  d_id := A.d_id

/-- The objects of the restricted category are those of the original one. -/
@[simp]
theorem restrictScalars_Obj (A : DGCategory.{v, u} R₁) : (restrictScalars σ A).Obj = A.Obj :=
  rfl

/-- The Hom groups of the restricted category are those of the original one. -/
@[simp]
theorem restrictScalars_Hom (A : DGCategory.{v, u} R₁) : (restrictScalars σ A).Hom = A.Hom :=
  rfl

/-- Restriction of scalars does not change the category of complexes. -/
theorem restrictScalars_Comp (A : DGCategory.{v, u} R₁) :
    (restrictScalars σ A).Comp = A.Comp :=
  rfl

/-- Restriction of scalars does not change the homotopy category. -/
theorem restrictScalars_K (A : DGCategory.{v, u} R₁) : (restrictScalars σ A).K = A.K :=
  rfl

/-- Restriction of scalars does not change the cocycles. -/
theorem restrictScalars_cocycle (A : DGCategory.{v, u} R₁) (x y : A.Obj) :
    (restrictScalars σ A).Cocycle x y = A.Cocycle x y :=
  rfl

/-- **An `R₁`-linear equivalence between Hom groups, read as an `R₀`-linear equivalence.** The
underlying bijection is unchanged; linearity is the original one at the scalar `σ r`. -/
def restrictScalarsLinearEquiv (A : DGCategory.{v, u} R₁) {x y x' y' : A.Obj} {n n' : ℤ}
    (e : A.Hom x y n ≃ₗ[R₁] A.Hom x' y' n') :
    (restrictScalars σ A).Hom x y n ≃ₗ[R₀] (restrictScalars σ A).Hom x' y' n' where
  toFun := e
  invFun := e.symm
  left_inv := e.left_inv
  right_inv := e.right_inv
  map_add' := e.map_add
  map_smul' r f := e.map_smul (σ r) f

/-- The restricted linear equivalence is the original map. -/
@[simp]
theorem restrictScalarsLinearEquiv_apply (A : DGCategory.{v, u} R₁) {x y x' y' : A.Obj}
    {n n' : ℤ} (e : A.Hom x y n ≃ₗ[R₁] A.Hom x' y' n') (f : A.Hom x y n) :
    restrictScalarsLinearEquiv σ A e f = e f :=
  rfl

/-- **A functor of differential graded categories over `R₁`, read over `R₀`.** Nothing changes
but the linearity axiom, which is the original one at the scalar `σ r`. -/
def DGFunctor.restrictScalars {A B : DGCategory.{v, u} R₁} (F : DGFunctor A B) :
    DGFunctor (DGCategory.restrictScalars σ A) (DGCategory.restrictScalars σ B) where
  obj := F.obj
  map := F.map
  map_add := F.map_add
  map_smul r f := F.map_smul (σ r) f
  map_d := F.map_d
  map_comp := F.map_comp
  map_id := F.map_id

/-- The restricted functor induces the same functor on the homotopy categories. -/
@[simp]
theorem DGFunctor.onK_restrictScalars {A B : DGCategory.{v, u} R₁} (F : DGFunctor A B) :
    (F.restrictScalars σ).onK = F.onK :=
  rfl

/-- The restricted functor induces the same functor on the categories of complexes. -/
@[simp]
theorem DGFunctor.onComp_restrictScalars {A B : DGCategory.{v, u} R₁} (F : DGFunctor A B) :
    (F.restrictScalars σ).onComp = F.onComp :=
  rfl

/-- **Axiom (B) for a differential graded category over `R₁`, read over `R₀`.** The shift
functors and the two translations are unchanged; the identifications `Hom(x, y)[n] ≅
Hom(x, y[n])` are the same maps, `R₀`-linear through `σ`. -/
def ShiftAxiomB.restrictScalars {A : DGCategory.{v, u} R₁} (S : ShiftAxiomB A) :
    ShiftAxiomB (DGCategory.restrictScalars σ A) where
  shiftFunctor n := (S.shiftFunctor n).restrictScalars σ
  compShift := S.compShift
  kShift := S.kShift
  compShift_functor := S.compShift_functor
  kShift_functor := S.kShift_functor
  zero_obj := S.zero_obj
  add_obj := S.add_obj
  zero_map := S.zero_map
  add_map := S.add_map
  toShift n x y k := restrictScalarsLinearEquiv σ A (S.toShift n x y k)
  toShift_d := fun n x y k f => by
    have hs : σ ((-1 : R₀) ^ n.natAbs) = (-1 : R₁) ^ n.natAbs := by
      rw [map_pow, map_neg, map_one]
    change S.toShift n x y (k + 1) (A.d' (show k + n + 1 = k + 1 + n by lia) f) =
      σ ((-1 : R₀) ^ n.natAbs) • A.d (S.toShift n x y k f)
    rw [hs]
    exact S.toShift_d n x y k f
  toShift_comp_right := S.toShift_comp_right
  toShift_comp_left := fun n {x y z} {l m} g f => by
    have hs : σ ((-1 : R₀) ^ (n * m).natAbs) = (-1 : R₁) ^ (n * m).natAbs := by
      rw [map_pow, map_neg, map_one]
    change S.toShift n x z (m + l)
        (A.comp (show m + (l + n) = m + l + n by lia) g f) =
      σ ((-1 : R₀) ^ (n * m).natAbs) •
        A.comp (show m + l = m + l from rfl) ((S.shiftFunctor n).map g)
          (S.toShift n x y l f)
    rw [hs]
    exact S.toShift_comp_left n g f

/-- Restriction of scalars does not change the differential graded shift functors. -/
@[simp]
theorem ShiftAxiomB.shiftFunctor_restrictScalars {A : DGCategory.{v, u} R₁} (S : ShiftAxiomB A)
    (n : ℤ) :
    (S.restrictScalars σ).shiftFunctor n = (S.shiftFunctor n).restrictScalars σ :=
  rfl

/-- **Restriction of scalars preserves strictness of the translation.** The translation of the
homotopy category and its two coherence isomorphisms are literally those of the original axiom
(B) datum. -/
theorem ShiftAxiomB.isStrictKShift_restrictScalars {A : DGCategory.{v, u} R₁}
    {S : ShiftAxiomB A} (hS : S.IsStrictKShift) : (S.restrictScalars σ).IsStrictKShift :=
  hS

/-- **A differential graded binary biproduct over `R₁`, read over `R₀`.** Every field is an
object, a homogeneous morphism, a differential or a composite, so each is the one of the
original datum. -/
def BinaryBiproductData.restrictScalars {A : DGCategory.{v, u} R₁} {X Y : A.Obj}
    (B : BinaryBiproductData A X Y) :
    BinaryBiproductData (DGCategory.restrictScalars σ A) X Y :=
  ⟨B.pt, B.inl, B.inr, B.fst, B.snd, B.inl_closed, B.inr_closed, B.fst_closed, B.snd_closed,
    B.inl_fst, B.inr_fst, B.inl_snd, B.inr_snd, B.fst_inl_add_snd_inr⟩

/-- **Axiom (A) for a differential graded category over `R₁`, read over `R₀`.** -/
def DirectSumAxiomA.restrictScalars {A : DGCategory.{v, u} R₁} (S : DirectSumAxiomA A) :
    DirectSumAxiomA (DGCategory.restrictScalars σ A) where
  zero := S.zero
  zero_from := S.zero_from
  zero_to := S.zero_to
  binaryBiproduct x y := (S.binaryBiproduct x y).map (fun B => B.restrictScalars σ)

/-- **An admissible short exact sequence over `R₁`, read over `R₀`.** -/
def GradedSplitShortExact.restrictScalars {A : DGCategory.{v, u} R₁} {x y z : A.Obj}
    (E : GradedSplitShortExact (A := A) x y z) :
    GradedSplitShortExact (A := DGCategory.restrictScalars σ A) x y z :=
  ⟨E.a, E.b, E.π, E.s, E.π_a, E.b_s, E.π_s, E.a_π_add_s_b⟩

/-- The connecting cocycle is unchanged by restriction of scalars: the identification
`Hom(x, y)[1] ≅ Hom(x, y[1])` of the restricted axiom (B) datum is the original map. -/
@[simp]
theorem GradedSplitShortExact.connectingCocycle_restrictScalars {A : DGCategory.{v, u} R₁}
    {x y z : A.Obj} (S : ShiftAxiomB A) (E : GradedSplitShortExact (A := A) x y z) :
    GradedSplitShortExact.connectingCocycle (S.restrictScalars σ) (E.restrictScalars σ) =
      GradedSplitShortExact.connectingCocycle S E :=
  rfl

/-- **A cone situation on a differential graded category over `R₁`, read over `R₀`.** The cones,
their admissible short exact sequences and their connecting arrows are unchanged: none of them
mentions the module structure. -/
def ConeSituation.restrictScalars {A : DGCategory.{v, u} R₁} (S : ConeSituation A) :
    ConeSituation (DGCategory.restrictScalars σ A) where
  directSum := S.directSum.restrictScalars σ
  shift := S.shift.restrictScalars σ
  cone := S.cone
  coneSequence := fun {_x _y} f => (S.coneSequence f).restrictScalars σ
  cone_connecting := fun {_x _y} f => S.cone_connecting f

/-- Restriction of scalars of a cone situation restricts its axiom (B) datum. -/
@[simp]
theorem ConeSituation.shift_restrictScalars {A : DGCategory.{v, u} R₁} (S : ConeSituation A) :
    (S.restrictScalars σ).shift = S.shift.restrictScalars σ :=
  rfl

end DGCategory

end
