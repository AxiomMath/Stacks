module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleRankOne.SiteConverse
public import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.GradedForms
public import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.HomogeneousTwistUnit
public import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.TotalSpaceFiniteType
public import StacksFrontier.AlgebraicGeometry.TwistGenerator.Basic
public import StacksFrontier.RingTheory.DeRham.LaurentResidue
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The Laurent chart of a line bundle over a trivializing affine open

Let `f : X ⟶ S` be a morphism of schemes and `L` an invertible `𝒪_X`-module, and let `L^⋆ ⟶ X`
be the relative spectrum of the Laurent algebra `⨁_{n ∈ ℤ} L^{⊗ n}`. Over an affine open `U` of
`X` the functions on the inverse image of `U` in `L^⋆` are the sections
`⨁_{n ∈ ℤ} L^{⊗ n}(U)` of that algebra, by
`Stacks.LineBundle.Situation.laurentSectionsIso`. When `L` is moreover *trivial* over `U` those
sections are a Laurent polynomial algebra: a trivialization provides a section of `L^{⊗ 1}` and
one of `L^{⊗ -1}` over `U` multiplying to `1`, and the first of them becomes the coordinate `T`.

This file introduces that datum — a **Laurent chart** — and the comparison it induces,

`Γ(X, U)[T;T⁻¹] ⟶ Γ(L^⋆, π⁻¹U)`,

together with the homogeneity of the integer powers of the coordinate, which is what identifies
the weight grading of the Laurent polynomial algebra with the grading of the Laurent algebra by
the tensor degree.

A Laurent chart is exactly the Laurent-algebra form of the pair `s ∈ L(U)`, `s' ∈ L^{⊗ -1}(U)`
with `s' s = 1` that the proof of Tag 0FUF chooses over each member of a trivializing cover, and
`Stacks.LineBundle.Situation.LaurentChart.coordinate` is the unit of which
`StacksFrontier.RingTheory.DeRham.LaurentResidueTrivialization` proves the residue to be
independent.

## Main definitions

* `Stacks.LineBundle.Situation.laurentStructureHom`: the structure map
  `Γ(X, U) ⟶ Γ(L^⋆, π⁻¹U)` of the Laurent algebra sheaf on sections.
* `Stacks.LineBundle.Situation.LaurentChart`: **a Laurent chart of the line bundle over an open
  `U`** — a section of `L^{⊗ 1}` and a section of `L^{⊗ -1}` whose product is `1`.
* `Stacks.LineBundle.Situation.LaurentChart.coordinate`: **the coordinate of a chart**, its
  generator read as a unit of the sections of the Laurent algebra sheaf.
* `Stacks.LineBundle.Situation.LaurentChart.hom`: **the comparison
  `Γ(X, U)[T;T⁻¹] ⟶ Γ(L^⋆, π⁻¹U)`** of a chart, the evaluation of a Laurent polynomial at the
  coordinate.
* `Stacks.LineBundle.Situation.LaurentChart.coeffEquiv`: the degree-`n` coordinate of a chart,
  the inverse of scaling the degree-`n` generator.
* `Stacks.LineBundle.Situation.LaurentChart.invAddHom`: the left inverse of the comparison, the
  degreewise reading of a function on the inverse image of `U`.
* `Stacks.LineBundle.Situation.LaurentChart.sectionsRingEquiv` and
  `Stacks.LineBundle.Situation.LaurentChart.sectionsAlgEquiv`: **the affine local model of `L^⋆`
  over the base**, the comparison of a chart read into the sections of the structure sheaf of
  `L^⋆` and then over the functions on an affine open of `S`.

## Main results

* `Stacks.LineBundle.Situation.LaurentChart.hom_C` and
  `Stacks.LineBundle.Situation.LaurentChart.hom_T`: the comparison is the structure map on
  constants and carries `T n` to the `n`th power of the coordinate, which characterizes it.
* `Stacks.LineBundle.Situation.LaurentChart.exists_coordinate_zpow_eq`: **every integer power of
  the coordinate is homogeneous**, of the degree equal to its exponent: `t ^ n` is a section of
  `L^{⊗ n}` over `U`, viewed in the sections of the Laurent algebra sheaf.
* `Stacks.LineBundle.Situation.LaurentChart.ofTrivialization`: **a trivialization of `L` over
  `U` gives a Laurent chart over `U`.**
* `Stacks.LineBundle.Situation.exists_laurentChart_over_affine` and
  `Stacks.LineBundle.Situation.exists_laurentChart_cover_over_affine`: **the affine opens
  carrying a Laurent chart and mapping into an affine open of `S` cover `X`** — the cover over
  which the proof of Tag 0FUF computes, with the chart datum in place of the trivialization.
* `Stacks.LineBundle.Situation.laurentStructureHom_eq_incl`: **the structure map is the
  inclusion of degree zero.**
* `Stacks.LineBundle.Situation.laurentAlgebraSheafIncl_congr`: the degree of a homogeneous
  section may be rewritten along an equality of degrees.
* `Stacks.LineBundle.Situation.LaurentChart.exists_hom_C_mul_T_eq` and
  `Stacks.LineBundle.Situation.LaurentChart.exists_hom_eq_of_mem_grade`: **the comparison carries
  a Laurent polynomial homogeneous of weight `n` to a homogeneous section of degree `n`** — the
  degreewise half of the comparison, which is what transports a statement about one grading to
  the other.
* `Stacks.LineBundle.Situation.injective_laurentAlgebraSheafIncl`: **over an affine open a
  homogeneous section is determined by its image** in the sections of the Laurent algebra sheaf.
* `Stacks.LineBundle.Situation.laurentAlgebraSheafIncl_smul` and
  `Stacks.LineBundle.Situation.injective_laurentStructureHom`: the inclusion is linear over the
  structure map, and that map is injective over an affine open.
* `Stacks.LineBundle.Situation.LaurentChart.trivialization`: **a Laurent chart on an affine open
  is a trivialization of `L` there** — the converse of
  `Stacks.LineBundle.Situation.LaurentChart.ofTrivialization`, which is what lets the generator
  family of a chart be `Stacks.AlgebraicGeometry.TwistGenerator.genInt` of that trivialization
  rather than a second construction of the same sections.
* `Stacks.LineBundle.Situation.LaurentChart.coordinate_zpow_eq`: **the `n`th power of the
  coordinate of a chart is the image of the degree-`n` generator of its trivialization**, which
  is the characterization that generator family is used through.
* `Stacks.LineBundle.Situation.LaurentChart.bijective_smul_genInt`: **`L^{⊗ n}` is free of rank
  one on that generator, for every integer `n`** — the integer-indexed counterpart of
  `Stacks.AlgebraicGeometry.TwistGenerator.bijective_toSpanSingleton_gen`, which runs over `ℕ`.
* `Stacks.LineBundle.Situation.LaurentChart.surjective_hom` and
  `Stacks.LineBundle.Situation.LaurentChart.injective_hom`: the comparison of a chart over an
  affine open is surjective and injective.
* `Stacks.LineBundle.Situation.LaurentChart.homEquiv`: **over an affine open the comparison of a
  chart is an isomorphism `Γ(X, U)[T;T⁻¹] ≅ Γ(L^⋆, π⁻¹U)`** — the affine local model of the
  complement of the zero section that the proof of Tag 0FUF computes in.
* `Stacks.LineBundle.Situation.LaurentChart.hom_single`: the comparison carries the monomial
  `a Tⁿ` to the degree-`n` section `a · tⁿ`.
* `Stacks.LineBundle.Situation.LaurentChart.exists_mem_grade_hom_eq`: every homogeneous section
  of degree `n` is the image of a Laurent polynomial of weight `n`.
* `Stacks.LineBundle.Situation.LaurentChart.hom_image_grade_eq`: **the comparison matches the two
  gradings** — it carries the weight-`n` part of `Γ(X, U)[T;T⁻¹]` exactly onto the degree-`n`
  homogeneous sections of `Γ(L^⋆, π⁻¹U)`, for every integer `n`.
* `Stacks.LineBundle.Situation.laurentSectionsIso_hom_laurentStructureHom`: **the affine local
  model carries the structure map of the Laurent algebra sheaf to the pullback of functions
  along the projection `π : L^⋆ ⟶ X`.**
* `Stacks.LineBundle.Situation.isAffineOpen_laurentPreimage` and
  `Stacks.LineBundle.Situation.laurentPreimage_le_laurentToBase_preimage`: the inverse image in
  `L^⋆` of an affine open of `X` is affine, and lies over whatever open of `S` its image does.
* `Stacks.LineBundle.Situation.LaurentChart.sectionsRingEquiv_C_appLE`: **the comparison of a
  chart is a comparison over the base** — it carries the constant Laurent polynomial on a
  function pulled back from `S` to that same function pulled back to `L^⋆`.

## Implementation notes

The defining relation of a chart is stated in the *sections of the algebra sheaf*, as
`laurentAlgebraSheafIncl 1 U gen * laurentAlgebraSheafIncl (-1) U genInv = 1`, rather than as an
equality `(mul 1 (-1)).app _ gen genInv = one.eval _` of local sections of `L^{⊗ (1 + -1)}`.
The two say the same thing, but the second mentions the degree `1 + (-1)` and so would force the
degree cast to `0` into every consumer, which is the `HEq` plague the graded algebra of Tag 01CU
is otherwise free of here. In the sections ring there is no degree index at all, and the
symmetry of the relation is then ordinary commutativity of a commutative ring rather than the
heterogeneous `Stacks.LineBundle.Situation.laurentAlgebra_mul_comm`.

Only one half of the relation is a field: `t t' = 1` gives `t' t = 1` because the sections of an
algebra sheaf are a commutative ring.

**Two spellings of the functions on `U`, and why it matters which one a statement uses.** The
scalars acting on `L^{⊗ n}(U)` and on the ungraded realization are spelled
`D.X.ringCatSheaf.obj.obj (op U)`, a `RingCat`, while `Γ(X, U)` is a `CommRingCat`; the two
carriers are equal only after unfolding `forget₂`, that is, only at *default* transparency. So
instance synthesis and `rw`, which run at reducible transparency, both fail across them: a goal
holding a `Γ(X, U)`-typed scalar in a degree-zero position is reported as "not type-correct
under the `implicit` transparency level" and no rewrite fires. Every statement about scalars
here is therefore phrased at the `ringCatSheaf` spelling, and the passage to `Γ(X, U)` is made
only by *applying* such a lemma, never by rewriting with it — which is why
`Stacks.LineBundle.Situation.laurentStructureHom_eq_incl` is used through `Eq.trans` and
`congrArg` in the freeness proof rather than through `rw`.

A type *ascription* does not help: `(a : ↥(D.X.ringCatSheaf.obj.obj (op U)))` for
`a : ↥Γ(D.X, U)` elaborates but leaves the elaborated type alone, so a following `•` still fails
to synthesize `HSMul`. There is no coercion for the ascription to insert, the carriers being
already equal. What does move a term between the two spellings is an explicit identity
application, `id (α := ↥(D.X.ringCatSheaf.obj.obj (op U))) a`, whose type is the target spelling
by its own signature; that is the form used in
`Stacks.LineBundle.Situation.LaurentChart.coeffEquiv` and in the injectivity proof.

Injectivity is proved by exhibiting the left inverse
`Stacks.LineBundle.Situation.LaurentChart.invAddHom` and comparing the two maps on the monomials
through `LaurentPolynomial.induction_on'`. `Finsupp.addHom_ext` does not apply: it wants
`(α →₀ M) →+ N`, and `LaurentPolynomial R` is a semireducible definition for
`AddMonoidAlgebra R ℤ`, so the unifier does not see the `Finsupp` through it — the same
transparency obstruction again, in the shape of a failed instantiation rather than a failed
rewrite. The left inverse itself contains no degree arithmetic: the summand index of
`DirectSum.toAddMonoid` is used only as the exponent of `T`.

The homogeneity of the powers is proved by induction over `ℤ` through `Int.induction_on`, with
`Stacks.LineBundle.Situation.laurentAlgebraSheafIncl_mul` supplying the step in both directions;
the degrees add on the nose, so no transport along an equality of degrees occurs.

The inverse of a chart is not constructed by hand out of the dual of `L`: it is produced by
`Stacks.AlgebraicGeometry.TwistGenerator.bijective_mulBilinear_genOne`, which says that
multiplying by the degree-one generator of a trivialization is a bijection
`L^{⊗ d}(U) → L^{⊗ (d + 1)}(U)` for every *integer* `d`, so the case `d = -1` produces the
section of `L^{⊗ -1}` pairing with the generator to `1`. That is why no compatibility of
`Stacks.SheafOfModules.TensorPower.overTensorPowerUnitIso` with the coherent multiplication is
needed, which is as well, since it is not available: the trivializations of the separate tensor
powers are not known to multiply, as recorded in
`StacksFrontier/AlgebraicGeometry/GradedAlgebraTwist/TrivializedSections.lean:70`.

**How the base ring enters, and why no diagram chase is needed.** Making the comparison an
isomorphism of algebras over `Γ(S, V)` needs one fact beyond the comparison itself: that the
affine local model `Stacks.LineBundle.Situation.laurentSectionsIso` carries the structure map of
the Laurent algebra sheaf to the pullback of functions along `π : L^⋆ ⟶ X`. That is not proved
here by unfolding the chart of Tag 01LP; it is
`Stacks.RelativeSpec.toBase_app` composed with `Stacks.RelativeSpec.universalAlgebraMap_app`,
whose right-hand side is the very composite that `laurentSectionsIso` is defined to be, so the
identification is the symmetry of an existing statement. The passage to `Γ(S, V)` is then
`Scheme.Hom.appLE_comp_appLE` at the factorization `L^⋆ ⟶ X ⟶ S` of
`Stacks.LineBundle.Situation.laurentToBase`.

Both steps are made by *applying* lemmas rather than by rewriting with them.
`Stacks.LineBundle.Situation.laurentSpectrumToBase` is a `def` and not reducibly the `toBase`
field of the glued spectrum it unfolds to, so a `rw` with `Stacks.RelativeSpec.toBase_app`
reports the target as "not type-correct under the `implicit` transparency level" — the same
transparency obstruction as the two spellings of the functions on `U` above. A term-level
`congrArg` crosses it without complaint.

## References

* [Stacks Project, Tag 0FUF](https://stacks.math.columbia.edu/tag/0FUF), whose proof works over
  a trivializing affine open, where the chart of this file is available
* [Stacks Project, Tag 0FUH](https://stacks.math.columbia.edu/tag/0FUH)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU), the integer tensor
  powers and their coherent multiplication
* [Stacks Project, Tag 01LP](https://stacks.math.columbia.edu/tag/01LP)
-/

open CategoryTheory TopologicalSpace AlgebraicGeometry Opposite

universe u v₁ u₁

@[expose] public noncomputable section

namespace Stacks.SheafOfModules

/-- **The section a recognition isomorphism sends to `1` is the section it was built from.** The
isomorphism `Stacks.SheafOfModules.overIsoUnitOfBijectiveSmul` of a generating section `s` is
the morphism corresponding to the family of restrictions of `s`, whose component is scaling that
restriction, so at the terminal object of the slice site it carries `1` to `1 • s`. -/
theorem generator_overIsoUnitOfBijectiveSmul {C : Type u₁} [Category.{v₁} C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}} (L : _root_.SheafOfModules.{u} R)
    (U : C) (s : L.val.obj (op U))
    (hs : ∀ (V : C) (f : V ⟶ U),
      Function.Bijective (fun r : R.obj.obj (op V) => r • L.val.map f.op s)) :
    ((overIsoUnitOfBijectiveSmul L U s hs).inv.val.app (op (Over.mk (𝟙 U)))).hom
        (1 : (R.over U).obj.obj (op (Over.mk (𝟙 U)))) = s := by
  change (1 : (R.over U).obj.obj (op (Over.mk (𝟙 U)))) •
      (show (L.over U).val.obj (op (Over.mk (𝟙 U))) from L.val.map (𝟙 U).op s) = s
  rw [one_smul, op_id, PresheafOfModules.map_id]
  rfl

end Stacks.SheafOfModules

namespace Stacks.LineBundle

variable (D : Situation.{u})

/-- The structure map `Γ(X, U) ⟶ Γ(L^⋆, π⁻¹U)` of the Laurent algebra sheaf of the line bundle,
read on the sections over an open `U` of `X`. -/
def Situation.laurentStructureHom (U : D.X.Opens) :
    Γ(D.X, U) →+* Stacks.RelativeSpec.AlgebraSheaf.sections D.laurentAlgebraSheaf U :=
  (D.laurentAlgebraSheaf.hom.hom.app (op U)).hom

/-- **The structure map of the Laurent algebra sheaf is the inclusion of degree zero.** Degree
zero of the Laurent algebra is the structure sheaf, by
`Stacks.LineBundle.Situation.laurentPieceZeroIso`, and the structure map of an ungraded
realization is `r ↦ r • 1`; so on sections it carries `r` to the degree-zero homogeneous section
`r`. This is what lets a statement about the grading of the sections be read off the constants of
a Laurent polynomial. -/
theorem Situation.laurentStructureHom_eq_incl (U : D.X.Opens) (r : Γ(D.X, U)) :
    D.laurentStructureHom U r =
      D.laurentAlgebraSheafIncl 0 U (show (D.tensorPower 0).val.obj (op U) from r) := by
  refine congrArg (Stacks.RelativeSpec.ungradedCommUnit D.X D.laurentAlgebra
    D.laurentAlgebra_mul_comm U).hom ?_
  have key : ∀ s : D.X.ringCatSheaf.obj.obj (op U),
      Stacks.GradedAlgebra.structureMap D.laurentAlgebra.toPresheafGradedAlgebra (op U) s =
        D.laurentAlgebra.toPresheafGradedAlgebra.incl 0
          (show (D.tensorPower 0).val.obj (op U) from s) := by
    intro s
    change s • (1 : D.laurentAlgebra.toPresheafGradedAlgebra.Total (op U)) = _
    rw [Stacks.GradedAlgebra.one_eq_incl, ← Stacks.GradedAlgebra.incl_smul]
    exact congrArg (D.laurentAlgebra.toPresheafGradedAlgebra.incl 0) (mul_one s)
  exact key r

/-- **The degree of a homogeneous section may be rewritten along an equality of degrees.** For a
free variable `n` the integers `0 + n` and `n` are equal but not definitionally so, since
`Int.add` has to case on its argument, and the homogeneous sections of the two degrees are
therefore different types; this transports between them. -/
theorem Situation.laurentAlgebraSheafIncl_congr {n m : ℤ} (h : n = m) (U : D.X.Opens)
    (x : (D.tensorPower n).val.obj (op U)) :
    D.laurentAlgebraSheafIncl n U x = D.laurentAlgebraSheafIncl m U (h ▸ x) := by
  subst h
  rfl

/-- **A Laurent chart of the line bundle over an open `U`**: a local section of `L^{⊗ 1}` and a
local section of `L^{⊗ -1}` whose product in the sections of the Laurent algebra sheaf is `1`.
This is the Laurent-algebra form of the pair `s ∈ L(U)`, `s' ∈ L^{⊗ -1}(U)` with `s' s = 1` that
the proof of Tag 0FUF picks over a trivializing open. -/
structure Situation.LaurentChart (U : D.X.Opens) where
  /-- The generator of the chart, a local section of `L^{⊗ 1}`. -/
  gen : (D.tensorPower 1).val.obj (op U)
  /-- Its inverse, a local section of `L^{⊗ -1}`. -/
  genInv : (D.tensorPower (-1)).val.obj (op U)
  /-- The generator and its inverse multiply to `1`. -/
  mul_eq_one :
    D.laurentAlgebraSheafIncl 1 U gen * D.laurentAlgebraSheafIncl (-1) U genInv = 1

namespace Situation.LaurentChart

variable {D} {U : D.X.Opens} (c : D.LaurentChart U)

/-- **The coordinate of a Laurent chart**: its generator, read as a unit of the sections of the
Laurent algebra sheaf over `U`. This is the `s` of the proof of Tag 0FUF, and the weight-one unit
whose `d log` the residue is read against. -/
def coordinate : (Stacks.RelativeSpec.AlgebraSheaf.sections D.laurentAlgebraSheaf U)ˣ where
  val := D.laurentAlgebraSheafIncl 1 U c.gen
  inv := D.laurentAlgebraSheafIncl (-1) U c.genInv
  val_inv := c.mul_eq_one
  inv_val := (mul_comm _ _).trans c.mul_eq_one

/-- The coordinate of a Laurent chart is the generator of the chart in degree one. -/
@[simp]
theorem coordinate_val :
    (c.coordinate : Stacks.RelativeSpec.AlgebraSheaf.sections D.laurentAlgebraSheaf U) =
      D.laurentAlgebraSheafIncl 1 U c.gen :=
  rfl

/-- The inverse of the coordinate of a Laurent chart is the inverse generator of the chart in
degree `-1`. -/
@[simp]
theorem coordinate_inv :
    (↑c.coordinate⁻¹ : Stacks.RelativeSpec.AlgebraSheaf.sections D.laurentAlgebraSheaf U) =
      D.laurentAlgebraSheafIncl (-1) U c.genInv :=
  rfl

/-- **The comparison `Γ(X, U)[T;T⁻¹] ⟶ Γ(L^⋆, π⁻¹U)` of a Laurent chart**: the evaluation of a
Laurent polynomial at the coordinate of the chart, over the structure map of the Laurent algebra
sheaf. -/
def hom : LaurentPolynomial ↥Γ(D.X, U) →+*
    Stacks.RelativeSpec.AlgebraSheaf.sections D.laurentAlgebraSheaf U :=
  LaurentPolynomial.eval₂ (D.laurentStructureHom U) c.coordinate

/-- The comparison of a Laurent chart sends a constant Laurent polynomial `C a` to the image of
`a` under the structure map of the Laurent algebra sheaf. -/
@[simp]
theorem hom_C (a : Γ(D.X, U)) :
    c.hom (LaurentPolynomial.C a) = D.laurentStructureHom U a :=
  LaurentPolynomial.eval₂_C _ _ a

/-- The comparison of a Laurent chart sends the monomial `T n` to the `n`-th power of the
coordinate of the chart. -/
@[simp]
theorem hom_T (n : ℤ) :
    c.hom (LaurentPolynomial.T n) = ((c.coordinate ^ n : _ˣ) :
      Stacks.RelativeSpec.AlgebraSheaf.sections D.laurentAlgebraSheaf U) :=
  LaurentPolynomial.eval₂_T _ _ n

/-- **Every integer power of the coordinate of a Laurent chart is homogeneous of the degree equal
to its exponent**: `t ^ n` is the image of a local section of `L^{⊗ n}` over `U`. This is what
matches the weight grading of `Γ(X, U)[T;T⁻¹]` with the grading of the Laurent algebra by tensor
degree. -/
theorem exists_coordinate_zpow_eq (n : ℤ) :
    ∃ x : (D.tensorPower n).val.obj (op U),
      ((c.coordinate ^ n : _ˣ) :
          Stacks.RelativeSpec.AlgebraSheaf.sections D.laurentAlgebraSheaf U) =
        D.laurentAlgebraSheafIncl n U x := by
  induction n using Int.induction_on with
  | zero =>
      refine ⟨D.laurentAlgebra.one.eval (op U), ?_⟩
      rw [zpow_zero, Units.val_one]
      exact (D.laurentAlgebraSheafIncl_one U).symm
  | succ k hk =>
      obtain ⟨x, hx⟩ := hk
      refine ⟨(D.laurentAlgebra.mul (k : ℤ) 1).app (op U) x c.gen, ?_⟩
      have h : ((c.coordinate ^ ((k : ℤ) + 1) : _ˣ) :
            Stacks.RelativeSpec.AlgebraSheaf.sections D.laurentAlgebraSheaf U) =
          D.laurentAlgebraSheafIncl ((k : ℤ) + 1) U
            ((D.laurentAlgebra.mul (k : ℤ) 1).app (op U) x c.gen) := by
        rw [← D.laurentAlgebraSheafIncl_mul, ← hx, ← c.coordinate_val, ← Units.val_mul,
          ← zpow_add_one]
      exact h
  | pred k hk =>
      obtain ⟨x, hx⟩ := hk
      refine ⟨(D.laurentAlgebra.mul (-k : ℤ) (-1)).app (op U) x c.genInv, ?_⟩
      have h : ((c.coordinate ^ ((-k : ℤ) + (-1)) : _ˣ) :
            Stacks.RelativeSpec.AlgebraSheaf.sections D.laurentAlgebraSheaf U) =
          D.laurentAlgebraSheafIncl ((-k : ℤ) + (-1)) U
            ((D.laurentAlgebra.mul (-k : ℤ) (-1)).app (op U) x c.genInv) := by
        rw [← D.laurentAlgebraSheafIncl_mul, ← hx, ← c.coordinate_inv, ← zpow_neg_one,
          ← Units.val_mul, ← zpow_add]
      exact h

/-- **The comparison of a Laurent chart carries a monomial of weight `n` to a homogeneous
section of degree `n`**: `a Tⁿ` goes to a section of `L^{⊗ n}` over `U`, viewed in the sections
of the Laurent algebra sheaf. This is the degreewise half of the comparison — it matches the
weight grading of `Γ(X, U)[T;T⁻¹]` with the grading of the sections by tensor degree, and so is
what a statement about one grading transports to the other along. -/
theorem exists_hom_C_mul_T_eq (n : ℤ) (a : Γ(D.X, U)) :
    ∃ x : (D.tensorPower n).val.obj (op U),
      c.hom (LaurentPolynomial.C a * LaurentPolynomial.T n) =
        D.laurentAlgebraSheafIncl n U x := by
  obtain ⟨g, hg⟩ := c.exists_coordinate_zpow_eq n
  refine ⟨zero_add n ▸ (D.laurentAlgebra.mul 0 n).app (op U)
    (show (D.tensorPower 0).val.obj (op U) from a) g, ?_⟩
  have h : c.hom (LaurentPolynomial.C a * LaurentPolynomial.T n) =
      D.laurentAlgebraSheafIncl ((0 : ℤ) + n) U
        ((D.laurentAlgebra.mul 0 n).app (op U)
          (show (D.tensorPower 0).val.obj (op U) from a) g) := by
    rw [map_mul, hom_C, hom_T, hg, D.laurentStructureHom_eq_incl,
      D.laurentAlgebraSheafIncl_mul]
  exact h.trans (D.laurentAlgebraSheafIncl_congr (zero_add n) U _)

/-- **The comparison of a Laurent chart carries a Laurent polynomial homogeneous of weight `n`
to a homogeneous section of degree `n`.** A homogeneous Laurent polynomial is a monomial, so
this is `Stacks.LineBundle.Situation.LaurentChart.exists_hom_C_mul_T_eq`; it is stated against
`AddMonoidAlgebra.grade`, which is the grading underlying
`LaurentDeRham.weightGrading`, so that no base ring has to be fixed. -/
theorem exists_hom_eq_of_mem_grade {n : ℤ} {q : LaurentPolynomial ↥Γ(D.X, U)}
    (hq : q ∈ AddMonoidAlgebra.grade ↥Γ(D.X, U) n) :
    ∃ x : (D.tensorPower n).val.obj (op U), c.hom q = D.laurentAlgebraSheafIncl n U x := by
  obtain ⟨a, ha⟩ := (AddMonoidAlgebra.mem_grade_iff' ↥Γ(D.X, U) n q).mp hq
  obtain ⟨x, hx⟩ := c.exists_hom_C_mul_T_eq n a
  refine ⟨x, ?_⟩
  rw [← ha, AddMonoidAlgebra.lsingle_apply, LaurentPolynomial.single_eq_C_mul_T]
  exact hx

end Situation.LaurentChart

/-- **A trivialization of the line bundle over an open gives a Laurent chart there.** The
generator is the degree-one generator
`Stacks.AlgebraicGeometry.TwistGenerator.genOne` of the trivialization, and its inverse exists
because multiplying by that generator is a bijection `L^{⊗ -1}(U) → L^{⊗ 0}(U) = 𝒪_X(U)`. -/
def Situation.LaurentChart.ofTrivialization {D : Situation.{u}} {U : D.X.Opens}
    (e : D.L.over U ≅ SheafOfModules.unit (D.X.ringCatSheaf.over U)) :
    D.LaurentChart U :=
  have hbij := Stacks.AlgebraicGeometry.TwistGenerator.bijective_mulBilinear_genOne D.L e (-1)
  have hsurj := hbij.2
    (show (D.tensorPower ((-1 : ℤ) + 1)).val.obj (op U) from (1 : Γ(D.X, U)))
  { gen := Stacks.AlgebraicGeometry.TwistGenerator.genOne D.L e
    genInv := hsurj.choose
    mul_eq_one := by
      have hs : (Stacks.SheafOfModules.TensorPower.mulBilinear D.X.sheaf.obj
            D.X.ringCatSheaf.property D.L (-1) 1).app (op U) hsurj.choose
            (Stacks.AlgebraicGeometry.TwistGenerator.genOne D.L e) =
          (1 : Γ(D.X, U)) :=
        hsurj.choose_spec
      have hmul := D.laurentAlgebraSheafIncl_mul (-1) 1 U hsurj.choose
        (Stacks.AlgebraicGeometry.TwistGenerator.genOne D.L e)
      rw [mul_comm, hmul]
      exact (congrArg (fun y : (D.tensorPower ((-1 : ℤ) + 1)).val.obj (op U) =>
        D.laurentAlgebraSheafIncl ((-1 : ℤ) + 1) U y) hs).trans
          (D.laurentAlgebraSheafIncl_one U) }

/-- **Every point of `X` has an affine open neighbourhood carrying a Laurent chart and mapping
into an affine open of `S`.** This is
`Stacks.LineBundle.Situation.exists_trivializing_affineOpen_over_affine` with the trivialization
converted into the chart datum the local computation of Tag 0FUF uses. -/
theorem Situation.exists_laurentChart_over_affine (x : D.X) :
    ∃ (U : D.X.affineOpens) (V : D.S.affineOpens), x ∈ U.1 ∧ U.1 ≤ D.f ⁻¹ᵁ V.1 ∧
      Nonempty (D.LaurentChart U.1) := by
  obtain ⟨U, V, hxU, hUV, ⟨e⟩⟩ := D.exists_trivializing_affineOpen_over_affine x
  exact ⟨U, V, hxU, hUV, ⟨Situation.LaurentChart.ofTrivialization e⟩⟩

/-- **The affine opens which carry a Laurent chart and map into an affine open of `S` cover
`X`.** This is the cover over which the proof of Tag 0FUF computes. -/
theorem Situation.exists_laurentChart_cover_over_affine :
    ∃ (I : Type u) (U : I → D.X.affineOpens) (V : I → D.S.affineOpens),
      (⨆ i, (U i).1) = ⊤ ∧ (∀ i, (U i).1 ≤ D.f ⁻¹ᵁ (V i).1) ∧
        ∀ i, Nonempty (D.LaurentChart (U i).1) := by
  obtain ⟨I, U, V, hcov, hUV, he⟩ := D.exists_affine_trivializing_cover_over_affine
  exact ⟨I, U, V, hcov, hUV,
    fun i => ⟨Situation.LaurentChart.ofTrivialization (he i).some⟩⟩

/-! ### Freeness of the homogeneous sections in every integer degree -/

/-- Rewriting the degree of a homogeneous section along an equality of degrees, with the result
type named so that the cast has a motive. -/
def Situation.tensorPowerCongr {n m : ℤ} (h : n = m) (U : D.X.Opens)
    (x : (D.tensorPower n).val.obj (op U)) : (D.tensorPower m).val.obj (op U) :=
  h ▸ x

/-- **A homogeneous section is determined by its image in the sections of the Laurent algebra
sheaf**, over an affine open: there the sheafification unit of the ungraded realization is
bijective, and the inclusion of a summand of a direct sum is injective. -/
theorem Situation.injective_laurentAlgebraSheafIncl {U : D.X.Opens} (hU : IsAffineOpen U)
    (n : ℤ) : Function.Injective (D.laurentAlgebraSheafIncl n U) := fun _ _ h =>
  DirectSum.of_injective
    (β := fun k : ℤ => ((D.laurentAlgebra.piece k).val.obj (op U) : Type u)) n
    ((Stacks.RelativeSpec.bijective_ungradedCommUnit_of_isAffineOpen D.X D.laurentAlgebra
      D.laurentAlgebra_mul_comm hU).1 h)

/-- **The inclusion of a homogeneous section is linear over the structure map**: scaling a
section of `L^{⊗ n}` is multiplying its image by the image of the scalar. -/
theorem Situation.laurentAlgebraSheafIncl_smul (U : D.X.Opens) (n : ℤ)
    (a : D.X.ringCatSheaf.obj.obj (op U)) (y : (D.tensorPower n).val.obj (op U)) :
    D.laurentAlgebraSheafIncl n U (a • y) =
      D.laurentStructureHom U a * D.laurentAlgebraSheafIncl n U y := by
  have h1 : Stacks.GradedAlgebra.structureMap D.laurentAlgebra.toPresheafGradedAlgebra (op U) a *
        D.laurentAlgebra.toPresheafGradedAlgebra.incl n y =
      a • D.laurentAlgebra.toPresheafGradedAlgebra.incl n y := by
    change a • (1 : D.laurentAlgebra.toPresheafGradedAlgebra.Total (op U)) * _ = _
    rw [Stacks.GradedAlgebra.smul_mul_eq, one_mul]
  refine (congrArg (Stacks.RelativeSpec.ungradedCommUnit D.X D.laurentAlgebra
    D.laurentAlgebra_mul_comm U).hom ?_).trans (map_mul _ _ _)
  exact (D.laurentAlgebra.toPresheafGradedAlgebra.incl_smul n a y).trans h1.symm

/-- **The structure map is injective over an affine open**, being the inclusion of degree
zero. -/
theorem Situation.injective_laurentStructureHom {U : D.X.Opens} (hU : IsAffineOpen U) :
    Function.Injective (D.laurentStructureHom U) := fun a b h =>
  D.injective_laurentAlgebraSheafIncl hU 0
    (((D.laurentStructureHom_eq_incl U a).symm.trans h).trans
      (D.laurentStructureHom_eq_incl U b))

namespace Situation.LaurentChart

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose

variable {D} {U : D.X.Opens} (c : D.LaurentChart U)

/-- **The defining relation of a chart at the level of local sections, over an affine open and
over every smaller open.** The relation of a chart is stated in the sections of the algebra
sheaf, where the inclusion of a degree is injective only over an affine open; there it is
therefore equivalent to the equality of local sections of `L^{⊗ (1 + -1)}`, and that equality,
being an equality of sections, restricts along any inclusion of opens. -/
theorem mul_res_eq_one (hU : IsAffineOpen U) {V : D.X.Opens} (f : V ⟶ U) :
    (D.laurentAlgebra.mul 1 (-1)).app (op V)
        ((D.tensorPower 1).val.map f.op c.gen)
        ((D.tensorPower (-1)).val.map f.op c.genInv) =
      (show (D.tensorPower ((1 : ℤ) + (-1))).val.obj (op V) from (1 : Γ(D.X, V))) := by
  have hU1 : (D.laurentAlgebra.mul 1 (-1)).app (op U) c.gen c.genInv =
      (show (D.tensorPower ((1 : ℤ) + (-1))).val.obj (op U) from (1 : Γ(D.X, U))) := by
    refine D.injective_laurentAlgebraSheafIncl hU ((1 : ℤ) + (-1)) ?_
    refine (D.laurentAlgebraSheafIncl_mul 1 (-1) U c.gen c.genInv).symm.trans ?_
    exact c.mul_eq_one.trans (D.laurentAlgebraSheafIncl_one U).symm
  refine ((D.laurentAlgebra.mul 1 (-1)).naturality f.op c.gen c.genInv).symm.trans ?_
  refine Eq.trans (congrArg ((D.tensorPower ((1 : ℤ) + (-1))).val.map f.op) hU1) ?_
  exact (Stacks.SheafOfModules.TensorPower.oneSection D.X.sheaf.obj
    D.X.ringCatSheaf.property D.L).property f.op

/-- **The generator of a chart on an affine open generates `L^{⊗ 1}` over every smaller open.**
Multiplying by the restricted generator is injective because multiplying the result by the
restricted inverse generator returns the scalar, and surjective because multiplying a section by
the restricted inverse generator produces the scalar it is the multiple of — both by
`Stacks.LineBundle.Situation.LaurentChart.mul_res_eq_one` and the associativity and unit laws of
Tag 01CU. Every degree occurring is a literal, so none of the heterogeneous equalities of Tag
01CU needs a reindexing. -/
theorem bijective_smul_res_gen (hU : IsAffineOpen U) (V : D.X.Opens) (f : V ⟶ U) :
    Function.Bijective (fun r : D.X.ringCatSheaf.obj.obj (op V) =>
      r • (D.tensorPower 1).val.map f.op c.gen) := by
  have hone := c.mul_res_eq_one hU f
  have hone' : (D.laurentAlgebra.mul (-1) 1).app (op V)
        ((D.tensorPower (-1)).val.map f.op c.genInv)
        ((D.tensorPower 1).val.map f.op c.gen) =
      (show (D.tensorPower ((-1 : ℤ) + 1)).val.obj (op V) from (1 : Γ(D.X, V))) :=
    eq_of_heq (HEq.trans (Stacks.SheafOfModules.TensorPower.mulBilinear_comm D.X.sheaf.obj
      D.X.ringCatSheaf.property D.L (-1) 1 (op V) _ _) (heq_of_eq hone))
  have hk : ∀ s : D.X.ringCatSheaf.obj.obj (op V),
      (D.laurentAlgebra.mul 1 (-1)).app (op V)
          (s • (D.tensorPower 1).val.map f.op c.gen)
          ((D.tensorPower (-1)).val.map f.op c.genInv) = s := fun s =>
    ((D.laurentAlgebra.mul 1 (-1)).map_smul_left (op V) s _ _).trans
      ((congrArg (fun z => s • z) hone).trans (mul_one s))
  have hmul01 : ∀ (r : ↥(D.X.ringCatSheaf.obj.obj (op V)))
      (z : (D.tensorPower 1).val.obj (op V)),
      (D.laurentAlgebra.mul 0 1).app (op V)
          (show (D.tensorPower (0 : ℤ)).val.obj (op V) from r) z = r • z := by
    intro r z
    refine Eq.trans (congrArg (fun w => (D.laurentAlgebra.mul 0 1).app (op V) w z)
      (show (show (D.tensorPower (0 : ℤ)).val.obj (op V) from r)
          = r • (show (D.tensorPower (0 : ℤ)).val.obj (op V) from (1 : Γ(D.X, V)))
        from (mul_one r).symm)) ?_
    refine ((D.laurentAlgebra.mul 0 1).map_smul_left (op V) r _ z).trans ?_
    exact congrArg (fun w => r • w) (eq_of_heq
      (Stacks.SheafOfModules.TensorPower.mulBilinear_one_mul D.X.sheaf.obj
        D.X.ringCatSheaf.property D.L 1 (op V) z))
  refine ⟨fun r r' hrr => (hk r).symm.trans ?_, fun y => ?_⟩
  · refine Eq.trans (congrArg (fun z => (D.laurentAlgebra.mul 1 (-1)).app (op V) z
      ((D.tensorPower (-1)).val.map f.op c.genInv)) hrr) (hk r')
  · refine ⟨(D.laurentAlgebra.mul 1 (-1)).app (op V) y
      ((D.tensorPower (-1)).val.map f.op c.genInv), ?_⟩
    refine (hmul01 _ ((D.tensorPower 1).val.map f.op c.gen)).symm.trans ?_
    refine Eq.trans (eq_of_heq (Stacks.SheafOfModules.TensorPower.mulBilinear_assoc
      D.X.sheaf.obj D.X.ringCatSheaf.property D.L 1 (-1) 1 (op V) y
      ((D.tensorPower (-1)).val.map f.op c.genInv)
      ((D.tensorPower 1).val.map f.op c.gen))) ?_
    refine Eq.trans (congrArg ((D.laurentAlgebra.mul 1 0).app (op V) y) hone') ?_
    exact eq_of_heq (Stacks.SheafOfModules.TensorPower.mulBilinear_mul_one D.X.sheaf.obj
      D.X.ringCatSheaf.property D.L 1 (op V) y)

/-- **A chart on an affine open trivializes `L^{⊗ 1}` there**, its generator being a basis of
one element by `Stacks.LineBundle.Situation.LaurentChart.bijective_smul_res_gen`. -/
def powOneTriv (hU : IsAffineOpen U) :
    (D.tensorPower 1).over U ≅ SheafOfModules.unit (D.X.ringCatSheaf.over U) :=
  Stacks.SheafOfModules.overIsoUnitOfBijectiveSmul (D.tensorPower 1) U c.gen
    (c.bijective_smul_res_gen hU)

/-- **A Laurent chart on an affine open is a trivialization of the line bundle there.** This is
the converse of `Stacks.LineBundle.Situation.LaurentChart.ofTrivialization`, and it is what lets
the generator family of a chart be the generator family
`Stacks.AlgebraicGeometry.TwistGenerator.genInt` of a trivialization rather than a second
construction of the same sections. The trivialization of `L^{⊗ 1}` is transported to one of `L`
along the comparison `L^{⊗ 1} ≅ L` of Tag 01CU. -/
def trivialization (hU : IsAffineOpen U) :
    D.L.over U ≅ SheafOfModules.unit (D.X.ringCatSheaf.over U) :=
  ((SheafOfModules.overFunctor D.X.ringCatSheaf U).mapIso
    (Stacks.SheafOfModules.TensorPower.tensorPowerOneIso D.X.sheaf.obj
      D.X.ringCatSheaf.property D.L)).symm ≪≫ c.powOneTriv hU

/-- The section of `L^{⊗ 1}` that the trivialization of a chart sends to `1` is the generator of
the chart. -/
theorem generator_powOneTriv (hU : IsAffineOpen U) :
    Stacks.SheafOfModules.TensorGenerator.generator D.X.sheaf.obj D.X.ringCatSheaf.property U
      (D.tensorPower 1) (c.powOneTriv hU) = c.gen :=
  Stacks.SheafOfModules.generator_overIsoUnitOfBijectiveSmul (D.tensorPower 1) U c.gen
    (c.bijective_smul_res_gen hU)

/-- **The degree-one generator of the trivialization of a chart is the generator of the
chart.** The transport along `L^{⊗ 1} ≅ L` is undone by the transport back which
`Stacks.AlgebraicGeometry.TwistGenerator.genOne` performs, so no comparison survives. -/
theorem genOne_trivialization (hU : IsAffineOpen U) :
    Stacks.AlgebraicGeometry.TwistGenerator.genOne D.L (c.trivialization hU) = c.gen := by
  refine Eq.trans (congrArg
    (fun y => (Stacks.SheafOfModules.TensorPower.tensorPowerOneIso D.X.sheaf.obj
        D.X.ringCatSheaf.property D.L).inv.val.app (op U)
      (((SheafOfModules.overFunctor D.X.ringCatSheaf U).mapIso
          (Stacks.SheafOfModules.TensorPower.tensorPowerOneIso D.X.sheaf.obj
            D.X.ringCatSheaf.property D.L)).hom.val.app (op (Over.mk (𝟙 U))) y))
    (c.generator_powOneTriv hU)) ?_
  exact congrArg (fun φ : D.tensorPower 1 ⟶ D.tensorPower 1 => φ.val.app (op U) c.gen)
    ((Stacks.SheafOfModules.TensorPower.tensorPowerOneIso D.X.sheaf.obj
      D.X.ringCatSheaf.property D.L).hom_inv_id)

/-- **The coordinate of a chart on an affine open is the unit of its trivialization.** A unit of
a monoid is determined by its value, so this is
`Stacks.LineBundle.Situation.LaurentChart.genOne_trivialization`. -/
theorem coordinate_eq_laurentGenUnit (hU : IsAffineOpen U) :
    c.coordinate = D.laurentGenUnit (c.trivialization hU) :=
  Units.ext (congrArg (D.laurentAlgebraSheafIncl 1 U) (c.genOne_trivialization hU).symm)

/-- **Every integer power of the coordinate of a chart on an affine open is the image of the
generator of that degree of the chart's trivialization.** This is the characterization the
generator family of a chart is used through: the family is
`Stacks.AlgebraicGeometry.TwistGenerator.genInt` of the trivialization
`Stacks.LineBundle.Situation.LaurentChart.trivialization`, so it is cast-free and choice-free,
and over an affine open it is the unique section with this image, by
`Stacks.LineBundle.Situation.injective_laurentAlgebraSheafIncl`. -/
theorem coordinate_zpow_eq (hU : IsAffineOpen U) (n : ℤ) :
    ((c.coordinate ^ n : _ˣ) :
        Stacks.RelativeSpec.AlgebraSheaf.sections D.laurentAlgebraSheaf U) =
      D.laurentAlgebraSheafIncl n U
        (Stacks.AlgebraicGeometry.TwistGenerator.genInt D.L (c.trivialization hU) n) :=
  (congrArg (fun u => ((u ^ n : _ˣ) :
      Stacks.RelativeSpec.AlgebraSheaf.sections D.laurentAlgebraSheaf U))
    (c.coordinate_eq_laurentGenUnit hU)).trans
      (D.laurentGenUnit_zpow (c.trivialization hU) n)

/-- Scaling the degree-`n` generator by `a` is multiplying the `n`th power of the coordinate by
the image of `a` under the structure map. -/
private theorem laurentStructureHom_mul_coordinate_zpow (hU : IsAffineOpen U) (n : ℤ)
    (a : D.X.ringCatSheaf.obj.obj (op U)) :
    D.laurentStructureHom U a * ((c.coordinate ^ n : _ˣ) :
        Stacks.RelativeSpec.AlgebraSheaf.sections D.laurentAlgebraSheaf U) =
      D.laurentAlgebraSheafIncl n U
        (a • Stacks.AlgebraicGeometry.TwistGenerator.genInt D.L (c.trivialization hU) n) :=
  (congrArg (fun z => D.laurentStructureHom U a * z) (c.coordinate_zpow_eq hU n)).trans
    (D.laurentAlgebraSheafIncl_smul U n a _).symm

/-- **`L^{⊗ n}` is free of rank one on the degree-`n` generator of the trivialization of a
chart, for every INTEGER `n`**: scaling that generator is a bijection from the functions on `U`
onto the sections of `L^{⊗ n}` over `U`.

This is the integer-indexed counterpart of
`Stacks.AlgebraicGeometry.TwistGenerator.bijective_toSpanSingleton_gen`, which runs over `ℕ`.
No induction over the degree is needed: a chart supplies the inverse of its coordinate outright,
so multiplying by `t ^ n` and by `t ^ (-n)` in the sections ring gives the two directions
uniformly in `n`.

It is the structure-sheaf case of
`Stacks.AlgebraicGeometry.TwistGenerator.bijective_tensorSectionsAt_genInt`, which needs no
affineness; what the affineness is used for here is the chart's own passage to a
trivialization. -/
theorem bijective_smul_genInt (hU : IsAffineOpen U) (n : ℤ) :
    Function.Bijective
      (fun a : D.X.ringCatSheaf.obj.obj (op U) =>
        a • Stacks.AlgebraicGeometry.TwistGenerator.genInt D.L (c.trivialization hU) n) := by
  refine ⟨fun a b hab => ?_, fun x => ?_⟩
  · refine D.injective_laurentStructureHom hU ((Units.mul_left_inj (c.coordinate ^ n)).mp ?_)
    exact (c.laurentStructureHom_mul_coordinate_zpow hU n a).trans
      ((congrArg (D.laurentAlgebraSheafIncl n U) hab).trans
        (c.laurentStructureHom_mul_coordinate_zpow hU n b).symm)
  · have hinv : (↑(c.coordinate ^ n)⁻¹ :
        Stacks.RelativeSpec.AlgebraSheaf.sections D.laurentAlgebraSheaf U) =
          D.laurentAlgebraSheafIncl (-n) U
            (Stacks.AlgebraicGeometry.TwistGenerator.genInt D.L
              (c.trivialization hU) (-n)) :=
      (congrArg Units.val (zpow_neg c.coordinate n)).symm.trans (c.coordinate_zpow_eq hU (-n))
    have hw : D.laurentAlgebraSheafIncl 0 U
          (D.tensorPowerCongr (add_neg_cancel n) U
            ((D.laurentAlgebra.mul n (-n)).app (op U) x
              (Stacks.AlgebraicGeometry.TwistGenerator.genInt D.L
                (c.trivialization hU) (-n)))) =
        D.laurentAlgebraSheafIncl n U x *
          (↑(c.coordinate ^ n)⁻¹ :
            Stacks.RelativeSpec.AlgebraSheaf.sections D.laurentAlgebraSheaf U) := by
      refine (D.laurentAlgebraSheafIncl_congr (add_neg_cancel n) U
        ((D.laurentAlgebra.mul n (-n)).app (op U) x
          (Stacks.AlgebraicGeometry.TwistGenerator.genInt D.L
            (c.trivialization hU) (-n)))).symm.trans ?_
      refine (D.laurentAlgebraSheafIncl_mul n (-n) U x
        (Stacks.AlgebraicGeometry.TwistGenerator.genInt D.L
          (c.trivialization hU) (-n))).symm.trans ?_
      exact congrArg (fun z => D.laurentAlgebraSheafIncl n U x * z) hinv.symm
    refine ⟨(D.tensorPowerCongr (add_neg_cancel n) U
      ((D.laurentAlgebra.mul n (-n)).app (op U) x
        (Stacks.AlgebraicGeometry.TwistGenerator.genInt D.L (c.trivialization hU) (-n))) :
        ↥(D.X.ringCatSheaf.obj.obj (op U))), ?_⟩
    refine D.injective_laurentAlgebraSheafIncl hU n ?_
    refine (D.laurentAlgebraSheafIncl_smul U n _
      (Stacks.AlgebraicGeometry.TwistGenerator.genInt D.L (c.trivialization hU) n)).trans ?_
    refine Eq.trans (congrArg (fun y => y * D.laurentAlgebraSheafIncl n U
        (Stacks.AlgebraicGeometry.TwistGenerator.genInt D.L (c.trivialization hU) n))
      ((D.laurentStructureHom_eq_incl U _).trans hw)) ?_
    refine Eq.trans (congrArg (fun z => (D.laurentAlgebraSheafIncl n U x *
        (↑(c.coordinate ^ n)⁻¹ :
          Stacks.RelativeSpec.AlgebraSheaf.sections D.laurentAlgebraSheaf U)) * z)
      (c.coordinate_zpow_eq hU n).symm) ?_
    refine (mul_assoc _ _ _).trans ?_
    refine Eq.trans (congrArg (fun z => D.laurentAlgebraSheafIncl n U x * z)
      (Units.inv_mul (c.coordinate ^ n))) ?_
    exact mul_one _

/-- **The comparison of a Laurent chart over an affine open is surjective.** Over an affine open
every function on the inverse image of `U` is a finite sum of homogeneous ones, and a homogeneous
section of degree `n` is a multiple of the `n`th power of the coordinate, by
`Stacks.LineBundle.Situation.LaurentChart.bijective_smul_genInt`. -/
theorem surjective_hom (hU : IsAffineOpen U) : Function.Surjective c.hom := by
  intro b
  obtain ⟨w, hw⟩ := (Stacks.RelativeSpec.bijective_ungradedCommUnit_of_isAffineOpen D.X
    D.laurentAlgebra D.laurentAlgebra_mul_comm hU).2 b
  subst hw
  induction w using D.laurentAlgebra.toPresheafGradedAlgebra.incl_induction with
  | zero => exact ⟨0, (map_zero c.hom).trans (map_zero _).symm⟩
  | incl i y =>
      obtain ⟨a, ha⟩ := (c.bijective_smul_genInt hU i).2 y
      refine ⟨LaurentPolynomial.C (a : ↥Γ(D.X, U)) * LaurentPolynomial.T i, ?_⟩
      refine (map_mul c.hom _ _).trans ?_
      refine (congrArg₂ (· * ·) (c.hom_C (a : ↥Γ(D.X, U))) (c.hom_T i)).trans ?_
      exact (c.laurentStructureHom_mul_coordinate_zpow hU i a).trans
        (congrArg (D.laurentAlgebraSheafIncl i U) ha)
  | add x y hx hy =>
      obtain ⟨p, hp⟩ := hx
      obtain ⟨q, hq⟩ := hy
      exact ⟨p + q, (map_add c.hom p q).trans ((congrArg₂ (· + ·) hp hq).trans
        (map_add _ x y).symm)⟩

end Situation.LaurentChart

namespace Situation.LaurentChart

/-- **The degree-`n` coordinate of a Laurent chart**: the inverse of scaling the degree-`n`
generator, a bijection by
`Stacks.LineBundle.Situation.LaurentChart.bijective_smul_genInt`. The source is spelled
`Γ(X, U)`; the scalar action is written on `id (α := _) a`, which re-types `a` into the
`ringCatSheaf` spelling the action lives at. See the implementation notes: an ascription will not
do this, because it leaves the elaborated type alone and instance search then fails. -/
def coeffEquiv {D : Situation.{u}} {U : D.X.Opens} (ch : D.LaurentChart U)
    (hU : IsAffineOpen U) (n : ℤ) :
    ↥Γ(D.X, U) ≃+ (D.tensorPower n).val.obj (op U) :=
  AddEquiv.ofBijective
    (AddMonoidHom.mk'
      (fun a : ↥Γ(D.X, U) =>
        id (α := ↥(D.X.ringCatSheaf.obj.obj (op U))) a •
          Stacks.AlgebraicGeometry.TwistGenerator.genInt D.L (ch.trivialization hU) n)
      (fun a _ => add_smul (id (α := ↥(D.X.ringCatSheaf.obj.obj (op U))) a) _ _))
    (ch.bijective_smul_genInt hU n)

/-- The inverse of `coeffEquiv` sends `a` times the degree-`n` generator of the trivialization
back to `a`. -/
@[simp]
theorem coeffEquiv_symm_smul {D : Situation.{u}} {U : D.X.Opens} (ch : D.LaurentChart U)
    (hU : IsAffineOpen U) (n : ℤ) (a : Γ(D.X, U)) :
    (ch.coeffEquiv hU n).symm
        (id (α := ↥(D.X.ringCatSheaf.obj.obj (op U))) a •
          Stacks.AlgebraicGeometry.TwistGenerator.genInt D.L (ch.trivialization hU) n) = a :=
  (ch.coeffEquiv hU n).symm_apply_apply a

/-- The left inverse of the comparison of a Laurent chart over an affine open: read a function on
the inverse image of `U` as a direct sum of homogeneous sections and send its degree-`n` piece to
the degree-`n` coordinate times `T n`. No degree arithmetic occurs — the summand index is used
only as the exponent of `T`. -/
def invAddHom {D : Situation.{u}} {U : D.X.Opens} (ch : D.LaurentChart U)
    (hU : IsAffineOpen U) :
    Stacks.RelativeSpec.AlgebraSheaf.sections D.laurentAlgebraSheaf U →+
      LaurentPolynomial ↥Γ(D.X, U) :=
  (DirectSum.toAddMonoid (fun n : ℤ =>
      (AddMonoidHom.mk'
          (fun a : ↥Γ(D.X, U) => LaurentPolynomial.C a * LaurentPolynomial.T n)
          (fun a b => by rw [map_add, add_mul])).comp
        (ch.coeffEquiv hU n).symm.toAddMonoidHom)).comp
    (Stacks.RelativeSpec.ungradedSectionsRingEquiv D.X D.laurentAlgebra
      D.laurentAlgebra_mul_comm hU).symm.toAddMonoidHom

/-- **The comparison of a Laurent chart carries the monomial `a Tⁿ` to the degree-`n` section
`a · tⁿ`.** This is the exact degreewise form of
`Stacks.LineBundle.Situation.LaurentChart.exists_hom_C_mul_T_eq`: the section is named rather
than merely asserted to exist, which is what the two directions of the degreewise comparison
need. -/
theorem hom_single {D : Situation.{u}} {U : D.X.Opens} (ch : D.LaurentChart U) (n : ℤ)
    (a : Γ(D.X, U)) :
    ch.hom (AddMonoidAlgebra.single n a) =
      D.laurentStructureHom U a * ((ch.coordinate ^ n : _ˣ) :
        Stacks.RelativeSpec.AlgebraSheaf.sections D.laurentAlgebraSheaf U) := by
  refine Eq.trans (congrArg ch.hom (LaurentPolynomial.single_eq_C_mul_T a n)) ?_
  refine (map_mul ch.hom _ _).trans ?_
  exact congrArg₂ (· * ·) (ch.hom_C a) (ch.hom_T n)

/-- **The comparison of a Laurent chart over an affine open carries the monomial `a Tⁿ` to the
degree-`n` section `a · tⁿ`.** This is
`Stacks.LineBundle.Situation.LaurentChart.hom_single` with the `n`th power of the coordinate
named as the image of the degree-`n` generator of the chart's trivialization, which is the
spelling the two directions of the degreewise comparison need. -/
theorem hom_single_genInt {D : Situation.{u}} {U : D.X.Opens} (ch : D.LaurentChart U)
    (hU : IsAffineOpen U) (n : ℤ) (a : Γ(D.X, U)) :
    ch.hom (AddMonoidAlgebra.single n a) =
      D.laurentAlgebraSheafIncl n U
        (id (α := ↥(D.X.ringCatSheaf.obj.obj (op U))) a •
          Stacks.AlgebraicGeometry.TwistGenerator.genInt D.L (ch.trivialization hU) n) := by
  exact (ch.hom_single n a).trans (ch.laurentStructureHom_mul_coordinate_zpow hU n a)

/-- **The comparison of a Laurent chart over an affine open is injective**, being split by
`Stacks.LineBundle.Situation.LaurentChart.invAddHom`. The two additive maps are compared on the
monomials, which generate a Laurent polynomial algebra additively. -/
theorem injective_hom {D : Situation.{u}} {U : D.X.Opens} (ch : D.LaurentChart U)
    (hU : IsAffineOpen U) : Function.Injective ch.hom := by
  have hsingle : ∀ (n : ℤ) (a : Γ(D.X, U)),
      ch.invAddHom hU (ch.hom (AddMonoidAlgebra.single n a)) =
        AddMonoidAlgebra.single n a := by
    intro n a
    refine Eq.trans (congrArg (ch.invAddHom hU) (ch.hom_single_genInt hU n a)) ?_
    refine Eq.trans (congrArg (DirectSum.toAddMonoid _)
      ((Stacks.RelativeSpec.ungradedSectionsRingEquiv D.X D.laurentAlgebra
        D.laurentAlgebra_mul_comm hU).symm_apply_apply _)) ?_
    refine (DirectSum.toAddMonoid_of _ n _).trans ?_
    refine Eq.trans (congrArg (fun r : ↥Γ(D.X, U) =>
      LaurentPolynomial.C r * LaurentPolynomial.T n)
      (ch.coeffEquiv_symm_smul hU n a)) ?_
    exact (LaurentPolynomial.single_eq_C_mul_T a n).symm
  have key : ∀ p : LaurentPolynomial ↥Γ(D.X, U), ch.invAddHom hU (ch.hom p) = p := by
    intro p
    refine LaurentPolynomial.induction_on' p ?_ ?_
    · intro r s hr hs
      rw [map_add, map_add, hr, hs]
    · intro n a
      have h := hsingle n a
      rw [LaurentPolynomial.single_eq_C_mul_T] at h
      exact h
  intro p q hpq
  exact (key p).symm.trans ((congrArg (ch.invAddHom hU) hpq).trans (key q))

/-- **The comparison of a Laurent chart over an affine open is an isomorphism**:
`Γ(X, U)[T;T⁻¹] ≅ Γ(L^⋆, π⁻¹U)`. This is the affine local model of the complement of the zero
section of the line bundle that the proof of Tag 0FUF computes in. -/
def homEquiv {D : Situation.{u}} {U : D.X.Opens} (ch : D.LaurentChart U)
    (hU : IsAffineOpen U) :
    LaurentPolynomial ↥Γ(D.X, U) ≃+*
      Stacks.RelativeSpec.AlgebraSheaf.sections D.laurentAlgebraSheaf U :=
  RingEquiv.ofBijective ch.hom ⟨ch.injective_hom hU, ch.surjective_hom hU⟩

/-- The ring isomorphism `homEquiv` of a Laurent chart over an affine open agrees with the
comparison `hom`. -/
@[simp]
theorem homEquiv_apply {D : Situation.{u}} {U : D.X.Opens} (ch : D.LaurentChart U)
    (hU : IsAffineOpen U) (p : LaurentPolynomial ↥Γ(D.X, U)) :
    ch.homEquiv hU p = ch.hom p :=
  rfl

/-- **Every homogeneous section of degree `n` is the image of a Laurent polynomial of weight
`n`.** This is the direction of the degreewise comparison that the isomorphism supplies: the
weight-`n` monomial is `Tⁿ` times the degree-`n` coordinate of the section. -/
theorem exists_mem_grade_hom_eq {D : Situation.{u}} {U : D.X.Opens} (ch : D.LaurentChart U)
    (hU : IsAffineOpen U) (n : ℤ) (x : (D.tensorPower n).val.obj (op U)) :
    ∃ q ∈ AddMonoidAlgebra.grade ↥Γ(D.X, U) n,
      ch.hom q = D.laurentAlgebraSheafIncl n U x := by
  refine ⟨AddMonoidAlgebra.single n ((ch.coeffEquiv hU n).symm x),
    AddMonoidAlgebra.single_mem_grade n _, ?_⟩
  refine (ch.hom_single_genInt hU n ((ch.coeffEquiv hU n).symm x)).trans ?_
  exact congrArg (D.laurentAlgebraSheafIncl n U) ((ch.coeffEquiv hU n).apply_symm_apply x)

/-- **The comparison of a Laurent chart over an affine open matches the two gradings**: it
carries the weight-`n` part of `Γ(X, U)[T;T⁻¹]` exactly onto the degree-`n` homogeneous sections
of `Γ(L^⋆, π⁻¹U)`, for every integer `n`.

`LaurentDeRham.weightGrading R A n` is `AddMonoidAlgebra.grade A n` with its scalars restricted
along a base ring, so it has the same underlying set and this statement is about it too, without
a base ring having to be fixed. -/
theorem hom_image_grade_eq {D : Situation.{u}} {U : D.X.Opens} (ch : D.LaurentChart U)
    (hU : IsAffineOpen U) (n : ℤ) :
    ch.hom '' (AddMonoidAlgebra.grade ↥Γ(D.X, U) n : Set (LaurentPolynomial ↥Γ(D.X, U))) =
      Set.range (D.laurentAlgebraSheafIncl n U) := by
  refine Set.eq_of_subset_of_subset (fun b hb => ?_) (fun b hb => ?_)
  · obtain ⟨q, hq, rfl⟩ := hb
    obtain ⟨x, hx⟩ := ch.exists_hom_eq_of_mem_grade hq
    exact ⟨x, hx.symm⟩
  · obtain ⟨x, rfl⟩ := hb
    obtain ⟨q, hq, hqx⟩ := ch.exists_mem_grade_hom_eq hU n x
    exact ⟨q, hq, hqx⟩

end Situation.LaurentChart

/-! ### The base ring -/

/-- The affine local model of `L^⋆` is the universal algebra map of the relative spectrum of the
Laurent algebra, read over an affine open of `X`: both are the chart of Tag 01LP transported
across the `Spec`-`Γ` adjunction. -/
theorem Situation.laurentSectionsIso_hom_eq (D : Situation.{u}) (U : D.X.affineOpens) :
    (D.laurentSectionsIso U).hom =
      (Stacks.RelativeSpec.universalAlgebraMap
        D.laurentRelativeSpecSituation).right.app (op U.1) :=
  (Stacks.RelativeSpec.universalAlgebraMap_app D.laurentRelativeSpecSituation U).symm

/-- **The affine local model carries the structure map of the Laurent algebra sheaf to the
pullback of functions along the projection `π : L^⋆ ⟶ X`.** -/
theorem Situation.laurentSectionsIso_hom_laurentStructureHom (D : Situation.{u})
    (U : D.X.affineOpens) (r : Γ(D.X, U.1)) :
    (D.laurentSectionsIso U).hom.hom (D.laurentStructureHom U.1 r) =
      (D.laurentSpectrumToBase.app U.1).hom r :=
  (congrArg (fun k => CommRingCat.Hom.hom k (D.laurentStructureHom U.1 r))
      (D.laurentSectionsIso_hom_eq U)).trans
    (congrArg (fun k => CommRingCat.Hom.hom k r)
      (Stacks.RelativeSpec.toBase_app D.laurentRelativeSpecSituation U.1)).symm

/-- The same identification with the pullback of functions written as a restricted section map,
the spelling at which it composes with the sections of the structure morphism of `X`. -/
theorem Situation.laurentSectionsIso_hom_laurentStructureHom' (D : Situation.{u})
    (U : D.X.affineOpens) (r : Γ(D.X, U.1)) :
    (D.laurentSectionsIso U).hom.hom (D.laurentStructureHom U.1 r) =
      (D.laurentSpectrumToBase.appLE U.1 (D.laurentSpectrumToBase ⁻¹ᵁ U.1) le_rfl).hom r := by
  rw [← Scheme.Hom.app_eq_appLE]
  exact D.laurentSectionsIso_hom_laurentStructureHom U r

/-- **The inverse image in `L^⋆` of an affine open of `X` is affine**, the projection
`π : L^⋆ ⟶ X` being an affine morphism. -/
theorem Situation.isAffineOpen_laurentPreimage (D : Situation.{u}) {U : D.X.Opens}
    (hU : IsAffineOpen U) : IsAffineOpen (D.laurentSpectrumToBase ⁻¹ᵁ U) :=
  IsAffineHom.isAffine_preimage U hU

/-- The inverse image in `L^⋆` of an open of `X` lying over an open `V` of `S` lies over `V`. -/
theorem Situation.laurentPreimage_le_laurentToBase_preimage (D : Situation.{u})
    {U : D.X.Opens} {V : D.S.Opens} (hUV : U ≤ D.f ⁻¹ᵁ V) :
    D.laurentSpectrumToBase ⁻¹ᵁ U ≤ D.laurentToBase ⁻¹ᵁ V := by
  change D.laurentSpectrumToBase ⁻¹ᵁ U ≤ (D.laurentSpectrumToBase ≫ D.f) ⁻¹ᵁ V
  rw [Scheme.Hom.comp_preimage]
  exact fun _ hx => hUV hx

namespace Situation.LaurentChart

/-- **The comparison of a Laurent chart as a ring isomorphism onto the functions on the inverse
image of `U` in `L^⋆`**: `Γ(X, U)[T;T⁻¹] ≅ Γ(L^⋆, π⁻¹U)`. This is
`Stacks.LineBundle.Situation.LaurentChart.homEquiv` followed by the affine local model
`Stacks.LineBundle.Situation.laurentSectionsIso`, so that the comparison lands in the sections of
the structure sheaf of `L^⋆` rather than in the sections of the Laurent algebra sheaf. -/
def sectionsRingEquiv {D : Situation.{u}} {U : D.X.affineOpens} (ch : D.LaurentChart U.1) :
    LaurentPolynomial ↥Γ(D.X, U.1) ≃+*
      Γ(D.laurentSpectrum, D.laurentSpectrumToBase ⁻¹ᵁ U.1) :=
  (ch.homEquiv U.2).trans (D.laurentSectionsIso U).commRingCatIsoToRingEquiv

/-- The ring isomorphism `sectionsRingEquiv` sends a Laurent polynomial `p` to the image of
`hom p` under `laurentSectionsIso`. -/
@[simp]
theorem sectionsRingEquiv_apply {D : Situation.{u}} {U : D.X.affineOpens}
    (ch : D.LaurentChart U.1) (p : LaurentPolynomial ↥Γ(D.X, U.1)) :
    ch.sectionsRingEquiv p = (D.laurentSectionsIso U).hom.hom (ch.hom p) :=
  rfl

/-- **The comparison of a Laurent chart is a comparison over the base**: it carries the constant
Laurent polynomial on a function pulled back from an affine open `V` of `S` to that function
pulled back to `L^⋆`. This is what makes the two sides algebras over `Γ(S, V)` *compatibly*, and
so what lets the base ring of the affine residue sequence of Tag 0FUF be the functions on an
affine open of the base. -/
theorem sectionsRingEquiv_C_appLE {D : Situation.{u}} {U : D.X.affineOpens}
    (ch : D.LaurentChart U.1) {V : D.S.Opens} (hUV : U.1 ≤ D.f ⁻¹ᵁ V) (r : Γ(D.S, V)) :
    ch.sectionsRingEquiv (LaurentPolynomial.C ((D.f.appLE V U.1 hUV).hom r)) =
      (D.laurentToBase.appLE V (D.laurentSpectrumToBase ⁻¹ᵁ U.1)
        (D.laurentPreimage_le_laurentToBase_preimage hUV)).hom r :=
  (congrArg (D.laurentSectionsIso U).hom.hom (ch.hom_C _)).trans
    ((D.laurentSectionsIso_hom_laurentStructureHom' U _).trans
      (congrArg (fun k => CommRingCat.Hom.hom k r)
        (Scheme.Hom.appLE_comp_appLE D.laurentSpectrumToBase D.f V U.1
          (D.laurentSpectrumToBase ⁻¹ᵁ U.1) hUV le_rfl)))

/-- **The affine local model of `L^⋆` over the base**: over an affine open `U` of `X` carrying a
Laurent chart and mapping into an affine open `V` of `S`, the functions on the inverse image of
`U` in `L^⋆` are the Laurent polynomial algebra `Γ(X, U)[T;T⁻¹]` **as algebras over
`Γ(S, V)`**.

This is the point at which the base ring enters: the affine residue sequence of Tag 0FUF is a
sequence of complexes of modules over a base ring `R` with `A` an `R`-algebra, and this
identification is what lets `R` be the functions on an affine open of `S` and `A` the functions
on an affine open of `X` lying over it. -/
@[sga "3 VIII 4.7" "special case"]
def sectionsAlgEquiv {D : Situation.{u}} {U : D.X.affineOpens} (ch : D.LaurentChart U.1)
    {V : D.S.Opens} (hUV : U.1 ≤ D.f ⁻¹ᵁ V) :
    letI := Stacks.Smooth.algebraAppLE D.f hUV
    letI := Stacks.Smooth.algebraAppLE D.laurentToBase
      (D.laurentPreimage_le_laurentToBase_preimage hUV)
    LaurentPolynomial ↥Γ(D.X, U.1) ≃ₐ[↥Γ(D.S, V)]
      ↥Γ(D.laurentSpectrum, D.laurentSpectrumToBase ⁻¹ᵁ U.1) :=
  letI := Stacks.Smooth.algebraAppLE D.f hUV
  letI := Stacks.Smooth.algebraAppLE D.laurentToBase
    (D.laurentPreimage_le_laurentToBase_preimage hUV)
  { ch.sectionsRingEquiv with
    commutes' := fun r => by
      rw [LaurentPolynomial.algebraMap_apply, RingHom.algebraMap_toAlgebra,
        RingHom.algebraMap_toAlgebra]
      exact ch.sectionsRingEquiv_C_appLE hUV r }

end Situation.LaurentChart

end Stacks.LineBundle

end
