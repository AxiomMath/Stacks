module

public import StacksFrontier.AlgebraicGeometry.DeRham.LogPoles.LogResidueSequence
public import StacksFrontier.AlgebraicGeometry.DeRham.CupProduct.GradedCommutativity
public import StacksFrontier.AlgebraicGeometry.DeRham.DifferentialGradedAlgebra.Basic

/-!
# The wedge product of relative forms over an open, as a ring computation

Let `f : X ⟶ S` be a morphism of schemes. This file names the wedge product `ω ∧ η` of two local
relative forms over an open `V` (`AlgebraicGeometry.Scheme.Hom.formWedge`), records its
linearity, its compatibility with restriction and with restriction to a closed subscheme, and
gives the means of computing with it: every local form is read in the ring
`⨁ i, Ω^i_{X/S}(V)` of all local forms over `V` (`AlgebraicGeometry.Scheme.Hom.totForm`), where
the wedge product is the ring multiplication, a local function `r` is the central element
`totScalar r`, and the exact one-form `dc` is `totExact c`.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.formWedge`: the wedge product of local relative forms, in the
  natural-number degree `p + q`.
* `AlgebraicGeometry.Scheme.Hom.totForm`, `totScalar`, `totExact`: local forms, functions and exact
  one-forms in the ring of all local forms.
* `AlgebraicGeometry.Scheme.Hom.formCast`: a local form read in another, equal, degree.

## Main results

* `AlgebraicGeometry.Scheme.Hom.totForm_formWedge`, `totForm_smul`, `totForm_exactWedge`: the
  dictionary between forms and the ring of all local forms.
* `AlgebraicGeometry.Scheme.Hom.totForm_mul_totExact`: a form of degree `n` and an exact one-form
  commute up to `(-1)^n`.
* `AlgebraicGeometry.Scheme.Hom.totForm_deRhamD_formWedge`: the graded Leibniz rule
  `d(ω ∧ η) = dω ∧ η + (-1)^p ω ∧ dη`, read in the ring of all local forms.
* `AlgebraicGeometry.Scheme.Hom.formRes_formWedge`: restriction to a closed subscheme is
  multiplicative.

## Implementation notes

The ring of all local forms is `AlgebraicGeometry.SheafOfModules.totalForms` of the package of
algebras `AlgebraicGeometry.SheafOfModules.differentialAlgebras (inverseImageStructureMap f)`,
which is `AlgebraicGeometry.Scheme.Hom.deRhamAlgebras f` by definition; it is spelled that way so
that the type of the package is syntactically the one the ring instances are declared at.
Identities in that ring are then proved either by `ring`-free rewriting with the lemmas above or
through generic lemmas about an arbitrary ring, which are applied by unification and so are
insensitive to the spelling.

## References

* [Stacks Project, Tag 0FUP](https://stacks.math.columbia.edu/tag/0FUP)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace
open AlgebraicGeometry.SheafOfModules

attribute [local instance] gradedFormsGOne gradedFormsGMul gradedFormsGRing

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- **The wedge product** `ω ∧ η` of a local relative `p`-form and a local relative `q`-form over
an open `V`, in degree `p + q`. -/
def formWedge (p q : ℕ) (V : X.Opens) (ω : Γ(relativeDifferentialForms f (p : ℤ), V))
    (η : Γ(relativeDifferentialForms f (q : ℤ), V)) :
    Γ(relativeDifferentialForms f ((p + q : ℕ) : ℤ), V) :=
  formProduct (deRhamAlgebras f) p q (op V) ω η

/-- A local relative `n`-form, read in the ring of all local forms over `V`. -/
abbrev totForm (n : ℕ) (V : X.Opens) :
    Γ(relativeDifferentialForms f (n : ℤ), V) →+
      totalForms (differentialAlgebras (inverseImageStructureMap f)) (op V) :=
  ofGradedForm (differentialAlgebras (inverseImageStructureMap f)) (op V) (n : ℤ)

/-- A local function, read as a degree-zero element of the ring of all local forms over `V`. -/
abbrev totScalar (V : X.Opens) (r : Γ(X, V)) :
    totalForms (differentialAlgebras (inverseImageStructureMap f)) (op V) :=
  scalarForm (differentialAlgebras (inverseImageStructureMap f)) (op V) r

/-- The exact one-form `dc`, read in the ring of all local forms over `V`. -/
abbrev totExact (V : X.Opens) (c : Γ(X, V)) :
    totalForms (differentialAlgebras (inverseImageStructureMap f)) (op V) :=
  exactForm (differentialAlgebras (inverseImageStructureMap f)) (op V) c

variable {f}

/-- A local relative form, read in another, equal, degree. -/
abbrev formCast {m n : ℕ} (h : m
    = n) {V : X.Opens} (x : Γ(relativeDifferentialForms f (m : ℤ), V)) :
    Γ(relativeDifferentialForms f (n : ℤ), V) :=
  _root_.SheafOfModules.gradedCast (fun k : ℕ => Γ(relativeDifferentialForms f (k : ℤ), V)) h x

/-- Reading a local form in an equal degree does not change it in the ring of all local forms. -/
theorem totForm_formCast {m n : ℕ} (h : m = n) {V : X.Opens}
    (x : Γ(relativeDifferentialForms f (m : ℤ), V)) :
    totForm f n V (formCast h x) = totForm f m V x := by
  subst h
  rfl

/-- Reading a local form in an equal degree commutes with restriction to a smaller open. -/
theorem formCast_map {m n : ℕ} (h : m = n) {V V' : X.Opens} (hV : V' ≤ V)
    (x : Γ(relativeDifferentialForms f (m : ℤ), V)) :
    (relativeDifferentialForms f (n : ℤ)).presheaf.map (homOfLE hV).op (formCast h x) =
      formCast h ((relativeDifferentialForms f (m : ℤ)).presheaf.map (homOfLE hV).op x) := by
  subst h
  rfl

/-- A local `n`-form is determined by its image in the ring of all local forms. -/
theorem totForm_injective (n : ℕ) (V : X.Opens) : Function.Injective (totForm f n V) :=
  DirectSum.of_injective (β := gradedForms (deRhamAlgebras f) (op V)) (n : ℤ)

/-- In the ring of all local forms, the wedge product `ω ∧ η` is the product of `ω` and `η`. -/
theorem totForm_formWedge (p q : ℕ) (V : X.Opens) (ω : Γ(relativeDifferentialForms f (p : ℤ), V))
    (η : Γ(relativeDifferentialForms f (q : ℤ), V)) :
    totForm f (p + q) V (formWedge f p q V ω η) = totForm f p V ω * totForm f q V η :=
  ofGradedForm_mul (deRhamAlgebras f) (op V) (p : ℤ) (q : ℤ) ω η

/-- In the ring of all local forms, the form `r • ω` is the product `totScalar r * ω`. -/
theorem totForm_smul (n : ℕ) (V : X.Opens) (r : Γ(X, V))
    (ω : Γ(relativeDifferentialForms f (n : ℤ), V)) :
    totForm f n V (r • ω) = totScalar f V r * totForm f n V ω :=
  (scalarForm_mul (deRhamAlgebras f) (op V) r (n : ℤ) ω).symm

/-- In the ring of all local forms, the form `dc ∧ β` is the product `totExact c * β`. -/
theorem totForm_exactWedge (n : ℕ) (V : X.Opens) (c : Γ(X, V))
    (β : Γ(relativeDifferentialForms f (n : ℤ), V)) :
    totForm f (n + 1) V (exactWedge f n V c β) = totExact f V c * totForm f n V β :=
  (ofGradedForm_reindexForm (deRhamAlgebras f) (Nat.add_comm 1 n) (op V) _).trans
    (ofGradedForm_mul (deRhamAlgebras f) (op V) 1 (n : ℤ) _ β)

/-- A local function commutes with every local form in the ring of all local forms. -/
theorem totScalar_mul_comm (V : X.Opens) (r : Γ(X, V)) (n : ℕ)
    (ω : Γ(relativeDifferentialForms f (n : ℤ), V)) :
    totScalar f V r * totForm f n V ω = totForm f n V ω * totScalar f V r :=
  (scalarForm_mul (deRhamAlgebras f) (op V) r (n : ℤ) ω).trans
    (mul_scalarForm (deRhamAlgebras f) (op V) r (n : ℤ) ω).symm

/-- A local function commutes with an exact one-form `dc` in the ring of all local forms. -/
theorem totScalar_mul_totExact_comm (V : X.Opens) (r c : Γ(X, V)) :
    totScalar f V r * totExact f V c = totExact f V c * totScalar f V r :=
  totScalar_mul_comm V r 1 (exactOne _ (op V) c)

/-- An exact one-form squares to zero: `dc ∧ dc = 0`. -/
theorem totExact_mul_self (V : X.Opens) (c : Γ(X, V)) :
    totExact f V c * totExact f V c = 0 :=
  exactForm_mul_self (deRhamAlgebras f) (op V) c

/-- A form of degree `n` and an exact one-form commute up to the sign `(-1)^n`. -/
theorem totForm_mul_totExact (n : ℕ) (V : X.Opens) (ω : Γ(relativeDifferentialForms f (n : ℤ), V))
    (c : Γ(X, V)) :
    totForm f n V ω * totExact f V c = (-1 : ℤ) ^ n • (totExact f V c * totForm f n V ω) := by
  have h := ofGradedForm_mul_comm (deRhamAlgebras f) n 1 (op V) ω (exactOne _ (op V) c)
  rw [mul_one] at h
  exact h

/-- The Leibniz rule `d(r • ω) = dr ∧ ω + r • dω`, read in the ring of all local forms. -/
theorem totForm_deRhamD_smul (n : ℕ) (V : X.Opens) (r : Γ(X, V))
    (ω : Γ(relativeDifferentialForms f (n : ℤ), V)) :
    totForm f (n + 1) V (deRhamD f n V (r • ω)) =
      totExact f V r * totForm f n V ω +
        totScalar f V r * totForm f (n + 1) V (deRhamD f n V ω) := by
  refine (congrArg (totForm f (n + 1) V) (deRhamD_smul n V r ω)).trans
    ((map_add (totForm f (n + 1) V) _ _).trans ?_)
  exact congrArg₂ (· + ·) (totForm_exactWedge n V r ω) (totForm_smul (n + 1) V r _)

private theorem ofGradedForm_XIsoOfEq_hom {m n : ℕ} (h : m = n) (V : X.Opens)
    (x : ((AlgebraicGeometry.SheafOfModules.deRhamComplex (deRhamAlgebras f)
      (deRhamDifferential (deRhamAlgebras f))).X m).val.obj (op V)) :
    totForm f n V (((AlgebraicGeometry.SheafOfModules.deRhamComplex (deRhamAlgebras f)
      (deRhamDifferential (deRhamAlgebras f))).XIsoOfEq h).hom.val.app (op V) x) =
      totForm f m V x := by
  subst h
  rw [HomologicalComplex.XIsoOfEq_rfl]
  rfl

/-- **The graded Leibniz rule for local forms, in the ring of all local forms**:
`d(ω ∧ η) = dω ∧ η + (-1)^p ω ∧ dη`. -/
theorem totForm_deRhamD_formWedge (p q : ℕ) (V : X.Opens)
    (ω : Γ(relativeDifferentialForms f (p : ℤ), V))
    (η : Γ(relativeDifferentialForms f (q : ℤ), V)) :
    totForm f (p + q + 1) V (deRhamD f (p + q) V (formWedge f p q V ω η)) =
      totForm f (p + 1) V (deRhamD f p V ω) * totForm f q V η +
        (-1 : ℤ) ^ p • (totForm f p V ω * totForm f (q + 1) V (deRhamD f q V η)) := by
  have h := congrArg (totForm f (p + q + 1) V)
    (d_formProduct (deRhamAlgebras f) (deRhamDifferential (deRhamAlgebras f)) p q (op V) ω η)
  refine h.trans ((map_add (totForm f (p + q + 1) V) _ _).trans ?_)
  refine congrArg₂ (· + ·) ((ofGradedForm_XIsoOfEq_hom _ V _).trans ?_)
    ((map_zsmul (totForm f (p + q + 1) V) _ _).trans
      (congrArg (fun z => (-1 : ℤ) ^ p • z) ((ofGradedForm_XIsoOfEq_hom _ V _).trans ?_)))
  · exact ofGradedForm_mul (deRhamAlgebras f) (op V) ((p + 1 : ℕ) : ℤ) (q : ℤ) _ η
  · exact ofGradedForm_mul (deRhamAlgebras f) (op V) (p : ℤ) ((q + 1 : ℕ) : ℤ) ω _

/-! ### Linearity, restriction and restriction to a subscheme -/

/-- The wedge product is additive in its first argument. -/
theorem formWedge_add_left (p q : ℕ) (V : X.Opens)
    (ω ω' : Γ(relativeDifferentialForms f (p : ℤ), V))
    (η : Γ(relativeDifferentialForms f (q : ℤ), V)) :
    formWedge f p q V (ω + ω') η = formWedge f p q V ω η + formWedge f p q V ω' η :=
  DFunLike.congr_fun (map_add (((deRhamAlgebras f).exterior.mul (p : ℤ) (q : ℤ)).app (op V)) ω ω') η

/-- The wedge product is additive in its second argument. -/
theorem formWedge_add_right (p q : ℕ) (V : X.Opens) (ω : Γ(relativeDifferentialForms f (p : ℤ), V))
    (η η' : Γ(relativeDifferentialForms f (q : ℤ), V)) :
    formWedge f p q V ω (η + η') = formWedge f p q V ω η + formWedge f p q V ω η' :=
  map_add ((((deRhamAlgebras f).exterior.mul (p : ℤ) (q : ℤ)).app (op V)) ω) η η'

/-- The wedge product is linear over local functions in its first argument. -/
theorem formWedge_smul_left (p q : ℕ) (V : X.Opens) (r : Γ(X, V))
    (ω : Γ(relativeDifferentialForms f (p : ℤ), V))
    (η : Γ(relativeDifferentialForms f (q : ℤ), V)) :
    formWedge f p q V (r • ω) η = r • formWedge f p q V ω η :=
  ((deRhamAlgebras f).exterior.mul (p : ℤ) (q : ℤ)).map_smul_left (op V) r ω η

/-- The wedge product is linear over local functions in its second argument. -/
theorem formWedge_smul_right (p q : ℕ) (V : X.Opens) (r : Γ(X, V))
    (ω : Γ(relativeDifferentialForms f (p : ℤ), V))
    (η : Γ(relativeDifferentialForms f (q : ℤ), V)) :
    formWedge f p q V ω (r • η) = r • formWedge f p q V ω η :=
  ((deRhamAlgebras f).exterior.mul (p : ℤ) (q : ℤ)).map_smul_right (op V) r ω η

/-- The wedge product with the zero form on the left is zero. -/
theorem formWedge_zero_left (p q : ℕ) (V : X.Opens)
    (η : Γ(relativeDifferentialForms f (q : ℤ), V)) :
    formWedge f p q V 0 η = 0 :=
  DFunLike.congr_fun (map_zero (((deRhamAlgebras f).exterior.mul (p : ℤ) (q : ℤ)).app (op V))) η

/-- The wedge product with the zero form on the right is zero. -/
theorem formWedge_zero_right (p q : ℕ) (V : X.Opens)
    (ω : Γ(relativeDifferentialForms f (p : ℤ), V)) :
    formWedge f p q V ω 0 = 0 :=
  map_zero ((((deRhamAlgebras f).exterior.mul (p : ℤ) (q : ℤ)).app (op V)) ω)

/-- The wedge product commutes with restriction to a smaller open. -/
theorem formWedge_res (p q : ℕ) {V W : X.Opens} (h : W ≤ V)
    (ω : Γ(relativeDifferentialForms f (p : ℤ), V))
    (η : Γ(relativeDifferentialForms f (q : ℤ), V)) :
    (relativeDifferentialForms f ((p + q : ℕ) : ℤ)).presheaf.map (homOfLE h).op
        (formWedge f p q V ω η) =
      formWedge f p q W ((relativeDifferentialForms f (p : ℤ)).presheaf.map (homOfLE h).op ω)
        ((relativeDifferentialForms f (q : ℤ)).presheaf.map (homOfLE h).op η) :=
  ((deRhamAlgebras f).exterior.mul (p : ℤ) (q : ℤ)).naturality (homOfLE h).op ω η

variable {Z : Scheme.{u}} (i : Z ⟶ X)

/-- **Restriction to a subscheme is multiplicative**: `(ω ∧ η)|_Z = ω|_Z ∧ η|_Z`. -/
theorem formRes_formWedge (p q : ℕ) (V : X.Opens) (ω : Γ(relativeDifferentialForms f (p : ℤ), V))
    (η : Γ(relativeDifferentialForms f (q : ℤ), V)) :
    formRes i ((p + q : ℕ) : ℤ) V (formWedge f p q V ω η) =
      formWedge (i ≫ f) p q (i ⁻¹ᵁ V) (formRes i (p : ℤ) V ω) (formRes i (q : ℤ) V η) :=
  relativeDifferentialFormsPullback_mul i f (i ≫ f) (𝟙 S) (Category.comp_id _).symm (p : ℤ)
    (q : ℤ) V ω η

end AlgebraicGeometry.Scheme.Hom

end
