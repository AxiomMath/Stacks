module

public import Mathlib.Algebra.Homology.HomotopyCategory
public import Mathlib.CategoryTheory.Abelian.Injective.Resolution

/-!
# Descending an injective resolution into an arbitrary complex of injectives

Mathlib's `CategoryTheory.InjectiveResolution.descHomotopyZero` and
`CategoryTheory.InjectiveResolution.descHomotopy` are stated for a morphism of cochain complexes
whose *target* is the complex underlying an injective resolution `J : InjectiveResolution Z`.
Inspecting their proofs shows that nothing about `J` is used beyond the injectivity of its objects
and its differentials: the exactness that drives the induction is the exactness of the *source*
resolution (`InjectiveResolution.exact₀` and `InjectiveResolution.exact_succ`), and the lifting
step `ShortComplex.Exact.descToInjective` only needs the target object to be injective. Neither
`J.ι` nor the quasi-isomorphism property of `J` appears.

This file records the resulting hypothesis weakening: the target may be an arbitrary cochain
complex `K : CochainComplex C ℕ` with injective objects. The proofs are Mathlib's, with
`J.cocomplex` replaced by `K`. The generalized declarations are named after the Mathlib ones with
a prime; they are intended to supersede them upstream, where Mathlib's versions become the special
case `K = J.cocomplex`.

## Main results

* `CategoryTheory.InjectiveResolution.descHomotopyZero'`: a morphism `f : I.cocomplex ⟶ K` from an
  injective resolution into a complex of injectives with `I.ι ≫ f = 0` is homotopic to zero.
* `CategoryTheory.InjectiveResolution.descHomotopy'`: two morphisms `I.cocomplex ⟶ K` that agree
  after precomposition with `I.ι` are homotopic.
* `CategoryTheory.InjectiveResolution.quotient_map_eq`: hence they become *equal* in the homotopy
  category, so a morphism out of `(HomotopyCategory.quotient C _).obj I.cocomplex` specified by
  "any descent" is well defined.
* `CategoryTheory.InjectiveResolution.homologyMap_mapHomologicalComplex_map_eq`: the induced maps
  on the homology of the image under an additive functor agree, which is how consumers (derived
  functors, `Ext`) use the statement.

## Implementation notes

The injectivity hypothesis on the target is taken as the instance-implicit
`[∀ n, Injective (K.X n)]`, matching `CochainComplex.isKInjective_of_injective`. This is the form
Mathlib conventions call for here: it is a `Prop`-valued class, so instance-implicit costs nothing and
lets the lifting step `descToInjective` find `Injective (K.X n)` by instance search instead of by
hand, and — crucially for the intended use — it makes Mathlib's own statements literal special
cases, since `InjectiveResolution.injective` is already an instance. A plain hypothesis
`(hK : ∀ n, Injective (K.X n))` would force every application to re-thread it through the three
auxiliary constructions. No boundedness hypothesis is needed or wanted: the complex is indexed by
`ℕ`, so it is already concentrated in degrees `≥ 0`, which is exactly the bounded-below condition
that the inductive argument consumes. (For `ℤ`-indexed complexes one must add boundedness, as in
`CochainComplex.isKInjective_of_injective`.)
-/

@[expose] public noncomputable section

open CategoryTheory Category Limits

universe v u v₂ u₂

namespace CategoryTheory

open Injective

namespace InjectiveResolution

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {Y : C} {I : InjectiveResolution Y} {K : CochainComplex C ℕ} [∀ n, Injective (K.X n)]

/-- An auxiliary definition for `descHomotopyZero'`. -/
def descHomotopyZeroZero' (f : I.cocomplex ⟶ K) (comm : I.ι ≫ f = 0) :
    I.cocomplex.X 1 ⟶ K.X 0 :=
  I.exact₀.descToInjective (f.f 0) (congr_fun (congr_arg HomologicalComplex.Hom.f comm) 0)

/-- The degree-zero component of `f` factors through `descHomotopyZeroZero' f comm`. -/
@[reassoc (attr := simp)]
lemma comp_descHomotopyZeroZero' (f : I.cocomplex ⟶ K) (comm : I.ι ≫ f = 0) :
    I.cocomplex.d 0 1 ≫ descHomotopyZeroZero' f comm = f.f 0 :=
  I.exact₀.comp_descToInjective _ _

/-- An auxiliary definition for `descHomotopyZero'`. -/
def descHomotopyZeroOne' (f : I.cocomplex ⟶ K) (comm : I.ι ≫ f = (0 : _ ⟶ K)) :
    I.cocomplex.X 2 ⟶ K.X 1 :=
  (I.exact_succ 0).descToInjective (f.f 1 - descHomotopyZeroZero' f comm ≫ K.d 0 1)
    (by rw [Preadditive.comp_sub, comp_descHomotopyZeroZero'_assoc f comm,
          HomologicalComplex.Hom.comm, sub_self])

/-- The defining property of `descHomotopyZeroOne'`. -/
@[reassoc (attr := simp)]
lemma comp_descHomotopyZeroOne' (f : I.cocomplex ⟶ K) (comm : I.ι ≫ f = (0 : _ ⟶ K)) :
    I.cocomplex.d 1 2 ≫ descHomotopyZeroOne' f comm =
      f.f 1 - descHomotopyZeroZero' f comm ≫ K.d 0 1 :=
  (I.exact_succ 0).comp_descToInjective _ _

/-- An auxiliary definition for `descHomotopyZero'`. -/
def descHomotopyZeroSucc' (f : I.cocomplex ⟶ K) (n : ℕ) (g : I.cocomplex.X (n + 1) ⟶ K.X n)
    (g' : I.cocomplex.X (n + 2) ⟶ K.X (n + 1))
    (w : f.f (n + 1) = I.cocomplex.d (n + 1) (n + 2) ≫ g' + g ≫ K.d n (n + 1)) :
    I.cocomplex.X (n + 3) ⟶ K.X (n + 2) :=
  (I.exact_succ (n + 1)).descToInjective (f.f (n + 2) - g' ≫ K.d _ _) (by
      dsimp
      rw [Preadditive.comp_sub, ← HomologicalComplex.Hom.comm, w, Preadditive.add_comp,
        Category.assoc, Category.assoc, HomologicalComplex.d_comp_d, comp_zero,
        add_zero, sub_self])

/-- The defining property of `descHomotopyZeroSucc'`. -/
@[reassoc (attr := simp)]
lemma comp_descHomotopyZeroSucc' (f : I.cocomplex ⟶ K) (n : ℕ)
    (g : I.cocomplex.X (n + 1) ⟶ K.X n) (g' : I.cocomplex.X (n + 2) ⟶ K.X (n + 1))
    (w : f.f (n + 1) = I.cocomplex.d (n + 1) (n + 2) ≫ g' + g ≫ K.d n (n + 1)) :
    I.cocomplex.d (n + 2) (n + 3) ≫ descHomotopyZeroSucc' f n g g' w =
      f.f (n + 2) - g' ≫ K.d _ _ :=
  (I.exact_succ (n + 1)).comp_descToInjective _ _

/-- A morphism from an injective resolution `I` of `Y` to a cochain complex `K` of injective
objects which vanishes on `I.ι` is homotopic to zero. This is
`CategoryTheory.InjectiveResolution.descHomotopyZero` with the target no longer required to
resolve anything. -/
def descHomotopyZero' (f : I.cocomplex ⟶ K) (comm : I.ι ≫ f = 0) : Homotopy f 0 :=
  Homotopy.mkCoinductive _ (descHomotopyZeroZero' f comm) (by simp)
    (descHomotopyZeroOne' f comm) (by simp) (fun n ⟨g, g', w⟩ =>
    ⟨descHomotopyZeroSucc' f n g g' (by simp only [w, add_comm]), by simp⟩)

/-- Two morphisms from an injective resolution `I` of `Y` to a cochain complex `K` of injective
objects which agree on `I.ι` are homotopic. This is
`CategoryTheory.InjectiveResolution.descHomotopy` with the target no longer required to resolve
anything; accordingly the hypothesis is stated as agreement on `I.ι` rather than through a
factorization `(CochainComplex.single₀ C).map f ≫ J.ι`, which presumes a `J.ι`. -/
def descHomotopy' (g h : I.cocomplex ⟶ K) (w : I.ι ≫ g = I.ι ≫ h) : Homotopy g h :=
  Homotopy.equivSubZero.invFun
    (descHomotopyZero' _ (by rw [Preadditive.comp_sub, w, sub_self]))

omit [∀ n, Injective (K.X n)] in
/-- A morphism out of `I.ι` is determined by its degree-zero component, so the hypothesis of
`descHomotopy'` may be checked in degree zero. -/
lemma ι_comp_ext (g h : I.cocomplex ⟶ K) (w : I.ι.f 0 ≫ g.f 0 = I.ι.f 0 ≫ h.f 0) :
    I.ι ≫ g = I.ι ≫ h := by
  ext
  simpa using w

/-- Two morphisms from an injective resolution `I` of `Y` to a cochain complex `K` of injective
objects which agree on `I.ι` become equal in the homotopy category. Consequently a morphism out of
`(HomotopyCategory.quotient C (ComplexShape.up ℕ)).obj I.cocomplex` may be specified by *any*
descent along `I.ι`. -/
theorem quotient_map_eq (g h : I.cocomplex ⟶ K) (w : I.ι ≫ g = I.ι ≫ h) :
    (HomotopyCategory.quotient C (ComplexShape.up ℕ)).map g =
      (HomotopyCategory.quotient C (ComplexShape.up ℕ)).map h :=
  HomotopyCategory.eq_of_homotopy _ _ (descHomotopy' g h w)

/-- Applying an additive functor `F` to two morphisms from an injective resolution `I` of `Y` to a
cochain complex `K` of injective objects which agree on `I.ι` gives equal morphisms in the
homotopy category. -/
theorem quotient_map_mapHomologicalComplex_map_eq {D : Type u₂} [Category.{v₂} D] [Abelian D]
    (F : C ⥤ D) [F.Additive] (g h : I.cocomplex ⟶ K) (w : I.ι ≫ g = I.ι ≫ h) :
    (HomotopyCategory.quotient D (ComplexShape.up ℕ)).map
        ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map g) =
      (HomotopyCategory.quotient D (ComplexShape.up ℕ)).map
        ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map h) :=
  HomotopyCategory.eq_of_homotopy _ _ (F.mapHomotopy (descHomotopy' g h w))

/-- The maps induced on the homology of the image under an additive functor `F` by two morphisms
from an injective resolution `I` of `Y` to a cochain complex `K` of injective objects which agree
on `I.ι` are equal. This is the form in which right derived functors consume the statement: the
value of `Rⁿ F` on a morphism may be computed from any descent along `I.ι`. -/
theorem homologyMap_mapHomologicalComplex_map_eq {D : Type u₂} [Category.{v₂} D] [Abelian D]
    (F : C ⥤ D) [F.Additive] (g h : I.cocomplex ⟶ K) (w : I.ι ≫ g = I.ι ≫ h) (n : ℕ) :
    HomologicalComplex.homologyMap ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map g) n =
      HomologicalComplex.homologyMap ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map h) n :=
  (F.mapHomotopy (descHomotopy' g h w)).homologyMap_eq n

end InjectiveResolution

end CategoryTheory

end
