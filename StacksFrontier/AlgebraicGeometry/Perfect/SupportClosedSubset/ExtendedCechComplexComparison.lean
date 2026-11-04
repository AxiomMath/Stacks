module

public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.Acyclicity
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.GlobalEquationsComplexData

/-!
# Any two extended alternating Čech complexes of the same equations agree

The extended alternating Čech complex of Stacks 0G7I is specified rather than constructed: the
data consists of the complex itself, the identification of its degree-`0` term with the
coefficient module, the identification of its degree-`p + 1` term with the product of the direct
images of the restrictions to the `(p + 1)`-fold principal intersections, and the sectionwise
formulas for the differentials.  This file shows that the specification determines the complex
up to a canonical isomorphism: two complexes satisfying it are isomorphic by the comparison of
the degree-`0` identifications in degree `0` and of the term identifications in each positive
degree.

As a consequence the acyclicity of Stacks 0G7K, proved for one inhabitant of the specification,
is available for every inhabitant.

## Main definitions

* `comparisonIso`: the comparison isomorphism between two complexes satisfying the specification
  of Stacks 0G7I.
* `ofData`: the specification of Stacks 0G7I read in the vocabulary in which the augmentation of
  Stacks 0G7L is stated.

## Main results

* `acyclic_restrict`: every complex satisfying the specification is acyclic after restriction to
  the union of the principal opens of the equations, which is Stacks 0G7K for an arbitrary
  inhabitant.

## Implementation notes

The specification occurs in this library in two namespaces whose fields have the same types:
`AlgebraicGeometry.ExtendedAlternatingCech.Data`, which carries the acyclicity of Stacks 0G7K,
and `Stacks.Perfect.ExtendedAlternatingCech.ExtendedAlternatingCechData`, which carries the
augmentation of Stacks 0G7L and the comparison of Stacks 0G7M.  The auxiliary notions they refer
to — the principal intersections `equationsOpen`, the direct images `restrictedModule` and the
sectionwise identification `restrictedModuleSection` — are given by the same definition in the
two namespaces, hence are definitionally equal, so `ofData` converts one into the other by
transporting the fields unchanged.  The comparison itself is then stated and proved in a single
vocabulary, which is what keeps it free of transport.

That the comparison commutes with the differentials is checked on sections, where the
sectionwise formulas of the specification turn both sides into the same ordered Čech
differential.

## References

* [Stacks Project, Tag 0G7I](https://stacks.math.columbia.edu/tag/0G7I)
* [Stacks Project, Tag 0G7K](https://stacks.math.columbia.edu/tag/0G7K)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Perfect.ExtendedAlternatingCech
open scoped AlgebraicGeometry

universe u

namespace Stacks.Perfect.CechComplexComparison

variable {X : Scheme.{u}} {c : ℕ} {f : Fin c → Γ(X, ⊤)} {F : X.Modules}

/-- The specification of Stacks 0G7I, read in the vocabulary of Stacks 0G7L.  All the fields are
transported unchanged: the two spellings of the principal intersections and of the direct images
of the restrictions are given by the same definition. -/
public def ofData (D : AlgebraicGeometry.ExtendedAlternatingCech.Data f F) :
    ExtendedAlternatingCechData f F where
  complex := D.complex
  zeroIso := D.zeroIso
  termIso := D.termIso
  sectionsIso := D.sectionsIso
  sectionsIso_compat := D.sectionsIso_compat
  differential_zero := D.differential_zero
  differential_succ := D.differential_succ

variable (D D' : ExtendedAlternatingCechData f F)

/-- The comparison of two complexes satisfying the specification of Stacks 0G7I in a single
degree: the identification of the coefficient modules in degree `0`, and the identification of
the products of direct images in each positive degree. -/
public def comparisonX : ∀ n : ℕ, D.complex.X n ⟶ D'.complex.X n
  | 0 => D.zeroIso.hom ≫ D'.zeroIso.inv
  | p + 1 => (D.termIso p).hom ≫ (D'.termIso p).inv

/-- The comparison of two complexes satisfying the specification of Stacks 0G7I is an isomorphism
in each degree. -/
public instance isIso_comparisonX (n : ℕ) : IsIso (comparisonX D D' n) := by
  cases n with
  | zero => exact inferInstanceAs (IsIso (D.zeroIso.hom ≫ D'.zeroIso.inv))
  | succ p => exact inferInstanceAs (IsIso ((D.termIso p).hom ≫ (D'.termIso p).inv))

/-- Applying a composite of module maps to a section is applying the factors one after the
other. -/
private theorem app_apply_of_comp_eq {A B C : X.Modules} (f : A ⟶ B) (g : B ⟶ C) (h : A ⟶ C)
    (hfg : f ≫ g = h) (V : X.Opens) (x : Γ(A, V)) : g.app V (f.app V x) = h.app V x := by
  subst hfg
  rfl

/-- In degree `0` the comparison is compatible with the identifications of the coefficient
module. -/
public theorem comparisonX_zero_comp (V : X.Opens) (x : Γ(D.complex.X 0, V)) :
    D'.zeroIso.hom.app V ((comparisonX D D' 0).app V x) = D.zeroIso.hom.app V x :=
  app_apply_of_comp_eq _ _ _ (by
    change (D.zeroIso.hom ≫ D'.zeroIso.inv) ≫ D'.zeroIso.hom = D.zeroIso.hom
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]) V x

/-- In positive degrees the comparison is compatible with the sectionwise identifications. -/
public theorem comparisonX_succ_sectionsIso (p : ℕ) (V : X.Opens)
    (x : Γ(D.complex.X (p + 1), V)) :
    D'.sectionsIso p V ((comparisonX D D' (p + 1)).app V x) = D.sectionsIso p V x := by
  funext s
  rw [D'.sectionsIso_compat p V _ s, D.sectionsIso_compat p V x s]
  exact congrArg _ <| app_apply_of_comp_eq _ _ _ (by
    change ((D.termIso p).hom ≫ (D'.termIso p).inv) ≫ ((D'.termIso p).hom ≫ Pi.π _ s) = _
    rw [Category.assoc, Iso.inv_hom_id_assoc]) V x

/-- **The specification of Stacks 0G7I determines the extended alternating Čech complex.**  The
degreewise identifications of two complexes satisfying it form a map of complexes. -/
public def comparisonHom : D.complex ⟶ D'.complex where
  f := comparisonX D D'
  comm' i j hij := by
    obtain rfl : i + 1 = j := hij
    cases i with
    | zero =>
        refine Scheme.Modules.hom_ext _ _ fun V => ?_
        ext x
        refine (D'.sectionsIso 0 V).injective ?_
        funext s
        rw [show ((comparisonX D D' 0 ≫ D'.complex.d 0 1).app V) x =
            (D'.complex.d 0 1).app V ((comparisonX D D' 0).app V x) from rfl,
          show ((D.complex.d 0 1 ≫ comparisonX D D' 1).app V) x =
            (comparisonX D D' 1).app V ((D.complex.d 0 1).app V x) from rfl,
          D'.differential_zero V _ s, comparisonX_zero_comp D D' V x,
          comparisonX_succ_sectionsIso D D' 0 V ((D.complex.d 0 1).app V x),
          D.differential_zero V x s]
    | succ p =>
        refine Scheme.Modules.hom_ext _ _ fun V => ?_
        ext x
        refine (D'.sectionsIso (p + 1) V).injective ?_
        rw [show ((comparisonX D D' (p + 1) ≫ D'.complex.d (p + 1) (p + 2)).app V) x =
            (D'.complex.d (p + 1) (p + 2)).app V ((comparisonX D D' (p + 1)).app V x) from rfl,
          show ((D.complex.d (p + 1) (p + 2) ≫ comparisonX D D' (p + 2)).app V) x =
            (comparisonX D D' (p + 2)).app V ((D.complex.d (p + 1) (p + 2)).app V x) from rfl,
          D'.differential_succ p V _,
          comparisonX_succ_sectionsIso D D' p V x,
          comparisonX_succ_sectionsIso D D' (p + 1) V ((D.complex.d (p + 1) (p + 2)).app V x),
          D.differential_succ p V x]

/-- The comparison of two complexes satisfying the specification of Stacks 0G7I is an isomorphism
of complexes. -/
public instance isIso_comparisonHom : IsIso (comparisonHom D D') := by
  have : ∀ n, IsIso ((comparisonHom D D').f n) := fun n => isIso_comparisonX D D' n
  exact HomologicalComplex.Hom.isIso_of_components _

/-- The comparison of two complexes satisfying the specification of Stacks 0G7I, as an
isomorphism of complexes. -/
public def comparisonIso : D.complex ≅ D'.complex :=
  asIso (comparisonHom D D')

/-- Two complexes satisfying the specification of Stacks 0G7I have isomorphic restrictions to an
open subscheme. -/
public def restrictComparisonIso (U : X.Opens) :
    ((Scheme.Modules.pullback U.ι).mapHomologicalComplex (ComplexShape.up ℕ)).obj D.complex ≅
      ((Scheme.Modules.pullback U.ι).mapHomologicalComplex (ComplexShape.up ℕ)).obj D'.complex :=
  ((Scheme.Modules.pullback U.ι).mapHomologicalComplex (ComplexShape.up ℕ)).mapIso
    (comparisonIso D D')

/-- **Stacks Project, Tag 0G7K, for an arbitrary complex satisfying the specification of Stacks
0G7I.**  The restriction of the complex to the union of the principal opens of the equations is
acyclic. -/
public theorem acyclic_restrict :
    (((Scheme.Modules.pullback (⨆ i, X.basicOpen (f i)).ι).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj D.complex).Acyclic := by
  have hA := AlgebraicGeometry.ExtendedAlternatingCech.acyclic_on_equationsComplement f F
  rw [HomologicalComplex.acyclic_iff] at hA ⊢
  intro n
  refine ((HomologicalComplex.exactAt_iff_isZero_homology _ n).2 ?_)
  refine IsZero.of_iso ((HomologicalComplex.exactAt_iff_isZero_homology _ n).1 (hA n)) ?_
  exact (HomologicalComplex.homologyFunctor _ (ComplexShape.up ℕ) n).mapIso
    (restrictComparisonIso D (ofData (AlgebraicGeometry.ExtendedAlternatingCech.data f F))
      (⨆ i, X.basicOpen (f i)))

end Stacks.Perfect.CechComplexComparison

end
