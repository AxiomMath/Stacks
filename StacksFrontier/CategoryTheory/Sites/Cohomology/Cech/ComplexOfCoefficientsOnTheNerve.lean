module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.FirstCocycles

/-!
# The Čech complex only sees the coefficients on the iterated fibre products

Let `E = {U_i → X}` be a family of morphisms of a category `C` whose finite nonempty iterated
fibre products exist, and let `F` and `F'` be abelian presheaves on `C`.  The Čech complex of
Stacks 03AM of `F` along `E` has as terms the products of the sections of `F` over the iterated
fibre products `U_{i_0} ×_X ⋯ ×_X U_{i_n}`, and as differential the alternating sums of the
restrictions along the face projections between them.  So it only depends on `F` at those
objects: if `F` and `F'` are identified on a class of objects containing every iterated fibre
product, compatibly with the restriction maps between objects of the class, then their Čech
complexes are isomorphic.

This is the form in which the Čech complex of a sheaf is computed from a model which agrees with
it only on part of the site, as when the sections of a module with the flat base change property
of Stacks 0762 are those of a quasi-coherent module on the objects lying flatly over a scheme.

## Main definitions

* `Stacks.CechSite.cechComplexIsoOfIsoOnNerve`: the isomorphism of Čech complexes induced by an
  identification of the coefficients on a class of objects containing the iterated fibre
  products.
* `Stacks.CechSite.cechCohomologyIsoOfIsoOnNerve`: the resulting isomorphism of Čech
  cohomology groups.

## References

* [Stacks Project, Tag 03AM](https://stacks.math.columbia.edu/tag/03AM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe a w v u

namespace Stacks.CechSite

variable {C : Type u} [Category.{v} C] {X : C} (E : PreZeroHypercover.{w} X)
  [HasProducts.{w} AddCommGrpCat.{a}]
  [∀ (n : ℕ) (i : Fin (n + 1) → E.I₀), HasProduct (fun j ↦ Over.mk (E.f (i j)))]
  {F F' : Cᵒᵖ ⥤ AddCommGrpCat.{a}} (Q : ObjectProperty C)
  (hQ : ∀ (n : ℕ) (k : Fin (n + 1) → E.I₀), Q (∏ᶜ (fun j ↦ Over.mk (E.f (k j)))).left)
  (e : ∀ Z : C, Q Z → (F.obj (op Z) ≅ F'.obj (op Z)))
  (he : ∀ {Z Z' : C} (hZ : Q Z) (hZ' : Q Z') (r : Z' ⟶ Z),
    F.map r.op ≫ (e Z' hZ').hom = (e Z hZ).hom ≫ F'.map r.op)

/-- The degree-`n` component of `Stacks.CechSite.cechComplexIsoOfIsoOnNerve`: the product of the
identifications at the iterated fibre products. -/
def cechComplexIsoOfIsoOnNerveX (n : ℕ) : (cechComplex E F).X n ≅ (cechComplex E F').X n :=
  (Pi.mapIso fun k : Fin (n + 1) → E.I₀ ↦ e _ (hQ n k) :
    (∏ᶜ cochainFactor E F n : AddCommGrpCat.{a}) ≅ ∏ᶜ cochainFactor E F' n)

/-- The factor of `Stacks.CechSite.cechComplexIsoOfIsoOnNerveX` indexed by `l` is the
identification at the iterated fibre product indexed by `l`. -/
lemma cechComplexIsoOfIsoOnNerveX_π (m : ℕ) (l : Fin (m + 1) → E.I₀)
    (y : (cechComplex E F).X m) :
    Pi.π (cochainFactor E F' m) l ((cechComplexIsoOfIsoOnNerveX E Q hQ e m).hom y) =
      (e _ (hQ m l)).hom (Pi.π (cochainFactor E F m) l y) :=
  ConcreteCategory.congr_hom (Pi.map_π (f := cochainFactor E F m) (g := cochainFactor E F' m)
    (fun k : Fin (m + 1) → E.I₀ ↦ (e _ (hQ m k)).hom) l) y

include he in
/-- `Stacks.CechSite.cechComplexIsoOfIsoOnNerveX_comm` on a single element and in a single
factor of the product in degree `n + 1`. -/
lemma cechComplexIsoOfIsoOnNerveX_comm_apply (n : ℕ) (k : Fin (n + 2) → E.I₀)
    (x : (cechComplex E F).X n) :
    Pi.π (cochainFactor E F' (n + 1)) k ((cechComplex E F').d n (n + 1)
      ((cechComplexIsoOfIsoOnNerveX E Q hQ e n).hom x)) =
    Pi.π (cochainFactor E F' (n + 1)) k ((cechComplexIsoOfIsoOnNerveX E Q hQ e (n + 1)).hom
      ((cechComplex E F).d n (n + 1) x)) := by
  rw [pi_π_differential_apply, cechComplexIsoOfIsoOnNerveX_π, pi_π_differential_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [map_zsmul, cechComplexIsoOfIsoOnNerveX_π]
  exact congrArg _ (ConcreteCategory.congr_hom (he (hQ n _) (hQ (n + 1) k)
    (faceProjection E k j).left) _).symm

include he in
/-- The degree-wise identifications `Stacks.CechSite.cechComplexIsoOfIsoOnNerveX` commute with the
Čech differentials, which is what makes them a map of complexes. -/
lemma cechComplexIsoOfIsoOnNerveX_comm (n : ℕ) :
    (cechComplexIsoOfIsoOnNerveX E Q hQ e n).hom ≫ (cechComplex E F').d n (n + 1) =
      (cechComplex E F).d n (n + 1) ≫ (cechComplexIsoOfIsoOnNerveX E Q hQ e (n + 1)).hom := by
  refine Pi.hom_ext (f := cochainFactor E F' (n + 1)) _ _ fun k ↦ ?_
  ext x
  exact cechComplexIsoOfIsoOnNerveX_comm_apply E Q hQ e he n k x

/-- **The Čech complex only depends on the coefficients at the iterated fibre products.**  An
identification of `F` with `F'` on a class of objects containing every iterated fibre product of
`E`, compatible with the restriction maps between objects of the class, induces an isomorphism of
Čech complexes, by the product of the identifications in each degree. -/
def cechComplexIsoOfIsoOnNerve : cechComplex E F ≅ cechComplex E F' :=
  HomologicalComplex.Hom.isoOfComponents (cechComplexIsoOfIsoOnNerveX E Q hQ e) (by
    rintro n _ rfl
    exact cechComplexIsoOfIsoOnNerveX_comm E Q hQ e he n)

/-- **Čech cohomology only depends on the coefficients at the iterated fibre products**, in the
sense of `Stacks.CechSite.cechComplexIsoOfIsoOnNerve`. -/
def cechCohomologyIsoOfIsoOnNerve (p : ℕ) : cechCohomology E F p ≅ cechCohomology E F' p :=
  (HomologicalComplex.homologyFunctor AddCommGrpCat.{a} (ComplexShape.up ℕ) p).mapIso
    (cechComplexIsoOfIsoOnNerve E Q hQ e he)

end Stacks.CechSite

end
