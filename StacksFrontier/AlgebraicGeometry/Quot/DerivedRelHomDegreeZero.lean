module

public import StacksFrontier.AlgebraicGeometry.Quot.LeftDerivedPullbackData
public import StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.LowerShriekDegreeZero
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategorySingleCompIso
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.DerivedPullbackTopDegree

/-!
# Degree-zero cohomology of the relative Hom functor of a left derived pullback datum

Let `P` be a pullback pseudofunctor datum of additive functors between abelian categories and
let `L` be its left derived datum on the derived categories.  For an object `E` of `D(M a₀)`,
a morphism `α : E ⟶ F[0]` and an object `G` of `M a₀`, degree-zero cohomology sends a morphism
`ψ : L(κ i)^*E ⟶ L(κ i)^*G[0]` to the morphism `(κ i)^*F ⟶ (κ i)^*G` obtained by reading
`H⁰(L(κ i)^*E)` as `(κ i)^*F` through `α`.  This file shows that, when `L(κ i)^*E` has no
cohomology in positive degrees and `α` induces an isomorphism on `H⁰` after every pullback, this
is a morphism of relative Hom functors: it is natural in the test object.

## Main definitions

* `CategoryTheory.PullbackData.singleComparison`: the comparison `L f (N[0]) ⟶ (f^*N)[0]` of the
  left derived functor at an object placed in degree zero.
* `CategoryTheory.PullbackData.degreeZeroBaseChange`: the comparison `H⁰(L f Z) ⟶ f^*H⁰(Z)` for
  `Z` with no cohomology in positive degrees.
* `CategoryTheory.PullbackData.degreeZeroCompare`: the comparison `H⁰(L(κ i)^*E) ⟶ (κ i)^*F`
  induced by `α : E ⟶ F[0]`.
* `CategoryTheory.PullbackData.relHomDegreeZero`: the morphism of relative Hom functors.

## Main results

* `CategoryTheory.PullbackData.singleComparison_triangle`: the comparison at objects placed in
  degree zero is compatible with the comparisons of the left derived and the underived data.
* `CategoryTheory.PullbackData.relHomDegreeZero_naturality`: the naturality of degree-zero
  cohomology in the test object.

## References

* [Stacks Project, Tag 08JY](https://stacks.math.columbia.edu/tag/08JY)
-/

@[expose] public noncomputable section

open CategoryTheory Category Limits

namespace CategoryTheory.PullbackData


section DegreeZero

universe v₁ u₁ v₂ u₂

variable {A : Type u₁} [Category.{v₁} A] {M : A → Type u₂} [∀ a, Category.{v₂} (M a)]
  [∀ a, Abelian (M a)] [∀ a, HasDerivedCategory.{v₂} (M a)]
  (P : PullbackData A M) [∀ {a b : A} (f : a ⟶ b), (P.pull f).Additive]
  (L : ∀ {a b : A}, (a ⟶ b) → (DerivedCategory (M b) ⥤ DerivedCategory (M a)))
  (c : ∀ {a b : A} (f : a ⟶ b),
    DerivedCategory.Qh ⋙ L f ⟶ (P.toHomotopy).pull f ⋙ DerivedCategory.Qh)

/-- The comparison `L f (N[0]) ⟶ (f^*N)[0]` of the left derived functor at an object placed in
degree zero. -/
def singleComparison {a b : A} (f : a ⟶ b) (N : M b) :
    (L f).obj ((DerivedCategory.singleFunctor (M b) 0).obj N) ⟶
      (DerivedCategory.singleFunctor (M a) 0).obj ((P.pull f).obj N) :=
  (L f).map ((DerivedCategory.quotientCompQhIso (M b)).inv.app
      ((HomologicalComplex.single (M b) (ComplexShape.up ℤ) 0).obj N)) ≫
    (c f).app ((HomotopyCategory.quotient (M b) (ComplexShape.up ℤ)).obj
      ((HomologicalComplex.single (M b) (ComplexShape.up ℤ) 0).obj N)) ≫
    DerivedCategory.Qh.map ((HomotopyCategory.quotient (M a) (ComplexShape.up ℤ)).map
      ((HomologicalComplex.singleMapHomologicalComplex (P.pull f) (ComplexShape.up ℤ) 0).hom.app
        N)) ≫
    (DerivedCategory.quotientCompQhIso (M a)).hom.app
      ((HomologicalComplex.single (M a) (ComplexShape.up ℤ) 0).obj ((P.pull f).obj N))

/-- The comparison at objects placed in degree zero is natural. -/
theorem singleComparison_naturality {a b : A} (f : a ⟶ b) {N N' : M b} (u : N ⟶ N') :
    (L f).map ((DerivedCategory.singleFunctor (M b) 0).map u) ≫ singleComparison P L c f N' =
      singleComparison P L c f N ≫
        (DerivedCategory.singleFunctor (M a) 0).map ((P.pull f).map u) := by
  have h1 := (DerivedCategory.quotientCompQhIso (M b)).inv.naturality
    ((HomologicalComplex.single (M b) (ComplexShape.up ℤ) 0).map u)
  have h2 := (c f).naturality ((HomotopyCategory.quotient (M b) (ComplexShape.up ℤ)).map
    ((HomologicalComplex.single (M b) (ComplexShape.up ℤ) 0).map u))
  have h3 := (HomologicalComplex.singleMapHomologicalComplex (P.pull f)
    (ComplexShape.up ℤ) 0).hom.naturality u
  have h4 := (DerivedCategory.quotientCompQhIso (M a)).hom.naturality
    ((HomologicalComplex.single (M a) (ComplexShape.up ℤ) 0).map ((P.pull f).map u))
  dsimp only [Functor.comp_obj, Functor.comp_map] at h1 h2 h3 h4
  have e0 : (DerivedCategory.singleFunctor (M b) 0).map u =
      DerivedCategory.Q.map ((HomologicalComplex.single (M b) (ComplexShape.up ℤ) 0).map u) := rfl
  have e1 : (DerivedCategory.singleFunctor (M a) 0).map ((P.pull f).map u) =
      DerivedCategory.Q.map ((HomologicalComplex.single (M a) (ComplexShape.up ℤ) 0).map
        ((P.pull f).map u)) := rfl
  have e2 : (P.toHomotopy.pull f).map ((HomotopyCategory.quotient (M b) (ComplexShape.up ℤ)).map
      ((HomologicalComplex.single (M b) (ComplexShape.up ℤ) 0).map u)) =
      (HomotopyCategory.quotient (M a) (ComplexShape.up ℤ)).map
        (((P.pull f).mapHomologicalComplex (ComplexShape.up ℤ)).map
          ((HomologicalComplex.single (M b) (ComplexShape.up ℤ) 0).map u)) := rfl
  simp only [singleComparison, Category.assoc]
  have h6 : DerivedCategory.Qh.map ((HomotopyCategory.quotient (M a) (ComplexShape.up ℤ)).map
        (((P.pull f).mapHomologicalComplex (ComplexShape.up ℤ)).map
          ((HomologicalComplex.single (M b) (ComplexShape.up ℤ) 0).map u))) ≫
      DerivedCategory.Qh.map ((HomotopyCategory.quotient (M a) (ComplexShape.up ℤ)).map
        ((HomologicalComplex.singleMapHomologicalComplex (P.pull f) (ComplexShape.up ℤ) 0).hom.app
          N')) ≫
      (DerivedCategory.quotientCompQhIso (M a)).hom.app
        ((HomologicalComplex.single (M a) (ComplexShape.up ℤ) 0).obj ((P.pull f).obj N')) =
      DerivedCategory.Qh.map ((HomotopyCategory.quotient (M a) (ComplexShape.up ℤ)).map
        ((HomologicalComplex.singleMapHomologicalComplex (P.pull f) (ComplexShape.up ℤ) 0).hom.app
          N)) ≫
      (DerivedCategory.quotientCompQhIso (M a)).hom.app
        ((HomologicalComplex.single (M a) (ComplexShape.up ℤ) 0).obj ((P.pull f).obj N)) ≫
      DerivedCategory.Q.map ((HomologicalComplex.single (M a) (ComplexShape.up ℤ) 0).map
        ((P.pull f).map u)) := by
    rw [← Functor.map_comp_assoc, ← Functor.map_comp, h3, Functor.map_comp, Functor.map_comp,
      Category.assoc, h4]
  rw [e0, e1, ← Functor.map_comp_assoc, h1, Functor.map_comp_assoc, reassoc_of% h2, e2]
  exact congrArg (fun t => (L f).map ((DerivedCategory.quotientCompQhIso (M b)).inv.app
      ((HomologicalComplex.single (M b) (ComplexShape.up ℤ) 0).obj N)) ≫
    (c f).app ((HomotopyCategory.quotient (M b) (ComplexShape.up ℤ)).obj
      ((HomologicalComplex.single (M b) (ComplexShape.up ℤ) 0).obj N)) ≫ t) h6

open Stacks.Sites.FibredCategory in
/-- The canonical morphism `Z ⟶ H⁰(Z)[0]` of an object with no cohomology in positive degrees. -/
def toSingleHomology {a : A} (Z : DerivedCategory (M a)) [Z.IsLE 0] :
    Z ⟶ (DerivedCategory.singleFunctor (M a) 0).obj
      ((DerivedCategory.homologyFunctor (M a) 0).obj Z) :=
  (homologyHomEquiv Z _).symm (𝟙 _)

omit [Category.{v₁} A] in
open Stacks.Sites.FibredCategory in
/-- Degree-zero cohomology of `Z ⟶ H⁰(Z)[0]` is the identity. -/
theorem homologyHomFun_toSingleHomology {a : A} (Z : DerivedCategory (M a)) [Z.IsLE 0] :
    homologyHomFun Z _ (toSingleHomology Z) = 𝟙 _ :=
  (homologyHomEquiv Z _).apply_symm_apply _

omit [Category.{v₁} A] in
open Stacks.Sites.FibredCategory in
/-- A morphism from an object with no cohomology in positive degrees to an object placed in
degree zero factors through `Z ⟶ H⁰(Z)[0]`. -/
theorem eq_toSingleHomology_comp {a : A} (Z : DerivedCategory (M a)) [Z.IsLE 0] {Y : M a}
    (ζ : Z ⟶ (DerivedCategory.singleFunctor (M a) 0).obj Y) :
    ζ = toSingleHomology Z ≫ (DerivedCategory.singleFunctor (M a) 0).map (homologyHomFun Z Y ζ) :=
  (homologyHomEquiv Z Y).injective (by
    rw [homologyHomEquiv_apply, homologyHomEquiv_apply, homologyHomFun_comp_right,
      homologyHomFun_toSingleHomology, Category.id_comp])

open Stacks.Sites.FibredCategory in
/-- The comparison `H⁰(L f Z) ⟶ f^*H⁰(Z)` for `Z` with no cohomology in positive degrees. -/
def degreeZeroBaseChange {a b : A} (f : a ⟶ b) (Z : DerivedCategory (M b)) [Z.IsLE 0] :
    (DerivedCategory.homologyFunctor (M a) 0).obj ((L f).obj Z) ⟶
      (P.pull f).obj ((DerivedCategory.homologyFunctor (M b) 0).obj Z) :=
  homologyHomFun ((L f).obj Z) _ ((L f).map (toSingleHomology Z) ≫ singleComparison P L c f _)

open Stacks.Sites.FibredCategory in
/-- Degree-zero cohomology of `L f ζ` followed by the comparison `L f (Y[0]) ⟶ (f^*Y)[0]`, for
`ζ : Z ⟶ Y[0]`, is the comparison `H⁰(L f Z) ⟶ f^*H⁰(Z)` followed by `f^*H⁰(ζ)`. -/
theorem homologyHomFun_map_comp_singleComparison {a b : A} (f : a ⟶ b)
    (Z : DerivedCategory (M b)) [Z.IsLE 0] {Y : M b}
    (ζ : Z ⟶ (DerivedCategory.singleFunctor (M b) 0).obj Y) :
    homologyHomFun ((L f).obj Z) ((P.pull f).obj Y) ((L f).map ζ ≫ singleComparison P L c f Y) =
      degreeZeroBaseChange P L c f Z ≫ (P.pull f).map (homologyHomFun Z Y ζ) := by
  conv_lhs => rw [eq_toSingleHomology_comp Z ζ]
  rw [Functor.map_comp, Category.assoc, singleComparison_naturality, ← Category.assoc,
    homologyHomFun_comp_right]
  rfl

variable [hL : ∀ {a b : A} (f : a ⟶ b),
    (L f).IsLeftDerivedFunctor (c f) (HomotopyCategory.quasiIso (M b) (ComplexShape.up ℤ))]
  [hcomp : ∀ {a b d : A} (f : a ⟶ b) (g : b ⟶ d),
    IsIso (derivedComp (fun _ => DerivedCategory.Qh)
      (fun a => HomotopyCategory.quasiIso (M a) (ComplexShape.up ℤ)) P.toHomotopy L c f g)]
  [hid : ∀ a : A, IsIso (derivedIdLift (fun _ => DerivedCategory.Qh)
      (fun a => HomotopyCategory.quasiIso (M a) (ComplexShape.up ℤ)) P.toHomotopy L c a)]

omit [∀ a, HasDerivedCategory.{v₂} (M a)] in
/-- The comparisons of `HomologicalComplex.single` with the pullbacks along `g`, `f` and
`k = f ≫ g` are compatible with the comparison `P.triangle hk` of the datum. -/
theorem singleMapHomologicalComplex_triangle {a b d : A} {f : a ⟶ b} {g : b ⟶ d} {k : a ⟶ d}
    (hk : f ≫ g = k) (N : M d) :
    ((P.pull f).mapHomologicalComplex (ComplexShape.up ℤ)).map
        ((HomologicalComplex.singleMapHomologicalComplex (P.pull g) (ComplexShape.up ℤ) 0).hom.app
          N) ≫
      (HomologicalComplex.singleMapHomologicalComplex (P.pull f) (ComplexShape.up ℤ) 0).hom.app
          ((P.pull g).obj N) ≫
        (HomologicalComplex.single (M a) (ComplexShape.up ℤ) 0).map ((P.triangle hk).inv.app N) =
      (NatTrans.mapHomologicalComplex (P.triangle hk).inv (ComplexShape.up ℤ)).app
          ((HomologicalComplex.single (M d) (ComplexShape.up ℤ) 0).obj N) ≫
        (HomologicalComplex.singleMapHomologicalComplex (P.pull k) (ComplexShape.up ℤ) 0).hom.app
          N := by
  rw [HomologicalComplex.singleMapHomologicalComplex_natTrans, ← Category.assoc,
    HomologicalComplex.singleMapHomologicalComplex_comp]

/-- The comparison `L k (N[0]) ⟶ (k^*N)[0]` for `k = f ≫ g` is compatible with the comparisons
`P.triangle hk` of the datum and of its left derived datum. -/
theorem singleComparison_triangle {a b d : A} {f : a ⟶ b} {g : b ⟶ d} {k : a ⟶ d}
    (hk : f ≫ g = k) (N : M d) :
    ((leftDerived (fun _ => DerivedCategory.Qh)
        (fun a => HomotopyCategory.quasiIso (M a) (ComplexShape.up ℤ)) P.toHomotopy L c).triangle
          hk).inv.app ((DerivedCategory.singleFunctor (M d) 0).obj N) ≫
        singleComparison P L c k N =
      (L f).map (singleComparison P L c g N) ≫ singleComparison P L c f ((P.pull g).obj N) ≫
        (DerivedCategory.singleFunctor (M a) 0).map ((P.triangle hk).inv.app N) := by
  have n1 : (L f).map ((L g).map ((DerivedCategory.quotientCompQhIso (M d)).inv.app
        ((HomologicalComplex.single (M d) (ComplexShape.up ℤ) 0).obj N))) ≫
      ((leftDerived (fun _ => DerivedCategory.Qh)
        (fun a => HomotopyCategory.quasiIso (M a) (ComplexShape.up ℤ)) P.toHomotopy L c).triangle
          hk).inv.app (DerivedCategory.Qh.obj ((HomotopyCategory.quotient (M d)
            (ComplexShape.up ℤ)).obj ((HomologicalComplex.single (M d) (ComplexShape.up ℤ) 0).obj
              N))) =
      ((leftDerived (fun _ => DerivedCategory.Qh)
        (fun a => HomotopyCategory.quasiIso (M a) (ComplexShape.up ℤ)) P.toHomotopy L c).triangle
          hk).inv.app ((DerivedCategory.singleFunctor (M d) 0).obj N) ≫
        (L k).map ((DerivedCategory.quotientCompQhIso (M d)).inv.app
          ((HomologicalComplex.single (M d) (ComplexShape.up ℤ) 0).obj N)) :=
    ((leftDerived (fun _ => DerivedCategory.Qh)
      (fun a => HomotopyCategory.quasiIso (M a) (ComplexShape.up ℤ)) P.toHomotopy L c).triangle
        hk).inv.naturality ((DerivedCategory.quotientCompQhIso (M d)).inv.app
          ((HomologicalComplex.single (M d) (ComplexShape.up ℤ) 0).obj N))
  have n2 := leftDerived_triangle_inv_fac (fun _ => DerivedCategory.Qh)
    (fun a => HomotopyCategory.quasiIso (M a) (ComplexShape.up ℤ)) P.toHomotopy L c hk
      ((HomotopyCategory.quotient (M d) (ComplexShape.up ℤ)).obj
        ((HomologicalComplex.single (M d) (ComplexShape.up ℤ) 0).obj N))
  have n4 := (c f).naturality ((HomotopyCategory.quotient (M b) (ComplexShape.up ℤ)).map
    ((HomologicalComplex.singleMapHomologicalComplex (P.pull g) (ComplexShape.up ℤ) 0).hom.app N))
  simp only [singleComparison, Functor.map_comp, Category.assoc]
  rw [← reassoc_of% n1, reassoc_of% n2]
  have htail : DerivedCategory.Qh.map ((P.toHomotopy.triangle hk).inv.app
        ((HomotopyCategory.quotient (M d) (ComplexShape.up ℤ)).obj
          ((HomologicalComplex.single (M d) (ComplexShape.up ℤ) 0).obj N))) ≫
      DerivedCategory.Qh.map ((HomotopyCategory.quotient (M a) (ComplexShape.up ℤ)).map
        ((HomologicalComplex.singleMapHomologicalComplex (P.pull k) (ComplexShape.up ℤ) 0).hom.app
          N)) ≫
      (DerivedCategory.quotientCompQhIso (M a)).hom.app
        ((HomologicalComplex.single (M a) (ComplexShape.up ℤ) 0).obj ((P.pull k).obj N)) =
      DerivedCategory.Qh.map ((P.toHomotopy.pull f).map
        ((HomotopyCategory.quotient (M b) (ComplexShape.up ℤ)).map
          ((HomologicalComplex.singleMapHomologicalComplex (P.pull g) (ComplexShape.up ℤ) 0).hom.app
            N))) ≫
      DerivedCategory.Qh.map ((HomotopyCategory.quotient (M a) (ComplexShape.up ℤ)).map
        ((HomologicalComplex.singleMapHomologicalComplex (P.pull f) (ComplexShape.up ℤ) 0).hom.app
          ((P.pull g).obj N))) ≫
      (DerivedCategory.quotientCompQhIso (M a)).hom.app
        ((HomologicalComplex.single (M a) (ComplexShape.up ℤ) 0).obj
          ((P.pull f).obj ((P.pull g).obj N))) ≫
      (DerivedCategory.singleFunctor (M a) 0).map ((P.triangle hk).inv.app N) := by
    have n5 := (DerivedCategory.quotientCompQhIso (M a)).hom.naturality
      ((HomologicalComplex.single (M a) (ComplexShape.up ℤ) 0).map ((P.triangle hk).inv.app N))
    have e5 : (DerivedCategory.singleFunctor (M a) 0).map ((P.triangle hk).inv.app N) =
        DerivedCategory.Q.map ((HomologicalComplex.single (M a) (ComplexShape.up ℤ) 0).map
          ((P.triangle hk).inv.app N)) := rfl
    have hc := singleMapHomologicalComplex_triangle P hk N
    dsimp only [Functor.comp_obj, Functor.comp_map] at n5
    have e6 : (P.toHomotopy.pull f).map ((HomotopyCategory.quotient (M b) (ComplexShape.up ℤ)).map
        ((HomologicalComplex.singleMapHomologicalComplex (P.pull g) (ComplexShape.up ℤ) 0).hom.app
          N)) = (HomotopyCategory.quotient (M a) (ComplexShape.up ℤ)).map
        (((P.pull f).mapHomologicalComplex (ComplexShape.up ℤ)).map
          ((HomologicalComplex.singleMapHomologicalComplex (P.pull g) (ComplexShape.up ℤ) 0).hom.app
            N)) := rfl
    have key := congrArg (fun t => DerivedCategory.Qh.map
      ((HomotopyCategory.quotient (M a) (ComplexShape.up ℤ)).map t) ≫
        (DerivedCategory.quotientCompQhIso (M a)).hom.app
          ((HomologicalComplex.single (M a) (ComplexShape.up ℤ) 0).obj ((P.pull k).obj N))) hc
    simp only [Functor.map_comp, Category.assoc] at key
    rw [toHomotopy_triangle_inv_app, e5, ← n5, e6]
    exact key.symm
  rw [← Functor.map_comp_assoc (L f) ((DerivedCategory.quotientCompQhIso (M b)).hom.app _),
    Iso.hom_inv_id_app, Functor.map_id, Category.id_comp]
  refine (congrArg (fun t => (L f).map ((L g).map ((DerivedCategory.quotientCompQhIso (M d)).inv.app
        ((HomologicalComplex.single (M d) (ComplexShape.up ℤ) 0).obj N))) ≫
      (L f).map ((c g).app ((HomotopyCategory.quotient (M d) (ComplexShape.up ℤ)).obj
        ((HomologicalComplex.single (M d) (ComplexShape.up ℤ) 0).obj N))) ≫
      (c f).app ((P.toHomotopy.pull g).obj
        ((HomotopyCategory.quotient (M d) (ComplexShape.up ℤ)).obj
          ((HomologicalComplex.single (M d) (ComplexShape.up ℤ) 0).obj N))) ≫ t) htail).trans ?_
  beta_reduce
  have n4' : (c f).app ((P.toHomotopy.pull g).obj ((HomotopyCategory.quotient (M d)
      (ComplexShape.up ℤ)).obj ((HomologicalComplex.single (M d) (ComplexShape.up ℤ) 0).obj N))) ≫
      DerivedCategory.Qh.map ((P.toHomotopy.pull f).map
        ((HomotopyCategory.quotient (M b) (ComplexShape.up ℤ)).map
          ((HomologicalComplex.singleMapHomologicalComplex (P.pull g) (ComplexShape.up ℤ) 0).hom.app
            N))) =
      (L f).map (DerivedCategory.Qh.map ((HomotopyCategory.quotient (M b) (ComplexShape.up ℤ)).map
          ((HomologicalComplex.singleMapHomologicalComplex (P.pull g) (ComplexShape.up ℤ) 0).hom.app
            N))) ≫
        (c f).app ((HomotopyCategory.quotient (M b) (ComplexShape.up ℤ)).obj
          ((HomologicalComplex.single (M b) (ComplexShape.up ℤ) 0).obj ((P.pull g).obj N))) :=
    ((c f).naturality ((HomotopyCategory.quotient (M b) (ComplexShape.up ℤ)).map
      ((HomologicalComplex.singleMapHomologicalComplex (P.pull g) (ComplexShape.up ℤ) 0).hom.app
        N))).symm
  have h7 : (c f).app ((P.toHomotopy.pull g).obj ((HomotopyCategory.quotient (M d)
      (ComplexShape.up ℤ)).obj ((HomologicalComplex.single (M d) (ComplexShape.up ℤ) 0).obj N))) ≫
      DerivedCategory.Qh.map ((P.toHomotopy.pull f).map
        ((HomotopyCategory.quotient (M b) (ComplexShape.up ℤ)).map
          ((HomologicalComplex.singleMapHomologicalComplex (P.pull g) (ComplexShape.up ℤ) 0).hom.app
            N))) ≫ DerivedCategory.Qh.map ((HomotopyCategory.quotient (M a) (ComplexShape.up ℤ)).map
        ((HomologicalComplex.singleMapHomologicalComplex (P.pull f) (ComplexShape.up ℤ) 0).hom.app
          ((P.pull g).obj N))) ≫
      (DerivedCategory.quotientCompQhIso (M a)).hom.app
        ((HomologicalComplex.single (M a) (ComplexShape.up ℤ) 0).obj
          ((P.pull f).obj ((P.pull g).obj N))) ≫
      (DerivedCategory.singleFunctor (M a) 0).map ((P.triangle hk).inv.app N) =
      (L f).map (DerivedCategory.Qh.map ((HomotopyCategory.quotient (M b) (ComplexShape.up ℤ)).map
          ((HomologicalComplex.singleMapHomologicalComplex (P.pull g) (ComplexShape.up ℤ) 0).hom.app
            N))) ≫
        (c f).app ((HomotopyCategory.quotient (M b) (ComplexShape.up ℤ)).obj
          ((HomologicalComplex.single (M b) (ComplexShape.up ℤ) 0).obj ((P.pull g).obj N))) ≫
      DerivedCategory.Qh.map ((HomotopyCategory.quotient (M a) (ComplexShape.up ℤ)).map
        ((HomologicalComplex.singleMapHomologicalComplex (P.pull f) (ComplexShape.up ℤ) 0).hom.app
          ((P.pull g).obj N))) ≫
      (DerivedCategory.quotientCompQhIso (M a)).hom.app
        ((HomologicalComplex.single (M a) (ComplexShape.up ℤ) 0).obj
          ((P.pull f).obj ((P.pull g).obj N))) ≫
      (DerivedCategory.singleFunctor (M a) 0).map ((P.triangle hk).inv.app N) := by
    rw [← Category.assoc, n4']
    exact Category.assoc _ _ _
  exact congrArg (fun t => (L f).map ((L g).map ((DerivedCategory.quotientCompQhIso (M d)).inv.app
        ((HomologicalComplex.single (M d) (ComplexShape.up ℤ) 0).obj N))) ≫
      (L f).map ((c g).app ((HomotopyCategory.quotient (M d) (ComplexShape.up ℤ)).obj
        ((HomologicalComplex.single (M d) (ComplexShape.up ℤ) 0).obj N))) ≫ t) h7

/-- The restriction map of the relative Hom functor of the left derived datum is conjugation by
the comparison `P.triangle`. -/
private theorem leftDerived_relHomMap_eq {I : Type*} [Category* I] {π : I ⥤ A} {a₀ : A}
    (κ : ConeTo π a₀) (E E' : DerivedCategory (M a₀)) {j i : I} (g : j ⟶ i)
    (ψ : (L (κ.leg i)).obj E ⟶ (L (κ.leg i)).obj E') :
    (leftDerived (fun _ => DerivedCategory.Qh)
        (fun a => HomotopyCategory.quasiIso (M a) (ComplexShape.up ℤ)) P.toHomotopy L c).relHomMap
          κ E E' g ψ =
      ((leftDerived (fun _ => DerivedCategory.Qh)
        (fun a => HomotopyCategory.quasiIso (M a) (ComplexShape.up ℤ)) P.toHomotopy L c).triangle
          (κ.w g)).hom.app E ≫ (L (π.map g)).map ψ ≫
      ((leftDerived (fun _ => DerivedCategory.Qh)
        (fun a => HomotopyCategory.quasiIso (M a) (ComplexShape.up ℤ)) P.toHomotopy L c).triangle
          (κ.w g)).inv.app E' := rfl

variable {I : Type*} [Category* I] {π : I ⥤ A} {a₀ : A} (κ : ConeTo π a₀)
  (E : DerivedCategory (M a₀)) {F : M a₀} (α : E ⟶ (DerivedCategory.singleFunctor (M a₀) 0).obj F)
  [hZ : ∀ i : I, ((L (κ.leg i)).obj E).IsLE 0]

omit hL hcomp hid hZ in
open Stacks.Sites.FibredCategory in
/-- The comparison `H⁰(L(κ i)^*E) ⟶ (κ i)^*F` induced by `α : E ⟶ F[0]`. -/
def degreeZeroCompare (i : I) :
    (DerivedCategory.homologyFunctor (M (π.obj i)) 0).obj ((L (κ.leg i)).obj E) ⟶
      (P.pull (κ.leg i)).obj F :=
  homologyHomFun _ _ ((L (κ.leg i)).map α ≫ singleComparison P L c (κ.leg i) F)

open Stacks.Sites.FibredCategory in
/-- For `g : j ⟶ i` and `ψ : L(κ i)^*E ⟶ L(κ i)^*G[0]`, degree-zero cohomology of the restriction
of `ψ` along `g`, followed by the comparison at `G`, is expressed through degree-zero cohomology of
`ψ`, the comparison `H⁰(L f Z) ⟶ f^*H⁰(Z)` and the comparisons of the two data. -/
theorem degreeZeroCompare_relHom {j i : I} (g : j ⟶ i) {G : M a₀}
    (ψ : (L (κ.leg i)).obj E ⟶ (L (κ.leg i)).obj ((DerivedCategory.singleFunctor (M a₀) 0).obj G)) :
    homologyHomFun _ _ ((leftDerived (fun _ => DerivedCategory.Qh)
        (fun a => HomotopyCategory.quasiIso (M a) (ComplexShape.up ℤ)) P.toHomotopy L c).relHomMap
          κ E _ g ψ ≫ singleComparison P L c (κ.leg j) G) =
      (DerivedCategory.homologyFunctor (M (π.obj j)) 0).map
          (((leftDerived (fun _ => DerivedCategory.Qh)
            (fun a => HomotopyCategory.quasiIso (M a) (ComplexShape.up ℤ)) P.toHomotopy L
              c).triangle (κ.w g)).hom.app E) ≫
        degreeZeroBaseChange P L c (π.map g) ((L (κ.leg i)).obj E) ≫
          (P.pull (π.map g)).map (homologyHomFun _ _ (ψ ≫ singleComparison P L c (κ.leg i) G)) ≫
            (P.triangle (κ.w g)).inv.app G := by
  rw [leftDerived_relHomMap_eq P L c κ E]
  rw [Category.assoc, Category.assoc, singleComparison_triangle, ← Functor.map_comp_assoc,
    homologyHomFun_comp_left, ← Category.assoc ((L (π.map g)).map _),
    homologyHomFun_comp_right]
  exact (congrArg (fun t => (DerivedCategory.homologyFunctor (M (π.obj j)) 0).map
      (((leftDerived (fun _ => DerivedCategory.Qh)
        (fun a => HomotopyCategory.quasiIso (M a) (ComplexShape.up ℤ)) P.toHomotopy L c).triangle
          (κ.w g)).hom.app E) ≫ t ≫ (P.triangle (κ.w g)).inv.app G)
    (homologyHomFun_map_comp_singleComparison P L c (π.map g) ((L (κ.leg i)).obj E)
      (ψ ≫ singleComparison P L c (κ.leg i) G))).trans (by simp only [Category.assoc])

omit hZ in
/-- Restriction of the pullback of a morphism `β` of `D(M a₀)` is the pullback of `β`. -/
theorem leftDerived_relHomMap_map {j i : I} (g : j ⟶ i) {E' : DerivedCategory (M a₀)}
    (β : E ⟶ E') :
    (leftDerived (fun _ => DerivedCategory.Qh)
        (fun a => HomotopyCategory.quasiIso (M a) (ComplexShape.up ℤ)) P.toHomotopy L c).relHomMap
          κ E E' g ((L (κ.leg i)).map β) = (L (κ.leg j)).map β := by
  rw [leftDerived_relHomMap_eq P L c κ E]
  have h := ((leftDerived (fun _ => DerivedCategory.Qh)
      (fun a => HomotopyCategory.quasiIso (M a) (ComplexShape.up ℤ)) P.toHomotopy L c).triangle
        (κ.w g)).hom.naturality β
  dsimp only [Functor.comp_map] at h
  rw [← reassoc_of% h, Iso.hom_inv_id_app, Category.comp_id]

open Stacks.Sites.FibredCategory in
/-- For `g : j ⟶ i`, the comparison `H⁰(L(κ j)^*E) ⟶ (κ j)^*F` is the composite of `H⁰` of the
comparison of the left derived datum, the comparison `H⁰(L f Z) ⟶ f^*H⁰(Z)`, the pullback of the
comparison at `i`, and the comparison `P.triangle` of the datum. -/
theorem degreeZeroCompare_naturality {j i : I} (g : j ⟶ i) :
    degreeZeroCompare P L c κ E α j =
      (DerivedCategory.homologyFunctor (M (π.obj j)) 0).map
          (((leftDerived (fun _ => DerivedCategory.Qh)
            (fun a => HomotopyCategory.quasiIso (M a) (ComplexShape.up ℤ)) P.toHomotopy L
              c).triangle (κ.w g)).hom.app E) ≫
        degreeZeroBaseChange P L c (π.map g) ((L (κ.leg i)).obj E) ≫
          (P.pull (π.map g)).map (degreeZeroCompare P L c κ E α i) ≫
            (P.triangle (κ.w g)).inv.app F := by
  rw [degreeZeroCompare, ← leftDerived_relHomMap_map P L c κ E g α]
  exact degreeZeroCompare_relHom P L c κ E g _

variable [hθ : ∀ i : I, IsIso (degreeZeroCompare P L c κ E α i)]

open Stacks.Sites.FibredCategory in
/-- Degree-zero cohomology commutes with restriction along a transition morphism. -/
theorem relHomDegreeZero_naturality {j i : I} (g : j ⟶ i) {G : M a₀}
    (ψ : (L (κ.leg i)).obj E ⟶ (L (κ.leg i)).obj ((DerivedCategory.singleFunctor (M a₀) 0).obj G)) :
    inv (degreeZeroCompare P L c κ E α j) ≫ homologyHomFun _ _ ((leftDerived
        (fun _ => DerivedCategory.Qh) (fun a => HomotopyCategory.quasiIso (M a) (ComplexShape.up ℤ))
          P.toHomotopy L c).relHomMap κ E _ g ψ ≫ singleComparison P L c (κ.leg j) G) =
      P.relHomMap κ F G g (inv (degreeZeroCompare P L c κ E α i) ≫
        homologyHomFun _ _ (ψ ≫ singleComparison P L c (κ.leg i) G)) := by
  have key : inv (degreeZeroCompare P L c κ E α j) ≫
      (DerivedCategory.homologyFunctor (M (π.obj j)) 0).map
          (((leftDerived (fun _ => DerivedCategory.Qh)
            (fun a => HomotopyCategory.quasiIso (M a) (ComplexShape.up ℤ)) P.toHomotopy L
              c).triangle (κ.w g)).hom.app E) ≫
        degreeZeroBaseChange P L c (π.map g) ((L (κ.leg i)).obj E) =
      (P.triangle (κ.w g)).hom.app F ≫
        (P.pull (π.map g)).map (inv (degreeZeroCompare P L c κ E α i)) := by
    rw [IsIso.inv_comp_eq, degreeZeroCompare_naturality P L c κ E α g]
    simp only [Category.assoc, Iso.inv_hom_id_app_assoc, ← Functor.map_comp, IsIso.hom_inv_id,
      Functor.map_id, Category.comp_id]
  rw [degreeZeroCompare_relHom, ← Category.assoc, ← Category.assoc, ← Category.assoc,
    Category.assoc _ _ (degreeZeroBaseChange P L c (π.map g) _), key]
  show _ = (P.triangle (κ.w g)).hom.app F ≫ (P.pull (π.map g)).map _ ≫
    (P.triangle (κ.w g)).inv.app G
  simp only [Functor.map_comp, Category.assoc]

/-- Degree-zero cohomology as a morphism of relative Hom functors: it sends
`ψ : L(κ i)^*E ⟶ L(κ i)^*G[0]` to `H⁰(ψ)`, read as a morphism `(κ i)^*F ⟶ (κ i)^*G` through the
comparisons `H⁰(L(κ i)^*E) ≅ (κ i)^*F` induced by `α`. -/
def relHomDegreeZero (hP : P.IsCoherent) (G : M a₀) :
    (leftDerived (fun _ => DerivedCategory.Qh)
        (fun a => HomotopyCategory.quasiIso (M a) (ComplexShape.up ℤ)) P.toHomotopy L
          c).relHomFunctor
        (leftDerived_isCoherent _ _ _ _ _ (toHomotopy_isCoherent P hP)) κ E
        ((DerivedCategory.singleFunctor (M a₀) 0).obj G) ⟶ P.relHomFunctor hP κ F G where
  app i := ↾fun (ψ : (L (κ.leg i.unop)).obj E ⟶
      (L (κ.leg i.unop)).obj ((DerivedCategory.singleFunctor (M a₀) 0).obj G)) =>
    inv (degreeZeroCompare P L c κ E α i.unop) ≫
      Stacks.Sites.FibredCategory.homologyHomFun _ _
        (ψ ≫ singleComparison P L c (κ.leg i.unop) G)
  naturality _ _ g := ConcreteCategory.hom_ext _ _ fun ψ =>
    relHomDegreeZero_naturality P L c κ E α g.unop ψ

omit hL hcomp hid hZ hθ in
/-- For right exact pullbacks, `L f (N[0]) ⟶ (f^*N)[0]` induces an isomorphism on `H⁰` as soon as
`N[0]` has a resolution `p : G ⟶ N[0]` by a complex concentrated in degrees `≤ 0` at which the
comparison of `L f` with `f^*` is invertible. -/
theorem isIso_homology_singleComparison_of_resolution [∀ {a b : A} (f : a ⟶ b),
      PreservesFiniteColimits (P.pull f)] {a b : A} (f : a ⟶ b) (N : M b)
    (G : CochainComplex (M b) ℤ) (hG : G.IsStrictlyLE 0)
    (p : G ⟶ (HomologicalComplex.single (M b) (ComplexShape.up ℤ) 0).obj N) (hp : QuasiIso p)
    (hc : IsIso ((c f).app ((HomotopyCategory.quotient (M b) (ComplexShape.up ℤ)).obj G))) :
    IsIso ((DerivedCategory.homologyFunctor (M a) 0).map (singleComparison P L c f N)) := by
  have := hG
  have := hp
  have := hc
  have hQp : IsIso (DerivedCategory.Qh.map
      ((HomotopyCategory.quotient (M b) (ComplexShape.up ℤ)).map p)) :=
    (NatIso.isIso_map_iff (DerivedCategory.quotientCompQhIso (M b)) p).2
      ((DerivedCategory.isIso_Q_map_iff_quasiIso _ p).2 inferInstance)
  have h3 : IsIso ((DerivedCategory.homologyFunctor (M a) 0).map
      (DerivedCategory.Qh.map ((P.toHomotopy.pull f).map
        ((HomotopyCategory.quotient (M b) (ComplexShape.up ℤ)).map p)))) := by
    have hmap := Stacks.AlgebraicGeometry.TopDegreeBaseChange.isIso_homologyMap_map_of_isStrictlyLE
      (P.pull f) p 0 inferInstance inferInstance inferInstance
    exact (NatIso.isIso_map_iff (Functor.isoWhiskerLeft
        (HomotopyCategory.quotient (M a) (ComplexShape.up ℤ))
        (DerivedCategory.homologyFunctorFactorsh (M a) 0) ≪≫
      HomotopyCategory.homologyFunctorFactors _ _ 0) _).2 hmap
  have nat := (c f).naturality ((HomotopyCategory.quotient (M b) (ComplexShape.up ℤ)).map p)
  have hcomp : IsIso ((DerivedCategory.homologyFunctor (M a) 0).map
      ((L f).map (DerivedCategory.Qh.map ((HomotopyCategory.quotient (M b)
        (ComplexShape.up ℤ)).map p)) ≫
      (c f).app ((HomotopyCategory.quotient (M b) (ComplexShape.up ℤ)).obj
        ((HomologicalComplex.single (M b) (ComplexShape.up ℤ) 0).obj N)))) := by
    have nat' : (L f).map (DerivedCategory.Qh.map ((HomotopyCategory.quotient (M b)
        (ComplexShape.up ℤ)).map p)) ≫
      (c f).app ((HomotopyCategory.quotient (M b) (ComplexShape.up ℤ)).obj
        ((HomologicalComplex.single (M b) (ComplexShape.up ℤ) 0).obj N)) =
      (c f).app ((HomotopyCategory.quotient (M b) (ComplexShape.up ℤ)).obj G) ≫
        DerivedCategory.Qh.map ((P.toHomotopy.pull f).map
          ((HomotopyCategory.quotient (M b) (ComplexShape.up ℤ)).map p)) := nat
    rw [nat', Functor.map_comp]
    infer_instance
  rw [Functor.map_comp] at hcomp
  have i2 := IsIso.of_isIso_comp_left
    ((DerivedCategory.homologyFunctor (M a) 0).map ((L f).map (DerivedCategory.Qh.map
      ((HomotopyCategory.quotient (M b) (ComplexShape.up ℤ)).map p))))
    ((DerivedCategory.homologyFunctor (M a) 0).map ((c f).app
      ((HomotopyCategory.quotient (M b) (ComplexShape.up ℤ)).obj
        ((HomologicalComplex.single (M b) (ComplexShape.up ℤ) 0).obj N))))
  have i1 : IsIso ((DerivedCategory.homologyFunctor (M a) 0).map ((L f).map
      ((DerivedCategory.quotientCompQhIso (M b)).inv.app
        ((HomologicalComplex.single (M b) (ComplexShape.up ℤ) 0).obj N)))) := inferInstance
  have i3 : IsIso ((DerivedCategory.homologyFunctor (M a) 0).map (DerivedCategory.Qh.map
      ((HomotopyCategory.quotient (M a) (ComplexShape.up ℤ)).map
        ((HomologicalComplex.singleMapHomologicalComplex (P.pull f) (ComplexShape.up ℤ) 0).hom.app
          N)))) := inferInstance
  have i4 : IsIso ((DerivedCategory.homologyFunctor (M a) 0).map
      ((DerivedCategory.quotientCompQhIso (M a)).hom.app
        ((HomologicalComplex.single (M a) (ComplexShape.up ℤ) 0).obj ((P.pull f).obj N)))) :=
    inferInstance
  simp only [singleComparison, Functor.map_comp]
  exact IsIso.comp_isIso' i1 (IsIso.comp_isIso' i2 (IsIso.comp_isIso' i3 i4))

end DegreeZero

end CategoryTheory.PullbackData
