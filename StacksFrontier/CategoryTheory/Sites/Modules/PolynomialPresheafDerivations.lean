module

public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.MvPolynomial.Derivation
public import Mathlib.CategoryTheory.Sites.Equivalence
public import StacksFrontier.CategoryTheory.Sites.Modules.Differentials
public import StacksFrontier.CategoryTheory.Sites.Modules.FreeAlgebraSheaf

/-!
# Derivations of a presheaf of polynomial rings and of its sheafification

Let `A` be a sheaf of commutative rings on a site and let `E` be a presheaf of sets. The
presheaf of polynomial rings `U ↦ A(U)[E(U)]` of
`Stacks.Sites.FreeAlgebra.polynomialPresheaf` is free on `E` over `A` objectwise, so a
derivation of it over `A` is nothing but a prescription of the values at the variables; and a
sheaf of commutative rings receiving a locally bijective morphism from that presheaf — the free
algebra sheaf `A[E]`, in any of its spellings — has the same derivations with values in a
*sheaf* of modules, because a derivation extends uniquely along a local bijection.

## Main results

* `Stacks.SheafOfModules.isLocallyBijective_toSheafification_commRingCat`: the unit of the
  sheafification of a presheaf of commutative rings is locally bijective.
* `Stacks.SheafOfModules.exists_derivation_of_polynomialVariable`: for a locally bijective
  morphism `α` from the polynomial presheaf `A(-)[E(-)]` into a sheaf of rings `Q`, a morphism of
  presheaves of sets from the variables to a sheaf of `Q`-modules is the family of values at the
  variables of a derivation of `Q`.
* `Stacks.SheafOfModules.derivation_ext_of_polynomialVariable`: a derivation of such a sheaf of
  rings over `A` is determined by its values on the variables.

## Implementation notes

`StacksFrontier/CategoryTheory/Sites/Modules/InternalHomAndFlatness/NaiveCotangentExtClass.lean`
proves the special case of these facts that its degree-zero term needs, as private helpers
(the sheafification spelling of the free algebra sheaf only). The statements here are the forms
the computation of the differentials of a free algebra sheaf consumes: an arbitrary locally
bijective `α`, the two steps of the existence proof composed into one statement, and the
local bijectivity of the unit stated for the unit itself.

`derivation_ext_of_polynomialVariable` is stated for an arbitrary morphism
`α : A(-)[E(-)] ⟶ Q` of presheaves of commutative rings into a sheaf of rings, locally
surjective and compatible with the structural morphisms from `A`, rather than only for the unit
of the sheafification. That is what lets it apply to the coproduct spelling `A ⨿ ℤ[E]` of the
free algebra sheaf used by the standard resolution of [Stacks, Tag 08SR], which receives such an
`α` through the comparison isomorphism of
`CategoryTheory.Sheaf.freeAlgebraSheafIso` and is not itself a sheafification of the polynomial
presheaf on the nose.

## References

* [Stacks Project, Tag 04BK](https://stacks.math.columbia.edu/tag/04BK), derivations of sheaves
  of rings.
* [Stacks Project, Tag 08TU](https://stacks.math.columbia.edu/tag/08TU), the free algebra sheaf.
-/

@[expose] public section

open CategoryTheory

universe v u w

namespace Stacks.SheafOfModules

open Stacks.Sites.FreeAlgebra

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- **The unit of the sheafification of a presheaf of commutative rings is locally bijective.**
Sheafification of presheaves of commutative rings on the site inverts exactly the locally
bijective morphisms: the site is essentially small relative to the universe `max w u v`, and the
small model's topology has that property. -/
lemma isLocallyBijective_toSheafification_commRingCat
    [HasWeakSheafify J CommRingCat.{max w u v}] (P : Cᵒᵖ ⥤ CommRingCat.{max w u v}) :
    Presheaf.IsLocallySurjective J ((toSheafification J CommRingCat.{max w u v}).app P) ∧
      Presheaf.IsLocallyInjective J ((toSheafification J CommRingCat.{max w u v}).app P) := by
  have : EssentiallySmall.{max w u v} C := essentiallySmallSelf.{w, v, u} C
  have : ((equivSmallModel.{max w u v} C).inverse.inducedTopology J).WEqualsLocallyBijective
      CommRingCat.{max w u v} := inferInstance
  have : J.WEqualsLocallyBijective CommRingCat.{max w u v} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{v, _, u, _, max w u v} J
  exact ⟨(J.W_toSheafify _).isLocallySurjective, (J.W_toSheafify _).isLocallyInjective⟩

/-- Equal vectors have equal combinations `r • x + s • y`. -/
private theorem smul_add_smul_congr {R : Type w} [Ring R] {N : ModuleCat.{w} R} (r s : R)
    {x x' y y' : N} (hx : x = x') (hy : y = y') :
    r • x + s • y = r • x' + s • y' := by
  rw [hx, hy]

/-- A family of values in a module over `R[E']` at the variables is the family of values of a
derivation of `R[E']` over `R`. -/
lemma exists_mvPolynomial_derivation_X (R : CommRingCat.{w}) (E' : Type w)
    (N : ModuleCat.{w} (MvPolynomial E' R)) (g : E' → N) :
    ∃ d : N.Derivation (CommRingCat.ofHom MvPolynomial.C), ∀ e, d.d (MvPolynomial.X e) = g e := by
  let : Module R N := Module.compHom N (MvPolynomial.C : R →+* MvPolynomial E' R)
  let : IsScalarTower R (MvPolynomial E' R) N := IsScalarTower.of_compHom _ _ _
  exact ⟨ModuleCat.Derivation.mk (MvPolynomial.mkDerivation R g)
    (fun x y => map_add _ x y) (fun x y => Derivation.leibniz _ x y)
    (fun r => MvPolynomial.derivation_C _ r), fun e => MvPolynomial.mkDerivation_X R g e⟩

/-- A morphism of presheaves of sets from `E` to a presheaf of modules over the polynomial
presheaf `A(-)[E(-)]` is the family of values at the variables of a derivation over `A`. -/
lemma exists_derivation_polynomialPresheaf (A : Sheaf J CommRingCat.{w}) (E : Cᵒᵖ ⥤ Type w)
    (N : PresheafOfModules.{w} (polynomialPresheaf J A E ⋙ forget₂ CommRingCat RingCat))
    (g : E ⟶ N.presheaf ⋙ forget AddCommGrpCat) :
    ∃ D : PresheafOfModulesOfCommRing.Derivation' N (polynomialCoefficientMap J A E),
      ∀ (X : Cᵒᵖ) (e : E.obj X), D.d (MvPolynomial.X e) = g.app X e := by
  choose d hX using fun X : Cᵒᵖ =>
    exists_mvPolynomial_derivation_X (A.obj.obj X) (E.obj X) (N.obj X) (g.app X)
  have hC (X : Cᵒᵖ) (r : A.obj.obj X) : (d X).d (MvPolynomial.C r) = 0 := (d X).d_map r
  have hn {X Y : Cᵒᵖ} (h : X ⟶ Y) (x : (polynomialPresheaf J A E).obj X) :
      (d Y).d ((polynomialPresheaf J A E).map h x) = N.map h ((d X).d x) := by
    induction x using MvPolynomial.induction_on with
    | C r =>
      rw [show (polynomialPresheaf J A E).map h (MvPolynomial.C r) =
        MvPolynomial.C (A.obj.map h r) from MvPolynomial.eval₂Hom_C _ _ _, hC, hC, map_zero]
      rfl
    | add p q hp hq =>
      refine Eq.trans (congrArg (fun t => (d Y).d t) (map_add _ p q)) ?_
      refine Eq.trans ((d Y).d_add _ _) ?_
      refine Eq.trans (congrArg₂ (· + ·) hp hq) ?_
      refine Eq.trans (map_add (ConcreteCategory.hom (N.map h)) _ _).symm ?_
      exact congrArg (fun t => (ConcreteCategory.hom (N.map h)) t) ((d X).d_add p q).symm
    | mul_X p e hp =>
      have hvar : (d Y).d ((polynomialPresheaf J A E).map h (MvPolynomial.X e)) =
          (ConcreteCategory.hom (N.map h)) ((d X).d (MvPolynomial.X e)) := by
        refine Eq.trans (congrArg (fun t => (d Y).d t)
          (MvPolynomial.eval₂Hom_X' _ _ _ : (polynomialPresheaf J A E).map h (MvPolynomial.X e) =
            MvPolynomial.X (E.map h e))) ?_
        refine Eq.trans (hX Y (E.map h e)) ?_
        refine Eq.trans (NatTrans.naturality_apply g h e) ?_
        exact congrArg (fun t => (ConcreteCategory.hom (N.map h)) t) (hX X e).symm
      refine Eq.trans (congrArg (fun t => (d Y).d t) (map_mul _ p (MvPolynomial.X e))) ?_
      refine Eq.trans ((d Y).d_mul _ _) ?_
      refine Eq.trans (smul_add_smul_congr _ _ hvar hp) ?_
      refine Eq.trans ?_ (congrArg (fun t => (ConcreteCategory.hom (N.map h)) t)
        ((d X).d_mul p (MvPolynomial.X e)).symm)
      refine Eq.trans ?_ (map_add (ConcreteCategory.hom (N.map h)) _ _).symm
      exact congrArg₂ (· + ·) (PresheafOfModules.map_smul N h p _).symm
        (PresheafOfModules.map_smul N h (MvPolynomial.X e) _).symm
  exact ⟨PresheafOfModulesOfCommRing.Derivation'.mk d (fun {X Y} h x => hn h x), hX⟩

/-- A derivation with values in a sheaf of modules extends along a locally bijective morphism
`α : P ⟶ Q` of presheaves of commutative rings into the sheaf of rings `Q`. -/
lemma exists_derivation_comp_of_isLocallyBijective
    [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{w}] {Q : Sheaf J CommRingCat.{w}}
    (M : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Q))
    {S P : Cᵒᵖ ⥤ CommRingCat.{w}} (a : S ⟶ P) (α : P ⟶ Q.obj)
    [Presheaf.IsLocallySurjective J α] [Presheaf.IsLocallyInjective J α]
    (D : PresheafOfModulesOfCommRing.Derivation' ((PresheafOfModules.restrictScalars
      (Functor.whiskerRight α (forget₂ CommRingCat RingCat))).obj M.val) a) :
    ∃ D' : PresheafOfModulesOfCommRing.Derivation' M.val (a ≫ α),
      ∀ (X : Cᵒᵖ) (x : P.obj X), D'.d (α.app X x) = D.d x := by
  let alphaAdd := Functor.whiskerRight α
    (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat)
  have : Presheaf.IsLocallySurjective J alphaAdd :=
    ⟨fun {_} x => Presheaf.imageSieve_mem J α x⟩
  have : Presheaf.IsLocallyInjective J alphaAdd :=
    ⟨fun {_} x y h => Presheaf.equalizerSieve_mem J α x y h⟩
  let d₀ : P ⋙ (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat) ⟶
      M.val.presheaf :=
    { app X := AddCommGrpCat.ofHom D.d
      naturality := by
        intro X Y g
        ext x
        exact D.d_map g x }
  let e := (J.W_of_isLocallyBijective alphaAdd).homEquiv M.val.presheaf M.isSheaf
  let d := e.symm d₀
  have hd : alphaAdd ≫ d = d₀ := e.apply_symm_apply d₀
  let δ (X : Cᵒᵖ) : Q.obj.obj X →+ M.val.obj X := (d.app X).hom
  have hd' (X : Cᵒᵖ) (x : P.obj X) : δ X (α.app X x) = D.d x :=
    congrArg (fun g => g.app X x) hd
  have hn {X Y : Cᵒᵖ} (g : X ⟶ Y) (x : Q.obj.obj X) :
      δ Y (Q.obj.map g x) = M.val.map g (δ X x) := NatTrans.naturality_apply d g x
  refine ⟨{ d := fun {X} => δ X
            d_map := hn
            d_app := ?_
            d_mul := ?_ }, hd'⟩
  · intro X x y
    apply M.isSheaf.isSeparated _ _
      (J.intersection_covering (Presheaf.imageSieve_mem J α x)
        (Presheaf.imageSieve_mem J α y))
    rintro Y g ⟨⟨x₀, hx₀⟩, ⟨y₀, hy₀⟩⟩
    show M.val.map g.op _ = M.val.map g.op _
    have hprod : Q.obj.map g.op (x * y) = α.app _ (x₀ * y₀) := by
      rw [map_mul, ← hx₀, ← hy₀, map_mul]
    have hy' : M.val.map g.op (δ X y) = D.d y₀ :=
      (hn g.op y).symm.trans ((congrArg (δ _) hy₀.symm).trans (hd' _ y₀))
    have hx' : M.val.map g.op (δ X x) = D.d x₀ :=
      (hn g.op x).symm.trans ((congrArg (δ _) hx₀.symm).trans (hd' _ x₀))
    have hleft : M.val.map g.op (δ X (x * y)) = D.d (x₀ * y₀) :=
      (hn g.op (x * y)).symm.trans ((congrArg (δ _) hprod).trans (hd' _ _))
    have h1 := PresheafOfModules.map_smul M.val g.op x (δ X y)
    have h2 := PresheafOfModules.map_smul M.val g.op y (δ X x)
    have hx₀' : α.app _ x₀ =
        ((Stacks.SheafOfModules.Tensor.ringSheaf Q).obj.map g.op) x := hx₀
    have hy₀' : α.app _ y₀ =
        ((Stacks.SheafOfModules.Tensor.ringSheaf Q).obj.map g.op) y := hy₀
    rw [← hx₀', hy'] at h1
    rw [← hy₀', hx'] at h2
    rw [map_add]
    exact hleft.trans ((D.d_mul x₀ y₀).trans (congrArg₂ (· + ·) h1 h2).symm)
  · intro X x
    exact (hd' _ (a.app X x)).trans (D.d_app x)

/-- **A prescription of values at the variables is the family of values of a derivation.** Let
`α : A(-)[E(-)] ⟶ Q` be a locally bijective morphism of presheaves of commutative rings from the
polynomial presheaf into a sheaf of rings `Q`, and let `M` be a sheaf of `Q`-modules. Then every
morphism of presheaves of sets `E ⟶ M` is the family of values on the variables of a
derivation of `Q` over `A(-)[E(-)]`'s coefficients with values in `M`.

The derivation is built in two steps: objectwise, `A(U)[E(U)]` is free on `E(U)` over `A(U)`, so
the values at the variables prescribe a derivation of the polynomial presheaf; and a derivation
with values in a sheaf extends uniquely along the local bijection `α`. -/
lemma exists_derivation_of_polynomialVariable
    [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    (A : Sheaf J CommRingCat.{w}) (E : Cᵒᵖ ⥤ Type w) {Q : Sheaf J CommRingCat.{w}}
    (α : polynomialPresheaf J A E ⟶ Q.obj)
    [Presheaf.IsLocallySurjective J α] [Presheaf.IsLocallyInjective J α]
    (M : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Q))
    (f : E ⟶ M.val.presheaf ⋙ forget AddCommGrpCat) :
    ∃ D : PresheafOfModulesOfCommRing.Derivation' M.val (polynomialCoefficientMap J A E ≫ α),
      ∀ (X : Cᵒᵖ) (e : E.obj X), D.d (α.app X (MvPolynomial.X e)) = f.app X e := by
  obtain ⟨D₀, hD₀⟩ := exists_derivation_polynomialPresheaf J A E
    ((PresheafOfModules.restrictScalars
      (Functor.whiskerRight α (forget₂ CommRingCat RingCat))).obj M.val) f
  obtain ⟨D, hD⟩ :=
    exists_derivation_comp_of_isLocallyBijective J M (polynomialCoefficientMap J A E) α D₀
  exact ⟨D, fun X e => (hD X _).trans (hD₀ X e)⟩

/-- **A derivation of a sheaf of commutative rings which is locally the polynomial presheaf
`A(-)[E(-)]` is determined by its values on the variables.** The sheaf of rings is given by a
locally surjective morphism `α` from the polynomial presheaf which is compatible with the
structural morphisms from `A`. -/
lemma derivation_ext_of_polynomialVariable
    [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    (A : Sheaf J CommRingCat.{w}) (E : Cᵒᵖ ⥤ Type w)
    {Q : Sheaf J CommRingCat.{w}} {φ : A ⟶ Q}
    (α : polynomialPresheaf J A E ⟶ Q.obj)
    [Presheaf.IsLocallySurjective J α]
    (hα : polynomialCoefficientMap J A E ≫ α = φ.hom)
    (M : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Q))
    (D₁ D₂ : PresheafOfModulesOfCommRing.Derivation' M.val φ.hom)
    (h : ∀ (X : Cᵒᵖ) (e : E.obj X),
      D₁.d (α.app X (MvPolynomial.X e)) = D₂.d (α.app X (MvPolynomial.X e))) : D₁ = D₂ := by
  have hp (X : Cᵒᵖ) (p : MvPolynomial (E.obj X) (A.obj.obj X)) :
      D₁.d (α.app X p) = D₂.d (α.app X p) := by
    induction p using MvPolynomial.induction_on with
    | C r =>
      have hCr : (ConcreteCategory.hom (α.app X)) (MvPolynomial.C r) =
          (ConcreteCategory.hom (φ.hom.app X)) r :=
        congrArg (fun t : A.obj ⟶ Q.obj => (ConcreteCategory.hom (t.app X)) r) hα
      rw [hCr, D₁.d_app, D₂.d_app]
    | add p q hp hq =>
      refine Eq.trans (congrArg (fun t => D₁.d t)
        (map_add (ConcreteCategory.hom (α.app X)) p q)) ?_
      refine Eq.trans (map_add D₁.d _ _) ?_
      refine Eq.trans (congrArg₂ (· + ·) hp hq) ?_
      refine Eq.trans (map_add D₂.d _ _).symm ?_
      exact congrArg (fun t => D₂.d t) (map_add (ConcreteCategory.hom (α.app X)) p q).symm
    | mul_X p e hp =>
      refine Eq.trans (congrArg (fun t => D₁.d t)
        (map_mul (ConcreteCategory.hom (α.app X)) p (MvPolynomial.X e))) ?_
      refine Eq.trans (D₁.d_mul _ _) ?_
      refine Eq.trans (smul_add_smul_congr _ _ (h X e) hp) ?_
      refine Eq.trans (D₂.d_mul _ _).symm ?_
      exact congrArg (fun t => D₂.d t)
        (map_mul (ConcreteCategory.hom (α.app X)) p (MvPolynomial.X e)).symm
  ext X x
  apply M.isSheaf.isSeparated _ _ (Presheaf.imageSieve_mem J α x)
  rintro Y f ⟨p, hpx⟩
  show M.val.map f.op (D₁.d x) = M.val.map f.op (D₂.d x)
  exact (D₁.d_map f.op x).symm.trans
    ((congrArg D₁.d hpx.symm).trans ((hp _ p).trans
      ((congrArg D₂.d hpx).trans (D₂.d_map f.op x))))

end Stacks.SheafOfModules

end
