module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.Homotopy
public import StacksFrontier.AlgebraicTopology.SimplicialObject.Homotopy.Basic
public import StacksFrontier.AlgebraicTopology.SimplicialSet.TrivialKanFibration
public import StacksFrontier.Cotangent.PolynomialAlgebraSite
public import StacksFrontier.Cotangent.StandardResolutionIsResolution
import StacksCore.Tactic.StacksAttribute

/-!
# Simplicial resolutions and the point criterion on the site of polynomial algebras

Let `A → B` be a ring map and let `C_{B/A}` be the site of polynomial `A`-algebras augmented to
`B` of Tag 08PR, the opposite of the category of pairs `(P, α : P → B)`. A simplicial
`A`-algebra `P_•` endowed with an augmentation `ε : P_• → B` is the same thing as a cosimplicial
object of `C_{B/A}`, and if `ε` is a resolution in the sense of Tag 08QI — each `P_n` a
polynomial algebra over `A` and `ε` a trivial Kan fibration on underlying simplicial sets — then
for every object `(Q, β)` of `C_{B/A}` the simplicial set

`S_• = Mor_{C_{B/A}}((P_•, ε), (Q, β))`

is homotopy equivalent to a singleton. That is the hypothesis of the criterion of Tag 08Q9, and
it is what this file proves, for an arbitrary resolution and then for the standard resolution.

## Main definitions

* `CommAlgCat.resolutionOver` and `CommAlgCat.resolutionAugmentation`: the augmentation `ε`, read
  as a simplicial object of `Over B` and then of the category of polynomial `A`-algebras
  augmented to `B`.
* `CommAlgCat.resolutionCosimplicialObject`: the same, read as a cosimplicial object of the site
  `C_{B/A}`.
* `CommAlgCat.resolutionMor`: the simplicial set `Mor_{C_{B/A}}((P_•, ε), W)`, defined directly,
  together with `CommAlgCat.resolutionMorIso` identifying it with the simplicial set of the
  criterion.

## Main results

* `CommAlgCat.trivialKanFibrations_resolutionMor`: the content of the source's proof. For a
  resolution `ε : P_• ⟶ B`, the morphism from `Mor_{C_{B/A}}((P_•, ε), W)` to the constant
  simplicial set on a singleton is a trivial Kan fibration.
* `CommAlgCat.exists_homotopyEquivalences_resolutionMor`: **Stacks 08PS**, that simplicial set is
  therefore homotopy equivalent to a singleton, which is the hypothesis the criterion of Tag 08Q9
  asks of a cosimplicial object.
* `CommAlgCat.exists_homotopyEquivalences_standardResolutionMor`: **Stacks 08PT**, the same for
  the standard resolution of `B` over `A`.

## Implementation notes

**What is proved, and what the attributes say.** The source's conclusion is the identification
`Lπ_!(ℱ) = ℱ(P_•, ε)` in `D(Ab)`, resp. `D(B)`, functorially in `ℱ`, obtained by feeding the
homotopy equivalence below into the criterion of Tag 08Q9. That last step is *not* taken here,
and the attributes say so. The reason is a size mismatch that is not about this file: the
criterion of Tag 08Q9 is stated — as it must be, since it is proved through the projective
generators of the category of abelian presheaves — for a *small* site, whereas the objects of
`CommAlgCat.polynomialSite` live in `Type (u + 1)` while its morphisms live in `Type u`, so it is
a large category. The source avoids the issue by a footnote restricting the sets of variables to
those of cardinality at most that of `B`; `CommAlgCat.polynomialSite` carries no such
restriction, and the two sites are not equivalent as categories of the size `Tag 08Q9` wants.
Everything in the source's proof other than the invocation of the criterion is proved here, and
the statement proved is literally the criterion's hypothesis on the cosimplicial object
`CommAlgCat.resolutionCosimplicialObject`, so that supplying a small model of the site — or a
version of Tag 08Q9 for a large one — turns these statements into the tags with no further
mathematics.

**The fibre and product decomposition is carried out on the lifting problem.** The source writes
`Q = A[E]`, decomposes `S_• = ∏_{e ∈ E} F_{β(e),•}` into the fibres of `ε`, and concludes by
stability of trivial Kan fibrations under base change (Tag 08NN) and under products (Tag 08NR).
Both of those are available (the `IsStableUnderBaseChange` instance of `SSet.trivialKanFibrations`
and `SSet.isStableUnderProductsOfShape_trivialKanFibrations`) but applying them would require
exhibiting `S_•` as a limit in simplicial sets, degreewise, and naming the fibres as simplicial
sets in their own right. Instead the decomposition is applied directly to a lifting problem for
`S_• → ∗`: a boundary `∂Δ[n] ⟶ S_•` is the same thing as a family, indexed by `E`, of maps
`∂Δ[n] ⟶ P_•` whose composites with `ε` are constant, each of which `ε` fills, and the fillers
assemble into `Δ[n] ⟶ S_•` because an `A`-algebra map out of `A[E]` is a function on `E`. The
passage from the trivial Kan fibration to the homotopy equivalence of simplicial objects is
Tag 08NS (`SSet.trivialKanFibrations_isHomotopyEquiv`) followed by Mathlib's
`SSet.Homotopy.toSimplicialObjectHomotopy`, exactly as in
`StacksFrontier/Cotangent/Resolution.lean`.

**Why `CommAlgCat.resolutionMor` is defined.** The simplicial set of the criterion is
`U.op ⋙ yoneda.obj W` for `U` the cosimplicial object, whose sections are morphisms of a full
subcategory of `Over B` read in an opposite category twice over. `CommAlgCat.resolutionMor`
spells those sections out, and `CommAlgCat.resolutionMorIso` is the comparison: the two
simplicial sets differ only by the `Opposite` wrapping Mathlib puts on the morphisms of an
opposite category, so the isomorphism is `Quiver.Hom.op` in each degree. The lifting argument
runs on the explicit one, and the criterion's form follows because trivial Kan fibrations respect
isomorphisms and a morphism to the constant simplicial set on a singleton is unique.

## References

* [Stacks Project, Tag 08PS](https://stacks.math.columbia.edu/tag/08PS)
* [Stacks Project, Tag 08PT](https://stacks.math.columbia.edu/tag/08PT)
* [Stacks Project, Tag 08Q9](https://stacks.math.columbia.edu/tag/08Q9)
* [Stacks Project, Tag 08QI](https://stacks.math.columbia.edu/tag/08QI)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite Simplicial

universe u

namespace CommAlgCat

variable {A : Type u} [CommRing A] {B : CommAlgCat.{u} A}
  {P : SimplicialObject (CommAlgCat.{u} A)}

/-! ### Morphisms out of a polynomial algebra augmented to `B` -/

section Generators

variable {Q Y : PolynomialAugmentation A B} {E : Type u}
  (e : MvPolynomial E A ≃ₐ[A] Q.obj.left)

/-- Two `A`-algebra maps out of a polynomial algebra `A[E] ≃ₐ[A] R` agreeing on the variables are
equal. -/
private theorem algHom_ext_of_equiv {R S : Type u} [CommRing R] [CommRing S] [Algebra A R]
    [Algebra A S] (e : MvPolynomial E A ≃ₐ[A] R) {f₁ f₂ : R →ₐ[A] S}
    (h : ∀ x, f₁ (e (MvPolynomial.X x)) = f₂ (e (MvPolynomial.X x))) : f₁ = f₂ :=
  (AlgHom.cancel_right (f := e.toAlgHom) e.surjective).mp
    (MvPolynomial.algHom_ext fun x => by simpa using h x)

/-- The `A`-algebra map out of `Q = A[E]` sending the variable `X_x` to `g x` lies over `B`, as
soon as each `g x` has the augmentation `β(X_x)`: two `A`-algebra maps out of a polynomial algebra
agreeing on the variables are equal. -/
lemma aeval_comp_symm_comp_hom (g : E → Y.obj.left)
    (hg : ∀ x, Y.obj.hom (g x) = Q.obj.hom (e (MvPolynomial.X x))) :
    (ConcreteCategory.ofHom ((MvPolynomial.aeval g).comp e.symm.toAlgHom) :
        Q.obj.left ⟶ Y.obj.left) ≫ Y.obj.hom = Q.obj.hom := by
  apply CommAlgCat.hom_ext
  exact algHom_ext_of_equiv e
    (f₁ := Y.obj.hom.hom.comp ((MvPolynomial.aeval g).comp e.symm.toAlgHom))
    (f₂ := Q.obj.hom.hom) fun x => by simpa using hg x

/-- A morphism of polynomial `A`-algebras augmented to `B` out of `(Q, β)`, given a presentation
`Q = A[E]` and the images of the variables: a function `g : E → Y` whose values have the
prescribed augmentations `β(X_x)` extends to an `A`-algebra map `Q ⟶ Y` over `B`. -/
def homOfGenerators (g : E → Y.obj.left)
    (hg : ∀ x, Y.obj.hom (g x) = Q.obj.hom (e (MvPolynomial.X x))) : Q ⟶ Y :=
  ObjectProperty.homMk (Over.homMk _ (aeval_comp_symm_comp_hom e g hg))

/-- The underlying `A`-algebra map of `CommAlgCat.homOfGenerators` is the evaluation map of the
presentation. -/
@[simp]
lemma homOfGenerators_hom_left (g : E → Y.obj.left)
    (hg : ∀ x, Y.obj.hom (g x) = Q.obj.hom (e (MvPolynomial.X x))) :
    (homOfGenerators e g hg).hom.left =
      (ConcreteCategory.ofHom ((MvPolynomial.aeval g).comp e.symm.toAlgHom) :
        Q.obj.left ⟶ Y.obj.left) :=
  rfl

/-- `CommAlgCat.homOfGenerators` sends the variable `X_x` to the prescribed value. -/
@[simp]
lemma homOfGenerators_hom_left_apply (g : E → Y.obj.left)
    (hg : ∀ x, Y.obj.hom (g x) = Q.obj.hom (e (MvPolynomial.X x))) (x : E) :
    (homOfGenerators e g hg).hom.left (e (MvPolynomial.X x)) = g x := by
  rw [homOfGenerators_hom_left]
  simp

/-- Two morphisms of polynomial `A`-algebras augmented to `B` out of `(Q, β)` agreeing on the
variables of a presentation `Q = A[E]` are equal. -/
lemma hom_ext_of_generators {f₁ f₂ : Q ⟶ Y}
    (h : ∀ x, f₁.hom.left (e (MvPolynomial.X x)) = f₂.hom.left (e (MvPolynomial.X x))) :
    f₁ = f₂ := by
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  apply CommAlgCat.hom_ext
  exact algHom_ext_of_equiv e h

/-- The underlying `A`-algebra map of a composite of morphisms of augmented algebras, on an
element. -/
lemma comp_hom_left_apply {Z : PolynomialAugmentation A B} (φ : Q ⟶ Y) (ψ : Y ⟶ Z)
    (a : Q.obj.left) : (φ ≫ ψ).hom.left a = ψ.hom.left (φ.hom.left a) :=
  rfl

end Generators

/-! ### A resolution as a cosimplicial object of the site -/

section Resolution

variable (ε : P ⟶ (SimplicialObject.const (CommAlgCat.{u} A)).obj B)

/-- The augmentation `ε : P_• ⟶ B`, read as a simplicial object of `Over B`: the term in degree
`n` is `P_n` together with the augmentation `ε_n`. -/
def resolutionOver : SimplexCategoryᵒᵖ ⥤ Over B :=
  P.toOver B (fun n => ε.app n) fun {_ _} _ => by simp

variable (hP : ∀ n, IsPolynomialAlgebra A (P.obj n))

/-- The augmentation `ε : P_• ⟶ B` of a degreewise polynomial simplicial `A`-algebra, read as a
simplicial object of the category of polynomial `A`-algebras augmented to `B`. -/
def resolutionAugmentation : SimplicialObject (PolynomialAugmentation A B) :=
  (IsPolynomialAlgebraOver A B).lift (resolutionOver ε) hP

/-- The simplicial operators of `CommAlgCat.resolutionAugmentation` are those of `P_•`. -/
@[simp]
lemma resolutionAugmentation_map_hom_left {m m' : SimplexCategoryᵒᵖ} (f : m ⟶ m') :
    ((resolutionAugmentation ε hP).map f).hom.left = P.map f :=
  rfl

/-- The augmentation `ε : P_• ⟶ B`, read as a cosimplicial object of the site `C_{B/A}`: the site
is the opposite of the category of polynomial `A`-algebras augmented to `B`, so a simplicial
object of the latter is a cosimplicial object of the former. -/
def resolutionCosimplicialObject : CosimplicialObject (polynomialSite A B) :=
  (resolutionAugmentation ε hP).rightOp

/-- The simplicial set `Mor_{C_{B/A}}((P_•, ε), W)` of morphisms of the site from the
cosimplicial object of a resolution to an object `W`, written out: its sections in degree `n` are
the `A`-algebra maps from `W` to `P_n` over `B`. -/
def resolutionMor (W : polynomialSite A B) : SimplexCategoryᵒᵖ ⥤ Type u where
  obj m := W.unop ⟶ (resolutionAugmentation ε hP).obj m
  map f := ↾fun g => g ≫ (resolutionAugmentation ε hP).map f
  map_id _ := by ext g; simp
  map_comp _ _ := by ext g; simp

/-- `CommAlgCat.resolutionMor` is the simplicial set the criterion of Tag 08Q9 is about: the
Yoneda functor at `W` evaluated on the cosimplicial object of the resolution. The two differ only
by the `Opposite` wrapping of the morphisms of an opposite category. -/
def resolutionMorIso (W : polynomialSite A B) :
    resolutionMor ε hP W ≅ (resolutionCosimplicialObject ε hP).op ⋙ yoneda.obj W where
  hom := { app := fun _ => ↾fun g => Quiver.Hom.op g, naturality := fun _ _ _ => rfl }
  inv := { app := fun _ => ↾fun g => Quiver.Hom.unop g, naturality := fun _ _ _ => rfl }
  hom_inv_id := by ext m g; rfl
  inv_hom_id := by ext m g; rfl

/-- The simplicial operators of `CommAlgCat.resolutionMor` are composition with those of the
resolution. -/
@[simp]
lemma resolutionMor_map_apply (W : polynomialSite A B) {m m' : SimplexCategoryᵒᵖ} (f : m ⟶ m')
    (g : (resolutionMor ε hP W).obj m) :
    (resolutionMor ε hP W).map f g = g ≫ (resolutionAugmentation ε hP).map f :=
  rfl

/-- The morphism of augmented algebras `W ⟶ P_n` determined, in a single degree, by a family of
maps `X ⟶ P_•` indexed by the variables of a presentation `W = A[E]` with constant
`ε`-images. -/
def morOfFamilyApp {W : polynomialSite A B} {E : Type u}
    (e : MvPolynomial E A ≃ₐ[A] W.unop.obj.left) {X : SimplexCategoryᵒᵖ ⥤ Type u}
    (L : E → (X ⟶ P ⋙ forget (CommAlgCat.{u} A)))
    (hL : ∀ (x : E) (m : SimplexCategoryᵒᵖ) (z : X.obj m),
      ε.app m ((L x).app m z) = W.unop.obj.hom (e (MvPolynomial.X x)))
    (m : SimplexCategoryᵒᵖ) (z : X.obj m) : W.unop ⟶ (resolutionAugmentation ε hP).obj m :=
  homOfGenerators e (fun x => (L x).app m z) fun x => hL x m z

/-- `CommAlgCat.morOfFamilyApp` sends the variable `X_x` of the presentation to the value of the
`x`-th member of the family. -/
@[simp]
lemma morOfFamilyApp_hom_left_apply {W : polynomialSite A B} {E : Type u}
    (e : MvPolynomial E A ≃ₐ[A] W.unop.obj.left) {X : SimplexCategoryᵒᵖ ⥤ Type u}
    (L : E → (X ⟶ P ⋙ forget (CommAlgCat.{u} A)))
    (hL : ∀ (x : E) (m : SimplexCategoryᵒᵖ) (z : X.obj m),
      ε.app m ((L x).app m z) = W.unop.obj.hom (e (MvPolynomial.X x)))
    (m : SimplexCategoryᵒᵖ) (z : X.obj m) (x : E) :
    (morOfFamilyApp ε hP e L hL m z).hom.left (e (MvPolynomial.X x)) = (L x).app m z :=
  homOfGenerators_hom_left_apply (Y := (resolutionAugmentation ε hP).obj m) e
    (fun x => (L x).app m z) (fun x => hL x m z) x

/-- A family of maps `X ⟶ P_•`, indexed by the variables of a presentation `W = A[E]` of an object
of the site, whose composites with `ε` are constant at the augmentations of the variables,
assembles into a map `X ⟶ Mor_{C_{B/A}}((P_•, ε), W)`: an `A`-algebra map out of `A[E]` over `B`
is a function on `E` with the prescribed augmentations. -/
def morOfFamily {W : polynomialSite A B} {E : Type u}
    (e : MvPolynomial E A ≃ₐ[A] W.unop.obj.left) {X : SimplexCategoryᵒᵖ ⥤ Type u}
    (L : E → (X ⟶ P ⋙ forget (CommAlgCat.{u} A)))
    (hL : ∀ (x : E) (m : SimplexCategoryᵒᵖ) (z : X.obj m),
      ε.app m ((L x).app m z) = W.unop.obj.hom (e (MvPolynomial.X x))) :
    X ⟶ resolutionMor ε hP W where
  app m := ↾fun z => morOfFamilyApp ε hP e L hL m z
  naturality m m' g := by
    ext z
    change morOfFamilyApp ε hP e L hL m' (X.map g z) =
      morOfFamilyApp ε hP e L hL m z ≫ (resolutionAugmentation ε hP).map g
    refine hom_ext_of_generators e fun x => ?_
    rw [comp_hom_left_apply, morOfFamilyApp_hom_left_apply, morOfFamilyApp_hom_left_apply,
      resolutionAugmentation_map_hom_left]
    exact ConcreteCategory.congr_hom ((L x).naturality g) z

/-- `CommAlgCat.morOfFamily` sends the variable `X_x` of the presentation to the value of the
`x`-th member of the family. -/
@[simp]
lemma morOfFamily_app_hom_left {W : polynomialSite A B} {E : Type u}
    (e : MvPolynomial E A ≃ₐ[A] W.unop.obj.left) {X : SimplexCategoryᵒᵖ ⥤ Type u}
    (L : E → (X ⟶ P ⋙ forget (CommAlgCat.{u} A)))
    (hL : ∀ (x : E) (m : SimplexCategoryᵒᵖ) (z : X.obj m),
      ε.app m ((L x).app m z) = W.unop.obj.hom (e (MvPolynomial.X x)))
    (m : SimplexCategoryᵒᵖ) (z : X.obj m) (x : E) :
    ((morOfFamily ε hP e L hL).app m z).hom.left (e (MvPolynomial.X x)) = (L x).app m z :=
  morOfFamilyApp_hom_left_apply ε hP e L hL m z x

end Resolution

/-! ### The point criterion -/

section Criterion

variable (ε : P ⟶ (SimplicialObject.const (CommAlgCat.{u} A)).obj B)
  (hP : ∀ n, IsPolynomialAlgebra A (P.obj n))

/-- Two morphisms of simplicial sets into the constant simplicial set on a singleton are
equal. -/
lemma hom_ext_toConstPUnit {X : SimplexCategoryᵒᵖ ⥤ Type u}
    (f g : X ⟶ (Functor.const SimplexCategoryᵒᵖ).obj PUnit.{u + 1}) : f = g := by
  ext m x
  rfl

/-- Let `ε : P_• ⟶ B` be a resolution of `B` over `A`:
every `P_n` is a polynomial algebra over `A` and `ε` is a trivial Kan fibration on underlying
simplicial sets. Then for every object `W = (Q, β)` of the site `C_{B/A}` the morphism from the
simplicial set `Mor_{C_{B/A}}((P_•, ε), W)` to the constant simplicial set on a singleton — there
is only one — is a trivial Kan fibration.

This is the source's decomposition `S_• = ∏_{e ∈ E} F_{β(e),•}` into fibres of `ε`, carried out
on a lifting problem: writing `Q = A[E]`, a map `∂Δ[n] ⟶ S_•` is a family of maps
`∂Δ[n] ⟶ P_•` with constant `ε`-image, each of which `ε` fills, and the fillers assemble. -/
theorem trivialKanFibrations_resolutionMor
    (hε : SSet.trivialKanFibrations (Functor.whiskerRight ε (forget (CommAlgCat.{u} A))))
    (W : polynomialSite A B)
    (f : resolutionMor ε hP W ⟶ (Functor.const SimplexCategoryᵒᵖ).obj PUnit.{u + 1}) :
    SSet.trivialKanFibrations f := by
  classical
  obtain ⟨E, ⟨e⟩⟩ := W.unop.property
  rw [SSet.trivialKanFibrations_iff]
  intro n
  have hlp := (SSet.trivialKanFibrations_iff _).mp hε n
  refine ⟨fun {t u} sq ↦ ?_⟩
  -- For each variable `x` of the presentation `W = A[E]`, the `x`-th coordinate of the given
  -- boundary is a map `∂Δ[n] ⟶ P_•` whose composite with `ε` is constant at the augmentation of
  -- `X_x`; it lands in the source's fibre `F_{β(x),•}`, and `ε` fills it.
  have hfill : ∀ x : E, ∃ L : (Δ[n] : SSet.{u}) ⟶ P ⋙ forget (CommAlgCat.{u} A),
      (∀ (m : SimplexCategoryᵒᵖ) (z : (∂Δ[n] : SSet.{u}).obj m),
          L.app m (∂Δ[n].ι.app m z) = (t.app m z).hom.left (e (MvPolynomial.X x))) ∧
        ∀ (m : SimplexCategoryᵒᵖ) (z : (Δ[n] : SSet.{u}).obj m),
          ε.app m (L.app m z) = W.unop.obj.hom (e (MvPolynomial.X x)) := by
    intro x
    let top : (∂Δ[n] : SSet.{u}) ⟶ P ⋙ forget (CommAlgCat.{u} A) :=
      { app := fun m => ↾fun z => (t.app m z).hom.left (e (MvPolynomial.X x))
        naturality := fun m m' g => by
          ext z
          have hz : t.app m' ((∂Δ[n] : SSet.{u}).map g z) =
              t.app m z ≫ (resolutionAugmentation ε hP).map g :=
            ConcreteCategory.congr_hom (t.naturality g) z
          exact congrArg (fun k : W.unop ⟶ (resolutionAugmentation ε hP).obj m' =>
            k.hom.left (e (MvPolynomial.X x))) hz }
    let bot : (Δ[n] : SSet.{u}) ⟶
        ((SimplicialObject.const (CommAlgCat.{u} A)).obj B) ⋙ forget (CommAlgCat.{u} A) :=
      { app := fun _ => ↾fun _ => W.unop.obj.hom (e (MvPolynomial.X x))
        naturality := fun m m' g => by
          ext z
          simp }
    have hsq : CommSq top ∂Δ[n].ι
        (Functor.whiskerRight ε (forget (CommAlgCat.{u} A))) bot := by
      refine ⟨?_⟩
      ext m z
      exact ConcreteCategory.congr_hom (t.app m z).hom.w (e (MvPolynomial.X x))
    obtain ⟨⟨L, hL₁, hL₂⟩⟩ := (hlp.sq_hasLift hsq).exists_lift
    exact ⟨L, fun m z => ConcreteCategory.congr_hom (NatTrans.congr_app hL₁ m) z,
      fun m z => ConcreteCategory.congr_hom (NatTrans.congr_app hL₂ m) z⟩
  choose Lf hLf₁ hLf₂ using hfill
  refine ⟨⟨{ l := morOfFamily ε hP e Lf hLf₂, fac_left := ?_,
             fac_right := hom_ext_toConstPUnit _ _ }⟩⟩
  ext m z
  refine hom_ext_of_generators e fun x => ?_
  exact (morOfFamily_app_hom_left ε hP e Lf hLf₂ m (∂Δ[n].ι.app m z) x).trans (hLf₁ x m z)

/-- **Stacks 08PS**. Let `P_•` be a simplicial `A`-algebra endowed with an augmentation
`ε : P_• ⟶ B`, assume every `P_n` is a polynomial algebra over `A` and that `ε` is a trivial Kan
fibration on underlying simplicial sets. Then for every object `W = (Q, β)` of the site `C_{B/A}`
the simplicial set `Mor_{C_{B/A}}((P_•, ε), W)` is homotopy equivalent to the constant simplicial
set on a singleton, which is the hypothesis the criterion of Tag 08Q9 asks of the cosimplicial
object `CommAlgCat.resolutionCosimplicialObject` of the resolution. -/
@[stacks 08PS "the hypothesis of the criterion of Tag 08Q9 for the cosimplicial object of a \
  resolution: each `Mor_C((P_•, ε), W)` is homotopy equivalent to a singleton. The conclusion \
  `Lπ_!(ℱ) = ℱ(P_•, ε)` in `D(Ab)`, resp. `D(B)`, functorially in `ℱ`, is not asserted: the \
  criterion as formalized asks for a small site, and `CommAlgCat.polynomialSite` is large — see \
  the \
  first implementation note"]
theorem exists_homotopyEquivalences_resolutionMor
    (hε : SSet.trivialKanFibrations (Functor.whiskerRight ε (forget (CommAlgCat.{u} A))))
    (W : polynomialSite A B) :
    ∃ f : (resolutionCosimplicialObject ε hP).op ⋙ yoneda.obj W ⟶
        (Functor.const SimplexCategoryᵒᵖ).obj PUnit.{u + 1},
      SimplicialObject.homotopyEquivalences (Type u) f := by
  let pt : (resolutionCosimplicialObject ε hP).op ⋙ yoneda.obj W ⟶
      (Functor.const SimplexCategoryᵒᵖ).obj PUnit.{u + 1} :=
    { app := fun _ => ↾fun _ => PUnit.unit
      naturality := fun _ _ _ => rfl }
  have htriv : SSet.trivialKanFibrations pt := by
    have h' := MorphismProperty.RespectsIso.precomp SSet.trivialKanFibrations
      (resolutionMorIso ε hP W).inv ((resolutionMorIso ε hP W).hom ≫ pt)
      (trivialKanFibrations_resolutionMor ε hP hε W ((resolutionMorIso ε hP W).hom ≫ pt))
    rwa [Iso.inv_hom_id_assoc] at h'
  obtain ⟨g, ⟨h₁⟩, ⟨h₂⟩⟩ := SSet.trivialKanFibrations_isHomotopyEquiv _ htriv
  exact ⟨pt, g, Relation.EqvGen.rel _ _ ⟨h₁.toSimplicialObjectHomotopy⟩,
    Relation.EqvGen.rel _ _ ⟨h₂.toSimplicialObjectHomotopy⟩⟩

end Criterion

/-! ### The standard resolution -/

/-- **Stacks 08PT**. Let `A → B` be a ring map and let `ε : P_• ⟶ B` be the standard resolution of
`B` over `A`. Then for every object `W` of the site `C_{B/A}` the simplicial set
`Mor_{C_{B/A}}((P_•, ε), W)` is homotopy equivalent to the constant simplicial set on a singleton,
which is the hypothesis the criterion of Tag 08Q9 asks of the cosimplicial object of the standard
resolution. The two hypotheses of Tag 08PS hold for it by Tag 08QI: its terms are polynomial
algebras, and its augmentation is a trivial Kan fibration because it is a homotopy equivalence of
underlying simplicial sets (Tag 08ND), hence a quasi-isomorphism of associated complexes
(Tag 08P2), hence — being degreewise surjective — a trivial Kan fibration (Tag 08P1). -/
@[stacks 08PT "the hypothesis of the criterion of Tag 08Q9 for the cosimplicial object of the \
  standard resolution: each `Mor_C((P_•, ε), W)` is homotopy equivalent to a singleton. The \
  conclusion `Lπ_!(ℱ) = ℱ(P_•, ε)` in `D(Ab)`, resp. `D(B)`, functorially in `ℱ`, is not \
  asserted, for the reason recorded at Tag 08PS in this file"]
theorem exists_homotopyEquivalences_standardResolutionMor (A : Type u) [CommRing A]
    (B : CommAlgCat.{u} A) (W : polynomialSite A B) :
    ∃ f : (resolutionCosimplicialObject (standardResolution.{u, u} A B).hom
          (standardResolution_isResolution.{u, u} A B).isPolynomialAlgebra).op ⋙
        yoneda.obj W ⟶ (Functor.const SimplexCategoryᵒᵖ).obj PUnit.{u + 1},
      SimplicialObject.homotopyEquivalences (Type u) f :=
  exists_homotopyEquivalences_resolutionMor _ _
    (standardResolution_isResolution.{u, u} A B).trivialKanFibration W

end CommAlgCat

end

