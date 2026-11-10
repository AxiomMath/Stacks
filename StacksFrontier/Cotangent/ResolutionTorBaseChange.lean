module

public import Mathlib.Algebra.Homology.AlternatingConst
public import Mathlib.AlgebraicTopology.ExtraDegeneracy
public import StacksFrontier.Cotangent.ResolutionBaseChange
public import StacksFrontier.Homology.Tor.Independence
public import StacksFrontier.Homology.Tor.IndependenceBaseChange
import StacksCore.Tactic.StacksAttribute

/-!
# The base change of a resolution along a derived-Cartesian square

Let `ε : P_• ⟶ B` be a resolution of `B` over `A` in the sense of Tag 08QI and let
```
A  --→  A'
|       |
B  --→  B'
```
be a commutative square of rings which induces a quasi-isomorphism `B ⊗_A^L A' = B'` — that is,
`Tor_i^A(A', B) = 0` for `i > 0` and the canonical map `A' ⊗_A B → B'` is bijective. Then the
base change `A' ⊗_A P_• ⟶ B'` is again a resolution, of `B'` over `A'`. This is the first half
of the proof of **Stacks 08QP**, and it is what this file supplies.

The source's argument is run verbatim. The Moore complex `s(P_•)` is a complex of free
`A`-modules, each `P_n` being a polynomial algebra, and `s(P_•) → B` is a quasi-isomorphism, so
`s(P_•)` is a projective resolution of `B`; hence `B ⊗_A^L A'` is computed by
`s(P_•) ⊗_A A' = s(A' ⊗_A P_•)`, and the hypothesis says exactly that `s(A' ⊗_A P_•) → B'` is a
quasi-isomorphism. The criterion of Tag 08QI then upgrades that to the resolution property.

## Main definitions

* `CommAlgCat.toModuleCat`: the forgetful functor from commutative `A`-algebras to `A`-modules.
* `CommAlgCat.moduleAugmentation`: an augmentation `ε : P_• ⟶ B` read in `A`-modules.
* `CommAlgCat.mooreProjectiveResolution`: **the Moore complex of a resolution, as a projective
  resolution of `B` in `ModuleCat A`.**

## Main results

* `CommAlgCat.quasiIso_mooreComplex_map_iff`: a quasi-isomorphism of Moore complexes of
  `A`-modules is the same thing as one of Moore complexes of abelian groups. This is what
  connects the criterion of Tag 08QI, which is stated for abelian groups, to the projective
  resolution, which has to live in `ModuleCat A`.
* `CommAlgCat.quasiIso_moore_augmentationBaseChange`: the Moore complex of the base-changed
  augmentation is a quasi-isomorphism.
* `CommAlgCat.isResolution_augmentationBaseChange`: **the base change of a resolution along a
  derived-Cartesian square is a resolution.**
* `CommAlgCat.isResolution_augmentationBaseChange_of_isPushout`: the same with the degree-zero
  half of the hypothesis supplied by `Algebra.IsPushout`.

## Implementation notes

**The hypothesis is the source's, written out.** "(92.6.0.1) induces a quasi-isomorphism
`B ⊗_A^L A' = B'`" is two conditions: the higher Tor modules `Tor_i^A(A', B)` vanish, which is
`RingTheory.TorIndependence.TorIndependent A A' B`, and the degree-zero part
`A' ⊗_A B → B'` is an isomorphism. The second is stated here as bijectivity of
`CommAlgCat.baseChangeAugmentation b (Over.mk (𝟙 B))`, the map `a' ⊗ x ↦ a' · b(x)`, rather than
as `Algebra.IsPushout`: that avoids demanding an `Algebra B B'` instance of a caller who has
only the `A`-algebra map `b : B → B'`, and `Algebra.IsPushout` implies it — see
`CommAlgCat.bijective_baseChangeUnit_of_isPushout`. Tor independence is a symmetric
notion; it is written with `A'` first because that is the order
`RingTheory.TorIndependence.torIndependent_iff_isZero_tor` produces and in which
`RingTheory.TorIndependence.quasiIso_tensor_map_projectiveResolution_of_isZero_Tor` consumes it.

**Three categories, and why.** The criterion of Tag 08QI
(`CommAlgCat.isResolution_quasiIso_homotopyEquivalence_tfae`) is stated for Moore complexes of
*abelian groups*; projective resolutions and Tor have to be taken in `ModuleCat A`; and the
base-changed algebra is an `A'`-algebra. The three are reconciled definitionally rather than by
transport: `CommAlgCat.quasiIso_mooreComplex_map_iff` moves `QuasiIso` between `ModuleCat A` and
`AddCommGrpCat` along `forget₂`, which is additive, preserves homology and reflects
isomorphisms; and the two ways of forming `A' ⊗_A P_n` — tensoring in `ModuleCat A`, and base
change of algebras followed by forgetting to abelian groups — give *equal* simplicial objects of
`AddCommGrpCat`, which is `CommAlgCat.simplicialBaseChange_comp_forget`. Only the augmentations
differ, and they differ exactly by `a' ⊗ x ↦ a' · b(x)`.

**The augmentation of the Moore complex is Mathlib's.**
`AlgebraicTopology.AlternatingFaceMapComplex.ε` is the natural map `s(X_•) ⟶ (single₀).obj Z`
attached to an augmented simplicial object, with degree-zero component the augmentation; and for
the *constant* augmented object it is a homotopy equivalence,
`SimplicialObject.Augmented.ExtraDegeneracy.const`. Naturality of it in the augmented object
therefore factors the comparison `s(P_•) ⟶ (single₀).obj B` as the Moore complex of `ε` followed
by a homotopy equivalence, which is where `QuasiIso` of the projective resolution's `π` comes
from. No exactness statement is proved by hand.

## References

* [Stacks Project, Tag 08QP](https://stacks.math.columbia.edu/tag/08QP)
* [Stacks Project, Tag 08QI](https://stacks.math.columbia.edu/tag/08QI)
* [Stacks Project, Tag 0661](https://stacks.math.columbia.edu/tag/0661)
* [Stacks Project, Tag 0660](https://stacks.math.columbia.edu/tag/0660)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology Opposite Simplicial
open scoped TensorProduct

universe u

namespace CommAlgCat

/-! ### Reading an augmented simplicial algebra in modules -/

/-- The forgetful functor from commutative `A`-algebras to `A`-modules. -/
abbrev toModuleCat (A : Type u) [CommRing A] : CommAlgCat.{u} A ⥤ ModuleCat.{u} A :=
  forget₂ (CommAlgCat.{u} A) (AlgCat.{u} A) ⋙ forget₂ (AlgCat.{u} A) (ModuleCat.{u} A)

/-- The forgetful functor from commutative `A`-algebras to abelian groups, spelled as the
criterion of Tag 08QI spells it. -/
abbrev toAddCommGrpCat (A : Type u) [CommRing A] : CommAlgCat.{u} A ⥤ AddCommGrpCat.{u} :=
  forget₂ (CommAlgCat.{u} A) (AlgCat.{u} A) ⋙ forget₂ (AlgCat.{u} A) (ModuleCat.{u} A) ⋙
    forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u}

section Module

variable {A : Type u} [CommRing A] {B : CommAlgCat.{u} A}
  {P : SimplicialObject (CommAlgCat.{u} A)}
  (ε : P ⟶ (SimplicialObject.const (CommAlgCat.{u} A)).obj B)

/-- An augmentation `ε : P_• ⟶ B` of a simplicial `A`-algebra, read as an augmentation of
simplicial `A`-modules. -/
def moduleAugmentation :
    (P ⋙ toModuleCat A) ⟶ (SimplicialObject.const (ModuleCat.{u} A)).obj
      ((toModuleCat A).obj B) where
  app n := (toModuleCat A).map (ε.app n)
  naturality m m' f := by
    have h := ε.naturality f
    simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id] at h ⊢
    rw [Functor.comp_map, ← Functor.map_comp, h]

/-- Forgetting the module structure of `CommAlgCat.moduleAugmentation` gives the augmentation of
abelian groups that the criterion of Tag 08QI is stated for. -/
lemma whiskerRight_moduleAugmentation :
    Functor.whiskerRight (moduleAugmentation ε)
        (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u}) =
      Functor.whiskerRight ε (toAddCommGrpCat A) := rfl

attribute [local instance] Functor.preservesHomologyOfExact

/-- The Moore complex of a whiskered morphism of simplicial modules is a quasi-isomorphism exactly
when the image of the Moore complex of the morphism under the additive functor is. -/
private lemma quasiIso_map_whiskerRight_iff {X Y : SimplicialObject (ModuleCat.{u} A)} (g : X ⟶ Y)
    (F : ModuleCat.{u} A ⥤ AddCommGrpCat.{u}) [F.Additive] :
    QuasiIso ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map
      ((alternatingFaceMapComplex (ModuleCat.{u} A)).map g)) ↔
    QuasiIso ((alternatingFaceMapComplex AddCommGrpCat.{u}).map (Functor.whiskerRight g F)) :=
  have hiso := alternatingFaceMapComplexCompMapHomologicalComplexIso
    (C := ModuleCat.{u} A) (D := AddCommGrpCat.{u}) F
  quasiIso_iff_of_arrow_mk_iso _ _
    (Arrow.isoMk (hiso.app X) (hiso.app Y) (hiso.hom.naturality g).symm)

/-- **The Moore complex of an augmentation is a quasi-isomorphism over `A` exactly when it is one
over `ℤ`.** `forget₂ (ModuleCat A) AddCommGrpCat` is additive, preserves homology — being exact —
and reflects isomorphisms, so it neither creates nor destroys quasi-isomorphisms; and the Moore
complex commutes with it. This is what lets the criterion of Tag 08QI, stated for abelian groups,
feed a projective resolution in `ModuleCat A`. -/
lemma quasiIso_mooreComplex_map_iff :
    QuasiIso ((alternatingFaceMapComplex (ModuleCat.{u} A)).map (moduleAugmentation ε)) ↔
      QuasiIso ((alternatingFaceMapComplex AddCommGrpCat.{u}).map
        (Functor.whiskerRight ε (toAddCommGrpCat A))) := by
  rw [← HomologicalComplex.quasiIso_map_iff_of_preservesHomology
    ((alternatingFaceMapComplex (ModuleCat.{u} A)).map (moduleAugmentation ε))
    (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})]
  exact quasiIso_map_whiskerRight_iff _ _

/-! ### The Moore complex of a resolution as a projective resolution -/

/-- The augmented simplicial `A`-module attached to an augmentation `ε : P_• ⟶ B`. -/
def augmentedModuleObject : SimplicialObject.Augmented (ModuleCat.{u} A) where
  left := P ⋙ toModuleCat A
  right := (toModuleCat A).obj B
  hom := moduleAugmentation ε

/-- The comparison `s(P_•) ⟶ (single₀).obj B` of Mathlib's
`AlgebraicTopology.AlternatingFaceMapComplex.ε`, for the augmentation `ε`. Its degree-zero
component is `ε₀` and it vanishes in positive degrees. -/
def mooreAugmentation :
    (alternatingFaceMapComplex (ModuleCat.{u} A)).obj (P ⋙ toModuleCat A) ⟶
      (ChainComplex.single₀ (ModuleCat.{u} A)).obj ((toModuleCat A).obj B) :=
  (AlternatingFaceMapComplex.ε (C := ModuleCat.{u} A)).app (augmentedModuleObject ε)

/-- The degree-zero component of `CommAlgCat.mooreAugmentation` is the augmentation in degree
zero. -/
@[simp]
lemma mooreAugmentation_f_zero :
    (mooreAugmentation ε).f 0 = (toModuleCat A).map (ε.app (op ⦋0⦌)) := by
  simp [mooreAugmentation, augmentedModuleObject, moduleAugmentation]

/-- The comparison `s(const B) ⟶ (single₀).obj B` for the *constant* augmented object; it is the
`hom` of a homotopy equivalence, by `SimplicialObject.Augmented.ExtraDegeneracy.const`. -/
abbrev mooreConstAugmentation (A : Type u) [CommRing A] (B : CommAlgCat.{u} A) :
    (alternatingFaceMapComplex (ModuleCat.{u} A)).obj
        ((SimplicialObject.const (ModuleCat.{u} A)).obj ((toModuleCat A).obj B)) ⟶
      (ChainComplex.single₀ (ModuleCat.{u} A)).obj ((toModuleCat A).obj B) :=
  (AlternatingFaceMapComplex.ε (C := ModuleCat.{u} A)).app
    (SimplicialObject.Augmented.const.obj ((toModuleCat A).obj B))

/-- `CommAlgCat.mooreConstAugmentation` is a quasi-isomorphism: it is the `hom` of the homotopy
equivalence supplied by the extra degeneracy of a constant augmented object. -/
lemma quasiIso_mooreConstAugmentation : QuasiIso (mooreConstAugmentation A B) :=
  inferInstanceAs (QuasiIso
    (SimplicialObject.Augmented.ExtraDegeneracy.const ((toModuleCat A).obj B)).homotopyEquiv.hom)

/-- **`CommAlgCat.mooreAugmentation` is the Moore complex of `ε` followed by the comparison for
the constant augmented object.** This is naturality of
`AlgebraicTopology.AlternatingFaceMapComplex.ε` at the morphism of augmented objects `(ε, 𝟙)`. -/
lemma mooreAugmentation_eq :
    mooreAugmentation ε = (alternatingFaceMapComplex (ModuleCat.{u} A)).map
      (moduleAugmentation ε) ≫ mooreConstAugmentation A B := by
  let f : augmentedModuleObject ε ⟶
      SimplicialObject.Augmented.const.obj ((toModuleCat A).obj B) :=
    { left := moduleAugmentation ε, right := 𝟙 _, w := by aesop_cat }
  have hleft : (SimplicialObject.Augmented.drop ⋙
      alternatingFaceMapComplex (ModuleCat.{u} A)).map f =
      (alternatingFaceMapComplex (ModuleCat.{u} A)).map (moduleAugmentation ε) := rfl
  have h := (AlternatingFaceMapComplex.ε (C := ModuleCat.{u} A)).naturality f
  have h2 : (SimplicialObject.Augmented.point ⋙
      ChainComplex.single₀ (ModuleCat.{u} A)).map f = 𝟙 _ :=
    CategoryTheory.Functor.map_id (ChainComplex.single₀ (ModuleCat.{u} A))
      ((toModuleCat A).obj B)
  rw [h2, hleft] at h
  exact h.symm

/-- `CommAlgCat.mooreAugmentation` is a quasi-isomorphism as soon as the Moore complex of `ε` is
one, the second factor of `CommAlgCat.mooreAugmentation_eq` being a homotopy equivalence. -/
lemma quasiIso_mooreAugmentation
    (hq : QuasiIso ((alternatingFaceMapComplex (ModuleCat.{u} A)).map (moduleAugmentation ε))) :
    QuasiIso (mooreAugmentation ε) := by
  rw [mooreAugmentation_eq ε]
  exact (quasiIso_iff_comp_right (hφ' := quasiIso_mooreConstAugmentation) _ _).2 hq

/-- Every term of the Moore complex of a degreewise polynomial simplicial algebra is a projective
`A`-module: a polynomial algebra is free over `A` on its monomials. -/
lemma projective_mooreComplex_X (hP : ∀ n, IsPolynomialAlgebra A (P.obj n)) (n : ℕ) :
    Projective (((alternatingFaceMapComplex (ModuleCat.{u} A)).obj (P ⋙ toModuleCat A)).X n) := by
  obtain ⟨ι, ⟨e⟩⟩ := hP (op ⦋n⦌)
  exact ModuleCat.projective_of_free
    ((MvPolynomial.basisMonomials ι A).map e.toLinearEquiv)

/-- **The Moore complex of a resolution of `B` over `A` is a projective resolution of `B` in
`ModuleCat A`.** The terms are projective because the terms of the simplicial algebra are
polynomial algebras, hence free `A`-modules; and the comparison to `B` in degree zero is a
quasi-isomorphism because the resolution property says the Moore complex of `ε` is one
(Tag 08QI). -/
def mooreProjectiveResolution (hP : ∀ n, IsPolynomialAlgebra A (P.obj n))
    (hq : QuasiIso ((alternatingFaceMapComplex AddCommGrpCat.{u}).map
      (Functor.whiskerRight ε (toAddCommGrpCat A)))) :
    ProjectiveResolution ((toModuleCat A).obj B) where
  complex := (alternatingFaceMapComplex (ModuleCat.{u} A)).obj (P ⋙ toModuleCat A)
  projective := projective_mooreComplex_X hP
  π := mooreAugmentation ε
  quasiIso := quasiIso_mooreAugmentation ε ((quasiIso_mooreComplex_map_iff ε).2 hq)

/-- The complex of `CommAlgCat.mooreProjectiveResolution` is the Moore complex of the simplicial
`A`-module underlying `P`. -/
@[simp]
lemma mooreProjectiveResolution_complex (hP : ∀ n, IsPolynomialAlgebra A (P.obj n))
    (hq : QuasiIso ((alternatingFaceMapComplex AddCommGrpCat.{u}).map
      (Functor.whiskerRight ε (toAddCommGrpCat A)))) :
    (mooreProjectiveResolution ε hP hq).complex =
      (alternatingFaceMapComplex (ModuleCat.{u} A)).obj (P ⋙ toModuleCat A) := rfl

/-- The augmentation of `CommAlgCat.mooreProjectiveResolution` is
`CommAlgCat.mooreAugmentation ε`. -/
@[simp]
lemma mooreProjectiveResolution_π (hP : ∀ n, IsPolynomialAlgebra A (P.obj n))
    (hq : QuasiIso ((alternatingFaceMapComplex AddCommGrpCat.{u}).map
      (Functor.whiskerRight ε (toAddCommGrpCat A)))) :
    (mooreProjectiveResolution ε hP hq).π = mooreAugmentation ε := rfl

end Module

/-! ### Base change along a derived-Cartesian square -/

section BaseChange

variable {A A' : Type u} [CommRing A] [CommRing A'] [Algebra A A']
  {B : CommAlgCat.{u} A} {B' : CommAlgCat.{u} A'}
  [Algebra A (B' : Type u)] [IsScalarTower A A' (B' : Type u)]
  (b : (B : Type u) →ₐ[A] (B' : Type u))
  {P : SimplicialObject (CommAlgCat.{u} A)}
  (ε : P ⟶ (SimplicialObject.const (CommAlgCat.{u} A)).obj B)

/-- Tensoring with `A'` over `A`, as an endofunctor of `A`-modules. This is the functor whose
left derived functors are `Tor_*^A(A', -)`. -/
abbrev tensorByBase (A A' : Type u) [CommRing A] [CommRing A'] [Algebra A A'] :
    ModuleCat.{u} A ⥤ ModuleCat.{u} A :=
  (MonoidalCategory.tensoringLeft (ModuleCat.{u} A)).obj (ModuleCat.of A A')

/-- **The two ways of forming `A' ⊗_A P_•` agree.** Tensoring the simplicial `A`-module
underlying `P_•` with `A'` and forgetting to abelian groups is the simplicial algebra
`CommAlgCat.simplicialBaseChange` forgotten to abelian groups — not merely isomorphic to it, but
equal: both are `A' ⊗_A P_n` in degree `n`, with the same additive maps. -/
lemma simplicialBaseChange_comp_forget :
    (P ⋙ toModuleCat A) ⋙ (tensorByBase A A' ⋙
        forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u}) =
      simplicialBaseChange b ε ⋙ toAddCommGrpCat A' := rfl

/-- The degree-zero part of the hypothesis of Stacks 08QP: the canonical map
`A' ⊗_A B → B'`, `a' ⊗ x ↦ a' · b(x)`. -/
abbrev baseChangeUnit : (A' ⊗[A] (B : Type u)) →ₐ[A'] (B' : Type u) :=
  baseChangeAugmentation b (Over.mk (𝟙 B))

/-- `CommAlgCat.baseChangeUnit b` sends `a' ⊗ x` to `a' · b(x)`. -/
@[simp]
lemma baseChangeUnit_tmul (a' : A') (x : (B : Type u)) :
    baseChangeUnit b (a' ⊗ₜ[A] x) = algebraMap A' (B' : Type u) a' * b x :=
  baseChangeAugmentation_tmul b (Over.mk (𝟙 B)) a' x

/-- `CommAlgCat.baseChangeUnit` is bijective when the square is a pushout of rings: the pushout
isomorphism `B ⊗_A A' ≃ B'` is the same map read through the commutativity of the tensor
product. -/
lemma bijective_baseChangeUnit_of_isPushout
    [Algebra (B : Type u) (B' : Type u)] [IsScalarTower A (B : Type u) (B' : Type u)]
    [Algebra.IsPushout A (B : Type u) A' (B' : Type u)]
    (hb : ∀ x : (B : Type u), b x = algebraMap (B : Type u) (B' : Type u) x) :
    Function.Bijective (baseChangeUnit b) := by
  have h : ∀ z : A' ⊗[A] (B : Type u), baseChangeUnit b z =
      Algebra.IsPushout.equiv A (B : Type u) A' (B' : Type u)
        ((Algebra.TensorProduct.comm A A' (B : Type u)) z) := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul a' x => simp [Algebra.IsPushout.equiv_tmul, hb x, mul_comm]
    | add z w hz hw => simp only [map_add, hz, hw]
  rw [show (baseChangeUnit b : A' ⊗[A] (B : Type u) → (B' : Type u)) =
    (Algebra.IsPushout.equiv A (B : Type u) A' (B' : Type u)) ∘
      (Algebra.TensorProduct.comm A A' (B : Type u)) from funext h]
  exact (Algebra.IsPushout.equiv A (B : Type u) A' (B' : Type u)).bijective.comp
    (Algebra.TensorProduct.comm A A' (B : Type u)).bijective

/-- The comparison of the two base-changed augmentations in their target: the identity on
`A' ⊗_A P_•` and `CommAlgCat.baseChangeUnit` on the constant part. -/
def baseChangeAugmentationComparison :
    ((SimplicialObject.const (ModuleCat.{u} A)).obj ((toModuleCat A).obj B)) ⋙
        (tensorByBase A A' ⋙ forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u}) ⟶
      ((SimplicialObject.const (CommAlgCat.{u} A')).obj B') ⋙ toAddCommGrpCat A' where
  app _ := AddCommGrpCat.ofHom (baseChangeUnit b).toAddMonoidHom
  naturality _ _ _ := by
    simp
    rfl

/-- The base-changed augmentation in degree `n`, written as `A' ⊗_A ε_n` followed by
`CommAlgCat.baseChangeUnit`. Both send `a' ⊗ p` to `a' · b(ε_n(p))`. -/
lemma augmentationBaseChange_app_eq (n : SimplexCategoryᵒᵖ)
    (z : A' ⊗[A] (P.obj n : Type u)) :
    ((augmentationBaseChange b ε).app n).hom z =
      baseChangeUnit b (TensorProduct.map (LinearMap.id : A' →ₗ[A] A')
        ((ε.app n).hom.toLinearMap) z) := by
  set φ := TensorProduct.map (LinearMap.id : A' →ₗ[A] A') ((ε.app n).hom.toLinearMap) with hφdef
  induction z using TensorProduct.inductionOn with
  | tmul a' p =>
    refine (augmentationBaseChange_app_tmul b ε n a' p).trans ?_
    rw [hφdef, TensorProduct.map_tmul, baseChangeUnit_tmul]
    rfl
  | add z w hz hw =>
    have h : ((augmentationBaseChange b ε).app n).hom (z + w) =
        ((augmentationBaseChange b ε).app n).hom z +
          ((augmentationBaseChange b ε).app n).hom w := map_add _ z w
    rw [h, map_add, map_add, hz, hw]

/-- **The base-changed augmentation factors through the tensor product in `ModuleCat A`.**
Forgetting to abelian groups, `A' ⊗_A ε` is `A' ⊗_A (-)` applied to `ε`, followed by
`CommAlgCat.baseChangeUnit` on the constant part. -/
lemma whiskerRight_augmentationBaseChange :
    Functor.whiskerRight (augmentationBaseChange b ε) (toAddCommGrpCat A') =
      Functor.whiskerRight (moduleAugmentation ε)
          (tensorByBase A A' ⋙ forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u}) ≫
        baseChangeAugmentationComparison b :=
  NatTrans.ext (funext fun n => AddCommGrpCat.hom_ext (AddMonoidHom.ext fun z =>
    augmentationBaseChange_app_eq b ε n z))

/-- `CommAlgCat.baseChangeAugmentationComparison` is an isomorphism when
`CommAlgCat.baseChangeUnit` is bijective, that is when the degree-zero part of the hypothesis of
Stacks 08QP holds. -/
lemma isIso_baseChangeAugmentationComparison
    (hφ : Function.Bijective (baseChangeUnit b)) :
    IsIso (baseChangeAugmentationComparison b (B := B) (B' := B')) := by
  have : ∀ n, IsIso ((baseChangeAugmentationComparison b (B := B) (B' := B')).app n) :=
    fun _ => (ConcreteCategory.isIso_iff_bijective _).2 hφ
  exact NatIso.isIso_of_isIso_app _

attribute [local instance] Functor.preservesHomologyOfExact

/-- Under Tor independence, tensoring with `A'` carries the Moore complex of `ε`, viewed as a map
of complexes of `A`-modules, to a quasi-isomorphism. -/
lemma quasiIso_tensorByBase_map_mooreComplex
    (hP : ∀ n, IsPolynomialAlgebra A (P.obj n))
    (hq : QuasiIso ((alternatingFaceMapComplex AddCommGrpCat.{u}).map
      (Functor.whiskerRight ε (toAddCommGrpCat A))))
    (hTor : RingTheory.TorIndependence.TorIndependent A A' (B : Type u)) :
    QuasiIso (((tensorByBase A A').mapHomologicalComplex
      (ComplexShape.down ℕ)).map ((alternatingFaceMapComplex (ModuleCat.{u} A)).map
        (moduleAugmentation ε))) := by
  -- Tor independence makes `A' ⊗_A -` carry the projective resolution to a quasi-isomorphism.
  have hTensor : QuasiIso (((tensorByBase A A').mapHomologicalComplex
      (ComplexShape.down ℕ)).map (mooreProjectiveResolution ε hP hq).π) :=
    RingTheory.TorIndependence.quasiIso_tensor_map_projectiveResolution_of_isZero_Tor
      (ModuleCat.of A A') ((toModuleCat A).obj B) (mooreProjectiveResolution ε hP hq)
      ((RingTheory.TorIndependence.torIndependent_iff_isZero_tor A A' (B : Type u)).1 hTor)
  -- Strip the homotopy equivalence `s(const B) ⟶ (single₀).obj B` from `π`.
  have hconst : QuasiIso (((tensorByBase A A').mapHomologicalComplex
      (ComplexShape.down ℕ)).map (mooreConstAugmentation A B)) :=
    inferInstanceAs (QuasiIso
      ((tensorByBase A A').mapHomotopyEquiv
        (SimplicialObject.Augmented.ExtraDegeneracy.const
          ((toModuleCat A).obj B)).homotopyEquiv).hom)
  have hcomp : ((tensorByBase A A').mapHomologicalComplex (ComplexShape.down ℕ)).map
      (mooreProjectiveResolution ε hP hq).π =
      ((tensorByBase A A').mapHomologicalComplex (ComplexShape.down ℕ)).map
          ((alternatingFaceMapComplex (ModuleCat.{u} A)).map (moduleAugmentation ε)) ≫
        ((tensorByBase A A').mapHomologicalComplex (ComplexShape.down ℕ)).map
          (mooreConstAugmentation A B) := by
    rw [mooreProjectiveResolution_π, mooreAugmentation_eq ε]
    exact Functor.map_comp _ _ _
  rw [hcomp] at hTensor
  exact (quasiIso_iff_comp_right (hφ' := hconst) _ _).1 hTensor

/-- **The Moore complex of the base-changed augmentation is a quasi-isomorphism.** This is the
source's computation: `s(P_•)` is a projective resolution of `B` in `ModuleCat A`, so
`s(A' ⊗_A P_•) = A' ⊗_A s(P_•)` computes `B ⊗_A^L A'`; Tor independence kills the higher
homology and `CommAlgCat.baseChangeUnit` identifies the degree-zero part with `B'`. -/
lemma quasiIso_moore_augmentationBaseChange
    (hP : ∀ n, IsPolynomialAlgebra A (P.obj n))
    (hq : QuasiIso ((alternatingFaceMapComplex AddCommGrpCat.{u}).map
      (Functor.whiskerRight ε (toAddCommGrpCat A))))
    (hTor : RingTheory.TorIndependence.TorIndependent A A' (B : Type u))
    (hφ : Function.Bijective (baseChangeUnit b)) :
    QuasiIso ((alternatingFaceMapComplex AddCommGrpCat.{u}).map
      (Functor.whiskerRight (augmentationBaseChange b ε) (toAddCommGrpCat A'))) := by
  have hmod := quasiIso_tensorByBase_map_mooreComplex ε hP hq hTor
  -- Forget the module structure; the composite functor is `A' ⊗_A -` landing in abelian groups.
  have hgrp : QuasiIso ((((tensorByBase A A' ⋙
      forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u}).mapHomologicalComplex
        (ComplexShape.down ℕ))).map ((alternatingFaceMapComplex (ModuleCat.{u} A)).map
          (moduleAugmentation ε))) :=
    inferInstanceAs (QuasiIso (((forget₂ (ModuleCat.{u} A)
      AddCommGrpCat.{u}).mapHomologicalComplex (ComplexShape.down ℕ)).map
        (((tensorByBase A A').mapHomologicalComplex (ComplexShape.down ℕ)).map _)))
  have hwhisk := (quasiIso_map_whiskerRight_iff (moduleAugmentation ε)
    (tensorByBase A A' ⋙ forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})).1 hgrp
  -- Finally compare the two augmentations.
  have := isIso_baseChangeAugmentationComparison b (B := B) (B' := B') hφ
  have hsplit : (alternatingFaceMapComplex AddCommGrpCat.{u}).map
      (Functor.whiskerRight (augmentationBaseChange b ε) (toAddCommGrpCat A')) =
      (alternatingFaceMapComplex AddCommGrpCat.{u}).map
          (Functor.whiskerRight (moduleAugmentation ε)
            (tensorByBase A A' ⋙ forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})) ≫
        (alternatingFaceMapComplex AddCommGrpCat.{u}).map
          (baseChangeAugmentationComparison b) := by
    rw [whiskerRight_augmentationBaseChange b ε]
    exact Functor.map_comp _ _ _
  rw [hsplit]
  exact (quasiIso_iff_comp_right _ _).2 hwhisk

/-- The base-changed augmentation is degreewise surjective when `A' ⊗_A B → B'` is surjective
and `ε` is surjective in degree zero: every element of `B'` comes from `A' ⊗_A B`, and
`A' ⊗_A P_n → A' ⊗_A B` hits it because the range of an additive map is closed under
addition. -/
lemma surjective_augmentationBaseChange_of_surjective
    (hε0 : Function.Surjective (ε.app (op ⦋0⦌)).hom)
    (hφ : Function.Surjective (baseChangeUnit b)) (n : SimplexCategoryᵒᵖ) :
    Function.Surjective ((augmentationBaseChange b ε).app n).hom := by
  have hεn := surjective_app_of_surjective_app_zero ε hε0 n
  have hmap : Function.Surjective (TensorProduct.map (LinearMap.id : A' →ₗ[A] A')
      ((ε.app n).hom.toLinearMap)) := LinearMap.lTensor_surjective A' hεn
  intro y
  obtain ⟨z, hz⟩ := hφ y
  obtain ⟨w, hw⟩ := hmap z
  exact ⟨w, (augmentationBaseChange_app_eq b ε n w).trans (by rw [hw, hz])⟩

/-- **Stacks 08QP, first half: the base change of a resolution along a derived-Cartesian square is
a resolution.** Let `ε : P_• ⟶ B` be a resolution of `B` over `A` in the sense of Tag 08QI, and
assume the square induces a quasi-isomorphism `B ⊗_A^L A' = B'`, which is to say that
`Tor_i^A(A', B)` vanishes for `i > 0` and the canonical map `A' ⊗_A B → B'` is bijective. Then
`A' ⊗_A P_• ⟶ B'` is a resolution of `B'` over `A'`.

The criterion of Tag 08QI applies: the terms `A' ⊗_A P_n` are polynomial algebras over `A'` on
the same variables, the augmentation is degreewise surjective because `A' ⊗_A B → B'` is, and the
Moore complex is a quasi-isomorphism by
`CommAlgCat.quasiIso_moore_augmentationBaseChange`. -/
theorem isResolution_augmentationBaseChange
    (hres : IsResolution A (B : Type u) P ε)
    (hTor : RingTheory.TorIndependence.TorIndependent A A' (B : Type u))
    (hφ : Function.Bijective (baseChangeUnit b)) :
    IsResolution A' (B' : Type u) (simplicialBaseChange b ε) (augmentationBaseChange b ε) := by
  have hε0 := SSet.surjective_app_zero_of_trivialKanFibrations hres.trivialKanFibration
  have htfae := isResolution_quasiIso_homotopyEquivalence_tfae A (B : Type u) P ε
    hres.isPolynomialAlgebra (surjective_app_of_surjective_app_zero ε hε0)
  have hq := (htfae.out 1 2).1 hres
  have htfae' := isResolution_quasiIso_homotopyEquivalence_tfae A' (B' : Type u)
    (simplicialBaseChange b ε) (augmentationBaseChange b ε)
    (isPolynomialAlgebra_simplicialBaseChange b ε hres.isPolynomialAlgebra)
    (surjective_augmentationBaseChange_of_surjective b ε hε0 hφ.surjective)
  exact (htfae'.out 2 1).1
    (quasiIso_moore_augmentationBaseChange b ε hres.isPolynomialAlgebra hq hTor hφ)

/-- **Stacks 08QP, first half**, with the degree-zero half of the hypothesis supplied by
`Algebra.IsPushout`: if `B'` is a pushout of `B` and `A'` over `A`, with `b` the structure map,
and `A'` and `B` are Tor independent over `A`, then the base change of a resolution is a
resolution. -/
theorem isResolution_augmentationBaseChange_of_isPushout
    [Algebra (B : Type u) (B' : Type u)] [IsScalarTower A (B : Type u) (B' : Type u)]
    [Algebra.IsPushout A (B : Type u) A' (B' : Type u)]
    (hb : ∀ x : (B : Type u), b x = algebraMap (B : Type u) (B' : Type u) x)
    (hres : IsResolution A (B : Type u) P ε)
    (hTor : RingTheory.TorIndependence.TorIndependent A A' (B : Type u)) :
    IsResolution A' (B' : Type u) (simplicialBaseChange b ε) (augmentationBaseChange b ε) :=
  isResolution_augmentationBaseChange b ε hres hTor
    (bijective_baseChangeUnit_of_isPushout b hb)

end BaseChange

end CommAlgCat

end
