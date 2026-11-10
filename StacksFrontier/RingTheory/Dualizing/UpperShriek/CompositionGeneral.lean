module

public import Mathlib.RingTheory.TensorProduct.MvPolynomial
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.Composition
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.FlatBaseChange
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.PolynomialExtension
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.RingEquivIso
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.RingEquivIsoLarge

/-!
# Composing algebraic upper shriek along two homomorphisms of finite type

Let `a : R →+* A` and `b : A →+* B` be of finite type, presented by `p` with `n` variables and
`q` with `m` variables.  Adjoining the `m` variables of `q` to the polynomial algebra of `p`
gives `T = R[x_1, …, x_n][y_1, …, y_m]`, and flattening it to `R[z_1, …, z_{n+m}]` produces a
presentation `p.comp q` of `b ∘ a` with `n + m` variables.  This file builds the transformation

`b^! ∘ a^! ⟶ (b ∘ a)^!`

at those presentations, and shows that it is invertible at `K` whenever a single flat base change
comparison of derived Hom is invertible at `K ⊗_R^L R[x_1, …, x_n]`.  No Noetherian hypothesis
is made.

## Main definitions

* `Dualizing.flattenPolynomial` — the identification `R[x][y] ≃ R[z_1, …, z_{n+m}]`.
* `Dualizing.PolynomialPresentation.comp` — the presentation of `b ∘ a` induced by a
  presentation of `a` and one of `b`.
* `Dualizing.flatDerivedExtensionLarge` — derived extension of scalars along a flat homomorphism,
  at a module universe above the rings.
* `Dualizing.polynomialDerivedHomBaseChange` — the base-change map of derived Hom at the square
  `P, A, P[y_1, …, y_m], A ⊗_P P[y_1, …, y_m]` of a presentation and `m` new variables.

## Main results

* `Dualizing.PolynomialPresentation.exists_upperShriekComp` — a transformation
  `b^! ∘ a^! ⟶ (b ∘ a)^!` at `p`, `q` and `p.comp q`, invertible at `K` whenever
  `Dualizing.polynomialDerivedHomBaseChange` is invertible at `K ⊗_R^L P`.
* `Dualizing.PolynomialPresentation.nonempty_upperShriekComp` — the existence of that
  transformation.

## Implementation notes

Upper shriek depends on the presentation and is well defined only up to isomorphism
(`Dualizing.PolynomialPresentation.nonempty_upperShriekFunctor_iso`).  Every statement here is
made at named presentations, the transformation being built at the induced presentation
`p.comp q`.

The three rings live in one universe `u` and the modules in an arbitrary universe `max v u`.  The
flat extensions of scalars along the polynomial algebras are therefore taken at that module
universe, as `Dualizing.flatDerivedExtensionLarge`, and so are the transports along the ring
isomorphisms `A ⊗_P P[y] ≃ A[y]` and `P[y] ≃ R[z]`.

## References

* [Stacks Project, Tag 0BZT](https://stacks.math.columbia.edu/tag/0BZT)
* [Stacks Project, Tag 0BZM](https://stacks.math.columbia.edu/tag/0BZM)
* [Stacks Project, Tag 0E29](https://stacks.math.columbia.edu/tag/0E29)
* [Stacks Project, Tag 0C0F](https://stacks.math.columbia.edu/tag/0C0F)
* [Stacks Project, Tag 08YU](https://stacks.math.columbia.edu/tag/08YU)
-/

@[expose] public section

open CategoryTheory
open scoped TensorProduct

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Dualizing

noncomputable section

/-- **Flattening a polynomial algebra over a polynomial algebra.**  Adjoining `m` variables to
`R[x_1, …, x_n]` gives the polynomial algebra on `n + m` variables over `R`. -/
def flattenPolynomial (R : Type u) [CommRing R] (n m : ℕ) :
    MvPolynomial (Fin m) (MvPolynomial (Fin n) R) ≃ₐ[R] MvPolynomial (Fin (n + m)) R :=
  let P := MvPolynomial (Fin n) R
  let e₁ : P ⊗[R] MvPolynomial (Fin m) R ≃ₐ[P] MvPolynomial (Fin m) P :=
    MvPolynomial.algebraTensorAlgEquiv R P
  let e₂ : P ⊗[R] MvPolynomial (Fin m) R ≃ₐ[R] MvPolynomial (Fin n ⊕ Fin m) R :=
    MvPolynomial.tensorEquivSum R (Fin n) (Fin m) R
  let e₃ : MvPolynomial (Fin n ⊕ Fin m) R ≃ₐ[R] MvPolynomial (Fin (n + m)) R :=
    MvPolynomial.renameEquiv R (finSumFinEquiv (m := n) (n := m))
  (e₁.restrictScalars R).symm.trans (e₂.trans e₃)

namespace PolynomialPresentation

variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]

/-- **The presentation of `b ∘ a` induced by a presentation of `a` and one of `b`.**  The
polynomial algebra is the one on the `n` variables of the first presentation together with the
`m` variables of the second, and the surjection onto the target is `χ ∘ P[y] → A[y]`, the second
presentation's surjection composed with the first one's after adjoining the new variables. -/
def comp {a : R →+* A} {b : A →+* B} (p : PolynomialPresentation a)
    (q : PolynomialPresentation b) : PolynomialPresentation (b.comp a) := by
  let T := MvPolynomial (Fin q.variableCount) p.Poly
  let h : T →+* B := q.toRingHom.comp (MvPolynomial.map p.toRingHom)
  let e := flattenPolynomial R p.variableCount q.variableCount
  have hp (x : R) : p.toRingHom (MvPolynomial.C x) = a x := by
    simpa only [RingHom.comp_apply] using congrArg (fun f : R →+* A => f x) p.commutes
  have hq (y : A) : q.toRingHom (MvPolynomial.C y) = b y := by
    simpa only [RingHom.comp_apply] using congrArg (fun f : A →+* B => f y) q.commutes
  have hcomm : h.comp ((MvPolynomial.C : p.Poly →+* T).comp
      (MvPolynomial.C : R →+* p.Poly)) = b.comp a := by
    ext x
    change q.toRingHom (MvPolynomial.map p.toRingHom
      (MvPolynomial.C (MvPolynomial.C x))) = b (a x)
    rw [MvPolynomial.map_C, hq, hp]
  have hsurj : Function.Surjective h :=
    q.surjective.comp (MvPolynomial.map_surjective p.toRingHom p.surjective)
  refine ⟨p.variableCount + q.variableCount, h.comp e.symm.toRingHom, ?_, ?_⟩
  · rw [RingHom.comp_assoc]
    have heC : e.symm.toRingHom.comp (MvPolynomial.C : R →+* _) =
        (MvPolynomial.C : p.Poly →+* T).comp (MvPolynomial.C : R →+* p.Poly) :=
      RingHom.ext fun x => e.symm.commutes x
    rw [heC, hcomm]
  · exact hsurj.comp e.symm.surjective

/-- The number of variables of `p.comp q` is the sum of the numbers of variables of `p` and `q`. -/
@[simp]
theorem comp_variableCount {a : R →+* A} {b : A →+* B} (p : PolynomialPresentation a)
    (q : PolynomialPresentation b) :
    (p.comp q).variableCount = p.variableCount + q.variableCount :=
  rfl

/-- The surjection of `p.comp q` is `q.toRingHom ∘ MvPolynomial.map p.toRingHom`, precomposed
with the inverse of the flattening equivalence `flattenPolynomial`. -/
theorem comp_toRingHom {a : R →+* A} {b : A →+* B} (p : PolynomialPresentation a)
    (q : PolynomialPresentation b) :
    (p.comp q).toRingHom =
      (q.toRingHom.comp (MvPolynomial.map p.toRingHom)).comp
        (flattenPolynomial R p.variableCount q.variableCount).symm.toRingHom :=
  rfl

end PolynomialPresentation

/-- The natural transformation exhibiting `Dualizing.flatDerivedExtension f hf` as a left derived
functor of extension of scalars along the flat homomorphism `f`. -/
def flatDerivedExtensionFactors {X Y : Type u} [CommRing X] [CommRing Y]
    (f : X →+* Y) (hf : f.Flat) :
    DerivedCategory.Q ⋙ flatDerivedExtension f hf ⟶
      (ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q := by
  let : Limits.PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u} f) :=
    extendScalars_preservesFiniteLimits_of_flat' f hf
  exact (ModuleCat.extendScalars.{u, u, u} f).mapDerivedCategoryFactors.hom

/-- `Dualizing.flatDerivedExtension` is a left derived functor of extension of scalars, with
comparison `Dualizing.flatDerivedExtensionFactors`. -/
theorem flatDerivedExtension_isLeftDerived {X Y : Type u} [CommRing X] [CommRing Y]
    (f : X →+* Y) (hf : f.Flat) :
    (flatDerivedExtension f hf).IsLeftDerivedFunctor (flatDerivedExtensionFactors f hf)
      (HomologicalComplex.quasiIso (ModuleCat.{u} X) (ComplexShape.up ℤ)) := by
  let : Limits.PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u} f) :=
    extendScalars_preservesFiniteLimits_of_flat' f hf
  exact Functor.isLeftDerivedFunctor_of_inverts _ _
    (ModuleCat.extendScalars.{u, u, u} f).mapDerivedCategoryFactors

/-- Derived extension of scalars along flat homomorphisms composes. -/
def flatDerivedExtensionComp {X Y Z : Type u} [CommRing X] [CommRing Y] [CommRing Z]
    (f : X →+* Y) (g : Y →+* Z) (hf : f.Flat) (hg : g.Flat) :
    flatDerivedExtension f hf ⋙ flatDerivedExtension g hg ≅
      flatDerivedExtension (g.comp f) (hf.comp hg) :=
  letI := flatDerivedExtension_isLeftDerived f hf
  letI := flatDerivedExtension_isLeftDerived g hg
  letI := flatDerivedExtension_isLeftDerived (g.comp f) (hf.comp hg)
  StacksDraft.DerivedRingEquivIso.derivedExtensionCompIso.{u, 0} f g _
    (flatDerivedExtensionFactors f hf) _ (flatDerivedExtensionFactors g hg) _
    (flatDerivedExtensionFactors (g.comp f) (hf.comp hg))

/-- Derived extension of scalars along a flat homomorphism, at the module universe `max v u`: the
functor induced on derived categories by the exact functor of extension of scalars. -/
def flatDerivedExtensionLarge {X Y : Type u} [CommRing X] [CommRing Y] (f : X →+* Y)
    (hf : f.Flat) :
    DerivedCategory (ModuleCat.{max v u} X) ⥤ DerivedCategory (ModuleCat.{max v u} Y) :=
  letI : Limits.PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, max v u} f) :=
    extendScalars_preservesFiniteLimits_of_flat'.{u, v} f hf
  (ModuleCat.extendScalars.{u, u, max v u} f).mapDerivedCategory

/-- The comparison exhibiting `Dualizing.flatDerivedExtensionLarge` as a left derived functor of
extension of scalars. -/
def flatDerivedExtensionLargeFactors {X Y : Type u} [CommRing X] [CommRing Y]
    (f : X →+* Y) (hf : f.Flat) :
    DerivedCategory.Q ⋙ flatDerivedExtensionLarge.{u, v} f hf ⟶
      (ModuleCat.extendScalars.{u, u, max v u} f).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q := by
  let : Limits.PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, max v u} f) :=
    extendScalars_preservesFiniteLimits_of_flat'.{u, v} f hf
  exact (ModuleCat.extendScalars.{u, u, max v u} f).mapDerivedCategoryFactors.hom

/-- `Dualizing.flatDerivedExtensionLarge` is a left derived functor of extension of scalars, with
comparison `Dualizing.flatDerivedExtensionLargeFactors`. -/
theorem flatDerivedExtensionLarge_isLeftDerived {X Y : Type u} [CommRing X] [CommRing Y]
    (f : X →+* Y) (hf : f.Flat) :
    (flatDerivedExtensionLarge.{u, v} f hf).IsLeftDerivedFunctor
      (flatDerivedExtensionLargeFactors.{u, v} f hf)
      (HomologicalComplex.quasiIso (ModuleCat.{max v u} X) (ComplexShape.up ℤ)) := by
  let : Limits.PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, max v u} f) :=
    extendScalars_preservesFiniteLimits_of_flat'.{u, v} f hf
  exact Functor.isLeftDerivedFunctor_of_inverts _ _
    (ModuleCat.extendScalars.{u, u, max v u} f).mapDerivedCategoryFactors

/-- Derived extension of scalars along flat homomorphisms composes, at the module universe
`max v u`. -/
def flatDerivedExtensionLargeComp {X Y Z : Type u} [CommRing X] [CommRing Y] [CommRing Z]
    (f : X →+* Y) (g : Y →+* Z) (hf : f.Flat) (hg : g.Flat) :
    flatDerivedExtensionLarge.{u, v} f hf ⋙ flatDerivedExtensionLarge.{u, v} g hg ≅
      flatDerivedExtensionLarge.{u, v} (g.comp f) (hf.comp hg) :=
  letI := flatDerivedExtensionLarge_isLeftDerived.{u, v} f hf
  letI := flatDerivedExtensionLarge_isLeftDerived.{u, v} g hg
  letI := flatDerivedExtensionLarge_isLeftDerived.{u, v} (g.comp f) (hf.comp hg)
  StacksDraft.DerivedRingEquivIso.derivedExtensionCompIso.{u, v} f g _
    (flatDerivedExtensionLargeFactors f hf) _ (flatDerivedExtensionLargeFactors g hg) _
    (flatDerivedExtensionLargeFactors (g.comp f) (hf.comp hg))

/-- Reading the pushout `A ⊗_P P[y_1, …, y_m]` as `A[y_1, …, y_m]` carries the inclusion of the
polynomial algebra `P[y_1, …, y_m]` to the map `MvPolynomial.map f` induced by `f : P →+* A`. -/
theorem polynomialTensorIncludeRight_eq {P A : Type u} [CommRing P] [CommRing A]
    (f : P →+* A) (m : ℕ) :
    letI : Algebra P A := f.toAlgebra
    (MvPolynomial.algebraTensorAlgEquiv P A (σ := Fin m)).toRingEquiv.toRingHom.comp
        (Algebra.TensorProduct.includeRight :
          MvPolynomial (Fin m) P →ₐ[P] TensorProduct P A (MvPolynomial (Fin m) P)).toRingHom =
      MvPolynomial.map f := by
  let : Algebra P A := f.toAlgebra
  apply MvPolynomial.ringHom_ext <;> intro <;>
    simp [MvPolynomial.algebraTensorAlgEquiv_tmul, RingHom.algebraMap_toAlgebra]

/-- **The base-change map of derived Hom at the square of a presentation and `m` new
variables.**  For a presentation `p` of `a : R →+* A` with polynomial algebra `P`, the square
`P → A`, `P → T = P[y_1, …, y_m]` with pushout `A ⊗_P T` gives

`RHom_P(A, -) ⊗_A^L (A ⊗_P T) ⟶ RHom_T(A ⊗_P T, - ⊗_P^L T)` ,

natural in the object of `D(P)`. -/
def polynomialDerivedHomBaseChange {R A : Type u} [CommRing R] [CommRing A] {a : R →+* A}
    (p : PolynomialPresentation a) (m : ℕ) :
    letI : Algebra p.Poly A := p.toRingHom.toAlgebra
    derivedHom.{u, v} (algebraMap p.Poly A) ⋙
        flatDerivedExtensionLarge.{u, v}
          (algebraMap A (TensorProduct p.Poly A (MvPolynomial (Fin m) p.Poly)))
          (RingHom.flat_algebraMap_iff.mpr inferInstance) ⟶
      flatDerivedExtensionLarge.{u, v} (algebraMap p.Poly (MvPolynomial (Fin m) p.Poly))
          (RingHom.flat_algebraMap_iff.mpr inferInstance) ⋙
        derivedHom.{u, v} (Algebra.TensorProduct.includeRight :
          MvPolynomial (Fin m) p.Poly →ₐ[p.Poly]
            TensorProduct p.Poly A (MvPolynomial (Fin m) p.Poly)).toRingHom := by
  letI : Algebra p.Poly A := p.toRingHom.toAlgebra
  let T := MvPolynomial (Fin m) p.Poly
  have hT : (algebraMap p.Poly T).Flat := RingHom.flat_algebraMap_iff.mpr inferInstance
  have hA : (algebraMap A (TensorProduct p.Poly A T)).Flat :=
    RingHom.flat_algebraMap_iff.mpr inferInstance
  exact derivedHomBaseChange.{u, u, u, v}
    (torIndependent_of_flat_right (R := p.Poly) (A := A) (B := T))
    (flatDerivedExtensionLarge.{u, v} (algebraMap p.Poly T) hT)
    (flatDerivedExtensionLargeFactors.{u, v} (algebraMap p.Poly T) hT)
    (flatDerivedExtensionLarge_isLeftDerived.{u, v} (algebraMap p.Poly T) hT)
    (flatDerivedExtensionLarge.{u, v} (algebraMap A (TensorProduct p.Poly A T)) hA)
    (flatDerivedExtensionLargeFactors.{u, v} (algebraMap A (TensorProduct p.Poly A T)) hA)
    (flatDerivedExtensionLarge_isLeftDerived.{u, v} (algebraMap A (TensorProduct p.Poly A T)) hA)

/-- **Derived Hom along a ring isomorphism of the source.**  Precomposing `f` with a ring
isomorphism `e` of its source and reading the result through the equivalence of derived
categories that `e` induces gives back derived Hom along `f`. -/
def derivedHomDomainRingEquivIso {X X' Y : Type u} [CommRing X] [CommRing X'] [CommRing Y]
    (e : X' ≃+* X) (f : X →+* Y) :
    (mapDerivedCategoryEquivalenceOfEquivalence
        (ModuleCat.restrictScalarsEquivalenceOfRingEquiv.{u, u, max v u} e)).functor ⋙
        derivedHom.{u, v} (f.comp e.toRingHom) ≅
      derivedHom.{u, v} f :=
  StacksDraft.DerivedRingEquivIso.derivedHomRingEquivIsoLarge.{u, v} e (RingEquiv.refl Y) f ≪≫
    Functor.isoWhiskerLeft _
      (StacksDraft.DerivedRingEquivIso.mapDerivedCategoryIdIsoLarge.{u, v} (B := Y)) ≪≫
    Functor.rightUnitor _

/-- **The pushout corner of the square of a presentation is a polynomial algebra over the
target.**  Derived extension of scalars along `A → A ⊗_P P[y_1, …, y_m]`, read through the
identification `A ⊗_P P[y] ≃ A[y]`, is derived extension of scalars along `A → A[y_1, …, y_m]` —
that is, the derived base change of a presentation with `m` variables. -/
def polynomialExtensionBaseChangeIso {R A : Type u} [CommRing R] [CommRing A] {a : R →+* A}
    (p : PolynomialPresentation a) (m : ℕ) :
    letI : Algebra p.Poly A := p.toRingHom.toAlgebra
    flatDerivedExtensionLarge.{u, v}
          (algebraMap A (TensorProduct p.Poly A (MvPolynomial (Fin m) p.Poly)))
          (RingHom.flat_algebraMap_iff.mpr inferInstance) ⋙
        (mapDerivedCategoryEquivalenceOfEquivalence
          (ModuleCat.restrictScalarsEquivalenceOfRingEquiv.{u, u, max v u}
            (MvPolynomial.algebraTensorAlgEquiv p.Poly A
              (σ := Fin m)).toRingEquiv.symm)).functor ≅
      flatDerivedExtensionLarge.{u, v} (MvPolynomial.C : A →+* MvPolynomial (Fin m) A)
        (RingHom.flat_algebraMap_iff.mpr inferInstance) := by
  letI : Algebra p.Poly A := p.toRingHom.toAlgebra
  let T := MvPolynomial (Fin m) p.Poly
  let Push := TensorProduct p.Poly A T
  let eB := (MvPolynomial.algebraTensorAlgEquiv p.Poly A (σ := Fin m)).toRingEquiv
  have hA : (algebraMap A Push).Flat := RingHom.flat_algebraMap_iff.mpr inferInstance
  have heB : eB.toRingHom.Flat := RingHom.Flat.of_bijective eB.bijective
  have hcomp : (eB.toRingHom.comp (algebraMap A Push)).Flat := hA.comp heB
  have hmap : eB.toRingHom.comp (algebraMap A Push) =
      (MvPolynomial.C : A →+* MvPolynomial (Fin m) A) :=
    RingHom.ext fun x =>
      (MvPolynomial.algebraTensorAlgEquiv p.Poly A (σ := Fin m)).commutes x
  have h := @StacksDraft.DerivedRingEquivIso.derivedExtensionRingEquivIsoRightLarge.{u, v}
    _ _ _ _ _ _ eB.symm (algebraMap A Push)
    (flatDerivedExtensionLarge.{u, v} (algebraMap A Push) hA)
    (flatDerivedExtensionLargeFactors.{u, v} (algebraMap A Push) hA)
    (flatDerivedExtensionLarge_isLeftDerived.{u, v} (algebraMap A Push) hA)
    (flatDerivedExtensionLarge.{u, v} (eB.toRingHom.comp (algebraMap A Push)) hcomp)
    (flatDerivedExtensionLargeFactors.{u, v} (eB.toRingHom.comp (algebraMap A Push)) hcomp)
    (flatDerivedExtensionLarge_isLeftDerived.{u, v} (eB.toRingHom.comp (algebraMap A Push)) hcomp)
  refine Iso.symm ?_
  simpa only [hmap] using h

/-- **Flattening the two polynomial algebras of a composite presentation.**  Derived base change
along `R → P = R[x_1, …, x_n]` followed by derived extension of scalars along
`P → T = P[y_1, …, y_m]`, read through the identification `T ≃ R[z_1, …, z_{n+m}]`, is the
derived base change of the composite presentation. -/
def polynomialFlattenExtensionIso {R A : Type u} [CommRing R] [CommRing A] {a : R →+* A}
    (p : PolynomialPresentation a) (m : ℕ) :
    p.derivedExtension.{u, v} ⋙
        flatDerivedExtensionLarge.{u, v} (algebraMap p.Poly (MvPolynomial (Fin m) p.Poly))
            (RingHom.flat_algebraMap_iff.mpr inferInstance) ⋙
          (mapDerivedCategoryEquivalenceOfEquivalence
            (ModuleCat.restrictScalarsEquivalenceOfRingEquiv.{u, u, max v u}
              (flattenPolynomial R p.variableCount m).toRingEquiv.symm)).functor ≅
      flatDerivedExtensionLarge.{u, v}
        (MvPolynomial.C : R →+* MvPolynomial (Fin (p.variableCount + m)) R)
        (RingHom.flat_algebraMap_iff.mpr inferInstance) := by
  let P := p.Poly
  let T := MvPolynomial (Fin m) P
  let eF := (flattenPolynomial R p.variableCount m).toRingEquiv
  have hC : (MvPolynomial.C : R →+* P).Flat := RingHom.flat_algebraMap_iff.mpr inferInstance
  have hT : (algebraMap P T).Flat := RingHom.flat_algebraMap_iff.mpr inferInstance
  have hAT : ((algebraMap P T).comp (MvPolynomial.C : R →+* P)).Flat := hC.comp hT
  have heF : eF.toRingHom.Flat := RingHom.Flat.of_bijective eF.bijective
  have hH : (eF.toRingHom.comp ((algebraMap P T).comp (MvPolynomial.C : R →+* P))).Flat :=
    hAT.comp heF
  have hmap : eF.toRingHom.comp ((algebraMap P T).comp (MvPolynomial.C : R →+* P)) =
      (MvPolynomial.C : R →+* MvPolynomial (Fin (p.variableCount + m)) R) :=
    RingHom.ext fun x => (flattenPolynomial R p.variableCount m).commutes x
  have h := @StacksDraft.DerivedRingEquivIso.derivedExtensionRingEquivIsoRightLarge.{u, v}
    _ _ _ _ _ _ eF.symm ((algebraMap P T).comp (MvPolynomial.C : R →+* P))
    (flatDerivedExtensionLarge.{u, v} ((algebraMap P T).comp (MvPolynomial.C : R →+* P)) hAT)
    (flatDerivedExtensionLargeFactors.{u, v} ((algebraMap P T).comp (MvPolynomial.C : R →+* P)) hAT)
    (flatDerivedExtensionLarge_isLeftDerived.{u, v}
      ((algebraMap P T).comp (MvPolynomial.C : R →+* P)) hAT)
    (flatDerivedExtensionLarge.{u, v} (eF.toRingHom.comp ((algebraMap P T).comp MvPolynomial.C)) hH)
    (flatDerivedExtensionLargeFactors.{u, v}
      (eF.toRingHom.comp ((algebraMap P T).comp MvPolynomial.C)) hH)
    (flatDerivedExtensionLarge_isLeftDerived.{u, v}
      (eF.toRingHom.comp ((algebraMap P T).comp MvPolynomial.C)) hH)
  refine (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight
    (flatDerivedExtensionLargeComp.{u, v} (MvPolynomial.C : R →+* P) (algebraMap P T) hC hT) _ ≪≫
    Iso.symm ?_
  simpa only [hmap] using h

namespace PolynomialPresentation

/-- **The composition transformation of upper shriek at a pair of presentations.**  Let `p`
present `a : R →+* A` with `n` variables and `q` present `b : A →+* B` with `m` variables.  Then
there is a transformation

`b^!(a^!(K)) ⟶ (b ∘ a)^!(K)`

of functors `D(R) ⥤ D(B)`, upper shriek being read at `p`, at `q` and at the induced
presentation `p.comp q` of `b ∘ a`, which is invertible at `K` as soon as the base-change map
`Dualizing.polynomialDerivedHomBaseChange p m` at the square
`P, A, P[y_1, …, y_m], A ⊗_P P[y_1, …, y_m]` is invertible at `K ⊗_R^L P`.

No hypothesis is made on the rings; the invertibility at `K` takes the invertibility of that
base-change map at `K ⊗_R^L P` as its hypothesis.  The modules live in an arbitrary universe
`max v u` above the universe `u` of the rings. -/
theorem exists_upperShriekComp {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    {a : R →+* A} {b : A →+* B} (p : PolynomialPresentation a)
    (q : PolynomialPresentation b) :
    ∃ τ : p.upperShriekFunctor.{u, v} ⋙ q.upperShriekFunctor.{u, v} ⟶
        (p.comp q).upperShriekFunctor.{u, v},
      ∀ K, IsIso ((polynomialDerivedHomBaseChange p q.variableCount).app
          (p.derivedExtension.{u, v}.obj K)) → IsIso (τ.app K) := by
  let : Algebra p.Poly A := p.toRingHom.toAlgebra
  let P := p.Poly
  let T := MvPolynomial (Fin q.variableCount) P
  let Push := TensorProduct P A T
  let eB := (MvPolynomial.algebraTensorAlgEquiv P A (σ := Fin q.variableCount)).toRingEquiv
  let EB := mapDerivedCategoryEquivalenceOfEquivalence
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv.{u, u, max v u} eB.symm)
  let eF := (flattenPolynomial R p.variableCount q.variableCount).toRingEquiv
  let EF := mapDerivedCategoryEquivalenceOfEquivalence
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv.{u, u, max v u} eF.symm)
  let r := p.comp q
  let E := p.derivedExtension.{u, v}
  let Hp := derivedHom.{u, v} p.toRingHom
  let G := q.derivedExtension.{u, v}
  let J := derivedHom.{u, v} q.toRingHom
  have hT : (algebraMap P T).Flat := RingHom.flat_algebraMap_iff.mpr inferInstance
  have hA : (algebraMap A Push).Flat := RingHom.flat_algebraMap_iff.mpr inferInstance
  let dT := flatDerivedExtensionLarge.{u, v} (algebraMap P T) hT
  let dA := flatDerivedExtensionLarge.{u, v} (algebraMap A Push) hA
  let ri := (Algebra.TensorProduct.includeRight : T →ₐ[P] Push).toRingHom
  let I := derivedHom.{u, v} ri
  let hTB : T →+* B := q.toRingHom.comp (MvPolynomial.map p.toRingHom)
  let Jh := derivedHom.{u, v} hTB
  let Jr := derivedHom.{u, v} r.toRingHom
  let s := shiftFunctor (DerivedCategory (ModuleCat.{max v u} B))
    ((p.variableCount + q.variableCount : ℕ) : ℤ)
  let : G.CommShift ℤ := by
    dsimp only [G, PolynomialPresentation.derivedExtension]
    infer_instance
  obtain ⟨hJcs⟩ := nonempty_commShift_derivedHom.{u, v} q.toRingHom
  let : J.CommShift ℤ := hJcs
  let post := EB.functor ⋙ J ⋙ s
  let eQ : dA ⋙ EB.functor ≅ G := polynomialExtensionBaseChangeIso p q.variableCount
  let eSource : p.upperShriekFunctor.{u, v} ⋙ q.upperShriekFunctor.{u, v} ≅
      E ⋙ (Hp ⋙ dA) ⋙ post :=
    Functor.isoWhiskerLeft (E ⋙ Hp)
        (Functor.isoWhiskerRight ((G ⋙ J).commShiftIso (p.variableCount : ℤ))
            (shiftFunctor (DerivedCategory (ModuleCat.{max v u} B)) (q.variableCount : ℤ)) ≪≫
          Functor.isoWhiskerLeft (G ⋙ J)
            (shiftFunctorAdd' (DerivedCategory (ModuleCat.{max v u} B)) (p.variableCount : ℤ)
              (q.variableCount : ℤ) ((p.variableCount + q.variableCount : ℕ) : ℤ)
              (by push_cast; ring)).symm) ≪≫
      Functor.isoWhiskerLeft (E ⋙ Hp) (Functor.isoWhiskerRight eQ.symm (J ⋙ s))
  let δ : Hp ⋙ dA ⟶ dT ⋙ I := polynomialDerivedHomBaseChange p q.variableCount
  have he : (q.toRingHom.comp eB.toRingHom).comp eB.symm.toRingHom = q.toRingHom :=
    RingHom.ext fun x => congrArg q.toRingHom (eB.apply_symm_apply x)
  have hcomp : (q.toRingHom.comp eB.toRingHom).comp ri = hTB := by
    rw [RingHom.comp_assoc]
    exact congrArg (fun f : T →+* MvPolynomial (Fin q.variableCount) A =>
      q.toRingHom.comp f) (polynomialTensorIncludeRight_eq p.toRingHom q.variableCount)
  obtain ⟨eCompHom⟩ := derivedHomCompIso.{u, v} ri (q.toRingHom.comp eB.toRingHom)
  let eHom : I ⋙ EB.functor ⋙ J ≅ Jh :=
    Functor.isoWhiskerLeft I
        (Functor.isoWhiskerLeft EB.functor
            (eqToIso (congrArg (fun f : MvPolynomial (Fin q.variableCount) A →+* B =>
              derivedHom.{u, v} f) he)).symm ≪≫
          derivedHomDomainRingEquivIso eB.symm (q.toRingHom.comp eB.toRingHom)) ≪≫
      eCompHom ≪≫ eqToIso (congrArg (fun f : T →+* B => derivedHom.{u, v} f) hcomp)
  let eFlatHom : EF.functor ⋙ Jr ≅ Jh := derivedHomDomainRingEquivIso eF.symm hTB
  let eExt : E ⋙ dT ⋙ EF.functor ≅ r.derivedExtension.{u, v} :=
    polynomialFlattenExtensionIso p q.variableCount
  let eTarget : E ⋙ (dT ⋙ I) ⋙ post ≅ r.upperShriekFunctor.{u, v} :=
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft (E ⋙ dT) eHom ≪≫
        Functor.isoWhiskerLeft (E ⋙ dT) eFlatHom.symm ≪≫
        Functor.isoWhiskerRight eExt Jr) s
  refine ⟨eSource.hom ≫ Functor.whiskerLeft E (Functor.whiskerRight δ post) ≫ eTarget.hom, ?_⟩
  intro K hδ
  have : IsIso ((Functor.whiskerLeft E (Functor.whiskerRight δ post)).app K) := by
    change IsIso (post.map (δ.app (E.obj K)))
    infer_instance
  change IsIso (eSource.hom.app K ≫
    (Functor.whiskerLeft E (Functor.whiskerRight δ post)).app K ≫ eTarget.hom.app K)
  infer_instance

/-- **The composition transformation of upper shriek.**  For presentations `p` of `a : R →+* A`
and `q` of `b : A →+* B` there is a transformation `q^! ∘ p^! ⟶ (p.comp q)^!` of functors
`D(R) ⥤ D(B)`. -/
theorem nonempty_upperShriekComp {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    {a : R →+* A} {b : A →+* B} (p : PolynomialPresentation a)
    (q : PolynomialPresentation b) :
    Nonempty (p.upperShriekFunctor.{u, v} ⋙ q.upperShriekFunctor.{u, v} ⟶
      (p.comp q).upperShriekFunctor.{u, v}) :=
  ⟨(p.exists_upperShriekComp q).choose⟩

end PolynomialPresentation

end

end Dualizing

end
