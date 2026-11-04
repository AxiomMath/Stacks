module

public import StacksFrontier.Algebra.Homology.DerivedCategory.ProjectiveCorepresents
public import StacksFrontier.RingTheory.Dualizing.DerivedHomothety.Equivariance
public import StacksFrontier.RingTheory.Dualizing.TrivialDuality

/-!
# The cohomology of derived Hom is corepresented by the unit

Let `f : S → T` be a homomorphism of commutative rings and let `Y` be an object of `D(S)`.  The
derived coextension functor `RHom_S(T, -) : D(S) ⥤ D(T)` of
`StacksFrontier/RingTheory/Dualizing/TrivialDuality.lean` is right adjoint to restriction of scalars,
and `T` is free of rank one over itself, hence projective; so the degree-`j` cohomology of
`RHom_S(T, Y)` is the group of morphisms in `D(S)` from `T`, restricted to `S` along `f` and placed
in degree zero, into `Y⟦j⟧`:

`H^j(RHom_S(T, Y)) ≅ Hom_{D(S)}(T[0], Y⟦j⟧)`.

The identification is `T`-linear, the `T`-module structure on the right-hand side being the one on
the *first* argument: `t` acts by precomposition with multiplication by `t` on `T[0]`, which is
`Dualizing.smulRestrictedUnitSingle`.

This is the first of the links separating the degreewise chase of [stacks 0E2F] (2) from the
hypotheses `hvan` and `h0` of `Dualizing.isRelativeDualizingComplex_baseChange_of_homology`; see
the module documentation of
`StacksFrontier/RingTheory/Dualizing/RelativeBaseChangeTorIndependence.lean`.  Applied at
`f = Δ' : B' → A'` it reads `H^j(RHom_{B'}(A', Y)) ≅ Hom_{D(B')}(A'[0], Y⟦j⟧)`, which is the side
of [stacks 0E1U]'s representability clause that the chase computes.

## Main definitions

* `Dualizing.restrictedUnitSingle` — `T`, viewed as an `S`-module through `f` and placed in a
  given degree; at `f = Δ'` this is `A'[n]` in `D(B')`.
* `Dualizing.smulRestrictedUnitSingle` — multiplication by `t` on it, which is the `T`-action on
  the first argument.
* `Dualizing.derivedHomHomologyAddEquiv` — the identification, additively.
* `Dualizing.derivedHomHomologyLinearEquiv` — the identification, `T`-linearly, for the
  `T`-module structure `Dualizing.smulHomRestrictedUnitSingle` by precomposition.

## Main results

* `Dualizing.derivedHomHomologyAddEquiv_smul` — **the `T`-linearity**: the additive identification
  carries the module structure of `H^j(RHom_S(T, Y))` to precomposition with multiplication.
* `Dualizing.nonempty_derivedHomHomologyAddEquiv` and
  `Dualizing.nonempty_derivedHomHomologyLinearEquiv` — the same with the adjunction, which
  `Dualizing.restrictScalarsDerived_adj_derivedHom` provides only as a `Nonempty`, discharged.

## Implementation notes

Both halves of the composition are already in the library: the adjunction is
`Dualizing.restrictScalarsDerived_adj_derivedHom`, and corepresentability of degree-`j` cohomology
by a projective object placed in degree `j` is
`DerivedCategory.homologyFromSingleLinearEquiv`, which is `T`-linear.  What this file adds is the
composite, and in particular the `T`-linearity of the adjunction bijection, which is *not* a
linearity of either adjoint functor: restriction of scalars forgets the `T`-structure, so `D(S)`
carries no `T`-linear structure at all and the `T`-action on `Hom_{D(S)}(T[0], Y⟦j⟧)` exists only
through the source object.  It is obtained from
`CategoryTheory.Adjunction.homEquiv_naturality_left_symm` applied to multiplication by `t` on the
free rank-one module, together with the `T`-linearity of
`DerivedCategory.singleFunctor (ModuleCat T) j`, which turns multiplication into the scalar
`t • 𝟙`.

The degree bookkeeping is done on the `D(S)` side: corepresentability is used at
`T[j]`, and `T[j] ≅ T[0]⟦-j⟧` (`CategoryTheory.SingleFunctors.shiftIso`) moves the shift to the
target through the adjunction of the shift equivalence.

Everything is at a single universe, which is all the application needs — `B'` and `A'` are both
`Type u` — and is what lets the free rank-one module be `ModuleCat.of T T` rather than a universe
lift of it as in `StacksFrontier/RingTheory/Dualizing/DerivedHomDuality/ExtComparison.lean`.

## References

* [Stacks Project, Tag 0E2F](https://stacks.math.columbia.edu/tag/0E2F)
* [Stacks Project, Tag 0E1U](https://stacks.math.columbia.edu/tag/0E1U)
-/

@[expose] public noncomputable section

open CategoryTheory

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Dualizing

variable {S T : Type u} [CommRing S] [CommRing T] (f : S →+* T)

/-- Evaluation at `1` identifies the morphisms out of the free rank-one module with the module
itself, `T`-linearly. -/
def evalOneLinearEquiv (N : ModuleCat.{u} T) : (ModuleCat.of T T ⟶ N) ≃ₗ[T] N :=
  (ModuleCat.homLinearEquiv (S := T)).trans (LinearMap.ringLmapEquivSelf T T N)

/-- `T`, viewed as an `S`-module through `f` and placed in degree `n` of the derived category of
`S`-modules.  For `f = Δ' : B' → A'` this is `A'[n]` in `D(B')`. -/
abbrev restrictedUnitSingle (n : ℤ) : DerivedCategory (ModuleCat.{u} S) :=
  (DerivedCategory.singleFunctor (ModuleCat.{u} S) n).obj
    ((ModuleCat.restrictScalars.{u} f).obj (ModuleCat.of T T))

/-- Multiplication by `t` on `T`, read as an endomorphism of `Dualizing.restrictedUnitSingle`.
This is the `T`-action on the first argument of `Hom_{D(S)}(T[n], -)`. -/
def smulRestrictedUnitSingle (t : T) (n : ℤ) :
    restrictedUnitSingle f n ⟶ restrictedUnitSingle f n :=
  (DerivedCategory.singleFunctor (ModuleCat.{u} S) n).map
    ((ModuleCat.restrictScalars.{u} f).map (t • 𝟙 (ModuleCat.of T T)))

/-- Multiplication by `1` on `Dualizing.restrictedUnitSingle` is the identity. -/
@[simp] theorem smulRestrictedUnitSingle_one (n : ℤ) :
    smulRestrictedUnitSingle f (1 : T) n = 𝟙 _ := by
  rw [smulRestrictedUnitSingle, one_smul, CategoryTheory.Functor.map_id,
    CategoryTheory.Functor.map_id]

/-- Multiplication by `0` on `Dualizing.restrictedUnitSingle` is the zero morphism. -/
@[simp] theorem smulRestrictedUnitSingle_zero (n : ℤ) :
    smulRestrictedUnitSingle f (0 : T) n = 0 := by
  rw [smulRestrictedUnitSingle, zero_smul, Functor.map_zero, Functor.map_zero]

/-- Multiplication by `t₁ * t₂` on `Dualizing.restrictedUnitSingle` is the composite of
multiplication by `t₁` and multiplication by `t₂`. -/
theorem smulRestrictedUnitSingle_mul (t₁ t₂ : T) (n : ℤ) :
    smulRestrictedUnitSingle f (t₁ * t₂) n =
      smulRestrictedUnitSingle f t₁ n ≫ smulRestrictedUnitSingle f t₂ n := by
  have h : (t₁ * t₂) • 𝟙 (ModuleCat.of T T) =
      (t₁ • 𝟙 (ModuleCat.of T T)) ≫ (t₂ • 𝟙 (ModuleCat.of T T)) := by
    rw [Linear.smul_comp, Category.id_comp, smul_smul]
  rw [smulRestrictedUnitSingle, smulRestrictedUnitSingle, smulRestrictedUnitSingle, h,
    CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]

/-- Multiplication by `t₁ + t₂` on `Dualizing.restrictedUnitSingle` is the sum of multiplication
by `t₁` and multiplication by `t₂`. -/
theorem smulRestrictedUnitSingle_add (t₁ t₂ : T) (n : ℤ) :
    smulRestrictedUnitSingle f (t₁ + t₂) n =
      smulRestrictedUnitSingle f t₁ n + smulRestrictedUnitSingle f t₂ n := by
  rw [smulRestrictedUnitSingle, smulRestrictedUnitSingle, smulRestrictedUnitSingle, add_smul,
    Functor.map_add, Functor.map_add]

/-- The free rank-one `T`-module in degree `j`, restricted to `S`, is `T` restricted to `S` in
degree zero and shifted by `-j`. -/
def restrictedUnitSingleIso (j : ℤ) :
    (CategoryTheory.shiftFunctor (DerivedCategory (ModuleCat.{u} S)) (-j)).obj
        (restrictedUnitSingle f 0) ≅
      (ModuleCat.restrictScalars.{u} f).mapDerivedCategory.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} T) j).obj (ModuleCat.of T T)) :=
  ((DerivedCategory.singleFunctors (ModuleCat.{u} S)).shiftIso (-j) j 0
      (neg_add_cancel j)).app ((ModuleCat.restrictScalars.{u} f).obj (ModuleCat.of T T)) ≪≫
    (((ModuleCat.restrictScalars.{u} f).mapDerivedCategorySingleFunctor j).app
      (ModuleCat.of T T)).symm

/-- `Dualizing.restrictedUnitSingleIso` is compatible with multiplication by `t`: on the left it
is the shift of `Dualizing.smulRestrictedUnitSingle` in degree zero, on the right the image under
restriction of multiplication on the free rank-one module in degree `j`. -/
theorem restrictedUnitSingleIso_hom_comp (t : T) (j : ℤ) :
    (restrictedUnitSingleIso f j).hom ≫
        (ModuleCat.restrictScalars.{u} f).mapDerivedCategory.map
          ((DerivedCategory.singleFunctor (ModuleCat.{u} T) j).map
            (t • 𝟙 (ModuleCat.of T T))) =
      (CategoryTheory.shiftFunctor (DerivedCategory (ModuleCat.{u} S)) (-j)).map
          (smulRestrictedUnitSingle f t 0) ≫ (restrictedUnitSingleIso f j).hom := by
  dsimp only [restrictedUnitSingleIso, smulRestrictedUnitSingle, Iso.trans_hom, Iso.symm_hom]
  set h : ModuleCat.of T T ⟶ ModuleCat.of T T := t • 𝟙 (ModuleCat.of T T) with hh
  set α := ((ModuleCat.restrictScalars.{u} f).mapDerivedCategorySingleFunctor j).app
    (ModuleCat.of T T) with hα'
  set β := ((DerivedCategory.singleFunctors (ModuleCat.{u} S)).shiftIso (-j) j 0
    (neg_add_cancel j)).app ((ModuleCat.restrictScalars.{u} f).obj (ModuleCat.of T T)) with hβ'
  have hα : (ModuleCat.restrictScalars.{u} f).mapDerivedCategory.map
        ((DerivedCategory.singleFunctor (ModuleCat.{u} T) j).map h) ≫ α.hom =
      α.hom ≫ (DerivedCategory.singleFunctor (ModuleCat.{u} S) j).map
        ((ModuleCat.restrictScalars.{u} f).map h) :=
    ((ModuleCat.restrictScalars.{u} f).mapDerivedCategorySingleFunctor j).hom.naturality h
  have hβ : (CategoryTheory.shiftFunctor (DerivedCategory (ModuleCat.{u} S)) (-j)).map
        ((DerivedCategory.singleFunctor (ModuleCat.{u} S) 0).map
          ((ModuleCat.restrictScalars.{u} f).map h)) ≫ β.hom =
      β.hom ≫ (DerivedCategory.singleFunctor (ModuleCat.{u} S) j).map
        ((ModuleCat.restrictScalars.{u} f).map h) :=
    ((DerivedCategory.singleFunctors (ModuleCat.{u} S)).shiftIso (-j) j 0
      (neg_add_cancel j)).hom.naturality ((ModuleCat.restrictScalars.{u} f).map h)
  have key : α.inv ≫ (ModuleCat.restrictScalars.{u} f).mapDerivedCategory.map
        ((DerivedCategory.singleFunctor (ModuleCat.{u} T) j).map h) =
      (DerivedCategory.singleFunctor (ModuleCat.{u} S) j).map
        ((ModuleCat.restrictScalars.{u} f).map h) ≫ α.inv := by
    rw [Iso.eq_comp_inv, Category.assoc, hα, Iso.inv_hom_id_assoc]
  rw [Category.assoc, key]
  simp only [← Category.assoc]
  rw [← hβ]

/-- The adjunction bijection of `Dualizing.restrictScalarsDerived_adj_derivedHom`, as an additive
equivalence. -/
def adjHomAddEquiv
    (adj : (ModuleCat.restrictScalars.{u} f).mapDerivedCategory ⊣ derivedHom.{u, u, u} f)
    (X : DerivedCategory (ModuleCat.{u} T)) (Y : DerivedCategory (ModuleCat.{u} S)) :
    (X ⟶ (derivedHom.{u, u, u} f).obj Y) ≃+
      ((ModuleCat.restrictScalars.{u} f).mapDerivedCategory.obj X ⟶ Y) :=
  AddEquiv.mk' (adj.homEquiv X Y).symm fun g h => by
    simp only [Adjunction.homEquiv_counit, Functor.map_add, Preadditive.add_comp]

/-- Shifting the target: `Hom(Z⟦-j⟧, Y) ≅ Hom(Z, Y⟦j⟧)`, as the adjunction bijection of the
equivalence given by shifting. -/
def shiftHomEquiv (Z Y : DerivedCategory (ModuleCat.{u} S)) (j : ℤ) :
    ((CategoryTheory.shiftFunctor (DerivedCategory (ModuleCat.{u} S)) (-j)).obj Z ⟶ Y) ≃
      (Z ⟶ (CategoryTheory.shiftFunctor (DerivedCategory (ModuleCat.{u} S)) j).obj Y) :=
  (CategoryTheory.shiftEquiv' (DerivedCategory (ModuleCat.{u} S)) (-j) j
    (neg_add_cancel j)).toAdjunction.homEquiv Z Y

/-- `Dualizing.shiftHomEquiv` sends `g` to the inverse of the isomorphism `Z⟦-j⟧⟦j⟧ ≅ Z` followed
by the shift of `g` by `j`. -/
theorem shiftHomEquiv_apply (Z Y : DerivedCategory (ModuleCat.{u} S)) (j : ℤ)
    (g : (CategoryTheory.shiftFunctor (DerivedCategory (ModuleCat.{u} S)) (-j)).obj Z ⟶ Y) :
    shiftHomEquiv Z Y j g =
      (CategoryTheory.shiftFunctorCompIsoId (DerivedCategory (ModuleCat.{u} S)) (-j) j
          (neg_add_cancel j)).inv.app Z ≫
        (CategoryTheory.shiftFunctor (DerivedCategory (ModuleCat.{u} S)) j).map g :=
  rfl

/-- Shifting the target: `Hom(Z⟦-j⟧, Y) ≅ Hom(Z, Y⟦j⟧)`, additively. -/
def shiftHomAddEquiv (Z Y : DerivedCategory (ModuleCat.{u} S)) (j : ℤ) :
    ((CategoryTheory.shiftFunctor (DerivedCategory (ModuleCat.{u} S)) (-j)).obj Z ⟶ Y) ≃+
      (Z ⟶ (CategoryTheory.shiftFunctor (DerivedCategory (ModuleCat.{u} S)) j).obj Y) :=
  AddEquiv.mk' (shiftHomEquiv Z Y j) fun g h => by
    rw [shiftHomEquiv_apply, shiftHomEquiv_apply, shiftHomEquiv_apply, Functor.map_add,
      Preadditive.comp_add]

/-- `Dualizing.shiftHomEquiv` is natural in the source object: precomposition with the shift of
`h` becomes precomposition with `h`. -/
theorem shiftHomEquiv_comp_left (Z Z' Y : DerivedCategory (ModuleCat.{u} S)) (j : ℤ)
    (h : Z ⟶ Z')
    (g : (CategoryTheory.shiftFunctor (DerivedCategory (ModuleCat.{u} S)) (-j)).obj Z' ⟶ Y) :
    shiftHomEquiv Z Y j
        ((CategoryTheory.shiftFunctor (DerivedCategory (ModuleCat.{u} S)) (-j)).map h ≫ g) =
      h ≫ shiftHomEquiv Z' Y j g := by
  have hn := (CategoryTheory.shiftFunctorCompIsoId (DerivedCategory (ModuleCat.{u} S)) (-j) j
    (neg_add_cancel j)).inv.naturality h
  simp only [Functor.comp_map, Functor.id_map] at hn
  rw [shiftHomEquiv_apply, shiftHomEquiv_apply, Functor.map_comp, ← Category.assoc, ← hn,
    Category.assoc]

/-- Precomposition with multiplication by `t` on the free rank-one module in degree `j` is the
scalar action of `t` on morphisms out of it. -/
theorem singleFunctor_map_smul_id_comp (j : ℤ) (t : T)
    (W : DerivedCategory (ModuleCat.{u} T))
    (u : (DerivedCategory.singleFunctor (ModuleCat.{u} T) j).obj (ModuleCat.of T T) ⟶ W) :
    (DerivedCategory.singleFunctor (ModuleCat.{u} T) j).map (t • 𝟙 (ModuleCat.of T T)) ≫ u =
      t • u := by
  rw [Functor.map_smul, CategoryTheory.Functor.map_id, Linear.smul_comp, Category.id_comp]

/-- Degree-`j` cohomology over `T` is corepresented, `T`-linearly, by the free rank-one module
placed in degree `j`: this is `DerivedCategory.homologyFromSingleLinearEquiv` with the
identification of morphisms out of `T` with `T` folded in. -/
def homologyLinearEquiv (W : DerivedCategory (ModuleCat.{u} T)) (j : ℤ) :
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} T) j).obj W) ≃ₗ[T]
      ((DerivedCategory.singleFunctor (ModuleCat.{u} T) j).obj (ModuleCat.of T T) ⟶ W) :=
  (evalOneLinearEquiv ((DerivedCategory.homologyFunctor (ModuleCat.{u} T) j).obj W)).symm.trans
    (DerivedCategory.homologyFromSingleLinearEquiv (ModuleCat.of T T) W j T).symm

/-- **The cohomology of derived Hom is corepresented by the unit.**  For `f : S → T` and `Y` in
`D(S)`, the degree-`j` cohomology of `RHom_S(T, Y)` is the group of morphisms from `T`, restricted
to `S` along `f` and placed in degree zero, into `Y⟦j⟧`.

This is the additive form; `Dualizing.derivedHomHomologyAddEquiv_smul` is the `T`-linearity, and
`Dualizing.derivedHomHomologyLinearEquiv` packages the two. -/
def derivedHomHomologyAddEquiv
    (adj : (ModuleCat.restrictScalars.{u} f).mapDerivedCategory ⊣ derivedHom.{u, u, u} f)
    (Y : DerivedCategory (ModuleCat.{u} S)) (j : ℤ) :
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} T) j).obj
        ((derivedHom.{u, u, u} f).obj Y)) ≃+
      (restrictedUnitSingle f 0 ⟶
        (CategoryTheory.shiftFunctor (DerivedCategory (ModuleCat.{u} S)) j).obj Y) :=
  ((homologyLinearEquiv ((derivedHom.{u, u, u} f).obj Y) j).toAddEquiv.trans
      ((adjHomAddEquiv f adj _ Y).trans
        (precompAddEquiv (restrictedUnitSingleIso f j) Y))).trans
    (shiftHomAddEquiv (restrictedUnitSingle f 0) Y j)

/-- An explicit formula for `Dualizing.derivedHomHomologyAddEquiv`: a cohomology class `x` is sent
to the image under `Dualizing.shiftHomEquiv` of `Dualizing.restrictedUnitSingleIso` followed by
the adjoint of the morphism corresponding to `x` under `Dualizing.homologyLinearEquiv`. -/
theorem derivedHomHomologyAddEquiv_apply
    (adj : (ModuleCat.restrictScalars.{u} f).mapDerivedCategory ⊣ derivedHom.{u, u, u} f)
    (Y : DerivedCategory (ModuleCat.{u} S)) (j : ℤ)
    (x : (DerivedCategory.homologyFunctor (ModuleCat.{u} T) j).obj
      ((derivedHom.{u, u, u} f).obj Y)) :
    derivedHomHomologyAddEquiv f adj Y j x =
      shiftHomEquiv (restrictedUnitSingle f 0) Y j
        ((restrictedUnitSingleIso f j).hom ≫
          (adj.homEquiv ((DerivedCategory.singleFunctor (ModuleCat.{u} T) j).obj
              (ModuleCat.of T T)) Y).symm
            (homologyLinearEquiv ((derivedHom.{u, u, u} f).obj Y) j x)) :=
  rfl

/-- **The `T`-linearity of the corepresentability of the cohomology of derived Hom.**  The additive
identification `Dualizing.derivedHomHomologyAddEquiv` carries the `T`-module structure of
`H^j(RHom_S(T, Y))` to precomposition with multiplication by `t` on `T[0]`, which is the `T`-action
on the first argument.

Restriction of scalars forgets the `T`-structure, so there is no `T`-linear structure on `D(S)` and
no `T`-linearity of either adjoint functor to appeal to; the statement is instead naturality of the
adjunction bijection in its first variable, at the morphism `t • 𝟙`. -/
theorem derivedHomHomologyAddEquiv_smul
    (adj : (ModuleCat.restrictScalars.{u} f).mapDerivedCategory ⊣ derivedHom.{u, u, u} f)
    (Y : DerivedCategory (ModuleCat.{u} S)) (j : ℤ) (t : T)
    (x : (DerivedCategory.homologyFunctor (ModuleCat.{u} T) j).obj
      ((derivedHom.{u, u, u} f).obj Y)) :
    derivedHomHomologyAddEquiv f adj Y j (t • x) =
      smulRestrictedUnitSingle f t 0 ≫ derivedHomHomologyAddEquiv f adj Y j x := by
  rw [derivedHomHomologyAddEquiv_apply, derivedHomHomologyAddEquiv_apply, map_smul,
    ← singleFunctor_map_smul_id_comp, Adjunction.homEquiv_naturality_left_symm,
    ← Category.assoc, restrictedUnitSingleIso_hom_comp, Category.assoc,
    shiftHomEquiv_comp_left]

/-- **The `T`-action on morphisms out of `T[n]` in `D(S)`**, by precomposition with multiplication.
This is the module structure in which `Dualizing.derivedHomHomologyLinearEquiv` is `T`-linear; it
is not an instance, since `D(S)` carries no `T`-linear structure and this action exists only
through the source object. -/
@[instance_reducible]
def smulHomRestrictedUnitSingle (n : ℤ) (Z : DerivedCategory (ModuleCat.{u} S)) :
    Module T (restrictedUnitSingle f n ⟶ Z) where
  smul t g := smulRestrictedUnitSingle f t n ≫ g
  one_smul g := by
    change smulRestrictedUnitSingle f (1 : T) n ≫ g = g
    rw [smulRestrictedUnitSingle_one, Category.id_comp]
  mul_smul t₁ t₂ g := by
    change smulRestrictedUnitSingle f (t₁ * t₂) n ≫ g = _ ≫ _ ≫ g
    rw [smulRestrictedUnitSingle_mul, Category.assoc]
  smul_zero t := Limits.comp_zero
  smul_add t g h := Preadditive.comp_add _ _ _ _ _ _
  add_smul t₁ t₂ g := by
    change smulRestrictedUnitSingle f (t₁ + t₂) n ≫ g = _ ≫ g + _ ≫ g
    rw [smulRestrictedUnitSingle_add, Preadditive.add_comp]
  zero_smul g := by
    change smulRestrictedUnitSingle f (0 : T) n ≫ g = 0
    rw [smulRestrictedUnitSingle_zero, Limits.zero_comp]

attribute [local instance] smulHomRestrictedUnitSingle

/-- **The cohomology of derived Hom is corepresented by the unit, `T`-linearly.**  For `f : S → T`
and `Y` in `D(S)`, the degree-`j` cohomology of `RHom_S(T, Y)` is, as a `T`-module, the morphisms
from `T` restricted to `S` and placed in degree zero into `Y⟦j⟧`, with `T` acting on the source by
multiplication (`Dualizing.smulHomRestrictedUnitSingle`). -/
def derivedHomHomologyLinearEquiv
    (adj : (ModuleCat.restrictScalars.{u} f).mapDerivedCategory ⊣ derivedHom.{u, u, u} f)
    (Y : DerivedCategory (ModuleCat.{u} S)) (j : ℤ) :
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} T) j).obj
        ((derivedHom.{u, u, u} f).obj Y)) ≃ₗ[T]
      (restrictedUnitSingle f 0 ⟶
        (CategoryTheory.shiftFunctor (DerivedCategory (ModuleCat.{u} S)) j).obj Y) :=
  (derivedHomHomologyAddEquiv f adj Y j).toLinearEquiv
    (derivedHomHomologyAddEquiv_smul f adj Y j)

/-- `Dualizing.derivedHomHomologyAddEquiv` with the adjunction discharged:
`Dualizing.restrictScalarsDerived_adj_derivedHom` provides it only as a `Nonempty`. -/
theorem nonempty_derivedHomHomologyAddEquiv (Y : DerivedCategory (ModuleCat.{u} S)) (j : ℤ) :
    Nonempty (((DerivedCategory.homologyFunctor (ModuleCat.{u} T) j).obj
        ((derivedHom.{u, u, u} f).obj Y)) ≃+
      (restrictedUnitSingle f 0 ⟶
        (CategoryTheory.shiftFunctor (DerivedCategory (ModuleCat.{u} S)) j).obj Y)) :=
  ⟨derivedHomHomologyAddEquiv f (restrictScalarsDerived_adj_derivedHom.{u, u, u} f).some Y j⟩

/-- `Dualizing.derivedHomHomologyLinearEquiv` with the adjunction discharged. -/
theorem nonempty_derivedHomHomologyLinearEquiv (Y : DerivedCategory (ModuleCat.{u} S)) (j : ℤ) :
    letI := smulHomRestrictedUnitSingle f 0
      ((CategoryTheory.shiftFunctor (DerivedCategory (ModuleCat.{u} S)) j).obj Y)
    Nonempty (((DerivedCategory.homologyFunctor (ModuleCat.{u} T) j).obj
        ((derivedHom.{u, u, u} f).obj Y)) ≃ₗ[T]
      (restrictedUnitSingle f 0 ⟶
        (CategoryTheory.shiftFunctor (DerivedCategory (ModuleCat.{u} S)) j).obj Y)) :=
  ⟨derivedHomHomologyLinearEquiv f (restrictScalarsDerived_adj_derivedHom.{u, u, u} f).some Y j⟩

/-- **The vanishing form.**  If there are no nonzero morphisms from `T[0]` into `Y⟦j⟧`, then
`H^j(RHom_S(T, Y))` is zero.  This is the shape in which the hypothesis `hvan` of
`Dualizing.isRelativeDualizingComplex_baseChange_of_homology` is consumed: being zero in
`ModuleCat T` is detected on the underlying additive group
(`ModuleCat.isZero_iff_subsingleton`), so the additive identification suffices and the module
structure is not needed. -/
theorem isZero_homology_derivedHom_of_subsingleton (Y : DerivedCategory (ModuleCat.{u} S))
    (j : ℤ) (h : Subsingleton (restrictedUnitSingle f 0 ⟶
      (CategoryTheory.shiftFunctor (DerivedCategory (ModuleCat.{u} S)) j).obj Y)) :
    Limits.IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} T) j).obj
      ((derivedHom.{u, u, u} f).obj Y)) := by
  obtain ⟨e⟩ := nonempty_derivedHomHomologyAddEquiv f Y j
  have : Subsingleton ((DerivedCategory.homologyFunctor (ModuleCat.{u} T) j).obj
    ((derivedHom.{u, u, u} f).obj Y)) := Function.Injective.subsingleton e.injective
  exact ModuleCat.isZero_of_subsingleton _

/-- **The degree-zero form.**  If the morphisms from `T[0]` into `Y⟦j⟧` are `T` itself as a
`T`-module — `T` acting on the source by multiplication — then `H^j(RHom_S(T, Y))` is `T`.  This is
the shape in which the hypothesis `h0` of
`Dualizing.isRelativeDualizingComplex_baseChange_of_homology` is consumed, and here the module
structure is needed: the conclusion is an isomorphism in `ModuleCat T`. -/
theorem nonempty_homology_derivedHom_iso (Y : DerivedCategory (ModuleCat.{u} S)) (j : ℤ)
    (e : (restrictedUnitSingle f 0 ⟶
        (CategoryTheory.shiftFunctor (DerivedCategory (ModuleCat.{u} S)) j).obj Y) ≃ₗ[T] T) :
    Nonempty ((DerivedCategory.homologyFunctor (ModuleCat.{u} T) j).obj
      ((derivedHom.{u, u, u} f).obj Y) ≅ ModuleCat.of T T) :=
  ⟨((derivedHomHomologyLinearEquiv f
    (restrictScalarsDerived_adj_derivedHom.{u, u, u} f).some Y j).trans e).toModuleIso⟩

end Dualizing

end
