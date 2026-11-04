module

public import StacksFrontier.RingTheory.Koszul.DerivedComparison
public import StacksFrontier.RingTheory.Koszul.PowModuleSystems

/-!
# Comparing the two Koszul systems of modules in the derived category

Let `f₁, …, f_r` be elements of a commutative ring `R`, let `K_m` be the Koszul differential
graded algebra with `d ξᵢ = fᵢ ^ m` and fix `t ≥ 1`. Over the inverse system of Koszul algebras
there are the two systems of left differential graded modules
`Koszul.powRestrictedModuleSystem` and `Koszul.powBaseTensorModuleSystem` — the system
`({}_{t+n}K_t)` and the system `(K_{t+n} ⊗_R K_t)`. Tag 0GZJ compares their derived limits after
tensoring, and the step of its proof that appeals to Tag 0GZI needs the two systems to be
*pro-isomorphic in the derived category*: a strictly increasing sequence of indices carrying,
alternately, a comparison map of Tag 0GZ7 in one direction and a multiplication map in the other,
whose two composites are the transition maps of the two systems.

This file assembles that data and proves its two composition identities, over abstract
differential graded algebras and at the Koszul algebras.

* The comparison maps come from Tag 0GZ7 (`Koszul.exists_derivedComparisonArrow`), which for
  `n ≥ t ≥ 1` produces a map `σ : {}_NK_t ⟶ {}_N(K_n ⊗_R K_t)` in `D(K_N^{opp}, d)` for any
  `N ≥ n + t`; the maps in the other direction are the multiplication maps
  `μ_m : K_m ⊗_R K_t → K_t`.
* The indices are taken to be the multiples `t, 2t, 3t, …` of `t` measured from the base `t` of
  the system. That is what makes the bound `N ≥ n + t` of Tag 0GZ7 available at every stage while
  keeping every index of the form `t + (index of the system)`, so that no transport along an
  equality of natural numbers — hence none along an equality of Koszul algebras — is needed
  anywhere.
* The two composition identities are
  `DifferentialGraded.StrictModuleSystem.RegularComparison.fwdBwd` and
  `DifferentialGraded.StrictModuleSystem.RegularComparison.bwdFwd`; they are exactly the two
  conditions that `DifferentialGraded.ProIsoDerived` asks for.

## Main definitions

* `DifferentialGraded.StrictModuleSystem.RegularComparison`: the data comparing two strict
  inverse systems of *regular* differential graded modules — a fixed algebra `B` read over
  `A_n`, and algebras `C_n` with a commuting system of homomorphisms `A_n → C_n → B`, together
  with multiplication homomorphisms `C_n → B`.
* `DifferentialGraded.StrictModuleSystem.RegularComparison.restrSystem` and
  `DifferentialGraded.StrictModuleSystem.RegularComparison.tensorSystem`: the two strict inverse
  systems of differential graded modules it compares.
* `DifferentialGraded.StrictModuleSystem.RegularComparison.crossMulHom`,
  `crossStepHom` and `crossRestrHom`: the multiplication homomorphism, the transition
  homomorphism and the comparison of the two presentations of `C_n` over `A_m`.
* `Koszul.powRegularComparison`: the Koszul instance of that data.
* `Koszul.powArrowData` and `Koszul.powComparisonArrow`: the comparison maps of Tag 0GZ7 at the
  indices `t + t * (2i + 1) < t + t * (2i + 2)`.

## Main results

* `DifferentialGraded.StrictModuleSystem.RegularComparison.fwdBwd` and
  `DifferentialGraded.StrictModuleSystem.RegularComparison.bwdFwd`: **the two composition
  identities of a pro-isomorphism in the derived category**, for a single stage and over
  abstract differential graded algebras.
* `DifferentialGradedModule.derivedTrans_comp_left` and
  `DifferentialGradedModule.derivedTrans_restrictScalars`: the map in the derived category of a
  composite of homomorphisms of differential graded modules splits off a factor on either side.
* `Koszul.powMul_comp_tensorHomLeft`: the multiplication maps are compatible with the transition
  homomorphisms, `μ_n ∘ (τ_{N,n} ⊗ id) = μ_N`.
* `Koszul.powComparisonArrow_comp_powMulHom` and
  `Koszul.powMulBaseHom_comp_powComparisonArrow`: the two composites of Tag 0GZ7 at the chosen
  indices.

## Implementation notes

*Everything is proved over abstract algebras and instantiated.* The underlying module of a graded
opposite algebra is produced by a choice, so no identity about a homomorphism of graded opposite
Koszul algebras evaluated on an element is within the kernel's reach. Accordingly every
identification of underlying maps below is carried out for abstract differential graded algebras
— that is what `DifferentialGraded.StrictModuleSystem.RegularComparison` is for — and the Koszul
instance is an *application* whose hypotheses are all equations between homomorphisms of
differential graded algebras, which the Koszul development provides. For the same reason the
reassociations in the derived category are performed through lemmas stated for abstract
categories: in a localized category the two sides of a composition are presented at different
instance paths for `CategoryTheory.Quiver.Hom` and `CategoryTheory.Category.assoc` then refuses
to rewrite.

*Why the object at which the comparison of restrictions is evaluated is a parameter.* Both
composition identities evaluate the identification
`DifferentialGraded.AlgebraSystem.restrComp` of a two-step restriction of scalars with a one-step
one at an object of a derived category, and that object has two names: the `n`-th object of the
inverse system underlying a strict one, and the `n`-th module of the strict system read in the
derived category. Those two names are definitionally equal, and conversion recognises them at
once both as objects and under a functor, but *not* under
`CategoryTheory.NatTrans.app`: the equation
`(T.toAlgebraSystem.restrComp h h').hom.app (N.toModuleSystem.obj n) = `
`(T.toAlgebraSystem.restrComp h h').hom.app N.derivedObj n` is not recognised within any
reasonable bound, exactly as the implementation notes of
`StacksFrontier/Algebra/DifferentialGraded/Module/InverseSystemStrictModule.lean` record for
`DifferentialGradedModule.derivedTrans_comp`. The object is therefore a parameter of
`DifferentialGraded.StrictModuleSystem.RegularComparison.fwdBwd` and
`DifferentialGraded.StrictModuleSystem.RegularComparison.bwdFwd`, to be supplied at whatever
presentation the consumer already has.

*The presentation of `{}_N(K_n ⊗_R K_t)`.* Tag 0GZ7 produces its comparison map into
`Koszul.powTensorRestrictedModule`, the tensor product `K_n ⊗_R K_t` restricted along the single
homomorphism `K_N → K_n → K_n ⊗_R K_t`, whereas a system of modules asks for the restriction
along `τ_{N,n}` of `Koszul.powBaseTensorRestrictedModule`. Restriction along a composite is the
composite of the restrictions, so the two differ only in that the graded opposite of a composite
is the composite of the graded opposites up to `DifferentialGradedAlgebra.oppHom_comp`; the
identity of `K_n ⊗_R K_t` is therefore a homomorphism between them, which is what
`DifferentialGraded.StrictModuleSystem.RegularComparison.crossRestrHom` is. No transport along an
equality of objects is involved.

## References

* [Stacks Project, Tag 0GZ7](https://stacks.math.columbia.edu/tag/0GZ7)
* [Stacks Project, Tag 0GZI](https://stacks.math.columbia.edu/tag/0GZI)
* [Stacks Project, Tag 0GZJ](https://stacks.math.columbia.edu/tag/0GZJ)
-/

@[expose] public noncomputable section

open CategoryTheory DifferentialGraded DifferentialGraded.Bimodule

universe u

namespace DifferentialGradedModule

/-! ### Reassociation in an abstract category -/

section Reassociation

/-- Reassociation of a three-fold composite, with both halves given: this is
`CategoryTheory.Category.assoc` in the form in which it can be applied by `exact` in a localized
category, where rewriting with associativity is not available. -/
theorem assoc_of_comp_eq {D : Type*} [Category D] {W X Y Z : D} (a : W ⟶ X) (b : X ⟶ Y)
    (c : Y ⟶ Z) {e : X ⟶ Z} {p : W ⟶ Z} (he : b ≫ c = e) (hp : a ≫ e = p) :
    (a ≫ b) ≫ c = p := by
  rw [Category.assoc, he, hp]

/-- Reassociation of a three-fold composite the other way, with both halves given. -/
theorem comp_assoc_of_comp_eq {D : Type*} [Category D] {W X Y Z : D} (a : W ⟶ X) (b : X ⟶ Y)
    (c : Y ⟶ Z) {e : W ⟶ Y} {p : W ⟶ Z} (he : a ≫ b = e) (hp : e ≫ c = p) :
    a ≫ b ≫ c = p := by
  rw [← Category.assoc, he, hp]

/-- A composite whose first two factors compose to the identity is its third factor. -/
theorem comp_comp_of_comp_eq_id {D : Type*} [Category D] {X Y Z : D} (a : X ⟶ Y) (b : Y ⟶ X)
    (c : X ⟶ Z) (h : a ≫ b = CategoryStruct.id X) : a ≫ b ≫ c = c := by
  rw [← Category.assoc, h, Category.id_comp]

/-- The image of a composite under a functor, composed with a third map. -/
theorem map_comp_comp {H D : Type*} [Category H] [Category D] (Q : H ⥤ D) {X Y Z : H}
    (a : X ⟶ Y) (b : Y ⟶ Z) {W : D} (c : Q.obj Z ⟶ W) :
    Q.map (a ≫ b) ≫ c = Q.map a ≫ Q.map b ≫ c := by
  rw [Q.map_comp, Category.assoc]

/-- **Naturality of the inverse of a factorization through localizations**, in the form that
splits a factor off the right of a map built from a composite: the generic shape of the identity
that `DifferentialGradedModule.derivedTrans_restrictScalars` is, stated for abstract
categories. -/
theorem map_comp_app_inv {H₁ H₂ D₁ D₂ : Type*} [Category H₁] [Category H₂] [Category D₁]
    [Category D₂] {Q₁ : H₁ ⥤ D₁} {Q₂ : H₂ ⥤ D₂} {Rst : H₂ ⥤ H₁} {F : D₂ ⥤ D₁}
    (fac : Q₂ ⋙ F ≅ Rst ⋙ Q₁) {X₁ : H₁} {X₂ X₃ : H₂} (a : X₁ ⟶ Rst.obj X₂) (b : X₂ ⟶ X₃) :
    Q₁.map (a ≫ Rst.map b) ≫ fac.inv.app X₃ =
      (Q₁.map a ≫ fac.inv.app X₂) ≫ F.map (Q₂.map b) := by
  simp only [Functor.map_comp, Category.assoc]
  exact congrArg (fun z => Q₁.map a ≫ z) (fac.inv.naturality b)

end Reassociation

/-! ### The canonical functor to the derived category, and two identities for `derivedTrans` -/

variable {R : Type u} [CommRing R]

/-- The canonical functor from differential graded `A`-modules to their derived category. -/
abbrev toDerived (A : DifferentialGradedAlgebra.{u, u} R) :
    DifferentialGradedModule.{u, u, u} A ⥤ derivedCategory' A :=
  toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q

variable {A B : DifferentialGradedAlgebra.{u, u} R}

/-- **A factor on the left splits off a `DifferentialGradedModule.derivedTrans`:** for a
homomorphism `a : M ⟶ M'` of differential graded `A`-modules and a homomorphism
`b : M' ⟶ N|_A`, the map of the composite is the map of `a` in the derived category followed by
the map of `b`. -/
theorem derivedTrans_comp_left (φ : A.Hom B) {M M' : DifferentialGradedModule.{u, u, u} A}
    {P : DifferentialGradedModule.{u, u, u} B} (a : M ⟶ M') (b : M' ⟶ restrictScalars φ P) :
    derivedTrans φ (a ≫ b) = (toDerived A).map a ≫ derivedTrans φ b := by
  simp only [derivedTrans, Functor.map_comp]
  exact Category.assoc _ _ _

/-- **A factor on the right splits off a `DifferentialGradedModule.derivedTrans`:** for a
homomorphism `v : M ⟶ N|_A` and a homomorphism `w : N ⟶ P` of differential graded `B`-modules,
the map of `v` followed by the restriction of `w` is the map of `v` followed by the derived
restriction of the map of `w`. -/
theorem derivedTrans_restrictScalars (φ : A.Hom B) {M : DifferentialGradedModule.{u, u, u} A}
    {N P : DifferentialGradedModule.{u, u, u} B} (v : M ⟶ restrictScalars φ N) (w : N ⟶ P) :
    derivedTrans φ (v ≫ (restrictScalarsFunctor φ).map w) =
      derivedTrans φ v ≫ (derivedRestriction φ).map ((toDerived B).map w) := by
  refine Eq.trans
    (congrArg (fun z => (quasiIsomorphisms' A).Q.map z ≫
        (derivedRestrictionFactorization φ).inv.app ((toHomotopyCategory B).obj P))
      ((toHomotopyCategory A).map_comp v (restrictScalarsHom φ w)))
    (map_comp_app_inv (derivedRestrictionFactorization φ) ((toHomotopyCategory A).map v)
      ((toHomotopyCategory B).map w))

end DifferentialGradedModule

namespace DifferentialGradedAlgebra

variable {R : Type u} [CommRing R]

/-- Composition of homomorphisms of differential graded algebras is associative. -/
theorem comp_assoc {A B C D : DifferentialGradedAlgebra.{u, u} R} (φ : A.Hom B) (ψ : B.Hom C)
    (χ : C.Hom D) : (χ.comp ψ).comp φ = χ.comp (ψ.comp φ) :=
  hom_eq_of_toAlgebraHom_eq rfl

/-- The identity homomorphism is a left unit for composition. -/
theorem idHom_comp {A B : DifferentialGradedAlgebra.{u, u} R} (φ : A.Hom B) :
    (idHom B).comp φ = φ :=
  hom_eq_of_toAlgebraHom_eq (AlgHom.ext fun _ => rfl)

/-- The identity homomorphism is a right unit for composition. -/
theorem comp_idHom {A B : DifferentialGradedAlgebra.{u, u} R} (φ : A.Hom B) :
    φ.comp (idHom A) = φ :=
  hom_eq_of_toAlgebraHom_eq (AlgHom.ext fun _ => rfl)

end DifferentialGradedAlgebra

namespace DifferentialGraded.StrictModuleSystem

open DifferentialGradedAlgebra DifferentialGradedModule

variable {R : Type u} [CommRing R]

/-- **The data comparing two strict inverse systems of regular differential graded modules.**
Over a strict inverse system `(A_n)` of differential graded algebras this records a differential
graded algebra `B` with homomorphisms `ψ_n : A_n → B` compatible with the transitions, a family
of differential graded algebras `C_n` with homomorphisms `θ_n : A_n → C_n` and a strict system of
homomorphisms `γ_{m,n} : C_m → C_n` making the squares commute, and multiplication homomorphisms
`μ_n : C_n → B` compatible with both.

The source's situation is `A_n = K_{t+n}^{opp}`, `B = K_t^{opp}` and
`C_n = (K_{t+n} ⊗_R K_t)^{opp}`, with `θ_n` the inclusion `a ↦ a ⊗ 1`, `γ` the maps
`τ ⊗ id` and `μ_n` the multiplication map `a ⊗ b ↦ τ(a) b`. The two systems of modules it
compares are the system of the regular `B`-module read over `A_n` through `ψ_n` and the system of
the regular `C_n`-modules read through `θ_n`. -/
structure RegularComparison (T : StrictAlgebraSystem R) where
  /-- The fixed algebra `B` whose regular module is the first system. -/
  base : DifferentialGradedAlgebra.{u, u} R
  /-- The homomorphism `ψ_n : A_n → B`. -/
  str : ∀ n : ℕ, (T.alg n).Hom base
  /-- The homomorphisms `ψ_n` are compatible with the transitions of `(A_n)`. -/
  str_trans : ∀ {n m : ℕ} (h : n ≤ m), (str n).comp (T.trans h) = str m
  /-- The algebra `C_n` whose regular module is the `n`-th term of the second system. -/
  big : ℕ → DifferentialGradedAlgebra.{u, u} R
  /-- The homomorphism `θ_n : A_n → C_n`. -/
  incl : ∀ n : ℕ, (T.alg n).Hom (big n)
  /-- The transition homomorphism `γ_{m,n} : C_m → C_n`. -/
  step : ∀ {n m : ℕ}, n ≤ m → (big m).Hom (big n)
  /-- The transition homomorphisms of `(C_n)` compose on the nose. -/
  step_comp : ∀ {n m k : ℕ} (h : n ≤ m) (h' : m ≤ k), (step h).comp (step h') = step (h.trans h')
  /-- The square `γ_{m,n} ∘ θ_m = θ_n ∘ τ_{m,n}` commutes. -/
  step_incl : ∀ {n m : ℕ} (h : n ≤ m), (step h).comp (incl m) = (incl n).comp (T.trans h)
  /-- The multiplication homomorphism `μ_n : C_n → B`. -/
  mul : ∀ n : ℕ, (big n).Hom base
  /-- The multiplication homomorphism restricts to `ψ_n` along `θ_n`. -/
  mul_incl : ∀ n : ℕ, (mul n).comp (incl n) = str n
  /-- The multiplication homomorphisms are compatible with the transitions of `(C_n)`. -/
  mul_step : ∀ {n m : ℕ} (h : n ≤ m), (mul n).comp (step h) = mul m

namespace RegularComparison

variable {T : StrictAlgebraSystem R} (D : RegularComparison T)

/-- **The first system:** the regular `B`-module, read over `A_n` through `ψ_n`, with the
identity of `B` as its transition homomorphisms. -/
def restrSystem : StrictModuleSystem T :=
  ofRestrictedRegularId T D.base D.str D.str_trans

/-- **The second system:** the regular `C_n`-modules, read over `A_n` through `θ_n`, with the
`γ_{m,n}` as their transition homomorphisms. -/
def tensorSystem : StrictModuleSystem T :=
  ofRestrictedRegular T D.big D.incl D.step D.step_comp fun h a =>
    congrArg (fun φ => φ.toAlgebraHom a) (D.step_incl h)

/-- **The multiplication homomorphism `μ_n`** as a homomorphism of differential graded
`A_n`-modules from the `n`-th term of the second system to the `n`-th term of the first. -/
def mulHom (n : ℕ) :
    restrictScalars (D.incl n) (regularModule (D.big n)) ⟶
      restrictScalars (D.str n) (regularModule D.base) :=
  restrictedRegularHom' (D.incl n) (D.str n) (D.mul n) fun a =>
    congrArg (fun φ : (T.alg n).Hom D.base => φ.toAlgebraHom a) (D.mul_incl n)

/-- **The multiplication homomorphism `μ_m`** as a `τ_{m,n}`-semilinear homomorphism from the
`m`-th term of the second system to the `n`-th term of the first. -/
def mulTrans {n m : ℕ} (h : n ≤ m) :
    restrictScalars (D.incl m) (regularModule (D.big m)) ⟶
      restrictScalars (T.trans h) (restrictScalars (D.str n) (regularModule D.base)) :=
  restrictedRegularHomRestrict (D.incl m) (T.trans h) (D.str n) (D.mul m) fun a =>
    congrArg (fun φ : (T.alg m).Hom D.base => φ.toAlgebraHom a)
      ((D.mul_incl m).trans (D.str_trans h).symm)

/-- **The semilinear multiplication homomorphism factors** through the transition homomorphism of
the second system followed by the multiplication homomorphism at the smaller index. -/
theorem mulTrans_eq {n m : ℕ} (h : n ≤ m) :
    D.mulTrans h =
      D.tensorSystem.trans h ≫ (restrictScalarsFunctor (T.trans h)).map (D.mulHom n) :=
  DifferentialGradedModule.Hom.ext (LinearMap.ext fun x =>
    (congrArg (fun φ : (D.big m).Hom D.base => φ.toAlgebraHom x) (D.mul_step h)).symm)

/-- The map in the derived category of the semilinear multiplication homomorphism, split along
`DifferentialGraded.StrictModuleSystem.RegularComparison.mulTrans_eq`. -/
theorem derivedTrans_mulTrans {n m : ℕ} (h : n ≤ m) :
    derivedTrans (T.trans h) (D.mulTrans h) =
      derivedTrans (T.trans h) (D.tensorSystem.trans h) ≫
        (derivedRestriction (T.trans h)).map ((toDerived (T.alg n)).map (D.mulHom n)) := by
  rw [D.mulTrans_eq h]
  exact derivedTrans_restrictScalars _ _ _

section Cross

/-- The multiplication homomorphism `μ_n` composed with a presentation of `C_n` as an algebra
over `A_m` is `ψ_m`. -/
theorem mul_comp_cross {n m : ℕ} (h : n ≤ m) (c : (T.alg m).Hom (D.big n))
    (hc : (D.incl n).comp (T.trans h) = c) : (D.mul n).comp c = D.str m := by
  rw [← hc, ← comp_assoc, D.mul_incl, D.str_trans]

/-- **The multiplication homomorphism `μ_n`**, read as a homomorphism of differential graded
`A_m`-modules out of `C_n` presented over `A_m` through `c`. In the source this is the map `μ_n`
of `Koszul.powMulHom`, the one with which the comparison map of Tag 0GZ7 composes to the
identity. -/
def crossMulHom {n m : ℕ} (h : n ≤ m) (c : (T.alg m).Hom (D.big n))
    (hc : (D.incl n).comp (T.trans h) = c) :
    restrictScalars c (regularModule (D.big n)) ⟶
      restrictScalars (D.str m) (regularModule D.base) :=
  restrictedRegularHom' c (D.str m) (D.mul n) fun a =>
    congrArg (fun φ : (T.alg m).Hom D.base => φ.toAlgebraHom a) (D.mul_comp_cross h c hc)

/-- **The transition homomorphism `γ_{m,n}`**, read as a homomorphism of differential graded
`A_m`-modules into `C_n` presented over `A_m` through `c`. In the source this is the map
`τ_{N,n} ⊗ id` of `Koszul.powTransitionTensorHom`, the one that the comparison map of Tag 0GZ7
composes with the multiplication map to give. -/
def crossStepHom {n m : ℕ} (h : n ≤ m) (c : (T.alg m).Hom (D.big n))
    (hc : (D.incl n).comp (T.trans h) = c) :
    restrictScalars (D.incl m) (regularModule (D.big m)) ⟶
      restrictScalars c (regularModule (D.big n)) :=
  restrictedRegularHom' (D.incl m) c (D.step h) fun a =>
    congrArg (fun φ : (T.alg m).Hom (D.big n) => φ.toAlgebraHom a) ((D.step_incl h).trans hc)

/-- **The comparison of the two presentations of `C_n` over `A_m`:** the identity of `C_n`, read
as a homomorphism of differential graded `A_m`-modules from `C_n` presented through `c` to the
restriction along `τ_{m,n}` of `C_n` presented over `A_n` through `θ_n`. -/
def crossRestrHom {n m : ℕ} (h : n ≤ m) (c : (T.alg m).Hom (D.big n))
    (hc : (D.incl n).comp (T.trans h) = c) :
    restrictScalars c (regularModule (D.big n)) ⟶
      restrictScalars (T.trans h) (restrictScalars (D.incl n) (regularModule (D.big n))) :=
  restrictedRegularIdHom c (T.trans h) (D.incl n) hc

end Cross

section Composites

variable {n m k l : ℕ}

/-- **The multiplication homomorphism `μ_m`** as a `τ_{k,n}`-semilinear homomorphism out of `C_m`
presented over `A_k` through `c`: the shape in which it is the composite of the two halves of the
first composition identity. -/
def crossMulTrans (hv : n ≤ m) (hu : m ≤ k) (c : (T.alg k).Hom (D.big m))
    (hc : (D.incl m).comp (T.trans hu) = c) :
    restrictScalars c (regularModule (D.big m)) ⟶
      restrictScalars (T.trans (hv.trans hu))
        (restrictScalars (D.str n) (regularModule D.base)) :=
  restrictedRegularHomRestrict c (T.trans (hv.trans hu)) (D.str n) (D.mul m) fun a =>
    congrArg (fun φ : (T.alg k).Hom D.base => φ.toAlgebraHom a)
      ((D.mul_comp_cross hu c hc).trans (D.str_trans (hv.trans hu)).symm)

/-- The semilinear multiplication homomorphism out of the other presentation factors as the
multiplication homomorphism followed by the transition homomorphism of the first system. -/
theorem crossMulTrans_eq (hv : n ≤ m) (hu : m ≤ k) (c : (T.alg k).Hom (D.big m))
    (hc : (D.incl m).comp (T.trans hu) = c) :
    D.crossMulTrans hv hu c hc =
      D.crossMulHom hu c hc ≫ D.restrSystem.trans (hv.trans hu) :=
  DifferentialGradedModule.Hom.ext
    (toLinearMap_comp (D.mul m) (idHom D.base) (D.mul m) (idHom_comp (D.mul m))).symm

/-- **The first composition identity, in the derived category:** the comparison of the two
presentations, followed by the derived restriction of the semilinear multiplication
homomorphism. -/
theorem derivedTrans_crossRestr_comp (hv : n ≤ m) (hu : m ≤ k) (c : (T.alg k).Hom (D.big m))
    (hc : (D.incl m).comp (T.trans hu) = c) :
    derivedTrans (T.trans hu) (D.crossRestrHom hu c hc) ≫
        (derivedRestriction (T.trans hu)).map (derivedTrans (T.trans hv) (D.mulTrans hv)) ≫
          (T.toAlgebraSystem.restrComp hv hu).hom.app (D.restrSystem.derivedObj n) =
      derivedTrans (T.trans (hv.trans hu)) (D.crossMulTrans hv hu c hc) :=
  derivedTrans_comp (T.trans hu) (T.trans hv) (T.trans (hv.trans hu)) (T.trans_comp hv hu)
    (D.crossRestrHom hu c hc) (D.mulTrans hv) (D.crossMulTrans hv hu c hc)
    (restrict_trans_comp _ _ _ (T.trans_comp hv hu) _ _ _
      (toLinearMap_comp _ _ _ (comp_idHom (D.mul m)))) (D.restrSystem.derivedObj n) rfl
    (T.toAlgebraSystem_restrComp_hom_app hv hu) _ rfl _ HEq.rfl _ HEq.rfl

/-- **The transition homomorphism `γ_{k,m}` followed by the comparison of the two presentations
of `C_m` is the transition homomorphism of the second system.** Both have underlying map
`γ_{k,m}`. -/
theorem crossStep_comp_crossRestr (hu : m ≤ k) (c : (T.alg k).Hom (D.big m))
    (hc : (D.incl m).comp (T.trans hu) = c) :
    D.crossStepHom hu c hc ≫ D.crossRestrHom hu c hc = D.tensorSystem.trans hu :=
  DifferentialGradedModule.Hom.ext
    (toLinearMap_comp (D.step hu) (idHom (D.big m)) (D.step hu) (idHom_comp (D.step hu)))

/-- **The second composition identity, in the derived category:** the transition map of the
second system, followed by the derived restriction of the transition homomorphism `γ` composed
with the comparison of presentations, is the transition map of the second system over the two
steps. -/
theorem derivedTrans_crossStep_comp (hu : m ≤ k) (hg : k ≤ l) (c : (T.alg k).Hom (D.big m))
    (hc : (D.incl m).comp (T.trans hu) = c) :
    derivedTrans (T.trans hg) (D.tensorSystem.trans hg) ≫
        (derivedRestriction (T.trans hg)).map (derivedTrans (T.trans hu)
          (D.crossStepHom hu c hc ≫ D.crossRestrHom hu c hc)) ≫
          (T.toAlgebraSystem.restrComp hu hg).hom.app (D.tensorSystem.derivedObj m) =
      D.tensorSystem.derivedMap (hu.trans hg) :=
  (congrArg (fun z => derivedTrans (T.trans hg) (D.tensorSystem.trans hg) ≫
      (derivedRestriction (T.trans hg)).map (derivedTrans (T.trans hu) z) ≫
        (T.toAlgebraSystem.restrComp hu hg).hom.app (D.tensorSystem.derivedObj m))
    (D.crossStep_comp_crossRestr hu c hc)).trans
    (D.tensorSystem.derivedMap_derivedMap hu hg).symm

/-- **The first composition identity of a pro-isomorphism in the derived category**, for a single
stage: a map `a` out of the first system whose composite with the multiplication homomorphism is
the identity, followed by the comparison of presentations and then by the derived restriction of
the semilinear multiplication homomorphism, is the transition map of the first system. -/
theorem fwdBwd {n m k : ℕ} (hv : n ≤ m) (hu : m ≤ k) (c : (T.alg k).Hom (D.big m))
    (hc : (D.incl m).comp (T.trans hu) = c)
    (a : (toDerived (T.alg k)).obj (restrictScalars (D.str k) (regularModule D.base)) ⟶
      (toDerived (T.alg k)).obj (restrictScalars c (regularModule (D.big m))))
    (ha : a ≫ (toDerived (T.alg k)).map (D.crossMulHom hu c hc) =
      CategoryStruct.id ((toDerived (T.alg k)).obj
        (restrictScalars (D.str k) (regularModule D.base))))
    (Z : derivedCategory' (T.alg n)) (hZ : D.restrSystem.derivedObj n = Z)
    (q : D.tensorSystem.derivedObj m ⟶ (T.toAlgebraSystem.restr hv).obj Z)
    (hq : HEq (derivedTrans (T.trans hv) (D.mulTrans hv)) q)
    (r : (toDerived (T.alg k)).obj (restrictScalars (D.str k) (regularModule D.base)) ⟶
      (T.toAlgebraSystem.restr (hv.trans hu)).obj Z)
    (hr : HEq (D.restrSystem.derivedMap (hv.trans hu)) r) :
    (a ≫ derivedTrans (T.trans hu) (D.crossRestrHom hu c hc)) ≫
        (T.toAlgebraSystem.restr hu).map q ≫
          (T.toAlgebraSystem.restrComp hv hu).hom.app Z = r := by
  subst hZ
  obtain rfl : derivedTrans (T.trans hv) (D.mulTrans hv) = q := eq_of_heq hq
  obtain rfl : D.restrSystem.derivedMap (hv.trans hu) = r := eq_of_heq hr
  exact assoc_of_comp_eq a _ _ (D.derivedTrans_crossRestr_comp hv hu c hc)
    (((congrArg (fun z => a ≫ derivedTrans (T.trans (hv.trans hu)) z)
          (D.crossMulTrans_eq hv hu c hc)).trans
        (congrArg (fun z => a ≫ z)
          (derivedTrans_comp_left (T.trans (hv.trans hu)) (D.crossMulHom hu c hc)
            (D.restrSystem.trans (hv.trans hu))))).trans
      (comp_comp_of_comp_eq_id _ _ _ ha))

/-- **The second composition identity of a pro-isomorphism in the derived category**, for a single
stage: the semilinear multiplication homomorphism, followed by the derived restriction of a map
`a` which the multiplication homomorphism composes with to give the transition homomorphism `γ`,
is the transition map of the second system. -/
theorem bwdFwd {m k l : ℕ} (hu : m ≤ k) (hg : k ≤ l) (c : (T.alg k).Hom (D.big m))
    (hc : (D.incl m).comp (T.trans hu) = c)
    (a : (toDerived (T.alg k)).obj (restrictScalars (D.str k) (regularModule D.base)) ⟶
      (toDerived (T.alg k)).obj (restrictScalars c (regularModule (D.big m))))
    (ha : (toDerived (T.alg k)).map (D.mulHom k) ≫ a =
      (toDerived (T.alg k)).map (D.crossStepHom hu c hc))
    (Z : derivedCategory' (T.alg m)) (hZ : D.tensorSystem.derivedObj m = Z)
    (p : (toDerived (T.alg k)).obj (restrictScalars (D.str k) (regularModule D.base)) ⟶
      (T.toAlgebraSystem.restr hu).obj Z)
    (hp : HEq (a ≫ derivedTrans (T.trans hu) (D.crossRestrHom hu c hc)) p)
    (r : D.tensorSystem.derivedObj l ⟶ (T.toAlgebraSystem.restr (hu.trans hg)).obj Z)
    (hr : HEq (D.tensorSystem.derivedMap (hu.trans hg)) r) :
    derivedTrans (T.trans hg) (D.mulTrans hg) ≫
        (T.toAlgebraSystem.restr hg).map p ≫
          (T.toAlgebraSystem.restrComp hu hg).hom.app Z = r := by
  subst hZ
  obtain rfl : a ≫ derivedTrans (T.trans hu) (D.crossRestrHom hu c hc) = p := eq_of_heq hp
  obtain rfl : D.tensorSystem.derivedMap (hu.trans hg) = r := eq_of_heq hr
  refine Eq.trans
    (congrArg (fun z => z ≫
        (derivedRestriction (T.trans hg)).map
            (a ≫ derivedTrans (T.trans hu) (D.crossRestrHom hu c hc)) ≫
          (T.toAlgebraSystem.restrComp hu hg).hom.app (D.tensorSystem.derivedObj m))
      (D.derivedTrans_mulTrans hg)) ?_
  exact assoc_of_comp_eq _ _ _
    (comp_assoc_of_comp_eq _ _ _ ((derivedRestriction (T.trans hg)).map_comp _ _).symm
      (congrArg (fun z => (derivedRestriction (T.trans hg)).map z ≫
          (T.toAlgebraSystem.restrComp hu hg).hom.app (D.tensorSystem.derivedObj m))
        (comp_assoc_of_comp_eq _ _ _ ha (derivedTrans_comp_left _ _ _).symm)))
    (D.derivedTrans_crossStep_comp hu hg c hc)

end Composites

end RegularComparison

end DifferentialGraded.StrictModuleSystem

namespace Koszul

open DifferentialGradedAlgebra DifferentialGradedModule
open scoped TensorProduct

variable {R : Type u} [CommRing R] {r : ℕ}

/-! ### The multiplication maps are compatible with the transition homomorphisms -/

/-- **The multiplication maps are compatible with the transition homomorphisms:** for
`1 ≤ t ≤ n ≤ N` the composite of `τ_{N,n} ⊗ id` and `μ_n` is `μ_N`. Both send `a ⊗ b` to
`τ_{N,t}(a) b`. -/
theorem powMul_comp_tensorHomLeft (f : Fin r → R) {t n N : ℕ} (ht : 1 ≤ t) (htn : t ≤ n)
    (hnN : n ≤ N) :
    (powMul f ht htn).comp
        (tensorHomLeft (powTransition f (ht.trans htn) hnN) (powAlgebra f t)) =
      powMul f ht (htn.trans hnN) := by
  refine hom_eq_of_toAlgebraHom_eq
    (tensorHom_ext (AlgHom.ext fun a => ?_) (AlgHom.ext fun c => ?_))
  · change (powMul f ht htn).toAlgebraHom
      ((tensorHomLeft (powTransition f (ht.trans htn) hnN) (powAlgebra f t)).toAlgebraHom
        (a ᵍ⊗ₜ[R] (1 : (powAlgebra f t).A) :
          (powAlgebra f N).grading ᵍ⊗[R] (powAlgebra f t).grading)) =
      (powMul f ht (htn.trans hnN)).toAlgebraHom
        (a ᵍ⊗ₜ[R] (1 : (powAlgebra f t).A) :
          (powAlgebra f N).grading ᵍ⊗[R] (powAlgebra f t).grading)
    rw [tensorHomLeft_tmul, powMul_tmul, powMul_tmul]
    exact congrArg (fun z => z * (1 : (powAlgebra f t).A))
      (powTransition_comp_apply f ht htn hnN a)
  · change (powMul f ht htn).toAlgebraHom
      ((tensorHomLeft (powTransition f (ht.trans htn) hnN) (powAlgebra f t)).toAlgebraHom
        ((1 : (powAlgebra f N).A) ᵍ⊗ₜ[R] c :
          (powAlgebra f N).grading ᵍ⊗[R] (powAlgebra f t).grading)) =
      (powMul f ht (htn.trans hnN)).toAlgebraHom
        ((1 : (powAlgebra f N).A) ᵍ⊗ₜ[R] c :
          (powAlgebra f N).grading ᵍ⊗[R] (powAlgebra f t).grading)
    rw [tensorHomLeft_tmul, powMul_tmul, powMul_tmul, map_one, map_one, map_one]

/-! ### The Koszul comparison data -/

variable (f : Fin r → R) {t : ℕ} (ht : 1 ≤ t)

/-- **The Koszul instance of the comparison data of two systems of regular modules:** the fixed
algebra is `K_t`, the `n`-th algebra of the second system is `K_{t+n} ⊗_R K_t`, the inclusions
are `a ↦ a ⊗ 1`, the transitions are the maps `τ ⊗ id` and the multiplication maps are the maps
`a ⊗ b ↦ τ(a) b`, all read on the graded opposite algebras. The two systems of modules it
compares are `Koszul.powRestrictedModuleSystem` and `Koszul.powBaseTensorModuleSystem`. -/
def powRegularComparison :
    StrictModuleSystem.RegularComparison (powStrictAlgebraSystem f ht) where
  base := oppAlgebra (powAlgebra f t)
  str n := oppPowTransition f ht (Nat.le_add_right t n)
  str_trans h := oppPowTransition_comp f ht (Nat.le_add_right t _) (Nat.add_le_add_left h t)
  big n := oppAlgebra (tensorProduct (powAlgebra f (t + n)) (powAlgebra f t))
  incl n := oppHom (tensorInclLeft (powAlgebra f (t + n)) (powAlgebra f t))
  step h := oppHom (tensorHomLeft
    (powTransition f (ht.trans (Nat.le_add_right t _)) (Nat.add_le_add_left h t))
    (powAlgebra f t))
  step_comp h h' := oppHom_tensorHomLeft_comp_oppHom_tensorHomLeft f t
    (ht.trans (Nat.le_add_right t _)) (Nat.add_le_add_left h t) (Nat.add_le_add_left h' t)
  step_incl h := oppHom_tensorHomLeft_comp_oppHom_tensorInclLeft f t
    (ht.trans (Nat.le_add_right t _)) (Nat.add_le_add_left h t)
  mul n := oppHom (powMul f ht (Nat.le_add_right t n))
  mul_incl n := (oppHom_comp (tensorInclLeft (powAlgebra f (t + n)) (powAlgebra f t))
      (powMul f ht (Nat.le_add_right t n))).trans
    (congrArg oppHom (hom_eq_of_toAlgebraHom_eq
      (powMul_comp_includeLeft f ht (Nat.le_add_right t n))))
  mul_step h := (oppHom_comp _ (powMul f ht (Nat.le_add_right t _))).trans
    (congrArg oppHom (powMul_comp_tensorHomLeft f ht (Nat.le_add_right t _)
      (Nat.add_le_add_left h t)))

/-! ### The comparison arrows of Tag 0GZ7 at the chosen indices -/

/-- The indices of the pro-isomorphism, measured from the base `t` of the system: the multiples
of `t`. The `j`-th index of the system is `t * j`, so the Koszul algebra there is
`K_{t + t * j}`. -/
theorem powIdx_strictMono {t : ℕ} (ht : 1 ≤ t) : StrictMono fun j : ℕ => t * j :=
  strictMono_nat_of_lt_succ fun j => by
    have h : t * (j + 1) = t * j + t := by ring
    omega

/-- Two consecutive chosen indices are in increasing order. -/
theorem powIdx_le (t i : ℕ) : t * (2 * i + 1) ≤ t * (2 * i + 2) := by
  have h : t * (2 * i + 2) = t * (2 * i + 1) + t := by ring
  omega

/-- The bound that Tag 0GZ7 asks for holds between two consecutive chosen indices. -/
theorem powIdx_add_le (t i : ℕ) :
    t + t * (2 * i + 1) + t ≤ t + t * (2 * i + 2) := by
  have h : t * (2 * i + 2) = t * (2 * i + 1) + t := by ring
  omega

/-- **The comparison data of Tag 0GZ7** at the indices `t + t * (2i + 1) ≤ t + t * (2i + 2)`,
whose difference is at least `t`, which is what `Koszul.nonempty_koszulArrowData` asks for. -/
def powArrowData (i : ℕ) :
    KoszulArrowData f (t + t * (2 * i + 1)) t (t + t * (2 * i + 2)) ht
      (Nat.le_add_right t _)
      (Nat.add_le_add_left (powIdx_le t i) t) :=
  (nonempty_koszulArrowData ht (Nat.le_add_right t _)
    (Nat.add_le_add_left (powIdx_le t i) t)
    (powIdx_add_le t i) r f).some

/-- **The comparison map of Tag 0GZ7** from `{}K_t` to `{}(K_{t + t(2i+1)} ⊗_R K_t)` in the
derived category of left differential graded `K_{t + t(2i+2)}`-modules. -/
def powComparisonArrow (i : ℕ) :
    (powDerived f (t + t * (2 * i + 2))).obj
        (powRestrictedModule f ht (Nat.le_add_right t (t * (2 * i + 2)))) ⟶
      (powDerived f (t + t * (2 * i + 2))).obj
        (powTensorRestrictedModule f t (ht.trans (Nat.le_add_right t (t * (2 * i + 1))))
          (Nat.add_le_add_left (powIdx_le t i) t)) :=
  derivedComparisonArrow (powArrowData f ht i)

/-- **The first composite of Tag 0GZ7 at the chosen indices:** postcomposing the comparison map
with the multiplication map `μ_{t+t(2i+1)}` gives the identity. -/
theorem powComparisonArrow_comp_powMulHom (i : ℕ) :
    powComparisonArrow f ht i ≫ (powDerived f (t + t * (2 * i + 2))).map
        (powMulHom f ht (Nat.le_add_right t (t * (2 * i + 1)))
          (Nat.add_le_add_left (powIdx_le t i) t)) =
      CategoryStruct.id ((powDerived f (t + t * (2 * i + 2))).obj
        (powRestrictedModule f ht (Nat.le_add_right t (t * (2 * i + 2))))) :=
  derivedComparisonArrow_comp_powMulHom (powArrowData f ht i)

/-- **The second composite of Tag 0GZ7 at the chosen indices:** precomposing the comparison map
with the multiplication map `μ_{t+t(2i+2)}` gives `τ ⊗ id`. -/
theorem powMulBaseHom_comp_powComparisonArrow (i : ℕ) :
    (powDerived f (t + t * (2 * i + 2))).map
          (powMulBaseHom f ht (Nat.le_add_right t (t * (2 * i + 2)))) ≫
        powComparisonArrow f ht i =
      (powDerived f (t + t * (2 * i + 2))).map
        (powTransitionTensorHom f t (ht.trans (Nat.le_add_right t (t * (2 * i + 1))))
          (Nat.add_le_add_left (powIdx_le t i) t)) :=
  powMulBaseHom_comp_derivedComparisonArrow (powArrowData f ht i)

end Koszul

end
