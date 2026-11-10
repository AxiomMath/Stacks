module

public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.DifferentialGraded.Endomorphism.BimoduleTensorEquivalence
public import StacksFrontier.Algebra.DifferentialGraded.Module.ConcentratedDerivedHom
public import StacksFrontier.Algebra.DifferentialGraded.Module.ExtLinear
public import StacksFrontier.Algebra.DifferentialGraded.Module.InternalHomBimodule
public import StacksFrontier.Algebra.DifferentialGraded.Module.RegularModuleRepresents
public import StacksFrontier.CategoryTheory.Linear.EndomorphismAlgEquiv

/-! # Hochschild cohomology of a differential graded algebra

Let `(A, d)` be a differential graded algebra over a commutative ring `R`. Its Hochschild
cohomology is the shifted derived self-`Hom` of the diagonal bimodule,
`HH^i(A, d) = Hom_{D(A^{opp} ⊗_R A, d)}(A, A[i])`. The diagonal bimodule is the regular
bimodule `DifferentialGraded.Bimodule.regularBimodule`, and Tag 0FQJ turns a differential
graded `(A, A)`-bimodule into a right differential graded module over the enveloping algebra
`A^{opp} ⊗_R A`, so the `Hom` is taken in the derived category `D(A^{opp} ⊗_R A, d)` of that
algebra.

## Main definitions

* `DifferentialGraded.Bimodule.envelopingAlgebra`: the enveloping differential graded algebra
  `A^{opp} ⊗_R A`.
* `DifferentialGraded.Bimodule.toEnvelopingDerived`: differential graded `(A, A)`-bimodules read
  in `D(A^{opp} ⊗_R A, d)`, through Tag 0FQJ.
* `DifferentialGraded.Bimodule.diagonalDerived`: the diagonal bimodule as an object of
  `D(A^{opp} ⊗_R A, d)`.
* `DifferentialGraded.Bimodule.hochschildCohomology`: `HH^i(A, d)`.

## Main results

* `DifferentialGraded.Bimodule.hochschildCohomology_addEquiv_of_diagonalEquivalence`: an
  additive equivalence of the two bimodule derived categories which commutes with the shift and
  carries the diagonal bimodule of `A` to the diagonal bimodule of `B` induces isomorphisms
  `HH^i(A, d) ≅ HH^i(B, d)` for every `i`. This is the conclusion the source draws from its
  suppositions on the functor `M ↦ Ω' ⊗^𝐋_A M ⊗^𝐋_A Ω`; those suppositions are the hypotheses
  here.
* `DifferentialGraded.Bimodule.centerAlgEquivDiagonalEnd`: for `A` concentrated in degree zero
  the endomorphism algebra of the diagonal bimodule is the centre of `A`, as `R`-algebras.
* `DifferentialGraded.Bimodule.centerAlgEquivDiagonalDerivedEnd` and
  `DifferentialGraded.Bimodule.centerAddEquivHochschildCohomologyZero`: **the source's equality
  `HH^0(A, d) = Z(A)` for `A = H^0(A)`**, as an isomorphism of `R`-algebras from the centre of
  `A` onto the endomorphism algebra of the diagonal bimodule in the derived category, and as an
  isomorphism onto the degree-zero Hochschild cohomology group itself. Left multiplication by a
  central element is the map in both.
* `DifferentialGraded.Bimodule.envelopingAlgebra_grading_eq_bot`: the enveloping algebra of an
  algebra concentrated in degree zero is concentrated in degree zero.
* `DifferentialGraded.Bimodule.diagonalDerivedEndAlgEquiv`: the degree-zero invariance as an
  isomorphism of `R`-**algebras** rather than of additive groups, for an additive, `R`-linear
  equivalence of the bimodule derived categories carrying diagonal to diagonal. Compatibility
  with the translation is not needed in degree zero.
* `DifferentialGraded.Bimodule.centerAlgEquivOfDiagonalEquivalence`: composing that with the two
  identifications `HH^0 = Z` gives `Z(A) ≃ₐ[R] Z(B)` for `A` and `B` concentrated in degree
  zero. This is the whole of Rickard's chain *except* the construction of the equivalence of
  bimodule derived categories, which nothing in this library produces from a derived equivalence
  `D(A) ≌ D(B)` — so it is **not** a proof of [Stacks, Tag 09SD] and carries no such tag. It
  reduces that tag, along the route its own remark proposes, to exactly that one functor.

## Implementation notes

The derived category used is `DifferentialGradedModule.derivedCategory'`, the localization of
the homotopy category at the quasi-isomorphisms, which is the one carrying the derived tensor
and derived `Hom` functors of this tree; the bimodule side enters only through Tag 0FQJ. The
source takes `Hom(A, A[i])` with the shift of the derived category, so `HH^i` is defined by
`shiftFunctor _ i`, and the degree-zero case is compared with `End` through `shiftFunctorZero`.

*The source gives no precise statement.* It writes "If we ever need this remark we will provide
a precise statement with a detailed proof here", and introduces the invariance by "it may happen
that". Accordingly the invariance result below takes the source's suppositions as hypotheses. It
is stated for an arbitrary equivalence of the bimodule derived categories which commutes with
the shift and matches the diagonals, which is all the source's argument uses about
`M ↦ Ω' ⊗^𝐋_A M ⊗^𝐋_A Ω`; the construction of that functor out of a pair of bimodules inducing
quasi-inverse derived tensor functors is not carried out here, and the source does not claim it
is automatic — it says the functor is an equivalence sending `A` to `B` only "as can happen
under suitable flatness conditions".

*Degree zero.* For the degree-zero identification the source supposes `A = H^0(A)`, taken here
as `A` being concentrated in degree zero. At the level of bimodules the endomorphism algebra of
the diagonal is then exactly the centre, which is `centerAlgEquivDiagonalEnd`. The passage from
bimodules to the derived category is injective by the degree-zero cohomology functor of
Tag 09KW, and surjective because the enveloping algebra and the diagonal over it are
concentrated in degree zero as well: for an algebra concentrated in degree zero the passage to
the derived category is bijective on the homomorphisms between modules concentrated in degree
zero, which is `DifferentialGradedModule.concentrated_q_map_surjective`, proved there by
resolving the module by free modules placed in the degrees `≤ 0`. No identification of
`D(C, d)` with the derived category of modules over the ring `C.A` is needed — the library has
that only for `C = DifferentialGradedAlgebra.degreeZero R A` with `A` *commutative*
(`DifferentialGradedModule.degreeZeroDerivedEquivalence`), which the enveloping algebra of a
noncommutative `A` is not.

## References

* [Stacks Project, Tag 09ST](https://stacks.math.columbia.edu/tag/09ST)
* [Stacks Project, Tag 0FQJ](https://stacks.math.columbia.edu/tag/0FQJ)
* [Stacks Project, Tag 09KX](https://stacks.math.columbia.edu/tag/09KX)
* [Stacks Project, Tag 09KY](https://stacks.math.columbia.edu/tag/09KY)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace DifferentialGraded.Bimodule

open DifferentialGradedModule

variable {R : Type u} [CommRing R]

/-- An `R`-linear additive functor induces an `R`-algebra homomorphism on endomorphism
algebras. -/
def endAlgHomOfLinearFunctor {C D : Type*} [Category C] [Category D]
    [Preadditive C] [Preadditive D] [Linear R C] [Linear R D] (F : C ⥤ D) [F.Linear R]
    [F.Additive] (X : C) : End X →ₐ[R] End (F.obj X) where
  toFun f := .of (F.map f.asHom)
  map_zero' := by ext; exact F.map_zero X X
  map_one' := by ext; exact F.map_id X
  map_add' f g := by ext; exact F.map_add
  map_mul' f g := by ext; exact F.map_comp g.asHom f.asHom
  commutes' r := by
    ext
    change F.map (r • 𝟙 X) = r • 𝟙 (F.obj X)
    rw [F.map_smul, F.map_id]

/-! ### The enveloping algebra and the diagonal bimodule in the derived category -/

/-- The enveloping differential graded algebra `A^{opp} ⊗_R A` of a differential graded algebra
`A`: the algebra whose right differential graded modules are the differential graded
`(A, A)`-bimodules, by Tag 0FQJ. -/
@[sga "5 IIIB 5.1" "partial"]
abbrev envelopingAlgebra (A : DifferentialGradedAlgebra.{u, u} R) :
    DifferentialGradedAlgebra.{u, u} R :=
  tensorAlgebra A A

/-- A differential graded `(A, A)`-bimodule, read in the derived category of the enveloping
algebra: the Tag 0FQJ equivalence followed by the passage to the derived category. -/
def toEnvelopingDerived (A : DifferentialGradedAlgebra.{u, u} R) :
    Bimodule A A ⥤ derivedCategory' (envelopingAlgebra A) :=
  (tensorEquivalence A A).equivalence.functor ⋙
    toHomotopyCategory (envelopingAlgebra A) ⋙ (quasiIsomorphisms' (envelopingAlgebra A)).Q

/-- The diagonal bimodule `A`, as an object of the derived category of bimodules
`D(A^{opp} ⊗_R A, d)`. -/
abbrev diagonalDerived (A : DifferentialGradedAlgebra.{u, u} R) :
    derivedCategory' (envelopingAlgebra A) :=
  (toEnvelopingDerived A).obj (regularBimodule A)

/-- **Hochschild cohomology.** The degree-`i` Hochschild cohomology of a differential graded
algebra `(A, d)` over `R` is
`HH^i(A, d) = Hom_{D(A^{opp} ⊗_R A, d)}(A, A[i])`, the group of morphisms from the diagonal
bimodule to its `i`-fold shift in the derived category of differential graded
`(A, A)`-bimodules. -/
abbrev hochschildCohomology (A : DifferentialGradedAlgebra.{u, u} R) (i : ℤ) :=
  diagonalDerived A ⟶
    (shiftFunctor (derivedCategory' (envelopingAlgebra A)) i).obj (diagonalDerived A)

/-- Degree-zero Hochschild cohomology is the endomorphism group of the diagonal bimodule in the
derived category of bimodules, by the identification of the zeroth shift with the identity. -/
def endAddEquivHochschildCohomologyZero (A : DifferentialGradedAlgebra.{u, u} R) :
    End (diagonalDerived A) ≃+ hochschildCohomology A 0 := by
  refine AddEquiv.ofBijective
    (AddMonoidHom.mk'
      (fun f : End (diagonalDerived A) =>
        (f.asHom ≫ (shiftFunctorZero (derivedCategory' (envelopingAlgebra A)) ℤ).inv.app
          (diagonalDerived A) : hochschildCohomology A 0))
      (fun f g => Preadditive.add_comp _ _ _ f.asHom g.asHom _)) ⟨?_, ?_⟩
  · intro f g h
    exact End.ext ((Iso.cancel_iso_inv_right f.asHom g.asHom
      ((shiftFunctorZero (derivedCategory' (envelopingAlgebra A)) ℤ).app
        (diagonalDerived A))).mp h)
  · intro g
    refine ⟨.of (g ≫ (shiftFunctorZero (derivedCategory' (envelopingAlgebra A)) ℤ).hom.app
      (diagonalDerived A)), ?_⟩
    change (g ≫ _) ≫ _ = g
    rw [Category.assoc, Iso.hom_inv_id_app, Category.comp_id]

/-! ### Invariance under an equivalence matching the diagonals -/

/-- **Invariance of Hochschild cohomology.** An additive equivalence between the derived
categories of bimodules which commutes with the shift and carries the diagonal bimodule of `A`
to the diagonal bimodule of `B` induces an isomorphism `HH^i(A, d) ≅ HH^i(B, d)` for every `i`,
given by conjugating a morphism `A → A[i]` by the functor and the comparison isomorphisms.

This is the conclusion the source draws, for the functor `M ↦ Ω' ⊗^𝐋_A M ⊗^𝐋_A Ω` on bimodule
derived categories, from its suppositions that this functor is an equivalence and sends the
`(A, A)`-bimodule `A` to the `(B, B)`-bimodule `B`. Only those properties of the functor enter
the argument, so they are the hypotheses here. -/
theorem hochschildCohomology_addEquiv_of_diagonalEquivalence
    (A B : DifferentialGradedAlgebra.{u, u} R)
    (F : derivedCategory' (envelopingAlgebra A) ⥤ derivedCategory' (envelopingAlgebra B))
    [F.IsEquivalence] [F.Additive] [F.CommShift ℤ]
    (e : F.obj (diagonalDerived A) ≅ diagonalDerived B) (i : ℤ) :
    ∃ φ : hochschildCohomology A i ≃+ hochschildCohomology B i,
      ∀ f : hochschildCohomology A i,
        φ f = e.inv ≫ F.map f ≫ (F.commShiftIso i).hom.app (diagonalDerived A) ≫
          (CategoryTheory.shiftFunctor (derivedCategory' (envelopingAlgebra B)) i).map
            e.hom := by
  refine ⟨AddEquiv.ofBijective
    (AddMonoidHom.mk'
      (fun f : hochschildCohomology A i =>
        (e.inv ≫ F.map f ≫ (F.commShiftIso i).hom.app (diagonalDerived A) ≫
          (CategoryTheory.shiftFunctor (derivedCategory' (envelopingAlgebra B)) i).map e.hom :
            hochschildCohomology B i))
      (fun f g => by simp)) ⟨?_, ?_⟩, fun _ => rfl⟩
  · intro f g h
    apply F.map_injective
    refine (cancel_mono ((F.commShiftIso i).hom.app (diagonalDerived A) ≫
      (CategoryTheory.shiftFunctor (derivedCategory' (envelopingAlgebra B)) i).map e.hom)).1 ?_
    refine (cancel_epi e.inv).1 ?_
    simpa only [AddMonoidHom.mk'_apply, Category.assoc] using h
  · intro g
    obtain ⟨f, hf⟩ := F.map_surjective (e.hom ≫ g ≫
      (CategoryTheory.shiftFunctor (derivedCategory' (envelopingAlgebra B)) i).map e.inv ≫
        (F.commShiftIso i).inv.app (diagonalDerived A))
    refine ⟨f, ?_⟩
    rw [AddMonoidHom.mk'_apply, hf]
    simp

/-! ### Degree zero for an algebra concentrated in degree zero

The source supposes `A = H^0(A)`, read here as `A` being concentrated in degree zero. -/

section Concentrated

variable {A : DifferentialGradedAlgebra.{u, u} R}

/-- Left multiplication by a central element of a differential graded algebra concentrated in
degree zero, as an endomorphism of the regular module. -/
def centerRegularHom (hA : ∀ n : ℤ, n ≠ 0 → A.grading n = ⊥) (z : Subalgebra.center R A.A) :
    DifferentialGradedModule.Hom (regularModule A) (regularModule A) where
  toFun := LinearMap.mulLeft R (z : A.A)
  map_smul := by
    intro x b
    change (z : A.A) * (x * b) = ((z : A.A) * x) * b
    rw [mul_assoc]
  map_grading := by
    intro n x hx
    change (z : A.A) * x ∈ A.grading n
    simpa only [zero_add] using
      (SetLike.mul_mem_graded (mem_grading_zero_of_concentrated hA (z : A.A)) hx :
        (z : A.A) * x ∈ A.grading (0 + n))
  map_d := by
    ext x
    change (z : A.A) * A.d x = A.d ((z : A.A) * x)
    rw [d_eq_zero_of_concentrated hA x, d_eq_zero_of_concentrated hA ((z : A.A) * x), mul_zero]

/-- `centerRegularHom hA z` sends `y` to `z * y`. -/
theorem centerRegularHom_toFun (hA : ∀ n : ℤ, n ≠ 0 → A.grading n = ⊥)
    (z : Subalgebra.center R A.A) (y : (regularModule A).M) :
    (centerRegularHom hA z).toFun y = (z : A.A) * y := rfl

/-- Left multiplication by `1` is the identity of the regular module. -/
theorem centerRegularHom_one (hA : ∀ n : ℤ, n ≠ 0 → A.grading n = ⊥) :
    centerRegularHom hA 1 = DifferentialGradedModule.Hom.id (regularModule A) := by
  refine DifferentialGradedModule.Hom.ext (LinearMap.ext fun y => ?_)
  rw [centerRegularHom_toFun]
  exact one_mul y

/-- Left multiplication by `z * z'` is the composite of the left multiplications by `z` and
`z'`. -/
theorem centerRegularHom_mul (hA : ∀ n : ℤ, n ≠ 0 → A.grading n = ⊥)
    (z z' : Subalgebra.center R A.A) :
    centerRegularHom hA (z * z') =
      DifferentialGradedModule.Hom.comp (centerRegularHom hA z) (centerRegularHom hA z') := by
  refine DifferentialGradedModule.Hom.ext (LinearMap.ext fun y => ?_)
  rw [centerRegularHom_toFun]
  change (z : A.A) * (z' : A.A) * y =
    (centerRegularHom hA z).toFun ((centerRegularHom hA z').toFun y)
  rw [centerRegularHom_toFun, centerRegularHom_toFun, mul_assoc]

/-- Left multiplication by `0` sends every element to `0`. -/
theorem centerRegularHom_apply_zero (hA : ∀ n : ℤ, n ≠ 0 → A.grading n = ⊥)
    (u : (regularModule A).M) : (centerRegularHom hA 0).toFun u = 0 := by
  rw [centerRegularHom_toFun]
  change (0 : A.A) * u = 0
  rw [zero_mul]

/-- Left multiplication by `z + z'` is the sum of the left multiplications by `z` and `z'`. -/
theorem centerRegularHom_apply_add (hA : ∀ n : ℤ, n ≠ 0 → A.grading n = ⊥)
    (z z' : Subalgebra.center R A.A) (u : (regularModule A).M) :
    (centerRegularHom hA (z + z')).toFun u =
      (centerRegularHom hA z).toFun u + (centerRegularHom hA z').toFun u := by
  rw [centerRegularHom_toFun, centerRegularHom_toFun, centerRegularHom_toFun]
  change ((z : A.A) + (z' : A.A)) * u = _
  rw [add_mul]

/-- Left multiplication by the image of `r : R` in the centre is scalar multiplication by `r`. -/
theorem centerRegularHom_apply_algebraMap (hA : ∀ n : ℤ, n ≠ 0 → A.grading n = ⊥) (r : R)
    (u : (regularModule A).M) :
    (centerRegularHom hA (algebraMap R (Subalgebra.center R A.A) r)).toFun u = r • u := by
  rw [centerRegularHom_toFun]
  change algebraMap R A.A r * u = r • u
  exact (Algebra.smul_def r u).symm

/-- Left multiplication by a central element commutes with the left action of `A` on the regular
module. -/
theorem centerRegularHom_map_left (hA : ∀ n : ℤ, n ≠ 0 → A.grading n = ⊥)
    (z : Subalgebra.center R A.A) (n p : ℤ) (a : A.grading n)
    (x : (regularModule A).grading p) :
    (centerRegularHom hA z).toFun
        ((show (regularModule A).grading (p + n) from
          ((regularBimoduleStructure A.idHom).1.action n a).v p (p + n) (by omega) x) :
            (regularModule A).M) =
      ((show (regularModule A).grading (p + n) from
        ((regularBimoduleStructure A.idHom).1.action n a).v p (p + n) (by omega)
          ((centerRegularHom hA z).gradedMap p x)) : (regularModule A).M) := by
  rw [regularBimoduleStructure_action A.idHom n p a x,
    regularBimoduleStructure_action A.idHom n p a ((centerRegularHom hA z).gradedMap p x)]
  change (z : A.A) * ((AlgHom.id R A.A) (a : A.A) * (x : A.A)) =
    (AlgHom.id R A.A) (a : A.A) * ((z : A.A) * (x : A.A))
  rw [AlgHom.coe_id, id_eq, ← mul_assoc, ← mul_assoc,
    (Subalgebra.mem_center_iff.mp z.property) (a : A.A)]

/-- Left multiplication by a central element of a differential graded algebra concentrated in
degree zero, as an endomorphism of the diagonal bimodule. -/
def centerDiagonalHom (hA : ∀ n : ℤ, n ≠ 0 → A.grading n = ⊥) (z : Subalgebra.center R A.A) :
    regularBimodule A ⟶ regularBimodule A where
  rightHom := centerRegularHom hA z
  map_left := centerRegularHom_map_left hA z

/-- Left multiplication by `1` is the identity of the diagonal bimodule. -/
theorem centerDiagonalHom_one (hA : ∀ n : ℤ, n ≠ 0 → A.grading n = ⊥) :
    centerDiagonalHom hA 1 = 𝟙 (regularBimodule A) :=
  Bimodule.Hom.ext (centerRegularHom_one hA)

/-- Left multiplication by `z * z'` on the diagonal bimodule is the composite of the left
multiplications by `z'` and then `z`. -/
theorem centerDiagonalHom_mul (hA : ∀ n : ℤ, n ≠ 0 → A.grading n = ⊥)
    (z z' : Subalgebra.center R A.A) :
    centerDiagonalHom hA (z * z') = centerDiagonalHom hA z' ≫ centerDiagonalHom hA z :=
  Bimodule.Hom.ext (centerRegularHom_mul hA z z')

/-- Every endomorphism of the regular module is left multiplication by its value at `1`. -/
theorem regularHom_apply (g : DifferentialGradedModule.Hom (regularModule A) (regularModule A))
    (y : (regularModule A).M) :
    g.toFun y = g.toFun (1 : (regularModule A).M) * y := by
  have h := g.map_smul (1 : (regularModule A).M) y
  change g.toFun ((1 : A.A) * y) = g.toFun (1 : A.A) * y at h
  rwa [one_mul] at h

/-- The value at `1` of an endomorphism of the regular module that commutes with the left
multiplications is central, when `A` is concentrated in degree zero. -/
theorem regularHom_one_mem_center (hA : ∀ n : ℤ, n ≠ 0 → A.grading n = ⊥)
    (g : DifferentialGradedModule.Hom (regularModule A) (regularModule A))
    (hg : ∀ (n p : ℤ) (a : A.grading n) (x : (regularModule A).grading p),
      g.toFun ((show (regularModule A).grading (p + n) from
          ((regularBimoduleStructure A.idHom).1.action n a).v p (p + n) (by omega) x) :
            (regularModule A).M) =
        ((show (regularModule A).grading (p + n) from
          ((regularBimoduleStructure A.idHom).1.action n a).v p (p + n) (by omega)
            (g.gradedMap p x)) : (regularModule A).M)) :
    g.toFun (1 : (regularModule A).M) ∈ Subalgebra.center R A.A := by
  rw [Subalgebra.mem_center_iff]
  intro a
  have h := hg 0 0 ⟨a, mem_grading_zero_of_concentrated hA a⟩
    ⟨(1 : A.A), SetLike.one_mem_graded A.grading⟩
  rw [regularBimoduleStructure_action A.idHom 0 0 ⟨a, mem_grading_zero_of_concentrated hA a⟩
      ⟨(1 : A.A), SetLike.one_mem_graded A.grading⟩,
    regularBimoduleStructure_action A.idHom 0 0 ⟨a, mem_grading_zero_of_concentrated hA a⟩
      (g.gradedMap 0 ⟨(1 : A.A), SetLike.one_mem_graded A.grading⟩)] at h
  change g.toFun ((AlgHom.id R A.A) a * (1 : A.A)) =
    (AlgHom.id R A.A) a * g.toFun (1 : (regularModule A).M) at h
  rw [AlgHom.coe_id, id_eq, mul_one] at h
  rw [← h, regularHom_apply g a]

/-- For a differential graded algebra concentrated in degree zero, left multiplication is a
bijection from the centre of `A` onto the endomorphisms of the diagonal bimodule. -/
theorem centerDiagonalHom_bijective (hA : ∀ n : ℤ, n ≠ 0 → A.grading n = ⊥) :
    Function.Bijective (centerDiagonalHom hA) := by
  have e : ∀ w : Subalgebra.center R A.A,
      (centerDiagonalHom hA w).rightHom.toFun (1 : (regularModule A).M) = (w : A.A) := fun w => by
    change (centerRegularHom hA w).toFun (1 : (regularModule A).M) = (w : A.A)
    rw [centerRegularHom_toFun]
    exact mul_one _
  constructor
  · intro z z' h
    have h' : (centerDiagonalHom hA z).rightHom.toFun (1 : (regularModule A).M) =
        (centerDiagonalHom hA z').rightHom.toFun (1 : (regularModule A).M) := by rw [h]
    rw [e z, e z'] at h'
    exact Subtype.ext h'
  · intro f
    refine ⟨⟨f.rightHom.toFun (1 : (regularModule A).M),
      regularHom_one_mem_center hA f.rightHom f.map_left⟩, ?_⟩
    refine Bimodule.Hom.ext (DifferentialGradedModule.Hom.ext (LinearMap.ext fun y => ?_))
    exact (centerRegularHom_toFun hA _ y).trans (regularHom_apply f.rightHom y).symm

/-- The centre of `A`, mapped to the endomorphism algebra of the diagonal bimodule read as a
module over the enveloping algebra through Tag 0FQJ, by left multiplication. -/
def centerToDiagonalModuleEnd (hA : ∀ n : ℤ, n ≠ 0 → A.grading n = ⊥) :
    Subalgebra.center R A.A →ₐ[R]
      End ((tensorEquivalence A A).equivalence.functor.obj (regularBimodule A)) := by
  refine {
    toFun := fun z => .of ((tensorEquivalence A A).equivalence.functor.map (centerDiagonalHom hA z))
    map_one' := ?_
    map_mul' := ?_
    map_zero' := ?_
    map_add' := ?_
    commutes' := ?_ }
  · ext : 1
    change (tensorEquivalence A A).equivalence.functor.map (centerDiagonalHom hA 1) = 𝟙 _
    rw [centerDiagonalHom_one]
    exact CategoryTheory.Functor.map_id _ _
  · intro z z'
    ext : 1
    change (tensorEquivalence A A).equivalence.functor.map (centerDiagonalHom hA (z * z')) =
      (tensorEquivalence A A).equivalence.functor.map (centerDiagonalHom hA z') ≫
        (tensorEquivalence A A).equivalence.functor.map (centerDiagonalHom hA z)
    rw [centerDiagonalHom_mul, CategoryTheory.Functor.map_comp]
  · apply End.ext
    change (tensorEquivalence A A).equivalence.functor.map (centerDiagonalHom hA 0) = 0
    apply DifferentialGradedModule.Hom.ext
    refine LinearMap.ext fun x => ?_
    apply ((tensorEquivalence A A).underlying (regularBimodule A)).injective
    have h1 := (tensorEquivalence A A).naturality (centerDiagonalHom hA 0) x
    have h4 : (0 : (tensorEquivalence A A).equivalence.functor.obj (regularBimodule A) ⟶
        (tensorEquivalence A A).equivalence.functor.obj (regularBimodule A)).toFun x = 0 := rfl
    rw [h1, h4, map_zero]
    exact centerRegularHom_apply_zero hA _
  · intro z z'
    apply End.ext
    change (tensorEquivalence A A).equivalence.functor.map (centerDiagonalHom hA (z + z')) =
      (tensorEquivalence A A).equivalence.functor.map (centerDiagonalHom hA z) +
        (tensorEquivalence A A).equivalence.functor.map (centerDiagonalHom hA z')
    apply DifferentialGradedModule.Hom.ext
    refine LinearMap.ext fun x => ?_
    apply ((tensorEquivalence A A).underlying (regularBimodule A)).injective
    have h1 := (tensorEquivalence A A).naturality (centerDiagonalHom hA (z + z')) x
    have h2 := (tensorEquivalence A A).naturality (centerDiagonalHom hA z) x
    have h3 := (tensorEquivalence A A).naturality (centerDiagonalHom hA z') x
    have h4 : ((tensorEquivalence A A).equivalence.functor.map (centerDiagonalHom hA z) +
          (tensorEquivalence A A).equivalence.functor.map (centerDiagonalHom hA z')).toFun x =
        ((tensorEquivalence A A).equivalence.functor.map (centerDiagonalHom hA z)).toFun x +
          ((tensorEquivalence A A).equivalence.functor.map
            (centerDiagonalHom hA z')).toFun x := rfl
    rw [h1, h4, map_add, h2, h3]
    exact centerRegularHom_apply_add hA z z' _
  · intro r
    apply End.ext
    change (tensorEquivalence A A).equivalence.functor.map
      (centerDiagonalHom hA (algebraMap R (Subalgebra.center R A.A) r)) = r • 𝟙 _
    apply DifferentialGradedModule.Hom.ext
    refine LinearMap.ext fun x => ?_
    apply ((tensorEquivalence A A).underlying (regularBimodule A)).injective
    have h1 := (tensorEquivalence A A).naturality
      (centerDiagonalHom hA (algebraMap R (Subalgebra.center R A.A) r)) x
    have h4 : (r • 𝟙 ((tensorEquivalence A A).equivalence.functor.obj
        (regularBimodule A))).toFun x = r • x := rfl
    rw [h1, h4, map_smul]
    exact centerRegularHom_apply_algebraMap hA r _

/-- **The endomorphism algebra of the diagonal bimodule is the centre.** For a differential
graded algebra concentrated in degree zero, the `R`-algebra of endomorphisms of the diagonal
bimodule — equivalently, of the diagonal read as a module over the enveloping algebra through
Tag 0FQJ — is the centre of `A`.

This is the bimodule-level form of the source's `HH^0(A, d) = Z(A)` for `A = H^0(A)`. The
source's own statement is about the endomorphism group in the *derived* category; the comparison
map from the algebra below to that group is `centerToDiagonalDerivedEnd`, and it is proved
bijective in `centerAlgEquivDiagonalDerivedEnd`. -/
def centerAlgEquivDiagonalEnd (hA : ∀ n : ℤ, n ≠ 0 → A.grading n = ⊥) :
    Subalgebra.center R A.A ≃ₐ[R]
      End ((tensorEquivalence A A).equivalence.functor.obj (regularBimodule A)) :=
  AlgEquiv.ofBijective (centerToDiagonalModuleEnd hA) (by
    change Function.Bijective (End.homEquiv.symm ∘
      (fun z => (tensorEquivalence A A).equivalence.functor.map (centerDiagonalHom hA z)))
    exact End.homEquiv.symm.bijective.comp (Function.Bijective.comp
      (g := (tensorEquivalence A A).equivalence.functor.map
        (X := regularBimodule A) (Y := regularBimodule A))
      ⟨CategoryTheory.Functor.map_injective _, CategoryTheory.Functor.map_surjective _⟩
      (centerDiagonalHom_bijective hA)))

end Concentrated

/-! ### The passage to the derived category is injective on concentrated modules -/

section Localization

open CategoryTheory.Limits

variable {C : DifferentialGradedAlgebra.{u, u} R}

/-- Two morphisms between short complexes with zero differentials in an abelian category agree on
the middle objects when they induce the same map on homology. -/
theorem shortComplex_middleMap_eq_of_homologyMap_eq
    {D : Type*} [Category D] [Abelian D] {S T : ShortComplex D}
    (hfS : S.f = 0) (hgS : S.g = 0) (hfT : T.f = 0) (hgT : T.g = 0)
    (f g : S ⟶ T) (h : ShortComplex.homologyMap f = ShortComplex.homologyMap g) :
    f.τ₂ = g.τ₂ := by
  rwa [(ShortComplex.LeftHomologyMapData.ofZeros f hfS hgS hfT hgT).homologyMap_eq,
    (ShortComplex.LeftHomologyMapData.ofZeros g hfS hgS hfT hgT).homologyMap_eq,
    Iso.cancel_iso_hom_left, Iso.cancel_iso_inv_right] at h

/-- A homomorphism between differential graded modules concentrated in degree zero is determined
by the map it induces on degree-zero cohomology. -/
theorem concentrated_homologyMap_injective (M N : DifferentialGradedModule C)
    (hM : ∀ n : ℤ, n ≠ 0 → M.grading n = ⊥) (hN : ∀ n : ℤ, n ≠ 0 → N.grading n = ⊥) :
    Function.Injective (fun f : M ⟶ N =>
      HomologicalComplex.homologyMap ((forgetToCochainComplex C).map f) 0) := by
  intro f g h
  have hd (P : DifferentialGradedModule C) (hP : ∀ n : ℤ, n ≠ 0 → P.grading n = ⊥) (i j : ℤ) :
      P.toCochainComplex.d i j = 0 := by
    by_cases hij : i + 1 = j
    · subst j
      rw [DifferentialGradedModule.toCochainComplex_d]
      ext x
      exact module_d_eq_zero_of_concentrated P hP x
    · exact P.toCochainComplex.shape i j hij
  have hfg := shortComplex_middleMap_eq_of_homologyMap_eq
    (S := M.toCochainComplex.sc 0) (T := N.toCochainComplex.sc 0)
    (hd M hM _ _) (hd M hM _ _) (hd N hN _ _) (hd N hN _ _)
    ((HomologicalComplex.shortComplexFunctor _ _ 0).map ((forgetToCochainComplex C).map f))
    ((HomologicalComplex.shortComplexFunctor _ _ 0).map ((forgetToCochainComplex C).map g)) h
  refine DifferentialGradedModule.Hom.ext (LinearMap.ext fun x => ?_)
  exact congrArg Subtype.val (ConcreteCategory.congr_hom hfg
    (⟨x, module_mem_grading_zero_of_concentrated M hM x⟩ : M.grading 0))

/-- The passage from differential graded modules to the derived category is injective on
homomorphisms between modules concentrated in degree zero: degree-zero cohomology, which factors
through the derived category, already determines such a homomorphism. -/
theorem concentrated_localization_map_injective (M N : DifferentialGradedModule C)
    (hM : ∀ n : ℤ, n ≠ 0 → M.grading n = ⊥) (hN : ∀ n : ℤ, n ≠ 0 → N.grading n = ⊥) :
    Function.Injective
      ((toHomotopyCategory C ⋙ (quasiIsomorphisms' C).Q).map (X := M) (Y := N)) := by
  intro f g h
  let e := Functor.isoWhiskerLeft (toHomotopyCategory C)
      (degreeZeroCohomologyOnLocalizationIso' C) ≪≫ degreeZeroCohomologyOnHomotopyIso' C
  have hh := congrArg (degreeZeroCohomologyOnLocalization' C).map h
  have hn := e.hom.naturality f
  have hn' := e.hom.naturality g
  have hh' : e.hom.app M ≫
      (forgetToCochainComplex C ⋙
        HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℤ) 0).map f =
      e.hom.app M ≫ (forgetToCochainComplex C ⋙
        HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℤ) 0).map g := by
    rw [← hn, ← hn']
    exact congrArg (· ≫ e.hom.app N) hh
  exact concentrated_homologyMap_injective M N hM hN
    ((Iso.cancel_iso_hom_left (e.app M) _ _).mp hh')

/-- **For an algebra concentrated in degree zero the passage to the derived category is bijective
on the homomorphisms between modules concentrated in degree zero.** Injectivity is the
degree-zero cohomology functor; surjectivity is
`DifferentialGradedModule.concentrated_q_map_surjective`, which resolves the source by free
modules placed in the degrees `≤ 0`. -/
theorem concentrated_localization_map_bijective (hC : ∀ n : ℤ, n ≠ 0 → C.grading n = ⊥)
    (M N : DifferentialGradedModule C)
    (hM : ∀ n : ℤ, n ≠ 0 → M.grading n = ⊥) (hN : ∀ n : ℤ, n ≠ 0 → N.grading n = ⊥) :
    Function.Bijective
      ((toHomotopyCategory C ⋙ (quasiIsomorphisms' C).Q).map (X := M) (Y := N)) :=
  ⟨concentrated_localization_map_injective M N hM hN,
    concentrated_q_map_surjective C hC M hM N hN⟩

end Localization

/-! ### The centre inside degree-zero Hochschild cohomology -/

section CenterToDerived

variable {A : DifferentialGradedAlgebra.{u, u} R}

/-- Tag 0FQJ does not change the grading, so a bimodule whose underlying right module is
concentrated in a degree gives a module over the enveloping algebra concentrated there. -/
theorem tensorEquivalence_grading_eq_bot (A B : DifferentialGradedAlgebra.{u, u} R)
    (N : Bimodule A B) (n : ℤ) (hN : N.rightModule.grading n = ⊥) :
    ((tensorEquivalence A B).equivalence.functor.obj N).grading n = ⊥ := by
  refine le_antisymm (fun x hx => ?_) bot_le
  have hx' := ((tensorEquivalence A B).grading N n x).mp hx
  rw [hN, Submodule.mem_bot] at hx'
  exact (Submodule.mem_bot R).mpr
    (((tensorEquivalence A B).underlying N).injective (by rw [hx', map_zero]))

/-- The diagonal bimodule of an algebra concentrated in degree zero, read as a module over the
enveloping algebra, is concentrated in degree zero. -/
theorem diagonalModule_concentrated (hA : ∀ n : ℤ, n ≠ 0 → A.grading n = ⊥) (n : ℤ)
    (hn : n ≠ 0) :
    ((tensorEquivalence A A).equivalence.functor.obj (regularBimodule A)).grading n = ⊥ :=
  tensorEquivalence_grading_eq_bot A A (regularBimodule A) n (hA n hn)

/-- The centre of a differential graded algebra concentrated in degree zero, mapped by left
multiplication into the endomorphism algebra of the diagonal bimodule in the derived category of
bimodules. -/
def centerToDiagonalDerivedEnd (hA : ∀ n : ℤ, n ≠ 0 → A.grading n = ⊥) :
    Subalgebra.center R A.A →ₐ[R] End (diagonalDerived A) :=
  (endAlgHomOfLinearFunctor
    (toHomotopyCategory (envelopingAlgebra A) ⋙
      (quasiIsomorphisms' (envelopingAlgebra A)).Q) _).comp (centerToDiagonalModuleEnd hA)

/-- **The centre injects into degree-zero Hochschild cohomology.** For a differential graded
algebra concentrated in degree zero, left multiplication by a central element gives an injective
`R`-algebra map from `Z(A)` to the endomorphism algebra of the diagonal bimodule in the derived
category of bimodules.

The source asserts that this map is an isomorphism, `HH^0(A, d) = Z(A)`; surjectivity is
`centerToDiagonalDerivedEnd_surjective` and the isomorphism is
`centerAlgEquivDiagonalDerivedEnd`. -/
theorem centerToDiagonalDerivedEnd_injective (hA : ∀ n : ℤ, n ≠ 0 → A.grading n = ⊥) :
    Function.Injective (centerToDiagonalDerivedEnd hA) := by
  intro z z' h
  have h' : (toHomotopyCategory (envelopingAlgebra A) ⋙
        (quasiIsomorphisms' (envelopingAlgebra A)).Q).map (centerToDiagonalModuleEnd hA z).asHom =
      (toHomotopyCategory (envelopingAlgebra A) ⋙
        (quasiIsomorphisms' (envelopingAlgebra A)).Q).map
          (centerToDiagonalModuleEnd hA z').asHom := congrArg End.asHom h
  exact (centerAlgEquivDiagonalEnd hA).injective (End.ext
    (concentrated_localization_map_injective _ _
      (diagonalModule_concentrated hA) (diagonalModule_concentrated hA) h'))

/-- The centre of `A`, mapped into degree-zero Hochschild cohomology. -/
def centerToHochschildCohomologyZero (hA : ∀ n : ℤ, n ≠ 0 → A.grading n = ⊥) :
    Subalgebra.center R A.A →+ hochschildCohomology A 0 :=
  (endAddEquivHochschildCohomologyZero A).toAddMonoidHom.comp
    (centerToDiagonalDerivedEnd hA).toAddMonoidHom

/-- For a differential graded algebra concentrated in degree zero, the map from the centre of `A`
to degree-zero Hochschild cohomology is injective. -/
theorem centerToHochschildCohomologyZero_injective
    (hA : ∀ n : ℤ, n ≠ 0 → A.grading n = ⊥) :
    Function.Injective (centerToHochschildCohomologyZero hA) :=
  (endAddEquivHochschildCohomologyZero A).injective.comp
    (centerToDiagonalDerivedEnd_injective hA)

/-! ### The centre is the whole of degree-zero Hochschild cohomology -/

/-- The graded opposite of a differential graded algebra concentrated in degree zero is
concentrated in degree zero: the opposite carries the same grading, transported along the
comparison isomorphism of its underlying modules. -/
theorem oppAlgebra_grading_eq_bot (hA : ∀ n : ℤ, n ≠ 0 → A.grading n = ⊥) (n : ℤ) (hn : n ≠ 0) :
    (oppAlgebra A).grading n = ⊥ := by
  refine le_antisymm (fun x hx => ?_) bot_le
  have h := ((DifferentialGradedAlgebra.opposite R A).mem_grading_iff n x).mp hx
  rw [hA n hn, Submodule.mem_bot] at h
  exact (Submodule.mem_bot R).mpr
    ((DifferentialGradedAlgebra.opposite R A).equiv.injective (by rw [h, map_zero]))

/-- **The enveloping algebra of an algebra concentrated in degree zero is concentrated in degree
zero.** Its degree-`n` part is spanned by the tensors of a homogeneous element of the opposite
algebra with a homogeneous element of the algebra whose degrees add to `n`, and for `n ≠ 0` one of
the two factors is homogeneous of a nonzero degree, hence zero. -/
theorem envelopingAlgebra_grading_eq_bot (hA : ∀ n : ℤ, n ≠ 0 → A.grading n = ⊥) (n : ℤ)
    (hn : n ≠ 0) : (envelopingAlgebra A).grading n = ⊥ := by
  refine le_antisymm ?_ bot_le
  change DifferentialGradedAlgebra.tensorProductGrading (oppAlgebra A) A n ≤ ⊥
  refine Submodule.span_le.mpr ?_
  rintro x ⟨p, q, a, b, ha, hb, hpq, rfl⟩
  by_cases hp : p = 0
  · have hb0 : b = 0 := by
      rw [hA q (by omega), Submodule.mem_bot] at hb
      exact hb
    rw [hb0]
    change GradedTensorProduct.of R (oppAlgebra A).grading A.grading (a ⊗ₜ[R] 0) ∈ _
    rw [TensorProduct.tmul_zero, map_zero]
    exact Submodule.zero_mem _
  · have ha0 : a = 0 := by
      rw [oppAlgebra_grading_eq_bot hA p hp, Submodule.mem_bot] at ha
      exact ha
    rw [ha0]
    change GradedTensorProduct.of R (oppAlgebra A).grading A.grading
      ((0 : (oppAlgebra A).A) ⊗ₜ[R] b) ∈ _
    rw [TensorProduct.zero_tmul, map_zero]
    exact Submodule.zero_mem _

/-- **The centre surjects onto degree-zero Hochschild cohomology.** For a differential graded
algebra concentrated in degree zero every endomorphism of the diagonal bimodule in the derived
category of bimodules is left multiplication by a central element.

The enveloping algebra is concentrated in degree zero as well, and so is the diagonal read over
it, so the passage to the derived category is surjective on the endomorphisms of the diagonal by
`DifferentialGradedModule.concentrated_q_map_surjective`; at the level of bimodules the
endomorphism algebra of the diagonal is the centre, which is
`DifferentialGraded.Bimodule.centerAlgEquivDiagonalEnd`. -/
theorem centerToDiagonalDerivedEnd_surjective (hA : ∀ n : ℤ, n ≠ 0 → A.grading n = ⊥) :
    Function.Surjective (centerToDiagonalDerivedEnd hA) := by
  intro g
  obtain ⟨φ, hφ⟩ := concentrated_q_map_surjective (envelopingAlgebra A)
    (envelopingAlgebra_grading_eq_bot hA)
    ((tensorEquivalence A A).equivalence.functor.obj (regularBimodule A))
    (diagonalModule_concentrated hA)
    ((tensorEquivalence A A).equivalence.functor.obj (regularBimodule A))
    (diagonalModule_concentrated hA) g.asHom
  obtain ⟨z, hz⟩ := (centerAlgEquivDiagonalEnd hA).surjective (.of φ)
  have hz' : centerToDiagonalModuleEnd hA z = .of φ := hz
  refine ⟨z, End.ext ?_⟩
  change (toHomotopyCategory (envelopingAlgebra A) ⋙
    (quasiIsomorphisms' (envelopingAlgebra A)).Q).map (centerToDiagonalModuleEnd hA z).asHom =
      g.asHom
  rw [hz']
  exact hφ

/-- **`HH^0(A, d) = Z(A)`.** For a differential graded algebra concentrated in degree zero — the
source's hypothesis `A = H^0(A)` — left multiplication by a central element is an isomorphism of
`R`-algebras from the centre of `A` onto the endomorphism algebra of the diagonal bimodule in the
derived category of bimodules, which is degree-zero Hochschild cohomology. -/
def centerAlgEquivDiagonalDerivedEnd (hA : ∀ n : ℤ, n ≠ 0 → A.grading n = ⊥) :
    Subalgebra.center R A.A ≃ₐ[R] End (diagonalDerived A) :=
  AlgEquiv.ofBijective (centerToDiagonalDerivedEnd hA)
    ⟨centerToDiagonalDerivedEnd_injective hA, centerToDiagonalDerivedEnd_surjective hA⟩

/-- For a differential graded algebra concentrated in degree zero, the map from the centre of `A`
to degree-zero Hochschild cohomology is surjective. -/
theorem centerToHochschildCohomologyZero_surjective
    (hA : ∀ n : ℤ, n ≠ 0 → A.grading n = ⊥) :
    Function.Surjective (centerToHochschildCohomologyZero hA) :=
  (endAddEquivHochschildCohomologyZero A).surjective.comp
    (centerToDiagonalDerivedEnd_surjective hA)

/-- **`HH^0(A, d) = Z(A)`, read in Hochschild cohomology.** The centre of an algebra concentrated
in degree zero is its degree-zero Hochschild cohomology, by left multiplication. -/
def centerAddEquivHochschildCohomologyZero (hA : ∀ n : ℤ, n ≠ 0 → A.grading n = ⊥) :
    Subalgebra.center R A.A ≃+ hochschildCohomology A 0 :=
  AddEquiv.ofBijective (centerToHochschildCohomologyZero hA)
    ⟨centerToHochschildCohomologyZero_injective hA,
      centerToHochschildCohomologyZero_surjective hA⟩

end CenterToDerived

section DiagonalTransport

variable {A B : DifferentialGradedAlgebra.{u, u} R}
  (F : derivedCategory' (envelopingAlgebra A) ⥤ derivedCategory' (envelopingAlgebra B))

/-- **A diagonal-matching equivalence identifies the endomorphism algebras of the diagonals.**
Let `F : D(A^{opp} ⊗_R A, d) ⥤ D(B^{opp} ⊗_R B, d)` be an additive, `R`-linear equivalence of
the bimodule derived categories and let `e` identify `F` of the diagonal bimodule of `A` with
the diagonal bimodule of `B`. Then `End (diagonalDerived A)` and `End (diagonalDerived B)` are
isomorphic as `R`-algebras, by `f ↦ e⁻¹ ∘ F f ∘ e`.

This is the degree-zero case of
`DifferentialGraded.Bimodule.hochschildCohomology_addEquiv_of_diagonalEquivalence`, sharpened
from an isomorphism of additive groups to one of `R`-algebras: the multiplication of
`HH^0(A, d) = End (diagonalDerived A)` is composition, which `F` preserves, and the scalars are
preserved because `F` is `R`-linear. Compatibility with the translation is not needed, since no
shift occurs in degree zero.

Being an isomorphism of algebras rather than of groups is what makes this the step that turns
the source's invariance of Hochschild cohomology into the invariance of the *centre*: composed
on both sides with `DifferentialGraded.Bimodule.centerAlgEquivDiagonalDerivedEnd` it gives
`DifferentialGraded.Bimodule.centerAlgEquivOfDiagonalEquivalence`. -/
noncomputable def diagonalDerivedEndAlgEquiv [F.IsEquivalence] [F.Additive] [F.Linear R]
    (e : F.obj (diagonalDerived A) ≅ diagonalDerived B) :
    End (diagonalDerived A) ≃ₐ[R] End (diagonalDerived B) :=
  ((Functor.FullyFaithful.ofFullyFaithful F).algEquivEndOfFullyFaithful (R := R)
      (diagonalDerived A)).trans
    (Iso.endAlgEquiv (R := R) e)

/-- **The centres of two algebras concentrated in degree zero, compared along a diagonal-matching
equivalence of their bimodule derived categories.** For differential graded `R`-algebras `A` and
`B` concentrated in degree zero and an additive, `R`-linear equivalence
`F : D(A^{opp} ⊗_R A, d) ⥤ D(B^{opp} ⊗_R B, d)` carrying the diagonal bimodule of `A` to the
diagonal bimodule of `B`, the centres of `A` and of `B` are isomorphic as `R`-algebras.

This is the whole of Rickard's chain
`Z(A) ≅ HH^0(A) = End_{D(A^{opp} ⊗_R A, d)}(A) ≅ End_{D(B^{opp} ⊗_R B, d)}(B) = HH^0(B) ≅ Z(B)`
except for the construction of `F`: the two outer identifications are
`DifferentialGraded.Bimodule.centerAlgEquivDiagonalDerivedEnd` and the middle one is
`DifferentialGraded.Bimodule.diagonalDerivedEndAlgEquiv`.

**This is not a proof of [Stacks, Tag 09SD]**, and it is deliberately not registered as one. The
hypothesis `F` is not produced from a derived equivalence `D(A) ≌ D(B)` anywhere in this library,
and the source does not claim it is automatic: it says the functor `M ↦ Ω' ⊗^𝐋_A M ⊗^𝐋_A Ω` is an
equivalence matching the diagonals only "as can happen under suitable flatness conditions". What
this declaration does is reduce the tag, along the route its own remark proposes, to exactly one
missing input — that functor. See the implementation notes of
`StacksFrontier/RingTheory/DerivedEquivalenceCenter.lean` for what constructing it would take. -/
noncomputable def centerAlgEquivOfDiagonalEquivalence [F.IsEquivalence] [F.Additive]
    [F.Linear R] (e : F.obj (diagonalDerived A) ≅ diagonalDerived B)
    (hA : ∀ n : ℤ, n ≠ 0 → A.grading n = ⊥) (hB : ∀ n : ℤ, n ≠ 0 → B.grading n = ⊥) :
    Subalgebra.center R A.A ≃ₐ[R] Subalgebra.center R B.A :=
  (centerAlgEquivDiagonalDerivedEnd hA).trans
    ((diagonalDerivedEndAlgEquiv F e).trans (centerAlgEquivDiagonalDerivedEnd hB).symm)

end DiagonalTransport

end DifferentialGraded.Bimodule

end
