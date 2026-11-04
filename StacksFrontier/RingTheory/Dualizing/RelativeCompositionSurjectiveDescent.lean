module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import StacksFrontier.RingTheory.Dualizing.DerivedHomBaseChange.Conservative
public import StacksFrontier.RingTheory.Dualizing.RelativeCompositionUntwisted

/-!
# Descending an isomorphism with a module along a surjection of rings

Let `f : C →+* C'` be a **surjective** ring map.  Derived restriction of scalars along `f` is
exact, so it commutes with cohomology, and it is faithful; hence it reflects the vanishing of
cohomology, and an object of `D(C')` whose restriction to `C` is concentrated in degree zero is
itself concentrated in degree zero.  Because `f` is surjective, restriction of scalars is
moreover *full* on modules -- a `C`-linear map between `C'`-modules is `C'`-linear -- so the
degree-zero cohomology descends as a `C'`-module.  Therefore

**an object `Z` of `D(C')` with `Z|_C ≅ N|_C` for a `C'`-module `N` satisfies `Z ≅ N` in
`D(C')`.**

This is a descent that restriction of scalars does *not* perform for a general target: it
reflects invertibility of a *morphism* always, but isomorphy of *objects* only when the
comparison object is a module placed in a single degree, where the truncation triangle of the
canonical t-structure reconstructs the object from its cohomology.

## What this is for

The module documentation of `StacksFrontier.RingTheory.Dualizing.RelativeComposition` reduces
clause (2) of [stacks 0E2C] for a composite `R → A → B` to the isomorphism (★)

`RHom_C(C', K ⊗ᴸ_B C) ≅ K_{B/A} ⊗ᴸ_B C'`,  `C = B ⊗[R] B`, `C' = B ⊗[A] B`,

an isomorphism of `D(C')`, and records two things owed of it: the *twist* by
`K_{B/A} ⊗ᴸ_B C`, and the *descent to `D(C')`* of its untwisted half

`RHom_C(C', K_{A/R} ⊗ᴸ_A C) ≅ C'`,

which `Dualizing.nonempty_internalHom_diagonalQuotient_untwisted` proves in `D(C)`.  **The
second of those is discharged here.**  The untwisted half has `C'` in degree zero on the
right-hand side, `Dualizing.diagonalQuotient` is surjective
(`Dualizing.surjective_diagonalQuotient`), and the descent lemma above therefore applies:
`Dualizing.nonempty_diagonalQuotientDerivedHom_untwisted` is the untwisted half as an
isomorphism of `D(C')`, carrying nothing beyond the hypotheses on `K_{A/R}`.

Two notes elsewhere in the tree are out of date because of this, and are corrected here rather
than edited there.  The module documentation of
`StacksFrontier.RingTheory.Dualizing.RelativeComposition` says of the untwisted half that "what it
leaves owed ... is its *descent to `D(C')`*, for the same reason (★) itself needs one"; the
reason is **not** the same, because the right-hand side of the untwisted half is a module in
degree zero and the right-hand side of (★) is not.  And the docstring of
`Dualizing.nonempty_restrict_diagonalQuotientDerivedHom_of_restrictDiagonalTensorIso` in
`StacksFrontier.RingTheory.Dualizing.RelativeCompositionUntwisted` says that "no ring of
[stacks 0E2H] carries a split surjection onto `C'`, so the statement below cannot be upgraded".
That is right about *that* statement, whose right-hand side is `K_{B/A} ⊗ᴸ_B C'`, and it is
right that no *section* exists; but a section is not what an upgrade needs.  Surjectivity of the
ring map alone suffices whenever the comparison object is a module in a single degree, and
`Dualizing.diagonalQuotient` is surjective.

The same lemma applies at the diagonal `Δ_{B/R} : C → B`, which is surjective as well, and
clause (2) of [stacks 0E2C] likewise has a module in degree zero -- the algebra `B` itself -- on
its right-hand side.  So `Dualizing.diagonalDerivedHom_of_internalHom_diagonal` reduces that
clause to a statement about the **single-ring internal Hom of `C`**: no derived Hom along a ring
map and no object of `D(C')` occurs in it.

## Main results

* `Dualizing.liftRestrictScalars` -- a `C`-linear map between `C'`-modules along a surjection is
  `C'`-linear; `Dualizing.isoOfRestrictScalarsIso`, the same for an isomorphism.
* `Dualizing.isLE_of_isLE_restrictScalars`, `Dualizing.isGE_of_isGE_restrictScalars` -- derived
  restriction of scalars reflects the bounds of the canonical t-structure, for an arbitrary ring
  map.
* `Dualizing.nonempty_iso_singleFunctor_of_restrictScalars` -- **the descent lemma.**
* `Dualizing.nonempty_diagonalQuotientDerivedHom_untwisted` -- **the untwisted half of (★) in
  `D(C')`.**
* `Dualizing.diagonalDerivedHom_of_internalHom_diagonal` -- clause (2) of [stacks 0E2C] for a
  composite from a single-ring internal-Hom statement over `C`.

## References

* [Stacks Project, Tag 0E2C](https://stacks.math.columbia.edu/tag/0E2C)
* [Stacks Project, Tag 0E2H](https://stacks.math.columbia.edu/tag/0E2H)
* [Stacks Project, Tag 0A63](https://stacks.math.columbia.edu/tag/0A63)
* [Stacks Project, Tag 0A70](https://stacks.math.columbia.edu/tag/0A70)
* [Stacks Project, Tag 0GMT](https://stacks.math.columbia.edu/tag/0GMT)
-/

@[expose] public section

open CategoryTheory
open CochainComplex.DerivedExtensionScalars
open StacksDraft.DerivedHom
open scoped TensorProduct

universe w w' u

namespace Dualizing

noncomputable section

/-! ### Restriction of scalars along a surjection, on modules -/

section Modules

variable {C C' : Type u} [CommRing C] [CommRing C'] (f : C →+* C')

/-- **A `C`-linear map between `C'`-modules along a surjection `f : C →+* C'` is `C'`-linear.**
Every scalar of `C'` is `f c` for some `c`, and the restricted action of `c` is the action of
`f c`, so `C'`-linearity is `C`-linearity. -/
def liftRestrictScalars (hf : Function.Surjective f) {M N : ModuleCat.{u} C'}
    (h : (ModuleCat.restrictScalars f).obj M ⟶ (ModuleCat.restrictScalars f).obj N) : M ⟶ N :=
  ModuleCat.ofHom
    { toFun := fun m => h.hom m
      map_add' := fun x y => h.hom.map_add x y
      map_smul' := fun c' m => by
        obtain ⟨c, rfl⟩ := hf c'
        exact h.hom.map_smul c m }

/-- `Dualizing.liftRestrictScalars` is a section of restriction of scalars on morphisms. -/
theorem map_liftRestrictScalars (hf : Function.Surjective f) {M N : ModuleCat.{u} C'}
    (h : (ModuleCat.restrictScalars f).obj M ⟶ (ModuleCat.restrictScalars f).obj N) :
    (ModuleCat.restrictScalars f).map (liftRestrictScalars f hf h) = h := rfl

/-- **An isomorphism of `C'`-modules from a `C`-linear one, along a surjection.**  Both the
isomorphism and its inverse are `C'`-linear by `Dualizing.liftRestrictScalars`, and the two
composites are identities because restriction of scalars is faithful. -/
def isoOfRestrictScalarsIso (hf : Function.Surjective f) {M N : ModuleCat.{u} C'}
    (g : (ModuleCat.restrictScalars f).obj M ≅ (ModuleCat.restrictScalars f).obj N) :
    M ≅ N where
  hom := liftRestrictScalars f hf g.hom
  inv := liftRestrictScalars f hf g.inv
  hom_inv_id := (ModuleCat.restrictScalars f).map_injective (by
    simp only [Functor.map_comp, map_liftRestrictScalars, g.hom_inv_id]; rfl)
  inv_hom_id := (ModuleCat.restrictScalars f).map_injective (by
    simp only [Functor.map_comp, map_liftRestrictScalars, g.inv_hom_id]; rfl)

/-- **Restriction of scalars reflects the zero module**, being faithful and additive. -/
theorem isZero_of_isZero_restrictScalars {M : ModuleCat.{u} C'}
    (h : Limits.IsZero ((ModuleCat.restrictScalars f).obj M)) : Limits.IsZero M := by
  rw [Limits.IsZero.iff_id_eq_zero] at h ⊢
  apply (ModuleCat.restrictScalars f).map_injective
  simp only [Functor.map_zero]
  exact h

end Modules

/-! ### The descent lemma -/

section Derived

variable {C C' : Type u} [CommRing C] [CommRing C']
variable [HasDerivedCategory.{w} (ModuleCat.{u} C)] [HasDerivedCategory.{w'} (ModuleCat.{u} C')]
variable (f : C →+* C')

/-- **Derived restriction of scalars reflects the upper bound of the canonical t-structure.**
Cohomology commutes with an exact functor, and restriction of scalars reflects the zero module.
No hypothesis on the ring map. -/
theorem isLE_of_isLE_restrictScalars (Z : DerivedCategory (ModuleCat.{u} C')) (n : ℤ)
    [((ModuleCat.restrictScalars f).mapDerivedCategory.obj Z).IsLE n] : Z.IsLE n := by
  rw [DerivedCategory.isLE_iff]
  intro i hi
  refine isZero_of_isZero_restrictScalars f (Limits.IsZero.of_iso ?_
    (((ModuleCat.restrictScalars f).mapDerivedCategoryCompHomologyFunctorIso i).app Z).symm)
  exact (DerivedCategory.isLE_iff _ n).1 inferInstance i hi

/-- **Derived restriction of scalars reflects the lower bound of the canonical t-structure.** -/
theorem isGE_of_isGE_restrictScalars (Z : DerivedCategory (ModuleCat.{u} C')) (n : ℤ)
    [((ModuleCat.restrictScalars f).mapDerivedCategory.obj Z).IsGE n] : Z.IsGE n := by
  rw [DerivedCategory.isGE_iff]
  intro i hi
  refine isZero_of_isZero_restrictScalars f (Limits.IsZero.of_iso ?_
    (((ModuleCat.restrictScalars f).mapDerivedCategoryCompHomologyFunctorIso i).app Z).symm)
  exact (DerivedCategory.isGE_iff _ n).1 inferInstance i hi

/-- **The descent lemma.**  Let `f : C →+* C'` be a *surjective* ring map, let `Z` be an object
of `D(C')` and let `N` be a `C'`-module.  If the restriction of `Z` to `C` is isomorphic to the
restriction of `N` placed in degree zero, then `Z` is isomorphic to `N` placed in degree zero,
in `D(C')`.

Nothing is carried.  Restriction of scalars is exact and faithful, so `Z` is concentrated in
degree zero (`Dualizing.isLE_of_isLE_restrictScalars`,
`Dualizing.isGE_of_isGE_restrictScalars`) and hence is a module in degree zero by the canonical
t-structure; the single-object functor is fully faithful, so that module is `C`-linearly
isomorphic to `N`; and surjectivity of `f` makes that isomorphism `C'`-linear
(`Dualizing.isoOfRestrictScalarsIso`).

Surjectivity is used only in the last step, and only there is it needed: for a general ring map
a `C`-linear isomorphism of `C'`-modules is not `C'`-linear. -/
theorem nonempty_iso_singleFunctor_of_restrictScalars (hf : Function.Surjective f)
    (Z : DerivedCategory (ModuleCat.{u} C')) (N : ModuleCat.{u} C')
    (e : (ModuleCat.restrictScalars f).mapDerivedCategory.obj Z ≅
      (ModuleCat.restrictScalars f).mapDerivedCategory.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} C') 0).obj N)) :
    Nonempty (Z ≅ (DerivedCategory.singleFunctor (ModuleCat.{u} C') 0).obj N) := by
  have eN : (ModuleCat.restrictScalars.{u} f).mapDerivedCategory.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} C') 0).obj N) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} C) 0).obj
        ((ModuleCat.restrictScalars.{u} f).obj N) :=
    ((ModuleCat.restrictScalars.{u} f).mapDerivedCategorySingleFunctor 0).app N
  have h1 : ((ModuleCat.restrictScalars.{u} f).mapDerivedCategory.obj Z).IsLE 0 :=
    DerivedCategory.TStructure.t.isLE_of_iso (e ≪≫ eN).symm 0
  have h2 : ((ModuleCat.restrictScalars.{u} f).mapDerivedCategory.obj Z).IsGE 0 :=
    DerivedCategory.TStructure.t.isGE_of_iso (e ≪≫ eN).symm 0
  have := isLE_of_isLE_restrictScalars f Z 0
  have := isGE_of_isGE_restrictScalars f Z 0
  obtain ⟨Y, ⟨eY⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE Z 0
  have eYN : (DerivedCategory.singleFunctor (ModuleCat.{u} C) 0).obj
        ((ModuleCat.restrictScalars.{u} f).obj Y) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} C) 0).obj
        ((ModuleCat.restrictScalars.{u} f).obj N) :=
    (((ModuleCat.restrictScalars.{u} f).mapDerivedCategorySingleFunctor 0).app Y).symm ≪≫
      (ModuleCat.restrictScalars.{u} f).mapDerivedCategory.mapIso eY.symm ≪≫ e ≪≫ eN
  exact ⟨eY ≪≫ (DerivedCategory.singleFunctor (ModuleCat.{u} C') 0).mapIso
    (isoOfRestrictScalarsIso f hf
      ((DerivedCategory.singleFunctor (ModuleCat.{u} C) 0).preimageIso eYN))⟩

end Derived

/-! ### The untwisted half of (★) in `D(C')` -/

section Untwisted

attribute [local instance 10000] HasDerivedCategory.standard

variable (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
  [Module.Flat R A] [Algebra.FinitePresentation R A] [Module.Flat A B]

/-- **The untwisted half of the isomorphism (★) of [stacks 0E2H], in `D(C')`.**  Let
`R → A → B` be flat of finite presentation and let `K_{A/R}` be a relative dualizing complex for
`R → A`.  Writing `C = B ⊗[R] B`, `C' = B ⊗[A] B` and `X = K_{A/R} ⊗ᴸ_A C`, derived Hom along the
surjection `Dualizing.diagonalQuotient : C → C'` carries `X` to `C'`:

`RHom_C(C', X) ≅ C'`,

an isomorphism of `D(C')`.  Nothing is carried beyond the hypotheses on `K_{A/R}`.

`Dualizing.nonempty_internalHom_diagonalQuotient_untwisted` is this statement in `D(C)` -- the
internal Hom of the single ring `C` out of `C'` -- and the two are the same statement read on
either side of `Dualizing.ProjectionFormula.restrictCoextendInternalHomIso` at
`Dualizing.diagonalQuotient`, which identifies restricted derived coextension of scalars with
that internal Hom.  So the content here is purely the descent, and
`Dualizing.nonempty_iso_singleFunctor_of_restrictScalars` performs it: the right-hand side is
the `C'`-module `C'` in degree zero, and `Dualizing.diagonalQuotient` is surjective. -/
theorem nonempty_diagonalQuotientDerivedHom_untwisted
    (KA : DerivedCategory (ModuleCat.{u} A))
    (hKA : IsRelativeDualizingComplex R A KA) :
    letI := diagonalAlgebra R A B
    letI := diagonalAlgebraSelf R A
    letI := diagonalQuotientAlgebra R A B
    letI := diagonalAlgebraQuot R A B
    letI := diagonalIsScalarTowerSelf R A B
    letI : Module.Flat R B := Module.Flat.trans R A B
    Nonempty
      ((derivedHom.{u, u, u} (diagonalQuotient R A B).toRingHom).obj
          ((diagonalDerivedExtension R B).obj
            ((totalDerivedExtensionScalars.{u, u, u} (algebraMap A B)).functor.obj KA)) ≅
        (DerivedCategory.singleFunctor (ModuleCat.{u} (B ⊗[A] B)) 0).obj
          (ModuleCat.of (B ⊗[A] B) (B ⊗[A] B))) := by
  let := diagonalAlgebra R A B
  let := diagonalAlgebraSelf R A
  let := diagonalQuotientAlgebra R A B
  let := diagonalAlgebraQuot R A B
  let := diagonalIsScalarTowerSelf R A B
  let : Module.Flat R B := Module.Flat.trans R A B
  have sg : (ModuleCat.restrictScalars.{u}
        (diagonalQuotient R A B).toRingHom).mapDerivedCategory.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} (B ⊗[A] B)) 0).obj
          (ModuleCat.of (B ⊗[A] B) (B ⊗[A] B))) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} (B ⊗[R] B)) 0).obj
        (ModuleCat.of (B ⊗[R] B) (B ⊗[A] B)) :=
    ((ModuleCat.restrictScalars.{u}
      (diagonalQuotient R A B).toRingHom).mapDerivedCategorySingleFunctor 0).app _
  have adjE : (totalDerivedExtensionScalars.{u, u, u}
        (diagonalQuotient R A B).toRingHom).functor ⊣
      (ModuleCat.restrictScalars.{u}
        (diagonalQuotient R A B).toRingHom).mapDerivedCategory :=
    @derivedExtensionScalarsAdjunction.{u, u, u} (B ⊗[R] B) (B ⊗[A] B) _ _ _ _ _
      (totalDerivedExtensionScalars.{u, u, u} (diagonalQuotient R A B).toRingHom).functor
      (totalDerivedExtensionScalars.{u, u, u} (diagonalQuotient R A B).toRingHom).comparison
      (totalDerivedExtensionScalars.{u, u, u} (diagonalQuotient R A B).toRingHom).isLeftDerived
  have ra : ProjectionFormula.restrictedAlgebra.{u, u}
        (ModuleCat.restrictScalars.{u}
          (diagonalQuotient R A B).toRingHom).mapDerivedCategory ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} (B ⊗[R] B)) 0).obj
        (ModuleCat.of (B ⊗[R] B) (B ⊗[A] B)) :=
    (ModuleCat.restrictScalars.{u}
      (diagonalQuotient R A B).toRingHom).mapDerivedCategory.mapIso
        (derivedTensorUnitIsoSingleSelf (B ⊗[A] B)) ≪≫ sg
  obtain ⟨uh⟩ := nonempty_internalHom_diagonalQuotient_untwisted R A B KA hKA
  refine nonempty_iso_singleFunctor_of_restrictScalars
    (diagonalQuotient R A B).toRingHom (surjective_diagonalQuotient R A B) _ _ ?_
  refine (ProjectionFormula.restrictCoextendInternalHomIso.{u, u}
      (diagonalQuotient R A B).toRingHom
      (totalDerivedExtensionScalars.{u, u, u} (diagonalQuotient R A B).toRingHom)
      (ModuleCat.restrictScalars.{u}
        (diagonalQuotient R A B).toRingHom).mapDerivedCategory
      (restrictScalarsDerived_adj_derivedHom.{u, u, u}
        (diagonalQuotient R A B).toRingHom).some adjE).app _ ≪≫ ?_
  exact (derivedHomAdjunctionOverRing (B ⊗[R] B)).hom.mapIso
      (ra.op.symm.prod (Iso.refl _)) ≪≫ uh ≪≫ sg.symm

omit [Algebra.FinitePresentation R A] in
/-- **Clause (2) of [stacks 0E2C] from a single-ring internal-Hom statement over `C`.**  Let
`R → A → B` be flat with `B` flat over `A`, write `C = B ⊗[R] B`, and let `K` be an object of
`D(B)`.  If the internal Hom of `D(C)` out of the diagonal `B` into `K ⊗ᴸ_B C` is the diagonal
`B`, then derived Hom from the diagonal of `R → B` carries `K ⊗ᴸ_B C` to `B[0]` -- which is
clause (2) of [stacks 0E2C] for `R → B` at `K`.

Nothing is carried.  The hypothesis is the conclusion read through
`Dualizing.ProjectionFormula.restrictCoextendInternalHomIso` at the diagonal
`Δ_{B/R} : C → B`, and the diagonal is surjective, so
`Dualizing.nonempty_iso_singleFunctor_of_restrictScalars` descends it; the right-hand side `B`
is a module in degree zero, which is what makes the descent available.

This replaces the `D(C')`-level hypothesis of
`Dualizing.diagonalDerivedHom_of_diagonalQuotientIso` by one in which no object of `D(B ⊗[A] B)`
and no derived Hom along a ring map occurs: clause (2) for a composite is equivalent to a
statement about the internal Hom of the single ring `C`.  It is *equivalent*, not weaker --
restriction along a surjection is faithful -- so it is not a weakening of [stacks 0E2H]. -/
theorem diagonalDerivedHom_of_internalHom_diagonal
    (K : DerivedCategory (ModuleCat.{u} B))
    (e : letI := diagonalAlgebraSelf R B
      letI : Module.Flat R B := Module.Flat.trans R A B
      (derivedHomAdjunctionOverRing (B ⊗[R] B)).hom.obj
          (Opposite.op ((DerivedCategory.singleFunctor (ModuleCat.{u} (B ⊗[R] B)) 0).obj
              (ModuleCat.of (B ⊗[R] B) B)),
            (diagonalDerivedExtension R B).obj K) ≅
        (DerivedCategory.singleFunctor (ModuleCat.{u} (B ⊗[R] B)) 0).obj
          (ModuleCat.of (B ⊗[R] B) B)) :
    letI : Module.Flat R B := Module.Flat.trans R A B
    Nonempty
      ((derivedHom.{u, u, u}
          (Algebra.TensorProduct.lmul' R (S := B)).toRingHom).obj
          ((diagonalDerivedExtension R B).obj K) ≅
        (DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).obj (ModuleCat.of B B)) := by
  let := diagonalAlgebraSelf R B
  let : Module.Flat R B := Module.Flat.trans R A B
  have hsurj : Function.Surjective
      (Algebra.TensorProduct.lmul' R (S := B)).toRingHom := fun b =>
    ⟨b ⊗ₜ[R] (1 : B), by simp⟩
  have sg : (ModuleCat.restrictScalars.{u}
        (Algebra.TensorProduct.lmul' R (S := B)).toRingHom).mapDerivedCategory.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).obj (ModuleCat.of B B)) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} (B ⊗[R] B)) 0).obj
        (ModuleCat.of (B ⊗[R] B) B) :=
    ((ModuleCat.restrictScalars.{u}
      (Algebra.TensorProduct.lmul' R (S := B)).toRingHom).mapDerivedCategorySingleFunctor 0).app _
  have adjE : (totalDerivedExtensionScalars.{u, u, u}
        (Algebra.TensorProduct.lmul' R (S := B)).toRingHom).functor ⊣
      (ModuleCat.restrictScalars.{u}
        (Algebra.TensorProduct.lmul' R (S := B)).toRingHom).mapDerivedCategory :=
    @derivedExtensionScalarsAdjunction.{u, u, u} (B ⊗[R] B) B _ _ _ _ _
      (totalDerivedExtensionScalars.{u, u, u}
        (Algebra.TensorProduct.lmul' R (S := B)).toRingHom).functor
      (totalDerivedExtensionScalars.{u, u, u}
        (Algebra.TensorProduct.lmul' R (S := B)).toRingHom).comparison
      (totalDerivedExtensionScalars.{u, u, u}
        (Algebra.TensorProduct.lmul' R (S := B)).toRingHom).isLeftDerived
  have ra : ProjectionFormula.restrictedAlgebra.{u, u}
        (ModuleCat.restrictScalars.{u}
          (Algebra.TensorProduct.lmul' R (S := B)).toRingHom).mapDerivedCategory ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} (B ⊗[R] B)) 0).obj
        (ModuleCat.of (B ⊗[R] B) B) :=
    (ModuleCat.restrictScalars.{u}
      (Algebra.TensorProduct.lmul' R (S := B)).toRingHom).mapDerivedCategory.mapIso
        (derivedTensorUnitIsoSingleSelf B) ≪≫ sg
  refine nonempty_iso_singleFunctor_of_restrictScalars
    (Algebra.TensorProduct.lmul' R (S := B)).toRingHom hsurj _ _ ?_
  refine (ProjectionFormula.restrictCoextendInternalHomIso.{u, u}
      (Algebra.TensorProduct.lmul' R (S := B)).toRingHom
      (totalDerivedExtensionScalars.{u, u, u}
        (Algebra.TensorProduct.lmul' R (S := B)).toRingHom)
      (ModuleCat.restrictScalars.{u}
        (Algebra.TensorProduct.lmul' R (S := B)).toRingHom).mapDerivedCategory
      (restrictScalarsDerived_adj_derivedHom.{u, u, u}
        (Algebra.TensorProduct.lmul' R (S := B)).toRingHom).some adjE).app _ ≪≫ ?_
  exact (derivedHomAdjunctionOverRing (B ⊗[R] B)).hom.mapIso
      (ra.op.symm.prod (Iso.refl _)) ≪≫ e ≪≫ sg.symm

end Untwisted

end

end Dualizing

end
