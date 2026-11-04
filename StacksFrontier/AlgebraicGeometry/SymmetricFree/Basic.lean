module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SectionwiseExteriorSymmetricAlgebra
public import StacksFrontier.LinearAlgebra.SymmetricPower.FreePresentation
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricAlgebraConstruction.Sectionwise

/-!
# Symmetric powers of a free presheaf of modules

Tag 00DN says that every symmetric power of a free module is free. For the sheaf-theoretic
clause (6) of Tag 01CK, and for the free terms of the presentation sequences of Tag 01CJ, what
is needed is the *presheaf* statement: the degree-`n` sectionwise symmetric power of a presheaf
of modules whose sections are free on a fixed index set, compatibly with restriction, is again
such a presheaf — on the degree-`n` monomials in that index set.

The content is a **naturality** statement, and it is the part Mathlib does not have.
`SymPow.basisSymmetricPower` gives, for each basis `b` of a module `M` over a commutative ring
`R`, a basis of `Symⁿ_R(M)` indexed by the degree-`n` monomials; what this file adds is that
those bases are compatible with base change: for a ring homomorphism `φ : R →+* S` and a
`φ`-semilinear map `u : M →ₛₗ[φ] N` matching two bases index by index, the induced semilinear
map on symmetric powers matches the two monomial bases index by index
(`Stacks.SymmetricFree.symMapₛₗ_basisSymmetricPower`).

## Main definitions

* `Stacks.SymmetricFree.SectionwiseBasis Q I`: a basis of the sections of a presheaf of modules
  `Q` over every object of the site, indexed by one fixed type `I` and compatible with the
  restriction maps. Such data is the same thing as an isomorphism of `Q` with the free presheaf
  of modules on the constant presheaf `I`, which is what
  `Stacks.SymmetricFree.SectionwiseBasis.isoFreeObj` produces.
* `Stacks.SymmetricFree.SectionwiseBasis.symPowInt`: **the sectionwise symmetric
  powers of such a presheaf again have one**, indexed by the degree-`n` monomials. This is Tag
  00DN at the level of presheaves of modules.

## Main results

* `Stacks.SymmetricFree.repr_mapₛₗ`: a semilinear map matching two bases index by index
  transports coordinates along the ring homomorphism.
* `Stacks.SymmetricFree.equivMvPolynomial_mapₛₗ`: **`SymmetricAlgebra.equivMvPolynomial` is
  natural in the ring**, along `MvPolynomial.map`.
* `Stacks.SymmetricFree.symMapₛₗ_basisSymmetricPower` and `repr_symMapₛₗ`: the monomial bases of
  the symmetric powers are compatible with semilinear base change.

## Implementation notes

**Why the naturality is not available.** Mathlib has no functoriality of `SymmetricAlgebra`
whatsoever — not in the module variable with the ring fixed, and a fortiori not along a ring
homomorphism. `SymmetricAlgebra.mapₛₗ` of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricPowerSheafification` supplies the
semilinear base change as a *ring homomorphism*, which is what makes the naturality of
`equivMvPolynomial` an application of `SymmetricAlgebra.ringHom_ext`: both composites are ring
homomorphisms out of `SymmetricAlgebra R M`, so they agree as soon as they agree on the image of
the base ring and on the degree-one generators, and on a degree-one generator the comparison is
exactly `Stacks.SymmetricFree.repr_mapₛₗ`.

**No `@[stacks]` tag.** Tag 00DN is a statement about modules and is already formalized as
`SymPow.free_symmetricPower`; nothing here is that statement, and the sheaf-level form lives in
`StacksDraft.AlgebraicGeometry.F3b.SymmetricFree.Sheaf`.

## References

* [Stacks Project, Tag 00DN](https://stacks.math.columbia.edu/tag/00DN)
* [Stacks Project, Tag 01CJ](https://stacks.math.columbia.edu/tag/01CJ)
* [Stacks Project, Tag 01CK](https://stacks.math.columbia.edu/tag/01CK)
-/

@[expose] public section

open CategoryTheory Opposite Module PresheafOfModules

universe v u w

namespace Stacks.SymmetricFree

/-! ### Coordinates along a ring homomorphism -/

section Coordinates

variable {R S : Type*} [Semiring R] [Semiring S] (φ : R →+* S)
  {M : Type*} [AddCommMonoid M] [Module R M] {N : Type*} [AddCommMonoid N] [Module S N]
  {κ : Type*}

/-- **A semilinear map matching two bases index by index transports coordinates along the ring
homomorphism.** -/
theorem repr_mapₛₗ (u : M →ₛₗ[φ] N) (b : Basis κ R M) (c : Basis κ S N)
    (h : ∀ i, u (b i) = c i) (m : M) :
    c.repr (u m) = Finsupp.mapRange φ (map_zero φ) (b.repr m) :=
  congrArg (fun g : M →ₛₗ[φ] (κ →₀ S) => g m)
    (b.ext (f₁ := c.repr.toLinearMap.comp u)
      (f₂ := (Finsupp.mapRange.linearMap φ.toSemilinearMap).comp b.repr.toLinearMap)
      fun i => by simp [h i])

end Coordinates

/-! ### Naturality of the monomial basis of a symmetric power -/

section Monomials

variable {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
  {M : Type*} [AddCommGroup M] [Module R M] {N : Type*} [AddCommGroup N] [Module S N]
  {κ : Type*}

/-- `SymmetricAlgebra.equivMvPolynomial` on a degree-one generator is the linear form the basis
gives, read in the variables of the polynomial ring. -/
theorem equivMvPolynomial_ι (b : Basis κ R M) (m : M) :
    SymmetricAlgebra.equivMvPolynomial b (SymmetricAlgebra.ι R M m) =
      b.constr R (MvPolynomial.X (R := R)) m := by
  simp [SymmetricAlgebra.equivMvPolynomial]

/-- **`SymmetricAlgebra.equivMvPolynomial` is natural in the ring.** A `φ`-semilinear map
matching two bases index by index induces, on the symmetric algebras, the coefficientwise map
`MvPolynomial.map φ` of the polynomial rings on that index set. -/
theorem equivMvPolynomial_mapₛₗ (u : M →ₛₗ[φ] N) (b : Basis κ R M) (c : Basis κ S N)
    (h : ∀ i, u (b i) = c i) (x : SymmetricAlgebra R M) :
    SymmetricAlgebra.equivMvPolynomial c (SymmetricAlgebra.mapₛₗ φ u x) =
      MvPolynomial.map φ (SymmetricAlgebra.equivMvPolynomial b x) := by
  have key : (SymmetricAlgebra.equivMvPolynomial c).toAlgHom.toRingHom.comp
        (SymmetricAlgebra.mapₛₗ φ u) =
      (MvPolynomial.map φ).comp
        (SymmetricAlgebra.equivMvPolynomial b).toAlgHom.toRingHom := by
    refine SymmetricAlgebra.ringHom_ext (fun r => by simp) fun m => ?_
    simp only [RingHom.comp_apply, SymmetricAlgebra.mapₛₗ_ι]
    change SymmetricAlgebra.equivMvPolynomial c (SymmetricAlgebra.ι S N (u m)) =
      MvPolynomial.map φ (SymmetricAlgebra.equivMvPolynomial b (SymmetricAlgebra.ι R M m))
    rw [equivMvPolynomial_ι, equivMvPolynomial_ι, Basis.constr_apply, Basis.constr_apply,
      repr_mapₛₗ φ u b c h m, Finsupp.sum_mapRange_index (fun a => by simp),
      Finsupp.sum, Finsupp.sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [MvPolynomial.smul_eq_C_mul]
  exact congrFun (congrArg (fun g : SymmetricAlgebra R M →+* MvPolynomial κ S => g.toFun) key) x

/-- `SymPow.symmetricPowerEquivHomogeneousSubmodule` is `SymmetricAlgebra.equivMvPolynomial` on
the underlying elements of the symmetric algebra. -/
theorem coe_symmetricPowerEquivHomogeneousSubmodule (b : Basis κ R M) (n : ℕ)
    (x : SymPow.symmetricPower n R M) :
    ((SymPow.symmetricPowerEquivHomogeneousSubmodule b n x :
        MvPolynomial.homogeneousSubmodule κ R n) : MvPolynomial κ R) =
      SymmetricAlgebra.equivMvPolynomial b (x : SymmetricAlgebra R M) := rfl

/-- The coordinates of a local section of a symmetric power in the monomial basis are the
coefficients of the corresponding polynomial. -/
theorem basisSymmetricPower_repr_apply (b : Basis κ R M) (n : ℕ)
    (x : SymPow.symmetricPower n R M) (d : {d : κ →₀ ℕ | Finsupp.degree d = n}) :
    (SymPow.basisSymmetricPower b n).repr x d =
      MvPolynomial.coeff (d : κ →₀ ℕ)
        (SymmetricAlgebra.equivMvPolynomial b (x : SymmetricAlgebra R M)) := by
  simp [SymPow.basisSymmetricPower, MvPolynomial.basisHomogeneousSubmodule,
    MvPolynomial.homogeneousSubmoduleEquivFinsupp, coe_symmetricPowerEquivHomogeneousSubmodule]
  rfl

/-- **Base change of a symmetric power transports monomial coordinates along the ring
homomorphism.** -/
theorem repr_symMapₛₗ (u : M →ₛₗ[φ] N) (b : Basis κ R M) (c : Basis κ S N)
    (h : ∀ i, u (b i) = c i) (n : ℕ) (x : SymPow.symmetricPower n R M) :
    (SymPow.basisSymmetricPower c n).repr (SymPow.symMapₛₗ n φ u x) =
      Finsupp.mapRange φ (map_zero φ) ((SymPow.basisSymmetricPower b n).repr x) := by
  ext d
  rw [Finsupp.mapRange_apply, basisSymmetricPower_repr_apply, basisSymmetricPower_repr_apply,
    SymPow.symMapₛₗ_coe, equivMvPolynomial_mapₛₗ φ u b c h, MvPolynomial.coeff_map]

/-- **The monomial bases of the symmetric powers are matched index by index** by the base change
of a semilinear map that matches two bases index by index. This is the naturality that Tag 00DN
needs in order to become a statement about presheaves and sheaves of modules rather than about
modules. -/
theorem symMapₛₗ_basisSymmetricPower (u : M →ₛₗ[φ] N) (b : Basis κ R M) (c : Basis κ S N)
    (h : ∀ i, u (b i) = c i) (n : ℕ) (d : {d : κ →₀ ℕ | Finsupp.degree d = n}) :
    SymPow.symMapₛₗ n φ u (SymPow.basisSymmetricPower b n d) =
      SymPow.basisSymmetricPower c n d :=
  (SymPow.basisSymmetricPower c n).repr.injective (by
    rw [repr_symMapₛₗ φ u b c h, Basis.repr_self, Basis.repr_self, Finsupp.mapRange_single,
      map_one])

end Monomials

/-! ### Presheaves of modules with a basis compatible with restriction -/

section Sectionwise

variable {C : Type u} [Category.{v} C] {R : Cᵒᵖ ⥤ RingCat.{w}}

/-- **The restriction maps of the free presheaf of modules on a constant presheaf of types fix
the tautological basis of its sections.** -/
theorem freeObj_const_restrictₛₗ_single (I : Type w) {X Y : Cᵒᵖ} (f : X ⟶ Y) (i : I)
    (r : R.obj X) :
    (freeObj (R := R) ((Functor.const Cᵒᵖ).obj I)).restrictₛₗ f (Finsupp.single i r) =
      Finsupp.single i ((R.map f).hom r) := by
  change (Finsupp.single i r).sum
      (fun j c => (R.map f).hom c • (Finsupp.single j 1 : I →₀ R.obj Y)) =
    Finsupp.single i ((R.map f).hom r)
  rw [Finsupp.sum_single_index (by simp)]
  simp [Finsupp.smul_single]

/-- **A basis of the sections of a presheaf of modules over every object of the site, indexed by
one fixed type and compatible with the restriction maps.** Equivalently, an isomorphism of `Q`
with the free presheaf of modules on the constant presheaf of types `I`; see
`Stacks.SymmetricFree.SectionwiseBasis.isoFreeObj`. -/
structure SectionwiseBasis (Q : PresheafOfModules.{w} R) (I : Type w) where
  /-- the basis of the sections over each object of the site -/
  basis (X : Cᵒᵖ) : Basis I (R.obj X) (Q.obj X)
  /-- the bases are matched index by index by the restriction maps -/
  restrictₛₗ_basis {X Y : Cᵒᵖ} (f : X ⟶ Y) (i : I) :
    Q.restrictₛₗ f (basis X i) = basis Y i

namespace SectionwiseBasis

variable {Q : PresheafOfModules.{w} R} {I : Type w} (hQ : SectionwiseBasis Q I)

/-- The coordinates of a `Stacks.SymmetricFree.SectionwiseBasis` commute with restriction. -/
theorem repr_restrictₛₗ {X Y : Cᵒᵖ} (f : X ⟶ Y) (x : Q.obj X) :
    (hQ.basis Y).repr (Q.restrictₛₗ f x) =
      Finsupp.mapRange (R.map f).hom (map_zero _) ((hQ.basis X).repr x) :=
  repr_mapₛₗ _ (Q.restrictₛₗ f) (hQ.basis X) (hQ.basis Y) (hQ.restrictₛₗ_basis f) x

/-- **A presheaf of modules with a `Stacks.SymmetricFree.SectionwiseBasis` indexed by `I` is the
free presheaf of modules on the constant presheaf of types `I`.** -/
noncomputable def isoFreeObj : Q ≅ freeObj ((Functor.const Cᵒᵖ).obj I) :=
  isoMk (fun X => (hQ.basis X).repr.toModuleIso) fun {X Y} f =>
    ModuleCat.hom_ext (Basis.ext (b := hQ.basis X) fun i => by
      change (hQ.basis Y).repr (Q.restrictₛₗ f (hQ.basis X i)) =
        (freeObj (R := R) ((Functor.const Cᵒᵖ).obj I)).restrictₛₗ f
          ((hQ.basis X).repr (hQ.basis X i))
      rw [hQ.restrictₛₗ_basis f i, Basis.repr_self, Basis.repr_self,
        freeObj_const_restrictₛₗ_single, map_one])

end SectionwiseBasis

/-- The free presheaf of modules on a constant presheaf of types has the tautological
`Stacks.SymmetricFree.SectionwiseBasis`. -/
noncomputable def freeObjSectionwiseBasis (I : Type w) :
    SectionwiseBasis (freeObj (R := R) ((Functor.const Cᵒᵖ).obj I)) I where
  basis _ := Finsupp.basisSingleOne
  restrictₛₗ_basis f i := by
    change (freeObj (R := R) ((Functor.const Cᵒᵖ).obj I)).restrictₛₗ f (Finsupp.single i 1) =
      Finsupp.single i 1
    rw [freeObj_const_restrictₛₗ_single, map_one]

end Sectionwise

/-! ### The sectionwise symmetric powers of a free presheaf of modules -/

section Symmetric

variable {C : Type u} [Category.{v} C] {O : Cᵒᵖ ⥤ CommRingCat.{w}}
  {Q : PresheafOfModules.{w} (O ⋙ forget₂ _ RingCat)} {I : Type w}

/-- **Tag 00DN for presheaves of modules: a presheaf of modules whose sections are free on a
fixed index set, compatibly with restriction, has sectionwise symmetric powers of the same
shape**, on the degree-`n` monomials in that index set. -/
noncomputable def SectionwiseBasis.symPowInt (hQ : SectionwiseBasis Q I) (n : ℕ) :
    SectionwiseBasis (PresheafOfModules.symPowInt.{v, u, w, w} (n : ℤ) Q)
      {d : I →₀ ℕ | Finsupp.degree d = n} where
  basis X := SymPow.basisSymmetricPower (hQ.basis X) n
  restrictₛₗ_basis {X Y} f d :=
    Subtype.ext (congrArg Subtype.val
      (symMapₛₗ_basisSymmetricPower ((O ⋙ forget₂ _ RingCat).map f).hom (Q.restrictₛₗ f)
        (hQ.basis X) (hQ.basis Y) (hQ.restrictₛₗ_basis f) n d))

end Symmetric

end Stacks.SymmetricFree

end
