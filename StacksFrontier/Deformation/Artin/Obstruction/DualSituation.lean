module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.Artin.Infinitesimal
public import StacksFrontier.Deformation.Artin.Infinitesimal.TangentFunctor
public import StacksFrontier.Homology.Tor.DerivedTensorFunctorLargeUniverse

/-!
# A dual deformation situation

The dual notion of an obstruction theory presents the tangent and obstruction data of an
object `x` of a category fibred in groupoids by a single complex of `A`-modules. A *dual
deformation situation* consists of a complex `K` in the derived category of `A`, an
isomorphism of the tangent functor `T_x(-)` with `H^1(K ⊗^L_A -)`, and, for every
deformation situation `(x, A' → A)` with kernel `I`, an obstruction element of
`H^2(K ⊗^L_A I)` which is functorial in the deformation situation and vanishes exactly when
`x` lifts to `Spec A'`.

## Main definitions

* `Deformation.Artin.derivedCohomology` — the cohomology of the derived tensor product with
  `K` in a fixed degree, as a functor of the module.
* `Deformation.Artin.SquareZeroThickening` — a square-zero thickening of `Spec A` in the
  site, with the arrow to it inside the big fppf site over `S`, and
  `Deformation.Artin.SquareZeroThickening.Hom` a morphism of such with its induced map of
  kernels.
* `Deformation.Artin.DualDeformationSituation` — the data and the three conditions of the
  source's situation.

## Implementation notes

The complex is represented by an object of the derived category, and cohomology in degree
`n` is the value of the derived homology functor in degree `n` on the derived tensor product.
Naturality of the obstructions is expressed with an explicit map of kernels, specified
pointwise, which avoids choosing a lift of scalars. The chosen big fppf site makes explicit
the site that the source leaves implicit, and the thickened algebra carries the witness that
its spectrum occurs in that site, since otherwise the category of lifts is not defined.

The kernel of the thickening carries its canonical module structure over the quotient ring,
`Stacks.Smooth.kerModule`, so that the obstruction lives in the cohomology of
`K ⊗^L_A I` as an `A`-module. The existence of a lift is `Nonempty` applied to the fibre of
`Under.post p` over the arrow of the thickening, which is the category of lifts of `x`.

Infinitesimal automorphisms could be incorporated as well; following the source they are
left out, which is what makes the resulting criterion sharpest.

## References

* [Stacks Project, Tag 07YX](https://stacks.math.columbia.edu/tag/07YX)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace Deformation.Artin

universe u v w

attribute [local instance] HasDerivedCategory.standard

/-- The cohomology of the derived tensor product of `K` with a module, in degree `n`. -/
public abbrev derivedCohomology (A : Type u) [CommRing A]
    (K : DerivedCategory (ModuleCat.{u} A)) (n : ℤ) :
    ModuleCat.{u} A ⥤ ModuleCat.{u} A :=
  DerivedCategory.singleFunctor (ModuleCat.{u} A) 0 ⋙
    CochainComplex.DerivedTensor.derivedTensorProduct K ⋙
    DerivedCategory.homologyFunctor (ModuleCat.{u} A) n

/-- A square-zero thickening of `Spec A` over `S`, represented in the big fppf site. -/
public structure SquareZeroThickening (A : Type u) [CommRing A] (B : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) (toS : Spec (.of A) ⟶ S)
    (hA : B.Contains (Spec (.of A))) (A' : Type u) [CommRing A'] where
  /-- The surjection `A' → A`. -/
  q : A' →+* A
  /-- It is a square-zero surjection. -/
  squareZeroSurjection : IsDeformationSituation q
  /-- The spectrum of `A'` occurs in the chosen big fppf site. -/
  hA' : B.Contains (Spec (.of A'))
  /-- Its structure morphism to the base, inside the site. -/
  toS' : B.obj hA' ⟶ B.obj hS
  /-- The closed immersion `Spec A ⟶ Spec A'` over `S`. -/
  arrow : algebraOver A B S hS toS hA ⟶ (Over.mk toS' : BigFppfOver B S hS)
  /-- It is the morphism of spectra determined by `q`. -/
  arrow_spec : B.inclusion.map arrow.left = Spec.map (CommRingCat.ofHom q)

/-! ### Realising an algebraic square-zero extension as a thickening in the site -/

section OfTower

variable (Λ A : Type u) [CommRing Λ] [CommRing A] [Algebra Λ A] (B : BigFppfSite.{u})
  (S : Scheme.{u}) (hS : B.Contains S) (toS : Spec (.of A) ⟶ S)
  (hA : B.Contains (Spec (.of A))) (baseMap : Spec (.of Λ) ⟶ S)
  (hbase : Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ baseMap = toS)
  (A' : Type u) [CommRing A'] [Algebra Λ A'] [Algebra A' A] [IsScalarTower Λ A' A]
  (hA' : B.Contains (Spec (.of A')))

/-- The structure morphism of `Spec A'` to the base, for a `Λ`-algebra `A'` whose base is
reached through the chosen affine open `Spec Λ ⟶ S`. -/
public def towerToBase : B.obj hA' ⟶ B.obj hS :=
  ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (algebraMap Λ A')) ≫ baseMap)

include hbase in
/-- **The square-zero thickening attached to an algebraic one.** A surjection `A' → A` of
`Λ`-algebras with square-zero kernel, whose spectrum lies in the site, is a square-zero
thickening of `Spec A` over `S` in the sense of Stacks 07YX.

The structure morphism of `Spec A'` is the one through the chosen affine open `Spec Λ ⟶ S`;
the closed immersion `Spec A ⟶ Spec A'` lies over `S` because the tower `Λ → A' → A`
commutes, which is `IsScalarTower.algebraMap_eq`. This is the form in which the extension of
Stacks 07YL meets condition (iii) of Stacks 07YX: that tag produces exactly a square-zero
surjection of `Λ`-algebras, and nothing in the site is determined by it beyond the size bound
`Deformation.Artin.contains_spec_of_surjective_of_mk_ker_le` supplies. -/
public def squareZeroThickeningOfTower
    (hsurj : Function.Surjective (algebraMap A' A))
    (hsq : RingHom.ker (algebraMap A' A) ^ 2 = ⊥) :
    SquareZeroThickening A B S hS toS hA A' where
  q := algebraMap A' A
  squareZeroSurjection := ⟨hsurj, hsq⟩
  hA' := hA'
  toS' := towerToBase Λ B S hS baseMap A' hA'
  arrow := by
    refine Over.homMk (ObjectProperty.homMk
      (Spec.map (CommRingCat.ofHom (algebraMap A' A))) : B.obj hA ⟶ B.obj hA') ?_
    apply ObjectProperty.hom_ext
    change Spec.map (CommRingCat.ofHom (algebraMap A' A)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap Λ A')) ≫ baseMap = toS
    rw [← Category.assoc, ← Spec.map_comp, ← hbase, ← CommRingCat.ofHom_comp,
      ← IsScalarTower.algebraMap_eq]
  arrow_spec := rfl

end OfTower

/-- The kernel of a square-zero thickening, with its canonical module structure over the
quotient. -/
public abbrev SquareZeroThickening.kernel {A : Type u} [CommRing A] {B : BigFppfSite.{u}}
    {S : Scheme.{u}} {hS : B.Contains S} {toS : Spec (.of A) ⟶ S}
    {hA : B.Contains (Spec (.of A))} {A' : Type u} [CommRing A']
    (D : SquareZeroThickening A B S hS toS hA A') : ModuleCat.{u} A :=
  letI := Stacks.Smooth.kerModule D.squareZeroSurjection.1 D.squareZeroSurjection.2
  ModuleCat.of A (RingHom.ker D.q)

/-- A morphism of square-zero thickenings over the fixed base, together with the map on
kernels it necessarily induces. -/
public structure SquareZeroThickening.Hom {A : Type u} [CommRing A] {B : BigFppfSite.{u}}
    {S : Scheme.{u}} {hS : B.Contains S} {toS : Spec (.of A) ⟶ S}
    {hA : B.Contains (Spec (.of A))} {A₁ A₂ : Type u} [CommRing A₁] [CommRing A₂]
    (D₁ : SquareZeroThickening A B S hS toS hA A₁)
    (D₂ : SquareZeroThickening A B S hS toS hA A₂) where
  /-- The map of thickened algebras. -/
  ringHom : A₁ →+* A₂
  /-- It lies over the identity of `A`. -/
  overBase : D₂.q.comp ringHom = D₁.q
  /-- It is a map over the base scheme. -/
  overS : Spec.map (CommRingCat.ofHom ringHom) ≫ B.inclusion.map D₁.toS' =
    B.inclusion.map D₂.toS'
  /-- The induced map of kernels. -/
  kernelMap : D₁.kernel ⟶ D₂.kernel
  /-- It is the restriction of the map of thickened algebras. -/
  kernelMap_spec : ∀ i : RingHom.ker D₁.q, (kernelMap i).1 = ringHom i.1

/-- **Stacks 07YX.** A dual deformation situation: a complex `K` of `A`-modules whose first
derived-tensor cohomology is the tangent functor of `x`, together with obstruction elements
in its second derived-tensor cohomology which are functorial in the deformation situation and
vanish exactly when `x` lifts. -/
@[stacks 07YX]
public structure DualDeformationSituation (A Λ : Type u) [CommRing A] [CommRing Λ]
    [Algebra Λ A] (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    [IsLocallyNoetherian S] (toS : Spec (.of A) ⟶ S) (hA : B.Contains (Spec (.of A)))
    (X : Type v) [Category.{w} X] (p : X ⥤ BigFppfOver B S hS) where
  /-- `A` is of finite type over `Λ`. -/
  finiteType : Algebra.FiniteType Λ A
  /-- The affine open of `S` that `Spec A` maps into. -/
  affineOpen : Spec (.of Λ) ⟶ S
  /-- It is an open immersion. -/
  openImmersion : IsOpenImmersion affineOpen
  /-- The structure morphism of `Spec A` factors through it. -/
  factorization : Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ affineOpen = toS
  /-- The object of the fibred category. -/
  x : X
  /-- It lies over `Spec A`. -/
  hx : p.obj x = algebraOver A B S hS toS hA
  /-- The ambient category is fibred in groupoids. -/
  fibered : p.IsFiberedInGroupoids
  /-- It satisfies the Rim–Schlessinger condition (RS*). -/
  rsStar : SatisfiesRSStar B S hS p fibered
  /-- The complex controlling the deformation theory of `x`. -/
  K : DerivedCategory (ModuleCat.{u} A)
  /-- Clause (2): the transformation `T_x(-) → H^1(K ⊗^L_A -)`. -/
  tangentMap : ∀ M : SiteModule A B,
    ((tangentFunctor A B S hS toS hA p x hx fibered rsStar).functor.obj M : Type _) →ₗ[A]
      ((derivedCohomology A K 1).obj M.obj : Type _)
  /-- Condition (i): it is an isomorphism. -/
  tangentBijective : ∀ M, Function.Bijective (tangentMap M)
  /-- It is a transformation of functors. -/
  tangentNatural : ∀ {M N : SiteModule A B} (f : M ⟶ N)
    (z : (tangentFunctor A B S hS toS hA p x hx fibered rsStar).functor.obj M),
    tangentMap N
        ((tangentFunctor A B S hS toS hA p x hx fibered rsStar).functor.map f z) =
      (derivedCohomology A K 1).map f.hom (tangentMap M z)
  /-- Clause (3): the obstruction element of a deformation situation. -/
  obstruction : ∀ (A' : Type u) [CommRing A'] (D : SquareZeroThickening A B S hS toS hA A'),
    (derivedCohomology A K 2).obj D.kernel
  /-- Condition (ii): obstruction elements are carried to obstruction elements. -/
  obstructionNatural : ∀ (A₁ A₂ : Type u) [CommRing A₁] [CommRing A₂]
    (D₁ : SquareZeroThickening A B S hS toS hA A₁)
    (D₂ : SquareZeroThickening A B S hS toS hA A₂) (f : SquareZeroThickening.Hom D₁ D₂),
    ((derivedCohomology A K 2).map f.kernelMap) (obstruction A₁ D₁) = obstruction A₂ D₂
  /-- Condition (iii): the obstruction vanishes exactly when a lift exists. -/
  obstruction_iff_lift : ∀ (A' : Type u) [CommRing A']
    (D : SquareZeroThickening A B S hS toS hA A'),
    Nonempty ((Under.post p).Fiber (Under.mk (eqToHom hx ≫ D.arrow))) ↔
      obstruction A' D = 0

end Deformation.Artin
