module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPresentationExact
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraTotalSections
public import StacksFrontier.AlgebraicGeometry.ClosedPushforward.Basic
public import StacksFrontier.AlgebraicGeometry.ConormalSequenceRight.Middle
public import StacksFrontier.AlgebraicGeometry.DeRham.DerivedDirectImage
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.EquationWedge
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.FractionClassMap
public import StacksCore.Tactic.StacksAttribute

/-!
# The Gysin map of a family of equations

Let `π : X ⟶ S` be a morphism of schemes, let `f₁, …, f_c ∈ Γ(X, 𝒪_X)` and let `i : Z ⟶ X` be the
closed subscheme they cut out. The **Gysin map**

`γ^p_{f₁, …, f_c} : Ω^p_{Z/S} ⟶ ℋ ᶜ_Z(Ω^{p+c}_{X/S})`

sends a local `p`-form `ω` on `Z` that is the restriction of a `p`-form `ω̃` on `X` to

`γ^p(ω) = c_{f₁, …, f_c}(ω̃|_Z) ∧ d f₁ ∧ ⋯ ∧ d f_c`,

where `c_{f₁, …, f_c}` is the canonical map into the local cohomology sheaf and `ℋ ᶜ_Z` is the
degree-`c` local cohomology sheaf of the common zero locus of the equations. The content of the
construction is that the right-hand side does not depend on the lift `ω̃`.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.exactOneFormSection` and
  `AlgebraicGeometry.Scheme.Hom.exactFormWedgeHom`: the exact one-form `d b` of a global function
  as a global section of `Ω^1_{X/S}`, and right multiplication by it.
* `AlgebraicGeometry.Scheme.Hom.formFractionClass`: the class of the fraction
  `ω̃ / (f₁ ⋯ f_c)` in the local cohomology sheaf, for `ω̃` a local differential form.
* `AlgebraicGeometry.Scheme.Hom.gysinFormulaHom`: the right-hand side of the Gysin formula, as a
  morphism out of `Ω^p_{X/S}`.
* `AlgebraicGeometry.Scheme.Hom.formRestriction`: restriction of relative differential forms to a
  subscheme.
* `AlgebraicGeometry.Scheme.Hom.FormKernelGeneratedByEquations`: the description of the kernel of
  that restriction by the equations and their differentials.
* `AlgebraicGeometry.Scheme.Hom.gysinMapOfFormKernel`: **the Gysin map**, granted that
  description of the kernel. The unconditional form, for the closed subscheme actually cut out by
  the equations, is `AlgebraicGeometry.Scheme.Hom.gysinMap` of
  `StacksFrontier.AlgebraicGeometry.DeRham.Gysin.GysinMapCutOut`, which carries
  [Stacks, Tag 0G83].

## Main results

* `SheafOfModules.GradedAlgebra.mul_generator_mul_prodDegOne_eq_zero`: an ordered wedge of
  degree-one generators with a repeated factor vanishes, after multiplication by an arbitrary
  homogeneous section.
* `AlgebraicGeometry.Scheme.Hom.epi_relativeDifferentialFormsMap`: the canonical map
  `i^*Ω^p_{X/S} ⟶ Ω^p_{Z/S}` of an immersion is an epimorphism.
* `AlgebraicGeometry.Scheme.Hom.epi_formRestriction`: restriction of `p`-forms to a closed
  subscheme is an epimorphism.
* `AlgebraicGeometry.Scheme.Hom.smulHom_comp_gysinFormulaHom` and
  `AlgebraicGeometry.Scheme.Hom.exactFormWedgeHom_comp_gysinFormulaHom`: the two vanishings that
  make the Gysin map well defined — the right-hand side of the formula kills `f_j ω'` and
  `ω'' ∧ d f_j`.
* `AlgebraicGeometry.Scheme.Hom.formRestriction_comp_gysinMapOfFormKernel`: the Gysin formula,
  which characterises the Gysin map.
* `AlgebraicGeometry.Scheme.Hom.formKernelGeneratedByEquations_of_mono` and
  `AlgebraicGeometry.Scheme.Hom.formKernelGeneratedByEquations_of_isUnit`: two cases in which the
  description of the kernel of restriction holds — when restriction is injective, and when one of
  the equations is invertible.

## Implementation notes

Both sheaves of the Gysin map live on the space of `Z`, and both are read here through the direct
image on `X`: the source as `i_*Ω^p_{Z/S}` along the closed immersion, the target as the direct
image of `ℋ ᶜ_Z(Ω^{p+c}_{X/S})` along the inclusion of the closed subset, which is the shape the
canonical map of [Stacks, Tag 0G7Q] is available in. Nothing is lost: both direct images are
faithful functors, by `Stacks.ClosedImmersion.faithful_pushforward` and by
`faithful_modulePushforward` of
`RingedSpaceModuleAdjunction.ClosedQuotientMorphismOfRingedSpaces`.
The two sheaves are *not* direct images of the same functor, and they cannot be: the target is a
sheaf of `i⁻¹𝒪_X`-modules which is not annihilated by the equations — already for one equation on
the affine line the degree-one local cohomology of the structure sheaf has invertible
multiplication by the equation — so the Gysin map is a map of `i⁻¹𝒪_X`-modules and not of
`𝒪_Z`-modules.

The number `c` of equations is an arbitrary natural number, as in the source. This is the
generality of the canonical map `c_{f₁, …, f_c}` of
`Stacks.Perfect.FractionClass.fractionClass`, whose construction divides by the product of the
equations — the empty product being `1`, so that for `c = 0` the fraction is the section itself
and the top term of the extended alternating Čech complex is its degree-zero term. The exterior
degree `p` is a natural number, so that the quasi-coherence of `Ω^{p+c}_{X/S}` is available; the
auxiliary constructions are stated for an arbitrary integer degree.

**The vanishing of a wedge with a repeated factor** is proved by passing to the ring of all local
sections of `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraTotalSections`. There the
graded multiplication becomes an ordinary associative multiplication, the degree-one generators
generate a copy of the exterior algebra of the module of sections, and Mathlib's
`ExteriorAlgebra.ι_mul_prod_list` applies; the identity is transported back along the injectivity
of `DirectSum.of`. No degree transport appears, which is why the statement is about the ordered
wedge with the repeated factor on the *right* of the moving form: the only reassociation needed is
the one `DirectSum` performs for free.

`FormKernelGeneratedByEquations` is an explicit hypothesis of `gysinMapOfFormKernel`, not an
input proved here. It asserts that the kernel of `Ω^p_{X/S} ⟶ i_*Ω^p_{Z/S}` is generated by the
sections `∑ f_j ω'_j + ∑ ω''_j ∧ d f_j`, which is the conjunction of exactness at the middle term
of the conormal sequence of [Stacks, Tag 01UZ] with the exterior clause of
[Stacks, Tag 01CJ]. Both are available, and the comparison carrying the resulting statement about
`⋀^p(i^*Ω_{X/S})` back to `Ω^p_{X/S}` on `X` is supplied in
`StacksFrontier.AlgebraicGeometry.DeRham.Gysin.GysinMapCutOut`, which therefore *proves* the
description for the closed subscheme cut out by the equations and carries
[Stacks, Tag 0G83]. The hypothesis is kept here so that the construction stays available at the
generality of an arbitrary `i : Z ⟶ X` satisfying it, which is the generality the projection
formula of [Stacks, Tag 0G8C] is stated in. The tagged [Stacks, Tag 0G8A] does *not* assume it:
`Stacks.DeRham.CohomologicalGysin.equationGysinHodgeMap` takes the hypothesis of Tag 0G83 that
the equations cut out `Z` and derives the description from it. Everything else the construction
needs is proved here: the two vanishings, the surjectivity of restriction, and the descent
itself.

## References

* [Stacks Project, Tag 0G83](https://stacks.math.columbia.edu/tag/0G83)
* [Stacks Project, Tag 0G7Q](https://stacks.math.columbia.edu/tag/0G7Q)
* [Stacks Project, Tag 01UZ](https://stacks.math.columbia.edu/tag/01UZ)
* [Stacks Project, Tag 01CJ](https://stacks.math.columbia.edu/tag/01CJ)
* [Stacks Project, Tag 08KS](https://stacks.math.columbia.edu/tag/08KS)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.SupportedComplexes
open Stacks.Perfect.CechDerivedSupport (equationsClosedSet isClosed_equationsClosedSet)

universe u

attribute [local instance] SheafOfModules.GradedAlgebra.sectionsGOne
  SheafOfModules.GradedAlgebra.sectionsGMul SheafOfModules.GradedAlgebra.sectionsGRing

namespace SheafOfModules.GradedAlgebra

variable {C : Type*} [Category* C] {J : GrothendieckTopology C} {R : Sheaf J RingCat}

/-- The ordered product of `n` degree-one local sections, read in the ring of all local sections,
is the product of the corresponding degree-one summands. -/
theorem of_prodDegOne (A : SheafOfModules.GradedAlgebra R) (U : Cᵒᵖ) (n : ℕ)
    (z : Fin n → (A.piece 1).val.obj U) :
    DirectSum.of (A.sectionsPiece U) (n : ℤ) (A.prodDegOne U n z) =
      (List.ofFn fun j => DirectSum.of (A.sectionsPiece U) 1 (z j)).prod := by
  induction n with
  | zero => simp only [List.ofFn_zero, List.prod_nil]; rfl
  | succ n ih =>
      rw [List.ofFn_succ', List.prod_concat, ← ih (fun i => z i.castSucc)]
      exact (A.of_mul_of_eq U (n : ℤ) 1 _ (z (Fin.last n))).symm

/-- **A wedge of degree-one generators with a repeated factor vanishes, after multiplication by
an arbitrary homogeneous section.** For a square-zero degree-one generator `ι` and a family `g`
of local sections, the product `ω · ι(g j) · (ι(g 0) ⋯ ι(g (n-1)))` is zero. -/
theorem mul_generator_mul_prodDegOne_eq_zero {A : SheafOfModules.GradedAlgebra R}
    {M : SheafOfModules R} {ι : M ⟶ A.piece 1} (hι : SquareZero ι) (U : Cᵒᵖ) (p : ℤ)
    (ω : (A.piece p).val.obj U) {n : ℕ} (g : Fin n → M.val.obj U) (j : Fin n) :
    (A.mul (p + 1) (n : ℤ)).app U
        ((A.mul p 1).app U ω (ι.val.app U (g j)))
        (A.prodDegOne U n fun k => ι.val.app U (g k)) = 0 := by
  refine DirectSum.of_injective (β := A.sectionsPiece U) (p + 1 + (n : ℤ)) ?_
  rw [map_zero, ← A.of_mul_of_eq U (p + 1) (n : ℤ), ← A.of_mul_of_eq U p 1, _root_.mul_assoc,
    A.of_prodDegOne U n, of_generator_mul_listProd_eq_zero hι U g j, mul_zero]

end SheafOfModules.GradedAlgebra

namespace AlgebraicGeometry.Scheme.Hom

variable {X S : Scheme.{u}}

/-! ### Reassociation helpers -/

/-- A composite with a vanishing left factor vanishes. -/
private theorem comp_left_eq_zero {C : Type*} [Category* C] [Limits.HasZeroMorphisms C]
    {A B D E : C} {a : A ⟶ B}
    {b : B ⟶ D} (h : a ≫ b = 0) (c : D ⟶ E) : a ≫ b ≫ c = 0 := by
  rw [← Category.assoc, h, zero_comp]

/-- A four-fold composite whose first three factors compose to zero vanishes. -/
private theorem comp4_eq_zero {C : Type*} [Category* C] [Limits.HasZeroMorphisms C]
    {A B D E F : C} {a : A ⟶ B} {b : B ⟶ D}
    {c : D ⟶ E} (h : a ≫ b ≫ c = 0) (e : E ⟶ F) : a ≫ b ≫ c ≫ e = 0 := by
  have hassoc : a ≫ b ≫ c ≫ e = (a ≫ b ≫ c) ≫ e := by
    rw [Category.assoc a (b ≫ c) e, Category.assoc b c e]
  rw [hassoc, h, zero_comp]

/-- A composite `s ≫ w ≫ φ` vanishes when `s` commutes past `w` into an endomorphism killed by
`φ`. -/
private theorem comp_comp_eq_zero_of_comm {C : Type*} [Category* C] [Limits.HasZeroMorphisms C]
    {A B T : C} {s : A ⟶ A}
    {w : A ⟶ B} {s' : B ⟶ B} {φ : B ⟶ T} (hcomm : s ≫ w = w ≫ s') (hz : s' ≫ φ = 0) :
    s ≫ w ≫ φ = 0 := by
  rw [← Category.assoc, hcomm, Category.assoc, hz, comp_zero]

/-- The relative differential `d b` of a global function, as a global section of `Ω^1_{X/S}`. -/
def exactOneFormSection (π : X ⟶ S) (b : Γ(X, ⊤)) :
    (relativeDifferentialForms π 1).sections :=
  PresheafOfModules.sectionsMk
    (fun U => exactOneForm π U (X.presheaf.map (homOfLE (le_top : U.unop ≤ ⊤)).op b))
    (fun {U V} h => by
      refine (exactOneForm_map π h _).trans (congrArg (exactOneForm π V) ?_)
      have hmor : (homOfLE (le_top : V.unop ≤ ⊤)) = h.unop ≫ homOfLE (le_top : U.unop ≤ ⊤) :=
        Subsingleton.elim _ _
      have happ := congrArg (fun g : V.unop ⟶ (⊤ : X.Opens) => (X.presheaf.map g.op).hom b) hmor
      simpa only [op_comp, Quiver.Hom.op_unop, Functor.map_comp, ConcreteCategory.comp_apply]
        using happ.symm)

/-- The value of the global section `d b` over an open is the exact one-form of the restriction
of `b` to that open. -/
@[simp]
theorem exactOneFormSection_eval (π : X ⟶ S) (b : Γ(X, ⊤)) (U : X.Opensᵒᵖ) :
    (exactOneFormSection π b).eval U =
      exactOneForm π U (X.presheaf.map (homOfLE (le_top : U.unop ≤ ⊤)).op b) :=
  rfl

/-- Right multiplication by the exact one-form `d b` of a global function, as a morphism
`Ω^p_{X/S} ⟶ Ω^{p+1}_{X/S}` of sheaves of modules. -/
def exactFormWedgeHom (π : X ⟶ S) (b : Γ(X, ⊤)) (p : ℤ) :
    relativeDifferentialForms π p ⟶ relativeDifferentialForms π (p + 1) :=
  (relativeDifferentialFormsAlgebra π).rightMul p 1 (exactOneFormSection π b)

/-- On a local section `ω` of `Ω^p_{X/S}`, right multiplication by `d b` is the wedge of `ω` with
the exact one-form of the restriction of `b`. -/
@[simp]
theorem exactFormWedgeHom_app_apply (π : X ⟶ S) (b : Γ(X, ⊤)) (p : ℤ) (U : X.Opensᵒᵖ)
    (ω : (relativeDifferentialForms π p).val.obj U) :
    (exactFormWedgeHom π b p).val.app U ω =
      ((relativeDifferentialFormsAlgebra π).mul p 1).app U ω
        (exactOneForm π U (X.presheaf.map (homOfLE (le_top : U.unop ≤ ⊤)).op b)) :=
  rfl

/-- **The wedge with the differential of one of the equations is annihilated by the Gysin wedge
factor.** Wedging a `p`-form with `d f_j` and then with `d f₁ ∧ ⋯ ∧ d f_c` gives zero, because the
resulting ordered wedge of degree-one forms repeats the factor `d f_j`. -/
theorem exactFormWedgeHom_comp_gysinWedgeHom (π : X ⟶ S) {c : ℕ} (f : Fin c → Γ(X, ⊤)) (p : ℤ)
    (j : Fin c) :
    exactFormWedgeHom π (f j) p ≫ gysinWedgeHom π f (p + 1) = 0 := by
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U =>
    ModuleCat.hom_ext (LinearMap.ext fun ω => ?_))
  exact SheafOfModules.GradedAlgebra.mul_generator_mul_prodDegOne_eq_zero
    (A := relativeDifferentialFormsAlgebra π)
    (ι := Scheme.Modules.exteriorGenerator (relativeDifferentials π))
    (Scheme.Modules.isExteriorAlgebra_exteriorAlgebra (relativeDifferentials π)).1 U p ω
    (fun k => (universalRelativeDerivation π).d
      (X.presheaf.map (homOfLE (le_top : U.unop ≤ ⊤)).op (f k))) j

/-! ### Surjectivity of the canonical map on differential forms along an immersion -/

variable {Z : Scheme.{u}}

/-- **The canonical comparison of exterior algebras is an epimorphism in each degree** for an
immersion `i : Z ⟶ X` over `S`. The canonical map on relative differentials is an epimorphism by
[Stacks, Tag 01UZ], and the exterior power of an epimorphism is an epimorphism by the exterior
surjectivity clause of [Stacks, Tag 01CJ]. -/
theorem epi_relativeDifferentialFormsComparison_app (i : Z ⟶ X) [IsImmersion i] (π : X ⟶ S)
    (hcomm : i ≫ π = (i ≫ π) ≫ 𝟙 S) (m : ℕ) :
    Epi ((relativeDifferentialFormsComparison i π (i ≫ π) (𝟙 S) hcomm).app (m : ℤ)) :=
  @SheafOfModules.ExtPresentation.epi_extDesc_app _ _ _ _ _ _
    (Scheme.Modules.exteriorGenerator ((Scheme.Modules.pullback i).obj (relativeDifferentials π)))
    (Scheme.Modules.exteriorGenerator (relativeDifferentials (i ≫ π)))
    (Scheme.Modules.isExteriorAlgebra_exteriorAlgebra _)
    (Scheme.Modules.isExteriorAlgebra_exteriorAlgebra _)
    (relativeDifferentialsMap i π (i ≫ π) (𝟙 S) hcomm)
    (Stacks.ConormalSequenceRight.differentialsMapOver_epi i π) m

/-- **The canonical map `i^*Ω^p_{X/S} ⟶ Ω^p_{Z/S}` is an epimorphism** for an immersion
`i : Z ⟶ X` over `S`, in every nonnegative degree. It is the comparison of [Stacks, Tag 01CI],
which is an isomorphism, followed by the degree-`p` component of the comparison of exterior
algebras, which is an epimorphism. -/
theorem epi_relativeDifferentialFormsMap (i : Z ⟶ X) [IsImmersion i] (π : X ⟶ S)
    (hcomm : i ≫ π = (i ≫ π) ≫ 𝟙 S) (m : ℕ) :
    Epi (relativeDifferentialFormsMap i π (i ≫ π) (𝟙 S) hcomm (m : ℤ)) :=
  epi_comp' (@IsIso.epi_of_iso _ _ _ _ _ (Iso.isIso_hom _))
    (epi_relativeDifferentialFormsComparison_app i π hcomm m)

/-- `Ω^{p+m}_{X/S}` is quasi-coherent, in the degree spelling `(p : ℤ) + (m : ℤ)` in which the
codomain of the Gysin map appears. -/
instance isQuasicoherent_relativeDifferentialForms_natCast_add (π : X ⟶ S) (p m : ℕ) :
    (relativeDifferentialForms π ((p : ℤ) + (m : ℤ))).IsQuasicoherent :=
  isQuasicoherent_relativeDifferentialForms π (p + m)

/-! ### The fraction class of a differential form -/

section FractionClass

attribute [local instance] HasDerivedCategory.standard

/-- The direct image on `X` of the degree-`c` local cohomology sheaf `ℋ^c_Z(ℱ)` along the common
zero locus `Z` of the equations `f₁, …, f_c`. -/
abbrev pushforwardLocalCohomology {X : Scheme.{u}} {c : ℕ} (f : Fin c → Γ(X, ⊤))
    (F : X.Modules) : X.Modules :=
  (modulePushforward (closedSubsetInclusion X.toRingedSpace (equationsClosedSet f))).obj
    (localCohomologySheafOfComplex X.toRingedSpace (equationsClosedSet f)
      (isClosed_equationsClosedSet f) (c : ℤ)
      ((DerivedCategory.singleFunctor X.Modules 0).obj F))

/-- **The fraction class of a relative differential form.** The map carrying a local `d`-form `ω̃`
to the class of the fraction `ω̃ / (f₁ ⋯ f_c)` in `i_* ℋ^c_Z(Ω^d_{X/S})`: the projection onto the
quotient by the equations, followed by the canonical map `c_{f₁, …, f_c}` of [Stacks, Tag 0G7Q]
read through the adjunction. -/
def formFractionClass (π : X ⟶ S) {c : ℕ} (f : Fin c → Γ(X, ⊤)) (d : ℤ)
    [(relativeDifferentialForms π d).IsQuasicoherent] :
    relativeDifferentialForms π d ⟶
      pushforwardLocalCohomology f (relativeDifferentialForms π d) :=
  cokernel.π (Stacks.Perfect.FractionClass.equationsMap f (relativeDifferentialForms π d)) ≫
    Stacks.Perfect.FractionClass.pushforwardFractionClass f (relativeDifferentialForms π d)

/-- **A multiple of an equation has vanishing fraction class.** Multiplying the numerator of the
fraction by one of the equations makes it a boundary in the extended alternating Čech complex,
by [Stacks, Tag 0G7Q]. -/
theorem smulHom_comp_formFractionClass (π : X ⟶ S) {c : ℕ} (f : Fin c → Γ(X, ⊤)) (d : ℤ)
    [(relativeDifferentialForms π d).IsQuasicoherent] (j : Fin c) :
    Stacks.Perfect.FractionClass.smulHom (f j) (relativeDifferentialForms π d) ≫
        formFractionClass π f d = 0 := by
  have h1 : Stacks.Perfect.FractionClass.smulHom (f j) (relativeDifferentialForms π d) ≫
      cokernel.π
          (Stacks.Perfect.FractionClass.equationsMap f (relativeDifferentialForms π d)) ≫
        Stacks.Perfect.FractionClass.quotientClassMapData f
          (relativeDifferentialForms π d) = 0 := by
    rw [Stacks.Perfect.FractionClass.cokernelπ_comp_quotientClassMapData]
    exact comp_left_eq_zero
      (Stacks.Perfect.FractionClass.smulHom_comp_classMap f (relativeDifferentialForms π d) j) _
  exact comp4_eq_zero h1 _

/-- **The Gysin formula.** The map carrying a local `d`-form `ω̃` on `X` to
`c_{f₁, …, f_c}(ω̃|_Z) ∧ d f₁ ∧ ⋯ ∧ d f_c`: wedge with the differentials of the equations, then
take the fraction class. -/
def gysinFormulaHom (π : X ⟶ S) {c : ℕ} (f : Fin c → Γ(X, ⊤)) (d : ℤ)
    [(relativeDifferentialForms π (d + (c : ℤ))).IsQuasicoherent] :
    relativeDifferentialForms π d ⟶
      pushforwardLocalCohomology f (relativeDifferentialForms π (d + (c : ℤ))) :=
  gysinWedgeHom π f d ≫ formFractionClass π f (d + (c : ℤ))

/-- **The Gysin formula kills multiples of the equations.** Replacing the lift `ω̃` by
`ω̃ + f_j ω'` does not change the value, because the fraction class of a multiple of an equation
vanishes and wedging commutes with multiplication by a global function. -/
theorem smulHom_comp_gysinFormulaHom (π : X ⟶ S) {c : ℕ} (f : Fin c → Γ(X, ⊤)) (d : ℤ)
    [(relativeDifferentialForms π (d + (c : ℤ))).IsQuasicoherent] (j : Fin c) :
    Stacks.Perfect.FractionClass.smulHom (f j) (relativeDifferentialForms π d) ≫
        gysinFormulaHom π f d = 0 :=
  comp_comp_eq_zero_of_comm
    (Stacks.Perfect.FractionClass.smulHom_naturality (f j) (gysinWedgeHom π f d))
    (smulHom_comp_formFractionClass π f (d + (c : ℤ)) j)

/-- **The Gysin formula kills wedges with the differentials of the equations.** Replacing the
lift `ω̃` by `ω̃ + ω'' ∧ d f_j` does not change the value, because the ordered wedge
`ω'' ∧ d f_j ∧ d f₁ ∧ ⋯ ∧ d f_c` repeats the degree-one factor `d f_j` and so vanishes. -/
theorem exactFormWedgeHom_comp_gysinFormulaHom (π : X ⟶ S) {c : ℕ} (f : Fin c → Γ(X, ⊤))
    (q : ℤ) [(relativeDifferentialForms π (q + 1 + (c : ℤ))).IsQuasicoherent]
    (j : Fin c) :
    exactFormWedgeHom π (f j) q ≫ gysinFormulaHom π f (q + 1) = 0 :=
  comp_left_eq_zero (exactFormWedgeHom_comp_gysinWedgeHom π f q j) _

/-! ### The Gysin map -/

/-- **Restriction of relative differential forms to a subscheme.** The transpose under
`i^* ⊣ i_*` of the canonical map `i^*Ω^d_{X/S} ⟶ Ω^d_{Z/S}` of [Stacks, Tag 01UV]: it carries a
local `d`-form `ω̃` on `X` to its restriction `ω̃|_Z`. -/
def formRestriction (i : Z ⟶ X) (π : X ⟶ S) (d : ℤ) :
    relativeDifferentialForms π d ⟶
      (Scheme.Modules.pushforward i).obj (relativeDifferentialForms (i ≫ π) d) :=
  (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app (relativeDifferentialForms π d) ≫
    (Scheme.Modules.pushforward i).map
      (relativeDifferentialFormsMap i π (i ≫ π) (𝟙 S) (by simp) d)

/-- **Restriction of `p`-forms to a closed subscheme is surjective.** The canonical map
`ℱ ⟶ i_*i^*ℱ` is an epimorphism along a closed immersion, by [Stacks, Tag 08KS], and the
canonical map `i^*Ω^p_{X/S} ⟶ Ω^p_{Z/S}` is an epimorphism which stays one after pushforward,
again by [Stacks, Tag 08KS]. -/
theorem epi_formRestriction (i : Z ⟶ X) [IsClosedImmersion i] (π : X ⟶ S) (p : ℕ) :
    Epi (formRestriction i π (p : ℤ)) :=
  epi_comp' (Stacks.ClosedImmersion.epi_unit_app i (relativeDifferentialForms π (p : ℤ)))
    (@Functor.PreservesEpimorphisms.preserves _ _ _ _ _
      (Stacks.ClosedImmersion.preservesEpimorphisms_modulePushforward_of_isClosedImmersion i)
      _ _ _ (epi_relativeDifferentialFormsMap i π (by simp) p))

/-- **The ambiguity in the lift of a form from the subscheme**, as an elimination principle: a
morphism out of `Ω^d_{X/S}` which kills every multiple `f_j ω'` of an equation and every wedge
`ω'' ∧ d f_j` with the differential of an equation kills the kernel of restriction to `Z`.

This is the statement that the kernel of `Ω^d_{X/S} ⟶ i_*Ω^d_{Z/S}` is generated by the sections
of the shape `∑ f_j ω'_j + ∑ ω''_j ∧ d f_j`, which is what [Stacks, Tag 0G83] appeals to; the
source writes the second family as `∑ d(f_j) ∧ ω''_j`, the same submodule by graded
commutativity of the wedge product. It is the conjunction of exactness at the middle term of the
conormal sequence of [Stacks, Tag 01UZ] with the exterior clause of [Stacks, Tag 01CJ], and so
is expected to hold whenever `Z` is cut out by the equations, once the comparison carrying the
exterior statement from `⋀^p(i^*Ω_{X/S})` to `Ω^p_{X/S}` is available. It is satisfiable:
`formKernelGeneratedByEquations_of_mono` and `formKernelGeneratedByEquations_of_isUnit` are two
cases in which it holds. -/
def FormKernelGeneratedByEquations (i : Z ⟶ X) (π : X ⟶ S) {c : ℕ} (f : Fin c → Γ(X, ⊤))
    (d : ℤ) : Prop :=
  ∀ {T : X.Modules} (ψ : relativeDifferentialForms π d ⟶ T),
    (∀ j, Stacks.Perfect.FractionClass.smulHom (f j) (relativeDifferentialForms π d) ≫ ψ = 0) →
    (∀ (q : ℤ) (hq : q + 1 = d) (j),
      exactFormWedgeHom π (f j) q ≫
        eqToHom (congrArg (relativeDifferentialForms π) hq) ≫ ψ = 0) →
    kernel.ι (formRestriction i π d) ≫ ψ = 0

/-- **The kernel description holds when restriction is injective.** The kernel of a
monomorphism vanishes, so the conclusion is vacuous: every morphism kills it. -/
theorem formKernelGeneratedByEquations_of_mono (i : Z ⟶ X) (π : X ⟶ S) {c : ℕ}
    (f : Fin c → Γ(X, ⊤)) (d : ℤ) (hmono : Mono (formRestriction i π d)) :
    FormKernelGeneratedByEquations i π f d := by
  intro T ψ _ _
  have hk : kernel.ι (formRestriction i π d) = 0 :=
    hmono.right_cancellation _ 0 (by rw [kernel.condition, zero_comp])
  rw [hk, zero_comp]

/-- **The kernel description holds when one of the equations is invertible.** Multiplication by
an invertible global function is an isomorphism of every module, so a morphism killing it is
itself zero. The common zero locus of the equations is then empty, and this is the degenerate
case of the description; it witnesses that the hypothesis of `gysinMap` is satisfiable. -/
theorem formKernelGeneratedByEquations_of_isUnit (i : Z ⟶ X) (π : X ⟶ S) {c : ℕ}
    (f : Fin c → Γ(X, ⊤)) (d : ℤ) {j : Fin c} (hj : IsUnit (f j)) :
    FormKernelGeneratedByEquations i π f d := by
  intro T ψ hsmul _
  obtain ⟨v, hv⟩ := hj.exists_right_inv
  have key : Stacks.Perfect.FractionClass.smulHom v (relativeDifferentialForms π d) ≫
      (Stacks.Perfect.FractionClass.smulHom (f j) (relativeDifferentialForms π d) ≫ ψ) = 0 := by
    rw [hsmul j, comp_zero]
  rw [← Category.assoc, ← Stacks.Perfect.FractionClass.smulHom_mul, mul_comm, hv,
    Stacks.Perfect.FractionClass.smulHom_one, Category.id_comp] at key
  rw [key, comp_zero]

/-- The Gysin formula kills a wedge with the differential of an equation, read in the target
degree through the identification of `Ω^{q+1}_{X/S}` with `Ω^d_{X/S}` for `q + 1 = d`. -/
theorem exactFormWedgeHom_eqToHom_comp_gysinFormulaHom (π : X ⟶ S) {c : ℕ}
    (f : Fin c → Γ(X, ⊤)) {q d : ℤ} (hq : q + 1 = d)
    [(relativeDifferentialForms π (d + (c : ℤ))).IsQuasicoherent] (j : Fin c) :
    exactFormWedgeHom π (f j) q ≫
        eqToHom (congrArg (relativeDifferentialForms π) hq) ≫ gysinFormulaHom π f d = 0 := by
  subst hq
  simpa using exactFormWedgeHom_comp_gysinFormulaHom π f q j

/-- **The Gysin map of a family of equations, granted a description of the kernel of restriction
of `p`-forms.** Let `π : X ⟶ S` be a morphism of schemes, let `f₁, …, f_c ∈ Γ(X, 𝒪_X)`, and let
`i : Z ⟶ X` be a closed immersion. The Gysin map

`γ^p_{f₁, …, f_c} : Ω^p_{Z/S} ⟶ ℋ^c_Z(Ω^{p+c}_{X/S})`

is the unique morphism whose value on the restriction `ω̃|_Z` of a local `p`-form `ω̃` on `X` is
`c_{f₁, …, f_c}(ω̃|_Z) ∧ d f₁ ∧ ⋯ ∧ d f_c`. Both sheaves are read on `X` through the direct image
along `i`, which is faithful; `ℋ^c_Z` is the local cohomology sheaf and `c_{f₁, …, f_c}` the
canonical map of [Stacks, Tag 0G7Q].

**The content is well-definedness**, that is, independence of the chosen lift `ω̃`: the map
`gysinFormulaHom` kills the kernel of restriction to `Z`, because a lift is determined up to
`∑ f_j ω'_j + ∑ ω''_j ∧ d f_j` and both kinds of term go to zero — the first by
`smulHom_comp_gysinFormulaHom`, the second by `exactFormWedgeHom_comp_gysinFormulaHom`. The map
is then the descent of `gysinFormulaHom` along the epimorphism `formRestriction`, taken
constructively with `CategoryTheory.Abelian.epiDesc`.

`hker` is the description of the kernel of restriction recorded in
`FormKernelGeneratedByEquations`, a hypothesis of this declaration rather than an input proved
here. For the closed subscheme actually cut out by `f₁, …, f_c` it holds, by
`formKernelGeneratedByEquations_of_isCutOutByEquations` of
`StacksFrontier.AlgebraicGeometry.DeRham.Gysin.GysinMapCutOut`, and the resulting unconditional
construction — which is the Gysin map of [Stacks, Tag 0G83] — is
`AlgebraicGeometry.Scheme.Hom.gysinMap` there. This general form is kept because it assumes
nothing about `Z` beyond that description, which is the generality the projection formula of
[Stacks, Tag 0G8C] is stated in; the tagged [Stacks, Tag 0G8A] is built from `gysinMap` and
assumes no kernel description. -/
def gysinMapOfFormKernel (i : Z ⟶ X) [IsClosedImmersion i] (π : X ⟶ S) {c : ℕ}
    (f : Fin c → Γ(X, ⊤)) (p : ℕ)
    [(relativeDifferentialForms π ((p : ℤ) + (c : ℤ))).IsQuasicoherent]
    (hker : FormKernelGeneratedByEquations i π f (p : ℤ)) :
    (Scheme.Modules.pushforward i).obj (relativeDifferentialForms (i ≫ π) (p : ℤ)) ⟶
      pushforwardLocalCohomology f
        (relativeDifferentialForms π ((p : ℤ) + (c : ℤ))) :=
  @Abelian.epiDesc _ _ _ _ _ (formRestriction i π (p : ℤ))
    (epi_formRestriction i π p) _ (gysinFormulaHom π f (p : ℤ))
    (hker (gysinFormulaHom π f (p : ℤ)) (fun j => smulHom_comp_gysinFormulaHom π f (p : ℤ) j)
      (fun _q hq j => exactFormWedgeHom_eqToHom_comp_gysinFormulaHom π f hq j))

/-- **The formula for the Gysin map, granted a description of the kernel of restriction of
`p`-forms.** On the restriction `ω̃|_Z` of a local `p`-form `ω̃` on `X`, the Gysin map takes the
value `c_{f₁, …, f_c}(ω̃|_Z) ∧ d f₁ ∧ ⋯ ∧ d f_c`. This is the equation of the source, and it
determines `gysinMapOfFormKernel` because restriction to `Z` is an epimorphism. The
unconditional form, for the closed subscheme actually cut out by the equations, is
`AlgebraicGeometry.Scheme.Hom.formRestriction_comp_gysinMap` of
`StacksFrontier.AlgebraicGeometry.DeRham.Gysin.GysinMapCutOut`. -/
theorem formRestriction_comp_gysinMapOfFormKernel (i : Z ⟶ X) [IsClosedImmersion i]
    (π : X ⟶ S) {c : ℕ} (f : Fin c → Γ(X, ⊤)) (p : ℕ)
    [(relativeDifferentialForms π ((p : ℤ) + (c : ℤ))).IsQuasicoherent]
    (hker : FormKernelGeneratedByEquations i π f (p : ℤ)) :
    formRestriction i π (p : ℤ) ≫ gysinMapOfFormKernel i π f p hker =
      gysinFormulaHom π f (p : ℤ) :=
  @Abelian.comp_epiDesc _ _ _ _ _ (formRestriction i π (p : ℤ))
    (epi_formRestriction i π p) _ (gysinFormulaHom π f (p : ℤ)) _

end FractionClass

end AlgebraicGeometry.Scheme.Hom

end
