module

public import StacksFrontier.RingTheory.Dualizing.MapDerivedCategory
public import StacksFrontier.Algebra.Category.ModuleCat.ExtendScalarsBaseRing
public import StacksFrontier.RingTheory.Dualizing.RelativeCoprojections
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.Composition
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.FlatBaseChangeIso
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.Independence
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.RelativeDualizingFiniteTorDimension
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.RelativePerfection
import StacksFrontier.RingTheory.Dualizing.UpperShriek.PolynomialEvalDualityProof

/-!
# The relative dualizing complex of the Noetherian theory is a relative dualizing complex

Let `φ : R → A` be a flat homomorphism of finite type of Noetherian rings.  There are two
notions of *relative dualizing complex* for `φ`, and this file proves that the first is an
instance of the second.

**The Noetherian one.**  `ω^•_{A/R} = φ^!(R)`, the value of the algebraic upper shriek functor
at the base ring placed in cohomological degree zero.  Upper shriek is read at a polynomial
presentation `p` of `φ`, as everywhere in `StacksDraft.RingTheory.Dualizing.UpperShriek`, so
`ω^•_{A/R}` is the object
`p.upperShriekFunctor.obj (R[0]) = RHom_P(A, R ⊗_R^L P)[n]` for `P = R[x_1, …, x_n] ↠ A`.

**The general one.**  `Dualizing.IsRelativeDualizingComplex`: for a flat ring map `R → A` of
finite presentation, an object `K` of `D(A)` is a relative dualizing complex when
1. `K` is perfect relative to `R`, and
2. `RHom_{A ⊗_R A}(A, K ⊗_A^L (A ⊗_R A))` is isomorphic to `A` in degree zero, the base change
   being taken along the left coprojection and derived Hom from the diagonal being the derived
   coextension of scalars along the multiplication map `A ⊗_R A → A`.

Condition (1) for `ω^•_{A/R}` is [stacks 0BZW] (2)(a),
`Dualizing.PolynomialPresentation.relativeDualizingComplex_isRelativelyPerfect`, already in the
library.  Condition (2) is proved here, and the two are assembled.

## Main definitions

There are no new definitions.

## Main results

* `Dualizing.PolynomialPresentation.relativeDualizingComplex_diagonalDerivedHom` —
  **the diagonal condition** for `ω^•_{A/R}`, which is condition (2) above.
* `Dualizing.PolynomialPresentation.relativeDualizingComplex_isRelativeDualizingComplex` —
  **[stacks 0E2E]**: `ω^•_{A/R}` is a relative dualizing complex in the general sense, at every
  polynomial presentation of `φ`, with nothing carried.
* `Dualizing.PolynomialPresentation.relativeDualizingComplex_diagonalDerivedHom_of_flat` and
  `Dualizing.PolynomialPresentation.relativeDualizingComplex_isRelativeDualizingComplex_of_flat`
  — the same two statements for `φ` flat, by the earlier route through [stacks 0BZV]; they
  carry nothing either, are subsumed and keep no tag.

## Implementation notes

### The proof of the diagonal condition

Write `B = A ⊗_R A`, let `p₁, p₂ : A → B` be the coprojections and `Δ : B → A` the
multiplication map.  The source argument is: base change for the relative dualizing complex at
`R' = A` identifies `ω^•_{A/R} ⊗_{A, p₁}^L B` with `p₂^!(A)`; derived Hom from the diagonal is
`Δ^!`, because `Δ` is surjective; and `Δ^! ∘ p₂^! = (Δ ∘ p₂)^! = id^!` is the identity.

Three turns of that argument are different here.

*The base change is taken along the right coprojection, not the left.*  Flat base change,
[stacks 0BZN], is stated in this library as `φ^!(K) ⊗_A^L A' ≅ (φ')^!(K ⊗_R^L R')` with
`A' = R' ⊗_R A`, so at `R' = A` and `K = R` the derived base change is along `includeRight` and
the target is upper shriek of `includeLeft` at `R ⊗_R^L A = A`.  That is the mirror image of the
source's labelling and costs nothing: the diagonal condition is symmetric in the two
coprojections, which is `Dualizing.derivedHomIncludeRightIso`, and that isomorphism is what
converts the result back into the left-coprojection form the definition is written with.  The
flat base change is read at the degreewise model `Dualizing.flatDerivedExtension` of derived
extension of scalars, and is compared with the total model `derivedHomIncludeRightIso` is
written with by uniqueness of left derived functors.

*Derived Hom from the diagonal is already `Δ^!`.*  The source needs the definition of `Δ^!` from
Section 0BZI together with [stacks 0A71] to recognise `RHom_{B}(A, -)`, an object of `D(B)`, as
an object of `D(A)`.  The definition of a relative dualizing complex in this library is written
with `Dualizing.derivedHom`, which lands in `D(A)` to begin with, so the identification needed is
`Dualizing.upperShriekFunctor_ofSurjective_iso_derivedHom`, which is [stacks 0C0G] for a
surjection and is unconditional.

*The last step is `(Δ ∘ p₂)^! ≅ id`.*  The composition
isomorphism is [stacks 0BZT] for a surjective second map,
`Dualizing.upperShriekFunctor_comp_ofSurjective`, which is unconditional; but the presentation of
`Δ ∘ p₂ = id_A` that it produces is the base-changed presentation followed by `Δ`, which has `n`
variables, not none.  Comparing it with the presentation with no variables — where upper shriek is
`RHom_A(A, -)`, the identity — is [stacks 0BZJ], whose one input is supplied in the proof by
`Dualizing.polynomialEvalDuality`.

### What is carried

Nothing, in `Dualizing.PolynomialPresentation.relativeDualizingComplex_diagonalDerivedHom` and
`Dualizing.PolynomialPresentation.relativeDualizingComplex_isRelativeDualizingComplex`.  Flat base
change [stacks 0BZN] (`Dualizing.PolynomialPresentation.isIso_upperShriekFlatBaseChange_app`),
relative perfection [stacks 0BZW] (2)(a)
(`Dualizing.PolynomialPresentation.relativeDualizingComplex_isRelativelyPerfect`) and the one input
of [stacks 0BZJ] (`Dualizing.polynomialEvalDuality`) are all proved.

The earlier statements
`Dualizing.PolynomialPresentation.relativeDualizingComplex_diagonalDerivedHom_of_flat` and
`Dualizing.PolynomialPresentation.relativeDualizingComplex_isRelativeDualizingComplex_of_flat`
reach the same conclusions for `φ` flat through the Tor-independent base change [stacks 0BZV],
and carry nothing either.  They are kept for their callers and are subsumed.

## References

* [Stacks Project, Tag 0E2E](https://stacks.math.columbia.edu/tag/0E2E)
* [Stacks Project, Tag 0E2C](https://stacks.math.columbia.edu/tag/0E2C)
* [Stacks Project, Tag 0BZV](https://stacks.math.columbia.edu/tag/0BZV)
* [Stacks Project, Tag 0BZT](https://stacks.math.columbia.edu/tag/0BZT)
* [Stacks Project, Tag 0BZJ](https://stacks.math.columbia.edu/tag/0BZJ)
* [Stacks Project, Tag 0C0G](https://stacks.math.columbia.edu/tag/0C0G)
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped TensorProduct
open CochainComplex.DerivedExtensionScalars

-- the added import of `…UpperShriek.PolynomialEvalDualityProof` brings further
-- `HasDerivedCategory` instances into scope, so the standard one is given priority
attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace Dualizing

namespace DiagonalCondition

/-- Restriction of scalars is exact, hence preserves finite limits; this is needed for the
functor it induces on derived categories to be defined. -/
local instance restrictScalars_preservesFiniteLimits {X Y : Type u} [Ring X] [Ring Y]
    (g : X →+* Y) : Limits.PreservesFiniteLimits (ModuleCat.restrictScalars.{u} g) := by
  constructor
  intro J _ _
  constructor
  intro F
  infer_instance

/-- Restriction of scalars is exact, hence preserves finite colimits; this is needed for the
functor it induces on derived categories to be defined. -/
local instance restrictScalars_preservesFiniteColimits {X Y : Type u} [Ring X] [Ring Y]
    (g : X →+* Y) : Limits.PreservesFiniteColimits (ModuleCat.restrictScalars.{u} g) := by
  constructor
  intro J _ _
  constructor
  intro F
  infer_instance

/-- **Derived Hom along the identity is the identity**: `RHom_B(B, -) ≅ id`.  Derived coextension
of scalars along `f` is right adjoint to the functor induced by restriction of scalars along `f`
([stacks 0A70]); for `f` the identity that functor is the identity, so uniqueness of adjoints
identifies `RHom_B(B, -)` with the identity. -/
def derivedHomIdIso (B : Type u) [CommRing B] :
    derivedHom.{u, 0} (RingHom.id B) ≅ 𝟭 (DerivedCategory (ModuleCat.{u} B)) :=
  (Adjunction.rightAdjointUniq Adjunction.id
    ((Classical.choice
      (restrictScalarsDerived_adj_derivedHom.{u, 0} (RingHom.id B))).ofNatIsoLeft
        mapDerivedCategoryIdIso)).symm

/-- Derived Hom along an endomorphism that happens to be the identity is the identity. -/
def derivedHomIsoIdOfEq {B : Type u} [CommRing B] (f : B →+* B)
    (hf : f = RingHom.id B) :
    derivedHom.{u, 0} f ≅ 𝟭 (DerivedCategory (ModuleCat.{u} B)) := by
  subst hf
  exact derivedHomIdIso B

end DiagonalCondition

namespace PolynomialPresentation

open DiagonalCondition

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]

/-- **The diagonal condition of [stacks 0E2C] for the relative dualizing complex
`ω^•_{A/R} = φ^!(R)`, through [stacks 0BZV]**, for `φ : R → A` flat of finite type between
Noetherian rings:
`RHom_{A ⊗_R A}(A, ω^•_{A/R} ⊗_A^L (A ⊗_R A))` is isomorphic to `A` placed in degree zero.

The proof follows the source.  Base change for the relative dualizing complex, [stacks 0BZV]
case (2), read at `R' = A`, identifies the derived base change of `ω^•_{A/R}` along the right
coprojection with upper shriek of the left coprojection at `A`; derived Hom from the diagonal is
upper shriek of the multiplication map, which is surjective ([stacks 0C0G]); composing the two
upper shrieks is [stacks 0BZT] for a surjective second map, and gives upper shriek of a
presentation of the identity of `A` with as many variables as the presentation `p` has; comparing
that with the presentation of the identity with no variables is [stacks 0BZJ], after which
derived Hom along the identity is the identity.  The passage from the right coprojection back to
the left one that [stacks 0E2C] is written with is `Dualizing.derivedHomIncludeRightIso`.

The one input of [stacks 0BZJ] used here is `Dualizing.PolynomialEvalDuality`, supplied by
`Dualizing.polynomialEvalDuality` and so not a hypothesis.  The same conclusion, through flat
base change [stacks 0BZN], is
`Dualizing.PolynomialPresentation.relativeDualizingComplex_diagonalDerivedHom`.
-/
theorem relativeDualizingComplex_diagonalDerivedHom_of_flat
    [IsNoetherianRing R] [IsNoetherianRing A]
    (p : PolynomialPresentation (algebraMap R A)) (hflat : (algebraMap R A).Flat) :
    letI : Module.Flat R A := RingHom.flat_algebraMap_iff.mp hflat
    Nonempty
      ((derivedHom.{u, u}
          (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A).toRingHom).obj
          ((diagonalDerivedExtension R A).obj
            (p.upperShriekFunctor.{u, 0}.obj
              ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)))) ≅
        (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)) := by
  let : Module.Flat R A := RingHom.flat_algebraMap_iff.mp hflat
  -- the multiplication map and the left coprojection of `A ⊗_R A`
  set δ : TensorProduct R A A →+* A :=
    (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A).toRingHom with hδdef
  set g : A →+* TensorProduct R A A :=
    (Algebra.TensorProduct.includeLeft : A →ₐ[R] TensorProduct R A A).toRingHom with hgdef
  have hcomp : δ.comp g = RingHom.id A := by
    ext a
    simp [hδdef, hgdef]
  have hδsurj : Function.Surjective δ := fun a =>
    ⟨g a, congrFun (congrArg DFunLike.coe hcomp) a⟩
  have hsurj : Function.Surjective (δ.comp g) := hcomp ▸ Function.surjective_id
  let X := (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)
  let ω := p.upperShriekFunctor.{u, 0}.obj
    ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R))
  -- derived base change along the right coprojection `A → A ⊗_R A`
  let DT := totalDerivedExtensionScalars.{u, u, u}
    (Algebra.TensorProduct.includeRight : A →ₐ[R] TensorProduct R A A).toRingHom
  let q := p.baseChange (R' := A)
  obtain ⟨eBC⟩ := relativeDualizingComplexBaseChange_of_flatAlgebra (R' := A) p hflat
    DT.functor DT.comparison DT.isLeftDerived
  obtain ⟨eΔ⟩ := upperShriekFunctor_ofSurjective_iso_derivedHom.{u, 0} δ hδsurj
  obtain ⟨eComp⟩ := upperShriekFunctor_comp_ofSurjective.{u, 0} q δ hδsurj
  obtain ⟨eVars⟩ := upperShriekFunctor_iso.{u, 0} polynomialEvalDuality.{u} (δ.comp g)
    (q.compSurjective δ hδsurj) (PolynomialPresentation.ofSurjective (δ.comp g) hsurj)
  obtain ⟨eNoVars⟩ := upperShriekFunctor_ofSurjective_iso_derivedHom.{u, 0} (δ.comp g) hsurj
  let eId := derivedHomIsoIdOfEq (δ.comp g) hcomp
  refine ⟨(derivedHomIncludeRightIso R A ω).symm ≪≫
    (derivedHom.{u, u} δ).mapIso eBC ≪≫ ?_⟩
  refine (show (derivedHom.{u, u} δ).obj (q.upperShriekFunctor.{u, 0}.obj X) =
      (derivedHom.{u, 0} δ).obj (q.upperShriekFunctor.{u, 0}.obj X) from rfl) ▸ ?_
  exact (eΔ.app (q.upperShriekFunctor.{u, 0}.obj X)).symm ≪≫ eComp.app X ≪≫ eVars.app X ≪≫
    eNoVars.app X ≪≫ eId.app X

/-- **[stacks 0E2E] along the route through [stacks 0BZV], for `φ` flat.**
Let `φ : R → A` be a flat homomorphism of finite type of Noetherian rings.  Then the relative
dualizing complex `ω^•_{A/R} = φ^!(R)` is a relative dualizing complex in the sense of
[stacks 0E2C].  The tag is registered on
`Dualizing.PolynomialPresentation.relativeDualizingComplex_isRelativeDualizingComplex`, which
carries nothing; this statement is subsumed by it and is kept for its callers.

Both conditions of that definition are proved.  Relative perfection is
`Dualizing.PolynomialPresentation.relativeDualizingComplex_isRelativelyPerfect_of_flat` and the
diagonal condition is
`Dualizing.PolynomialPresentation.relativeDualizingComplex_diagonalDerivedHom_of_flat`; neither
assumes any part of the conclusion.  Finite presentation of `φ` is not a hypothesis: a flat map of
finite type of Noetherian rings is of finite presentation, and a polynomial presentation exists
only for a map of finite type.

Nothing is carried.  The one input,
`Dualizing.PolynomialEvalDuality` — [stacks 0BZH] at the evaluation
surjections, the one input of [stacks 0BZJ] — is discharged by `Dualizing.polynomialEvalDuality`.
See this module's documentation. -/
theorem relativeDualizingComplex_isRelativeDualizingComplex_of_flat
    [IsNoetherianRing R] [IsNoetherianRing A]
    (p : PolynomialPresentation (algebraMap R A)) (hflat : (algebraMap R A).Flat) :
    letI : Module.Flat R A := RingHom.flat_algebraMap_iff.mp hflat
    letI : Algebra.FinitePresentation R A :=
      Algebra.FinitePresentation.of_finiteType.mp (RingHom.finiteType_algebraMap.mp p.finiteType)
    IsRelativeDualizingComplex R A
      (p.upperShriekFunctor.{u, 0}.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R))) := by
  let : Module.Flat R A := RingHom.flat_algebraMap_iff.mp hflat
  let : Algebra.FinitePresentation R A :=
    Algebra.FinitePresentation.of_finiteType.mp (RingHom.finiteType_algebraMap.mp p.finiteType)
  exact ⟨p.relativeDualizingComplex_isRelativelyPerfect_of_flat hflat,
    p.relativeDualizingComplex_diagonalDerivedHom_of_flat hflat⟩

/-- **The diagonal condition of [stacks 0E2C] for `ω^•_{A/R} = φ^!(R)`, with nothing carried.**
For `φ : R → A` flat of finite type with `R` Noetherian and `p` any polynomial presentation of
`φ`, `RHom_{A ⊗_R A}(A, ω^•_{A/R} ⊗_A^L (A ⊗_R A))` is isomorphic to `A` placed in degree zero.

The route is the source's.  Flat base change [stacks 0BZN] along the flat map `R → A`,
`Dualizing.PolynomialPresentation.isIso_upperShriekFlatBaseChange_app`, identifies the derived
base change of `ω^•_{A/R}` along the right coprojection with `q^!(A)`, for `q` the base-changed
presentation of the left coprojection; derived Hom from the diagonal is upper shriek of the
multiplication map `Δ`, which is surjective ([stacks 0C0G]); `Δ^! ∘ q^! ≅ (Δ ∘ p₂)^!` is
[stacks 0BZT] for a surjective second map; and `(Δ ∘ p₂)^! = id^!` is the identity by the
independence of the presentation, [stacks 0BZJ].  The passage from the right coprojection to the
left one in which [stacks 0E2C] is written is `Dualizing.derivedHomIncludeRightIso`. -/
theorem relativeDualizingComplex_diagonalDerivedHom [IsNoetherianRing R]
    (p : PolynomialPresentation (algebraMap R A)) (hflat : (algebraMap R A).Flat) :
    letI : Module.Flat R A := RingHom.flat_algebraMap_iff.mp hflat
    Nonempty
      ((derivedHom.{u, u}
          (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A).toRingHom).obj
          ((diagonalDerivedExtension R A).obj
            (p.upperShriekFunctor.{u, 0}.obj
              ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)))) ≅
        (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)) := by
  let : Module.Flat R A := RingHom.flat_algebraMap_iff.mp hflat
  set δ : TensorProduct R A A →+* A :=
    (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A).toRingHom with hδdef
  set g : A →+* TensorProduct R A A :=
    (Algebra.TensorProduct.includeLeft : A →ₐ[R] TensorProduct R A A).toRingHom with hgdef
  have hcomp : δ.comp g = RingHom.id A := by
    ext a
    simp [hδdef, hgdef]
  have hδsurj : Function.Surjective δ := fun a =>
    ⟨g a, congrFun (congrArg DFunLike.coe hcomp) a⟩
  have hsurj : Function.Surjective (δ.comp g) := hcomp ▸ Function.surjective_id
  let R0 := (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)
  let X := (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)
  let ω := p.upperShriekFunctor.{u, 0}.obj R0
  let fR := (Algebra.TensorProduct.includeRight : A →ₐ[R] TensorProduct R A A).toRingHom
  let DT := totalDerivedExtensionScalars.{u, u, u} fR
  let q := p.baseChange (R' := A)
  -- flat base change [stacks 0BZN] at `R' = A`, evaluated at `R[0]`
  have := p.isIso_upperShriekFlatBaseChange_app.{u, 0} (R' := A) hflat R0
    (derivedCategoryBBounded_singleFunctor_obj.{u, 0} (ModuleCat.of R R) inferInstance).1.1
  let eFB := asIso ((p.upperShriekFlatBaseChange.{u, 0} (R' := A) hflat).app R0)
  -- `R[0] ⊗_R^L A ≅ A[0]`
  let eUnit : (flatDerivedExtension (algebraMap R A) hflat).obj R0 ≅ X := by
    let : Limits.PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u} (algebraMap R A)) :=
      extendScalars_preservesFiniteLimits_of_flat' _ hflat
    exact ((ModuleCat.extendScalars.{u, u, u} (algebraMap R A)).mapDerivedCategorySingleFunctor
        0).app (ModuleCat.of R R) ≪≫
      (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).mapIso
        (ModuleCat.ExtendScalars.objSelfIso (algebraMap R A))
  -- the two models of derived extension of scalars along the right coprojection agree
  let eDT : DT.functor ≅ flatDerivedExtension fR (flat_includeRight hflat) := by
    let := DT.isLeftDerived
    let := flatDerivedExtension_isLeftDerivedFunctor fR (flat_includeRight hflat)
    exact Functor.leftDerivedNatIso _ _ DT.comparison
      (flatDerivedExtensionComparison fR (flat_includeRight hflat))
      (HomologicalComplex.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ)) (Iso.refl _)
  let eBC : DT.functor.obj ω ≅ q.upperShriekFunctor.{u, 0}.obj X :=
    eDT.app ω ≪≫ eFB ≪≫ q.upperShriekFunctor.{u, 0}.mapIso eUnit
  obtain ⟨eΔ⟩ := upperShriekFunctor_ofSurjective_iso_derivedHom.{u, 0} δ hδsurj
  obtain ⟨eComp⟩ := upperShriekFunctor_comp_ofSurjective.{u, 0} q δ hδsurj
  obtain ⟨eVars⟩ := upperShriekFunctor_iso.{u, 0} polynomialEvalDuality.{u} (δ.comp g)
    (q.compSurjective δ hδsurj) (PolynomialPresentation.ofSurjective (δ.comp g) hsurj)
  obtain ⟨eNoVars⟩ := upperShriekFunctor_ofSurjective_iso_derivedHom.{u, 0} (δ.comp g) hsurj
  let eId := derivedHomIsoIdOfEq (δ.comp g) hcomp
  refine ⟨(derivedHomIncludeRightIso R A ω).symm ≪≫
    (derivedHom.{u, u} δ).mapIso eBC ≪≫ ?_⟩
  refine (show (derivedHom.{u, u} δ).obj (q.upperShriekFunctor.{u, 0}.obj X) =
      (derivedHom.{u, 0} δ).obj (q.upperShriekFunctor.{u, 0}.obj X) from rfl) ▸ ?_
  exact (eΔ.app (q.upperShriekFunctor.{u, 0}.obj X)).symm ≪≫ eComp.app X ≪≫ eVars.app X ≪≫
    eNoVars.app X ≪≫ eId.app X

/-- **Stacks Project, Tag 0E2E.**  Let `φ : R → A` be a flat homomorphism of finite type of
Noetherian rings.  Then the relative dualizing complex `ω^•_{A/R} = φ^!(R)` is a relative
dualizing complex in the sense of [stacks 0E2C]; here `φ^!` is read at `p`, which is an arbitrary
polynomial presentation of `φ`.

Relative perfection is [stacks 0BZW] (2)(a),
`Dualizing.PolynomialPresentation.relativeDualizingComplex_isRelativelyPerfect`, and the diagonal
condition is `Dualizing.PolynomialPresentation.relativeDualizingComplex_diagonalDerivedHom`, from
flat base change [stacks 0BZN], the composition [stacks 0BZT] and the independence of the
presentation [stacks 0BZJ].  Finite presentation of `φ`, which [stacks 0E2C] is stated for, is
not a hypothesis: a flat map of finite type of Noetherian rings is of finite presentation, and a
polynomial presentation exists only for a map of finite type. -/
@[stacks 0E2E]
theorem relativeDualizingComplex_isRelativeDualizingComplex
    [IsNoetherianRing R] [IsNoetherianRing A]
    (p : PolynomialPresentation (algebraMap R A)) (hflat : (algebraMap R A).Flat) :
    letI : Module.Flat R A := RingHom.flat_algebraMap_iff.mp hflat
    letI : Algebra.FinitePresentation R A :=
      Algebra.FinitePresentation.of_finiteType.mp (RingHom.finiteType_algebraMap.mp p.finiteType)
    IsRelativeDualizingComplex R A
      (p.upperShriekFunctor.{u, 0}.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R))) := by
  let : Module.Flat R A := RingHom.flat_algebraMap_iff.mp hflat
  let : Algebra.FinitePresentation R A :=
    Algebra.FinitePresentation.of_finiteType.mp (RingHom.finiteType_algebraMap.mp p.finiteType)
  exact ⟨p.relativeDualizingComplex_isRelativelyPerfect hflat,
    p.relativeDualizingComplex_diagonalDerivedHom hflat⟩

end PolynomialPresentation

end Dualizing

end
