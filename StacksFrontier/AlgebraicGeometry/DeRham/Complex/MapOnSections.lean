module

public import StacksFrontier.AlgebraicGeometry.DeRham.Complex.DifferentialForms
public import StacksFrontier.AlgebraicGeometry.ExternalTensorPullback.ComparisonSections
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.DifferentialMap

/-!
# The canonical map on relative differential forms, read on local sections

A commutative square of schemes

```
W → X
↓    ↓
S' → S
```

induces the canonical map `f^*Ω^n_{X/S} ⟶ Ω^n_{W/S'}` of
`StacksFrontier.AlgebraicGeometry.DeRham.Complex.DifferentialForms`. Composing it with the unit of
`f^* ⊣ f_*` gives, for every open `U` of `X`, a map

`Γ(Ω^n_{X/S}, U) ⟶ Γ(Ω^n_{W/S'}, f⁻¹U)`

which is the operation "pull back a differential form along `f`". It is multiplicative, unital,
semilinear over the structure morphism of `f`, and compatible with restriction to a smaller open.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.relativeDifferentialFormsPullback`: the pullback of a local
  differential form along a commutative square.

## Main results

* `AlgebraicGeometry.Scheme.Hom.relativeDifferentialFormsPullback_mul` and
  `relativeDifferentialFormsPullback_one`: **pulling back a form is a homomorphism of graded
  algebras on local sections.**
* `AlgebraicGeometry.Scheme.Hom.relativeDifferentialFormsPullback_smul`: it is semilinear over
  `f^# : Γ(X, U) ⟶ Γ(W, f⁻¹U)`.
* `AlgebraicGeometry.Scheme.Hom.relativeDifferentialFormsPullback_map`: it commutes with
  restriction.
* `AlgebraicGeometry.Scheme.Hom.relativeDifferentialsMap_modulesPullbackUnit_d` and
  `relativeDifferentialFormsPullback_exteriorGenerator_d`: **the canonical
  map on relative differentials carries the pullback of an exact differential `d x` to the exact
  differential `d (f^# x)`** (Tag 01UV, on local sections).

## References

* [Stacks Project, Tag 01UV](https://stacks.math.columbia.edu/tag/01UV)
* [Stacks Project, Tag 01CI](https://stacks.math.columbia.edu/tag/01CI)
* [Stacks Project, Tag 0FL5](https://stacks.math.columbia.edu/tag/0FL5)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite
open Stacks.Tag01VSPullbackTensor Stacks.PullbackExteriorAlgebra

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X S' S W : Scheme.{u}} (f : W ⟶ X) (a : X ⟶ S) (a' : W ⟶ S')

/-- **Stacks Project, Tag 01CI for the sheaf of relative differentials.** The comparison between
the pullback of the exterior algebra of `Ω_{X/S}` and the exterior algebra of `f^*Ω_{X/S}`,
packaged with its compatibilities with the products, the units and the degree-one generators. -/
noncomputable def relativeDifferentialFormsPullbackIso :
    ExteriorAlgebraPullbackIso f.toLRSHom.toShHom
      (relativeDifferentialFormsAlgebra a)
      (Scheme.Modules.exteriorGenerator (relativeDifferentials a))
      (Scheme.Modules.exteriorAlgebra ((Scheme.Modules.pullback f).obj (relativeDifferentials a)))
      (Scheme.Modules.exteriorGenerator
        ((Scheme.Modules.pullback f).obj (relativeDifferentials a))) :=
  exteriorAlgebraPullbackIso f.toLRSHom.toShHom
    (relativeDifferentialFormsAlgebra a)
    (Scheme.Modules.exteriorGenerator (relativeDifferentials a))
    (Scheme.Modules.exteriorAlgebra ((Scheme.Modules.pullback f).obj (relativeDifferentials a)))
    (Scheme.Modules.exteriorGenerator
      ((Scheme.Modules.pullback f).obj (relativeDifferentials a)))
    (Scheme.Modules.isExteriorAlgebra_exteriorAlgebra (relativeDifferentials a))
    (Scheme.Modules.isExteriorAlgebra_exteriorAlgebra _)

variable (g : S' ⟶ S) (hcomm : f ≫ a = a' ≫ g)

/-- **The pullback of a local differential form along a commutative square of schemes.** A local
section of `Ω^n_{X/S}` over an open `U` of `X` is carried to a local section of `Ω^n_{W/S'}` over
`f⁻¹U` by the unit of `f^* ⊣ f_*` followed by the canonical map
`f^*Ω^n_{X/S} ⟶ Ω^n_{W/S'}`. -/
noncomputable def relativeDifferentialFormsPullback (n : ℤ) (U : X.Opens)
    (ω : Γ(relativeDifferentialForms a n, U)) : Γ(relativeDifferentialForms a' n, f ⁻¹ᵁ U) :=
  Scheme.Modules.Hom.app (relativeDifferentialFormsMap f a a' g hcomm n) (f ⁻¹ᵁ U)
    (modulesPullbackUnit f (relativeDifferentialForms a n) U ω)

/-- The pullback of a local differential form is the comparison of Tag 01CI followed by the
canonical graded comparison, applied to the pullback-unit image of the form. -/
theorem relativeDifferentialFormsPullback_eq (n : ℤ) (U : X.Opens)
    (ω : Γ(relativeDifferentialForms a n, U)) :
    relativeDifferentialFormsPullback f a a' g hcomm n U ω =
      ((relativeDifferentialFormsComparison f a a' g hcomm).app n).val.app (op (f ⁻¹ᵁ U))
        (((relativeDifferentialFormsPullbackIso f a).app n).hom.val.app (op (f ⁻¹ᵁ U))
          (modulesPullbackUnit f (relativeDifferentialForms a n) U ω)) :=
  rfl

/-- **Pulling back a differential form is multiplicative.** -/
theorem relativeDifferentialFormsPullback_mul (i j : ℤ) (U : X.Opens)
    (x : Γ(relativeDifferentialForms a i, U)) (y : Γ(relativeDifferentialForms a j, U)) :
    relativeDifferentialFormsPullback f a a' g hcomm (i + j) U
        (((relativeDifferentialFormsAlgebra a).mul i j).app (op U) x y) =
      ((relativeDifferentialFormsAlgebra a').mul i j).app (op (f ⁻¹ᵁ U))
        (relativeDifferentialFormsPullback f a a' g hcomm i U x)
        (relativeDifferentialFormsPullback f a a' g hcomm j U y) :=
  Eq.trans
    (congrArg
      (((relativeDifferentialFormsComparison f a a' g hcomm).app (i + j)).val.app (op (f ⁻¹ᵁ U)))
      ((relativeDifferentialFormsPullbackIso f a).map_mul i j (op U) x y))
    ((relativeDifferentialFormsComparison f a a' g hcomm).map_mul i j (op (f ⁻¹ᵁ U)) _ _)

/-- **Pulling back a differential form is unital**: the unit of `Ω^•_{X/S}` goes to the unit of
`Ω^•_{W/S'}`. -/
theorem relativeDifferentialFormsPullback_one (U : X.Opens) :
    relativeDifferentialFormsPullback f a a' g hcomm 0 U
        ((relativeDifferentialFormsAlgebra a).one.eval (op U)) =
      (relativeDifferentialFormsAlgebra a').one.eval (op (f ⁻¹ᵁ U)) :=
  Eq.trans
    (congrArg
      (((relativeDifferentialFormsComparison f a a' g hcomm).app 0).val.app (op (f ⁻¹ᵁ U)))
      ((relativeDifferentialFormsPullbackIso f a).map_one (op U)))
    ((relativeDifferentialFormsComparison f a a' g hcomm).map_one (op (f ⁻¹ᵁ U)))

/-- Pulling back a form whose pullback-unit image is `z` is the canonical map applied to `z`. -/
private theorem relativeDifferentialFormsPullback_eq_app (n : ℤ) (U : X.Opens)
    {ω : Γ(relativeDifferentialForms a n, U)}
    {z : Γ((Scheme.Modules.pullback f).obj (relativeDifferentialForms a n), f ⁻¹ᵁ U)}
    (h : Stacks.RingedSpace.pullbackUnit f.toLRSHom.toShHom
      (relativeDifferentialForms a n) (op U) ω = z) :
    relativeDifferentialFormsPullback f a a' g hcomm n U ω =
      Scheme.Modules.Hom.app (relativeDifferentialFormsMap f a a' g hcomm n) (f ⁻¹ᵁ U) z :=
  congrArg _ h

/-- **Pulling back a differential form is semilinear** over the structure morphism of `f`. -/
theorem relativeDifferentialFormsPullback_smul (n : ℤ) (U : X.Opens) (r : Γ(X, U))
    (ω : Γ(relativeDifferentialForms a n, U)) :
    relativeDifferentialFormsPullback f a a' g hcomm n U (r • ω) =
      (f.app U).hom r • relativeDifferentialFormsPullback f a a' g hcomm n U ω :=
  (relativeDifferentialFormsPullback_eq_app f a a' g hcomm n U
      (Stacks.RingedSpace.pullbackUnit_smul f.toLRSHom.toShHom
        (relativeDifferentialForms a n) (op U) r ω)).trans
    (Scheme.Modules.Hom.app_smul ..)

/-- Pulling back the zero form gives the zero form. -/
theorem relativeDifferentialFormsPullback_zero (n : ℤ) (U : X.Opens) :
    relativeDifferentialFormsPullback f a a' g hcomm n U 0 = 0 :=
  (relativeDifferentialFormsPullback_eq_app f a a' g hcomm n U (map_zero _)).trans
    (map_zero _)

/-- Pulling back a differential form is additive. -/
theorem relativeDifferentialFormsPullback_add (n : ℤ) (U : X.Opens)
    (x y : Γ(relativeDifferentialForms a n, U)) :
    relativeDifferentialFormsPullback f a a' g hcomm n U (x + y) =
      relativeDifferentialFormsPullback f a a' g hcomm n U x +
        relativeDifferentialFormsPullback f a a' g hcomm n U y :=
  (relativeDifferentialFormsPullback_eq_app f a a' g hcomm n U (map_add _ _ _)).trans
    (map_add _ _ _)

/-- Pulling back a differential form commutes with negation. -/
theorem relativeDifferentialFormsPullback_neg (n : ℤ) (U : X.Opens)
    (x : Γ(relativeDifferentialForms a n, U)) :
    relativeDifferentialFormsPullback f a a' g hcomm n U (-x) =
      -relativeDifferentialFormsPullback f a a' g hcomm n U x :=
  (relativeDifferentialFormsPullback_eq_app f a a' g hcomm n U (map_neg _ _)).trans
    (map_neg _ _)

/-- **Pulling back a differential form commutes with restriction** to a smaller open. -/
theorem relativeDifferentialFormsPullback_map (n : ℤ) {U V : X.Opens} (hVU : V ≤ U)
    (ω : Γ(relativeDifferentialForms a n, U)) :
    relativeDifferentialFormsPullback f a a' g hcomm n V
        ((relativeDifferentialForms a n).presheaf.map (homOfLE hVU).op ω) =
      (relativeDifferentialForms a' n).presheaf.map
        (homOfLE (show f ⁻¹ᵁ V ≤ f ⁻¹ᵁ U from fun _ hz => hVU hz)).op
        (relativeDifferentialFormsPullback f a a' g hcomm n U ω) :=
  Eq.trans
    (congrArg
      (Scheme.Modules.Hom.app (relativeDifferentialFormsMap f a a' g hcomm n) (f ⁻¹ᵁ V))
      (modulesPullbackUnit_map f (relativeDifferentialForms a n) hVU ω))
    (homApp_presheaf_map (relativeDifferentialFormsMap f a a' g hcomm n) _ _)

/-- Pulling back a differential form respects the heterogeneous equality of two forms of equal
degree. -/
theorem relativeDifferentialFormsPullback_heq {i j : ℤ} (hij : i = j) (U : X.Opens)
    {x : Γ(relativeDifferentialForms a i, U)} {y : Γ(relativeDifferentialForms a j, U)}
    (hxy : HEq x y) :
    HEq (relativeDifferentialFormsPullback f a a' g hcomm i U x)
      (relativeDifferentialFormsPullback f a a' g hcomm j U y) := by
  subst hij
  cases eq_of_heq hxy
  rfl

/-- **Stacks Project, Tag 01UV, on local sections.** The canonical map on relative differentials
carries the pullback-unit image of the exact differential `d x` of a local section `x` of `𝒪_X`
to the exact differential `d (f^# x)` of its pullback. -/
theorem relativeDifferentialsMap_modulesPullbackUnit_d (U : X.Opens) (x : Γ(X, U)) :
    Scheme.Modules.Hom.app (relativeDifferentialsMap f a a' g hcomm) (f ⁻¹ᵁ U)
        (modulesPullbackUnit f (relativeDifferentials a) U
          ((universalRelativeDerivation a).d x))
      = (universalRelativeDerivation a').d ((f.app U).hom x) := by
  have h0 := relativeDifferentialsMap_app_d g hcomm U x
  rw [Adjunction.homEquiv_unit] at h0
  exact h0

/-- **The pullback of an exact differential is the exact differential of the pullback**: in
degree one, the pullback of the generator `d b` is the generator `d (f^# b)`. -/
theorem relativeDifferentialFormsPullback_exteriorGenerator_d (U : X.Opens) (b : Γ(X, U)) :
    relativeDifferentialFormsPullback f a a' g hcomm 1 U
        (Scheme.Modules.Hom.app (Scheme.Modules.exteriorGenerator (relativeDifferentials a)) U
          ((universalRelativeDerivation a).d b)) =
      Scheme.Modules.Hom.app
        (Scheme.Modules.exteriorGenerator (relativeDifferentials a')) (f ⁻¹ᵁ U)
        ((universalRelativeDerivation a').d ((f.app U).hom b)) :=
  Eq.trans
    (congrArg
      (((relativeDifferentialFormsComparison f a a' g hcomm).app 1).val.app (op (f ⁻¹ᵁ U)))
      ((relativeDifferentialFormsPullbackIso f a).map_generator (op U)
        ((universalRelativeDerivation a).d b)))
    (Eq.trans
      (_root_.SheafOfModules.hom_congr_app_apply
        (relativeDifferentialFormsComparison_generator f a a' g hcomm) (op (f ⁻¹ᵁ U))
        (modulesPullbackUnit f (relativeDifferentials a) U
          ((universalRelativeDerivation a).d b)))
      (congrArg
        (Scheme.Modules.Hom.app
          (Scheme.Modules.exteriorGenerator (relativeDifferentials a')) (f ⁻¹ᵁ U))
        (relativeDifferentialsMap_modulesPullbackUnit_d f a a' g hcomm U b)))

end AlgebraicGeometry.Scheme.Hom

end
