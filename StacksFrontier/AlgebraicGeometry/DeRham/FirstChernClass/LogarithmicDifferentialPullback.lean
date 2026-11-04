module

public import StacksFrontier.AlgebraicGeometry.Curves.GlueingSquishing.GlueingUnitsSequence
public import StacksFrontier.AlgebraicGeometry.DeRham.FirstChernClass.FilteredFirstChernClass
public import StacksFrontier.AlgebraicGeometry.DeRham.Functoriality

/-!
# Logarithmic differentiation commutes with pullback, in the de Rham spelling

Let

```
X' --f--> X
|         |
S' -----> S
```

be a commutative square of schemes. The canonical homomorphism of sheaves of graded algebras
`⋀ Ω_{X/S} ⟶ f_*(⋀ Ω_{X'/S'})` of Stacks Tag 07HX
(`AlgebraicGeometry.Scheme.Hom.deRhamFormsPushforwardHom`) carries the logarithmic differential
`d log u = u⁻¹ · d u` of an invertible local section of `𝒪_X` to the logarithmic differential of
its pullback along `f`. This file proves that, on local sections and as an identity of morphisms
of sheaves of abelian groups, for the logarithmic differential
`AlgebraicGeometry.SheafOfModules.logarithmicDifferential` out of which the de Rham and
Hodge-filtered first Chern classes of Stacks Tags 0FLE and 0FME are built.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.unitsComplexPushforwardMapPlus`: the pullback of units
  `𝒪_X^* ⟶ f_*𝒪_{X'}^*` placed in cohomological degree one, as a morphism of bounded-below
  complexes of abelian sheaves `𝒪_X^*[-1] ⟶ f_*(𝒪_{X'}^*[-1])`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.deRhamFormsPushforwardHom_logarithmicDifferential`:
  **logarithmic differentiation commutes with the canonical homomorphism of de Rham algebras**,
  on local sections.
* `AlgebraicGeometry.Scheme.Hom.logarithmicDifferentialAbelianSheafHom_deRham_naturality`: the
  same square, as an identity of morphisms of sheaves of abelian groups — pullback of units
  followed by `d log` on `X'` is `d log` on `X` followed by the degree-one component of the
  canonical map of de Rham complexes
  `AlgebraicGeometry.Scheme.Hom.deRhamAbelianPushforwardMap`.
* `AlgebraicGeometry.Scheme.Hom.unitsComplexPushforwardMapPlus_logarithmicDifferentialComplexMapPlus`:
  **the same square on bounded-below complexes** — `d log : 𝒪_X^*[-1] ⟶ Ω^•_{X/S}` commutes with
  the two pullback maps of the square. This is the form Tag 0FMD's de Rham square consumes,
  through the functoriality
  `AlgebraicGeometry.Scheme.Hom.derivedSectionsPullback_naturality` of pullback on derived global
  sections.

## Implementation notes

The lift of the sheaf-level square to complexes is
`HomologicalComplex.mkHomFromSingle_comp_extendMap_mapHomologicalComplexExtendIso`, which is
stated on abstract data. The relative de Rham complex is indexed by `ℕ` and extended by zero to
`ℤ`, and the comparison of the extension of a direct image with the direct image of the
extension is a third factor in the map of complexes, so the degree-one computation carries three
layers of bookkeeping. On the de Rham complexes themselves neither `rw` nor `simp` can perform
it: the type of `AlgebraicGeometry.SheafOfModules.deRhamAbelianComplexPlus (deRhamAlgebras p')`
is type-correct only at default transparency, requiring `relativeDifferentials` to be unfolded to
`AlgebraicGeometry.SheafOfModules.moduleOfDifferentials`, so the motive the rewriting tactics
build is rejected. On abstract data the same computation is three rewrites.

There are two logarithmic differentials in the library, because there are two realizations of
the sheaf of relative differentials of a morphism of schemes.
`AlgebraicGeometry.Scheme.Hom.logarithmicDifferential` lands in `Ω_{X/S}` itself, and the square
it satisfies, `AlgebraicGeometry.Scheme.Hom.logarithmicDifferentialSheafHom_naturality`, is
stated for the transpose `Ω_{X/S} ⟶ f_*Ω_{X'/S'}` of the canonical morphism of Tag 01UV; that
is the form the Hodge first Chern class of
`StacksFrontier.AlgebraicGeometry.DeRham.FirstChernClass.HodgeFirstChernClass` is built in.
`AlgebraicGeometry.SheafOfModules.logarithmicDifferential` lands in the degree-one piece
`⋀¹ Ω_{X/S}` of the exterior algebra, which is the degree-one term of the relative de Rham
complex, and the square proved here is stated for
`AlgebraicGeometry.Scheme.Hom.deRhamFormsPushforwardHom`, the homomorphism of exterior algebras
of the square. It is that second form the de Rham first Chern class
`AlgebraicGeometry.SheafOfModules.deRhamFirstChernClassAbelian` is built in, because the
hypercohomology it is taken in is that of the de Rham complex.

The proof is the two computation rules of the homomorphism of exterior algebras:
`AlgebraicGeometry.Scheme.Hom.deRhamFormsPushforwardHom_smul`, that it is semilinear for
`f^♯ : 𝒪_X ⟶ f_*𝒪_{X'}`, and
`AlgebraicGeometry.Scheme.Hom.deRhamFormsPushforwardHom_exactOne`, that it carries the exact
differential of a local section to the exact differential of its pullback. The logarithmic
differential is the product of the two.

## References

* [Stacks Project, Tag 0FMD](https://stacks.math.columbia.edu/tag/0FMD)
* [Stacks Project, Tag 0FLE](https://stacks.math.columbia.edu/tag/0FLE)
* [Stacks Project, Tag 0FME](https://stacks.math.columbia.edu/tag/0FME)
* [Stacks Project, Tag 07HX](https://stacks.math.columbia.edu/tag/07HX)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.LerayLowDegree (abelianPushforward)
open Stacks.GlueSquishUnits (unitsPushforwardMap unitsPushforwardMap_app)

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X' X S' S : Scheme.{u}} (f : X' ⟶ X) (p : X ⟶ S) (p' : X' ⟶ S') (g : S' ⟶ S)
  (hcomm : f ≫ p = p' ≫ g)

/-- **Logarithmic differentiation commutes with the canonical homomorphism of de Rham
algebras**: the homomorphism `⋀ Ω_{X/S} ⟶ f_*(⋀ Ω_{X'/S'})` of a commutative square of schemes
carries `d log u` to `d log` of the pullback of `u`. The logarithmic differential is
`u⁻¹ · d u`, the homomorphism is semilinear for `f^♯` and carries `d u` to `d (f^♯ u)`. -/
theorem deRhamFormsPushforwardHom_logarithmicDifferential (U : (X.Opens)ᵒᵖ)
    (u : (X.sheaf.obj.obj U)ˣ) :
    ((deRhamFormsPushforwardHom f p p' g hcomm).app 1).val.app U
        (SheafOfModules.logarithmicDifferential (deRhamAlgebras p) U u) =
      SheafOfModules.logarithmicDifferential (deRhamAlgebras p')
        ((opensMap f.toLRSHom.toShHom).op.obj U)
        (Units.map (f.app U.unop).hom.toMonoidHom u) := by
  have h1 : SheafOfModules.logarithmicDifferential (deRhamAlgebras p) U u =
      (u⁻¹).val • SheafOfModules.exactOne (deRhamAlgebras p) U u.val := rfl
  refine Eq.trans (congrArg (ConcreteCategory.hom
    (((deRhamFormsPushforwardHom f p p' g hcomm).app 1).val.app U)) h1) ?_
  refine Eq.trans (deRhamFormsPushforwardHom_smul f p p' g hcomm 1 U (u⁻¹).val
    (SheafOfModules.exactOne (deRhamAlgebras p) U u.val)) ?_
  exact congrArg
    (fun z : ((relativeDifferentialFormsAlgebra p').piece 1).val.obj
        ((opensMap f.toLRSHom.toShHom).op.obj U) =>
      @SMul.smul (X'.sheaf.obj.obj ((opensMap f.toLRSHom.toShHom).op.obj U)) _ _
        ((f.app U.unop).hom (u⁻¹).val) z)
    (deRhamFormsPushforwardHom_exactOne f p p' g hcomm U u.val)

/-- **The square of sheaves of abelian groups expressing that `d log` commutes with pullback**,
in the de Rham spelling: pullback of units followed by `d log` on `X'` is `d log` on `X`
followed by the degree-one component of the canonical map of de Rham complexes
`Ω^•_{X/S} ⟶ f_*Ω^•_{X'/S'}` of Stacks Tag 07HX. -/
theorem logarithmicDifferentialAbelianSheafHom_deRham_naturality :
    unitsPushforwardMap f ≫
        (abelianPushforward.{u, u} f.base).map
          (SheafOfModules.logarithmicDifferentialAbelianSheafHom (deRhamAlgebras p')
            (SheafOfModules.deRhamDifferential (deRhamAlgebras p'))) =
      SheafOfModules.logarithmicDifferentialAbelianSheafHom (deRhamAlgebras p)
          (SheafOfModules.deRhamDifferential (deRhamAlgebras p)) ≫
        (deRhamAbelianPushforwardMap f p p' g hcomm).f 1 := by
  apply Sheaf.hom_ext
  ext U s
  obtain ⟨V⟩ := U
  obtain ⟨u, rfl⟩ : ∃ u : (X.sheaf.obj.obj (op V))ˣ, Additive.ofMul u = s := ⟨s, rfl⟩
  show (SheafOfModules.logarithmicDifferentialAbelianSheafHom (deRhamAlgebras p')
      (SheafOfModules.deRhamDifferential (deRhamAlgebras p'))).hom.app (op (f ⁻¹ᵁ V))
      ((unitsPushforwardMap f).hom.app (op V) (Additive.ofMul u)) =
    ((deRhamFormsPushforwardHom f p p' g hcomm).app 1).val.app (op V)
      (SheafOfModules.logarithmicDifferential (deRhamAlgebras p) (op V) u)
  refine Eq.trans (congrArg (fun t =>
    (SheafOfModules.logarithmicDifferentialAbelianSheafHom (deRhamAlgebras p')
      (SheafOfModules.deRhamDifferential (deRhamAlgebras p'))).hom.app (op (f ⁻¹ᵁ V)) t)
    (unitsPushforwardMap_app f V u)) ?_
  exact (deRhamFormsPushforwardHom_logarithmicDifferential f p p' g hcomm (op V) u).symm

/-! ### The `d log` square on complexes -/

/-- The only index related to `1` in the cohomological complex shape on `ℤ` is `2`. -/
private theorem eq_two_of_rel_one {k : ℤ} (hk : (ComplexShape.up ℤ).Rel 1 k) : k = 2 := by
  have hk' : (1 : ℤ) + 1 = k := hk
  omega

/-- Every morphism into the degree-one term of `f_*(𝒪_{X'}^*[-1])` is killed by the differential
out of degree one, that complex being zero in degree two. This is the single condition for
`AlgebraicGeometry.Scheme.Hom.unitsComplexPushforwardMapPlus` to be a morphism of complexes; it
is stated on a variable `φ` so that the equation is formed in the category of abelian sheaves in
which the complex lives rather than in the definitionally equal spelling the sheaf of units
carries. -/
theorem comp_d_unitsComplexPushforward_eq_zero (k : ℤ) (hk : (ComplexShape.up ℤ).Rel 1 k)
    (φ : SheafOfModules.unitsAbelianSheaf X.toRingedSpace ⟶
      ((abelianPushforward.{u, u} f.base).mapCochainComplexPlus.obj
        (SheafOfModules.unitsComplexPlus X'.toRingedSpace)).obj.X 1) :
    φ ≫ ((abelianPushforward.{u, u} f.base).mapCochainComplexPlus.obj
        (SheafOfModules.unitsComplexPlus X'.toRingedSpace)).obj.d 1 k = 0 := by
  obtain rfl := eq_two_of_rel_one hk
  exact ((abelianPushforward.{u, u} f.base).map_isZero
    (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 1
      (SheafOfModules.unitsAbelianSheaf X'.toRingedSpace) 2 (by omega))).eq_of_tgt _ _

/-- **`𝒪_X^*[-1] ⟶ f_*(𝒪_{X'}^*[-1])`**: the pullback of units along a morphism of schemes,
placed in cohomological degree one, as a morphism of bounded-below complexes of abelian sheaves.
The source is concentrated in degree one, so the datum is
`Stacks.GlueSquishUnits.unitsPushforwardMap` in that degree and there is no closedness condition
to check, the target being zero in degree two. -/
def unitsComplexPushforwardMapPlus :
    SheafOfModules.unitsComplexPlus X.toRingedSpace ⟶
      (abelianPushforward.{u, u} f.base).mapCochainComplexPlus.obj
        (SheafOfModules.unitsComplexPlus X'.toRingedSpace) :=
  ObjectProperty.homMk (HomologicalComplex.mkHomFromSingle
    (unitsPushforwardMap f ≫ (abelianPushforward.{u, u} f.base).map
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 1
        (SheafOfModules.unitsAbelianSheaf X'.toRingedSpace)).inv)
    (fun k hk => comp_d_unitsComplexPushforward_eq_zero f k hk _))

/-- The degree-one component of `AlgebraicGeometry.Scheme.Hom.unitsComplexPushforwardMapPlus`. -/
theorem unitsComplexPushforwardMapPlus_hom_f_one :
    (unitsComplexPushforwardMapPlus f).hom.f 1 =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 1
          (SheafOfModules.unitsAbelianSheaf X.toRingedSpace)).hom ≫
        unitsPushforwardMap f ≫ (abelianPushforward.{u, u} f.base).map
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 1
            (SheafOfModules.unitsAbelianSheaf X'.toRingedSpace)).inv :=
  HomologicalComplex.mkHomFromSingle_f _
    (fun k hk => comp_d_unitsComplexPushforward_eq_zero f k hk _)

/-- **The `d log` square on bounded-below complexes of abelian sheaves**: the pullback of units
in degree one, followed by `d log` on `X'`, is `d log` on `X` followed by the canonical map of de
Rham complexes `Ω^•_{X/S} ⟶ f_*Ω^•_{X'/S'}` of Stacks Tag 07HX. Both sides are morphisms out of
a complex concentrated in degree one, so there is a single degree to check, and there the
identity is
`AlgebraicGeometry.Scheme.Hom.logarithmicDifferentialAbelianSheafHom_deRham_naturality`. -/
theorem unitsComplexPushforwardMapPlus_logarithmicDifferentialComplexMapPlus :
    unitsComplexPushforwardMapPlus f ≫
        (abelianPushforward.{u, u} f.base).mapCochainComplexPlus.map
          (SheafOfModules.logarithmicDifferentialComplexMapPlus (deRhamAlgebras p')
            (SheafOfModules.deRhamDifferential (deRhamAlgebras p'))) =
      SheafOfModules.logarithmicDifferentialComplexMapPlus (deRhamAlgebras p)
          (SheafOfModules.deRhamDifferential (deRhamAlgebras p)) ≫
        deRhamAbelianPushforwardMapPlus f p p' g hcomm :=
  ObjectProperty.hom_ext _
    (HomologicalComplex.mkHomFromSingle_comp_extendMap_mapHomologicalComplexExtendIso
      (abelianPushforward.{u, u} f.base) _ ComplexShape.embeddingUpNat rfl
      (deRhamAbelianPushforwardMap f p p' g hcomm) (unitsPushforwardMap f)
      (SheafOfModules.logarithmicDifferentialAbelianSheafHom (deRhamAlgebras p)
        (SheafOfModules.deRhamDifferential (deRhamAlgebras p)))
      (SheafOfModules.logarithmicDifferentialAbelianSheafHom (deRhamAlgebras p')
        (SheafOfModules.deRhamDifferential (deRhamAlgebras p')))
      (fun k hk => comp_d_unitsComplexPushforward_eq_zero f k hk _)
      (fun k hk => by
        obtain rfl := eq_two_of_rel_one hk
        exact SheafOfModules.logarithmicDifferentialAbelian_comp_d (deRhamAlgebras p)
          (SheafOfModules.deRhamDifferential (deRhamAlgebras p)))
      (fun k hk => by
        obtain rfl := eq_two_of_rel_one hk
        exact SheafOfModules.logarithmicDifferentialAbelian_comp_d (deRhamAlgebras p')
          (SheafOfModules.deRhamDifferential (deRhamAlgebras p')))
      (logarithmicDifferentialAbelianSheafHom_deRham_naturality f p p' g hcomm))

end AlgebraicGeometry.Scheme.Hom

end
