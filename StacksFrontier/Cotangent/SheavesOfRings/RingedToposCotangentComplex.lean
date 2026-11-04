module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposHom
public import StacksFrontier.Cotangent.SheavesOfRings.CotangentComplex
import StacksCore.Tactic.StacksAttribute

/-!
# The cotangent complex of a morphism of ringed topoi

For a morphism of ringed topoi `(f, f♯) : (Sh(C), 𝒪_C) ⟶ (Sh(D), 𝒪_D)` the cotangent complex
`L_f` is the cotangent complex `L_{𝒪_C/f⁻¹𝒪_D}` of the inverse-image form
`f⁻¹𝒪_D ⟶ 𝒪_C` of the structure map, a complex of sheaves of `𝒪_C`-modules on the source
site, concentrated in non-positive cohomological degrees.

## Main definitions

* `AlgebraicGeometry.RingedToposHom.cotangentComplex` is `L_f`.
* `AlgebraicGeometry.RingedToposHom.cotangentComplexDerived` is `L_f` as an object of the
  derived category of sheaves of `𝒪_C`-modules.

## Main results

* `AlgebraicGeometry.RingedToposHom.cotangentComplex_isZero_pos`: `L_f` vanishes in positive
  cohomological degrees.

## Implementation notes

The source site is required to carry its structure sheaf in the universe `max u v w`, where
`u` and `v` are the universes of its objects and of its morphisms: this is the universe range
of `CategoryTheory.Sheaf.cotangentComplex`, whose standard resolution is formed by sheafifying
polynomial algebras on the site. The target ringed topos is unconstrained, its structure sheaf
being carried to the source site by the inverse image before the cotangent complex is formed.

## References

* [Stacks Project, Tag 08SU](https://stacks.math.columbia.edu/tag/08SU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u w v' u' w' t

namespace AlgebraicGeometry.RingedToposHom

variable {X : RingedTopos.{v, u, max u v w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget RingCat.{max u v w})]
  [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  (f : RingedToposHom X Y)

/-- **Stacks 08SU.** The cotangent complex `L_f = L_{𝒪_C/f⁻¹𝒪_D}` of a morphism of ringed
topoi `(f, f♯) : (Sh(C), 𝒪_C) ⟶ (Sh(D), 𝒪_D)`: the cotangent complex of the inverse-image
form `f⁻¹𝒪_D ⟶ 𝒪_C` of its structure map. -/
@[stacks 08SU]
noncomputable def cotangentComplex :
    CochainComplex (Sheaf.targetModules.{u, v, w} X.J X.O) ℤ :=
  Sheaf.cotangentComplex.{u, v, w} X.J f.fSharpInverseImage

/-- **Stacks 08SU.** The cotangent complex of a morphism of ringed topoi, regarded as an object
of the derived category of sheaves of `𝒪_C`-modules. -/
@[stacks 08SU "the derived object"]
noncomputable abbrev cotangentComplexDerived
    [HasDerivedCategory.{t} (Sheaf.targetModules.{u, v, w} X.J X.O)] :
    DerivedCategory (Sheaf.targetModules.{u, v, w} X.J X.O) :=
  DerivedCategory.Q.obj f.cotangentComplex

/-- The cotangent complex of a morphism of ringed topoi vanishes in positive cohomological
degrees. -/
theorem cotangentComplex_isZero_pos (m : ℤ) (hm : 0 < m) :
    IsZero ((f.cotangentComplex).X m) :=
  Sheaf.cotangentComplex_isZero_pos.{u, v, w} X.J f.fSharpInverseImage m hm

/-- The term of the cotangent complex in degree `-n` is the sheaf of relative differentials of
the `n`th term of the standard resolution of `f⁻¹𝒪_D ⟶ 𝒪_C`, base changed to `𝒪_C`. -/
noncomputable def cotangentComplex_degreeIso (n : ℕ) :
    (f.cotangentComplex).X (-(n : ℤ)) ≅
      (Sheaf.cotangentSimplicialModule.{u, v, w} X.J f.fSharpInverseImage).object.obj
        (Opposite.op (SimplexCategory.mk n)) :=
  Sheaf.cotangentComplex_degreeIso.{u, v, w} X.J f.fSharpInverseImage n

end AlgebraicGeometry.RingedToposHom

end
