module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.InducedCompactification
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomologyZero
public import StacksFrontier.Algebra.Homology.DerivedCategory.BaseChangeBoundedBelow

/-!
# The base change of a compactification, and extension by zero across it

Let
```
X' --g'--> X
|f'        |f
v          v
Y' --g---> Y
```
be a cartesian square of schemes and `j : X ⟶ X̄` a compactification of `X` over `Y`, with
structure morphism `f̄ : X̄ ⟶ Y`. The fibre product `X̄' = X̄ ×_Y Y'` is proper over `Y'`, and
the morphism `j' : X' ⟶ X̄'` with components `g' ≫ j` and `f'` is an open immersion, being the
base change of `j` along `ḡ' : X̄' ⟶ X̄`: the square formed by `g'`, `j'`, `j` and `ḡ'` is
cartesian by the pasting law. So `j'` is a compactification of `X'` over `Y'`; it is the one
through which [Stacks, Tag 0F7L] computes `Rf'_!`.

Across the cartesian square of compactifications extension by zero commutes with inverse image
([Stacks, Tag 03S6]), and this persists on bounded below derived categories, inverse image and
extension by zero being exact: `Rj'_! ∘ (g')⁻¹ ≅ (ḡ')⁻¹ ∘ Rj_!`. This is the second arrow of the
proof of Tag 0F7L.

## Main definitions

* `AlgebraicGeometry.CompactificationOf.baseChange`: the compactification `X' ⟶ X̄ ×_Y Y'`.
* `Stacks.EtaleCohomology.etaleModuleDerivedExtensionByZeroBaseChangeIso`: the isomorphism
  `(g')⁻¹ ⋙ Rj'_! ≅ Rj_! ⋙ (ḡ')⁻¹` of functors on bounded below derived categories.

## Main results

* `AlgebraicGeometry.CompactificationOf.isPullback_baseChange`: the square of open immersions
  `j'`, `j` over `g'`, `ḡ'` is cartesian.

## References

* [Stacks Project, Tag 0F7L](https://stacks.math.columbia.edu/tag/0F7L)
* [Stacks Project, Tag 03S6](https://stacks.math.columbia.edu/tag/03S6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u r

namespace AlgebraicGeometry.CompactificationOf

variable {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {g : Y' ⟶ Y} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
  (sq : IsPullback g' f' f g) (j : CompactificationOf (Over.mk f))

/-- The open immersion `X' ⟶ X̄ ×_Y Y'` with components `g' ≫ j` and `f'`. -/
def baseChangeImmersion : X' ⟶ pullback j.toBase g :=
  pullback.lift (g' ≫ j.immersion) f' (by rw [Category.assoc, immersion_toBase]; exact sq.w)

/-- The first component of `baseChangeImmersion` is `g' ≫ j`. -/
@[reassoc (attr := simp)]
lemma baseChangeImmersion_fst :
    baseChangeImmersion sq j ≫ pullback.fst j.toBase g = g' ≫ j.immersion :=
  pullback.lift_fst _ _ _

/-- The second component of `baseChangeImmersion` is `f'`. -/
@[reassoc (attr := simp)]
lemma baseChangeImmersion_snd : baseChangeImmersion sq j ≫ pullback.snd j.toBase g = f' :=
  pullback.lift_snd _ _ _

/-- **The square of the base-changed open immersion is cartesian**: `X'` is the inverse image of
`X` in `X̄ ×_Y Y'`, by the pasting law applied to the cartesian squares `X'` over `X` and
`X̄ ×_Y Y'` over `X̄`. -/
theorem isPullback_baseChangeImmersion :
    IsPullback g' (baseChangeImmersion sq j) j.immersion (pullback.fst j.toBase g) := by
  have hbot : IsPullback (pullback.fst j.toBase g) (pullback.snd j.toBase g) j.toBase g :=
    IsPullback.of_hasPullback j.toBase g
  refine IsPullback.of_bot ?_ (baseChangeImmersion_fst sq j).symm hbot
  rw [baseChangeImmersion_snd, immersion_toBase]
  exact sq

/-- `baseChangeImmersion` is an open immersion, as a base change of `j`. -/
instance isOpenImmersion_baseChangeImmersion : IsOpenImmersion (baseChangeImmersion sq j) :=
  MorphismProperty.of_isPullback (P := @IsOpenImmersion) (isPullback_baseChangeImmersion sq j)
    inferInstance

/-- `baseChangeImmersion` is étale, being an open immersion. -/
instance etale_baseChangeImmersion : Etale (baseChangeImmersion sq j) :=
  inferInstance

/-- **The base change of a compactification along a cartesian square**: for `X'` the base
change of `X` along `g : Y' ⟶ Y`, the open immersion `X' ⟶ X̄ ×_Y Y'` into the base change of
the ambient proper scheme is a compactification of `X'` over `Y'`. -/
def baseChange : CompactificationOf (Over.mk f') where
  obj := StructuredArrow.mk (Y := Over.mk (pullback.snd j.toBase g))
    (Over.homMk (baseChangeImmersion sq j) (baseChangeImmersion_snd sq j))
  property := by
    refine ⟨isOpenImmersion_baseChangeImmersion sq j, ?_⟩
    change IsProper (pullback.snd j.toBase g)
    infer_instance

/-- The ambient scheme of `baseChange` is `X̄ ×_Y Y'`. -/
@[simp]
lemma baseChange_space : (baseChange sq j).space = pullback j.toBase g :=
  rfl

/-- The open immersion of `baseChange` is `baseChangeImmersion`. -/
@[simp]
lemma baseChange_immersion : (baseChange sq j).immersion = baseChangeImmersion sq j :=
  rfl

/-- The structure morphism of `baseChange` is the projection `X̄ ×_Y Y' ⟶ Y'`. -/
@[simp]
lemma baseChange_toBase : (baseChange sq j).toBase = pullback.snd j.toBase g :=
  rfl

/-- The open immersion of `baseChange` is an open immersion. -/
instance isOpenImmersion_baseChange_immersion : IsOpenImmersion (baseChange sq j).immersion :=
  isOpenImmersion_baseChangeImmersion sq j

/-- The square of the base-changed compactification is cartesian. -/
theorem isPullback_baseChange :
    IsPullback g' (baseChange sq j).immersion j.immersion (pullback.fst j.toBase g) :=
  isPullback_baseChangeImmersion sq j

end AlgebraicGeometry.CompactificationOf

namespace Stacks.EtaleCohomology

open AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

attribute [local instance] etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits

variable (Λ : Type r) [Ring Λ] {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {g : Y' ⟶ Y} {g' : X' ⟶ X}
  {f' : X' ⟶ Y'} (sq : IsPullback g' f' f g) (j : CompactificationOf (Over.mk f))

/-- **Extension by zero commutes with inverse image across the base change of a compactification,
on bounded below derived categories** ([Stacks, Tag 03S6]): `(g')⁻¹ ⋙ Rj'_! ≅ Rj_! ⋙ (ḡ')⁻¹`
for `j' : X' ⟶ X̄ ×_Y Y'` the base change of `j` (the immersion of
`AlgebraicGeometry.CompactificationOf.baseChange`) and `ḡ' : X̄ ×_Y Y' ⟶ X̄` the projection. The
underived isomorphism is `Stacks.EtaleCohomology.etaleModuleInverseImageExtensionByZeroIso`;
it derives because inverse image and extension by zero are exact. -/
def etaleModuleDerivedExtensionByZeroBaseChangeIso :
    (etaleModuleInverseImage.{u, r} Λ g').mapDerivedCategoryPlus ⋙
        etaleModuleDerivedExtensionByZero.{u, r} Λ (CompactificationOf.baseChangeImmersion sq j) ≅
      etaleModuleDerivedExtensionByZero.{u, r} Λ j.immersion ⋙
        (etaleModuleInverseImage.{u, r} Λ (pullback.fst j.toBase g)).mapDerivedCategoryPlus :=
  Stacks.Cohomology.BoundedBelowComplexes.derivedBaseChangePlusIso
    (etaleModuleInverseImage.{u, r} Λ g')
    (etaleModuleInverseImage.{u, r} Λ (pullback.fst j.toBase g))
    (etaleModuleExtensionByZero.{u, r} Λ j.immersion)
    (etaleModuleExtensionByZero.{u, r} Λ (CompactificationOf.baseChangeImmersion sq j))
    (etaleModuleInverseImageExtensionByZeroIso.{u, r} Λ
      (CompactificationOf.isPullback_baseChangeImmersion sq j))
    (fun _ _ => Functor.rightAcyclic_of_exact _ _)

end Stacks.EtaleCohomology
