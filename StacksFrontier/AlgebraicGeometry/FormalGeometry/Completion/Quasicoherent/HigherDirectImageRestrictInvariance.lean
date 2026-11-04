module

public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.SchemeRestriction

/-!
# A higher direct image restricted to `V` depends only on the sheaf over `f⁻¹(V)`

Let `f : X ⟶ Y` be a morphism of schemes and `V ⊆ Y` an open, with `U = f⁻¹(V)`. This file
proves that `R ᵖ f_*` restricted to `V` **inverts** every morphism of `𝒪_X`-modules that becomes
an isomorphism after restriction to `U`, and that the unit
`𝒢 ⟶ (j_U)_*(𝒢|_U)` of `AlgebraicGeometry.Scheme.Modules.restrictAdjunction` is such a morphism.

## Main results

* `Stacks.AlgebraicGeometry.SchemeHigherDirectImage.isIso_restrictFunctor_map_rightDerived_map`
  and `…_rightDerivedPlus_map`: if `φ|_U` is an isomorphism then `(R ᵖ f_* φ)|_V` is one.
* `Stacks.AlgebraicGeometry.SchemeHigherDirectImage.isIso_restrictFunctor_map_unit`: the unit of
  `restrictAdjunction U.ι` becomes an isomorphism after restriction to `U`.
* `SchemeHigherDirectImage.isIso_restrictFunctor_map_rightDerivedPlus_unit`: the two combined —
  `(R ᵖ f_*(𝒢 ⟶ (j_U)_*(𝒢|_U)))|_V` is an isomorphism.
* `Stacks.AlgebraicGeometry.SchemeHigherDirectImage.isIso_restrictFunctor_map_unit_of_le`: the
  unit of `restrictAdjunction U.ι` becomes an isomorphism after restriction to any open
  `U' ⊆ U`.

## Main definitions

* `Stacks.AlgebraicGeometry.SchemeHigherDirectImage.extendRestrictLE`: **the comparison
  `(j_U)_*(ℳ|_U) ⟶ (j_{U'})_*(ℳ|_{U'})` for `U' ≤ U`**, with
  `…unit_comp_extendRestrictLE` saying that it carries the unit at `U` to the unit at `U'`.
  This is what makes the action of `ℐⁱ` on `R ᵖ f_*(ℐⁿℱ)` compatible with shrinking the open of
  the base, with no compatibility of [Stacks, Tag 01E5] across nested opens.

## Implementation notes

The only input is that [Stacks, Tag 01E5] holds in the scheme vocabulary **as a natural
isomorphism in the module**, which is
`Stacks.AlgebraicGeometry.SchemeHigherDirectImage.higherDirectImageRestrictIso`. Naturality at
`φ` puts `(R ᵖ f_* φ)|_V` in a commuting square with `R ᵖ (f ∣_ V)_* (φ|_U)`, which is an
isomorphism because `φ|_U` is; the two horizontal maps being isomorphisms, so is the fourth
side. **No compatibility of the comparison across nested opens is used**, and that is the point:
that compatibility is known in the tree only in degree zero
(`Stacks.Cohomology.HigherDirectImage.higherDirectImageRestrictIso_zero_ofLE`), which is why
`Stacks.Blowup.pushforwardReesGradedModule` — the graded `⨁ₙ ℐⁿ`-module structure on
`⨁ₙ R ᵖ f_*(ℐⁿℱ)` of the setup paragraph of [Stacks, Tag 02O7] — exists only for `p = 0`.

These two results are what make the positive-degree structure reachable without that missing
compatibility. A local section `r` of `ℐⁱ` over `V` is not a morphism of sheaves on `X`, but
`𝒢 ↦ (j_U)_*(𝒢|_U)` turns it into one: multiplication by the inverse image of `r`, a section of
`ℐⁱ𝒪_X` over `U`, gives `ℐⁿℱ ⟶ (j_U)_*((ℐⁿ⁺ⁱℱ)|_U)` **on `X`**, so `R ᵖ f_*` may be applied to
it; the unit `ℐⁿ⁺ⁱℱ ⟶ (j_U)_*((ℐⁿ⁺ⁱℱ)|_U)` becomes invertible after restricting to `V` by the
results here, and dividing by it lands the action back in `R ᵖ f_*(ℐⁿ⁺ⁱℱ)`. Compatibility of
that action with shrinking `V` then becomes a statement about restriction of sections, not about
derived functors.

The `ℕ`-indexed form is the one that is proved; the `ℤ`-indexed form for
`CategoryTheory.Functor.rightDerivedPlus` is obtained from it through the naturality of
`Stacks.DerivedIndexing.rightDerivedIso`, since the comparison of the two indexings is itself
natural in the module.

## References

* [Stacks Project, Tag 01E5](https://stacks.math.columbia.edu/tag/01E5)
* [Stacks Project, Tag 02O7](https://stacks.math.columbia.edu/tag/02O7)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

attribute [local instance 100000] HasDerivedCategory.standard

namespace Stacks.AlgebraicGeometry.SchemeHigherDirectImage

/-- If a morphism of `𝒪_X`-modules becomes an isomorphism after restriction to `f⁻¹(V)`, then
the `p`-th higher direct image of it becomes an isomorphism after restriction to `V`.

This is naturality of [Stacks, Tag 01E5] in the module; no compatibility of the comparison
across nested opens is used. -/
public theorem isIso_restrictFunctor_map_rightDerived_map {X Y : Scheme.{u}} (f : X ⟶ Y)
    (V : Y.Opens) (p : ℕ) {G H : X.Modules} (φ : G ⟶ H)
    [IsIso ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).map φ)] :
    IsIso ((Scheme.Modules.restrictFunctor V.ι).map
      (((Scheme.Modules.pushforward f).rightDerived p).map φ)) := by
  have h1 : IsIso ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι ⋙
      (Scheme.Modules.pushforward (f ∣_ V)).rightDerived p).map φ) := by
    show IsIso (((Scheme.Modules.pushforward (f ∣_ V)).rightDerived p).map
      ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).map φ))
    infer_instance
  have hnat := (higherDirectImageRestrictIso f V p).hom.naturality φ
  have h2 : IsIso ((higherDirectImageRestrictIso f V p).hom.app G ≫
      ((Scheme.Modules.pushforward f).rightDerived p ⋙
        Scheme.Modules.restrictFunctor V.ι).map φ) := by
    rw [← hnat]
    infer_instance
  exact IsIso.of_isIso_comp_left
    ((higherDirectImageRestrictIso f V p).hom.app G)
    (((Scheme.Modules.pushforward f).rightDerived p ⋙
      Scheme.Modules.restrictFunctor V.ι).map φ)

/-- `isIso_restrictFunctor_map_rightDerived_map` for the `ℤ`-indexed derived functors, at a
natural-number degree. The two indexings are compared by
`Stacks.DerivedIndexing.rightDerivedIso`, which is natural in the module, so invertibility
transports. -/
public theorem isIso_restrictFunctor_map_rightDerivedPlus_map {X Y : Scheme.{u}} (f : X ⟶ Y)
    (V : Y.Opens) (p : ℕ) {G H : X.Modules} (φ : G ⟶ H)
    [IsIso ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).map φ)] :
    IsIso ((Scheme.Modules.restrictFunctor V.ι).map
      (((Scheme.Modules.pushforward f).rightDerivedPlus (p : ℤ)).map φ)) := by
  have hι := Stacks.DerivedIndexing.rightDerivedIso (Scheme.Modules.pushforward f) p
  have hnat := hι.hom.naturality φ
  have h1 : IsIso ((Scheme.Modules.restrictFunctor V.ι).map
      (((Scheme.Modules.pushforward f).rightDerived p).map φ ≫ hι.hom.app H)) := by
    have := isIso_restrictFunctor_map_rightDerived_map f V p φ
    rw [Functor.map_comp]
    infer_instance
  rw [hnat, Functor.map_comp] at h1
  have := h1
  exact IsIso.of_isIso_comp_left
    ((Scheme.Modules.restrictFunctor V.ι).map (hι.hom.app G))
    ((Scheme.Modules.restrictFunctor V.ι).map
      (((Scheme.Modules.pushforward f).rightDerivedPlus (p : ℤ)).map φ))

/-- The unit `𝒢 ⟶ (j_U)_*(𝒢|_U)` of `AlgebraicGeometry.Scheme.Modules.restrictAdjunction`
becomes an isomorphism after restriction to `U`.

The counit of that adjunction is an isomorphism, and the left triangle identity exhibits the
restricted unit as its inverse. -/
public instance isIso_restrictFunctor_map_unit {X : Scheme.{u}} (U : X.Opens) (G : X.Modules) :
    IsIso ((Scheme.Modules.restrictFunctor U.ι).map
      ((Scheme.Modules.restrictAdjunction U.ι).unit.app G)) := by
  have h := (Scheme.Modules.restrictAdjunction U.ι).left_triangle_components G
  have hc : IsIso ((Scheme.Modules.restrictAdjunction U.ι).counit.app
      ((Scheme.Modules.restrictFunctor U.ι).obj G)) :=
    NatIso.isIso_app_of_isIso _ _
  have h2 : IsIso ((Scheme.Modules.restrictFunctor U.ι).map
        ((Scheme.Modules.restrictAdjunction U.ι).unit.app G) ≫
      (Scheme.Modules.restrictAdjunction U.ι).counit.app
        ((Scheme.Modules.restrictFunctor U.ι).obj G)) := by
    rw [h]
    infer_instance
  have := h2
  exact IsIso.of_isIso_comp_right
    ((Scheme.Modules.restrictFunctor U.ι).map
      ((Scheme.Modules.restrictAdjunction U.ι).unit.app G))
    ((Scheme.Modules.restrictAdjunction U.ι).counit.app
      ((Scheme.Modules.restrictFunctor U.ι).obj G))

/-- **The invertibility that makes the positive-degree action of [Stacks, Tag 02O7]
constructible.** The `p`-th higher direct image of the unit `𝒢 ⟶ (j_{f⁻¹V})_*(𝒢|_{f⁻¹V})`
becomes an isomorphism after restriction to `V`.

Multiplication by a section of `ℐⁱ` over `V` is a morphism of sheaves on `X` with target
`(j_{f⁻¹V})_*((ℐⁿ⁺ⁱℱ)|_{f⁻¹V})` rather than `ℐⁿ⁺ⁱℱ`; this is what divides the discrepancy
away over `V`. -/
public instance isIso_restrictFunctor_map_rightDerivedPlus_unit {X Y : Scheme.{u}} (f : X ⟶ Y)
    (V : Y.Opens) (p : ℕ) (G : X.Modules) :
    IsIso ((Scheme.Modules.restrictFunctor V.ι).map
      (((Scheme.Modules.pushforward f).rightDerivedPlus (p : ℤ)).map
        ((Scheme.Modules.restrictAdjunction (f ⁻¹ᵁ V).ι).unit.app G))) :=
  isIso_restrictFunctor_map_rightDerivedPlus_map f V p _

/-- The unit `𝒢 ⟶ (j_U)_*(𝒢|_U)` becomes an isomorphism after restriction to **any** open
`U' ⊆ U`, not only to `U` itself.

Restriction to `U'` factors as restriction to `U` followed by restriction along the inclusion
`U' ⊆ U` (`AlgebraicGeometry.Scheme.Modules.restrictFunctorComp`), and the first factor already
inverts the unit (`isIso_restrictFunctor_map_unit`); a functor carries isomorphisms to
isomorphisms. This is what makes the comparison `extendRestrictLE` between the extensions from
two nested opens exist. -/
public theorem isIso_restrictFunctor_map_unit_of_le {X : Scheme.{u}} {U U' : X.Opens}
    (h : U' ≤ U) (M : X.Modules) :
    IsIso ((Scheme.Modules.restrictFunctor U'.ι).map
      ((Scheme.Modules.restrictAdjunction U.ι).unit.app M)) := by
  have hcomp : U'.ι = X.homOfLE h ≫ U.ι := (X.homOfLE_ι h).symm
  have : IsOpenImmersion (X.homOfLE h ≫ U.ι) := inferInstance
  set e : Scheme.Modules.restrictFunctor U'.ι ≅
      Scheme.Modules.restrictFunctor U.ι ⋙ Scheme.Modules.restrictFunctor (X.homOfLE h) :=
    Scheme.Modules.restrictFunctorCongr hcomp ≪≫
      Scheme.Modules.restrictFunctorComp (X.homOfLE h) U.ι with he
  have hiso : IsIso ((Scheme.Modules.restrictFunctor U.ι ⋙
      Scheme.Modules.restrictFunctor (X.homOfLE h)).map
      ((Scheme.Modules.restrictAdjunction U.ι).unit.app M)) := by
    show IsIso ((Scheme.Modules.restrictFunctor (X.homOfLE h)).map
      ((Scheme.Modules.restrictFunctor U.ι).map
        ((Scheme.Modules.restrictAdjunction U.ι).unit.app M)))
    have := isIso_restrictFunctor_map_unit U M
    infer_instance
  have hnat := e.hom.naturality ((Scheme.Modules.restrictAdjunction U.ι).unit.app M)
  have h2 : IsIso ((Scheme.Modules.restrictFunctor U'.ι).map
      ((Scheme.Modules.restrictAdjunction U.ι).unit.app M) ≫
      e.hom.app ((Scheme.Modules.restrictFunctor U.ι ⋙
        Scheme.Modules.pushforward U.ι).obj M)) := by
    rw [hnat]
    have := hiso
    infer_instance
  have := h2
  exact IsIso.of_isIso_comp_right
    ((Scheme.Modules.restrictFunctor U'.ι).map
      ((Scheme.Modules.restrictAdjunction U.ι).unit.app M))
    (e.hom.app ((Scheme.Modules.restrictFunctor U.ι ⋙
      Scheme.Modules.pushforward U.ι).obj M))

/-- **The comparison `(j_U)_*(ℳ|_U) ⟶ (j_{U'})_*(ℳ|_{U'})` for nested opens `U' ≤ U`.**

On sections over an open `W` of `X` the two sides are the sections of `ℳ` over `U ⊓ W` and over
`U' ⊓ W`, and this is the restriction between them; it is *defined* through the adjunction
instead, which is what makes `unit_comp_extendRestrictLE` abstract nonsense. Under
`AlgebraicGeometry.Scheme.Modules.restrictAdjunction` at `U'` it corresponds to the inverse of
the restricted unit, which `isIso_restrictFunctor_map_unit_of_le` makes invertible. -/
public def extendRestrictLE {X : Scheme.{u}} {U U' : X.Opens} (h : U' ≤ U) (M : X.Modules) :
    (Scheme.Modules.pushforward U.ι).obj ((Scheme.Modules.restrictFunctor U.ι).obj M) ⟶
      (Scheme.Modules.pushforward U'.ι).obj ((Scheme.Modules.restrictFunctor U'.ι).obj M) :=
  haveI := isIso_restrictFunctor_map_unit_of_le h M
  (Scheme.Modules.restrictAdjunction U'.ι).unit.app
      ((Scheme.Modules.pushforward U.ι).obj ((Scheme.Modules.restrictFunctor U.ι).obj M)) ≫
    (Scheme.Modules.pushforward U'.ι).map
      (inv ((Scheme.Modules.restrictFunctor U'.ι).map
        ((Scheme.Modules.restrictAdjunction U.ι).unit.app M)))

/-- **The comparison of the extensions is compatible with the units.** This is the triangle that
makes `extendRestrictLE` the right map: the unit at `U` followed by it is the unit at `U'`. -/
public theorem unit_comp_extendRestrictLE {X : Scheme.{u}} {U U' : X.Opens} (h : U' ≤ U)
    (M : X.Modules) :
    (Scheme.Modules.restrictAdjunction U.ι).unit.app M ≫ extendRestrictLE h M =
      (Scheme.Modules.restrictAdjunction U'.ι).unit.app M := by
  have := isIso_restrictFunctor_map_unit_of_le h M
  have hnat : (Scheme.Modules.restrictAdjunction U.ι).unit.app M ≫
      (Scheme.Modules.restrictAdjunction U'.ι).unit.app
        ((Scheme.Modules.pushforward U.ι).obj ((Scheme.Modules.restrictFunctor U.ι).obj M)) =
      (Scheme.Modules.restrictAdjunction U'.ι).unit.app M ≫
        (Scheme.Modules.pushforward U'.ι).map ((Scheme.Modules.restrictFunctor U'.ι).map
          ((Scheme.Modules.restrictAdjunction U.ι).unit.app M)) :=
    (Scheme.Modules.restrictAdjunction U'.ι).unit.naturality _
  rw [extendRestrictLE, ← Category.assoc, hnat, Category.assoc, ← Functor.map_comp,
    IsIso.hom_inv_id, CategoryTheory.Functor.map_id]
  exact Category.comp_id _

/-- `isIso_restrictFunctor_map_rightDerivedPlus_unit` in the `ℕ`-indexed derived functors. -/
public instance isIso_restrictFunctor_map_rightDerived_unit {X Y : Scheme.{u}} (f : X ⟶ Y)
    (V : Y.Opens) (p : ℕ) (G : X.Modules) :
    IsIso ((Scheme.Modules.restrictFunctor V.ι).map
      (((Scheme.Modules.pushforward f).rightDerived p).map
        ((Scheme.Modules.restrictAdjunction (f ⁻¹ᵁ V).ι).unit.app G))) :=
  isIso_restrictFunctor_map_rightDerived_map f V p _

end Stacks.AlgebraicGeometry.SchemeHigherDirectImage

end

end
