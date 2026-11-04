module

public import Mathlib.AlgebraicGeometry.FunctionField
public import StacksFrontier.AlgebraicGeometry.InvertiblePullbackFlat.FiberChart

/-!
# The generic fibre on an affine chart, and the unit the penultimate paragraph of Tag 0BD7 needs

`StacksFrontier/AlgebraicGeometry/InvertiblePullbackFlat/StalkGenerator.lean` proves the penultimate
paragraph of Stacks Tag 0BD7 at a point from two inputs: that every fibre ring
`Ideal.Fiber 𝔭 𝒪_{X, x}` of `𝒪_{Y, y} → 𝒪_{X, x}` is a domain, and that the germ of the
meromorphic section is a **unit** of the one fibre ring `Ideal.Fiber ⊥ 𝒪_{X, x}` — the source's
`A ⊗_R K`, by `Ideal.fiberBotRingEquivOfIsLocalization`. The first input is discharged in
`StacksFrontier/AlgebraicGeometry/InvertiblePullbackFlat/FiberChart.lean`. The second is the subject
of this file, and what is proved here is the reduction of it to a statement about an **affine open
of the generic fibre** rather than about a germ.

Two things are done.

* `Spec (Ideal.Fiber 𝔮 Γ(X, U))` is exhibited as an open subscheme of the scheme-theoretic fibre
  `f.fiber y'`, for affine opens `U ≤ f ⁻¹ᵁ V` and `𝔮` a prime of `Γ(Y, V)` with `y'` the
  corresponding point of `V` (`AlgebraicGeometry.fiberAppLEι`,
  `AlgebraicGeometry.isOpenImmersion_fiberAppLEι`). At `𝔮 = ⊥` the point `y'` is the generic
  point of an integral `Y` (`AlgebraicGeometry.fromSpec_eq_genericPoint_of_asIdeal_eq_bot`), so
  `Ideal.Fiber ⊥ Γ(X, U)` is the ring of an affine open of the **generic fibre** `X_ξ`
  (`AlgebraicGeometry.genericFiberChartι`). That open is nonempty for a flat `f`
  (`AlgebraicGeometry.nontrivial_fiberBot_appLE`).

* The unit may then be produced on the chart and transported to the stalk: the four algebra maps
  of the chart square give a ring homomorphism
  `Ideal.Fiber ⊥ Γ(X, U) → Ideal.Fiber ⊥ 𝒪_{X, x}`
  (`AlgebraicGeometry.chartFiberBotToStalkFiberBot`), under which a unit stays a unit. With it,
  the conclusion of the penultimate paragraph of Stacks Tag 0BD7 at the point `x` — nonzero
  `g, r ∈ 𝒪_{Y, f x}` and a unit `u` of `𝒪_{X, x}` with `r s = g u` — follows from the single
  hypothesis that the given element of `Ideal.Fiber ⊥ Γ(X, U)` is a unit
  (`AlgebraicGeometry.exists_isUnit_mul_eq_of_isUnit_fiberBot_chart`).

So the unit is asked for in `Ideal.Fiber ⊥ Γ(X, U)` — by the first item the ring of *global
sections* of an affine open of `X_ξ` — rather than in the ring of germs `Ideal.Fiber ⊥ 𝒪_{X, x}`.
Assumption (5) of the tag is a global trivialization of `ℒ` on `X_ξ`, so the restriction of a
trivializing section to that affine open is an element of exactly that ring. The unit itself is
`AlgebraicGeometry.isUnit_genericFiberChartCoord`, built from
`Stacks.SheafOfModules.exists_isUnit_smul_eq_generator_of_subset_generatingLocus`,
`AlgebraicGeometry.bijective_genericFiberChartSections` and
`AlgebraicGeometry.genericFiberChartGenerator`.

## Main definitions

* `AlgebraicGeometry.fiberAppLEIsoFiberComp`: the fibre of `Spec Γ(X, U) → Spec Γ(Y, V)` is the
  fibre of `Spec Γ(X, U) → X → Y`.
* `AlgebraicGeometry.fiberAppLEι`: the resulting morphism
  `Spec (Ideal.Fiber 𝔮 Γ(X, U)) ⟶ f.fiber (hV.fromSpec 𝔮)`.
* `AlgebraicGeometry.fiberChartι`: the same with the point of `Y` an explicit argument carrying
  its own equation, which is the form a consumer holding a *named* point can apply.
* `AlgebraicGeometry.genericFiberChartι`: the case `𝔮 = ⊥` of an integral `Y`, landing in the
  generic fibre.
* `Ideal.fiberMapOfIsLocalization`: the map of fibre rings along a localization of the base and
  an algebra map upstairs.
* `AlgebraicGeometry.chartFiberBotToStalkFiberBot`: that map for the chart square of a morphism of
  schemes, from `Ideal.Fiber ⊥ Γ(X, U)` to `Ideal.Fiber ⊥ 𝒪_{X, x}`.

## Main results

* `AlgebraicGeometry.isOpenImmersion_fiberAppLEι` and
  `AlgebraicGeometry.isOpenImmersion_fiberChartι`: those morphisms are open immersions.
* `AlgebraicGeometry.fromSpec_eq_genericPoint_of_asIdeal_eq_bot`: on an integral scheme the zero
  prime of an affine chart is the generic point.
* `Ideal.fiberMapOfIsLocalization_one_tmul` and
  `AlgebraicGeometry.chartFiberBotToStalkFiberBot_one_tmul`: the defining equation of those two
  maps, on the image of the algebra upstairs — which, the target being a localization of that
  algebra, determines them.
* `AlgebraicGeometry.nontrivial_fiberBot_appLE`: for a flat `f` the chart's generic fibre ring is
  nonzero, so the affine open above is nonempty.
* `AlgebraicGeometry.exists_isUnit_mul_eq_of_isUnit_fiberBot_chart`: the conclusion of the
  penultimate paragraph of Stacks Tag 0BD7 at a point, with a unit of the chart's generic fibre
  ring as its only hypothesis beyond the tag's own.

## Implementation notes

The prime `𝔮` of `AlgebraicGeometry.fromSpec_eq_genericPoint_of_asIdeal_eq_bot` is an arbitrary
`PrimeSpectrum Γ(Y, V)` with its own equation `𝔮.asIdeal = ⊥` rather than being written `⊥` in
place: `(⊥ : PrimeSpectrum Γ(Y, V))` exists only once `Γ(Y, V)` is known to be a domain, which
needs `V` nonempty, and stating the hypothesis as an equation keeps that out of the statement.
The same device makes `AlgebraicGeometry.fiberChartι` applicable at a named point: with the point
a variable and its equation a hypothesis, the open-immersion proof is `subst` followed by
`AlgebraicGeometry.isOpenImmersion_fiberAppLEι`, where a statement written at
`hV.fromSpec 𝔮` would need a transport that changes the fibre scheme itself.

`Ideal.fiberMapOfIsLocalization` likewise takes the contracted prime `𝔮` of `T` with its equation
`𝔭.comap (algebraMap T R) = 𝔮`, for the reason recorded in
`StacksFrontier/AlgebraicGeometry/InvertiblePullbackFlat/FiberLocalization.lean`: `[𝔮.IsPrime]`
depends on `𝔮`, so a consumer with its own name for the contraction cannot rewrite the equation
into the statement. Here the equation is also what makes the `⊥` case available, since
`(⊥ : Ideal R).comap (algebraMap T R) = ⊥` is `Ideal.comap_bot_of_injective` applied to the
injectivity of a germ on an integral scheme (`AlgebraicGeometry.germ_injective_of_isIntegral`).

`AlgebraicGeometry.IsOpenImmersion.of_isIso` does not fire as an instance here, so the two
isomorphisms in front of `AlgebraicGeometry.fiberCompι` are absorbed by
`CategoryTheory.MorphismProperty.RespectsIso.precomp` with the isomorphism passed explicitly, as
in `StacksFrontier/AlgebraicGeometry/InvertiblePullbackFlat/FiberChart.lean`.

`AlgebraicGeometry.nontrivial_fiberBot_appLE` is proved from the ring homomorphism of this file
rather than by a second descent argument: a ring mapping to a nonzero ring is nonzero
(`RingHom.domain_nontrivial`), and the stalk's generic fibre ring is nonzero by
`AlgebraicGeometry.nontrivial_fiber_stalkMap_of_flat`. Geometrically this is the observation of
`FiberChart.lean` that a generalization of `x` lies in every open containing `x`.

## References

* [Stacks Project, Tag 0BD7](https://stacks.math.columbia.edu/tag/0BD7)
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite TopologicalSpace Algebra TensorProduct

namespace Ideal

/-- **The map of fibre rings along a localization of the base.** Let `R` be a localization of `T`
at `N`, let `A` be a `T`-algebra and an `S`-algebra and an `R`-algebra compatibly, let `𝔭` be a
prime of `R` and `𝔮` its contraction to `T`. Then `Ideal.Fiber 𝔮 S` maps to `Ideal.Fiber 𝔭 A`.

Two steps: `Algebra.TensorProduct.lTensor` of `S → A` over the residue field of `𝔮` gives
`Ideal.Fiber 𝔮 S → Ideal.Fiber 𝔮 A`, and `Ideal.fiberComapRingEquivOfIsLocalization` identifies
`Ideal.Fiber 𝔮 A` with `Ideal.Fiber 𝔭 A` — localizing the base does not change a fibre ring. -/
noncomputable def fiberMapOfIsLocalization
    {T S R A : Type u} [CommRing T] [CommRing S] [CommRing R] [CommRing A]
    [Algebra T S] [Algebra T R] [Algebra R A] [Algebra T A] [Algebra S A]
    [IsScalarTower T R A] [IsScalarTower T S A]
    (N : Submonoid T) [IsLocalization N R]
    (p : Ideal R) [p.IsPrime] (q : Ideal T) [q.IsPrime]
    (hq : p.comap (algebraMap T R) = q) :
    q.Fiber S →+* p.Fiber A := by
  subst hq
  let φ : (p.comap (algebraMap T R)).Fiber S →ₐ[(p.comap (algebraMap T R)).ResidueField]
      (p.comap (algebraMap T R)).Fiber A :=
    Algebra.TensorProduct.lTensor _ (IsScalarTower.toAlgHom T S A)
  exact (fiberComapRingEquivOfIsLocalization (A := A) N p).toRingHom.comp φ.toRingHom

/-- **The defining equation of `Ideal.fiberMapOfIsLocalization`**: on the image of `S` in
`Ideal.Fiber 𝔮 S` it is the algebra map `S → A`. Since `Ideal.Fiber 𝔭 A` is a localization of `A`
at the image of `T`, this one equation determines the map. -/
theorem fiberMapOfIsLocalization_one_tmul
    {T S R A : Type u} [CommRing T] [CommRing S] [CommRing R] [CommRing A]
    [Algebra T S] [Algebra T R] [Algebra R A] [Algebra T A] [Algebra S A]
    [IsScalarTower T R A] [IsScalarTower T S A]
    (N : Submonoid T) [IsLocalization N R]
    (p : Ideal R) [p.IsPrime] (q : Ideal T) [q.IsPrime]
    (hq : p.comap (algebraMap T R) = q) (s : S) :
    fiberMapOfIsLocalization N p q hq ((1 : q.ResidueField) ⊗ₜ[T] s)
      = (1 : p.ResidueField) ⊗ₜ[R] (algebraMap S A s) := by
  subst hq
  show fiberComapRingEquivOfIsLocalization N p
      (Algebra.TensorProduct.lTensor (p.comap (algebraMap T R)).ResidueField
        (IsScalarTower.toAlgHom T S A) ((1 : (p.comap (algebraMap T R)).ResidueField) ⊗ₜ[T] s))
    = _
  rw [Algebra.TensorProduct.lTensor, Algebra.TensorProduct.map_tmul]
  exact fiberComapRingEquivOfIsLocalization_one_tmul N p _

end Ideal

namespace AlgebraicGeometry

/-- **The fibre of `Spec Γ(X, U) → Spec Γ(Y, V)` is the fibre of `Spec Γ(X, U) → X → Y`.** The
two morphisms `Spec.map (f.appLE V U e) ≫ hV.fromSpec` and `hU.fromSpec ≫ f` are equal
(`AlgebraicGeometry.IsAffineOpen.SpecMap_appLE_fromSpec`), and an open immersion on the target
does not change a fibre (`AlgebraicGeometry.fiberCompIsoFiber`). -/
noncomputable def fiberAppLEIsoFiberComp {X Y : Scheme.{u}} (f : X ⟶ Y)
    {V : Y.Opens} {U : X.Opens} (hV : IsAffineOpen V) (hU : IsAffineOpen U) (e : U ≤ f ⁻¹ᵁ V)
    (q : PrimeSpectrum ↑Γ(Y, V)) :
    (Spec.map (f.appLE V U e)).fiber q ≅ (hU.fromSpec ≫ f).fiber (hV.fromSpec q) :=
  IsAffineOpen.SpecMap_appLE_fromSpec f hV hU e ▸
    fiberCompIsoFiber (Spec.map (f.appLE V U e)) hV.fromSpec q

/-- **The fibre ring of an affine chart, as a subscheme of the fibre.** For affine opens
`U ≤ f ⁻¹ᵁ V` and a prime `𝔮` of `Γ(Y, V)`, the canonical morphism
`Spec (Ideal.Fiber 𝔮 Γ(X, U)) ⟶ f.fiber (hV.fromSpec 𝔮)`: the fibre of
`Spec Γ(X, U) → Spec Γ(Y, V)` is that spectrum
(`AlgebraicGeometry.specMapFiberIsoSpecFiberRing`), it is the fibre of
`Spec Γ(X, U) → X → Y` (`AlgebraicGeometry.fiberAppLEIsoFiberComp`), and the fibre of a composite
with an open immersion in front maps to the fibre of the second factor
(`AlgebraicGeometry.fiberCompι`). -/
noncomputable def fiberAppLEι {X Y : Scheme.{u}} (f : X ⟶ Y)
    {V : Y.Opens} {U : X.Opens} (hV : IsAffineOpen V) (hU : IsAffineOpen U) (e : U ≤ f ⁻¹ᵁ V)
    (q : PrimeSpectrum ↑Γ(Y, V)) :
    letI : Algebra ↑Γ(Y, V) ↑Γ(X, U) := (f.appLE V U e).hom.toAlgebra
    Spec (CommRingCat.of (q.asIdeal.Fiber ↑Γ(X, U))) ⟶ f.fiber (hV.fromSpec q) :=
  letI : Algebra ↑Γ(Y, V) ↑Γ(X, U) := (f.appLE V U e).hom.toAlgebra
  (specMapFiberIsoSpecFiberRing (R := ↑Γ(Y, V)) (S := ↑Γ(X, U)) q).inv ≫
    (fiberAppLEIsoFiberComp f hV hU e q).hom ≫ fiberCompι hU.fromSpec f (hV.fromSpec q)

/-- **`AlgebraicGeometry.fiberAppLEι` is an open immersion**, being
`AlgebraicGeometry.fiberCompι` of an open immersion preceded by two isomorphisms. -/
theorem isOpenImmersion_fiberAppLEι {X Y : Scheme.{u}} (f : X ⟶ Y)
    {V : Y.Opens} {U : X.Opens} (hV : IsAffineOpen V) (hU : IsAffineOpen U) (e : U ≤ f ⁻¹ᵁ V)
    (q : PrimeSpectrum ↑Γ(Y, V)) :
    letI : Algebra ↑Γ(Y, V) ↑Γ(X, U) := (f.appLE V U e).hom.toAlgebra
    IsOpenImmersion (fiberAppLEι f hV hU e q) :=
  let : Algebra ↑Γ(Y, V) ↑Γ(X, U) := (f.appLE V U e).hom.toAlgebra
  MorphismProperty.RespectsIso.precomp @IsOpenImmersion
    (specMapFiberIsoSpecFiberRing (R := ↑Γ(Y, V)) (S := ↑Γ(X, U)) q).inv
    ((fiberAppLEIsoFiberComp f hV hU e q).hom ≫ fiberCompι hU.fromSpec f (hV.fromSpec q))
    (MorphismProperty.RespectsIso.precomp @IsOpenImmersion
      (fiberAppLEIsoFiberComp f hV hU e q).hom
      (fiberCompι hU.fromSpec f (hV.fromSpec q))
      (isOpenImmersion_fiberCompι hU.fromSpec f (hV.fromSpec q)))

/-- **`AlgebraicGeometry.fiberAppLEι` at a named point of the target.** The point is a variable
with its own equation `hV.fromSpec 𝔮 = y`, so that a consumer holding a point of `Y` — the
generic point, say — can apply the morphism without transporting along an equality of points,
which would change the fibre scheme. -/
noncomputable def fiberChartι {X Y : Scheme.{u}} (f : X ⟶ Y)
    {V : Y.Opens} {U : X.Opens} (hV : IsAffineOpen V) (hU : IsAffineOpen U) (e : U ≤ f ⁻¹ᵁ V)
    (q : PrimeSpectrum ↑Γ(Y, V)) (y : Y) (hy : hV.fromSpec q = y) :
    letI : Algebra ↑Γ(Y, V) ↑Γ(X, U) := (f.appLE V U e).hom.toAlgebra
    Spec (CommRingCat.of (q.asIdeal.Fiber ↑Γ(X, U))) ⟶ f.fiber y :=
  letI : Algebra ↑Γ(Y, V) ↑Γ(X, U) := (f.appLE V U e).hom.toAlgebra
  hy ▸ fiberAppLEι f hV hU e q

/-- **`AlgebraicGeometry.fiberChartι` is an open immersion.** With the point a variable the
equation substitutes away and this is `AlgebraicGeometry.isOpenImmersion_fiberAppLEι`. -/
theorem isOpenImmersion_fiberChartι {X Y : Scheme.{u}} (f : X ⟶ Y)
    {V : Y.Opens} {U : X.Opens} (hV : IsAffineOpen V) (hU : IsAffineOpen U) (e : U ≤ f ⁻¹ᵁ V)
    (q : PrimeSpectrum ↑Γ(Y, V)) (y : Y) (hy : hV.fromSpec q = y) :
    letI : Algebra ↑Γ(Y, V) ↑Γ(X, U) := (f.appLE V U e).hom.toAlgebra
    IsOpenImmersion (fiberChartι f hV hU e q y hy) := by
  let _ : Algebra ↑Γ(Y, V) ↑Γ(X, U) := (f.appLE V U e).hom.toAlgebra
  subst hy
  exact isOpenImmersion_fiberAppLEι f hV hU e q

/-- **On an integral scheme the zero prime of an affine chart is the generic point.** For `V` an
affine open containing a point and `𝔮` a prime of `Γ(Y, V)` with `𝔮.asIdeal = ⊥`, the point
`hV.fromSpec 𝔮` of `Y` is the generic point: on the affine scheme `Spec Γ(Y, V)` the generic
point is `⊥` (`AlgebraicGeometry.genericPoint_eq_bot_of_affine`, `Γ(Y, V)` being a domain), and
the generic point of a nonempty open is the generic point of the whole scheme
(`AlgebraicGeometry.IsAffineOpen.primeIdealOf_genericPoint`). -/
theorem fromSpec_eq_genericPoint_of_asIdeal_eq_bot {Y : Scheme.{u}} [IsIntegral Y]
    {V : Y.Opens} (hV : IsAffineOpen V) {y : Y} (hy : y ∈ V)
    (q : PrimeSpectrum ↑Γ(Y, V)) (hq : q.asIdeal = ⊥) :
    hV.fromSpec q = genericPoint Y := by
  have _ : Nonempty ↥(V.toScheme) := ⟨⟨y, hy⟩⟩
  have _ : IsDomain ↑Γ(Y, V) := IsIntegral.component_integral V
  rw [show q = ⊥ from PrimeSpectrum.ext hq, ← genericPoint_eq_bot_of_affine (Γ(Y, V)),
    ← hV.primeIdealOf_genericPoint, hV.fromSpec_primeIdealOf]

/-- **The chart's generic fibre ring is the ring of an affine open of the generic fibre.** For
affine opens `x ∈ U ≤ f ⁻¹ᵁ V` of a morphism to an integral scheme, this is the canonical
morphism `Spec (Ideal.Fiber ⊥ Γ(X, U)) ⟶ X_ξ`, an open immersion by
`AlgebraicGeometry.isOpenImmersion_genericFiberChartι`.

This is why assumption (5) of Stacks Tag 0BD7 bears on `Ideal.Fiber ⊥ Γ(X, U)` at all: a
trivializing section of `ℒ` on `X_ξ` restricts to this affine open. -/
noncomputable def genericFiberChartι {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegral Y] {x : X}
    {V : Y.Opens} {U : X.Opens} (hV : IsAffineOpen V) (hU : IsAffineOpen U) (e : U ≤ f ⁻¹ᵁ V)
    (hx : x ∈ U) :
    letI : Algebra ↑Γ(Y, V) ↑Γ(X, U) := (f.appLE V U e).hom.toAlgebra
    letI : Nonempty ↥(V.toScheme) := ⟨⟨f x, e hx⟩⟩
    letI : IsDomain ↑Γ(Y, V) := IsIntegral.component_integral V
    Spec (CommRingCat.of ((⊥ : Ideal ↑Γ(Y, V)).Fiber ↑Γ(X, U))) ⟶ f.fiber (genericPoint Y) :=
  letI : Algebra ↑Γ(Y, V) ↑Γ(X, U) := (f.appLE V U e).hom.toAlgebra
  letI : Nonempty ↥(V.toScheme) := ⟨⟨f x, e hx⟩⟩
  letI : IsDomain ↑Γ(Y, V) := IsIntegral.component_integral V
  fiberChartι f hV hU e (⊥ : PrimeSpectrum ↑Γ(Y, V)) (genericPoint Y)
    (fromSpec_eq_genericPoint_of_asIdeal_eq_bot hV (e hx) (⊥ : PrimeSpectrum ↑Γ(Y, V)) rfl)

/-- **`AlgebraicGeometry.genericFiberChartι` is an open immersion.** -/
theorem isOpenImmersion_genericFiberChartι {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegral Y] {x : X}
    {V : Y.Opens} {U : X.Opens} (hV : IsAffineOpen V) (hU : IsAffineOpen U) (e : U ≤ f ⁻¹ᵁ V)
    (hx : x ∈ U) :
    letI : Algebra ↑Γ(Y, V) ↑Γ(X, U) := (f.appLE V U e).hom.toAlgebra
    letI : Nonempty ↥(V.toScheme) := ⟨⟨f x, e hx⟩⟩
    letI : IsDomain ↑Γ(Y, V) := IsIntegral.component_integral V
    IsOpenImmersion (genericFiberChartι f hV hU e hx) :=
  let : Algebra ↑Γ(Y, V) ↑Γ(X, U) := (f.appLE V U e).hom.toAlgebra
  have : Nonempty ↥(V.toScheme) := ⟨⟨f x, e hx⟩⟩
  have : IsDomain ↑Γ(Y, V) := IsIntegral.component_integral V
  isOpenImmersion_fiberChartι f hV hU e (⊥ : PrimeSpectrum ↑Γ(Y, V)) (genericPoint Y)
    (fromSpec_eq_genericPoint_of_asIdeal_eq_bot hV (e hx) (⊥ : PrimeSpectrum ↑Γ(Y, V)) rfl)

/-- **The chart square's map of generic fibre rings.** For affine opens `x ∈ U ≤ f ⁻¹ᵁ V` of a
morphism to an integral scheme, a ring homomorphism
`Ideal.Fiber ⊥ Γ(X, U) → Ideal.Fiber ⊥ 𝒪_{X, x}`.

The four algebra structures of the chart and the two scalar towers are built here exactly as in
`AlgebraicGeometry.forall_isDomain_fiber_stalkMap_of_chart`, the agreement of the towers being
`AlgebraicGeometry.germ_stalkMap_appLE`; the map itself is
`Ideal.fiberMapOfIsLocalization` at the localization `Γ(Y, V) → 𝒪_{Y, f x}`, whose contraction of
`⊥` is `⊥` because a germ on an integral scheme is injective. -/
noncomputable def chartFiberBotToStalkFiberBot {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegral Y]
    {x : X} {V : Y.Opens} {U : X.Opens} (hV : IsAffineOpen V) (e : U ≤ f ⁻¹ᵁ V) (hx : x ∈ U) :
    letI : Algebra ↑Γ(Y, V) ↑Γ(X, U) := (f.appLE V U e).hom.toAlgebra
    letI : Algebra ↑(Y.presheaf.stalk (f x)) ↑(X.presheaf.stalk x) :=
      (f.stalkMap x).hom.toAlgebra
    letI : Nonempty ↥(V.toScheme) := ⟨⟨f x, e hx⟩⟩
    letI : IsDomain ↑Γ(Y, V) := IsIntegral.component_integral V
    (⊥ : Ideal ↑Γ(Y, V)).Fiber ↑Γ(X, U) →+*
      (⊥ : Ideal ↑(Y.presheaf.stalk (f x))).Fiber ↑(X.presheaf.stalk x) := by
  letI : Algebra ↑Γ(Y, V) ↑Γ(X, U) := (f.appLE V U e).hom.toAlgebra
  letI : Algebra ↑(Y.presheaf.stalk (f x)) ↑(X.presheaf.stalk x) :=
    (f.stalkMap x).hom.toAlgebra
  letI : Nonempty ↥(V.toScheme) := ⟨⟨f x, e hx⟩⟩
  letI : IsDomain ↑Γ(Y, V) := IsIntegral.component_integral V
  letI : Algebra ↑Γ(Y, V) ↑(Y.presheaf.stalk (f x)) :=
    Y.presheaf.algebra_section_stalk ⟨f x, e hx⟩
  letI : Algebra ↑Γ(X, U) ↑(X.presheaf.stalk x) :=
    X.presheaf.algebra_section_stalk ⟨x, hx⟩
  letI : Algebra ↑Γ(Y, V) ↑(X.presheaf.stalk x) :=
    ((Y.presheaf.germ V (f x) (e hx)) ≫ f.stalkMap x).hom.toAlgebra
  haveI : IsScalarTower ↑Γ(Y, V) ↑(Y.presheaf.stalk (f x)) ↑(X.presheaf.stalk x) :=
    IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower ↑Γ(Y, V) ↑Γ(X, U) ↑(X.presheaf.stalk x) :=
    IsScalarTower.of_algebraMap_eq' (by
      change (((Y.presheaf.germ V (f x) (e hx)) ≫ f.stalkMap x)).hom =
        (X.presheaf.germ U x hx).hom.comp (f.appLE V U e).hom
      rw [germ_stalkMap_appLE]
      rfl)
  haveI := hV.isLocalization_stalk ⟨f x, e hx⟩
  have hinj : Function.Injective (algebraMap ↑Γ(Y, V) ↑(Y.presheaf.stalk (f x))) :=
    germ_injective_of_isIntegral (X := Y) (U := V) (f x) (e hx)
  exact Ideal.fiberMapOfIsLocalization
    (hV.primeIdealOf ⟨f x, e hx⟩).asIdeal.primeCompl
    (⊥ : Ideal ↑(Y.presheaf.stalk (f x))) (⊥ : Ideal ↑Γ(Y, V))
    (Ideal.comap_bot_of_injective _ hinj)

/-- **The defining equation of `AlgebraicGeometry.chartFiberBotToStalkFiberBot`**: on the image
of `Γ(X, U)` in the chart's generic fibre ring it is the germ at `x`. By
`Ideal.fiberMapOfIsLocalization_one_tmul`, since the map is that one. -/
theorem chartFiberBotToStalkFiberBot_one_tmul {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegral Y]
    {x : X} {V : Y.Opens} {U : X.Opens} (hV : IsAffineOpen V) (e : U ≤ f ⁻¹ᵁ V) (hx : x ∈ U)
    (a : ↑Γ(X, U)) :
    letI : Algebra ↑Γ(Y, V) ↑Γ(X, U) := (f.appLE V U e).hom.toAlgebra
    letI : Algebra ↑(Y.presheaf.stalk (f x)) ↑(X.presheaf.stalk x) :=
      (f.stalkMap x).hom.toAlgebra
    letI : Nonempty ↥(V.toScheme) := ⟨⟨f x, e hx⟩⟩
    letI : IsDomain ↑Γ(Y, V) := IsIntegral.component_integral V
    chartFiberBotToStalkFiberBot f hV e hx
        ((1 : (⊥ : Ideal ↑Γ(Y, V)).ResidueField) ⊗ₜ[↑Γ(Y, V)] a)
      = (1 : (⊥ : Ideal ↑(Y.presheaf.stalk (f x))).ResidueField)
          ⊗ₜ[↑(Y.presheaf.stalk (f x))] ((X.presheaf.germ U x hx).hom a) := by
  let : Algebra ↑Γ(Y, V) ↑Γ(X, U) := (f.appLE V U e).hom.toAlgebra
  let : Algebra ↑(Y.presheaf.stalk (f x)) ↑(X.presheaf.stalk x) :=
    (f.stalkMap x).hom.toAlgebra
  let : Nonempty ↥(V.toScheme) := ⟨⟨f x, e hx⟩⟩
  let : IsDomain ↑Γ(Y, V) := IsIntegral.component_integral V
  let : Algebra ↑Γ(Y, V) ↑(Y.presheaf.stalk (f x)) :=
    Y.presheaf.algebra_section_stalk ⟨f x, e hx⟩
  let : Algebra ↑Γ(X, U) ↑(X.presheaf.stalk x) :=
    X.presheaf.algebra_section_stalk ⟨x, hx⟩
  let : Algebra ↑Γ(Y, V) ↑(X.presheaf.stalk x) :=
    ((Y.presheaf.germ V (f x) (e hx)) ≫ f.stalkMap x).hom.toAlgebra
  have : IsScalarTower ↑Γ(Y, V) ↑(Y.presheaf.stalk (f x)) ↑(X.presheaf.stalk x) :=
    IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower ↑Γ(Y, V) ↑Γ(X, U) ↑(X.presheaf.stalk x) :=
    IsScalarTower.of_algebraMap_eq' (by
      show (((Y.presheaf.germ V (f x) (e hx)) ≫ f.stalkMap x)).hom =
        (X.presheaf.germ U x hx).hom.comp (f.appLE V U e).hom
      rw [germ_stalkMap_appLE]
      rfl)
  have := hV.isLocalization_stalk ⟨f x, e hx⟩
  exact Ideal.fiberMapOfIsLocalization_one_tmul _ _ _ _ a

/-- **The chart's generic fibre ring is nonzero, for a flat morphism.** It maps to the generic
fibre ring of `𝒪_{Y, f x} → 𝒪_{X, x}`, which is nonzero by
`AlgebraicGeometry.nontrivial_fiber_stalkMap_of_flat`, and a ring that maps to a nonzero ring is
nonzero. Equivalently, the affine open `Spec (Ideal.Fiber ⊥ Γ(X, U))` of the generic fibre is
nonempty: some generalization of `x` lies over the generic point, and it lies in `U`. -/
theorem nontrivial_fiberBot_appLE {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] [IsIntegral Y] {x : X}
    {V : Y.Opens} {U : X.Opens} (hV : IsAffineOpen V) (e : U ≤ f ⁻¹ᵁ V) (hx : x ∈ U) :
    letI : Algebra ↑Γ(Y, V) ↑Γ(X, U) := (f.appLE V U e).hom.toAlgebra
    letI : Nonempty ↥(V.toScheme) := ⟨⟨f x, e hx⟩⟩
    letI : IsDomain ↑Γ(Y, V) := IsIntegral.component_integral V
    Nontrivial ((⊥ : Ideal ↑Γ(Y, V)).Fiber ↑Γ(X, U)) := by
  let _ : Algebra ↑Γ(Y, V) ↑Γ(X, U) := (f.appLE V U e).hom.toAlgebra
  let _ : Algebra ↑(Y.presheaf.stalk (f x)) ↑(X.presheaf.stalk x) :=
    (f.stalkMap x).hom.toAlgebra
  let _ : Nonempty ↥(V.toScheme) := ⟨⟨f x, e hx⟩⟩
  let _ : IsDomain ↑Γ(Y, V) := IsIntegral.component_integral V
  have _ : Nontrivial ((⊥ : Ideal ↑(Y.presheaf.stalk (f x))).Fiber ↑(X.presheaf.stalk x)) :=
    nontrivial_fiber_stalkMap_of_flat f x (⊥ : Ideal ↑(Y.presheaf.stalk (f x)))
  exact (chartFiberBotToStalkFiberBot f hV e hx).domain_nontrivial

/-- **The penultimate paragraph of Stacks Tag 0BD7 at a point, from a unit on the chart.** Let
`f : X → Y` be flat with integral fibres, `X` locally Noetherian and integral, `Y` locally
Noetherian, integral and normal — hypotheses (1), (2) and (3) of the tag, with the integrality of
`X` that the tag derives from them. Let `x ∈ U ≤ f ⁻¹ᵁ V` be an affine chart at `x`. Then for
every **unit** `b` of the chart's generic fibre ring `Ideal.Fiber ⊥ Γ(X, U)` there are nonzero
`g, r ∈ 𝒪_{Y, f x}` and a unit `u` of `𝒪_{X, x}` with `r b = g u` in `Ideal.Fiber ⊥ 𝒪_{X, x}` —
the source's "there exists `g ∈ R(Y)^*` such that `φ^*(g) s` generates `ℒ_x`", with `s` the image
of `b`.

The unit is transported to the stalk by `AlgebraicGeometry.chartFiberBotToStalkFiberBot`, the
primality input is `AlgebraicGeometry.forall_isDomain_fiber_stalkMap`, and the conclusion is
`Ideal.exists_isUnit_mul_eq_of_isDomain_fiber` at `R = 𝒪_{Y, f x}`, `A = 𝒪_{X, x}` and
`B = Ideal.Fiber ⊥ 𝒪_{X, x}`, which is a localization of `𝒪_{X, x}` at the image of the nonzero
elements of `𝒪_{Y, f x}` by `IsLocalization.tensorRight`.

By `AlgebraicGeometry.genericFiberChartι` the hypothesis on `b` is about an affine open of the
generic fibre `X_ξ`, where assumption (5) of the tag lives, rather than about a germ. -/
theorem exists_isUnit_mul_eq_of_isUnit_fiberBot_chart {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f]
    [IsIntegral X] [IsIntegral Y] [IsNormal Y] [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (hfib : ∀ y : Y, IsIntegral (f.fiber y))
    {x : X} {V : Y.Opens} {U : X.Opens} (hV : IsAffineOpen V) (e : U ≤ f ⁻¹ᵁ V) (hx : x ∈ U) :
    letI : Algebra ↑Γ(Y, V) ↑Γ(X, U) := (f.appLE V U e).hom.toAlgebra
    letI : Algebra ↑(Y.presheaf.stalk (f x)) ↑(X.presheaf.stalk x) :=
      (f.stalkMap x).hom.toAlgebra
    letI : Nonempty ↥(V.toScheme) := ⟨⟨f x, e hx⟩⟩
    letI : IsDomain ↑Γ(Y, V) := IsIntegral.component_integral V
    letI : Algebra ↑(X.presheaf.stalk x)
        ((⊥ : Ideal ↑(Y.presheaf.stalk (f x))).Fiber ↑(X.presheaf.stalk x)) :=
      Algebra.TensorProduct.rightAlgebra
    ∀ b : (⊥ : Ideal ↑Γ(Y, V)).Fiber ↑Γ(X, U), IsUnit b →
      ∃ (g r : ↑(Y.presheaf.stalk (f x))) (u : ↑(X.presheaf.stalk x)),
        g ≠ 0 ∧ r ≠ 0 ∧ IsUnit u ∧
          algebraMap ↑(Y.presheaf.stalk (f x))
                ((⊥ : Ideal ↑(Y.presheaf.stalk (f x))).Fiber ↑(X.presheaf.stalk x)) r
              * chartFiberBotToStalkFiberBot f hV e hx b =
            algebraMap ↑(Y.presheaf.stalk (f x))
                ((⊥ : Ideal ↑(Y.presheaf.stalk (f x))).Fiber ↑(X.presheaf.stalk x)) g
              * algebraMap ↑(X.presheaf.stalk x)
                ((⊥ : Ideal ↑(Y.presheaf.stalk (f x))).Fiber ↑(X.presheaf.stalk x)) u := by
  let _ : Algebra ↑Γ(Y, V) ↑Γ(X, U) := (f.appLE V U e).hom.toAlgebra
  let _ : Algebra ↑(Y.presheaf.stalk (f x)) ↑(X.presheaf.stalk x) :=
    (f.stalkMap x).hom.toAlgebra
  let _ : Nonempty ↥(V.toScheme) := ⟨⟨f x, e hx⟩⟩
  let _ : IsDomain ↑Γ(Y, V) := IsIntegral.component_integral V
  let _ : Algebra ↑(X.presheaf.stalk x)
      ((⊥ : Ideal ↑(Y.presheaf.stalk (f x))).Fiber ↑(X.presheaf.stalk x)) :=
    Algebra.TensorProduct.rightAlgebra
  have _ : IsLocalization
      (Algebra.algebraMapSubmonoid ↑(X.presheaf.stalk x)
        (nonZeroDivisors ↑(Y.presheaf.stalk (f x))))
      ((⊥ : Ideal ↑(Y.presheaf.stalk (f x))).Fiber ↑(X.presheaf.stalk x)) :=
    IsLocalization.tensorRight ((⊥ : Ideal ↑(Y.presheaf.stalk (f x))).ResidueField)
      (nonZeroDivisors ↑(Y.presheaf.stalk (f x)))
  have _ : Module.FaithfullyFlat ↑(Y.presheaf.stalk (f x)) ↑(X.presheaf.stalk x) :=
    Flat.faithfullyFlat_stalkMap f x
  intro b hb
  exact Ideal.exists_isUnit_mul_eq_of_isDomain_fiber
    (forall_isDomain_fiber_stalkMap f hfib x) (hb.map (chartFiberBotToStalkFiberBot f hV e hx))

end AlgebraicGeometry

end
