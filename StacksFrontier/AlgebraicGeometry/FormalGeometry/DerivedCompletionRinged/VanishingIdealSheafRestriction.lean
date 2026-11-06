module

public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryComparisons
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.Localization
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.VanishingIdealSheaf
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Localization.RestrictionDerivedProducts

/-!
# The condition `T(K|_U, f) = 0` is stable under restriction

Let `(𝒞, 𝒪)` be a ringed site, let `K ∈ D(𝒪)` and let `a : V ⟶ U` be a morphism of `𝒞`. This
file proves that `T(K|_U, f) = 0` implies `T(K|_V, f|_V) = 0`, which is the first of the two
inputs [Stacks, Tag 0998] needs beyond the objectwise statement of
`StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.VanishingIdealSheaf`:
it makes the ideals `AlgebraicGeometry.RingedSite.derivedCompleteIdealAt` into a submodule of
the *presheaf* of modules underlying `𝒪`.

## Main results

* `AlgebraicGeometry.RingedSite.preservesProducts_mapDerivedCategory_overFunctor`:
  `PreservesLimitsOfShape (Discrete ℕ) (SheafOfModules.overFunctor 𝒪 U).mapDerivedCategory`, in
  the ringed-site spelling.
* `Stacks.SheafOfModules.overMap_map_terminalSectionToEnd`: restriction of sheaves of modules
  between two slice sites carries multiplication by a section over the larger object to
  multiplication by its restriction.
* `AlgebraicGeometry.RingedSite.IsDerivedCompleteAtSection.restrict`: **the condition
  `T(K|_U, f) = 0` is stable under restriction.**
* `AlgebraicGeometry.RingedSite.derivedCompleteIdealAt_le_comap`: the same read as an inclusion
  of ideals, which is the subpresheaf condition.

## Implementation notes

The transport is `AlgebraicGeometry.RingedSite.isDerivedCompleteAt_map_of_smul_id` along the
functor `SheafOfModules.overMap 𝒪 a` of restriction from `𝒞/U` to `𝒞/V`, which takes three
inputs:

* additivity, which is additivity of a pushforward of sheaves of modules;
* that it matches the two scalars, which is `overMap_map_terminalSectionToEnd` below: the two
  compatible families of local sections attached to `f` restrict `f` along the same arrow of
  `𝒞`, which is `Stacks.SheafOfModules.terminalSection_over_val` read on both sides, exactly as
  in `AlgebraicGeometry.RingedSite.pushforward_iteratedSlice_map_terminalSectionToEnd`;
* that the induced functor of derived categories preserves the countable products, which is
  `Stacks.Cohomology.Localization.preservesProducts_mapDerivedCategory_overMap`. Grothendieck's
  AB4* fails for sheaves of modules, so the countable products of the two derived categories
  are not exact and the general `CategoryTheory.Functor.preservesProducts_mapDerivedCategory`
  does not apply; the K-injective route of
  `CategoryTheory.Functor.preservesProducts_mapDerivedCategory_of_isKInjective` does.

Restricting to `𝒞/V` directly and restricting to `𝒞/U` and then along `Over.map a` agree, by
`SheafOfModules.overFunctorMap`; the comparison is carried to derived categories by
`Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso` and
`mapDerivedCategoryCompIso`.

*Universes.* The ringed site is a `RingedSite.{u, u, u}`, where the objectwise statements of
`StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.VanishingIdealSheaf` are
stated for a `RingedSite.{u, v, max u v}`. The restriction is forced by
[Stacks, Tag 08FI]: `Stacks.Cohomology.Localization.isKInjective_over` and
`isKInjective_overMap`, which the product preservation consumes, are stated with the objects,
the morphisms, the sheaf of rings and the module sections in one universe. It is the generality
in which this library has the other ringed-site statements about derived completeness —
`AlgebraicGeometry.RingedSite.isDerivedComplete_restrictScalars_of_extendIdeal` for
[Stacks, Tag 099C], and `Stacks.Cohomology.Localization.derivedRestrictionIso` — so nothing
downstream loses by it.

No `@[stacks 0998]` attribute is attached here: the tag asserts that the rule
`U ↦ {f | T(K|_U, f) = 0}` is a sheaf of ideals, and the sheaf condition is its other half. That
half, and the sheaf of ideals itself —
`AlgebraicGeometry.RingedSite.derivedCompleteIdealSheaf`, which carries the unscoped
`@[stacks 0998]` — are in
`StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.VanishingIdealSheafCondition`,
which consumes `IsDerivedCompleteAtSection.restrict` below.

## References

* [Stacks Project, Tag 0998](https://stacks.math.columbia.edu/tag/0998)
* [Stacks Project, Tag 0999](https://stacks.math.columbia.edu/tag/0999)
* [Stacks Project, Tag 08FI](https://stacks.math.columbia.edu/tag/08FI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped IsMulCommutative

universe u v w

namespace Stacks.SheafOfModules

/-- **Restriction between two slice sites matches the two multiplication operators attached to a
section.** For `a : V ⟶ U`, the compatible family of local sections of `R` which a section `f`
over `U` defines on `𝒞/U`, and the one which its restriction `f|_V` defines on `𝒞/V`, both
restrict `f` along the arrow of `𝒞` underlying an object of `𝒞/V`; so the restriction
`SheafOfModules.overMap R a` carries multiplication by the first to multiplication by the
second. -/
theorem overMap_map_terminalSectionToEnd {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} (R : Sheaf J RingCat.{w})
    [∀ W : Cᵒᵖ, IsMulCommutative (R.obj.obj W)] {V U : C} (a : V ⟶ U)
    (f : R.obj.obj (op U)) (M : _root_.SheafOfModules.{w} (R.over U)) :
    (_root_.SheafOfModules.overMap.{w} R a).map
        ((terminalSectionToEnd (R.over U) (Over.mk (𝟙 U)) Over.mkIdTerminal f).asHom.app M) =
      (terminalSectionToEnd (R.over V) (Over.mk (𝟙 V)) Over.mkIdTerminal
            (R.obj.map a.op f)).asHom.app
        ((_root_.SheafOfModules.overMap.{w} R a).obj M) :=
  map_globalSectionToEnd (F := Over.map a) (S := R.over V) (R := R.over U)
    (Sheaf.pushforwardOverMapIso R a).inv
    (terminalSection (R.over U) (Over.mk (𝟙 U)) Over.mkIdTerminal f)
    (terminalSection (R.over V) (Over.mk (𝟙 V)) Over.mkIdTerminal (R.obj.map a.op f))
    (fun W ↦ by
      show (terminalSection (R.over V) (Over.mk (𝟙 V)) Over.mkIdTerminal
        (R.obj.map a.op f)).val W = _
      rw [terminalSection_over_val R V (R.obj.map a.op f) W,
        terminalSection_over_val R U f (op ((Over.map a).obj (unop W)))]
      show R.obj.map ((unop W).hom).op (R.obj.map a.op f) =
        R.obj.map ((unop W).hom ≫ a).op f
      rw [← RingCat.comp_apply, ← R.obj.map_comp, ← op_comp])
    M

end Stacks.SheafOfModules

namespace AlgebraicGeometry.RingedSite

attribute [local instance] HasDerivedCategory.standard

variable (X : RingedSite.{u, u, u})

attribute [local instance] isMulCommutative_over overCatCenterLinear
  overFunctor_preservesFiniteLimits overFunctor_preservesFiniteColimits
  hasProductsOfShape_nat_derivedCategory_over

/-- **Derived restriction to a slice site of a ringed site preserves countable products**, in
the spelling the derived-completeness predicate of [Stacks, Tag 0999] is stated at:
`PreservesLimitsOfShape (Discrete ℕ) (SheafOfModules.overFunctor 𝒪 U).mapDerivedCategory`.

This is `Stacks.Cohomology.Localization.preservesProducts_mapDerivedCategory_overFunctor` at the
structure sheaf of a ringed site, recorded here because this is where the predicate's consumers
live. The companion statement for the restriction between two slices is what
`IsDerivedCompleteAtSection.restrict` below consumes. -/
theorem preservesProducts_mapDerivedCategory_overFunctor (U : X.C) :
    PreservesLimitsOfShape (Discrete ℕ)
      (SheafOfModules.overFunctor.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        U).mapDerivedCategory :=
  Stacks.Cohomology.Localization.preservesProducts_mapDerivedCategory_overFunctor
    X.J ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) U

/-- **The condition `T(K|_U, f) = 0` is stable under restriction.** For a morphism
`a : V ⟶ U` of the site, if the restriction of `K` to the slice at `U` is derived complete at a
section `f` of `𝒪` over `U`, then the restriction of `K` to the slice at `V` is derived complete
at `f|_V`.

This is the transport of the Milnor condition along the restriction
`SheafOfModules.overMap 𝒪 a` from `𝒞/U` to `𝒞/V`: that functor matches the two multiplication
operators (`Stacks.SheafOfModules.overMap_map_terminalSectionToEnd`) and the functor it induces
on derived categories preserves the countable products
(`Stacks.Cohomology.Localization.preservesProducts_mapDerivedCategory_overMap`), and restricting
to `𝒞/U` and then along `Over.map a` is restricting to `𝒞/V`
(`SheafOfModules.overFunctorMap`). -/
theorem IsDerivedCompleteAtSection.restrict
    (K : DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
    {V U : X.C} (a : V ⟶ U) (f : ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj.obj (op U))
    (hf : IsDerivedCompleteAtSection X K U f) :
    IsDerivedCompleteAtSection X K V
      (((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj.map a.op f) := by
  let Φ := SheafOfModules.overMap.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) a
  have hΦlim : PreservesFiniteLimits Φ :=
    Stacks.SheafOfModules.LocalCokernel.overMap_preservesFiniteLimits
      (R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) a
  let := hΦlim
  have hΦcolim : PreservesFiniteColimits Φ :=
    Stacks.SheafOfModules.LocalCokernel.overMap_preservesFiniteColimits
      (R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) a
  let := hΦcolim
  have hpl : PreservesLimitsOfShape (Discrete ℕ) Φ.mapDerivedCategory :=
    Stacks.Cohomology.Localization.preservesProducts_mapDerivedCategory_overMap
      X.J ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) a
  let := hpl
  -- the two scalars, and the fact that `Φ` matches them
  let aU : CatCenter (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U)) :=
    overTerminalRingHom X U f
  let aV : CatCenter (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V)) :=
    overTerminalRingHom X V (((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj.map a.op f)
  have hmap : ∀ M : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U),
      Φ.map (aU.asHom.app M) = aV.asHom.app (Φ.obj M) :=
    Stacks.SheafOfModules.overMap_map_terminalSectionToEnd
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) a f
  have hsmulD : ∀ L : DerivedCategory
      (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U)),
      Φ.mapDerivedCategory.map (aU • 𝟙 L) = aV • 𝟙 (Φ.mapDerivedCategory.obj L) :=
    fun L ↦ Stacks.SheafOfModules.DerivedRestrictScalars.mapDerivedCategory_map_smul_id
      Φ aU aV
      (fun Z ↦ Stacks.SemilinearFunctor.map_smul_id_mapHomologicalComplex Φ aU aV
        (fun M ↦ (congrArg Φ.map (Category.comp_id (aU.asHom.app M))).trans
          ((hmap M).trans (Category.comp_id (aV.asHom.app (Φ.obj M))).symm))
        (ComplexShape.up ℤ) Z) L
  -- restricting to `V` is restricting to `U` and then along `Over.map a`
  let i₁ := Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso
    (SheafOfModules.overFunctor.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) U) Φ
  let i₂ := Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso
    (SheafOfModules.overFunctor.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) U ⋙ Φ)
    (SheafOfModules.overFunctor.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) V)
    (SheafOfModules.overFunctorMap.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) a)
  exact (isDerivedCompleteAt_iff_of_iso ((i₁.app K).symm ≪≫ i₂.app K) aV).mp
    (isDerivedCompleteAt_map_of_smul_id Φ.mapDerivedCategory (hsmulD _) hf)

/-- **The ideals of `AlgebraicGeometry.RingedSite.derivedCompleteIdealAt` form a submodule of the
presheaf of modules underlying `𝒪`**, in the form the submodule structure asks for: the ideal at
`U` is carried into the ideal at `V` by restriction along any `a : V ⟶ U`. -/
theorem derivedCompleteIdealAt_le_comap
    (K : DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
    {V U : X.C} (a : V ⟶ U) :
    derivedCompleteIdealAt X K U ≤
      (derivedCompleteIdealAt X K V).comap
        (((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj.map a.op).hom :=
  fun f hf ↦ (mem_derivedCompleteIdealAt_iff X K V _).2
    (IsDerivedCompleteAtSection.restrict X K a f
      ((mem_derivedCompleteIdealAt_iff X K U f).1 hf))

end AlgebraicGeometry.RingedSite

end
