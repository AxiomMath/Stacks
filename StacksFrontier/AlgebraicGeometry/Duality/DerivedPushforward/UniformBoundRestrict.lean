module

public import StacksFrontier.AlgebraicGeometry.DerivedAcyclic.Pushforward
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedPushforward.UniformBoundAnyModel

/-!
# The uniform cohomological bound for `Rf_*` after restriction to a quasi-compact open

Let `f : X ⟶ S` be a quasi-compact and quasi-separated morphism of schemes — with **no**
hypothesis on `S` — and let `j : V ⟶ S` be an open immersion with `V` quasi-compact. Then `Rf_*`
followed by restriction to `V` raises the upper cohomological bound of an object with
quasi-coherent cohomology by an amount depending only on `f` and `j`.

This is [Stacks, Tag 08D5] part (2) in the form [Stacks, Tag 08DZ] consumes: the target of a
quasi-compact quasi-separated morphism need not be quasi-compact, so the bound is only available
after cutting the target down to a quasi-compact open, and [Stacks, Tag 08FE] identifies the
composite with the derived direct image along the restricted morphism `f⁻¹V ⟶ V`, whose target is
quasi-compact.

`AlgebraicGeometry.isLE_rightDerived_pullback_obj` is the same statement at
`CategoryTheory.HasDerivedCategory.standard`, which was all that part (2) was available at. With
part (2) now transported — `Stacks.Duality.exists_isLE_derivedPushforward_obj_anyModel` — the
restricted form follows at the **locally small** model
`AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`, which is the model at which
`Stacks.Duality.quasiCoherentDerivedCategory` has the direct sums Brown representability asks
for.

## Main results

* `Stacks.Duality.exists_isLE_derivedPushforwardPullback_obj_locallySmall` — the bound at the
  locally small model.

## Implementation notes

**No `attribute [local instance] HasDerivedCategory.standard`.** The standard model is never a
global instance — it is installed file by file — so in this file every `DerivedCategory Z.Modules`
resolves to the locally small `AlgebraicGeometry.Scheme.Modules.hasDerivedCategory` at morphism
universe `u`, uniquely and with no priority juggling.

**Why the model is fixed rather than a binder.** The proof restricts along `j`, which introduces
the scheme `f⁻¹V = X ×_S V` *inside* the proof; a statement with free binders
`[HasDerivedCategory.{w} X.Modules]` and `[HasDerivedCategory.{w} S.Modules]` could not name the
instance for that scheme. Carrying `∀ Z : Scheme.{u}, HasDerivedCategory.{w} Z.Modules` instead
would be general, but the locally small model is the only model besides `standard` at which the
instance exists for every scheme at once, so nothing is lost.

[Stacks, Tag 08FE], `Stacks.Cohomology.derivedPushforwardRestrictIso`, is already stated at free
`HasDerivedCategory` instances and for arbitrary choices of the four right derived functors with
their units; it is applied here to `Stacks.Duality.derivedPushforward` along `f` and `g` and to
the exact restriction functors along `i` and `j`. It is stated for the ringed-space spelling
`SheafOfModules (structureSheafRing X.toRingedSpace)` of the category of
`𝒪_X`-modules, and the four `HasDerivedCategory` instances it asks for in that spelling are
supplied by instance search in the same way the standard-model form supplies them: the two
spellings are definitionally equal, and so are their locally small instances, both being
`Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian`.

## References

* [Stacks Project, Tag 08D5](https://stacks.math.columbia.edu/tag/08D5)
* [Stacks Project, Tag 08DZ](https://stacks.math.columbia.edu/tag/08DZ)
* [Stacks Project, Tag 08FE](https://stacks.math.columbia.edu/tag/08FE)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open StacksDraft.PseudoCoherence (mapDerivedCategoryCompHomologyFunctorIso)

universe u

namespace Stacks.Duality

attribute [local instance] AlgebraicGeometry.pullback_preservesFiniteLimits_of_isOpenImmersion

/-- **The bound of [Stacks, Tag 08D5] part (2) after restriction to a quasi-compact open of the
target, at the locally small model.** For `f : X ⟶ S` quasi-compact and quasi-separated and
`j : V ⟶ S` an open immersion with `V` quasi-compact, there is an integer `N` such that `Rf_*`
followed by restriction to `V` carries an object of `D(𝒪_X)` with quasi-coherent cohomology lying
in degrees `≤ d` into degrees `≤ d + N - 1`. No hypothesis is placed on `S`; the shape of the
bound is the one `AlgebraicGeometry.isLE_rightDerived_pullback_obj` has, so that the consumers of
that statement transcribe unchanged.

The square cut out by `V` is a pullback, so [Stacks, Tag 08FE] identifies the composite with
restriction along `i : f⁻¹V ⟶ X` followed by the derived direct image along the restricted
morphism `g : f⁻¹V ⟶ V`, whose target is quasi-compact; restriction is exact, so it preserves
both quasi-coherence of the cohomology sheaves and the upper bound, and
`Stacks.Duality.exists_isLE_derivedPushforward_obj_anyModel` supplies the bound for `g`.

This is `AlgebraicGeometry.isLE_rightDerived_pullback_obj` off
`CategoryTheory.HasDerivedCategory.standard`. -/
theorem exists_isLE_derivedPushforwardPullback_obj_locallySmall
    {X S V : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    (j : V ⟶ S) [IsOpenImmersion j] [CompactSpace V] :
    ∃ N : ℤ, ∀ (E : DerivedCategory X.Modules) (d : ℤ),
      (∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj E).IsQuasicoherent) →
      E.IsLE d →
      ((derivedPushforward f ⋙ (Scheme.Modules.pullback j).mapDerivedCategory).obj E).IsLE
        (d + N - 1) := by
  let U := Limits.pullback f j
  let i : U ⟶ X := Limits.pullback.fst f j
  let g : U ⟶ V := Limits.pullback.snd f j
  let Fi := Scheme.Modules.pullback i
  let Fj := Scheme.Modules.pullback j
  let Ri := Fi.mapDerivedCategory
  let Rj := Fj.mapDerivedCategory
  let αi := Fi.mapDerivedCategoryFactorsh.inv
  let αj := Fj.mapDerivedCategoryFactorsh.inv
  have hiR : Ri.IsRightDerivedFunctor αi
      (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ)) :=
    Functor.isRightDerivedFunctor_of_inverts _ Ri Fi.mapDerivedCategoryFactorsh
  have hjR : Rj.IsRightDerivedFunctor αj
      (HomotopyCategory.quasiIso S.Modules (ComplexShape.up ℤ)) :=
    Functor.isRightDerivedFunctor_of_inverts _ Rj Fj.mapDerivedCategoryFactorsh
  have hfR : (derivedPushforward f).IsRightDerivedFunctor (derivedPushforwardUnit f)
      (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ)) := inferInstance
  have hgR : (derivedPushforward g).IsRightDerivedFunctor (derivedPushforwardUnit g)
      (HomotopyCategory.quasiIso U.Modules (ComplexShape.up ℤ)) := inferInstance
  -- The four right-derived-functor witnesses are supplied explicitly: their statements are
  -- phrased in the scheme spelling of the module categories, which instance search does not
  -- unify with the ringed-space spelling of [Stacks, Tag 08FE].
  let e : derivedPushforward f ⋙ Rj ≅ Ri ⋙ derivedPushforward g :=
    @Stacks.Cohomology.derivedPushforwardRestrictIso _ _ _ _
      f.toLRSHom.toShHom i.toLRSHom.toShHom j.toLRSHom.toShHom g.toLRSHom.toShHom
      _ _ (isPullback_toShHom i g f j (IsPullback.of_hasPullback f j)) _ _ _ _
      (derivedPushforward f) (derivedPushforward g) Ri Rj
      (derivedPushforwardUnit f) (derivedPushforwardUnit g) αi αj hfR hgR hiR hjR
  obtain ⟨N, hN⟩ := exists_isLE_derivedPushforward_obj_anyModel g
  refine ⟨N + 1, fun E d hqc hE ↦ ?_⟩
  rw [show d + (N + 1) - 1 = d + N by omega]
  have hqc' : ∀ n : ℤ,
      ((DerivedCategory.homologyFunctor U.Modules n).obj (Ri.obj E)).IsQuasicoherent := by
    intro n
    have := hqc n
    exact (SheafOfModules.isQuasicoherent U.ringCatSheaf).prop_of_iso
      ((Scheme.Modules.restrictFunctorIsoPullback i).app _ ≪≫
        ((mapDerivedCategoryCompHomologyFunctorIso Fi n).app E).symm)
      (inferInstance : ((Scheme.Modules.restrictFunctor i).obj _).IsQuasicoherent)
  have hE' : (Ri.obj E).IsLE d := by
    rw [DerivedCategory.isLE_iff]
    intro n hn
    have : E.IsLE d := hE
    exact (Fi.map_isZero (E.isZero_of_isLE d n hn)).of_iso
      ((mapDerivedCategoryCompHomologyFunctorIso Fi n).app E)
  have hbound : ((Ri ⋙ derivedPushforward g).obj E).IsLE (d + N) := hN _ hqc' d hE'
  exact DerivedCategory.TStructure.t.isLE_of_iso (e.app E).symm (d + N)

end Stacks.Duality

end
