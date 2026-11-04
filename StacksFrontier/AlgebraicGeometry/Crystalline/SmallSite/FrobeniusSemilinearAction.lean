module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.FrobeniusIsogenyReduction
public import StacksFrontier.Homology.Tor.DerivedChangeOfRingsAdjunction

/-!
# The canonical map of [Stacks, Tag 07N5] is exactly a `σ`-semilinear action on `RΓ`

[Stacks, Tag 07N5] asserts that the canonical map

`F_E ∘ (F_X)^*_cris : RΓ(Cris(X/S), E) ⊗^L_{A, σ} A ⟶ RΓ(Cris(X/S), E)`

becomes an isomorphism after inverting `p`; the assertion is
`Crystalline.GlobalCrystallineSituation.SmallSite.Statement07N5`, with that map as its parameter.

This file constructs the adjunction

`- ⊗^L_{A'} A  ⊣  restriction of scalars along A' ⟶ A`

at the universes of this chapter's module-valued crystalline cohomology, and deduces that a term
of `Crystalline.GlobalCrystallineSituation.SmallSite.FrobeniusMap07N5` is **the same data** as a
morphism

`RΓ(Cris(X/S), E) ⟶ σ_* RΓ(Cris(X/S), E)`   in `D(Mod_A)`,

where `σ_*` is restriction of scalars along `σ`.  By Mathlib's `ModuleCat.semilinearMapAddEquiv`,
a morphism into a restriction of scalars along `σ` is a `σ`-semilinear map, so arrow 1 of
[Stacks, Tag 07N5] is a `σ`-semilinear endomorphism of `RΓ`.  The ring map is `σ` by
`Crystalline.GlobalCrystallineSituation.SmallSite.baseChangeRingHom_specSigma`.

## Main definitions

Everything lives in the namespace `Crystalline.GlobalCrystallineSituation.SmallSite`.

* `derivedBaseChangeTensorAdjunction`: **`- ⊗^L_{A'} A` is left adjoint to restriction of scalars
  along `A' ⟶ A`**, at the universes of this chapter's cohomology.
* `frobeniusSigmaRestrictScalars`: **`σ_* : D(Mod_A) ⥤ D(Mod_A)`**, restriction of scalars along
  the Frobenius lift `σ` of a Frobenius crystal situation [Stacks, Tag 07N2].
* `frobeniusDerivedBaseChangeAdjunction`: the `σ`-twist `- ⊗^L_{A, σ} A` is left adjoint to `σ_*`.
* `SigmaSemilinearAction07N5`: **the type of a `σ`-semilinear Frobenius action on `RΓ`**,
  `RΓ(Cris(X/S), E) ⟶ σ_* RΓ(Cris(X/S), E)`: arrow 1 of [Stacks, Tag 07N5].
* `frobeniusMap07N5OfSemilinearAction`: the map of [Stacks, Tag 07N5] determined by such an
  action.

## Main results

* `frobeniusMap07N5Equiv`: **arrow 1 of [Stacks, Tag 07N5] is exactly a `σ`-semilinear action on
  `RΓ`**: the carried map of the tag and the `σ`-semilinear endomorphisms of `RΓ` are in natural
  bijection.
* `frobeniusMap07N5OfSemilinearAction_semilinearAction` and
  `semilinearAction_frobeniusMap07N5OfSemilinearAction`: the two round trips.
* `exists_unique_semilinearAction_07N5`: every map of the tag's type comes from one and only one
  `σ`-semilinear action.
* `statement07N5_semilinearAction_iff`: [Stacks, Tag 07N5] quantified over the carried maps and
  quantified over the `σ`-semilinear actions are the same assertion.
* `statement07N5_semilinearAction_iff_baseChangeArrows07N5Isogeny`: **the two reductions
  compose**: for a `σ`-semilinear action whose induced map factors through the third arrow, the
  tag is equivalent to the isogeny statement for the first two arrows alone.

## References

* [Stacks Project, Tag 07N5](https://stacks.math.columbia.edu/tag/07N5)
* [Stacks Project, Tag 07N2](https://stacks.math.columbia.edu/tag/07N2)
* [Stacks Project, Tag 0GMT](https://stacks.math.columbia.edu/tag/0GMT)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped AlgebraicGeometry

universe u wS wA wA' wP

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

/-! ### The derived base change tensor product is left adjoint to restriction of scalars -/

section Adjunction

variable {S S' : GlobalCrystallineSituation.{u}}
  [HasDerivedCategory.{wA} (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤))]
  [HasDerivedCategory.{wA'} (ModuleCat.{u + 1} Γ(S'.S.scheme, ⊤))]

/-- **The chapter's derived tensor product is the total left derived functor of degreewise
extension of scalars**, stated for `derivedBaseChangeTensor`. -/
instance derivedBaseChangeTensor_isLeftDerived (f : S.S ⟶ S'.S) :
    (derivedBaseChangeTensor f).IsLeftDerivedFunctor
      (derivedBaseChangeTensorBundle f).comparison
      (HomologicalComplex.quasiIso (ModuleCat.{u + 1} Γ(S'.S.scheme, ⊤))
        (ComplexShape.up ℤ)) :=
  (derivedBaseChangeTensorBundle f).isLeftDerived

/-- **`- ⊗^L_{A'} A` is left adjoint to restriction of scalars along `baseChangeRingHom f`.**

This is [Stacks, Tag 0GMT],
`CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction`, at the ring universe
`u` and the module universe `u + 1` of this chapter's module-valued crystalline cohomology, for
the chapter's derived tensor product `derivedBaseChangeTensor`. -/
def derivedBaseChangeTensorAdjunction (f : S.S ⟶ S'.S) :
    derivedBaseChangeTensor f ⊣
      (ModuleCat.restrictScalars (baseChangeRingHom f)).mapDerivedCategory :=
  @CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction.{u, u, u + 1}
    _ _ _ _ (baseChangeRingHom f) _ _ (derivedBaseChangeTensor f)
    (derivedBaseChangeTensorBundle f).comparison
    (derivedBaseChangeTensorBundle f).isLeftDerived

end Adjunction

/-! ### `σ`-semilinear actions on `RΓ(Cris(X/S), E)` -/

section Semilinear

variable (T : Crystalline.FCrystalSituation.{u})
  [HasDerivedCategory.{wA} (ModuleCat.{u + 1} Γ(T.global.S.scheme, ⊤))]

/-- **`σ_* : D(Mod_A) ⥤ D(Mod_A)`**, restriction of scalars along the Frobenius lift `σ` of a
Frobenius crystal situation [Stacks, Tag 07N2], on the derived category of `A`-modules.  The ring
map `baseChangeRingHom T.specSigma` is `σ` by `baseChangeRingHom_specSigma`. -/
def frobeniusSigmaRestrictScalars :
    DerivedCategory (ModuleCat.{u + 1} Γ(T.global.S.scheme, ⊤)) ⥤
      DerivedCategory (ModuleCat.{u + 1} Γ(T.global.S.scheme, ⊤)) :=
  (ModuleCat.restrictScalars
    (baseChangeRingHom (S := T.global) (S' := T.global) T.specSigma)).mapDerivedCategory

/-- `frobeniusSigmaRestrictScalars` is restriction of scalars along
`baseChangeRingHom T.specSigma`. -/
theorem frobeniusSigmaRestrictScalars_eq_restrictScalars_sigma :
    frobeniusSigmaRestrictScalars T =
      (ModuleCat.restrictScalars
        (baseChangeRingHom (S := T.global) (S' := T.global) T.specSigma)).mapDerivedCategory :=
  rfl

/-- **The `σ`-twist `- ⊗^L_{A, σ} A` is left adjoint to `σ_*`**:
`derivedBaseChangeTensorAdjunction` at `f = Spec(σ)`. -/
def frobeniusDerivedBaseChangeAdjunction :
    frobeniusDerivedBaseChangeTensor T ⊣ frobeniusSigmaRestrictScalars T :=
  derivedBaseChangeTensorAdjunction T.specSigma

variable [HasDerivedCategory.{wS} (ModuleSheaf T.global)]

/-- **The type of a `σ`-semilinear Frobenius action on `RΓ(Cris(X/S), E)`**, a morphism

`RΓ(Cris(X/S), E) ⟶ σ_* RΓ(Cris(X/S), E)`

of `D(Mod_A)`.  This is arrow 1 of the proof of [Stacks, Tag 07N5]: the action of the Frobenius on
module-valued crystalline cohomology, semilinear over the Frobenius lift `σ`.  Here `E` is a sheaf
of `𝒪_{X/S}`-modules on the small site. -/
abbrev SigmaSemilinearAction07N5 (E : SheafOfModules.{u} (structureSheaf T.global)) :=
  DerivedCategory.Plus.ι.obj (moduleULiftDerivedGlobalSections T.global E) ⟶
    (frobeniusSigmaRestrictScalars T).obj
      (DerivedCategory.Plus.ι.obj (moduleULiftDerivedGlobalSections T.global E))

/-- **Arrow 1 of [Stacks, Tag 07N5] is exactly a `σ`-semilinear action on `RΓ`.**

The maps `RΓ(Cris(X/S), E) ⊗^L_{A, σ} A ⟶ RΓ(Cris(X/S), E)` of the tag's type and the
`σ`-semilinear endomorphisms `RΓ(Cris(X/S), E) ⟶ σ_* RΓ(Cris(X/S), E)` of `RΓ` are in natural
bijection, by the adjunction `frobeniusDerivedBaseChangeAdjunction`. -/
def frobeniusMap07N5Equiv (E : SheafOfModules.{u} (structureSheaf T.global)) :
    FrobeniusMap07N5 T E ≃ SigmaSemilinearAction07N5 T E :=
  (frobeniusDerivedBaseChangeAdjunction T).homEquiv _ _

/-- **The map of [Stacks, Tag 07N5] determined by a `σ`-semilinear action on `RΓ`**, the inverse
direction of `frobeniusMap07N5Equiv`: the adjoint transpose of the action. -/
def frobeniusMap07N5OfSemilinearAction {E : SheafOfModules.{u} (structureSheaf T.global)}
    (a : SigmaSemilinearAction07N5 T E) : FrobeniusMap07N5 T E :=
  (frobeniusMap07N5Equiv T E).symm a

/-- The `σ`-semilinear action of the map a `σ`-semilinear action determines is that action. -/
@[simp]
theorem semilinearAction_frobeniusMap07N5OfSemilinearAction
    {E : SheafOfModules.{u} (structureSheaf T.global)} (a : SigmaSemilinearAction07N5 T E) :
    frobeniusMap07N5Equiv T E (frobeniusMap07N5OfSemilinearAction T a) = a :=
  (frobeniusMap07N5Equiv T E).apply_symm_apply a

/-- The map determined by the `σ`-semilinear action of a map is that map. -/
@[simp]
theorem frobeniusMap07N5OfSemilinearAction_semilinearAction
    {E : SheafOfModules.{u} (structureSheaf T.global)} (ψ : FrobeniusMap07N5 T E) :
    frobeniusMap07N5OfSemilinearAction T (frobeniusMap07N5Equiv T E ψ) = ψ :=
  (frobeniusMap07N5Equiv T E).symm_apply_apply ψ

/-- **Every map of the type of [Stacks, Tag 07N5] comes from one and only one `σ`-semilinear
action on `RΓ`.** -/
theorem exists_unique_semilinearAction_07N5
    {E : SheafOfModules.{u} (structureSheaf T.global)} (ψ : FrobeniusMap07N5 T E) :
    ∃! a : SigmaSemilinearAction07N5 T E, frobeniusMap07N5OfSemilinearAction T a = ψ :=
  (frobeniusMap07N5Equiv T E).symm.bijective.existsUnique ψ

end Semilinear

/-! ### [Stacks, Tag 07N5] read as an assertion about `σ`-semilinear actions -/

section Statement

variable (T : Crystalline.FCrystalSituation.{u})
  [HasDerivedCategory.{wS} (ModuleSheaf T.global)]
  [HasDerivedCategory.{wA} (ModuleCat.{u + 1} Γ(T.global.S.scheme, ⊤))]
  [HasDerivedCategory.{wP} (ModuleCat.{u + 1} (invertPrimeRing T.global))]

/-- **[Stacks, Tag 07N5], quantified over `σ`-semilinear actions instead of over carried maps.**

`Crystalline.GlobalCrystallineSituation.SmallSite.Statement07N5` is a proposition about a family of
maps of type `FrobeniusMap07N5`, one for each `F`-crystal; asserting it for every such family is
the same as asserting it for every family of `σ`-semilinear actions on `RΓ`. -/
theorem statement07N5_semilinearAction_iff :
    (∀ frobeniusMap : ∀ E : Crystalline.FCrystal T,
        FrobeniusMap07N5 T (toSmallFCrystal E), Statement07N5 T frobeniusMap) ↔
      ∀ action : ∀ E : Crystalline.FCrystal T,
        SigmaSemilinearAction07N5 T (toSmallFCrystal E),
          Statement07N5 T fun E => frobeniusMap07N5OfSemilinearAction T (action E) := by
  refine ⟨fun h action => h _, fun h frobeniusMap => ?_⟩
  simpa only [frobeniusMap07N5OfSemilinearAction_semilinearAction] using
    h fun E => frobeniusMap07N5Equiv T (toSmallFCrystal E) (frobeniusMap E)

/-- **The two reductions of [Stacks, Tag 07N5] compose.**

For a family of `σ`-semilinear actions on `RΓ` whose induced maps factor through the third arrow of
the source's proof, and under the delimiter inherited from [Stacks, Tag 07N4], the tag is
*equivalent* to the assertion that the first two arrows become an isomorphism after inverting `p`.
This is
`Crystalline.GlobalCrystallineSituation.SmallSite.statement07N5_iff_baseChangeArrows07N5Isogeny`
read at the map a `σ`-semilinear action induces. -/
theorem statement07N5_semilinearAction_iff_baseChangeArrows07N5Isogeny
    (action : ∀ E : Crystalline.FCrystal T,
      SigmaSemilinearAction07N5 T (toSmallFCrystal E))
    (hrank : BoundedCommonLocalRanks07N5 T)
    (hfac : FrobeniusFactorsThroughCohomologyMap07N5 T
      fun E => frobeniusMap07N5OfSemilinearAction T (action E)) :
    (Statement07N5 T fun E => frobeniusMap07N5OfSemilinearAction T (action E)) ↔
      BaseChangeArrows07N5Isogeny T
        fun E => frobeniusMap07N5OfSemilinearAction T (action E) :=
  statement07N5_iff_baseChangeArrows07N5Isogeny T _ hrank hfac

end Statement

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
