module

public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.DualizingComplexScheme
public import StacksFrontier.RingTheory.Dualizing.NormalizedShift
public import StacksFrontier.Topology.Sheaves.Functors.Module.SemilinearStalk
public import StacksFrontier.Topology.Sheaves.Modules.StalkAcyclic
public import StacksFrontier.Topology.Sheaves.Modules.StalkExactness

/-!
# The shift function of a dualizing complex on a locally Noetherian scheme

A dualizing complex `K` on a locally Noetherian scheme determines an integer at each point `x`:
the unique shift normalizing the derived stalk of `K` at `x` as a dualizing complex over the local
ring `𝒪_{X,x}`, in the sense of `Dualizing.IsNormalizedDualizingComplex`. This is the function of
[Stacks, Tag 0AWF].

## Main definitions

* `Stacks.Duality.schemeStalkModuleFunctor` — the stalk functor at `x`, with scalars transported
  from the `RingCat`-valued stalk of the sheaf of rings to the scheme's own local ring
  `𝒪_{X,x} = X.presheaf.stalk x`.
* `Stacks.Duality.derivedStalkOfComplex` — the derived stalk at `x` of a *cochain complex* of
  `𝒪_X`-modules, obtained by applying that functor degreewise.
* `Stacks.Duality.associatedShiftFunction` — **[Stacks, Tag 0AWF]** the shift function: at `x` it
  is the infimum of the set of `n` for which some representative of `K` has normalized derived
  stalk after shifting by `-n`.

## Implementation notes

The stalk functor used is `AlgebraicGeometry.SheafOfModules.stalkFunctor`, which is
already known to be additive (`AlgebraicGeometry.SheafOfModules.stalkFunctor_additive`) and to
preserve finite limits and finite colimits
(`AlgebraicGeometry.SheafOfModules.stalkFunctor_preservesFiniteLimits`,
`AlgebraicGeometry.SheafOfModules.instPreservesFiniteColimitsStalkFunctor`), so no exactness
argument is repeated here. What it does *not* do is land in modules over the scheme's local ring:
its target is `ModuleCat (TopCat.Presheaf.stalk X.ringCatSheaf.obj x)`, and
`SemilinearStalk.commStalkIso` is the comparison with `X.presheaf.stalk x` along which the scalars
are restricted. That restriction is the only content of
`Stacks.Duality.schemeStalkModuleFunctor`.

`Stacks.Duality.derivedStalkOfComplex` is defined on a cochain complex rather than on an object of
`D(𝒪_X)` so that the set defining the shift function can quantify over representatives: this is
what makes `Stacks.Duality.associatedShiftFunction` a definition requiring no choice of
representative. The companion statement of [Stacks, Tag 0AWF] — that for a dualizing complex
*every* representative is normalized after shifting by exactly this integer, so that the infimum
is attained and the set is a singleton — is not proved here but in
`StacksFrontier/AlgebraicGeometry/Duality/RelativeDualizing/DerivedStalkModel.lean`, as part of
`Stacks.Duality.isUniversallyCatenary_and_isDimensionFunction_associatedShiftFunction`.

Both declarations take **free** `HasDerivedCategory` binders, for `X.Modules` and for
`ModuleCat 𝒪_{X,x}` respectively, so neither pins a model: under `set_option pp.explicit true`
the string `HasDerivedCategory.standard` does not occur in either type. This matters, because at
`HasDerivedCategory.standard` the morphisms of `D(𝒪_X)` live in `Type (u+1)` and the coproducts of
[Stacks, Tag 0A8G] do not exist, so a statement about `D(𝒪_X)` pinned there is a different — and
sometimes vacuous — statement; see `StacksFrontier/Homology/DerivedCategory/LocallySmall.lean`. The
free binders also match `Stacks.Duality.IsDualizingComplex`, which takes one, so the two compose
at whichever model a consumer chooses. The file-level `attribute [local instance]` below exists
only to supply the standard model where `Dualizing.IsNormalizedDualizingComplex` demands it: that
predicate *is* pinned, because `Dualizing.derivedHom` bakes the standard model into its own type,
and over `ModuleCat A` that pin is forced and legitimate rather than weakening.

## References

* [Stacks Project, Tag 0AWF](https://stacks.math.columbia.edu/tag/0AWF)
* [Stacks Project, Tag 0AX1](https://stacks.math.columbia.edu/tag/0AX1)
* [Stacks Project, Tag 0A87](https://stacks.math.columbia.edu/tag/0A87)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.Duality

/-- The stalk functor at `x` of sheaves of modules on a scheme, with scalars transported along
`SemilinearStalk.commStalkIso` so that the target is modules over the scheme's local ring
`𝒪_{X,x}` rather than over the `RingCat`-valued stalk of the sheaf of rings. -/
def schemeStalkModuleFunctor {X : Scheme.{u}} (x : X) :
    SheafOfModules.{u} X.ringCatSheaf ⥤ ModuleCat.{u} (X.presheaf.stalk x) :=
  AlgebraicGeometry.SheafOfModules.stalkFunctor X.ringCatSheaf x ⋙
    ModuleCat.restrictScalars.{u, u}
      (SemilinearStalk.commStalkIso X.presheaf x).inv.hom

/-- The stalk functor `Stacks.Duality.schemeStalkModuleFunctor x` is additive. -/
instance schemeStalkModuleFunctor_additive {X : Scheme.{u}} (x : X) :
    (schemeStalkModuleFunctor x).Additive := by
  let F := AlgebraicGeometry.SheafOfModules.stalkFunctor X.ringCatSheaf x
  let H := ModuleCat.restrictScalars.{u, u}
    (SemilinearStalk.commStalkIso X.presheaf x).inv.hom
  constructor
  intro A B f g
  change H.map (F.map (f + g)) = H.map (F.map f) + H.map (F.map g)
  rw [F.map_add]
  exact H.map_add

/-- The derived stalk at `x` of a cochain complex of sheaves of modules: apply
`Stacks.Duality.schemeStalkModuleFunctor` degreewise and pass to the derived category of
`𝒪_{X,x}`-modules. -/
def derivedStalkOfComplex {X : Scheme.{u}} (x : X)
    [HasDerivedCategory (ModuleCat.{u} (X.presheaf.stalk x))]
    (E : CochainComplex X.Modules ℤ) :
    DerivedCategory (ModuleCat.{u} (X.presheaf.stalk x)) :=
  DerivedCategory.Q.obj
    (((schemeStalkModuleFunctor x).mapHomologicalComplex (ComplexShape.up ℤ)).obj E)

/-- **Stacks Project, Tag 0AWF.** The shift function of a dualizing complex on a locally
Noetherian scheme: at `x` it is the least `n` such that some representative `E` of `K` has
normalized derived stalk at `x` after shifting by `-n`. -/
def associatedShiftFunction {X : Scheme.{u}}
    [IsLocallyNoetherian X] [HasDerivedCategory X.Modules]
    (K : DerivedCategory X.Modules) : X → ℤ := fun x ↦
  sInf {n : ℤ | ∃ E : CochainComplex X.Modules ℤ,
    Nonempty (DerivedCategory.Q.obj E ≅ K) ∧
      Dualizing.IsNormalizedDualizingComplex
        (A := X.presheaf.stalk x) ((derivedStalkOfComplex x E)⟦-n⟧)}

end Stacks.Duality

end
