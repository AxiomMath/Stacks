module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentAdicSystem
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentStalkLocalProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Properness.ProperSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.SupportClosedFiniteType
public import StacksFrontier.AlgebraicGeometry.Topologies.FiniteTypeOnSiteEpi

/-!
# Proper support along the completion of a coherent module on an algebraic space

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` which is locally of finite
type and let `𝓘 ⊆ 𝒪_X` be a sheaf of ideals on the small étale site of `X`.  A coherent
`𝒪_X`-module `M` whose support is proper over `Y` has all of its quotients `M / 𝓘 ^ n M`
supported inside the support of `M`, hence again proper over `Y`.  This is the statement which
cuts the completion functor `Coh(𝒪_X) ⟶ Coh(X, 𝓘)` of Stacks 08B4 down to the full
subcategories of objects with support proper over `Y`, that is, Stacks 08B8.

The argument has three steps and uses no quasi-coherence of `𝓘`.  The projection
`M ⟶ M / 𝓘 ^ n M` is an epimorphism, so the quotient is of finite type (Stacks 03DL(5)) and
therefore has closed support (Stacks 07TZ); the epimorphism is a local surjection, so the
support of the quotient is contained in that of `M` (Stacks 04KB(5)); and a closed subset of a
closed subset proper over the base is proper over the base (Stacks 0CZE).  Only the last two
steps are specific to the base, and the first two hold for an arbitrary quotient of a module of
finite type, which is why the quotient clause of Stacks 0CZK part (1) is recorded here in that
generality.

## Main definitions

* `AlgebraicGeometry.Space.isCoherentProperOver` and
  `AlgebraicGeometry.Space.CoherentModulesProperOver` — the category
  `Coh_{support proper over Y}(𝒪_X)`, the source of Stacks 08B8.
* `AlgebraicGeometry.Space.isCoherentAdicSystemProperOver` and
  `AlgebraicGeometry.Space.CoherentAdicSystemsProperOver` — the category
  `Coh_{support proper over Y}(X, 𝓘)`, the target of Stacks 08B8.  As in the source, the
  condition is imposed on the first term of the system, every later term being supported inside
  it.

## Main results

* `AlgebraicGeometry.Space.hasProperSupport_of_epi` — the quotient clause of Stacks 0CZK
  part (1): a quotient of a module of finite type with support proper over `Y` has support
  proper over `Y`.
* `AlgebraicGeometry.Space.hasProperSupport_idealPowerQuotient` — the support condition of
  Stacks 08B8: the terms `M / 𝓘 ^ n M` of the completion of a coherent module with support
  proper over `Y` have support proper over `Y`.

## Implementation notes

The support of a module is the support of its underlying abelian sheaf, so the hypotheses and
conclusions are stated for `(SheafOfModules.toSheaf _).obj M`, matching
`AlgebraicGeometry.Space.HasProperSupport`.

Coherence of `M / 𝓘 ^ n M` is *not* used here: finite type of the quotient, which is all the
support statement consumes, needs only finite type of `M` and is supplied by
`Stacks.SheafOfModules.isFiniteTypeOnSite_of_epi`.  It is nonetheless available, should a
consumer want it: `AlgebraicGeometry.Space.isCoherent_idealPowerQuotient`, resting on
quasi-coherence of the subsheaf `𝓘 ^ n M`
(`AlgebraicGeometry.Space.isQuasicoherentOnSite_idealPowerMultiple`).

### The arrow of Stacks 08B8 itself

The two full subcategories named above are the source and the target of equation 76.42.5.1, and
`AlgebraicGeometry.Space.hasProperSupport_idealPowerQuotient` is the reason the equation makes
sense: the completion of an object of the source satisfies the defining condition of the target.
The arrow between them is *not* constructed here, but the functor it would restrict is now
available: the completion functor `Coh(𝒪_X) ⟶ Coh(X, 𝓘)` of Stacks 08B4 is
`AlgebraicGeometry.Space.completionFunctor`, and the attribute on
`hasProperSupport_idealPowerQuotient` names it.  What is left is to corestrict that functor to
the two full subcategories, for which this file supplies the object-level condition.  Earlier
revisions of this note said the functor was unavailable on an algebraic space; that is no longer
the case.

## References

* [Stacks Project, Tag 08B8](https://stacks.math.columbia.edu/tag/08B8)
* [Stacks Project, Tag 08B4](https://stacks.math.columbia.edu/tag/08B4)
* [Stacks Project, Tag 0CZK](https://stacks.math.columbia.edu/tag/0CZK)
* [Stacks Project, Tag 0CZE](https://stacks.math.columbia.edu/tag/0CZE)
* [Stacks Project, Tag 07TZ](https://stacks.math.columbia.edu/tag/07TZ)
* [Stacks Project, Tag 04KB](https://stacks.math.columbia.edu/tag/04KB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-! ### Proper support of a quotient -/

/-- **Stacks 0CZK, part (1), the quotient clause.** A quotient of an `𝒪_X`-module of finite
type whose support is proper over `Y` again has support proper over `Y`.

The quotient is of finite type by Stacks 03DL(5), so its support is closed by Stacks 07TZ; an
epimorphism of sheaves of modules is a local surjection, so that support is contained in the
support of the source by Stacks 04KB(5); and a closed subset of a closed subset proper over the
base is proper over the base by Stacks 0CZE. -/
@[stacks 0CZK "part (1), quotients"]
theorem hasProperSupport_of_epi (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) (hf : IsLocallyOfFiniteType B S hS f)
    {M N : Modules.{u, u} B S hS X hX} (p : M ⟶ N) [Epi p]
    (hMft : SheafOfModules.IsFiniteTypeOnSite M)
    (hM : HasProperSupport B S hS hX hY f hf ((SheafOfModules.toSheaf _).obj M)) :
    HasProperSupport B S hS hX hY f hf ((SheafOfModules.toSheaf _).obj N) := by
  let _ : SheafOfModules.IsFiniteTypeOnSite N :=
    Stacks.SheafOfModules.isFiniteTypeOnSite_of_epi p hMft
  exact hasProperSupport_of_subset B S hS hX hY f hf
    (isClosed_supportOfSheaf_of_isFiniteTypeOnSite B S hS X hX N)
    (@supportOfSheaf_subset_of_isLocallySurjective B S hS X hX _ _
      ((SheafOfModules.toSheaf _).map p)
      (Stacks.SheafOfModules.EpiMono.isLocallySurjective_of_epi p)) hM

/-- **Stacks 08B8, the support condition.** The terms `M / 𝓘 ^ n M` of the completion of a
coherent `𝒪_X`-module `M` whose support is proper over `Y` again have support proper over `Y`.

A coherent module is of finite type, and `M / 𝓘 ^ n M` is a quotient of `M`, so this is the
quotient clause of Stacks 0CZK part (1). -/
@[stacks 08B8 "the support condition, by which equation 76.42.2.1 restricts to the two full \
subcategories constructed below: the completion M / 𝓘 ^ n M of a coherent module with support \
proper over the base again has support proper over the base. The arrow itself is the completion \
functor of Stacks 08B4, which is \
`AlgebraicGeometry.Space.completionFunctor`"]
theorem hasProperSupport_idealPowerQuotient (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) (hf : IsLocallyOfFiniteType B S hS f)
    (𝓘 : (SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X hX).O))).Submodule)
    (n : ℕ) (M : Modules.{u, u} B S hS X hX) (hMcoh : IsCoherent B S hS X hX M)
    (hM : HasProperSupport B S hS hX hY f hf ((SheafOfModules.toSheaf _).obj M)) :
    HasProperSupport B S hS hX hY f hf
      ((SheafOfModules.toSheaf _).obj (idealPowerQuotient B S hS X hX 𝓘 n M)) :=
  have : SheafOfModules.IsCoherentOnSite M := hMcoh.toIsCoherentOnSite
  hasProperSupport_of_epi B S hS hX hY f hf
    (cokernel.π (idealPowerMultiple B S hS X hX 𝓘 n M).ι)
    (isFiniteTypeOnSite_of_isCoherentOnSite B S hS ⟨X, hX⟩ M) hM

/-! ### The two categories of Stacks 08B8 -/

/-- Coherent `𝒪_X`-modules with support proper over `Y`, as a property of objects of
`Coh(𝒪_X)`.  This is the condition cutting out the source of equation 76.42.5.1. -/
def isCoherentProperOver (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) (hf : IsLocallyOfFiniteType B S hS f) :
    ObjectProperty (CoherentModules.{u, u} B S hS X hX) :=
  fun M => HasProperSupport B S hS hX hY f hf ((SheafOfModules.toSheaf _).obj M.obj)

/-- The category `Coh_{support proper over Y}(𝒪_X)` of coherent `𝒪_X`-modules whose support is
proper over `Y`: the source of equation 76.42.5.1. -/
abbrev CoherentModulesProperOver (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) (hf : IsLocallyOfFiniteType B S hS f) :=
  (isCoherentProperOver B S hS hX hY f hf).FullSubcategory

/-- Coherent adic systems along `𝓘` whose first term has support proper over `Y`, as a property
of objects of `Coh(X, 𝓘)`.  This is the condition cutting out the target of equation 76.42.5.1;
every later term of such a system has the same support condition, the first term being a
quotient of it. -/
def isCoherentAdicSystemProperOver (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) (hf : IsLocallyOfFiniteType B S hS f)
    (𝓘 : (SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X hX).O))).Submodule) :
    ObjectProperty (CoherentAdicSystems.{u} B S hS X hX 𝓘) :=
  fun E => HasProperSupport B S hS hX hY f hf
    ((SheafOfModules.toSheaf _).obj (E.obj.obj (op 0)))

/-- The category `Coh_{support proper over Y}(X, 𝓘)` of coherent adic systems along `𝓘` whose
first term has support proper over `Y`: the target of equation 76.42.5.1. -/
abbrev CoherentAdicSystemsProperOver (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) (hf : IsLocallyOfFiniteType B S hS f)
    (𝓘 : (SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X hX).O))).Submodule) :=
  (isCoherentAdicSystemProperOver B S hS hX hY f hf 𝓘).FullSubcategory

end AlgebraicGeometry.Space

end
