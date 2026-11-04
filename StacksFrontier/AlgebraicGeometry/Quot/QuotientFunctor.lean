module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.RelativeHom
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModule
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulesAbelian
public import StacksFrontier.AlgebraicGeometry.Topologies.ModuleTypesOnSite

/-!
# The functor of quotients of a quasi-coherent module (Stacks 082M)

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` of a big fppf site and let
`F` be a quasi-coherent `𝒪_X`-module.  For a scheme `T` over `Y`, write `X_T = X ×_Y T` and
write `F_T` for the pullback of `F` along the projection `X_T ⟶ X`.  Stacks 082M attaches to
this data the set

`Q_{F/X/Y}(T) = {quotients F_T ⟶ Q with Q a quasi-coherent 𝒪_{X_T}-module flat over T}`,

two quotients being identified when they have the same kernel, together with the subset
`Q^{fp}_{F/X/Y}(T)` of those quotients that are of finite presentation as `𝒪_{X_T}`-modules.

## Main definitions

* `AlgebraicGeometry.Space.QuotientSituation`: **Stacks 082M**, the standing data — a morphism
  of algebraic spaces together with a quasi-coherent module on its source.
* `AlgebraicGeometry.Space.QuotientSituation.baseChangeModule`: the module `F_T` on the base
  change `X_T`.
* `AlgebraicGeometry.Space.QuotientSituation.quotientModule`: the quotient `F_T / K` of `F_T`
  by a submodule `K`.
* `AlgebraicGeometry.Space.QuotientSituation.quotients`: **Stacks 082M**, the set
  `Q_{F/X/Y}(T)` of quotients of `F_T` that are quasi-coherent and flat over `T`.
* `AlgebraicGeometry.Space.QuotientSituation.finitePresentationQuotients`: **Stacks 082M**, the
  subset `Q^{fp}_{F/X/Y}(T)` of those quotients which are of finite presentation.

## Main results

* `AlgebraicGeometry.Space.QuotientSituation.finitePresentationQuotients_subset_quotients`: the
  finitely presented quotients form a subset of all quotients.
* `AlgebraicGeometry.Space.QuotientSituation.epi_quotientProjection`: the projection
  `F_T ⟶ F_T / K` is an epimorphism, so each element of `Q_{F/X/Y}(T)` really does name a
  quotient of `F_T`.

## Implementation notes

**Why the quotients are indexed by subobjects.**  The source identifies two quotients of `F_T`
when they have the same kernel, so the set it describes is a set of *submodules* of `F_T`: the
kernel determines the quotient up to the unique isomorphism commuting with the projections, and
conversely every submodule `K` is the kernel of `F_T ⟶ F_T/K`.  `Q_{F/X/Y}(T)` is therefore
defined here as a set of elements of `CategoryTheory.Subobject (F_T)`, the conditions of the
source being read on the quotient `F_T/K`, which is `CategoryTheory.Limits.cokernel` of the
inclusion.  Indexing by subobjects rather than by a structure carrying an epimorphism is what
makes `Q_{F/X/Y}(T)` a *set* with the source's identification built in rather than a groupoid.

**The category of modules is abelian.**  `AlgebraicGeometry.Space.Modules` is
`SheafOfModules` on the small étale ringed site, which is abelian once that site has
sheafification and its local equivalences are the locally bijective morphisms; both are the
instances of `StacksFrontier.AlgebraicGeometry.Spaces.ModulesAbelian`.  That is what makes the
quotient `F_T / K` available as `CategoryTheory.Limits.cokernel` of the inclusion of `K`.

**Quasi-coherence, finite presentation and flatness.**  These are the predicates the adjacent
`AlgebraicGeometry.Space.CoherentObject` of Stacks 08KB uses for the same three conditions:
`SheafOfModules.IsQuasicoherentOnSite` (Stacks 03G9),
`SheafOfModules.IsFinitePresentationOnSite` (Stacks 03DL), and
`AlgebraicGeometry.Space.IsFlatOver` (Stacks 05VV) along the projection `X_T ⟶ T`.  The base
change `X_T` and its two projections are those of
`StacksFrontier.AlgebraicGeometry.Quot.RelativeHom`, so this situation shares its base-change
calculus with Stacks 08KB and with the Hilbert functor of Stacks 0CZY.

**The test objects.**  `T` ranges over `AlgebraicGeometry.Space.SchemesOver D.Y`, the schemes
of the big fppf site equipped with a morphism to `Y` read as a morphism of algebraic spaces.
This is the source's `(Sch/B)` and is the index category of Stacks 08KB and 0CZY as well.

## References

* [Stacks Project, Tag 082M](https://stacks.math.columbia.edu/tag/082M)
* [Stacks Project, Tag 08KB](https://stacks.math.columbia.edu/tag/08KB)
* [Stacks Project, Tag 03G9](https://stacks.math.columbia.edu/tag/03G9)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 05VV](https://stacks.math.columbia.edu/tag/05VV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u

/-! ### The standing data -/

/-- **Stacks 082M, the standing data.**  A morphism `f : X ⟶ Y` of algebraic spaces over `S`
together with a quasi-coherent `𝒪_X`-module `F`: the data whose quotients, flat over the test
scheme, the functor of quotients of `F/X/Y` classifies. -/
@[stacks 082M "the standing data"]
structure QuotientSituation (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) where
  /-- The source of the morphism, the space the module lives on. -/
  X : AlgebraicSpaces B S hS
  /-- The target of the morphism, the base over which the quotients are taken. -/
  Y : AlgebraicSpaces B S hS
  /-- The morphism itself. -/
  f : X ⟶ Y
  /-- The module on the source. -/
  F : Modules.{u, u} B S hS X.1 X.2
  /-- It is quasi-coherent (Stacks 03G9). -/
  quasicoherent : F.IsQuasicoherentOnSite

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace QuotientSituation

variable (D : QuotientSituation B S hS)

/-- The base change `X_T = X ×_Y T` of the situation to a scheme `T` over `Y`. -/
abbrev space (T : SchemesOver D.Y) : AlgebraicSpaces B S hS := baseChangeSpace D.f T

/-- The projection `X_T ⟶ X` of the base change to the source of the morphism, along which the
module is pulled back. -/
abbrev sourceProjection (T : SchemesOver D.Y) : D.space T ⟶ D.X := baseChangeProjection D.f T

/-- The projection `X_T ⟶ T` of the base change to its test scheme, over which the quotients
are required to be flat. -/
abbrev projection (T : SchemesOver D.Y) :
    D.space T ⟶ (schemeSpaceFunctor B S hS).obj T.left :=
  baseChangeInclusion D.f T

/-- The morphism `X_h : X_T ⟶ X_{T'}` of base changes induced by a morphism `h : T ⟶ T'` of
test schemes over `Y`. -/
abbrev relativeMap {T T' : SchemesOver D.Y} (h : T ⟶ T') : D.space T ⟶ D.space T' :=
  baseChangeMap D.f h

/-- The module `F_T`, the pullback of `F` along the projection `X_T ⟶ X`. -/
abbrev baseChangeModule (T : SchemesOver D.Y) :
    Modules.{u, u} B S hS (D.space T).1 (D.space T).2 :=
  (modulePullback B S hS (D.sourceProjection T)).obj D.F

/-- The quotient `F_T / K` of `F_T` by a submodule `K`, that is, the quotient whose kernel
is `K`. -/
abbrev quotientModule (T : SchemesOver D.Y) (K : Subobject (D.baseChangeModule T)) :
    Modules.{u, u} B S hS (D.space T).1 (D.space T).2 :=
  cokernel K.arrow

/-- The projection `F_T ⟶ F_T / K` of `F_T` onto its quotient by `K`. -/
abbrev quotientProjection (T : SchemesOver D.Y) (K : Subobject (D.baseChangeModule T)) :
    D.baseChangeModule T ⟶ D.quotientModule T K :=
  cokernel.π K.arrow

/-- The projection onto the quotient by a submodule is an epimorphism. -/
instance epi_quotientProjection (T : SchemesOver D.Y) (K : Subobject (D.baseChangeModule T)) :
    Epi (D.quotientProjection T K) :=
  coequalizer.π_epi

/-- The kernel of the projection `F_T ⟶ F_T / K` is `K` again.  Together with surjectivity of
the projection this says that the submodules of `F_T` list the quotients of `F_T` once each,
which is the source's identification of two quotients with the same kernel. -/
@[stacks 082M "the identification of two quotients of F_T that have the same kernel: the \
submodules of F_T list the quotients of F_T once each"]
theorem mk_kernel_quotientProjection (T : SchemesOver D.Y)
    (K : Subobject (D.baseChangeModule T)) :
    Subobject.mk (kernel.ι (D.quotientProjection T K)) = K := by
  refine (Subobject.mk_eq_mk_of_comm _ K.arrow
    (IsLimit.conePointUniqueUpToIso (kernelIsKernel (cokernel.π K.arrow))
      (Abelian.monoIsKernelOfCokernel (Cofork.ofπ (cokernel.π K.arrow)
        ((cokernel.condition K.arrow).trans zero_comp.symm))
        (cokernelIsCokernel K.arrow))) ?_).trans
    (Subobject.mk_arrow K)
  exact IsLimit.conePointUniqueUpToIso_hom_comp _ _ WalkingParallelPair.zero

/-! ### The quotients -/

/-- **Stacks 082M.**  The set `Q_{F/X/Y}(T)` of quotients of `F_T` which are quasi-coherent and
flat over the test scheme `T`, the two conditions of the source.

A quotient of `F_T` is recorded by its kernel, a submodule `K` of `F_T`, the quotient itself
being `F_T / K`; this is exactly the source's identification of two quotients of `F_T` that
have the same kernel. -/
@[stacks 082M "the set of quotients"]
def quotients (T : SchemesOver D.Y) : Set (Subobject (D.baseChangeModule T)) :=
  {K | (D.quotientModule T K).IsQuasicoherentOnSite ∧
    IsFlatOver B S hS (D.space T).2 (D.projection T).hom (D.quotientModule T K)}

/-- **Stacks 082M.**  The subset `Q^{fp}_{F/X/Y}(T)` of `Q_{F/X/Y}(T)` consisting of those
quotients `F_T ⟶ Q` for which `Q` is of finite presentation as an `𝒪_{X_T}`-module. -/
@[stacks 082M "the finite-presentation subfunctor"]
def finitePresentationQuotients (T : SchemesOver D.Y) :
    Set (Subobject (D.baseChangeModule T)) :=
  {K | K ∈ D.quotients T ∧ (D.quotientModule T K).IsFinitePresentationOnSite}

/-- The finitely presented quotients of `F_T` form a subset of all its quotients which are
quasi-coherent and flat over `T`. -/
theorem finitePresentationQuotients_subset_quotients (T : SchemesOver D.Y) :
    D.finitePresentationQuotients T ⊆ D.quotients T :=
  fun _ hK => hK.1

end QuotientSituation

end AlgebraicGeometry.Space

end
