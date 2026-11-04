module

public import StacksFrontier.AlgebraicGeometry.AffineCohomologyVanishing.AffineBase
public import StacksFrontier.AlgebraicGeometry.Cohomology.ColimitsHigherDirect.CohomologyOfOpen
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.PushforwardCoherence.RestrictPushforward
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.SectionsOnOpenDerived

/-!
# The cohomology of an open of a scheme, computed upstairs and downstairs

Let `X` be a scheme and `V` an open of `X`.  The cohomology of a sheaf of `𝒪_X`-modules "on `V`"
can be read in two ways: derive the sections functor `Γ(V, -)` on sheaves of modules over the
*ambient* `X`, or restrict the sheaf to the open subscheme `V` first and derive global sections
there.  The two agree, and this file says so in the vocabulary of schemes.

This is [Stacks, Tag 01E1] (2) for an open immersion `V ⟶ X` of schemes.  It is the dictionary
between the ringed-space formalization of the section functor, where the tag is proved, and the
scheme formalization, where the finiteness criteria of [Stacks, Tag 0BK0] and [Stacks, Tag 01XK]
are stated.

## Main results

* `Stacks.Cohomology.SchemeOpenSections.derivedEvaluationRestrictIso` — deriving the sections of
  sheaves of `𝒪_X`-modules over `V` agrees with restricting to `V` and deriving global sections
  there, naturally in the sheaf.
* `Stacks.Cohomology.SchemeOpenSections.derivedSectionsOnOpenIso` — the same comparison for
  `Stacks.Cohomology.ModuleComparison.sectionsOnOpen`, so with both sides read as modules over
  the *global* functions `Γ(X, 𝒪_X)`, which is the shape the local-cohomology sequence of
  [Stacks, Tag 0BK0] (2) uses; the restriction of scalars that appears on the right is the one
  along `V.ι.appTop`, the criterion of [Stacks, Tag 01XK] having that same restriction.

## Implementation notes

**Everything here is definitional except two named equalities.**  Writing
`Y := Stacks.Cohomology.HigherDirectImage.asRingSheafedSpace X.toRingedSpace` for `X` viewed as a
sheafed space over `RingCat`, the following all hold by `rfl`, which is why this dictionary is
three lines rather than a development:

* `AlgebraicGeometry.OXSh Y = X.ringCatSheaf`, hence `SheafOfModules (OXSh Y) = X.Modules`;
* `AlgebraicGeometry.OUSh Y V = V.toScheme.ringCatSheaf`, so the structure sheaf of the open
  subscheme *is* the restricted structure sheaf;
* `SheafOfModules.evaluation (OUSh Y V) (op ⊤) = Stacks.Cohomology.AffineBase.moduleGlobalSections
  V.toScheme`, an equality of *functors*: global sections on the open subscheme are exactly the
  right-hand functor of [Stacks, Tag 01E1] (2);
* the restriction of scalars along `X.ringCatSheaf.obj.map (homOfLE le_top).op` equals the one
  along `V.ι.appTop.hom`.

The two equalities that are not `rfl` are
`Stacks.LocalCohomology.schemeRestrictFunctor_eq_moduleRestriction`, which identifies the scheme
restriction functor with the ringed-space one, and `AlgebraicGeometry.jFun_obj_top`, which says
the image of the whole open subspace is the open itself.

The ambient open is therefore spelled `(jFun Y V).obj ⊤` in
`derivedEvaluationRestrictIso`, matching [Stacks, Tag 01E1] (2) as it is stated.  Spelling it `V`
would change the ring of sections and so force a restriction of scalars along an `eqToHom` of a
ring equality — the transport this library declines.  `derivedSectionsOnOpenIso` is nevertheless
stated at the open `V` itself, and that is sound for a different reason:
`Stacks.Cohomology.ModuleComparison.sectionsOnOpen` has target the modules over the *global*
functions, a category that does not mention the open, so the two spellings give two functors of
the same type and `jFun_obj_top` transports between them by `eqToIso` with no module structure
moved.

## References

* [Stacks Project, Tag 01E1](https://stacks.math.columbia.edu/tag/01E1)
* [Stacks Project, Tag 0BK0](https://stacks.math.columbia.edu/tag/0BK0)
* [Stacks Project, Tag 01XK](https://stacks.math.columbia.edu/tag/01XK)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Cohomology.AffineBase Stacks.Cohomology.HigherDirectImage
open Stacks.Cohomology.ModuleComparison Stacks.Cohomology.SectionsWithSupport

universe u

namespace Stacks.Cohomology.SchemeOpenSections

variable (X : Scheme.{u}) (V : X.Opens)

/-- The open of `X` swept out by the whole of the open subspace `V`.  It is `V` itself, by
`AlgebraicGeometry.jFun_obj_top`, but the sections of `𝒪_X` over it are *definitionally* the
global functions of the open subscheme `V`, which `V` itself is not. -/
noncomputable abbrev imageTop : X.Opens :=
  (jFun (asRingSheafedSpace X.toRingedSpace) V).obj
    (⊤ : Opens ((Opens.toTopCat X.carrier).obj V))

/-- `imageTop X V` is `V`. -/
theorem imageTop_eq : imageTop X V = V :=
  jFun_obj_top (asRingSheafedSpace X.toRingedSpace) V

/-! ### The comparison over the sections on the open -/

/-- **[Stacks, Tag 01E1] (2) for an open immersion of schemes.** Deriving the sections of sheaves
of `𝒪_X`-modules over the open `V` agrees with restricting to the open subscheme `V` and deriving
its global sections, naturally in the sheaf of modules.

The scheme restriction functor is the ringed-space one
(`Stacks.LocalCohomology.schemeRestrictFunctor_eq_moduleRestriction`), after which this is
`AlgebraicGeometry.cohomologyOverModuleNatIsoRestriction`: both the structure sheaf of the open
subscheme and its global sections functor agree with the restricted ones on the nose. -/
public noncomputable def derivedEvaluationRestrictIso (p : ℕ) :
    (SheafOfModules.evaluation X.ringCatSheaf (op (imageTop X V))).rightDerived p ≅
      Scheme.Modules.restrictFunctor V.ι ⋙
        (moduleGlobalSections V.toScheme).rightDerived p := by
  rw [Stacks.LocalCohomology.schemeRestrictFunctor_eq_moduleRestriction X V]
  exact AlgebraicGeometry.cohomologyOverModuleNatIsoRestriction
    (asRingSheafedSpace X.toRingedSpace) V p

/-! ### The comparison over the global functions -/

/-- The comparison of `derivedEvaluationRestrictIso` after restriction of scalars to the global
functions, at the open `imageTop X V`. -/
public noncomputable def derivedSectionsOnImageTopIso (p : ℕ) :
    (sectionsOnOpen X.toRingedSpace (imageTop X V)).rightDerived p ≅
      Scheme.Modules.restrictFunctor V.ι ⋙
        ((moduleGlobalSections V.toScheme).rightDerived p ⋙
          ModuleCat.restrictScalars V.ι.appTop.hom) :=
  (sectionsOnOpenDerivedIso X.toRingedSpace (imageTop X V) p).symm ≪≫
    Functor.isoWhiskerRight (derivedEvaluationRestrictIso X V p)
      (ModuleCat.restrictScalars V.ι.appTop.hom)

/-- **The cohomology of an open of a scheme, as a module over the global functions.** Deriving
the sections over `V` of sheaves of `𝒪_X`-modules, read over `Γ(X, 𝒪_X)`, agrees with restricting
to the open subscheme `V`, deriving global sections there and restricting scalars along
`V.ι.appTop` — the restriction of scalars under which [Stacks, Tag 01XK] states its finiteness
criterion.

The open of the ambient space is `V` here rather than `imageTop X V`; the target of
`Stacks.Cohomology.ModuleComparison.sectionsOnOpen` does not depend on the open, so
`imageTop_eq` moves between the two spellings by `eqToIso` and no module structure is
transported. -/
public noncomputable def derivedSectionsOnOpenIso (p : ℕ) :
    (sectionsOnOpen X.toRingedSpace V).rightDerived p ≅
      Scheme.Modules.restrictFunctor V.ι ⋙
        ((moduleGlobalSections V.toScheme).rightDerived p ⋙
          ModuleCat.restrictScalars V.ι.appTop.hom) :=
  eqToIso (congrArg (fun W : X.Opens => (sectionsOnOpen X.toRingedSpace W).rightDerived p)
    (imageTop_eq X V).symm) ≪≫ derivedSectionsOnImageTopIso X V p

end Stacks.Cohomology.SchemeOpenSections

end
