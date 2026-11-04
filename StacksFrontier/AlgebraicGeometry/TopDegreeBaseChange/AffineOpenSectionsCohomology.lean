module

public import StacksFrontier.AlgebraicGeometry.Modules.RestrictOpenSections
public import StacksFrontier.AlgebraicGeometry.PullbackSections.Affine
public import StacksFrontier.AlgebraicGeometry.ProperCoherentFiniteType.Basic
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.BaseChangeMapSections
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.SchemeRestriction

/-!
# [Stacks, Tag 01XK] over an affine open, and the two ends of `γ⁺` on sections

`BaseChangeMapSections.lean` reduces conclusion (c) of [Stacks, Tag 0EX3] to the bijectivity of

> `Γ(W, γ⁺) : Γ(W, h^* R^d f'_* F') ⟶ Γ(W, R^d f''_* (h')^* F')`

for the affine opens `W` of `Y''` lying over an affine open `V` of `Y'`
(`isIso_topDirectImageBaseChangeMap_of_bijective_app_plus_affineOpens`). Computing those two
modules needs [Stacks, Tag 01XK] — *the cohomology of a quasi-coherent module is the global
sections of its higher direct image* — over an affine **open** of the target, whereas the library's
form of that tag,
`Stacks.Cohomology.AffineBase.cohomologyIsoGlobalSectionsRightDerivedPushforward`, is stated for
a morphism whose target is an affine **scheme**.

This file supplies the open form, in the spelling the reduction consumes — the sections
`Γ(R^d f_* F, V)` as a module over `Γ(Y, V)`, not the global sections of a restriction over
`Γ(V, ⊤)` — and reads it at the two ends of `γ⁺`.

## Main definitions

* `…TopDegreeBaseChange.affineOpenCohomology`: `H^d(f⁻¹(V), F|_{f⁻¹(V)})` as a module over
  `Γ(Y, V)`, the functions on the affine open `V` of the target.

## Main results

* `…TopDegreeBaseChange.affineOpenCohomologyIsoSections`: **[Stacks, Tag 01XK] over an affine
  open of the target, on sections.** For a quasi-compact quasi-separated `f : X ⟶ Y`, an affine
  open `V` of `Y` and a quasi-coherent `F`, the degree-`d` cohomology `H^d(f⁻¹(V), F|)` is the
  module `Γ(R^d f_* F, V)` of sections over `V`, over `Γ(Y, V)`. The target `Y` of `f` carries
  **no** hypothesis.
* `…TopDegreeBaseChange.targetSectionsIsoCohomology`: **the target of `γ⁺` over `W`, computed.**
* `…TopDegreeBaseChange.sourceSectionsIsoTensor`: **the source of `γ⁺` over `W`, computed** as
  `Γ(Y'', W) ⊗_{Γ(Y', V)} H^d(f'⁻¹(V), F'|)`.

## Implementation notes

*The two steps of the open form.* [Stacks, Tag 01XK] applies to `f ∣_ V`, whose target is the
affine scheme `V`, and computes `H^d(f⁻¹(V), F|)` as the global sections of
`R^d (f ∣_ V)_* (F|)`; the restriction comparison of [Stacks, Tag 01E5], in its scheme-level
`ℤ`-indexed objectwise form
`Stacks.AlgebraicGeometry.SchemeHigherDirectImage.rightDerivedPlusRestrictObjIso`, identifies
that with the restriction of `R^d f_* F` to `V`. Both ends of `γ⁺` are already stated at
`CategoryTheory.Functor.rightDerivedPlus`, so no transport between the two models of `Rf_*`
intervenes.

*The change of spelling of the sections.* The restriction spelling that 01E5 produces,
`Γ(R^d f_* F |_V, ⊤)` over `Γ(V, ⊤)`, is turned into `Γ(R^d f_* F, V)` over `Γ(Y, V)` by
`AlgebraicGeometry.openSectionsModuleIso`
(`StacksFrontier/AlgebraicGeometry/Modules/RestrictOpenSections.lean`). That is the one step this
file used to be blocked on. Its content is that the two module structures on those sections
agree — the `Γ(V, ⊤)`-action that `Scheme.Modules.restrictFunctor` produces, which
`Stacks.Cohomology.moduleGlobalSections` passes through unchanged, and Mathlib's action of
`Γ(Y, V.ι ''ᵁ ⊤)` — and they do, with no ring map between them, so a *linear* map suffices;
see the implementation notes of that file for why the identification is nevertheless not an
`rfl` outside Mathlib.

*Why the source is a tensor product and the target is not.* The target of `γ⁺` is a higher
direct image along `f''`, so 01XK applies to it directly over `W`. The source is the pullback
along `h` of a higher direct image along `f'`, so its sections over `W` are first computed by
`AlgebraicGeometry.affinePullbackSectionsBaseChangeIso` — the base change of the sections over
`V` — and 01XK is then applied over `V`.

## References

* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
* [Stacks Project, Tag 01E5](https://stacks.math.columbia.edu/tag/01E5)
* [Stacks Project, Tag 01XJ](https://stacks.math.columbia.edu/tag/01XJ)
* [Stacks Project, Tag 01XK](https://stacks.math.columbia.edu/tag/01XK)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.Cohomology.AffineBase
open Stacks.AlgebraicGeometry.SchemeHigherDirectImage

universe u

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

attribute [local instance 10000] HasDerivedCategory.standard

/-- The degree-`d` cohomology of the restriction of `F` to `f⁻¹(V)`, as a module over the ring
`Γ(Y, V)` of functions on the open `V` of the target.

The cohomology is a module over `Γ(f⁻¹(V), ⊤)`; the scalars are restricted along
`(f ∣_ V).appTop`, which is the comparison [Stacks, Tag 01XK] is stated at, and then along
`AlgebraicGeometry.Scheme.Opens.topIso`, which is the transport along `V.ι ''ᵁ ⊤ = V`. -/
abbrev affineOpenCohomology {X Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.Opens) (F : X.Modules)
    (d : ℕ) : ModuleCat Γ(Y, V) :=
  (ModuleCat.restrictScalars (Scheme.Opens.topIso V).inv.hom).obj
    ((ModuleCat.restrictScalars (f ∣_ V).appTop.hom).obj
      (((moduleGlobalSections (f ⁻¹ᵁ V : Scheme)).rightDerivedPlus (d : ℤ)).obj
        ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).obj F)))

/-- **[Stacks, Tag 01XK] over an affine open of the target, on sections.** For a quasi-compact
and quasi-separated morphism `f : X ⟶ Y` of schemes, an affine open `V` of `Y` and a
quasi-coherent module `F` on `X`, the degree-`d` cohomology of the restriction of `F` to
`f⁻¹(V)` is the module `Γ(R^d f_* F, V)` of sections of `R^d f_* F` over `V`, as modules over
`Γ(Y, V)`.

The library's form of the tag asks the target of the morphism to be an affine *scheme*; here `Y`
carries no hypothesis at all and only the open `V` is affine. -/
def affineOpenCohomologyIsoSections {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] (V : Y.Opens) [IsAffine (V : Scheme)]
    (F : X.Modules) [F.IsQuasicoherent] (d : ℕ) :
    affineOpenCohomology f V F d ≅
      ModuleCat.of Γ(Y, V)
        Γ(((Scheme.Modules.pushforward f).rightDerivedPlus (d : ℤ)).obj F, V) :=
  (ModuleCat.restrictScalars (Scheme.Opens.topIso V).inv.hom).mapIso
      ((cohomologyIsoGlobalSectionsRightDerivedPushforward (f ∣_ V) (d : ℤ)).app
          ⟨(Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).obj F, inferInstance⟩ ≪≫
        (moduleGlobalSections (V : Scheme)).mapIso
          (rightDerivedPlusRestrictObjIso f V d F)) ≪≫
    openSectionsModuleIso _ V

variable {X'' Y'' : Scheme.{u}}

/-- **The target of `γ⁺`, computed on sections over an affine open of `Y''`.** The target of the
canonical map of [Stacks, Tag 0EX3] (c) is `R^d f''_* ((h')^* F')`, and its sections over an
affine open `W` of `Y''` are the degree-`d` cohomology of `(h')^* F'` over `f''⁻¹(W)`.

The coefficient is quasi-coherent by [Stacks, Tag 01BG], and the finiteness of `f''` is taken as
an explicit argument, as in `isQuasicoherent_target_topDirectImageBaseChangeMapPlus`, so that a
consumer whose morphism is only definitionally the one in hand can supply it in argument
position. -/
def targetSectionsIsoCohomology
    (S : Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation.{u})
    (F' : S.X'.Modules) [F'.IsQuasicoherent]
    (h' : X'' ⟶ S.X') (f'' : X'' ⟶ Y'') (hqc : QuasiCompact f'') (hqs : QuasiSeparated f'')
    (W : Y''.Opens) [IsAffine (W : Scheme)] :
    affineOpenCohomology f'' W ((Scheme.Modules.pullback h').obj F') S.d ≅
      ModuleCat.of Γ(Y'', W)
        Γ(((Scheme.Modules.pushforward f'').rightDerivedPlus (S.d : ℤ)).obj
          ((Scheme.Modules.pullback h').obj F'), W) :=
  have := hqc
  have := hqs
  have := AffineBaseChange.isQuasicoherent_pullback h' F'
  affineOpenCohomologyIsoSections f'' W ((Scheme.Modules.pullback h').obj F') S.d

/-- **The source of `γ⁺`, computed on sections over an affine open of `Y''`.** The source of the
canonical map of [Stacks, Tag 0EX3] (c) is `h^* R^d f'_* F'`. Over an affine open `W` of `Y''`
lying inside `h⁻¹(V)` for an affine open `V` of `Y'`, its sections are the base change along
`h.appLE V W` of the sections of `R^d f'_* F'` over `V`, and those are the degree-`d`
cohomology of `F'` over `f'⁻¹(V)`.

The base change is `AlgebraicGeometry.affinePullbackSectionsBaseChangeIso`, which needs
`R^d f'_* F'` to be quasi-coherent — that is [Stacks, Tag 01XJ]. -/
def sourceSectionsIsoTensor
    (S : Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation.{u})
    (F' : S.X'.Modules) [F'.IsQuasicoherent] (h : Y'' ⟶ S.Y')
    {V : S.Y'.Opens} (hV : IsAffineOpen V)
    {W : Y''.Opens} (hW : IsAffineOpen W) (hWV : W ≤ h ⁻¹ᵁ V) :
    ModuleCat.of Γ(Y'', W)
        Γ((Scheme.Modules.pullback h).obj
          (((Scheme.Modules.pushforward S.f').rightDerivedPlus (S.d : ℤ)).obj F'), W) ≅
      (ModuleCat.extendScalars (h.appLE V W hWV).hom).obj
        (affineOpenCohomology S.f' V F' S.d) :=
  have := S.quasiCompact_f'
  have := S.quasiSeparated_f'
  have : IsAffine (V : Scheme) := hV
  have : (((Scheme.Modules.pushforward S.f').rightDerivedPlus (S.d : ℤ)).obj F').IsQuasicoherent :=
    AlgebraicGeometry.ProperCoherentFiniteType.isQuasicoherent_rightDerivedPlus S.f' F'
      inferInstance (S.d : ℤ)
  (affinePullbackSectionsBaseChangeIso h
      (((Scheme.Modules.pushforward S.f').rightDerivedPlus (S.d : ℤ)).obj F') hV hW hWV).symm ≪≫
    (ModuleCat.extendScalars (h.appLE V W hWV).hom).mapIso
      (affineOpenCohomologyIsoSections S.f' V F' S.d).symm

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
