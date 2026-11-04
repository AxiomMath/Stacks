module

public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.AffineOpenSectionsCohomology

/-!
# [Stacks, Tag 01E5] on sections over the open, with no hypothesis

`…SchemeHigherDirectImage.rightDerivedPlusRestrictObjIso` (`SchemeRestriction.lean`) is
[Stacks, Tag 01E5] at the **sheaf** level: `Rᵈ(f ∣_ V)_*(F|_{f⁻¹V}) ≅ (Rᵈ f_* F)|_V`, with no
hypothesis on `f`, on `V` or on `F`. The tail of conclusion (c) of [Stacks, Tag 0EX3] meets it on
**sections**, as a comparison between the global sections of the open subscheme `V` of the higher
direct image along the restricted morphism and the sections over `V` of the higher direct image
along `f`. That comparison is the sheaf-level one followed by
`AlgebraicGeometry.openSectionsModuleIso`, and both factors are unconditional.

It was already written down twice, and both times **welded to the [Stacks, Tag 01XK] factor** — in
`…TopDegreeBaseChange.affineOpenCohomologyIsoSections` (`AffineOpenSectionsCohomology.lean`) and,
inverted, in `…TopDegreeBaseChange.affineOpenCohomologyIsoSectionsOf_inv_eq`
(`BaseChangeSectionsTail.lean`) — so that it is reachable only behind `QuasiCompact f`,
`QuasiSeparated f`, `IsAffine (V : Scheme)` and quasi-coherence of `F`, none of which it needs.
This file pulls it out.

## Main results

* `…TopDegreeBaseChange.rightDerivedPlusRestrictSectionsIso` — **[Stacks, Tag 01E5] on sections.**
  For a morphism of schemes `f : X ⟶ Y`, an open `V ⊆ Y`, a degree `d` and a module `F` on `X`,

  > the global sections over the open subscheme `V` of `Rᵈ(f ∣_ V)_*(F|_{f⁻¹V})`, read over
  > `Γ(Y, V)` through `AlgebraicGeometry.Scheme.Opens.topIso`, are `Γ(Rᵈ f_* F, V)`.

  **Nothing is assumed** of `f`, of `V`, of `F` or of `d`.
* `…TopDegreeBaseChange.affineOpenCohomologyIsoSections_eq` — the gated statement factors through
  it: `affineOpenCohomologyIsoSections` is [Stacks, Tag 01XK] over `V`, read under the restriction
  of scalars, followed by this comparison. So the two are the same morphism and no second copy is
  hidden.

## Implementation notes

*Only the hypotheses move.* Nothing new is proved: the comparison is
`rightDerivedPlusRestrictObjIso` read under
`Stacks.Cohomology.AffineBase.moduleGlobalSections (V : Scheme)` and the restriction of scalars,
followed by `openSectionsModuleIso`. The factorisation is the two `Iso.trans`es reassociated and
`CategoryTheory.Functor.mapIso_trans`.

*No `@[stacks …]` attribute is placed.* [Stacks, Tag 01E5] carries its own where the sheaf-level
comparison is built, and [Stacks, Tag 01XK] where its own is; this is neither tag restated but one
of them read on sections.

## References

* [Stacks Project, Tag 01E5](https://stacks.math.columbia.edu/tag/01E5)
* [Stacks Project, Tag 01XK](https://stacks.math.columbia.edu/tag/01XK)
* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.Cohomology.AffineBase
open Stacks.AlgebraicGeometry.SchemeHigherDirectImage

universe u

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

attribute [local instance 10000] HasDerivedCategory.standard

/-- **[Stacks, Tag 01E5] on sections over the open, with no hypothesis.** For a morphism of
schemes `f : X ⟶ Y`, an open `V ⊆ Y`, a degree `d` and a module `F` on `X`, the global sections
over the open subscheme `V` of the degree-`d` higher direct image of `F|_{f⁻¹V}` along `f ∣_ V`,
read over `Γ(Y, V)` through `AlgebraicGeometry.Scheme.Opens.topIso`, are the sections of
`Rᵈ f_* F` over `V`.

This is `…SchemeHigherDirectImage.rightDerivedPlusRestrictObjIso` — the sheaf-level comparison —
read under `Stacks.Cohomology.AffineBase.moduleGlobalSections (V : Scheme)` and the restriction of
scalars, followed by `AlgebraicGeometry.openSectionsModuleIso`, which identifies the global
sections of a restriction with the sections over the open. Both factors are unconditional, so
**nothing is assumed** of `f`, of `V`, of `F` or of `d`: no affineness, no quasi-compactness, no
quasi-separatedness and no quasi-coherence. The gated
`…TopDegreeBaseChange.affineOpenCohomologyIsoSections` is this comparison with
[Stacks, Tag 01XK] over `V` in front, which is where those hypotheses belong; see
`affineOpenCohomologyIsoSections_eq`. -/
def rightDerivedPlusRestrictSectionsIso {X Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.Opens) (d : ℕ)
    (F : X.Modules) :
    (ModuleCat.restrictScalars (Scheme.Opens.topIso V).inv.hom).obj
        ((moduleGlobalSections (V : Scheme)).obj
          (((Scheme.Modules.pushforward (f ∣_ V)).rightDerivedPlus (d : ℤ)).obj
            ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).obj F))) ≅
      ModuleCat.of Γ(Y, V)
        Γ(((Scheme.Modules.pushforward f).rightDerivedPlus (d : ℤ)).obj F, V) :=
  (ModuleCat.restrictScalars (Scheme.Opens.topIso V).inv.hom).mapIso
      ((moduleGlobalSections (V : Scheme)).mapIso
        (rightDerivedPlusRestrictObjIso f V d F)) ≪≫
    openSectionsModuleIso _ V

/-- **The gated sections form of [Stacks, Tag 01XK] over `V` factors through the ungated
[Stacks, Tag 01E5] on sections.** `…TopDegreeBaseChange.affineOpenCohomologyIsoSections` is
[Stacks, Tag 01XK] at the restricted morphism, read under the restriction of scalars along
`AlgebraicGeometry.Scheme.Opens.topIso`, followed by `rightDerivedPlusRestrictSectionsIso`.

So the comparison the previous declaration isolates is the same morphism that was already there,
and the four hypotheses belong to the 01XK factor alone. -/
theorem affineOpenCohomologyIsoSections_eq {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] (V : Y.Opens) [IsAffine (V : Scheme)]
    (F : X.Modules) [F.IsQuasicoherent] (d : ℕ) :
    affineOpenCohomologyIsoSections f V F d =
      (ModuleCat.restrictScalars (Scheme.Opens.topIso V).inv.hom).mapIso
          ((cohomologyIsoGlobalSectionsRightDerivedPushforward (f ∣_ V) (d : ℤ)).app
            ⟨(Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).obj F, inferInstance⟩) ≪≫
        rightDerivedPlusRestrictSectionsIso f V d F := by
  simp only [affineOpenCohomologyIsoSections, rightDerivedPlusRestrictSectionsIso,
    Functor.mapIso_trans]
  exact Iso.trans_assoc _ _ _

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
