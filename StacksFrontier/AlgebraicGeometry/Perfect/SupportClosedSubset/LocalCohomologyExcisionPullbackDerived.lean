module

public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.LocalCohomologyExcisionPullback

/-!
# Excision for sheaf local cohomology: the pullback spelling is the restriction spelling

The project carries excision for the right derived functors of the subsheaf of sections with
support in **two spellings of one functor**: along the abstract pullback
`RingedSpaceModuleAdjunction.modulePullback` of the ringed-space inclusion of an open subscheme,
as `Stacks.Cohomology.SupportedComplexes.supportedSectionsRightDerivedPullbackNatIso`, and along
`AlgebraicGeometry.Scheme.Modules.restrictFunctor` of the inclusion of that open subscheme, as
`Stacks.Perfect.LocalCohomologyExcision.localCohomologyRestrictNatIso`.  The two functors are
identified by `Stacks.Gysin.modulePullbackRestrictFunctorIso`.  This file carries the excision
across that identification in **every degree**; the degree-zero half is
`supportedSectionsRestrictNatIso_eq_pullback` in
`Stacks.Perfect.LocalCohomologyExcision`'s `LocalCohomologyExcisionPullback`.

## Main definitions and results

* `localCohomologyRestrictNatIso_eq_pullback`: **the classical degree-`n` excision for the
  right derived functors of sections with support agrees across the two spellings of
  restriction to an open subscheme.**  Both excisions are built by the same recipe —
  `Stacks.Cohomology.ModuleComparison.rightDerivedCompIso` to move the restriction out of a
  right derived functor, then `Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso`
  to move it back in — and `Stacks.Gysin.modulePullbackRestrictFunctorIso` intertwines them.
* `modulePullbackOn` and its five homological instances, with
  `modulePullbackOnRestrictIso`, `supportedSectionsPullbackOnIso` and
  `supportedSectionsPullbackOnTargetIso`: the abstract pullback and the three comparisons
  along it, written at the `AlgebraicGeometry.Scheme.Modules` spelling of the categories of
  modules.  These exist for the reason `supportedSectionsOn` does; see the implementation
  notes.

## Implementation notes

**The mathematics is three existing naturality statements and a diagram chase.**  Writing `H_T`
for the sections supported on `T`, `f^*` for the abstract pullback and `(-)|_W` for
`restrictFunctor`, the chase composes:

* `Stacks.Cohomology.DerivedCompTransport.rightDerivedCompIso_hom_app_natTrans` for the first
  factor, at the two exact functors `f^*` and `(-)|_W` over the **common** target
  `(-)|_W ⋙ H_{W ∩ T}` — which is what `supportedSectionsPullbackRestrictTargetIso` was built
  to supply — with `supportedSectionsRestrictNatIso_eq_pullback` as the degree-zero input;
* `Stacks.DerivedIndexing.moduleComparison_rightDerivedCompIso_hom_app` to move that target
  back to `f^* ⋙ H_{W ∩ T}`, applied to both comparisons: it computes each as one and the same
  `rightDerivedCompIso` inverse followed by the right derived functor of the degree-zero datum,
  so moving the target costs exactly `CategoryTheory.NatTrans.rightDerived_comp` applied to
  `supportedSectionsPullbackRestrictTargetIso`, whose `hom` *is* the pullback comparison
  followed by the whiskered identification, by `rfl`;
* `Stacks.Cohomology.DerivedCompTransport.compRightDerivedNatIso_hom_app_natTrans_exact` for
  the second factor.

**The obstacle is the spelling, and the fix is an ascribed `def`.**
`AlgebraicGeometry.Scheme.Modules X` and `SheafOfModules (structureSheafRing X.toRingedSpace)`
are definitionally equal but carry different *syntactic* `Category` and `Preadditive`
instances — see the "Two names for one category" paragraph of
`Stacks.Perfect.LocalCohomologyExcision`'s module docstring.  Here `supportedSectionsOn Y T`
fixes the source category at the `Scheme.Modules` spelling while the codomain of
`modulePullback f` comes out at the `SheafOfModules` spelling, so every homological side
condition on the pullback is demanded at a **mixed** instance pair — `Category` from
`Scheme.Modules`, `Preadditive` through `CategoryTheory.Abelian.toPreadditive` of the
`Scheme.Modules` instance — that matches no recorded instance, and instance search, running at
`instances` transparency, cannot unfold the plain `def` `AlgebraicGeometry.Scheme.Modules` to
see that it is the same pair.  Supplying the instances as local hypotheses does not help: a
hypothesis stated at the `SheafOfModules` spelling is a different syntactic proposition.

The fix is the one `supportedSectionsOn` itself uses: `modulePullbackOn` is `modulePullback`
of the ringed-space inclusion with its type **ascribed** at the `Scheme.Modules` spelling, and
its five homological instances are recorded at that spelling, each transported from the
`SheafOfModules` one by a type ascription — which elaborates at default transparency, where the
`def` does unfold.  The three comparisons are then restated at the ascribed functor
(`modulePullbackOnRestrictIso`, `supportedSectionsPullbackOnIso`,
`supportedSectionsPullbackOnTargetIso`, each the corresponding library isomorphism with its type
ascribed), and the whole chase runs inside one consistent spelling.  The statement itself needs
none of this: it mentions only already-elaborated definitions, so it forces no instance
synthesis, and the two spellings meet only in its `Eq`, which is checked at default
transparency.

**`rw` is not usable at these junctions**, the compositions on the two sides belonging to two
syntactically different categories.  Both chases are therefore `private theorem`s at a variable
category with the objects implicit and the morphisms explicit, applied by a single `exact`, as
`mono_square` and `paste_two` of `LocalCohomologyExcisionPullback` are.

**No `@[stacks ...]` attribute is attached**: this is a passage between two spellings of one
construction, not the statement of a tag, exactly as for `localCohomologyRestrictNatIso` and
`supportedSectionsRestrictNatIso_eq_pullback` themselves.

## References

* [Stacks Project, Remark 17.13.5 (Tag 0G6N)](https://stacks.math.columbia.edu/tag/0G6N)
* [Stacks Project, Tag 015Z](https://stacks.math.columbia.edu/tag/015Z)
* [Stacks Project, Tag 01E1](https://stacks.math.columbia.edu/tag/01E1)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.SupportedComplexes
open Stacks.SheafOfModules.SupportedSections

universe u

attribute [local implicit_reducible] CategoryTheory.Functor.sheafPushforwardContinuous

namespace Stacks.Perfect.LocalCohomologyExcision

/-! ### Two chases at a variable category -/

/-- **The crossing chase.**  Two paths out of `o₁` into `o₅`, each a composite of two factors,
are equal once the first factors are intertwined through a common `t`, the intertwining is
reassociated through `o₄`, and the second factors are intertwined there.

Stated at an arbitrary category with the objects implicit and the morphisms explicit, so that it
applies by a single `exact`: the two spellings of the category of modules on the open subscheme
are definitionally but not syntactically equal, and `rw` is not usable across them. -/
private theorem crossing_chase {C : Type*} [Category* C] {o₁ o₂ o₃ o₄ o₅ o₆ : C}
    (u : o₁ ⟶ o₂) (v : o₂ ⟶ o₃) (w : o₃ ⟶ o₅) (t : o₁ ⟶ o₃) (x : o₁ ⟶ o₄) (k : o₄ ⟶ o₃)
    (y : o₄ ⟶ o₆) (z : o₆ ⟶ o₅)
    (h₁ : u ≫ v = t) (h₂ : t = x ≫ k) (h₃ : k ≫ w = y ≫ z) :
    u ≫ v ≫ w = (x ≫ y) ≫ z := by
  rw [← Category.assoc, h₁, h₂, Category.assoc, h₃, Category.assoc]

/-- **Reassociating two morphisms computed through a common first factor.**  If `t` and `x` are
both `i` followed by something, and the two somethings differ by `k`, then `t` is `x` followed
by `k`.  Stated at an arbitrary category with the objects implicit and the morphisms
explicit. -/
private theorem regroup {C : Type*} [Category* C] {o₁ o₃ o₄ o₇ : C}
    (i : o₁ ⟶ o₇) (a : o₇ ⟶ o₄) (k : o₄ ⟶ o₃) (b : o₇ ⟶ o₃) (t : o₁ ⟶ o₃) (x : o₁ ⟶ o₄)
    (ht : t = i ≫ b) (hx : x = i ≫ a) (hb : b = a ≫ k) : t = x ≫ k := by
  rw [ht, hx, hb, Category.assoc]

/-! ### The abstract pullback, at the `Scheme.Modules` spelling -/

variable {Y : Scheme.{u}} (T : Set Y) (W : Y.Opens)

/-- Pullback of modules along the ringed-space inclusion of the open subscheme `W`, with its
type written at the `AlgebraicGeometry.Scheme.Modules` spelling of the categories of modules.
See the module docstring: this ascription is what makes the functor's homological side
conditions findable in a statement that also mentions `supportedSectionsOn`. -/
def modulePullbackOn (W : Y.Opens) : Y.Modules ⥤ W.toScheme.Modules :=
  modulePullback (Y.toRingedSpace.ofRestrict W.isOpenEmbedding)

/-- Pullback along the inclusion of an open subscheme is additive. -/
instance modulePullbackOn_additive (W : Y.Opens) : (modulePullbackOn W).Additive :=
  inferInstanceAs (modulePullback (Y.toRingedSpace.ofRestrict W.isOpenEmbedding)).Additive

/-- Pullback along the inclusion of an open subscheme preserves homology, being exact. -/
instance modulePullbackOn_preservesHomology (W : Y.Opens) :
    (modulePullbackOn W).PreservesHomology :=
  Stacks.Cohomology.openImmersionModulePullback_preservesHomology
    (Y.toRingedSpace.ofRestrict W.isOpenEmbedding)

/-- Pullback along the inclusion of an open subscheme preserves finite limits. -/
instance modulePullbackOn_preservesFiniteLimits (W : Y.Opens) :
    PreservesFiniteLimits (modulePullbackOn W) :=
  preservesFiniteLimits_modulePullback_of_isOpenImmersion
    (Y.toRingedSpace.ofRestrict W.isOpenEmbedding)

/-- Pullback along the inclusion of an open subscheme preserves finite colimits. -/
instance modulePullbackOn_preservesFiniteColimits (W : Y.Opens) :
    PreservesFiniteColimits (modulePullbackOn W) :=
  preservesFiniteColimits_modulePullback (Y.toRingedSpace.ofRestrict W.isOpenEmbedding)

/-- **[Stacks, Tag 01E1]** read at this spelling: pullback along the inclusion of an open
subscheme preserves injective objects. -/
instance modulePullbackOn_preservesInjectiveObjects (W : Y.Opens) :
    (modulePullbackOn W).PreservesInjectiveObjects :=
  Stacks.Cohomology.RelativeMayerVietoris.modulePullback_preservesInjectiveObjects
    (Y.toRingedSpace.ofRestrict W.isOpenEmbedding)

/-- `Stacks.Gysin.modulePullbackRestrictFunctorIso` at the ascribed spelling. -/
def modulePullbackOnRestrictIso (W : Y.Opens) :
    modulePullbackOn W ≅ Scheme.Modules.restrictFunctor W.ι :=
  Stacks.Gysin.modulePullbackRestrictFunctorIso W

/-- `Stacks.SheafOfModules.SupportedSections.supportedSectionsPullbackNatIso` — degree-zero
excision along the abstract pullback — at the ascribed spelling. -/
def supportedSectionsPullbackOnIso : supportedSectionsOn Y T ⋙ modulePullbackOn W ≅
    modulePullbackOn W ⋙ supportedSectionsOn W.toScheme (W.ι ⁻¹' T) :=
  supportedSectionsPullbackNatIso (Y.toRingedSpace.ofRestrict W.isOpenEmbedding) T

/-- `supportedSectionsPullbackRestrictTargetIso` — the same comparison with its target moved to
the `restrictFunctor` spelling — at the ascribed spelling. -/
def supportedSectionsPullbackOnTargetIso :
    supportedSectionsOn Y T ⋙ modulePullbackOn W ≅
      Scheme.Modules.restrictFunctor W.ι ⋙ supportedSectionsOn W.toScheme (W.ι ⁻¹' T) :=
  supportedSectionsPullbackRestrictTargetIso T W

/-! ### Excision across the two spellings, in every degree -/

/-- **Excision for sheaf local cohomology: the two spellings of the restriction agree in every
degree.**  Let `Y` be a scheme, `T ⊆ Y` a subset, `W ⊆ Y` an open subscheme and `n` a degree.
The classical degree-`n` excision `(Rⁿ H_T ℱ)|_W ≅ Rⁿ H_{W ∩ T}(ℱ|_W)` built along the abstract
pullback of the ringed-space inclusion of `W`
(`Stacks.Cohomology.SupportedComplexes.supportedSectionsRightDerivedPullbackNatIso`) and the one
built along `AlgebraicGeometry.Scheme.Modules.restrictFunctor` of the inclusion of `W`
(`localCohomologyRestrictNatIso`) correspond under
`Stacks.Gysin.modulePullbackRestrictFunctorIso`.

Both are `Stacks.Cohomology.ModuleComparison.rightDerivedCompIso` followed by
`Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso`, at the two degree-zero
comparisons that `supportedSectionsRestrictNatIso_eq_pullback` identifies; each factor is
carried across the identification by its own naturality, and the square is the two pasted.  No
closedness assumption on `T` is needed. -/
theorem localCohomologyRestrictNatIso_eq_pullback (n : ℕ) (M : Y.Modules) :
    (Stacks.Gysin.modulePullbackRestrictFunctorIso W).hom.app
          ((localCohomologyOn Y T n).obj M) ≫
        (localCohomologyRestrictNatIso T W n).hom.app M =
      (supportedSectionsRightDerivedPullbackNatIso
            (Y.toRingedSpace.ofRestrict W.isOpenEmbedding) T n).hom.app M ≫
        (localCohomologyOn W.toScheme (W.ι ⁻¹' T) n).map
          ((Stacks.Gysin.modulePullbackRestrictFunctorIso W).hom.app M) := by
  exact crossing_chase _ _ _ _ _ _ _ _
    (Stacks.Cohomology.DerivedCompTransport.rightDerivedCompIso_hom_app_natTrans
      (supportedSectionsOn Y T)
      (Scheme.Modules.restrictFunctor W.ι ⋙ supportedSectionsOn W.toScheme (W.ι ⁻¹' T))
      (modulePullbackOnRestrictIso W).hom (supportedSectionsPullbackOnTargetIso T W)
      (supportedSectionsRestrictNatIso T W)
      (supportedSectionsRestrictNatIso_eq_pullback T W) n M)
    (regroup _ _ _ _ _ _
      (Stacks.DerivedIndexing.moduleComparison_rightDerivedCompIso_hom_app
        (supportedSectionsOn Y T) (modulePullbackOn W)
        (Scheme.Modules.restrictFunctor W.ι ⋙ supportedSectionsOn W.toScheme (W.ι ⁻¹' T))
        (supportedSectionsPullbackOnTargetIso T W) n M)
      (Stacks.DerivedIndexing.moduleComparison_rightDerivedCompIso_hom_app
        (supportedSectionsOn Y T) (modulePullbackOn W)
        (modulePullbackOn W ⋙ supportedSectionsOn W.toScheme (W.ι ⁻¹' T))
        (supportedSectionsPullbackOnIso T W) n M)
      (NatTrans.congr_app
        (NatTrans.rightDerived_comp (supportedSectionsPullbackOnIso T W).hom
          (Functor.whiskerRight (modulePullbackOnRestrictIso W).hom
            (supportedSectionsOn W.toScheme (W.ι ⁻¹' T))) n) M))
    (Stacks.Cohomology.DerivedCompTransport.compRightDerivedNatIso_hom_app_natTrans_exact
      (modulePullbackOn W) (Scheme.Modules.restrictFunctor W.ι)
      (modulePullbackOnRestrictIso W).hom
      (supportedSectionsOn W.toScheme (W.ι ⁻¹' T)) n M)

end Stacks.Perfect.LocalCohomologyExcision

end
