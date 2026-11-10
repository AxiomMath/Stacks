module

public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.GysinSupportCohomologyExcisionClassical
public import
 StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.LocalCohomologyExcisionPullbackDerived

/-!
# The derived excision of Tag 0G78 is the abelian excision, in the restriction spelling

Let `Y` be a scheme, `T ⊆ Y` closed, `W ⊆ Y` an open subscheme and `T' = W ∩ T`.  The project
has two excision isomorphisms for `i_*ℋ ⁿ_T`:

* the **derived** one of [Stacks, Tag 0G78], `Stacks.Gysin.supportCohomologyRestrictIso`, which
  is `Stacks.Perfect.SupportPushExcision.derivedSupportedPushforwardPullbackIso` read on
  degree-`n` cohomology sheaves; and
* the **abelian** one,
  `Stacks.Perfect.LocalCohomologyExcision.localCohomologyRestrictNatIso`, Mathlib's `ℕ`-indexed
  right derived functors of the subsheaf of sections supported on `T`, excised by
  [Stacks, Tag 015Z].

They agree, conjugated by the identification `β = Stacks.Gysin.supportCohomologyOnIso` of the
two spellings of `i_*ℋ ⁿ_T`:

`(supportCohomologyRestrictIso W hT hTW n ℱ).hom =
  (restrictFunctor W.ι).map (β.hom.app ℱ) ≫ (localCohomologyRestrictNatIso T W n).hom.app ℱ ≫
    β'.inv.app ((restrictFunctor W.ι).obj ℱ)`.

That is `supportCohomologyRestrictIso_hom_eq_localCohomologyRestrictNatIso`, the only result of
this file, and it is the coherence that the implementation notes of
`StacksFrontier/AlgebraicGeometry/DeRham/Gysin/GysinTargetExcision.lean` recorded as missing — the
one statement the square of [Stacks, Tag 0G87] needs from the abelian model, in the spelling
`AlgebraicGeometry.Scheme.Modules.restrictFunctor` in which [Stacks, Tag 0G87] is stated.

## Main results

* `Stacks.Gysin.supportCohomologyRestrictIso_hom_eq_localCohomologyRestrictNatIso`: **the
  derived excision of [Stacks, Tag 0G78] is the abelian excision.**

## Implementation notes

**All the mathematics is in the two inputs, and neither is in this file.**

* `Stacks.Gysin.supportCohomologyPullbackIso_hom_eq_supportedSectionsRightDerivedPullback` is the
  same statement in the `RingedSpaceModuleAdjunction.modulePullback` spelling of the
  restriction, with
  `Stacks.Cohomology.SupportedComplexes.supportedSectionsRightDerivedPullbackNatIso` as its
  middle factor.  Its five steps — the fold-in of the degree-zero datum, the uniqueness of right
  derived functors, the derived/classical square, the transport of the classical excision across
  the two spellings of the degree-zero functor, and the recognition of the two verticals as `β`
  and `β'` — are listed in its own module docstring.
* `Stacks.Perfect.LocalCohomologyExcision.localCohomologyRestrictNatIso_eq_pullback` carries that
  middle factor across `Stacks.Gysin.modulePullbackRestrictFunctorIso` to
  `localCohomologyRestrictNatIso`.

**What is left is one four-square chase.**  `supportCohomologyRestrictIso` *is*
`supportCohomologyPullbackIso` conjugated by `Stacks.Gysin.modulePullbackRestrictFunctorIso` —
that is `supportCohomologyRestrictIso_hom_eq_pullback` below, which holds by `rfl` — so the
proof is: substitute the pullback form, move the identification of the two spellings inwards past
`β` on the left and past `β'` on the right by naturality, replace the classical excision by
`localCohomologyRestrictNatIso`, and cancel the identification against its inverse.  Each step is
a naturality square of a natural transformation of the library; they are pasted by `restrict_chase`,
stated at a variable category with the objects implicit and the morphisms explicit and applied by
a single `exact`, because at these categories the two spellings of the category of modules on `W`
are definitionally but not syntactically equal and `rw` is not usable across them.

**No `@[stacks ...]` attribute is attached.**  This is the comparison of two constructions of one
isomorphism, not the statement of a tag: [Stacks, Tag 0G78] is the canonical map, which
`Stacks.Perfect.SupportPushExcision.supportedPullbackNatTrans` carries, and [Stacks, Tag 0G87] is
the square this is an input to.

## References

* [Stacks Project, Remark 20.34.12 (Tag 0G78)](https://stacks.math.columbia.edu/tag/0G78)
* [Stacks Project, Tag 0G87](https://stacks.math.columbia.edu/tag/0G87)
* [Stacks Project, Tag 015Z](https://stacks.math.columbia.edu/tag/015Z)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Perfect.LocalCohomologyExcision
open Stacks.Perfect.SupportedFraction

universe u

namespace Stacks.Gysin

attribute [local instance 10000] HasDerivedCategory.standard

variable {Y : Scheme.{u}} (W : Y.Opens) {T : Set Y} (hT : IsClosed T)
  (hTW : IsClosed (W.ι ⁻¹' T)) (n : ℕ) (F : Y.Modules)

/-! ### The restriction form is the pullback form conjugated -/

/-- **`Stacks.Gysin.supportCohomologyRestrictIso` is `supportCohomologyPullbackIso` conjugated by
`Stacks.Gysin.modulePullbackRestrictFunctorIso`.**  True by definition; recorded because the
comparison below is proved in the pullback spelling and transported here. -/
theorem supportCohomologyRestrictIso_hom_eq_pullback :
    (supportCohomologyRestrictIso W hT hTW (n : ℤ) F).hom =
      (modulePullbackRestrictFunctorIso W).inv.app
          ((supportCohomologySheafFunctor hT (n : ℤ)).obj F) ≫
        (supportCohomologyPullbackIso (Y.toRingedSpace.ofRestrict W.isOpenEmbedding)
            T hT (n : ℤ) F).hom ≫
          (supportCohomologySheafFunctor hTW (n : ℤ)).map
            ((modulePullbackRestrictFunctorIso W).hom.app F) := rfl

/-! ### The chase -/

/-- The four naturality squares pasted.  Stated at an arbitrary category with the objects
implicit and the morphisms explicit, so that it applies by a single `exact`: at the categories
of sheaves of modules on `W` the `AlgebraicGeometry.Scheme.Modules` spelling and the
`SheafOfModules (structureSheafRing _)` spelling are definitionally but not syntactically equal,
and a rewrite whose motive crosses them is not type-correct. -/
private theorem restrict_chase {D : Type*} [Category* D] {o₁ o₂ o₃ o₄ o₅ o₆ o₇ o₈ : D}
    (linv : o₁ ⟶ o₂) (fpb : o₂ ⟶ o₃) (cl : o₃ ⟶ o₄) (bi : o₄ ⟶ o₅) (scm : o₅ ⟶ o₆)
    (lrb : o₁ ⟶ o₇) (linv' : o₇ ⟶ o₃) (lh : o₃ ⟶ o₇) (lcr : o₇ ⟶ o₈) (lcm : o₄ ⟶ o₈)
    (bi' : o₈ ⟶ o₆)
    (hn1 : linv ≫ fpb = lrb ≫ linv') (hn2 : bi ≫ scm = lcm ≫ bi')
    (h6 : lh ≫ lcr = cl ≫ lcm) (hi : linv' ≫ lh = CategoryStruct.id o₇) :
    linv ≫ (fpb ≫ cl ≫ bi) ≫ scm = lrb ≫ lcr ≫ bi' := by
  simp only [Category.assoc]
  rw [reassoc_of% hn1, hn2, ← reassoc_of% h6, reassoc_of% hi]

/-! ### The comparison -/

/-- **The derived excision of [Stacks, Tag 0G78], read on degree-`n` cohomology sheaves, is the
abelian excision of the right derived functors of the sections with support, conjugated by
`Stacks.Gysin.supportCohomologyOnIso`.**

For a scheme `Y`, a closed `T ⊆ Y`, an open subscheme `W ⊆ Y`, `T' = W ∩ T`, a degree `n` and an
`𝒪_Y`-module `ℱ`:

`(supportCohomologyRestrictIso W hT hTW n ℱ).hom =
  (restrictFunctor W.ι).map (β.hom.app ℱ) ≫ (localCohomologyRestrictNatIso T W n).hom.app ℱ ≫
    β'.inv.app ((restrictFunctor W.ι).obj ℱ)`

with `β = Stacks.Gysin.supportCohomologyOnIso Y T hT n`, the identification of the cohomology
sheaf of `i_* R𝓗_T(ℱ[0])` with Mathlib's `Rⁿ H_T(ℱ)`, and `β'` its counterpart on `W`.

The left-hand side is the **derived** excision of [Stacks, Tag 0G78], which is what the chart
transports of the Gysin globalisation of [Stacks, Tag 0G86] use; the middle factor of the
right-hand side is the **abelian** excision, which is where the action of [Stacks, Tag 0G74]
part (2) on the de Rham differential lives.  Identifying them is the one input the square of
[Stacks, Tag 0G87] still needed from the abelian model, and the implementation notes of
`StacksFrontier/AlgebraicGeometry/DeRham/Gysin/GysinTargetExcision.lean` recorded it as the
coherence "the library does not have".

The proof is
`Stacks.Gysin.supportCohomologyPullbackIso_hom_eq_supportedSectionsRightDerivedPullback`, the
same statement in the `RingedSpaceModuleAdjunction.modulePullback` spelling, carried across
`Stacks.Gysin.modulePullbackRestrictFunctorIso` by
`Stacks.Perfect.LocalCohomologyExcision.localCohomologyRestrictNatIso_eq_pullback` and two
naturality squares. -/
theorem supportCohomologyRestrictIso_hom_eq_localCohomologyRestrictNatIso :
    (supportCohomologyRestrictIso W hT hTW (n : ℤ) F).hom =
      (Scheme.Modules.restrictFunctor W.ι).map ((supportCohomologyOnIso Y T hT n).hom.app F) ≫
        (localCohomologyRestrictNatIso T W n).hom.app F ≫
          (supportCohomologyOnIso W.toScheme (W.ι ⁻¹' T) hTW n).inv.app
            ((Scheme.Modules.restrictFunctor W.ι).obj F) := by
  rw [supportCohomologyRestrictIso_hom_eq_pullback W hT hTW n F,
    supportCohomologyPullbackIso_hom_eq_supportedSectionsRightDerivedPullback W T hT hTW n F]
  exact restrict_chase _ _ _ _ _ _ _ _ _ _ _
    (((modulePullbackRestrictFunctorIso W).inv.naturality
      ((supportCohomologyOnIso Y T hT n).hom.app F)).symm)
    (((supportCohomologyOnIso W.toScheme (W.ι ⁻¹' T) hTW n).inv.naturality
      ((modulePullbackRestrictFunctorIso W).hom.app F)).symm)
    (localCohomologyRestrictNatIso_eq_pullback T W n F)
    ((modulePullbackRestrictFunctorIso W).inv_hom_id_app
      ((localCohomologyOn Y T n).obj F))

end Stacks.Gysin

end
