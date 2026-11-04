module

public import StacksFrontier.AlgebraicGeometry.EtaleAlgebra.FlatBaseChange.AlgebraComparison
public import StacksFrontier.AlgebraicGeometry.FlatBaseChangeCohomology.AffineDegreeZero.Modules

/-!
# The degree-zero base-change normalisation over an open of the base

Let
```
X' --g'--> X
|f'        |f
S' --g-->  S
```
be a commutative square of schemes and let `ℱ` be an `𝒪_X`-module.  The file
`AffineDegreeZero/Modules.lean` pins the base-change morphism
`Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans` down by computing it on *global*
sections:  it carries the pullback along `g` of a global section of `f_* ℱ` to the pullback of
that section along `g'`.  This file records the same normalisation over an arbitrary open `U` of
`S`, which is the form the spreading-out arguments need — they have a section over a shrinking
neighbourhood of a point and never over the whole base.

Over a general `U` the two pullbacks no longer live over literally the same open:  the left-hand
one lands in sections over `f' ⁻¹ᵁ (g ⁻¹ᵁ U)` and the right-hand one over `g' ⁻¹ᵁ (f ⁻¹ᵁ U)`.
The square makes those two opens equal, so a restriction map between them mediates, and it is the
only thing that distinguishes these statements from the `_top` ones.

## Main results

* `Stacks.AlgebraicGeometry.FlatBaseChangeCohomology.baseChangeNatTrans_app_pullbackUnitSections`:
  the normalisation over an open `U` of `S`, in the
  `AlgebraicGeometry.Scheme.Modules.pullbackUnitSections` spelling, with the mediating
  restriction map explicit.
* `Stacks.AlgebraicGeometry.FlatBaseChangeCohomology.baseChangeNatTrans_app_pullbackSection`:
  the same in the `AlgebraicGeometry.Scheme.Modules.pullbackSection` spelling, where no
  restriction map survives because it has been absorbed into the target open.

Both are new statements;  the global-section forms
`baseChangeNatTrans_app_top_pullbackUnitSections` and
`baseChangeNatTrans_app_top_pullbackSectionsHom` of `AffineDegreeZero/Modules.lean` are the
`U = ⊤` cases and are left as they stand.

## References

* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry
open Stacks.AlgebraicGeometry.SectionsBaseChange

universe u

namespace Stacks.AlgebraicGeometry.FlatBaseChangeCohomology

variable {X X' S S' : Scheme.{u}} {f : X ⟶ S} {f' : X' ⟶ S'} {g : S' ⟶ S} {g' : X' ⟶ X}

/-- **The normalisation over an open of the base: the base-change morphism carries the pullback
of a section along `g` to its pullback along `g'`.**  This is what pins `baseChangeNatTrans` down
as *the* comparison between its two sheaves, over an arbitrary open of the base rather than only
over the whole base.

The target of the two pullbacks is the same group of sections read over two equal opens —
`f' ⁻¹ᵁ (g ⁻¹ᵁ U)` on the left, `g' ⁻¹ᵁ (f ⁻¹ᵁ U)` on the right — so the restriction map between
them appears on the right-hand side;  over `U = ⊤` it disappears, which is
`Stacks.AlgebraicGeometry.FlatBaseChangeCohomology.baseChangeNatTrans_app_top_pullbackUnitSections`.

The identification of the two composite direct images over `U` is
`Stacks.FundamentalGroup.pushforwardSquareIso_hom_app_app`, which already states it as the
presheaf map of an arbitrary morphism of opens. -/
theorem baseChangeNatTrans_app_pullbackUnitSections (w : g' ≫ f = f' ≫ g) (F : X.Modules)
    (U : S.Opens) (h : f' ⁻¹ᵁ (g ⁻¹ᵁ U) ≤ g' ⁻¹ᵁ (f ⁻¹ᵁ U)) (a : Γ(F, f ⁻¹ᵁ U)) :
    (((AffinePushforward.baseChangeNatTrans w).app F).app (g ⁻¹ᵁ U)).hom
        (pullbackUnitSections g ((Scheme.Modules.pushforward f).obj F) U a) =
      ((Scheme.Modules.pullback g').obj F).presheaf.map (homOfLE h).op
        (pullbackUnitSections g' F (f ⁻¹ᵁ U) a) := by
  have hh := congrArg (fun t => ((Scheme.Modules.Hom.app t U).hom) a)
    (pushforward_unit_comp_pushforwardSquareIso w F)
  simp only [Scheme.Modules.Hom.comp_app, Scheme.Modules.pushforward_map_app,
    Stacks.FundamentalGroup.pushforwardSquareIso_hom_app_app w _ U (homOfLE h)] at hh
  exact hh.symm

/-- **The normalisation in the `AlgebraicGeometry.Scheme.Hom.appLE` spelling.**  For opens `U` of
`S` and `V ≤ g ⁻¹ᵁ U` of `S'`, the base-change morphism read over `V` carries the pullback along
`g` of a section of `f_* F` over `U` to the pullback along `g'` of that section of `F` over
`f ⁻¹ᵁ U`, taken over `f' ⁻¹ᵁ V`.  No restriction map survives:  it has been absorbed into the
target open. -/
theorem baseChangeNatTrans_app_pullbackSection (w : g' ≫ f = f' ≫ g) (F : X.Modules)
    (U : S.Opens) (V : S'.Opens) (hV : V ≤ g ⁻¹ᵁ U)
    (h : f' ⁻¹ᵁ (g ⁻¹ᵁ U) ≤ g' ⁻¹ᵁ (f ⁻¹ᵁ U)) (hV' : f' ⁻¹ᵁ V ≤ g' ⁻¹ᵁ (f ⁻¹ᵁ U))
    (a : Γ(F, f ⁻¹ᵁ U)) :
    (((AffinePushforward.baseChangeNatTrans w).app F).app V).hom
        (Scheme.Modules.pullbackSection g ((Scheme.Modules.pushforward f).obj F) U V hV a) =
      Scheme.Modules.pullbackSection g' F (f ⁻¹ᵁ U) (f' ⁻¹ᵁ V) hV' a := by
  have hnat := PresheafOfModules.naturality_apply
    ((AffinePushforward.baseChangeNatTrans w).app F).val (homOfLE hV).op
    (pullbackUnitSections g ((Scheme.Modules.pushforward f).obj F) U a)
  rw [show (Scheme.Modules.pullbackSection g ((Scheme.Modules.pushforward f).obj F) U V hV a :
        Γ((Scheme.Modules.pullback g).obj ((Scheme.Modules.pushforward f).obj F), V)) =
      ((Scheme.Modules.pullback g).obj
          ((Scheme.Modules.pushforward f).obj F)).presheaf.map (homOfLE hV).op
        (pullbackUnitSections g ((Scheme.Modules.pushforward f).obj F) U a) from rfl]
  refine (hnat.trans (congrArg _ (baseChangeNatTrans_app_pullbackUnitSections w F U h a))).trans ?_
  show ((Scheme.Modules.pullback g').obj F).presheaf.map
      ((Opens.map f'.base).map (homOfLE hV)).op
      (((Scheme.Modules.pullback g').obj F).presheaf.map (homOfLE h).op
        (pullbackUnitSections g' F (f ⁻¹ᵁ U) a)) = _
  refine Eq.trans ?_ (map_pullbackUnitSections g' F (f ⁻¹ᵁ U) (f' ⁻¹ᵁ V) hV' a)
  rw [← ConcreteCategory.comp_apply, ← ((Scheme.Modules.pullback g').obj F).presheaf.map_comp]
  exact congrArg (fun t => ConcreteCategory.hom
      (((Scheme.Modules.pullback g').obj F).presheaf.map t)
      ((pullbackUnitSections g' F (f ⁻¹ᵁ U)) a)) (Subsingleton.elim _ _)

end Stacks.AlgebraicGeometry.FlatBaseChangeCohomology

end
