module

public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.GysinForgetLocalCohomologySheafRestrict
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.GysinTargetExcisionAbelianComparison

/-!
# The abelian reading of the derived excision is the abelian excision

Let `Y` be a scheme, `T ⊆ Y` a closed subset, `W ⊆ Y` an open subscheme and `n` a degree.  The
development carries two comparisons `(i_*ℋ ⁿ_T(ℱ_ab))|_W ⟶ i'_*ℋ ⁿ_{W ∩ T}(ℱ_ab|_W)`:

* `Stacks.Gysin.excisionAbComparison`, the underlying morphism of abelian sheaves of the
  **derived** excision of [Stacks, Tag 0G78] conjugated by the two copies of
  [Stacks, Tag 0G74] part (2); and
* `Stacks.Gysin.abelianExcision`, the **classical** excision for the local cohomology sheaves of
  sheaves of abelian groups, which is a natural transformation on *all* abelian sheaves.

This file proves that they agree —
`Stacks.Gysin.ExcisionAbComparisonEqAbelianExcision`, the one equation the implementation notes of
`StacksFrontier/AlgebraicGeometry/DeRham/Gysin/GysinAbelianExcisionBridge.lean` recorded as open —
and therefore that `Stacks.Gysin.SupportCohomologyRestrictAbNatural` holds for **every** morphism
of the underlying abelian sheaves, the relative de Rham differential included.

Nothing new is proved about either excision.  The two inputs are proved and unconditional:

* `Stacks.Gysin.supportCohomologyRestrictIso_hom_eq_localCohomologyRestrictNatIso` — the derived
  excision of [Stacks, Tag 0G78] on degree-`n` cohomology sheaves is
  `Stacks.Perfect.LocalCohomologyExcision.localCohomologyRestrictNatIso`, conjugated by the
  bridge `Stacks.Gysin.supportCohomologyOnIso` between the two spellings of `i_*ℋ ⁿ_T`; and
* `Stacks.Gysin.forget_localCohomologySheafRestrict_comm` — forgetting the module structure
  carries that classical module excision to the classical abelian excision, in every degree.

What this file adds is the cancellation that turns the second square into the first equation: the
bridge `Stacks.Gysin.supportCohomologyOnIso` and the comparison of [Stacks, Tag 0G74] part (2) on
`Y` cancel against their inverses, and what is left on each side is one of the two comparisons.

## Main results

* `Stacks.Gysin.excisionAbComparison_eq_abelianExcision`: **the two comparisons agree**, at the
  underlying abelian sheaf of every `𝒪_Y`-module.
* `Stacks.Gysin.excisionAbComparisonEqAbelianExcision`:
  `Stacks.Gysin.ExcisionAbComparisonEqAbelianExcision`, that equation as the named `Prop`.
* `Stacks.Gysin.supportCohomologyRestrictAbNatural`: **the abelian reading of the derived excision
  commutes with the action of [Stacks, Tag 0G74] part (2) on an arbitrary morphism of the
  underlying abelian sheaves** — in particular on one that is `𝒪_Y`-linear for no `Y`, which is
  the case `Stacks.Gysin.supportCohomologyRestrictAbNatural_abelianSheaf_map` cannot reach and the
  case the chart transport of [Stacks, Tag 0G87] needs.

## Implementation notes

**The shape of the cancellation.**  Write `β` for `Stacks.Gysin.supportCohomologyOnIso` on `Y`,
`β'` for its counterpart on the chart, `λ` and `λ'` for the two copies of [Stacks, Tag 0G74]
part (2), and `κ` for `localCohomologyRestrictNatIso`.  The first input reads the derived excision
as `β ≫ κ ≫ β'⁻¹` and the second says

`(κ ≫ β'⁻¹ ≫ λ')_ab = (β⁻¹ ≫ λ)_ab|_W ≫ abelianExcision`,

so conjugating by `λ⁻¹` on the left and `λ'` on the right turns the derived comparison into
`λ⁻¹|_W ≫ β|_W ≫ (β⁻¹ ≫ λ)|_W ≫ abelianExcision`, in which the inner four factors are the image
under the restriction of abelian sheaves of two mutually inverse pairs.  That cancellation is
`leg_cancel`, and the three-step assembly is `chase`.

**Where the two readings of the category of abelian sheaves meet.**  The chart's side of
`Stacks.Gysin.forget_localCohomologySheafRestrict_comm` is stated in the spelling of
`Stacks.Cohomology.DegreewiseExcisionSquare`: the forgetful functor as
`CategoryTheory.SheafOfModules.toSheaf` at the structure sheaf of the underlying ringed space, the
restriction of abelian sheaves as
`Stacks.Cohomology.RestrictForgetComparison.restrictAbelian`, and the module excision as
`Stacks.Cohomology.DegreewiseExcisionSquare.moduleExcisionEndo`.  The equation proved here is in
the Gysin spelling — `Stacks.Perfect.AbelianFraction.abelianSheaf`,
`Stacks.Gysin.abelianRestrict` and `localCohomologyRestrictNatIso`.  Each pair is definitionally
equal, and the crossing is confined to the single declaration `forgetSquare_gysin`, whose proof is
the degreewise square and nothing else; the implementation notes of
`StacksFrontier/AlgebraicGeometry/DeRham/Gysin/GysinForgetLocalCohomologySheafRestrict.lean` record
what each crossing costs, and the `attribute [local implicit_reducible]` block below is copied
from there for the same reason.

Everything downstream of `forgetSquare_gysin` is in one reading, and `chase` is stated at an
arbitrary category with every object implicit and every morphism explicit, so applying it reads
each object off a given morphism instead of solving for it.

**No `@[stacks ...]` attribute is attached here.**  Both excisions carry their own tags —
[Stacks, Tag 0G78] for the derived one and [Stacks, Tag 015Z] for the classical one — and this is
their comparison; the square of [Stacks, Tag 0G87] is what it is an input to, and it is registered
in `StacksFrontier/AlgebraicGeometry/DeRham/Gysin/GysinDeRhamConormalRank.lean`.

## References

* [Stacks Project, Tag 0G87](https://stacks.math.columbia.edu/tag/0G87)
* [Stacks Project, Remark 20.34.12 (Tag 0G78)](https://stacks.math.columbia.edu/tag/0G78)
* [Stacks Project, Lemma 20.34.8 (Tag 0G74)](https://stacks.math.columbia.edu/tag/0G74)
* [Stacks Project, Tag 015Z](https://stacks.math.columbia.edu/tag/015Z)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Cohomology.DegreewiseExcisionSquare (moduleExcisionEndo)
open Stacks.Cohomology.RestrictForgetComparison (restrictAbelian)
open Stacks.Cohomology.SupportedComplexes (abelianLocalCohomologySheafRestrictNatIso)
open Stacks.Perfect.AbelianFraction (abelianSheaf)
open Stacks.Perfect.GysinAbelianSquare (abelianLocalCohomologyPushforward
  supportCohomologySheafForgetIso)
open Stacks.Perfect.LocalCohomologyExcision (localCohomologyRestrictNatIso)

universe u

namespace Stacks.Gysin

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local implicit_reducible] AlgebraicGeometry.Scheme.Modules
  Stacks.Perfect.AbelianFraction.abelianSheaf Stacks.Gysin.abelianRestrict
  Stacks.Gysin.abelianExcision Stacks.Gysin.supportCohomologyRestrictAbHom
  Stacks.Cohomology.DegreewiseExcisionSquare.moduleExcisionEndo
  Stacks.Cohomology.DegreewiseExcisionSquare.abelianExcisionEndo
  Stacks.Perfect.LocalCohomologyExcision.localCohomologyOn
  Stacks.Perfect.LocalCohomologyExcision.supportedSectionsOn
  Stacks.Cohomology.SupportedComplexes.abelianLocalCohomologySheafPushforwardIso
  Stacks.Cohomology.SupportedComplexes.abelianLocalCohomologySheafRestrictNatIso

/-! ### The formal chase, at an arbitrary category -/

/-- **The three-step chase that turns the forget square into the equation of the two
comparisons.**  Given a factorisation `hm` of the middle arrow, the square `hsq` and the
cancellation `hid` of the two outer conjugating pairs, the composite `u ≫ m ≫ l` is `ae`.

Stated at an arbitrary category with every object implicit and every morphism explicit: the
objects are then read off the given morphisms rather than solved for, so the one place the two
definitionally equal spellings of the category of abelian sheaves on the chart have to meet is a
comparison of objects. -/
private theorem chase {D : Type*} [Category* D] {s p q₁ q₂ p₂ t : D}
    (u : s ⟶ p) (v : p ⟶ q₁) (w : q₁ ⟶ q₂) (b : q₂ ⟶ p₂) (l : p₂ ⟶ t)
    (m : p ⟶ p₂) (r : q₁ ⟶ s) (ae : s ⟶ t)
    (hm : m = v ≫ w ≫ b) (hsq : w ≫ b ≫ l = r ≫ ae)
    (hid : u ≫ v ≫ r = CategoryStruct.id s) :
    u ≫ m ≫ l = ae := by
  simp only [hm, Category.assoc, hsq]
  rw [← Category.assoc v, ← Category.assoc, hid, Category.id_comp]

/-! ### The two inputs, in the Gysin spelling -/

section Inputs

variable {Y : Scheme.{u}} (W : Y.Opens) {T : Set Y} (hT : IsClosed T)
  (hTW : IsClosed (W.ι ⁻¹' T)) (n : ℕ) (F : Y.Modules)

/-- **The abelian reading of the derived excision, split into its three factors.**  This is
`Stacks.Gysin.supportCohomologyRestrictIso_hom_eq_localCohomologyRestrictNatIso` carried through
the forgetful functor, the first factor read back as the restriction of abelian sheaves of a
morphism on `Y` by `Stacks.Gysin.restrictAbHom_abelianSheaf_map`. -/
private theorem supportCohomologyRestrictAbHom_eq :
    supportCohomologyRestrictAbHom W hT hTW (n : ℤ) F =
      (abelianRestrict W).map
          ((abelianSheaf Y).map ((supportCohomologyOnIso Y T hT n).hom.app F)) ≫
        (abelianSheaf W.toScheme).map ((localCohomologyRestrictNatIso T W n).hom.app F) ≫
          (abelianSheaf W.toScheme).map
            ((supportCohomologyOnIso W.toScheme (W.ι ⁻¹' T) hTW n).inv.app
              ((Scheme.Modules.restrictFunctor W.ι).obj F)) :=
  (congrArg (abelianSheaf W.toScheme).map
      (supportCohomologyRestrictIso_hom_eq_localCohomologyRestrictNatIso W hT hTW n F)).trans
    (Functor.map_comp₃ (abelianSheaf W.toScheme) _ _ _)

/-- **The degree-`n` forget square, in the Gysin spelling.**  The left-hand side is
`Stacks.Gysin.forget_localCohomologySheafRestrict_comm` with the module excision written as
`localCohomologyRestrictNatIso` under `Stacks.Perfect.AbelianFraction.abelianSheaf`, and the
right-hand side is its ambient leg folded by
`Stacks.Gysin.restrictAbelian_map_localCohomologyForgetLeg` and written with
`Stacks.Gysin.abelianRestrict`.

Each of those two is a definitional identity of a single factor, and this is the only declaration
in the file that crosses the two readings. -/
private theorem forgetSquare_gysin :
    (abelianSheaf W.toScheme).map ((localCohomologyRestrictNatIso T W n).hom.app F) ≫
        (abelianSheaf W.toScheme).map
            ((supportCohomologyOnIso W.toScheme (W.ι ⁻¹' T) hTW n).inv.app
              ((Scheme.Modules.restrictFunctor W.ι).obj F)) ≫
          (supportCohomologySheafForgetIso hTW n).hom.app
            ((Scheme.Modules.restrictFunctor W.ι).obj F) =
      (abelianRestrict W).map
          ((abelianSheaf Y).map ((supportCohomologyOnIso Y T hT n).inv.app F) ≫
            (supportCohomologySheafForgetIso hT n).hom.app F) ≫
        abelianExcision W hT hTW n ((abelianSheaf Y).obj F) :=
  (forget_localCohomologySheafRestrict_comm W hT hTW n F).trans
    (congrArg
      (fun x => x ≫
        (abelianLocalCohomologySheafRestrictNatIso (X := Y.carrier) T W hT hTW n).hom.app
          ((abelianSheaf Y).obj F))
      (restrictAbelian_map_localCohomologyForgetLeg W hT n F).symm)

/-! ### The cancellation of the two conjugating pairs -/

/-- The bridge `Stacks.Gysin.supportCohomologyOnIso` and the comparison of [Stacks, Tag 0G74]
part (2) on `Y`, each cancelled against its inverse, on the underlying abelian sheaves. -/
private theorem legIdentity :
    (supportCohomologySheafForgetIso hT n).inv.app F ≫
        (abelianSheaf Y).map ((supportCohomologyOnIso Y T hT n).hom.app F) ≫
          ((abelianSheaf Y).map ((supportCohomologyOnIso Y T hT n).inv.app F) ≫
            (supportCohomologySheafForgetIso hT n).hom.app F) =
      CategoryStruct.id
        ((abelianLocalCohomologyPushforward Y.toRingedSpace T hT n).obj
          ((abelianSheaf Y).obj F)) := by
  rw [← Category.assoc ((abelianSheaf Y).map ((supportCohomologyOnIso Y T hT n).hom.app F)),
    ← (abelianSheaf Y).map_comp, Iso.hom_inv_id_app, (abelianSheaf Y).map_id, Category.id_comp,
    Iso.inv_hom_id_app]
  rfl

/-- `legIdentity` restricted to the chart: the three factors are images under
`Stacks.Gysin.abelianRestrict` of morphisms on `Y`, so the functor collapses them into one and
the identity is carried along. -/
private theorem leg_cancel :
    (abelianRestrict W).map ((supportCohomologySheafForgetIso hT n).inv.app F) ≫
        (abelianRestrict W).map
            ((abelianSheaf Y).map ((supportCohomologyOnIso Y T hT n).hom.app F)) ≫
          (abelianRestrict W).map
            ((abelianSheaf Y).map ((supportCohomologyOnIso Y T hT n).inv.app F) ≫
              (supportCohomologySheafForgetIso hT n).hom.app F) =
      CategoryStruct.id
        ((abelianRestrict W).obj
          ((abelianLocalCohomologyPushforward Y.toRingedSpace T hT n).obj
            ((abelianSheaf Y).obj F))) :=
  ((abelianRestrict W).map_comp₃ _ _ _).symm.trans
    ((congrArg (abelianRestrict W).map (legIdentity hT n F)).trans
      ((abelianRestrict W).map_id _))

end Inputs

/-! ### The two comparisons agree -/

section Agreement

variable {Y : Scheme.{u}} (W : Y.Opens) {T : Set Y} (hT : IsClosed T)
  (hTW : IsClosed (W.ι ⁻¹' T)) (n : ℕ)

/-- **The abelian reading of the derived excision of [Stacks, Tag 0G78] is the classical excision
for the local cohomology sheaves of sheaves of abelian groups**, at the underlying abelian sheaf
of every `𝒪_Y`-module.

Both sides are morphisms `(i_*ℋ ⁿ_T(ℱ_ab))|_W ⟶ i'_*ℋ ⁿ_{W ∩ T}(ℱ_ab|_W)`, one built from the
derived excision of [Stacks, Tag 0G78] conjugated by the two copies of [Stacks, Tag 0G74]
part (2) and one from the classical right derived functors of the abelian sections with support.
This is the derived-versus-classical comparison that the implementation notes of
`StacksFrontier/AlgebraicGeometry/DeRham/Gysin/GysinAbelianExcisionBridge.lean` recorded as the one
statement left between the library and the square of [Stacks, Tag 0G87]. -/
theorem excisionAbComparison_eq_abelianExcision (F : Y.Modules) :
    excisionAbComparison W hT hTW n F = abelianExcision W hT hTW n ((abelianSheaf Y).obj F) :=
  (excisionAbComparison_eq W hT hTW n F).trans
    (chase
      ((abelianRestrict W).map ((supportCohomologySheafForgetIso hT n).inv.app F))
      ((abelianRestrict W).map
        ((abelianSheaf Y).map ((supportCohomologyOnIso Y T hT n).hom.app F)))
      ((abelianSheaf W.toScheme).map ((localCohomologyRestrictNatIso T W n).hom.app F))
      ((abelianSheaf W.toScheme).map
        ((supportCohomologyOnIso W.toScheme (W.ι ⁻¹' T) hTW n).inv.app
          ((Scheme.Modules.restrictFunctor W.ι).obj F)))
      ((supportCohomologySheafForgetIso hTW n).hom.app
        ((Scheme.Modules.restrictFunctor W.ι).obj F))
      (supportCohomologyRestrictAbHom W hT hTW (n : ℤ) F)
      ((abelianRestrict W).map
        ((abelianSheaf Y).map ((supportCohomologyOnIso Y T hT n).inv.app F) ≫
          (supportCohomologySheafForgetIso hT n).hom.app F))
      (abelianExcision W hT hTW n ((abelianSheaf Y).obj F))
      (supportCohomologyRestrictAbHom_eq W hT hTW n F)
      (forgetSquare_gysin W hT hTW n F)
      (leg_cancel W hT n F))

/-- `Stacks.Gysin.ExcisionAbComparisonEqAbelianExcision`: the equation of
`excisionAbComparison_eq_abelianExcision` as the named `Prop`, which is the shape
`Stacks.Gysin.supportCohomologyRestrictAbNatural_of_excisionAbComparison_eq` consumes. -/
theorem excisionAbComparisonEqAbelianExcision :
    ExcisionAbComparisonEqAbelianExcision W hT hTW n :=
  fun F => excisionAbComparison_eq_abelianExcision W hT hTW n F

/-- **The compatibility the square of [Stacks, Tag 0G87] needs, for every morphism of the
underlying abelian sheaves.**  The abelian reading of the derived excision of
[Stacks, Tag 0G78] commutes with the action of [Stacks, Tag 0G74] part (2) on an arbitrary
morphism `ψ` of the underlying abelian sheaves — in particular on the relative de Rham
differential of `X/S`, which is `𝒪_X`-linear for no `X`.

`Stacks.Gysin.supportCohomologyRestrictAbNatural_abelianSheaf_map` is the `𝒪_Y`-linear case; this
is the general one, and it follows from `excisionAbComparisonEqAbelianExcision` by
`Stacks.Gysin.supportCohomologyRestrictAbNatural_of_excisionAbComparison_eq`, the content of that
reduction being that the classical excision is a natural transformation on **all** sheaves of
abelian groups. -/
theorem supportCohomologyRestrictAbNatural {F G : Y.Modules}
    (ψ : (abelianSheaf Y).obj F ⟶ (abelianSheaf Y).obj G) :
    SupportCohomologyRestrictAbNatural W hT hTW n ψ :=
  supportCohomologyRestrictAbNatural_of_excisionAbComparison_eq W hT hTW n
    (excisionAbComparisonEqAbelianExcision W hT hTW n) ψ

end Agreement

end Stacks.Gysin

end
