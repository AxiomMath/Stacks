module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.BasePasting
public import StacksFrontier.Homology.DerivedIndexing.UnitSingleFunctoriality

/-!
# The derived comparison of a square on a complex concentrated in degree zero

Let `P : 𝒜₀ ⥤ 𝒜₁` and `P' : ℬ₀ ⥤ ℬ₁` be additive, let `U₂ : 𝒜₁ ⥤ ℬ₁` and `U₀ : 𝒜₀ ⥤ ℬ₀` be
additive with the right derived functor of `U₂` computed degreewise, and let
`τ : P ⋙ U₂ ⟶ U₀ ⋙ P'` be a comparison of the two composites.
`Stacks.Cohomology.BaseChange.derived` descends `τ` to a comparison `RP ⋙ RU₂ ⟶ RU₀ ⋙ RP'` of
bounded below right derived functors. This file computes that descent on the complexes
concentrated in degree zero, where the canonical map
`Stacks.DerivedIndexing.rightDerivedPlusUnitSingle` of each of the four functors is available.

The computation is the *target* side of the degreewise descent of a base change pasting law, the
counterpart of
`Stacks.EtaleCohomology.relativeLeray_comp_baseChangeSourceIso`: on the target the underived
comparison of the upper square meets its own descent, and the identity below is where they meet.

## Main results

* `Stacks.Cohomology.BaseChange.rightDerivedPlusCompTrans_comp_derived`: **the descent of `τ`,
  read through the comparison of the derived functors of the composites, is the derived functor
  of `τ`.** Both sides are transformations `R(P ⋙ U₂) ⟶ RU₀ ⋙ RP'`; they have the same
  composite with the derived-functor unit of `R(P ⋙ U₂)`, so
  `CategoryTheory.Functor.rightDerived_ext` applies.
* `Stacks.Cohomology.BaseChange.unitSingle_comp_derived`: **the derived comparison of the square
  on a complex concentrated in degree zero.** `τ` placed in degree zero, followed by the two
  canonical maps of the target leg, is the two canonical maps of the source leg followed by the
  derived comparison.

## Implementation notes

The descent `Stacks.Cohomology.BaseChange.derived` takes the comparison `e` between the
degreewise action of `U₂` on bounded below homotopy categories and its right derived functor as
an argument rather than deriving it from exactness. Only the hypothesis `e.hom` *is* the
derived-functor unit is used here, so that is what both results assume; it holds by `rfl` for
`Stacks.Cohomology.BaseChange.exactUnitIso` and for `asIso` of the unit, which are the two forms
the development produces. No exactness of `U₂` or of `U₀` is needed.

Both chases are run by `rw` with the rearranging equations supplied explicitly, rather than
through a chase lemma stated on variables in an abstract category. A chase lemma is the usual
device here — see `Stacks.EtaleCohomology.srcChase` — but at these types it is the *more*
expensive route: its ten implicit morphisms have to be solved against components of comparisons
of right derived functors, whose sources and targets agree only after unfolding
`CategoryTheory.Functor.rightDerivedFunctorPlus` and the localization of the bounded below
homotopy category, and that unification exhausts the declaration's heartbeat budget. Named
equations hand `rw` the instantiation for free. The residual identity is nonetheless split into
its two halves, one per declaration, because the budget is counted per declaration.

## References

* [Stacks Project, Tag 015M](https://stacks.math.columbia.edu/tag/015M)
* [Stacks Project, Tag 05T2](https://stacks.math.columbia.edu/tag/05T2)
* [Stacks Project, Tag 0F02](https://stacks.math.columbia.edu/tag/0F02)

Tags covered: none.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace Stacks.Cohomology.BaseChange

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-! ### The descent of a square, on a complex concentrated in degree zero -/

section Residual

variable {A₀ A₁ B₀ B₁ : Type u}
  [Category.{v} A₀] [Category.{v} A₁] [Category.{v} B₀] [Category.{v} B₁]
  [Abelian A₀] [Abelian A₁] [Abelian B₀] [Abelian B₁]
  [EnoughInjectives A₀] [EnoughInjectives A₁] [EnoughInjectives B₀]
  (P : A₀ ⥤ A₁) (P' : B₀ ⥤ B₁) (U₂ : A₁ ⥤ B₁) (U₀ : A₀ ⥤ B₀)
  [P.Additive] [P'.Additive] [U₂.Additive] [U₀.Additive]
  (τ : P ⋙ U₂ ⟶ U₀ ⋙ P')
  (e : U₂.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh ≅
    DerivedCategory.Plus.Qh ⋙ U₂.rightDerivedFunctorPlus)

/-- The derived-functor unit of `R(P ⋙ Q)`, followed by the comparison `R(P ⋙ Q) ⟶ RP ⋙ RQ`, is
the unit of `RQ` at `P(K)` followed by `RQ` applied to the unit of `RP` at `K`. -/
private theorem unit_comp_compTrans_app {C D E : Type u} [Category.{v} C] [Category.{v} D]
    [Category.{v} E] [Abelian C] [Abelian D] [Abelian E] [EnoughInjectives C] [EnoughInjectives D]
    (P : C ⥤ D) (Q : D ⥤ E) [P.Additive] [Q.Additive] (K : HomotopyCategory.Plus C) :
    (P ⋙ Q).rightDerivedFunctorPlusUnith.app K ≫
        (Stacks.DerivedIndexing.rightDerivedPlusCompTrans P Q).app
          (DerivedCategory.Plus.Qh.obj K) =
      Q.rightDerivedFunctorPlusUnith.app (P.mapHomotopyCategoryPlus.obj K) ≫
        Q.rightDerivedFunctorPlus.map (P.rightDerivedFunctorPlusUnith.app K) :=
  (Stacks.DerivedIndexing.rightDerivedPlusCompTrans_fac_app P Q K).trans
    (Stacks.DerivedIndexing.rightDerivedPlusCompUnit_app P Q K)

omit [EnoughInjectives A₀] in
/-- **The degreewise action on bounded below homotopy categories has one definition.**
`Stacks.Cohomology.BaseChange.mapPlus` and
`CategoryTheory.Functor.mapHomotopyCategoryPlusNatTrans` are the same transformation: both lift
`CategoryTheory.NatTrans.mapHomotopyCategory` through the inclusion of the bounded below
part. -/
public theorem mapPlus_eq_mapHomotopyCategoryPlusNatTrans {F G : A₀ ⥤ B₁} [F.Additive]
    [G.Additive] (σ : F ⟶ G) :
    mapPlus σ = Functor.mapHomotopyCategoryPlusNatTrans σ :=
  rfl

/-- **The unit of `RU₂` cancels the comparison `e`, leaving the two units of the target leg.**
This is `Stacks.Cohomology.BaseChange.onHomotopy_app` with the first factor cancelled; it is the
one computation the residual identity needs. -/
public theorem unit_comp_onHomotopy_app (he : e.hom = U₂.rightDerivedFunctorPlusUnith)
    (K : HomotopyCategory.Plus A₀) :
    U₂.rightDerivedFunctorPlusUnith.app (P.mapHomotopyCategoryPlus.obj K) ≫
        (onHomotopy P P' U₂ U₀ τ e).app K =
      DerivedCategory.Plus.Qh.map ((Functor.mapHomotopyCategoryPlusNatTrans τ).app K) ≫
        P'.rightDerivedFunctorPlusUnith.app (U₀.mapHomotopyCategoryPlus.obj K) ≫
          P'.rightDerivedFunctorPlus.map (U₀.rightDerivedFunctorPlusUnith.app K) := by
  rw [onHomotopy_app, ← Category.assoc, ← he, Iso.hom_inv_id_app, Category.id_comp,
    mapPlus_eq_mapHomotopyCategoryPlusNatTrans]

/-- **The source half of the residual identity.** The derived-functor unit of `R(P ⋙ U₂)`,
the comparison `R(P ⋙ U₂) ⟶ RP ⋙ RU₂` of [Stacks, Tag 05T2] and the descent
`Stacks.Cohomology.BaseChange.derived` compose to the degreewise action of `τ` followed by the
two units of the target leg: this is
`Stacks.DerivedIndexing.rightDerivedPlusCompTrans_fac_app`,
`Stacks.Cohomology.BaseChange.derived_fac_app` and `unit_comp_onHomotopy_app`. -/
public theorem unit_comp_compTrans_comp_derived_app
    (he : e.hom = U₂.rightDerivedFunctorPlusUnith) (K : HomotopyCategory.Plus A₀) :
    (P ⋙ U₂).rightDerivedFunctorPlusUnith.app K ≫
        (Stacks.DerivedIndexing.rightDerivedPlusCompTrans P U₂).app
            (DerivedCategory.Plus.Qh.obj K) ≫
          (derived P P' U₂ U₀ τ e).app (DerivedCategory.Plus.Qh.obj K) =
      DerivedCategory.Plus.Qh.map ((Functor.mapHomotopyCategoryPlusNatTrans τ).app K) ≫
        P'.rightDerivedFunctorPlusUnith.app (U₀.mapHomotopyCategoryPlus.obj K) ≫
          P'.rightDerivedFunctorPlus.map (U₀.rightDerivedFunctorPlusUnith.app K) := by
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (CategoryTheory.eq_whisker (unit_comp_compTrans_app P U₂ K) _) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (CategoryTheory.whisker_eq _ (derived_fac_app P P' U₂ U₀ τ e K)) ?_
  exact unit_comp_onHomotopy_app P P' U₂ U₀ τ e he K

omit [EnoughInjectives A₁] in
/-- **The target half of the residual identity.** The derived-functor unit of `R(P ⋙ U₂)`,
the right derived functor of `τ` and the comparison `R(U₀ ⋙ P') ⟶ RU₀ ⋙ RP'` compose to the
same thing: this is `Stacks.DerivedIndexing.rightDerivedFunctorPlusNatTrans_app` and
`Stacks.DerivedIndexing.rightDerivedPlusCompTrans_fac_app`. -/
public theorem unit_comp_natTrans_comp_compTrans_app (K : HomotopyCategory.Plus A₀) :
    (P ⋙ U₂).rightDerivedFunctorPlusUnith.app K ≫
        (Stacks.DerivedIndexing.rightDerivedFunctorPlusNatTrans τ).app
            (DerivedCategory.Plus.Qh.obj K) ≫
          (Stacks.DerivedIndexing.rightDerivedPlusCompTrans U₀ P').app
            (DerivedCategory.Plus.Qh.obj K) =
      DerivedCategory.Plus.Qh.map ((Functor.mapHomotopyCategoryPlusNatTrans τ).app K) ≫
        P'.rightDerivedFunctorPlusUnith.app (U₀.mapHomotopyCategoryPlus.obj K) ≫
          P'.rightDerivedFunctorPlus.map (U₀.rightDerivedFunctorPlusUnith.app K) := by
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans
    (CategoryTheory.eq_whisker
      (Stacks.DerivedIndexing.rightDerivedFunctorPlusNatTrans_app τ K) _) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  exact CategoryTheory.whisker_eq _ (unit_comp_compTrans_app U₀ P' K)

/-- **The descent of `τ : P ⋙ U₂ ⟶ U₀ ⋙ P'`, read through the comparisons of the derived
functors of the two composites, is the right derived functor of `τ`.** The comparison
`R(P ⋙ U₂) ⟶ RP ⋙ RU₂` of [Stacks, Tag 05T2] followed by
`Stacks.Cohomology.BaseChange.derived` is
`Stacks.DerivedIndexing.rightDerivedFunctorPlusNatTrans` of `τ` followed by the comparison
`R(U₀ ⋙ P') ⟶ RU₀ ⋙ RP'`.

Both sides are transformations out of `R(P ⋙ U₂)`, which is a right derived functor with unit
`CategoryTheory.Functor.rightDerivedFunctorPlusUnith`, so
`CategoryTheory.Functor.rightDerived_ext` reduces the identity to the two halves
`unit_comp_compTrans_comp_derived_app` and `unit_comp_natTrans_comp_compTrans_app`. -/
public theorem rightDerivedPlusCompTrans_comp_derived
    (he : e.hom = U₂.rightDerivedFunctorPlusUnith) :
    Stacks.DerivedIndexing.rightDerivedPlusCompTrans P U₂ ≫ derived P P' U₂ U₀ τ e =
      Stacks.DerivedIndexing.rightDerivedFunctorPlusNatTrans τ ≫
        Stacks.DerivedIndexing.rightDerivedPlusCompTrans U₀ P' := by
  refine Functor.rightDerived_ext (P ⋙ U₂).rightDerivedFunctorPlus
    (P ⋙ U₂).rightDerivedFunctorPlusUnith (HomotopyCategory.Plus.quasiIso A₀) _ _ _
    (NatTrans.ext (funext fun K => ?_))
  exact (unit_comp_compTrans_comp_derived_app P P' U₂ U₀ τ e he K).trans
    (unit_comp_natTrans_comp_compTrans_app P P' U₂ U₀ τ K).symm

/-- **The derived comparison of a square on a complex concentrated in degree zero.** For
`τ : P ⋙ U₂ ⟶ U₀ ⋙ P'`, writing `u` for `Stacks.DerivedIndexing.rightDerivedPlusUnitSingle`:

`(ℱ ↦ ℱ[0])(τ_ℱ) ≫ u P' (U₀ℱ) ≫ RP'(u U₀ ℱ) = u U₂ (Pℱ) ≫ RU₂(u P ℱ) ≫ derived_{ℱ[0]}`.

This is the identity the target side of the degreewise descent of a base change pasting law
reduces to: `τ` is the underived comparison of the upper square, the left-hand side is how the
degreewise target is identified with cohomology of the derived composite, and the right-hand
side is the derived comparison itself.

It is the two functorialities of the canonical map
(`Stacks.DerivedIndexing.rightDerivedPlusUnitSingle_comp_app` twice,
`Stacks.DerivedIndexing.rightDerivedPlusUnitSingle_natTrans_app` once) together with
`rightDerivedPlusCompTrans_comp_derived`. -/
public theorem unitSingle_comp_derived (he : e.hom = U₂.rightDerivedFunctorPlusUnith) (M : A₀) :
    (DerivedCategory.Plus.singleFunctor B₁ 0).map (τ.app M) ≫
        (Stacks.DerivedIndexing.rightDerivedPlusUnitSingle P').app (U₀.obj M) ≫
          P'.rightDerivedFunctorPlus.map
            ((Stacks.DerivedIndexing.rightDerivedPlusUnitSingle U₀).app M) =
      (Stacks.DerivedIndexing.rightDerivedPlusUnitSingle U₂).app (P.obj M) ≫
        U₂.rightDerivedFunctorPlus.map
            ((Stacks.DerivedIndexing.rightDerivedPlusUnitSingle P).app M) ≫
          (derived P P' U₂ U₀ τ e).app ((DerivedCategory.Plus.singleFunctor A₀ 0).obj M) := by
  have hD : (Stacks.DerivedIndexing.rightDerivedPlusCompTrans P U₂).app
          ((DerivedCategory.Plus.singleFunctor A₀ 0).obj M) ≫
        (derived P P' U₂ U₀ τ e).app ((DerivedCategory.Plus.singleFunctor A₀ 0).obj M) =
      (Stacks.DerivedIndexing.rightDerivedFunctorPlusNatTrans τ).app
          ((DerivedCategory.Plus.singleFunctor A₀ 0).obj M) ≫
        (Stacks.DerivedIndexing.rightDerivedPlusCompTrans U₀ P').app
          ((DerivedCategory.Plus.singleFunctor A₀ 0).obj M) :=
    NatTrans.congr_app (rightDerivedPlusCompTrans_comp_derived P P' U₂ U₀ τ e he)
      ((DerivedCategory.Plus.singleFunctor A₀ 0).obj M)
  rw [← Stacks.DerivedIndexing.rightDerivedPlusUnitSingle_comp_app U₀ P' M, ← Category.assoc,
    Stacks.DerivedIndexing.rightDerivedPlusUnitSingle_natTrans_app τ M, Category.assoc, ← hD,
    ← Category.assoc, Stacks.DerivedIndexing.rightDerivedPlusUnitSingle_comp_app P U₂ M,
    Category.assoc]

end Residual

end Stacks.Cohomology.BaseChange

end
