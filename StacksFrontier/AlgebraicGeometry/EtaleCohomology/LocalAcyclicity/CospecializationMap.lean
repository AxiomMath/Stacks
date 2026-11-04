module

public import Mathlib.CategoryTheory.Comma.Arrow
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocalAcyclicity.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.StalkOfDerivedPushforward
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The cospecialization map

Let `f : X ⟶ S` be a morphism of schemes, let `s` be a geometric point of `S` and let `t` be a
geometric point of the strict henselization `Spec 𝒪^{sh}_{S,s}`. Writing
`Y = X ×_S Spec 𝒪^{sh}_{S,s}` for the base change of `X`, the two geometric fibres of `f` over `s`
and over `t` sit in the diagram

`X_t ⟶ Y ⟵ X_s`,

whose left-hand morphism `h` is the projection of `X_t = Y ×_{Spec 𝒪^{sh}_{S,s}} t` and whose
right-hand morphism `i` is the canonical morphism of
`AlgebraicGeometry.geometricFibreToStrictHenselizationBaseChange`. For an object `K` of the
unbounded derived category `D(X_étale)` the unit of the adjunction between inverse image and
derived direct image along `h` gives the comparison

`β_{K,s,t} : K|_Y ⟶ Rh_*(K|_{X_t})`,

and the cospecialization map `RΓ(X_t, K) ⟶ RΓ(X_s, K)` is built from `β_{K,s,t}` by inverting its
inverse image `i⁻¹β_{K,s,t}` on the closed fibre. This file constructs the diagram and the
comparison `β_{K,s,t}`, and records the invertibility of `i⁻¹β_{K,s,t}` under local acyclicity.

## Main definitions

* `Stacks.EtaleCohomology.smallEtalePushforwardAbPullbackUnit`: on abelian sheaves, the
  adjunction unit `c⁻¹F ⟶ h_*((h ≫ c)⁻¹F)` for a morphism `h` into the target of `c`.
* `Stacks.EtaleCohomology.smallEtaleDerivedPushforwardAbPullbackUnit`: the same comparison
  `c⁻¹M ⟶ Rh_*((h ≫ c)⁻¹M)` on unbounded derived categories.
* `AlgebraicGeometry.cospecializationFibre`: the fibre `X_t` of the base change
  `Y ⟶ Spec 𝒪^{sh}_{S,s}` over a geometric point `t`, with its morphisms
  `AlgebraicGeometry.cospecializationFibreToBaseChange` (the morphism `h`),
  `AlgebraicGeometry.cospecializationFibreToPoint` and
  `AlgebraicGeometry.cospecializationFibreToSource`.
* `AlgebraicGeometry.cospecializationUnit`: the comparison `β_{K,s,t} : K|_Y ⟶ Rh_*(K|_{X_t})`.
* `AlgebraicGeometry.HasDerivedStalkConservativity`: isomorphy in the unbounded derived category
  of abelian sheaves on a small étale site is detected on stalks.
* `AlgebraicGeometry.HasCospecializationStalkComparison`: the stalks of `i⁻¹β_{K,s,t}` are, as
  arrows, canonical maps of Tag 0GJN.

## Main results

* `AlgebraicGeometry.isIso_pullback_cospecializationUnit`: assuming
  `AlgebraicGeometry.HasDerivedStalkConservativity` and
  `AlgebraicGeometry.HasCospecializationStalkComparison`, the inverse image `i⁻¹β_{K,s,t}` on the
  closed geometric fibre is an isomorphism when `f` is locally acyclic relative to `K`.

## References

* [Stacks Project, Tag 0GJT](https://stacks.math.columbia.edu/tag/0GJT)
* [Stacks Project, Tag 0GJU](https://stacks.math.columbia.edu/tag/0GJU)
* [Stacks Project, Tag 0GJP](https://stacks.math.columbia.edu/tag/0GJP)
* [Stacks Project, Tag 0GJS](https://stacks.math.columbia.edu/tag/0GJS)
* [Stacks Project, Tag 03Q1](https://stacks.math.columbia.edu/tag/03Q1)
* [Stacks Project, Tag 03Q9](https://stacks.math.columbia.edu/tag/03Q9)
* [Stacks Project, Tag 03PU](https://stacks.math.columbia.edu/tag/03PU)
* [Stacks Project, Tag 0GIX](https://stacks.math.columbia.edu/tag/0GIX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

/-! ### The adjunction unit along a morphism into the target -/

section PullbackUnit

variable {Z W T : Scheme.{u}} (c : W ⟶ Z) (h : T ⟶ W)

/-- The unit of the adjunction between inverse image and direct image of abelian sheaves on the
small étale sites along `h : T ⟶ W`, read on inverse images from a scheme `Z` under `c : W ⟶ Z`:
the comparison `c⁻¹F ⟶ h_*((h ≫ c)⁻¹F)`, natural in `F`. -/
def smallEtalePushforwardAbPullbackUnit :
    smallEtalePullbackAb c ⟶ smallEtalePullbackAb (h ≫ c) ⋙ smallEtalePushforwardAb h :=
  (Functor.rightUnitor (smallEtalePullbackAb c)).inv ≫
    Functor.whiskerLeft (smallEtalePullbackAb c) (smallEtaleAdjunctionAb h).unit ≫
    (Functor.associator (smallEtalePullbackAb c) (smallEtalePullbackAb h)
      (smallEtalePushforwardAb h)).inv ≫
    Functor.whiskerRight (smallEtalePullbackAbCompIso h c).hom (smallEtalePushforwardAb h)

/-- On an abelian sheaf, the comparison is the adjunction unit at the inverse image under `c`,
followed by the direct image of the identification of the two inverse images. -/
theorem smallEtalePushforwardAbPullbackUnit_app
    (F : Sheaf (smallEtaleTopology Z) Ab.{u + 1}) :
    (smallEtalePushforwardAbPullbackUnit c h).app F =
      (smallEtaleAdjunctionAb h).unit.app ((smallEtalePullbackAb c).obj F) ≫
        (smallEtalePushforwardAb h).map ((smallEtalePullbackAbCompIso h c).hom.app F) := by
  simp [smallEtalePushforwardAbPullbackUnit]

variable
  [((smallEtalePushforwardAb h).mapHomotopyCategory (.up ℤ) ⋙
      DerivedCategory.Qh).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso (Sheaf (smallEtaleTopology T) Ab.{u + 1}) (.up ℤ))]

/-- The comparison `c⁻¹M ⟶ Rh_*((h ≫ c)⁻¹M)` on unbounded derived categories of abelian sheaves
on the small étale sites, natural in `M`: the unit of the adjunction between inverse image and
derived direct image along `h`, read on inverse images under `c : W ⟶ Z`. -/
def smallEtaleDerivedPushforwardAbPullbackUnit :
    smallEtaleDerivedPullbackAb c ⟶
      smallEtaleDerivedPullbackAb (h ≫ c) ⋙ smallEtaleDerivedPushforwardAb h :=
  Stacks.DerivedFunctor.exactDerivedDesc (smallEtalePullbackAb c)
    (smallEtalePullbackAb (h ≫ c)) (smallEtalePushforwardAb h)
    (smallEtaleDerivedPushforwardAb h) (smallEtaleDerivedPushforwardAbUnit h)
    (smallEtalePushforwardAbPullbackUnit c h)

/-- On every complex of abelian sheaves, the derived comparison factors the degreewise adjunction
unit through the unit of the derivation of direct image, read through the identifications of the
degreewise actions of the inverse images with their actions on derived categories. -/
theorem smallEtaleDerivedPushforwardAbPullbackUnit_fac_app
    (J : HomotopyCategory (Sheaf (smallEtaleTopology Z) Ab.{u + 1}) (.up ℤ)) :
    (smallEtalePullbackAb c).mapDerivedCategoryFactorsh.inv.app J ≫
        (smallEtaleDerivedPushforwardAbPullbackUnit c h).app (DerivedCategory.Qh.obj J) =
      DerivedCategory.Qh.map ((Stacks.DerivedFunctor.mapHomotopyCategoryOfComp
          (smallEtalePullbackAb c) (smallEtalePullbackAb (h ≫ c))
          (smallEtalePushforwardAb h) (smallEtalePushforwardAbPullbackUnit c h)).app J) ≫
        (smallEtaleDerivedPushforwardAbUnit h).app
            (((smallEtalePullbackAb (h ≫ c)).mapHomotopyCategory (.up ℤ)).obj J) ≫
          (smallEtaleDerivedPushforwardAb h).map
            ((smallEtalePullbackAb (h ≫ c)).mapDerivedCategoryFactorsh.inv.app J) :=
  Stacks.DerivedFunctor.exactDerivedDesc_fac_app (smallEtalePullbackAb c)
    (smallEtalePullbackAb (h ≫ c)) (smallEtalePushforwardAb h)
    (smallEtaleDerivedPushforwardAb h) (smallEtaleDerivedPushforwardAbUnit h)
    (smallEtalePushforwardAbPullbackUnit c h) J

end PullbackUnit

end Stacks.EtaleCohomology

namespace AlgebraicGeometry

open Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

/-! ### The fibre over a geometric point of the strict henselization -/

section Fibre

variable (B : BigEtaleSite.{u}) {X S : Scheme.{u}} (hS : B.Contains S) (f : X ⟶ S)
  (s : GeometricPoint S) (t : GeometricPoint (strictHenselization B S hS s))

/-- The fibre `X_t = Y ×_{Spec 𝒪^{sh}_{S,s}} t` of the base change
`Y = X ×_S Spec 𝒪^{sh}_{S,s}` of `f : X ⟶ S` over a geometric point `t` of the strict
henselization of `S` at a geometric point `s`. -/
@[sga "4½ Arcata 5.1.6"]
abbrev cospecializationFibre : Scheme.{u} :=
  pullback (strictHenselizationBaseChangeToStrictHenselization B hS f s) t.hom

/-- The morphism `h : X_t ⟶ Y`: the projection of the fibre `X_t` to the base change
`Y = X ×_S Spec 𝒪^{sh}_{S,s}`. -/
abbrev cospecializationFibreToBaseChange :
    cospecializationFibre B hS f s t ⟶ strictHenselizationBaseChange B hS f s :=
  pullback.fst (strictHenselizationBaseChangeToStrictHenselization B hS f s) t.hom

/-- The structure morphism `X_t ⟶ t` of the fibre over the geometric point `t`. -/
abbrev cospecializationFibreToPoint : cospecializationFibre B hS f s t ⟶ t.source :=
  pullback.snd (strictHenselizationBaseChangeToStrictHenselization B hS f s) t.hom

/-- The morphism `X_t ⟶ X`: the projection to the base change followed by the projection to
`X`. -/
abbrev cospecializationFibreToSource : cospecializationFibre B hS f s t ⟶ X :=
  cospecializationFibreToBaseChange B hS f s t ≫
    strictHenselizationBaseChangeToSource B hS f s

/-- Unbounded derived direct image of abelian sheaves exists along the morphism
`h : X_t ⟶ Y` from the fibre over `t` to the base change to the strict henselization. -/
abbrev HasDerivedDirectImageOnCospecializationFibre : Prop :=
  ((smallEtalePushforwardAb
        (cospecializationFibreToBaseChange B hS f s t)).mapHomotopyCategory (.up ℤ) ⋙
      DerivedCategory.Qh).HasRightDerivedFunctor
    (HomotopyCategory.quasiIso
      (Sheaf (smallEtaleTopology (cospecializationFibre B hS f s t)) Ab.{u + 1}) (.up ℤ))

end Fibre

/-! ### The comparison `β_{K,s,t}` -/

section Unit

variable (B : BigEtaleSite.{u}) {X S : Scheme.{u}} (hS : B.Contains S) (f : X ⟶ S)
  (s : GeometricPoint S) (t : GeometricPoint (strictHenselization B S hS s))
  [HasDerivedDirectImageOnCospecializationFibre B hS f s t]

/-- The comparison

`β_{K,s,t} : K|_Y ⟶ Rh_*(K|_{X_t})`,

the unit of the adjunction between inverse image and derived direct image along the morphism
`h : X_t ⟶ Y` from the fibre over a geometric point `t` of `Spec 𝒪^{sh}_{S,s}` to the base change
`Y = X ×_S Spec 𝒪^{sh}_{S,s}`, evaluated on the restriction of an object `K` of `D(X_étale)`
to `Y`. -/
def cospecializationUnit (K : smallEtaleDerivedCategory X) :
    (smallEtaleDerivedPullbackAb (strictHenselizationBaseChangeToSource B hS f s)).obj K ⟶
      (smallEtaleDerivedPushforwardAb (cospecializationFibreToBaseChange B hS f s t)).obj
        ((smallEtaleDerivedPullbackAb (cospecializationFibreToSource B hS f s t)).obj K) :=
  (smallEtaleDerivedPushforwardAbPullbackUnit
    (strictHenselizationBaseChangeToSource B hS f s)
    (cospecializationFibreToBaseChange B hS f s t)).app K

end Unit

/-! ### Derived-stalk conservativity and the stalk computation -/

/-- Isomorphy in the unbounded derived category of abelian sheaves on a small étale site is
detected on the stalks at the geometric points. -/
def HasDerivedStalkConservativity : Prop :=
  ∀ {Z : Scheme.{u}} {M N : smallEtaleDerivedCategory Z} (φ : M ⟶ N),
    (∀ z : GeometricPoint Z, IsIso ((smallEtaleDerivedStalkAb z.hom).map φ)) → IsIso φ

/-- The stalk of the inverse image `i⁻¹β_{K,s,t}` of the comparison `β_{K,s,t}` on the closed
geometric fibre `X_s` at a geometric point `x` of `X_s` is, as an arrow, a canonical map
`α_{K,y,τ}` of Tag 0GJN at some geometric point `y` of `X` and some geometric point `τ` of
`Spec 𝒪^{sh}_{S,f(y)}`. -/
def HasCospecializationStalkComparison (B : BigEtaleSite.{u}) : Prop :=
  ∀ {X S : Scheme.{u}} (hX : B.Contains X) (hS : B.Contains S) (f : X ⟶ S)
      (s : GeometricPoint S) (t : GeometricPoint (strictHenselization B S hS s))
      [HasDerivedDirectImageOnCospecializationFibre B hS f s t]
      (K : smallEtaleDerivedCategory X) (x : GeometricPoint (geometricFibre f s)),
    ∃ (y : GeometricPoint X) (τ : GeometricPoint (strictHenselization B S hS (y.map f))),
      Nonempty (Arrow.mk ((smallEtaleDerivedStalkAb x.hom).map
            ((smallEtaleDerivedPullbackAb
              (geometricFibreToStrictHenselizationBaseChange B hS f s)).map
                (cospecializationUnit B hS f s t K))) ≅
          Arrow.mk ((vanishingCyclesFibreMap B hX hS f y τ).app K))

/-! ### Invertibility of the comparison on the closed geometric fibre -/

section Main

variable (B : BigEtaleSite.{u}) {X S : Scheme.{u}} (hX : B.Contains X) (hS : B.Contains S)
  (f : X ⟶ S)
  (s : GeometricPoint S) (t : GeometricPoint (strictHenselization B S hS s))
  [HasDerivedDirectImageOnCospecializationFibre B hS f s t]
  (K : smallEtaleDerivedCategory X)

/-- Assume that isomorphy in unbounded derived categories of abelian sheaves on small étale sites
is detected on stalks (`hcons`) and that the stalks of `i⁻¹β_{K,s,t}` are canonical maps of
Tag 0GJN (`hcomp`). For a morphism of schemes `f : X ⟶ S` which is locally acyclic relative to an
object `K` of `D(X_étale)`, the inverse image on the closed geometric fibre `X_s` of the
comparison `β_{K,s,t} : K|_Y ⟶ Rh_*(K|_{X_t})` is an isomorphism. -/
@[stacks 0GJU "modulo derived-stalk conservativity and the stalk computation"]
theorem isIso_pullback_cospecializationUnit
    (hla : IsLocallyAcyclicRelative B hX hS f K)
    (hcons : HasDerivedStalkConservativity.{u})
    (hcomp : HasCospecializationStalkComparison B) :
    IsIso ((smallEtaleDerivedPullbackAb
      (geometricFibreToStrictHenselizationBaseChange B hS f s)).map
        (cospecializationUnit B hS f s t K)) := by
  refine hcons _ fun x => ?_
  obtain ⟨y, τ, ⟨e⟩⟩ := hcomp hX hS f s t K x
  exact (Arrow.isIso_iff_isIso_of_isIso e.hom).2 (hla y τ)

end Main

end AlgebraicGeometry

end
