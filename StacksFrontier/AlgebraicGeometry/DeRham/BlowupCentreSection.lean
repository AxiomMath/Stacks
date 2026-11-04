module

public import StacksFrontier.AlgebraicGeometry.DeRham.BlowupExceptionalBoundaryLift
public import StacksFrontier.AlgebraicGeometry.DeRham.LerayHirsch.DirectImageMapChain
public import StacksFrontier.AlgebraicGeometry.DeRham.LerayHirsch.PowerSummandsSection
public import StacksFrontier.AlgebraicGeometry.DeRham.LerayHirsch.ProjectiveBundlePowers

/-!
# The section on the centre in the proof of [Stacks, Tag 0FUW]

Let `p : E ⟶ Z` and `g : Z ⟶ S` be morphisms of schemes and `ℒ` an invertible module on `E`.
Write `c : Ω^•_{Z/S} ⟶ Rp_*Ω^•_{E/S}` for the canonical map and
`θ : Ω^•_{E/S}[-2] ⟶ Ω^•_{E/S}` for the untwisted map of [Stacks, Tag 0FU7] attached to
`c₁^{dR}(ℒ)`. The proof of [Stacks, Tag 0FUW] needs, for the exceptional divisor `p : E ⟶ Z` of
the blowing up and `ℒ = 𝒪_{X'}(-E)|_E`, that the map

`c ⊕ Rp_*θ : Ω^•_{Z/S} ⊕ Rp_*(Ω^•_{E/S}[-2]) ⟶ Rp_*Ω^•_{E/S}`

has a section restricting to the inclusion of `Ω^•_{Z/S}` along `c`
(`Stacks.DeRham.BlowupTriangle.HasCentreSection`). This file shows that it is all that is left of
[Stacks, Tag 0FUW], and that it holds whenever the Leray--Hirsch morphism of the powers of
`c₁^{dR}(ℒ)` is an isomorphism with at least one summand: in particular for the projective bundle
`𝐏(ℰ) ⟶ Z` of a locally free module of positive rank and `ℒ = 𝒪(1)`, once Remark 0FUN (i) is
known.

## Main definitions

* `Stacks.DeRham.BlowupTriangle.HasCentreSection`: the section on the centre.

## Main results

* `Stacks.DeRham.BlowupTriangle.exists_retraction_toBlowUp_of_hasCentreSection`: the splitting
  of [Stacks, Tag 0FUW] from the section on the centre.
* `Stacks.DeRham.BlowupTriangle.hasCentreSection_of_isIso_lerayHirschPowerMorphism`: the section
  from the Leray--Hirsch decomposition (Remark 0FUN).
* `Stacks.DeRham.BlowupTriangle.hasCentreSection_projectiveBundle_of_isIso`: the case of a
  projective bundle.

## References

* [Stacks Project, Tag 0FUW](https://stacks.math.columbia.edu/tag/0FUW)
* [Stacks Project, Tag 0FUN](https://stacks.math.columbia.edu/tag/0FUN)
* [Stacks Project, Tag 0FU7](https://stacks.math.columbia.edu/tag/0FU7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.DeRhamDirectImage AlgebraicGeometry.DeRhamLerayHirsch
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPushforward)
open scoped Stacks.StandardDerivedModel

universe u

attribute [-instance] CategoryTheory.catToReflQuiver

-- The statements mix the `Modules` and `ModuleSheaves` spellings of the categories of modules,
-- which agree only at default transparency; these make them agree for unification.
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose SheafedSpace.sheaf
  AlgebraicGeometry.RingedSpace.inverseImage

namespace Stacks.DeRham.BlowupTriangle

section Definition

variable {E Z S : Scheme.{u}} (p : E ⟶ Z) (g : Z ⟶ S) (L : E.Modules)
  [hL : AlgebraicGeometry.SheafOfModules.IsInvertible E.sheaf.obj E.ringCatSheaf.property L]

/-- **The section on the centre**: for `p : E ⟶ Z`, `g : Z ⟶ S` and an invertible module `ℒ` on
`E`, there are `τ : Rp_*Ω^•_{E/S} ⟶ Ω^•_{Z/S}` and `ν : Rp_*Ω^•_{E/S} ⟶ Rp_*(Ω^•_{E/S}[-2])` with
`c ≫ τ = 𝟙`, `c ≫ ν = 0` and `τ ≫ c + ν ≫ Rp_*θ = 𝟙`, for `c : Ω^•_{Z/S} ⟶ Rp_*Ω^•_{E/S}` the
canonical map and `θ : Ω^•_{E/S}[-2] ⟶ Ω^•_{E/S}` the untwisted map of [Stacks, Tag 0FU7] for
`c₁^{dR}(ℒ)`. Equivalently, `c ⊕ Rp_*θ` has a section restricting to the inclusion of
`Ω^•_{Z/S}` along `c`. -/
def HasCentreSection : Prop :=
  ∃ (τ : (derivedPushforward (Stacks.DeRhamSmooth.relativeBase p g)).obj (deRham (p ≫ g)) ⟶
      deRham g)
    (ν : (derivedPushforward (Stacks.DeRhamSmooth.relativeBase p g)).obj (deRham (p ≫ g)) ⟶
      (derivedPushforward (Stacks.DeRhamSmooth.relativeBase p g)).obj
        ((deRham (p ≫ g))⟦(-2 : ℤ)⟧)),
    (DerivedCategory.Q.map (chain p g) ≫
        unit (Stacks.DeRhamSmooth.relativeBase p g) (deRhamCochainComplex (p ≫ g))) ≫ τ = 𝟙 _ ∧
      (DerivedCategory.Q.map (chain p g) ≫
        unit (Stacks.DeRhamSmooth.relativeBase p g) (deRhamCochainComplex (p ≫ g))) ≫ ν = 0 ∧
      τ ≫ (DerivedCategory.Q.map (chain p g) ≫
          unit (Stacks.DeRhamSmooth.relativeBase p g) (deRhamCochainComplex (p ≫ g))) +
        ν ≫ (derivedPushforward (Stacks.DeRhamSmooth.relativeBase p g)).map
          (untwistedChern { X := E, S := S, f := p ≫ g, L := L }) = 𝟙 _

end Definition

section Splitting

variable {S X Z : Scheme.{u}} (f : X ⟶ S) (i : Z ⟶ X) [IsClosedImmersion i]

/-- **[Stacks, Tag 0FUW] from the section on the centre.** For `f` smooth and `Z` smooth over `S`,
if the exceptional divisor `p : E ⟶ Z` has the section on the centre for `𝒪_{X'}(-E)|_E`, then
the canonical map `Ω^•_{X/S} ⟶ Rb_*Ω^•_{X'/S}` has a retraction. -/
theorem exists_retraction_toBlowUp_of_hasCentreSection [Smooth f] [Smooth (i ≫ f)]
    (h : HasCentreSection (exceptionalProjection i) (i ≫ f) (exceptionalSituation f i).L
      (hL := (exceptionalSituation f i).invertible)) :
    ∃ r : blowUpDeRham f i ⟶ deRham f, toBlowUp f i ≫ r = 𝟙 _ :=
  exists_retraction_toBlowUp_of_centre f i h

end Splitting

section LerayHirsch

variable {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S) (L : X.Modules)
  [hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]

/-- The first Chern class `c₁^{dR}(ℒ) ∈ H^2_{dR}(X/S)` of an invertible module, relative to `S`
through `f ≫ g`, in the degree `((2 : ℕ) : ℤ)` of the Leray--Hirsch morphism of its powers. -/
abbrev chernClassTwo :
    SheafOfModules.deRhamCohomology (Scheme.Hom.deRhamAlgebras (f ≫ g))
      (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras (f ≫ g))) ((2 : ℕ) : ℤ) :=
  SheafOfModules.deRhamCohomologyFirstChernClass (X := X.toRingedSpace)
    (Scheme.Hom.deRhamAlgebras (f ≫ g))
    (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras (f ≫ g))) L
    (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ L hL)

/-- The untwisted map of [Stacks, Tag 0FU7] for `c₁^{dR}(ℒ)` is the untwisted map of the class
`c₁^{dR}(ℒ)` in degree `((2 : ℕ) : ℤ)`. -/
theorem untwistedChern_eq_classUntwisted :
    untwistedChern { X := X, S := S, f := f ≫ g, L := L } =
      classUntwisted (f ≫ g) ((2 : ℕ) : ℤ) (chernClassTwo f g L) :=
  rfl

/-- **Transporting the section on the centre along an equality of morphisms of ringed spaces**
and of translation amounts: if `c' ⊕ Rb_*θ'` has a section restricting to the inclusion along
`c'`, then so does `c ⊕ Ra_*θ`, for `a = b`, `c` and `c'` corresponding under the identification
of the two direct images, and `θ`, `θ'` corresponding maps out of translates by equal amounts. -/
theorem exists_section_derivedPushforward_of_eq {A B : RingedSpace.{u, u}} {a b : A ⟶ B}
    (e : a = b) {K K' : DerivedCategory (SheafOfModules.{u} (structureSheafRing A))}
    {T : DerivedCategory (SheafOfModules.{u} (structureSheafRing B))} {n m : ℤ} (hnm : n = m)
    (c : T ⟶ (derivedPushforward a).obj K') (c' : T ⟶ (derivedPushforward b).obj K')
    (hc : c ≫ eqToHom (congrArg (fun k => (derivedPushforward k).obj K') e) = c')
    (θn : K⟦n⟧ ⟶ K') (θm : K⟦m⟧ ⟶ K') (hθ : HEq θn θm)
    (H : ∃ (τ : (derivedPushforward b).obj K' ⟶ T)
      (ν : (derivedPushforward b).obj K' ⟶ (derivedPushforward b).obj (K⟦m⟧)),
      c' ≫ τ = 𝟙 T ∧ c' ≫ ν = 0 ∧ τ ≫ c' + ν ≫ (derivedPushforward b).map θm = 𝟙 _) :
    ∃ (τ : (derivedPushforward a).obj K' ⟶ T)
      (ν : (derivedPushforward a).obj K' ⟶ (derivedPushforward a).obj (K⟦n⟧)),
      c ≫ τ = 𝟙 T ∧ c ≫ ν = 0 ∧ τ ≫ c + ν ≫ (derivedPushforward a).map θn = 𝟙 _ := by
  subst e hnm hc
  obtain rfl := eq_of_heq hθ
  simpa using H

/-- **The section on the centre from the Leray--Hirsch decomposition.** If the Leray--Hirsch
morphism `ξ̃ : ⨁_{t < r} Ω^•_{Y/S}[-2t] ⟶ Rf_*Ω^•_{X/S}` of the powers of `c₁^{dR}(ℒ)` is an
isomorphism, `r ≥ 1`, then `f : X ⟶ Y` has the section on the centre for `ℒ` (Remark 0FUN). -/
theorem hasCentreSection_of_isIso_lerayHirschPowerMorphism (r : ℕ) (hr : 0 < r)
    [IsIso (lerayHirschPowerMorphism f g 2 (chernClassTwo f g L) r)] :
    HasCentreSection f g L := by
  have e := baseMap_eq_relativeBase f g
  obtain ⟨τ, ν, h₁, h₂, h₃⟩ :=
    exists_section_of_isIso_lerayHirschPowerMorphism f g 2 (chernClassTwo f g L) r hr
  have hc : (DerivedCategory.Q.map (chain f g) ≫
      unit (Stacks.DeRhamSmooth.relativeBase f g) (deRhamCochainComplex (f ≫ g))) ≫
        eqToHom (congrArg (fun k => (derivedPushforward k).obj (deRhamObject (f ≫ g))) e.symm) =
      deRhamDirectImageMap f g := by
    rw [← deRhamDirectImageMap_comp_eqToHom]
    simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
  exact exists_section_derivedPushforward_of_eq e.symm (show (-2 : ℤ) = -((2 : ℕ) : ℤ) by norm_num)
    _ _ hc (untwistedChern { X := X, S := S, f := f ≫ g, L := L })
    (classUntwisted (f ≫ g) ((2 : ℕ) : ℤ) (chernClassTwo f g L))
    (heq_of_eq (untwistedChern_eq_classUntwisted f g L)) ⟨τ, ν, h₁, h₂, h₃⟩

end LerayHirsch

section ProjectiveBundle

open Stacks.RelativeProj (projectiveBundle projectiveBundleToBase tautologicalDatumTwist
  isInvertible_tautologicalDatumTwist)

variable {Y S : Scheme.{u}} (g : Y ⟶ S) (F : Y.Modules) [F.IsQuasicoherent]

/-- **The section on the centre for a projective bundle**: if the Leray--Hirsch morphism
`ξ̃ : ⨁_{t < r} Ω^•_{Y/S}[-2t] ⟶ Rp_*Ω^•_{𝐏(F)/S}` of the powers of `c₁^{dR}(𝒪(1))` is an
isomorphism (Remark 0FUN (i)) and `r ≥ 1`, then `p : 𝐏(F) ⟶ Y` has the section on the centre for
`𝒪(1)`. -/
theorem hasCentreSection_projectiveBundle_of_isIso (r : ℕ) (hr : 0 < r)
    [IsIso (projectiveBundleLerayHirschMorphism g F r)] :
    HasCentreSection (projectiveBundleToBase Y F) g (tautologicalDatumTwist F)
      (hL := isInvertible_tautologicalDatumTwist F) :=
  hasCentreSection_of_isIso_lerayHirschPowerMorphism (projectiveBundleToBase Y F) g
    (tautologicalDatumTwist F) (hL := isInvertible_tautologicalDatumTwist F) r hr

end ProjectiveBundle

end Stacks.DeRham.BlowupTriangle

end
