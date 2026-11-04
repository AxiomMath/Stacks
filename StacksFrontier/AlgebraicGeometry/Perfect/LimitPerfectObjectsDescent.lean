module

public import StacksFrontier.AlgebraicGeometry.Perfect.LimitPerfectObjects
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeDescentPerfectColimit
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectOverIsomorphism
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectPerfectObjectsCanonical

/-!
# Perfect objects descend along a directed limit of schemes

Let `i ↦ S_i` be a directed inverse system of quasi-compact and quasi-separated schemes with
affine transition morphisms, with limit `S`. Every perfect object of `D(𝒪_S)` is the derived
pullback of a perfect object of `D(𝒪_{S_i})` for some `i`.

## Main definitions

* `AlgebraicGeometry.DescentSituation.identityRelative`: the relative descent situation whose
  fixed morphism is the identity of the base stage.

## Main results

* `AlgebraicGeometry.DescentSituation.exists_isPerfect_derivedPullback_iso`: every perfect object
  of `D(𝒪_S)` is, up to isomorphism, the derived pullback of a perfect object of `D(𝒪_{S_i})` for
  some stage `i`.

## References

* [Stacks Project, Tag 09RD](https://stacks.math.columbia.edu/tag/09RD)
* [Stacks Project, Tag 09RF](https://stacks.math.columbia.edu/tag/09RF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite StrictlyPerfect
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)

universe u

namespace AlgebraicGeometry.DescentSituation

attribute [local instance 10000] HasDerivedCategory.standard

variable {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] (D : DescentSituation.{u, u} I)

/-- The relative descent situation of `D` whose fixed morphism is the identity of the base
stage. -/
def identityRelative : RelativeDescentSituation.{u, u} I where
  descent := D
  X₀ := Over.mk (𝟙 (D.system.obj (op D.base)))
  flat := inferInstanceAs (Flat (𝟙 _))
  finitePresentation := ⟨inferInstanceAs (LocallyOfFinitePresentation (𝟙 _)),
    inferInstanceAs (QuasiCompact (𝟙 _)), inferInstanceAs (QuasiSeparated (𝟙 _))⟩

/-- The second projection of the fibre product along an identity is an isomorphism. -/
theorem isIso_pullback_snd_id {X Y : Scheme.{u}} (g : Y ⟶ X) : IsIso (pullback.snd (𝟙 X) g) :=
  inferInstance

/-- Perfect objects descend along a directed limit: every perfect object of `D(𝒪_S)` is, up to
isomorphism, the derived pullback of a perfect object of `D(𝒪_{S_i})` for some stage `i` beyond
the base stage. -/
theorem exists_isPerfect_derivedPullback_iso
    (E : DerivedCategory (OXMod.{u, u} D.limitCone.pt.toRingedSpace))
    (hE : RingedSpace.IsPerfect (X := D.limitCone.pt.toRingedSpace) E) :
    ∃ (i : I) (_ : D.base ≤ i)
      (Eᵢ : DerivedCategory (OXMod.{u, u} (D.system.obj (op i)).toRingedSpace)),
      RingedSpace.IsPerfect (X := (D.system.obj (op i)).toRingedSpace) Eᵢ ∧
        Nonempty ((derivedPullback (D.limitCone.π.app (op i)).toLRSHom.toShHom).obj Eᵢ ≅ E) := by
  let t := D.identityRelative.structureMapLimit
  have : IsIso t := isIso_pullback_snd_id _
  let E' := (derivedPullback t.toLRSHom.toShHom).obj E
  obtain ⟨i, Ei, hEi, ⟨eE⟩⟩ := D.identityRelative.perfectEssentiallySurjectiveCanonical E'
    (Scheme.Hom.isPerfectRelativeTo_canonical_of_isPerfect t E'
      (RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback t.toLRSHom.toShHom E hE))
  have hs : IsIso (D.identityRelative.structureMapAt i) := isIso_pullback_snd_id _
  have : CompactSpace (D.identityRelative.descent.system.obj (op i.1)) := D.quasiCompact i.1
  have : CompactSpace (D.identityRelative.schemeAt i) :=
    (Scheme.homeoOfIso (asIso (D.identityRelative.structureMapAt i)).symm).compactSpace
  have hEi' := Scheme.Hom.isPerfect_of_isPerfectRelativeTo_of_isIso
    (D.identityRelative.structureMapAt i) Ei hEi
  let es := asIso (D.identityRelative.structureMapAt i)
  let p := D.identityRelative.projection i
  let π := D.identityRelative.descent.limitCone.π.app (op i.1)
  have h₁ : inv t ≫ p = π ≫ es.inv := by
    rw [IsIso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
    exact pullback.lift_snd _ _ _
  exact ⟨i.1, i.2, (derivedPullback es.inv.toLRSHom.toShHom).obj Ei,
    RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback _ Ei hEi',
    ⟨(Stacks.DerivedPullback.schemeFactorIso π es.inv _ rfl).app Ei ≪≫
      ((Stacks.DerivedPullback.schemeFactorIso (inv t) p _ h₁).app Ei).symm ≪≫
      (derivedPullback (inv t).toLRSHom.toShHom).mapIso eE ≪≫
      (Stacks.DerivedPullback.schemeFactorIso (inv t) t (𝟙 _) (IsIso.inv_hom_id t)).app E ≪≫
      (Stacks.Cohomology.DerivedPushforwardAssociativity.derivedPullbackIdIso _).app E⟩⟩

end AlgebraicGeometry.DescentSituation

end
