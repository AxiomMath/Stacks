module

public import StacksFrontier.AlgebraicGeometry.Cohomology.InjectiveQcoh.ArtinianPushforwardColimitCardinal
public import StacksFrontier.AlgebraicGeometry.Cohomology.InjectiveQcoh.InjectiveQcohSpace
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleAffinePushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedFiniteTypeOnCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedPushforwardQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteDirectImageCoherence

/-!
# Stacks 09TI on the small étale site of a Noetherian affine scheme

Let `U` be an object of the big fppf site over a scheme `S` whose underlying scheme is affine
and locally Noetherian, regarded as an algebraic space.  This file proves that every injective
object of `QCoh(𝒪_U)`, the quasi-coherent modules on the small étale site of `U`, is a filtered
colimit of Artinian direct images over `U`, in the sense of
`AlgebraicGeometry.Space.IsArtinianPushforward`.

## Main results

* `AlgebraicGeometry.Space.modulePushforwardRepresentedQuasicoherentIso`: the direct image along
  an affine morphism of represented algebraic spaces commutes with the equivalence of
  Stacks 03DX (2).
* `AlgebraicGeometry.Space.exists_filtered_colimit_artinian_pushforwards_of_isAffine`: every
  injective object of `QCoh(𝒪_U)`, for `U` affine and locally Noetherian, is a filtered colimit
  of Artinian direct images over `U`.

## References

* [Stacks Project, Tag 09TI](https://stacks.math.columbia.edu/tag/09TI)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 07UB](https://stacks.math.columbia.edu/tag/07UB)
* [Stacks Project, Tag 08HD](https://stacks.math.columbia.edu/tag/08HD)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Cardinal

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The direct image along a morphism of represented algebraic spaces with affine underlying
morphism of schemes, of the module that a quasi-coherent Zariski module becomes on the small
étale site, is the module that the Zariski direct image becomes. -/
noncomputable def modulePushforwardRepresentedQuasicoherentIso {Z U : BigFppfOver B S hS}
    (g : Z ⟶ U)
    [_root_.AlgebraicGeometry.IsAffineHom
      (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) g.left)]
    (M : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj Z).ringCatSheaf).FullSubcategory)
    (hM : SheafOfModules.IsQuasicoherent ((Scheme.Modules.pushforward
      (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) g.left)).obj
        M.obj)) :
    (modulePushforward B S hS (schemeSpaceMap g)).obj
        ((representedQuasicoherentSheavesEquivalence B S hS Z).functor.obj M).obj ≅
      ((representedQuasicoherentSheavesEquivalence B S hS U).functor.obj
        ⟨_, hM⟩).obj :=
  (representedModulePushforwardObjIso B S hS g _).symm ≪≫
    (representedSmallEtaleModuleEquivalence B S hS U).functor.mapIso
      (_root_.AlgebraicGeometry.SmallEtale.pushforwardAssociatedModuleIso
        (associatedBigEtaleSite B) g.left M.obj M.property)

/-- The spectrum of a ring of cardinality at most `max ℵ₀ #Γ(T, ⊤)`, for an affine scheme `T`
contained in a big fppf site, is contained in it. -/
theorem contains_spec_of_card_le {T : Scheme.{u}} [IsAffine T] (hT : B.Contains T)
    (R : CommRingCat.{u}) (hR : #R ≤ max ℵ₀ #Γ(T, ⊤)) : B.Contains (Spec R) := by
  refine lt_of_le_of_lt ?_ hT
  rw [Scheme.size_of_isAffine, Scheme.size_of_isAffine,
    Cardinal.mk_congr (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv.toEquiv]
  exact max_le (le_max_left _ _) hR

/-- **Stacks 09TI on the small étale site of a Noetherian affine scheme.**  Let `U` be an object
of the big fppf site over `S` whose underlying scheme is affine and locally Noetherian.  Every
injective object of `QCoh(𝒪_U)`, the quasi-coherent modules on the small étale site of the
algebraic space `U` represents, is a filtered colimit of Artinian direct images over `U`. -/
theorem exists_filtered_colimit_artinian_pushforwards_of_isAffine (U : BigFppfOver B S hS)
    (hUaff : IsAffine ((BigFppfOver.toScheme B S hS).obj U))
    (hUnoeth : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj U))
    (JY : QuasicoherentSheaves.{u, u} B S hS (schemeSpace U).1 (schemeSpace U).2)
    [Injective JY] :
    ∃ (I : Type u) (inst : SmallCategory I),
      letI := inst
      ∃ (_ : IsFiltered I)
        (D : I ⥤ QuasicoherentSheaves.{u, u} B S hS (schemeSpace U).1 (schemeSpace U).2)
        (c : Cocone D),
        (∀ i, IsArtinianPushforward B S hS (schemeSpace U) (D.obj i).obj) ∧
          Nonempty (IsColimit c) ∧ Nonempty (c.pt ≅ JY) := by
  let T := (BigFppfOver.toScheme B S hS).obj U
  have : IsAffine T := hUaff
  have : IsLocallyNoetherian T := hUnoeth
  have : IsAffine (Over.left U).obj := hUaff
  let e := representedQuasicoherentSheavesEquivalence B S hS U
  let J0 := e.inverse.obj JY
  have : e.inverse.PreservesInjectiveObjects :=
    @Functor.preservesInjectiveObjects_of_isEquivalence _ _ _ _ e.inverse e.isEquivalence_inverse
  have : Injective J0 := @Functor.injective_obj _ _ _ _ e.inverse this JY ‹_›
  obtain ⟨I, inst, hf, D0, φ, hD0, ⟨hc⟩⟩ :=
    exists_filtered_colimit_tilde_pushforwards_artinian_card_le T J0
  refine ⟨I, inst, hf, D0 ⋙ e.functor, e.functor.mapCocone (Cocone.mk J0 φ), ?_,
    ⟨isColimitOfPreserves e.functor hc⟩, ⟨e.counitIso.app JY⟩⟩
  intro i
  obtain ⟨R, hR, f, N, hN, hcard, ⟨eN⟩⟩ := hD0 i
  let Z := BigFppfOver.mk B S hS (contains_spec_of_card_le B U.left.property R hcard)
    (f ≫ B.inclusion.map U.hom)
  let gZ : Z ⟶ U := Over.homMk (ObjectProperty.homMk f) (by
    apply ObjectProperty.hom_ext
    rfl)
  have : IsAffine (Over.left Z).obj := inferInstanceAs (IsAffine (Spec R))
  have : _root_.AlgebraicGeometry.IsAffineHom
      (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) gZ.left) :=
    isAffineHom_of_isAffine _
  have hΓ : IsArtinianRing Γ(Spec R, ⊤) :=
    (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv.symm.isArtinianRing
  let M : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj Z).ringCatSheaf).FullSubcategory :=
    ⟨tilde N, inferInstanceAs (tilde N).IsQuasicoherent⟩
  have hM : SheafOfModules.IsQuasicoherent ((Scheme.Modules.pushforward
      (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) gZ.left)).obj
        M.obj) :=
    (SheafOfModules.isQuasicoherent _).prop_of_iso eN (D0.obj i).property
  let eZ := representedQuasicoherentSheavesEquivalence B S hS Z
  have : Fact (HasEtaleLocalProperty B S hS (schemeSpace Z).1
      (fun V : Scheme.{u} => IsLocallyNoetherian V)) :=
    ⟨hasEtaleLocalProperty_of_representable B S hS _ _ Z (Iso.refl _)
      (inferInstanceAs (IsLocallyNoetherian (Spec R)))⟩
  have hcoh : IsCoherent B S hS (schemeSpace Z).1 (schemeSpace Z).2 (eZ.functor.obj M).obj :=
    (isCoherent_iff_isQuasicoherentOnSite_and_isFiniteType B S hS _ _ _).2
      ⟨(eZ.functor.obj M).property,
        Stacks.SheafOfModules.presheaf_isFiniteType_of_isFiniteTypeOnSite _
          (isFiniteTypeOnSite_representedQuasicoherentSchemeEquivalence B S hS Z (tilde N)
            M.property ((tilde_isFiniteType_iff N).2 hN))⟩
  refine ⟨Z, inferInstanceAs (IsAffine (Spec R)), hΓ, schemeSpaceMap gZ, (eZ.functor.obj M).obj,
    hcoh, ⟨modulePushforwardRepresentedQuasicoherentIso B S hS gZ M hM ≪≫
      (ObjectProperty.ι _).mapIso (e.functor.mapIso (ObjectProperty.isoMk _ eN.symm))⟩⟩

end AlgebraicGeometry.Space

end
