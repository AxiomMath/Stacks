module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.NatIsoSquare
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.OverPullbackComp
public import StacksFrontier.CategoryTheory.Adjunction.Mates

/-!
# Mates of the factors of the coherence square of Stacks 03DV

The compatibility of the comparison of Stacks 03DV with composition of objects of the big fppf
site is reduced, in
`AlgebraicGeometry.BigFppfOver.associatedModuleObjRestrictNatIso_comp_of_pentagon`, to a pentagon
between the mates of its factors. This file computes the mates of those factors that concern
restriction to an object, together with general lemmas on conjugation of isomorphisms of left
adjoints.

## Main results

* `Stacks.Mates.conjugateIsoEquiv_of_heq_adjunction`: conjugation commutes with a transport of
  the two left adjoints along equalities of functors, provided the two adjunctions are
  transported along the same equalities. `Stacks.Mates.heq_adjunction_comp` is the
  corresponding congruence for `CategoryTheory.Adjunction.comp`.
* `Stacks.Mates.conjugateIsoEquiv_trans`, `Stacks.Mates.conjugateIsoEquiv_iso_symm`,
  `Stacks.Mates.conjugateIsoEquiv_isoWhiskerLeft`,
  `Stacks.Mates.conjugateIsoEquiv_isoWhiskerRight` and
  `Stacks.Mates.conjugateIsoEquiv_leftAdjointUniq`: conjugation read on isomorphisms.
* `Stacks.Mates.conjugateIsoEquiv_congr_source` and
  `Stacks.Mates.conjugateIsoEquiv_congr_target`: changing the adjunction conjugates the mate by
  the comparison of the two right adjoints.
* `Stacks.Mates.conjugateIsoEquiv_equivalenceCounitIso`: the mate of the counit isomorphism of
  an equivalence is the unit isomorphism of the inverse equivalence.
* `Stacks.Scheme.Modules.conjugateIsoEquiv_pullbackCongr` and
  `Stacks.Scheme.Modules.conjugateIsoEquiv_pullbackComp`, and
  `AlgebraicGeometry.BigFppfOver.conjugateIsoEquiv_pullbackComp_objHom`: the mate of the
  contraction of the iterated pullback of modules on schemes along the structure morphisms of
  `T` and of `T'` over it.
* `Stacks.SheafOfModules.conjugateIsoEquiv_pullbackPushforwardOverIso`: the mate of the
  identification of restriction to a slice with a pullback is the identity.
* `AlgebraicGeometry.BigFppfOver.conjugateIsoEquiv_associatedModuleObjIso`: the mate of the
  comparison of Stacks 03DV at an object of the big fppf site is the composite of comparisons
  of pushforwards of sheaves of modules carried by the square of ringed sites.
* `AlgebraicGeometry.BigFppfOver.objRestrictOverPullbackAdjunction_heq`: the adjunction between
  restriction to an object and `SheafOfModules.overPullback` is, up to `HEq`, the adjunction
  `SheafOfModules.overMapPushforwardAdj` of the structure morphism.
* `AlgebraicGeometry.BigFppfOver.conjugateIsoEquiv_objRestrictComp`: the mate of the
  functoriality of restriction to an object of the big fppf site, with respect to the
  `SheafOfModules.overPullback` adjunctions, is the congruence isomorphism of
  `CategoryTheory.Over.w` followed by `Stacks.SheafOfModules.overPullbackComp`.

## Implementation notes

`AlgebraicGeometry.BigFppfOver.objRestrictComp` and
`AlgebraicGeometry.BigFppfOver.objRestrictOverPullbackAdjunction` are both built by rewriting
along `AlgebraicGeometry.BigFppfOver.objRestrict_eq_overMap`, so each is a `cast`. Nothing here
unfolds `AlgebraicGeometry.BigFppfOver.objRestrict`: the two `cast`s are stripped by `HEq`, since
checking the underlying definitional equality does not fit the heartbeat budget.

The transport in `conjugateIsoEquiv_pullbackComp_objHom` is
`AlgebraicGeometry.Scheme.Modules.pullbackCongr`, a `CategoryTheory.eqToIso`, and not
`Stacks.SheafOfModules.pullbackCongr`, which is built from the uniqueness of a left adjoint; the
two have different mates.

`SheafOfModules.pushforward` along `(objHom B S hS T).toRingCatSheafHom` and
`Scheme.Modules.pushforward (objHom B S hS T)` are definitionally equal, but instance search does
not see through the one to the other, so `sheafPushforward_objHom_isRightAdjoint` restates the
instance.

## References

* [Stacks Project, Tag 03DV](https://stacks.math.columbia.edu/tag/03DV)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v₀ v₁ v₂ u₀ u₁ u₂ w u

namespace Stacks.Mates

variable {C₀ : Type u₀} {C₁ : Type u₁} {C₂ : Type u₂}
  [Category.{v₀} C₀] [Category.{v₁} C₁] [Category.{v₂} C₂]

/-- Let `α : L₂' ≅ L₁'` be an isomorphism of left adjoints and let `h₁ : L₁ = L₁'`,
`h₂ : L₂ = L₂'` be equalities of functors. Then the mate of `α` conjugated by the two
transports, taken with respect to adjunctions of `L₁` and `L₂`, is the mate of `α` itself taken
with respect to adjunctions of `L₁'` and `L₂'` that are heterogeneously equal to them. -/
public theorem conjugateIsoEquiv_of_heq_adjunction
    {L₁ L₁' L₂ L₂' : C₀ ⥤ C₁} {R₁ R₂ : C₁ ⥤ C₀} (h₁ : L₁ = L₁') (h₂ : L₂ = L₂')
    (adj₁ : L₁ ⊣ R₁) (adj₁' : L₁' ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (adj₂' : L₂' ⊣ R₂)
    (e₁ : HEq adj₁ adj₁') (e₂ : HEq adj₂ adj₂') (α : L₂' ≅ L₁') :
    conjugateIsoEquiv adj₁ adj₂ (eqToIso h₂ ≪≫ α ≪≫ eqToIso h₁.symm) =
      conjugateIsoEquiv adj₁' adj₂' α := by
  subst h₁
  subst h₂
  obtain rfl := eq_of_heq e₁
  obtain rfl := eq_of_heq e₂
  simp

/-- If two adjunctions with equal left adjoints and the same right adjoint are heterogeneously
equal in each of two composable slots, so are the two composites. -/
public theorem heq_adjunction_comp {L₁ L₁' : C₀ ⥤ C₁} {L₂ L₂' : C₁ ⥤ C₂} {R₁ : C₁ ⥤ C₀}
    {R₂ : C₂ ⥤ C₁} (h₁ : L₁ = L₁') (h₂ : L₂ = L₂')
    (adj₁ : L₁ ⊣ R₁) (adj₁' : L₁' ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (adj₂' : L₂' ⊣ R₂)
    (e₁ : HEq adj₁ adj₁') (e₂ : HEq adj₂ adj₂') :
    HEq (adj₁.comp adj₂) (adj₁'.comp adj₂') := by
  subst h₁
  subst h₂
  obtain rfl := eq_of_heq e₁
  obtain rfl := eq_of_heq e₂
  rfl

/-! ### Conjugation read on isomorphisms -/

/-- The mate of `α.symm`, the two adjunctions being exchanged, is the inverse of the mate of
`α`. -/
public theorem conjugateIsoEquiv_iso_symm {L₁ L₂ : C₀ ⥤ C₁} {R₁ R₂ : C₁ ⥤ C₀}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (α : L₂ ≅ L₁) :
    conjugateIsoEquiv adj₂ adj₁ α.symm = (conjugateIsoEquiv adj₁ adj₂ α).symm :=
  rfl

/-- The mate of a composite of isomorphisms of left adjoints is the composite of the mates, in
the other order. -/
public theorem conjugateIsoEquiv_trans {L₁ L₂ L₃ : C₀ ⥤ C₁} {R₁ R₂ R₃ : C₁ ⥤ C₀}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (adj₃ : L₃ ⊣ R₃) (α : L₃ ≅ L₂) (β : L₂ ≅ L₁) :
    conjugateIsoEquiv adj₁ adj₃ (α ≪≫ β) =
      conjugateIsoEquiv adj₁ adj₂ β ≪≫ conjugateIsoEquiv adj₂ adj₃ α :=
  Iso.ext (conjugateEquiv_comp adj₁ adj₂ adj₃ β.hom α.hom).symm

/-- The mate of the canonical comparison `Adjunction.leftAdjointUniq` of two left adjoints of
the same functor is the identity. -/
public theorem conjugateIsoEquiv_leftAdjointUniq {L₁ L₂ : C₀ ⥤ C₁} {R : C₁ ⥤ C₀}
    (adj₁ : L₁ ⊣ R) (adj₂ : L₂ ⊣ R) :
    conjugateIsoEquiv adj₂ adj₁ (Adjunction.leftAdjointUniq adj₁ adj₂) = Iso.refl R :=
  Iso.ext (Stacks.CategoryTheory.conjugateEquiv_leftAdjointUniq_hom adj₁ adj₂)

/-- The mate of an isomorphism whiskered on the left is the mate whiskered on the right. -/
public theorem conjugateIsoEquiv_isoWhiskerLeft {L₁ L₂ : C₁ ⥤ C₂} {R₁ R₂ : C₂ ⥤ C₁}
    {L : C₀ ⥤ C₁} {R : C₁ ⥤ C₀} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (adj : L ⊣ R) (τ : L₂ ≅ L₁) :
    conjugateIsoEquiv (adj.comp adj₁) (adj.comp adj₂) (Functor.isoWhiskerLeft L τ) =
      Functor.isoWhiskerRight (conjugateIsoEquiv adj₁ adj₂ τ) R :=
  Iso.ext (conjugateEquiv_whiskerLeft adj₁ adj₂ adj τ.hom)

/-- The mate of an isomorphism whiskered on the right is the mate whiskered on the left. -/
public theorem conjugateIsoEquiv_isoWhiskerRight {L₁ L₂ : C₀ ⥤ C₁} {R₁ R₂ : C₁ ⥤ C₀}
    {L : C₁ ⥤ C₂} {R : C₂ ⥤ C₁} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (adj : L ⊣ R) (τ : L₂ ≅ L₁) :
    conjugateIsoEquiv (adj₁.comp adj) (adj₂.comp adj) (Functor.isoWhiskerRight τ L) =
      Functor.isoWhiskerLeft R (conjugateIsoEquiv adj₁ adj₂ τ) :=
  Iso.ext (conjugateEquiv_whiskerRight adj₁ adj₂ adj τ.hom)

/-- Changing the adjunction `adj₂` of the source `L₂` of the isomorphism to `adj₂'` composes the
mate with the comparison of the two right adjoints of `L₂`, which is the mate of the identity of
`L₂`. -/
public theorem conjugateIsoEquiv_congr_source {L₁ L₂ : C₀ ⥤ C₁} {R₁ R₂ R₂' : C₁ ⥤ C₀}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (adj₂' : L₂ ⊣ R₂') (α : L₂ ≅ L₁) :
    conjugateIsoEquiv adj₁ adj₂' α =
      conjugateIsoEquiv adj₁ adj₂ α ≪≫ conjugateIsoEquiv adj₂ adj₂' (Iso.refl L₂) :=
  (congrArg (fun x => conjugateIsoEquiv adj₁ adj₂' x) (Iso.refl_trans α)).symm.trans
    (conjugateIsoEquiv_trans adj₁ adj₂ adj₂' (Iso.refl L₂) α)

/-- Changing the adjunction `adj₁` of the target `L₁` of the isomorphism to `adj₁'` precomposes
the mate with the comparison of the two right adjoints of `L₁`, which is the mate of the
identity of `L₁`. -/
public theorem conjugateIsoEquiv_congr_target {L₁ L₂ : C₀ ⥤ C₁} {R₁ R₁' R₂ : C₁ ⥤ C₀}
    (adj₁ : L₁ ⊣ R₁) (adj₁' : L₁ ⊣ R₁') (adj₂ : L₂ ⊣ R₂) (α : L₂ ≅ L₁) :
    conjugateIsoEquiv adj₁' adj₂ α =
      conjugateIsoEquiv adj₁' adj₁ (Iso.refl L₁) ≪≫ conjugateIsoEquiv adj₁ adj₂ α :=
  (congrArg (fun x => conjugateIsoEquiv adj₁' adj₂ x) (Iso.trans_refl α)).symm.trans
    (conjugateIsoEquiv_trans adj₁' adj₁ adj₂ α (Iso.refl L₁))

/-- For an equivalence `e`, the mate of the counit isomorphism `e.inverse ⋙ e.functor ≅ 𝟭`,
with respect to the identity adjunction and the composite of the adjunctions of `e.symm` and `e`,
is the unit isomorphism of `e.symm`. -/
public theorem conjugateIsoEquiv_equivalenceCounitIso (e : C₀ ≌ C₁) :
    conjugateIsoEquiv (Adjunction.id (C := C₁)) (e.symm.toAdjunction.comp e.toAdjunction)
        e.counitIso = e.symm.unitIso := by
  refine Iso.ext ?_
  ext d
  simp [conjugateEquiv_apply_app]

end Stacks.Mates

namespace Stacks.SheafOfModules

variable {C : Type u₀} [Category.{v₀} C] [HasBinaryProducts C]
  {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}

/-- The mate of `SheafOfModules.pullbackPushforwardOverIso`, the identification of restriction
to the slice over `Y` with the pullback along `SheafOfModules.pushforwardOver`, is the
identity. -/
public theorem conjugateIsoEquiv_pullbackPushforwardOverIso (Y : C) :
    conjugateIsoEquiv (SheafOfModules.overPushforwardOverAdj.{w} (R := R) Y)
        (SheafOfModules.pullbackPushforwardAdjunction.{w}
          (SheafOfModules.pushforwardOver (R := R) Y))
        (SheafOfModules.pullbackPushforwardOverIso.{w} (R := R) Y) =
      Iso.refl (SheafOfModules.pushforward.{w} (SheafOfModules.pushforwardOver (R := R) Y)) :=
  Stacks.Mates.conjugateIsoEquiv_leftAdjointUniq _ _

end Stacks.SheafOfModules

namespace Stacks.Scheme.Modules

variable {X Y Z : AlgebraicGeometry.Scheme.{u}}

/-- The mate of `AlgebraicGeometry.Scheme.Modules.pullbackCongr` along an equality `f = g` of
morphisms of schemes is the transport of the pushforward, in the reverse orientation. -/
public theorem conjugateIsoEquiv_pullbackCongr {f g : X ⟶ Y} (hf : f = g) :
    conjugateIsoEquiv (AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction g)
        (AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction f)
        (AlgebraicGeometry.Scheme.Modules.pullbackCongr hf) =
      eqToIso (congrArg (fun k : X ⟶ Y => AlgebraicGeometry.Scheme.Modules.pushforward k)
        hf).symm := by
  subst hf
  refine Iso.ext ?_
  simp [AlgebraicGeometry.Scheme.Modules.pullbackCongr]

/-- The mate of the contraction `AlgebraicGeometry.Scheme.Modules.pullbackComp f g` of an
iterated pullback of modules on schemes is the inverse of the contraction of the iterated
pushforward. -/
public theorem conjugateIsoEquiv_pullbackComp (f : X ⟶ Y) (g : Y ⟶ Z) :
    conjugateIsoEquiv (AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g))
        ((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction g).comp
          (AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction f))
        (AlgebraicGeometry.Scheme.Modules.pullbackComp f g) =
      (AlgebraicGeometry.Scheme.Modules.pushforwardComp f g).symm := by
  have h : conjugateIsoEquiv
      ((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction g).comp
        (AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction f))
      (AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g))
      (AlgebraicGeometry.Scheme.Modules.pullbackComp f g).symm =
        AlgebraicGeometry.Scheme.Modules.pushforwardComp f g :=
    Iso.ext (AlgebraicGeometry.Scheme.Modules.conjugateEquiv_pullbackComp_inv f g)
  rw [Stacks.Mates.conjugateIsoEquiv_iso_symm] at h
  rw [← h, Iso.symm_symm_eq]

end Stacks.Scheme.Modules

namespace AlgebraicGeometry.BigFppfOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The mate of the comparison of Stacks 03DV on the localization -/

/-- The pushforward of sheaves of modules along the comparison of ringed sites of the structure
morphism of `T`, read on sheaves of rings, is a right adjoint. -/
public instance sheafPushforward_objHom_isRightAdjoint (T : BigFppfOver B S hS) :
    (SheafOfModules.pushforward.{u} (objHom B S hS T).toRingCatSheafHom).IsRightAdjoint :=
  inferInstanceAs (Scheme.Modules.pushforward (objHom B S hS T)).IsRightAdjoint

/-- With respect to the two composite pullback–pushforward adjunctions, the mate of
`AlgebraicGeometry.BigFppfOver.associatedModuleObjIso` is the composite of the comparisons of
pushforwards of sheaves of modules supplied by the square of ringed sites of
`AlgebraicGeometry.BigFppfOver.comparisonComp_objStarIso`. -/
public theorem conjugateIsoEquiv_associatedModuleObjIso (T : BigFppfOver B S hS) :
    conjugateIsoEquiv
        ((SheafOfModules.pullbackPushforwardAdjunction.{u} (structureMap B S hS)).comp
          (SheafOfModules.overPushforwardOverAdj.{u} (R := structureSheaf B S hS) T))
        ((SheafOfModules.pullbackPushforwardAdjunction.{u}
            (objHom B S hS T).toRingCatSheafHom).comp
          (SheafOfModules.pullbackPushforwardAdjunction.{u} (objSliceStructureMap B S hS T)))
        (associatedModuleObjIso B S hS T) =
      SheafOfModules.pushforwardComp.{u} (structureMap B S hS)
          (SheafOfModules.pushforwardOver T) ≪≫
        SheafOfModules.pushforwardCongr₂.{u} _ (objStarIso B S hS T)
            (comparisonComp_objStarIso B S hS T) ≪≫
          (SheafOfModules.pushforwardComp.{u} (objHom B S hS T).toRingCatSheafHom
            (objSliceStructureMap B S hS T)).symm := by
  have hA : conjugateIsoEquiv
      ((SheafOfModules.pullbackPushforwardAdjunction.{u} (structureMap B S hS)).comp
        (SheafOfModules.overPushforwardOverAdj.{u} (R := structureSheaf B S hS) T))
      ((SheafOfModules.pullbackPushforwardAdjunction.{u} (structureMap B S hS)).comp
        (SheafOfModules.pullbackPushforwardAdjunction.{u}
          (SheafOfModules.pushforwardOver (R := structureSheaf B S hS) T)))
      (Functor.isoWhiskerLeft (SheafOfModules.pullback.{u} (structureMap B S hS))
        (SheafOfModules.pullbackPushforwardOverIso.{u} (R := structureSheaf B S hS) T)) =
        Iso.refl _ := by
    refine Eq.trans (Stacks.Mates.conjugateIsoEquiv_isoWhiskerLeft _ _ _ _) ?_
    refine Eq.trans (congrArg (fun α => Functor.isoWhiskerRight α
        (SheafOfModules.pushforward.{u} (structureMap B S hS)))
      (Stacks.SheafOfModules.conjugateIsoEquiv_pullbackPushforwardOverIso
        (R := structureSheaf B S hS) T)) ?_
    exact Iso.ext (by simp)
  refine Eq.trans (Stacks.Mates.conjugateIsoEquiv_trans _
    ((SheafOfModules.pullbackPushforwardAdjunction.{u} (structureMap B S hS)).comp
      (SheafOfModules.pullbackPushforwardAdjunction.{u}
        (SheafOfModules.pushforwardOver (R := structureSheaf B S hS) T))) _ _ _) ?_
  refine Eq.trans (congrArg (fun x => x ≪≫ conjugateIsoEquiv
      ((SheafOfModules.pullbackPushforwardAdjunction.{u} (structureMap B S hS)).comp
        (SheafOfModules.pullbackPushforwardAdjunction.{u}
          (SheafOfModules.pushforwardOver (R := structureSheaf B S hS) T)))
      ((SheafOfModules.pullbackPushforwardAdjunction.{u}
          (objHom B S hS T).toRingCatSheafHom).comp
        (SheafOfModules.pullbackPushforwardAdjunction.{u} (objSliceStructureMap B S hS T)))
      (SheafOfModules.pullbackSquareIso.{u} (objHom B S hS T).toRingCatSheafHom
        (objSliceStructureMap B S hS T) (structureMap B S hS)
        (SheafOfModules.pushforwardOver T) (objStarIso B S hS T)
        (comparisonComp_objStarIso B S hS T))) hA) ?_
  exact Eq.trans (Iso.refl_trans _)
    (Stacks.SheafOfModules.conjugateIsoEquiv_pullbackSquareIso _ _ _ _ _
      (comparisonComp_objStarIso B S hS T))

/-! ### The two spellings of restriction to an object, on the adjunctions -/

/-- The adjunction `AlgebraicGeometry.BigFppfOver.objRestrictOverPullbackAdjunction` between
restriction to an object and `SheafOfModules.overPullback` is, up to `HEq`, the adjunction
`SheafOfModules.overMapPushforwardAdj` at the structure morphism. -/
public theorem objRestrictOverPullbackAdjunction_heq (T : BigFppfOver B S hS) :
    HEq (objRestrictOverPullbackAdjunction B S hS T)
      (SheafOfModules.overMapPushforwardAdj.{u} B.structureSheaf T.hom) := by
  unfold objRestrictOverPullbackAdjunction
  simp only [eq_mpr_eq_cast]
  exact cast_heq _ _

/-! ### The mate of the contraction of the iterated pullback -/

/-- For `g : T' ⟶ T`, the pullback along the structure morphism of `T` followed by the pullback
along `g`, contracted by `AlgebraicGeometry.Scheme.Modules.pullbackComp` and transported to the
structure morphism of `T'` along `AlgebraicGeometry.BigFppfOver.objHom_comp`, has as mate the
transport of the pushforward followed by the contraction of the iterated pushforward. -/
public theorem conjugateIsoEquiv_pullbackComp_objHom {T T' : BigFppfOver B S hS} (g : T' ⟶ T) :
    conjugateIsoEquiv (Scheme.Modules.pullbackPushforwardAdjunction (objHom B S hS T'))
        ((Scheme.Modules.pullbackPushforwardAdjunction (objHom B S hS T)).comp
          (Scheme.Modules.pullbackPushforwardAdjunction
            (objHom B (objScheme B S hS T) (contains_objScheme B S hS T) (Over.mk g.left))))
        (Scheme.Modules.pullbackComp
            (objHom B (objScheme B S hS T) (contains_objScheme B S hS T) (Over.mk g.left))
            (objHom B S hS T) ≪≫
          Scheme.Modules.pullbackCongr (objHom_comp B S hS g)) =
      eqToIso (congrArg
          (fun k : objScheme B S hS T' ⟶ S => Scheme.Modules.pushforward k)
          (objHom_comp B S hS g)).symm ≪≫
        (Scheme.Modules.pushforwardComp
          (objHom B (objScheme B S hS T) (contains_objScheme B S hS T) (Over.mk g.left))
          (objHom B S hS T)).symm := by
  refine Eq.trans (Stacks.Mates.conjugateIsoEquiv_trans _
    (Scheme.Modules.pullbackPushforwardAdjunction
      (objHom B (objScheme B S hS T) (contains_objScheme B S hS T) (Over.mk g.left) ≫
        objHom B S hS T)) _ _ _) ?_
  rw [Stacks.Scheme.Modules.conjugateIsoEquiv_pullbackCongr,
    Stacks.Scheme.Modules.conjugateIsoEquiv_pullbackComp]

/-! ### The mate of the functoriality of restriction to an object -/

/-- With respect to the adjunctions
`AlgebraicGeometry.BigFppfOver.objRestrictOverPullbackAdjunction`, whose right adjoints are the
functors `SheafOfModules.overPullback` along the structure morphisms, the mate of
`AlgebraicGeometry.BigFppfOver.objRestrictComp` at `g : T' ⟶ T` is the congruence isomorphism of
`CategoryTheory.Over.w` for `g` followed by `Stacks.SheafOfModules.overPullbackComp`. -/
public theorem conjugateIsoEquiv_objRestrictComp {T T' : BigFppfOver B S hS} (g : T' ⟶ T) :
    conjugateIsoEquiv (objRestrictOverPullbackAdjunction B S hS T')
        ((objRestrictOverPullbackAdjunction B S hS T).comp
          (objRestrictOverPullbackAdjunction B (objScheme B S hS T)
            (contains_objScheme B S hS T) (Over.mk g.left)))
        (objRestrictComp B S hS g) =
      Stacks.SheafOfModules.overPullbackCongr B.structureSheaf (Over.w g).symm ≪≫
        Stacks.SheafOfModules.overPullbackComp B.structureSheaf T.hom g.left := by
  refine Eq.trans (congrArg
    (fun α => conjugateIsoEquiv (objRestrictOverPullbackAdjunction B S hS T')
      ((objRestrictOverPullbackAdjunction B S hS T).comp
        (objRestrictOverPullbackAdjunction B (objScheme B S hS T)
          (contains_objScheme B S hS T) (Over.mk g.left))) α)
    (objRestrictComp_eq B S hS g)) ?_
  refine Eq.trans (Stacks.Mates.conjugateIsoEquiv_of_heq_adjunction
    (objRestrict_eq_overMap B S hS T') (objRestrict_comp_eq_overMap_comp B S hS g) _
    (SheafOfModules.overMapPushforwardAdj.{u} B.structureSheaf T'.hom) _
    ((SheafOfModules.overMapPushforwardAdj.{u} B.structureSheaf T.hom).comp
      (SheafOfModules.overMapPushforwardAdj.{u} B.structureSheaf g.left))
    (objRestrictOverPullbackAdjunction_heq B S hS T')
    (Stacks.Mates.heq_adjunction_comp (objRestrict_eq_overMap B S hS T)
      (objRestrict_eq_overMap B (objScheme B S hS T) (contains_objScheme B S hS T)
        (Over.mk g.left)) _ _ _ _
      (objRestrictOverPullbackAdjunction_heq B S hS T)
      (objRestrictOverPullbackAdjunction_heq B (objScheme B S hS T)
        (contains_objScheme B S hS T) (Over.mk g.left))) _) ?_
  exact Stacks.SheafOfModules.conjugateIsoEquiv_overMapCompIso_trans_overMapCongrIso
    B.structureSheaf T.hom g.left (Over.w g)

end AlgebraicGeometry.BigFppfOver

end
