module

public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.RelativelyPerfectHomDescentTriangle
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.MayerVietorisTag
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullbackUnitComp
public import StacksFrontier.RingTheory.Dualizing.MapDerivedCategory

/-!
# The Mayer–Vietoris step for the conclusion of Stacks 0DKV

In Situation 0DKU fix `K₀, L₀ ∈ D(𝒪_{X₀})`.  For an étale morphism `w : W ⟶ X₀` of algebraic
spaces write `w^*` for restriction of modules along `w` and `w_!` for extension by zero, and
consider the object `w_!(w^*K₀)` of `D(𝒪_{X₀})`.  This file shows that the conclusion of
Stacks 0DKV for the pair `(w_!(w^*K₀), L₀)`, at every shift of the first argument, passes from
the three pieces of an elementary distinguished square `(U ⊆ W, V ⟶ W)` to `W` itself.

This is the Mayer–Vietoris step of the source's proof of Stacks 0DKV.  It is carried out on
`X₀` alone: extension by zero along `w` carries the Mayer–Vietoris triangle of Stacks 08GV on
`W` to a distinguished triangle of `D(𝒪_{X₀})` whose three objects are the objects
`(j ≫ w)_!((j ≫ w)^*K₀)` attached to the three pieces, and the conclusion of the tag at every
shift is closed under distinguished triangles in its first argument.

## Main definitions

* `AlgebraicGeometry.Space.etaleModuleLowerShriekCompIso`: extension by zero along a composite
  of étale morphisms is the composite of the extensions by zero.
* `AlgebraicGeometry.Space.etaleModuleExtendRestrict`: the functor `w_!(w^*-)` on `𝒪_Y`-modules.

## Main results

* `AlgebraicGeometry.Space.RelativeDescentSituation.shiftedHomDescent_extendRestrict_of_eds`:
  the Mayer–Vietoris step.
* `AlgebraicGeometry.Space.RelativeDescentSituation.shiftedHomDescent_of_extendRestrict_id`:
  for the identity of `X₀` the object `w_!(w^*K₀)` is `K₀`.

## References

* [Stacks Project, Tag 0DKV](https://stacks.math.columbia.edu/tag/0DKV)
* [Stacks Project, Tag 08GV](https://stacks.math.columbia.edu/tag/08GV)
* [Stacks Project, Tag 03DJ](https://stacks.math.columbia.edu/tag/03DJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace AlgebraicGeometry.Space

universe u v

attribute [local instance] etaleModulePullback_additive preservesFiniteLimits_etaleModulePullback
  preservesFiniteColimits_etaleModulePullback CategoryTheory.Limits.comp_preservesFiniteLimits
  CategoryTheory.Limits.comp_preservesFiniteColimits

section ExtensionRestriction

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Extension by zero along a composite of étale morphisms** is the composite of the
extensions by zero: both are left adjoint to restriction along the composite. -/
def etaleModuleLowerShriekCompIso {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : IsEtale B S hS f.hom) (hg : IsEtale B S hS g.hom)
    (hfg : IsEtale B S hS (f ≫ g).hom) :
    etaleModuleLowerShriek B S hS f hf ⋙ etaleModuleLowerShriek B S hS g hg ≅
      etaleModuleLowerShriek B S hS (f ≫ g) hfg :=
  Adjunction.leftAdjointUniq
    (((etaleModuleLowerShriekAdjunction B S hS f hf).comp
      (etaleModuleLowerShriekAdjunction B S hS g hg)).ofNatIsoRight
      (etaleModulePullbackCompIso B S hS f g hf hg hfg))
    (etaleModuleLowerShriekAdjunction B S hS (f ≫ g) hfg)

/-- The functor `w_!(w^*-)` on `𝒪_Y`-modules: restriction along an étale morphism `w : X ⟶ Y`
followed by extension by zero. -/
abbrev etaleModuleExtendRestrict {X Y : AlgebraicSpaces B S hS} (w : X ⟶ Y)
    (hw : IsEtale B S hS w.hom) :
    Modules.{u, u} B S hS Y.1 Y.2 ⥤ Modules.{u, u} B S hS Y.1 Y.2 :=
  etaleModulePullback.{u, u} B S hS w hw ⋙ etaleModuleLowerShriek B S hS w hw

/-- `w_!(j_!(j^*(w^*-)))` is `(j ≫ w)_!((j ≫ w)^*-)`. -/
def etaleModuleExtendRestrictCompIso {X Y Z : AlgebraicSpaces B S hS} (j : X ⟶ Y) (w : Y ⟶ Z)
    (hj : IsEtale B S hS j.hom) (hw : IsEtale B S hS w.hom)
    (hjw : IsEtale B S hS (j ≫ w).hom) :
    etaleModulePullback.{u, u} B S hS w hw ⋙ etaleModuleExtendRestrict B S hS j hj ⋙
        etaleModuleLowerShriek B S hS w hw ≅ etaleModuleExtendRestrict B S hS (j ≫ w) hjw :=
  Functor.isoWhiskerRight (etaleModulePullbackCompIso B S hS j w hj hw hjw)
      (etaleModuleLowerShriek B S hS j hj ⋙ etaleModuleLowerShriek B S hS w hw) ≪≫
    Functor.isoWhiskerLeft (etaleModulePullback.{u, u} B S hS (j ≫ w) hjw)
      (etaleModuleLowerShriekCompIso B S hS j w hj hw hjw)

/-- Restriction along the identity followed by extension by zero along the identity is the
identity functor. -/
def etaleModuleExtendRestrictIdIso (X : AlgebraicSpaces B S hS)
    (h : IsEtale B S hS (𝟙 X : X ⟶ X).hom) :
    etaleModuleExtendRestrict B S hS (𝟙 X) h ≅ 𝟭 (Modules.{u, u} B S hS X.1 X.2) :=
  Functor.isoWhiskerRight (etaleModulePullbackIdIso B S hS h) _ ≪≫ Functor.leftUnitor _ ≪≫
    (Adjunction.leftAdjointUniq (etaleModuleLowerShriekAdjunction B S hS (𝟙 X) h)
      ((Adjunction.id).ofNatIsoRight (etaleModulePullbackIdIso B S hS h).symm))

end ExtensionRestriction

namespace RelativeDescentSituation

/- The conclusion of Stacks 0DKV,
`AlgebraicGeometry.Space.RelativeDescentSituation.HomDescent`, and the derived pullback
`AlgebraicGeometry.Space.smallEtaleDerivedModulePullback` it is built from are stated for the
standard model of the derived category, so the declarations below are stated at it too. -/
attribute [local instance 10000] HasDerivedCategory.standard

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)]
  (D : RelativeDescentSituation B S hS hZ I) (P : DerivedPullbackComposition B S hS)

/-! Restriction and extension by zero along a morphism into `X₀` are exact.  These are
`AlgebraicGeometry.Space.etaleModulePullback_additive` and its companions, restated with target
`X₀` because instance search does not reach them through `initialSource`. -/

/-- Restriction along an étale morphism into `X₀` is additive. -/
theorem additive_etaleModulePullback_initial {W : AlgebraicSpaces B S hS}
    (w : W ⟶ D.initialSource) (hw : IsEtale B S hS w.hom) :
    (etaleModulePullback.{u, u} B S hS w hw).Additive :=
  etaleModulePullback_additive B S hS w hw

/-- Restriction along an étale morphism into `X₀` preserves finite limits. -/
theorem preservesFiniteLimits_etaleModulePullback_initial {W : AlgebraicSpaces B S hS}
    (w : W ⟶ D.initialSource) (hw : IsEtale B S hS w.hom) :
    PreservesFiniteLimits (etaleModulePullback.{u, u} B S hS w hw) :=
  preservesFiniteLimits_etaleModulePullback B S hS w hw

/-- Restriction along an étale morphism into `X₀` preserves finite colimits. -/
theorem preservesFiniteColimits_etaleModulePullback_initial {W : AlgebraicSpaces B S hS}
    (w : W ⟶ D.initialSource) (hw : IsEtale B S hS w.hom) :
    PreservesFiniteColimits (etaleModulePullback.{u, u} B S hS w hw) :=
  preservesFiniteColimits_etaleModulePullback B S hS w hw

/-- Extension by zero along an étale morphism into `X₀` is additive. -/
theorem additive_etaleModuleLowerShriek_initial {W : AlgebraicSpaces B S hS}
    (w : W ⟶ D.initialSource) (hw : IsEtale B S hS w.hom) :
    (etaleModuleLowerShriek B S hS w hw).Additive :=
  etaleModuleLowerShriek_additive B S hS w hw

/-- Extension by zero along an étale morphism into `X₀` preserves finite limits. -/
theorem preservesFiniteLimits_etaleModuleLowerShriek_initial {W : AlgebraicSpaces B S hS}
    (w : W ⟶ D.initialSource) (hw : IsEtale B S hS w.hom) :
    PreservesFiniteLimits (etaleModuleLowerShriek B S hS w hw) :=
  preservesFiniteLimits_etaleModuleLowerShriek B S hS w hw

/-- Extension by zero along an étale morphism into `X₀` preserves finite colimits. -/
theorem preservesFiniteColimits_etaleModuleLowerShriek_initial {W : AlgebraicSpaces B S hS}
    (w : W ⟶ D.initialSource) (hw : IsEtale B S hS w.hom) :
    PreservesFiniteColimits (etaleModuleLowerShriek B S hS w hw) :=
  preservesFiniteColimits_etaleModuleLowerShriek B S hS w hw

attribute [local instance] additive_etaleModulePullback_initial
  preservesFiniteLimits_etaleModulePullback_initial
  preservesFiniteColimits_etaleModulePullback_initial additive_etaleModuleLowerShriek_initial
  preservesFiniteLimits_etaleModuleLowerShriek_initial
  preservesFiniteColimits_etaleModuleLowerShriek_initial

/-- The object `w_!(w^*K₀)` of `D(𝒪_{X₀})` attached to an étale morphism `w : W ⟶ X₀`. -/
abbrev extendRestrictObj {W : AlgebraicSpaces B S hS} (w : W ⟶ D.initialSource)
    (hw : IsEtale B S hS w.hom) (K₀ : D.InitialDerived) : D.InitialDerived :=
  (etaleModuleExtendRestrict B S hS w hw).mapDerivedCategory.obj K₀

variable {D}

/-- **The Mayer–Vietoris step of Stacks 0DKV.** Let `w : W ⟶ X₀` be étale and let
`(U ⊆ W, V ⟶ W)` be an elementary distinguished square with intersection `U ×_W V`.  If the
conclusion of the tag holds at every shift for `(j ≫ w)_!((j ≫ w)^*K₀)` against `L₀`, for each of
the three morphisms `j` from `U`, `V` and `U ×_W V` to `W`, then it holds for `w_!(w^*K₀)`. -/
theorem shiftedHomDescent_extendRestrict_of_eds {W : AlgebraicSpaces B S hS}
    (w : W ⟶ D.initialSource) (hw : IsEtale B S hS w.hom)
    {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {Uo : Subfunctor W.1} {fV : V ⟶ W.1}
    (hsq : IsElementaryDistinguishedSquare B S hS W.2 Uo fV) (K₀ L₀ : D.InitialDerived)
    (hU : D.ShiftedHomDescent P (D.extendRestrictObj (edsOpenHom B S hS hsq ≫ w)
      (isEtale_comp B S hS (isEtale_edsOpenHom B S hS hsq) hw) K₀) L₀)
    (hV : D.ShiftedHomDescent P (D.extendRestrictObj (edsEtaleHom B S hS hsq ≫ w)
      (isEtale_comp B S hS (isEtale_edsEtaleHom B S hS hsq) hw) K₀) L₀)
    (hP : D.ShiftedHomDescent P (D.extendRestrictObj (edsInterHom B S hS hsq ≫ w)
      (isEtale_comp B S hS (isEtale_edsInterHom B S hS hsq) hw) K₀) L₀) :
    D.ShiftedHomDescent P (D.extendRestrictObj w hw K₀) L₀ := by
  obtain ⟨δ, hT⟩ := (mayerVietoris_shortExact_and_mem_distTriang B S hS hsq).2
    ((etaleModulePullback.{u, u} B S hS w hw).mapDerivedCategory.obj K₀)
  have hT' := (etaleModuleLowerShriek B S hS w hw).mapDerivedCategory.map_distinguished _ hT
  have key : ∀ {Y : AlgebraicSpaces B S hS} (j : Y ⟶ W) (hj : IsEtale B S hS j.hom),
      D.ShiftedHomDescent P (D.extendRestrictObj (j ≫ w) (isEtale_comp B S hS hj hw) K₀) L₀ →
      D.ShiftedHomDescent P ((etaleModuleLowerShriek B S hS w hw).mapDerivedCategory.obj
        ((etaleModuleExtendRestrict B S hS j hj).mapDerivedCategory.obj
          ((etaleModulePullback.{u, u} B S hS w hw).mapDerivedCategory.obj K₀))) L₀ :=
    fun j hj ↦ shiftedHomDescent_of_iso P
      (((etaleModuleLowerShriek B S hS w hw).mapDerivedCategory.mapIso
        ((Dualizing.mapDerivedCategoryComp (etaleModulePullback.{u, u} B S hS w hw)
          (etaleModuleExtendRestrict B S hS j hj)).app K₀).symm ≪≫
      ((Dualizing.mapDerivedCategoryComp
        (etaleModulePullback.{u, u} B S hS w hw ⋙ etaleModuleExtendRestrict B S hS j hj)
        (etaleModuleLowerShriek B S hS w hw)).app K₀).symm ≪≫
      (Dualizing.mapDerivedCategoryNatIso _ _
        (etaleModuleExtendRestrictCompIso B S hS j w hj hw (isEtale_comp B S hS hj hw))).app
          K₀).symm)
  refine shiftedHomDescent_of_iso P ((Dualizing.mapDerivedCategoryComp
      (etaleModulePullback.{u, u} B S hS w hw) (etaleModuleLowerShriek B S hS w hw)).app K₀).symm
    (shiftedHomDescent_obj₃ P _ hT' L₀ ?_ ?_)
  · exact key _ (isEtale_edsInterHom B S hS hsq) hP
  · -- the middle term, through the image of the biproduct triangle
    exact shiftedHomDescent_obj₂ P _
      ((etaleModuleLowerShriek B S hS w hw).mapDerivedCategory.map_distinguished _
        (binaryBiproductTriangle_distinguished _ _)) L₀
      (key _ (isEtale_edsOpenHom B S hS hsq) hU) (key _ (isEtale_edsEtaleHom B S hS hsq) hV)

/-- For the identity of `X₀` the object `w_!(w^*K₀)` is `K₀`, so the conclusion of Stacks 0DKV
for `K₀` follows from its form at the identity. -/
theorem shiftedHomDescent_of_extendRestrict_id
    (h : IsEtale B S hS (𝟙 D.initialSource : D.initialSource ⟶ D.initialSource).hom)
    {K₀ L₀ : D.InitialDerived}
    (hK : D.ShiftedHomDescent P (D.extendRestrictObj (𝟙 D.initialSource) h K₀) L₀) :
    D.ShiftedHomDescent P K₀ L₀ :=
  have := etaleModulePullback_additive B S hS (𝟙 D.initialSource) h
  have := preservesFiniteLimits_etaleModulePullback B S hS (𝟙 D.initialSource) h
  have := preservesFiniteColimits_etaleModulePullback B S hS (𝟙 D.initialSource) h
  have := etaleModuleLowerShriek_additive B S hS (𝟙 D.initialSource) h
  have := preservesFiniteLimits_etaleModuleLowerShriek B S hS (𝟙 D.initialSource) h
  have := preservesFiniteColimits_etaleModuleLowerShriek B S hS (𝟙 D.initialSource) h
  shiftedHomDescent_of_iso P
    ((Dualizing.mapDerivedCategoryNatIso _ _
      (etaleModuleExtendRestrictIdIso B S hS D.initialSource h)).app K₀ ≪≫
      (Functor.mapDerivedCategoryIdIso
        (C₁ := Modules.{u, u} B S hS D.X₀ D.initial_isAlgebraicSpace)).app K₀) hK

end RelativeDescentSituation

end AlgebraicGeometry.Space

end
