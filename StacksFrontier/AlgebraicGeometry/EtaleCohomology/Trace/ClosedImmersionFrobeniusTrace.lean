module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ExactPushforwardTwistTrace
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CanonicalCompactSupportFrobenius
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.DirectImageSystem
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.IntegralCohomologicalDimension

/-!
# The canonical Frobenius trace along a finite morphism

Let `i : Z' ⟶ Y'` be a morphism of schemes over `S` intertwining endomorphisms `π_Z` of `Z'` and
`π_Y` of `Y'` over `S`.  The composition isomorphisms of direct images assemble into the data
`γ : i_* ⋙ (p_Y)_* ≅ (p_Z)_*` and `ρ : (π_Z)_* ⋙ i_* ⟶ i_* ⋙ (π_Y)_*` of
`CategoryTheory.Functor.perfectDerivedTrace_derivedTwistEndo_map_eq`, and the compatibility it
asks for is the associativity of the composition isomorphisms.  For `i` integral (for instance a
closed immersion) the direct image `i_*` is exact and preserves injectives, so the twisted trace
on `RΓ(S, R(p_Y)_* (i_* K))` is the one on `RΓ(S, R(p_Z)_* K)`.

## Main results

* `Stacks.EtaleCohomology.directImageTwistTransfer_compat`: the compatibility of `γ`, `ρ` and
  the two twists' identifications.
* `Stacks.EtaleCohomology.perfectDerivedTrace_derivedTwistEndo_directImage_eq`: the trace
  comparison for an integral `i`.

## References

* [Stacks Project, Tag 03UG](https://stacks.math.columbia.edu/tag/03UG), Steps 1 and 2.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.FilteredDerived Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

attribute [local instance] HasDerivedCategory.standard

universe u r

namespace Stacks.EtaleCohomology

variable (Λ : Type r) [Ring Λ] {Z' Y' S : Scheme.{u}} (i : Z' ⟶ Y') (πZ : Z' ⟶ Z') (πY : Y' ⟶ Y')
  (pY : Y' ⟶ S) (pZ : Z' ⟶ S) (e₁ : πZ ≫ i = i ≫ πY) (e₂ : pZ = i ≫ pY) (hY : pY = πY ≫ pY)
  (hZ : pZ = πZ ≫ pZ)

private lemma directImageChase {D : Type*} [Category D] {A B B' E F H : D}
    (a : A ⟶ B) (b : B ⟶ B') (c : B' ⟶ B) (d : B ⟶ H) (x : B' ⟶ E) (y : E ⟶ H) (z : A ⟶ F)
    (w : F ⟶ H) (hA : c ≫ d = x ≫ y) (hB : a ≫ d = z ≫ w) (hc : b ≫ c = 𝟙 B) :
    (a ≫ b) ≫ x ≫ y = z ≫ w := by
  rw [← hA, Category.assoc, reassoc_of% hc, hB]

/-- The comparison `(π_Z)_* ⋙ i_* ⟶ i_* ⋙ (π_Y)_*` through `(π_Z ≫ i)_* = (i ≫ π_Y)_*`. -/
abbrev directImageTwistTransfer :
    etaleModuleDirectImage.{u, r} Λ πZ ⋙ etaleModuleDirectImage.{u, r} Λ i ⟶
      etaleModuleDirectImage.{u, r} Λ i ⋙ etaleModuleDirectImage.{u, r} Λ πY :=
  (etaleModuleDirectImageComp.{u, r} Λ πZ i (πZ ≫ i) rfl).hom ≫
    (etaleModuleDirectImageComp.{u, r} Λ i πY (πZ ≫ i) e₁).inv

include e₂ hY hZ in
/-- **The compatibility of the transfer data**: the associativity of the composition
isomorphisms of direct images. -/
lemma directImageTwistTransfer_compat (X : EtaleModules.{u, r} Λ Z') :
    (etaleModuleDirectImage.{u, r} Λ pY).map
        ((directImageTwistTransfer Λ i πZ πY e₁).app X) ≫
      (etaleModuleDirectImageComp.{u, r} Λ πY pY pY hY).hom.app
        ((etaleModuleDirectImage.{u, r} Λ i).obj X) ≫
      (etaleModuleDirectImageComp.{u, r} Λ i pY pZ e₂).hom.app X =
    (etaleModuleDirectImageComp.{u, r} Λ i pY pZ e₂).hom.app
        ((etaleModuleDirectImage.{u, r} Λ πZ).obj X) ≫
      (etaleModuleDirectImageComp.{u, r} Λ πZ pZ pZ hZ).hom.app X := by
  have h₁ : pZ = (πZ ≫ i) ≫ pY := by rw [Category.assoc, ← e₂, ← hZ]
  have hA := congrArg (fun e => e.hom.app X) (smallEtalePushforwardComp'_assoc i πY pY (πZ ≫ i)
    e₁ pY hY pZ h₁ e₂ (ModuleCat.{max (u + 1) r} Λ))
  have hB := congrArg (fun e => e.hom.app X) (smallEtalePushforwardComp'_assoc πZ i pY (πZ ≫ i)
    rfl pZ e₂ pZ h₁ hZ (ModuleCat.{max (u + 1) r} Λ))
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Category.id_comp] at hA hB
  have hc := (smallEtalePushforward pY (ModuleCat.{max (u + 1) r} Λ)).congr_map
    ((smallEtalePushforwardComp' i πY (πZ ≫ i) e₁ (ModuleCat.{max (u + 1) r} Λ)).inv_hom_id_app X)
  rw [Functor.map_comp, CategoryTheory.Functor.map_id] at hc
  simp only [directImageTwistTransfer, etaleModuleDirectImageComp, NatTrans.comp_app,
    Functor.map_comp]
  exact directImageChase (hA := hA) (hB := hB) (hc := hc)

include e₂ hY hZ in
/-- **The twisted trace along an integral morphism.**  For `i` integral (for instance a closed
immersion) and a bounded below complex `K'` on `Z'` with a twist `τ' : K' ⟶ (π_Z)_* K'`, the trace
of the derived twisted endomorphism of `RΓ(S, R(p_Y)_*(i_* K'))` attached to `i_*(τ') ≫ ρ` is the
trace of that of `RΓ(S, R(p_Z)_* K')` attached to `τ'`. -/
theorem perfectDerivedTrace_derivedTwistEndo_directImage_eq [IsIntegralHom i]
    (K' : CochainComplex.Plus (EtaleModules.{u, r} Λ Z'))
    (τ' : K' ⟶ (etaleModuleDirectImage.{u, r} Λ πZ).mapCochainComplexPlus.obj K')
    (hK : StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      ((etaleModuleGlobalSections.{u, r} Λ S).rightDerivedFunctorPlus.obj
        ((etaleModuleDirectImage.{u, r} Λ pY).rightDerivedFunctorPlus.obj
          (DerivedCategory.Plus.Q.obj
            ((etaleModuleDirectImage.{u, r} Λ i).mapCochainComplexPlus.obj K'))))))
    (hK' : StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      ((etaleModuleGlobalSections.{u, r} Λ S).rightDerivedFunctorPlus.obj
        ((etaleModuleDirectImage.{u, r} Λ pZ).rightDerivedFunctorPlus.obj
          (DerivedCategory.Plus.Q.obj K'))))) :
    perfectDerivedTrace Λ ⟨_, hK⟩ (DerivedCategory.Plus.ι.map (Functor.derivedTwistEndo
        (etaleModuleDirectImage.{u, r} Λ πY) (etaleModuleDirectImage.{u, r} Λ pY)
        (etaleModuleGlobalSections.{u, r} Λ S)
        (etaleModuleDirectImageComp.{u, r} Λ πY pY pY hY)
        ((etaleModuleDirectImage.{u, r} Λ i).mapCochainComplexPlus.obj K')
        ((etaleModuleDirectImage.{u, r} Λ i).mapCochainComplexPlus.map τ' ≫
          Functor.twistTransferMap (etaleModuleDirectImage.{u, r} Λ πY)
            (etaleModuleDirectImage.{u, r} Λ πZ) (etaleModuleDirectImage.{u, r} Λ i)
            (directImageTwistTransfer Λ i πZ πY e₁) K'))) =
      perfectDerivedTrace Λ ⟨_, hK'⟩ (DerivedCategory.Plus.ι.map (Functor.derivedTwistEndo
        (etaleModuleDirectImage.{u, r} Λ πZ) (etaleModuleDirectImage.{u, r} Λ pZ)
        (etaleModuleGlobalSections.{u, r} Λ S)
        (etaleModuleDirectImageComp.{u, r} Λ πZ pZ pZ hZ) K' τ')) := by
  have hex := etaleModuleDirectImage_exact_of_isIntegralHom Λ i
  have : PreservesFiniteLimits (etaleModuleDirectImage.{u, r} Λ i) :=
    ((exactFunctor_iff _).1 hex).1
  have : PreservesFiniteColimits (etaleModuleDirectImage.{u, r} Λ i) :=
    ((exactFunctor_iff _).1 hex).2
  exact Functor.perfectDerivedTrace_derivedTwistEndo_map_eq _ _ _ _ _ _
    (etaleModuleDirectImageComp.{u, r} Λ πY pY pY hY)
    (etaleModuleDirectImageComp.{u, r} Λ πZ pZ pZ hZ)
    (etaleModuleDirectImageComp.{u, r} Λ i pY pZ e₂) _
    (directImageTwistTransfer_compat Λ i πZ πY pY pZ e₁ e₂ hY hZ) K' τ' hK hK'

end Stacks.EtaleCohomology

end
