module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleTwoIsoChartProjection
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionChartBaseChangeDense
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SquareZeroExtensionAmbientSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftDifferenceSquareZeroValues

/-!
# The inverse image of the ambient structure sheaf is the extension

Let `E` be a square-zero extension `𝒜 ⟶ 𝒪_X` of the structure sheaf of `X`, and let
`i : X ⟶ X'` be the morphism to the ambient algebraic space built from a charted presentation.
We show that the comparison `i⁻¹𝒪_{X'} ⟶ 𝒜` is an isomorphism of sheaves of commutative rings
on the small étale site of `X`, compatible with the surjections onto `𝒪_X`.

## Main definitions

* `ambientSharp`: The comparison `𝒪_{X'} ⟶ i_*𝒜`.
* `ambientSheafIsoHom`: The comparison `i⁻¹𝒪_{X'} ⟶ 𝒜`, adjunct to `ambientSharp`.

## Main results

* `isIso_ambientSheafIsoHom`: The comparison `i⁻¹𝒪_{X'} ⟶ 𝒜` is an isomorphism.
* `ambientSheafIsoHom_comp_π`: Composed with `𝒜 ⟶ 𝒪_X`, the comparison is the inverse-image
  form of `i^♯`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe u

namespace AlgebraicGeometry.Space

namespace SquareZeroExtension

attribute [local instance] hasSheafify_bigFppfOver

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X Y : AlgebraicSpaces B S hS} {f : X ⟶ Y} {E : SquareZeroExtension B S hS f}
  {C : ChartedPresentation B S hS f}
  {hcU : B.Contains (chartThickening B S hS E (presentationChart C.P))}
  {hcR : B.Contains (chartThickening B S hS E (presentationRelationChart C.P))}
  (i : X ⟶ ambient E C hcU hcR)
  (hi : C.P.toSpace ≫ i.hom = yoneda.map (incU E C hcU) ≫ ambQuot E C hcU hcR)

/-- The pushforward of the morphism of topoi underlying `i` is the direct image along `i` on small
étale sites. -/
theorem toToposHom_pushforward_eq :
    (smallEtaleRingedToposHom B S hS i).toToposHom.pushforward = smallEtaleDirectImage B S hS i :=
  rfl

/-- Restriction of sheaves of rings along base change of étale charts to `X`. -/
abbrev baseChangeRestrict (A : Sheaf (SmallEtale.topology B S hS X.1) CommRingCat.{u}) :
    Sheaf (SmallEtale.topology B S hS (ambient E C hcU hcR).1) CommRingCat.{u} :=
  letI := isContinuous_smallBaseChange B S hS i (ambRep i hi)
  ((smallBaseChange B S hS i (ambRep i hi)).sheafPushforwardContinuous CommRingCat.{u}
    (SmallEtale.topology B S hS (ambient E C hcU hcR).1) (SmallEtale.topology B S hS X.1)).obj A

/-- The comparison of the direct image with restriction along base change, on the underlying
sheaves of rings. -/
def pushforwardRingIsoRestrictionRing (A : Sheaf (SmallEtale.topology B S hS X.1) CommRingCat.{u}) :
    letI := isContinuous_smallBaseChange B S hS i (ambRep i hi)
    pullbackRingSheaf (SmallEtale.topology B S hS (ambient E C hcU hcR).1)
        (smallEtaleDirectImage B S hS i)
        (Stacks.SheafOfModules.Tensor.ringSheaf (J := SmallEtale.topology B S hS X.1) A) ≅
      pullbackRingSheaf (SmallEtale.topology B S hS (ambient E C hcU hcR).1)
        ((smallBaseChange B S hS i (ambRep i hi)).sheafPushforwardContinuous (Type u)
          (SmallEtale.topology B S hS (ambient E C hcU hcR).1)
          (SmallEtale.topology B S hS X.1))
        (Stacks.SheafOfModules.Tensor.ringSheaf (J := SmallEtale.topology B S hS X.1) A) :=
  letI := isContinuous_smallBaseChange B S hS i (ambRep i hi)
  { hom := pullbackRingSheafMapOfNatTrans _ _ (chartComparison B S hS i (ambRep i hi)).hom
    inv := pullbackRingSheafMapOfNatTrans _ _ (chartComparison B S hS i (ambRep i hi)).inv
    hom_inv_id := pullbackRingSheafMapOfNatTrans_hom_inv_id _ _ _
    inv_hom_id := pullbackRingSheafMapOfNatTrans_hom_inv_id _ _
      (chartComparison B S hS i (ambRep i hi)).symm }

/-- The comparison of the direct image of sheaves of rings with restriction along base change of
étale charts, on sheaves of rings. -/
def pushforwardRingIsoRestriction (A : Sheaf (SmallEtale.topology B S hS X.1) CommRingCat.{u}) :
    (pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS i).toToposHom).obj A ≅
      baseChangeRestrict i hi A :=
  letI := isContinuous_smallBaseChange B S hS i (ambRep i hi)
  (show (pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS i).toToposHom).obj A ≅
      pullbackCommRingSheaf.{u, u, u, u + 1, u, u + 1}
        (SmallEtale.topology B S hS (ambient E C hcU hcR).1)
        (smallEtaleDirectImage B S hS i) A from Iso.refl _) ≪≫
  (fullyFaithfulForgetCommRingSheaf.{u, u, u + 1}
      (SmallEtale.topology B S hS (ambient E C hcU hcR).1)).preimageIso
      (X := pullbackCommRingSheaf.{u, u, u, u + 1, u, u + 1}
        (SmallEtale.topology B S hS (ambient E C hcU hcR).1)
        (smallEtaleDirectImage B S hS i) A)
      (Y := pullbackCommRingSheaf.{u, u, u, u + 1, u, u + 1}
        (SmallEtale.topology B S hS (ambient E C hcU hcR).1)
        ((smallBaseChange B S hS i (ambRep i hi)).sheafPushforwardContinuous (Type u)
          (SmallEtale.topology B S hS (ambient E C hcU hcR).1)
          (SmallEtale.topology B S hS X.1)) A)
      (pushforwardRingIsoRestrictionRing i hi A) ≪≫
    restrictionCommRingIso _ _ (smallBaseChange B S hS i (ambRep i hi)) A

/-- The direct-image form of the comparison: `𝒪_{X'} ⟶ i_*𝒜`. -/
def ambientSharp :
    (smallEtaleRingedTopos B S hS (ambient E C hcU hcR)).O ⟶
      (pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS i).toToposHom).obj E.A :=
  ambientSheafHom i hi ≫ (pushforwardRingIsoRestriction i hi E.A).inv

/-- The comparison `𝒪_{X'} ⟶ i_*𝒜` is an isomorphism. -/
instance isIso_ambientSharp : IsIso (ambientSharp i hi) := by
  rw [ambientSharp]
  infer_instance

/-- **The comparison `i⁻¹𝒪_{X'} ⟶ 𝒜`**, adjunct to `ambientSharp`. -/
def ambientSheafIsoHom :
    (inverseImageCommRingFunctor (smallEtaleRingedToposHom B S hS i).toToposHom).obj
        (smallEtaleRingedTopos B S hS (ambient E C hcU hcR)).O ⟶ E.A :=
  ((commRingImageAdjunction (smallEtaleRingedToposHom B S hS i).toToposHom).homEquiv _ _).symm
    (ambientSharp i hi)

/-- The comparison `i⁻¹𝒪_{X'} ⟶ 𝒜` is an isomorphism. -/
instance isIso_ambientSheafIsoHom : IsIso (ambientSheafIsoHom i hi) := by
  have hci := (isThickeningHom_ambientMap i hi).isClosedImmersion
  have hc : IsIso (smallEtaleRingedToposHom B S hS i).toToposHom.adj.counit :=
    (smallEtalePullbackPushforwardCounitIso B S hS i hci).isIso_hom
  have h : (sheafCompose (SmallEtale.topology B S hS X.1)
      (CategoryTheory.forget CommRingCat.{u})).map (ambientSheafIsoHom i hi) =
      (smallEtaleRingedToposHom B S hS i).toToposHom.inverseImage.map
        ((sheafCompose (smallEtaleRingedTopos B S hS (ambient E C hcU hcR)).J
          (CategoryTheory.forget CommRingCat.{u})).map (ambientSharp i hi)) ≫
      (smallEtaleRingedToposHom B S hS i).toToposHom.adj.counit.app
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (J := SmallEtale.topology B S hS X.1) E.A).ringSheaf :=
    (MorphismOfTopoi.ringAdjunction_homEquiv_symm_forget
      (smallEtaleRingedToposHom B S hS i).toToposHom _ _ (ambientSharp i hi)).trans
      ((smallEtaleRingedToposHom B S hS i).toToposHom.adj.homEquiv_counit _ _ _)
  have : IsIso ((sheafCompose (SmallEtale.topology B S hS (ambient E C hcU hcR).1)
      (CategoryTheory.forget CommRingCat.{u})).map (ambientSharp i hi)) := inferInstance
  have : IsIso ((sheafCompose (SmallEtale.topology B S hS X.1)
      (CategoryTheory.forget CommRingCat.{u})).map (ambientSheafIsoHom i hi)) := by
    rw [h]
    have i0 : IsIso ((sheafCompose (smallEtaleRingedTopos B S hS (ambient E C hcU hcR)).J
        (CategoryTheory.forget CommRingCat.{u})).map (ambientSharp i hi)) :=
      Functor.map_isIso _ _
    have i1 := NatIso.isIso_app_of_isIso (smallEtaleRingedToposHom B S hS i).toToposHom.adj.counit
      (Stacks.SheafOfModules.Tensor.ringSheaf (J := SmallEtale.topology B S hS X.1) E.A).ringSheaf
    have i2 : IsIso ((smallEtaleRingedToposHom B S hS i).toToposHom.inverseImage.map
        ((sheafCompose (smallEtaleRingedTopos B S hS (ambient E C hcU hcR)).J
          (CategoryTheory.forget CommRingCat.{u})).map (ambientSharp i hi))) :=
      ((smallEtaleRingedToposHom B S hS i).toToposHom.inverseImage.mapIso
        ((sheafCompose (smallEtaleRingedTopos B S hS (ambient E C hcU hcR)).J
          (CategoryTheory.forget CommRingCat.{u})).mapIso (asIso (ambientSharp i hi)))).isIso_hom
    exact IsIso.comp_isIso' i2 i1
  exact isIso_of_reflects_iso _ (sheafCompose (SmallEtale.topology B S hS X.1)
    (CategoryTheory.forget CommRingCat.{u}))

/-- Two morphisms of sheaves of commutative rings agree as soon as they agree on all sections. -/
theorem commRingSheaf_hom_ext {Cc : Type*} [Category Cc] {Jc : GrothendieckTopology Cc}
    {P Q : Sheaf Jc CommRingCat.{u}} {a b : P ⟶ Q}
    (h : ∀ W x, a.hom.app W x = b.hom.app W x) : a = b :=
  Sheaf.hom_ext (NatTrans.ext (funext fun W => CommRingCat.hom_ext (RingHom.ext (h W))))

/-- On sections, the comparison of the direct image with restriction is the chart comparison of
sheaves of sets. -/
theorem pushforwardRingIsoRestriction_hom_app
    (A : Sheaf (SmallEtale.topology B S hS X.1) CommRingCat.{u})
    (W : (SmallEtale B S hS (ambient E C hcU hcR).1)ᵒᵖ)
    (y : ToType (((pushforwardCommRingFunctor
      (smallEtaleRingedToposHom B S hS i).toToposHom).obj A).obj.obj W)) :
    (pushforwardRingIsoRestriction i hi A).hom.hom.app W y =
      ((chartComparison B S hS i (ambRep i hi)).hom.app
        (Stacks.SheafOfModules.Tensor.ringSheaf (J := SmallEtale.topology B S hS X.1)
          A).ringSheaf).hom.app W y := by
  let := isContinuous_smallBaseChange B S hS i (ambRep i hi)
  have h1 := (fullyFaithfulForgetCommRingSheaf.{u, u, u + 1}
      (SmallEtale.topology B S hS (ambient E C hcU hcR).1)).map_preimage
      (X := pullbackCommRingSheaf.{u, u, u, u + 1, u, u + 1}
        (SmallEtale.topology B S hS (ambient E C hcU hcR).1) (smallEtaleDirectImage B S hS i) A)
      (Y := pullbackCommRingSheaf.{u, u, u, u + 1, u, u + 1}
        (SmallEtale.topology B S hS (ambient E C hcU hcR).1)
        ((smallBaseChange B S hS i (ambRep i hi)).sheafPushforwardContinuous (Type u)
          (SmallEtale.topology B S hS (ambient E C hcU hcR).1)
          (SmallEtale.topology B S hS X.1)) A)
      (pushforwardRingIsoRestrictionRing i hi A).hom
  have h2 := congrArg (fun m => (sheafCompose (SmallEtale.topology B S hS (ambient E C hcU hcR).1)
    (CategoryTheory.forget RingCat.{u})).map m) h1
  simp only [pushforwardRingIsoRestrictionRing] at h2
  exact Sheaf.hom_congr_app_apply h2 W y

/-- The comparison of the direct image with restriction along base change commutes with the
morphisms induced by `E.π : 𝒜 ⟶ 𝒪_X`. -/
theorem pushforwardRingIsoRestriction_naturality :
    letI := isContinuous_smallBaseChange B S hS i (ambRep i hi)
    (pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS i).toToposHom).map E.π ≫
        (pushforwardRingIsoRestriction i hi (smallEtaleRingedTopos B S hS X).O).hom =
      (pushforwardRingIsoRestriction i hi E.A).hom ≫
        ((smallBaseChange B S hS i (ambRep i hi)).sheafPushforwardContinuous CommRingCat.{u}
          (SmallEtale.topology B S hS (ambient E C hcU hcR).1)
          (SmallEtale.topology B S hS X.1)).map E.π := by
  let := isContinuous_smallBaseChange B S hS i (ambRep i hi)
  refine commRingSheaf_hom_ext fun W y => ?_
  change (pushforwardRingIsoRestriction i hi (smallEtaleRingedTopos B S hS X).O).hom.hom.app W
      (((pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS i).toToposHom).map
        E.π).hom.app W y) =
    E.π.hom.app _ ((pushforwardRingIsoRestriction i hi E.A).hom.hom.app W y)
  rw [pushforwardRingIsoRestriction_hom_app, pushforwardRingIsoRestriction_hom_app]
  have hπ := Sheaf.hom_congr_app_apply (MorphismOfTopoi.pushforwardRing_map_forget
    (smallEtaleRingedToposHom B S hS i).toToposHom E.π) W y
  refine (congrArg _ hπ).trans ?_
  exact Sheaf.hom_congr_app_apply ((chartComparison B S hS i (ambRep i hi)).hom.naturality
    ((sheafCompose (SmallEtale.topology B S hS X.1) (CategoryTheory.forget CommRingCat.{u})).map
      E.π)) W y

/-- **The comparison lies over the structure map**: followed by the direct image of the reduction
it is `i^♯`. -/
theorem ambientSharp_comp_π :
    ambientSharp i hi ≫
        (pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS i).toToposHom).map E.π =
      (smallEtaleRingedToposHom B S hS i).fSharp := by
  let := isContinuous_smallBaseChange B S hS i (ambRep i hi)
  refine (cancel_mono (pushforwardRingIsoRestriction i hi (smallEtaleRingedTopos B S hS X).O).hom).1
    ?_
  rw [ambientSharp, Category.assoc, Category.assoc, pushforwardRingIsoRestriction_naturality,
    Iso.inv_hom_id_assoc, ambientSheafHom_comp_π]
  refine commRingSheaf_hom_ext fun W s => ?_
  change _ = (pushforwardRingIsoRestriction i hi (smallEtaleRingedTopos B S hS X).O).hom.hom.app W
    ((smallEtaleRingedToposHom B S hS i).fSharp.hom.app W s)
  refine Eq.trans ?_ (pushforwardRingIsoRestriction_hom_app i hi
    (smallEtaleRingedTopos B S hS X).O W
    ((smallEtaleRingedToposHom B S hS i).fSharp.hom.app W s)).symm
  exact (chartComparison_structureSharp B S hS i (ambRep i hi) W.unop s).symm

/-- **The comparison `i⁻¹𝒪_{X'} ≅ 𝒜` is compatible with the surjections to `𝒪_X`.** -/
theorem ambientSheafIsoHom_comp_π :
    ambientSheafIsoHom i hi ≫ E.π = (smallEtaleRingedToposHom B S hS i).fSharpInverseImage := by
  rw [ambientSheafIsoHom, ← Adjunction.homEquiv_naturality_right_symm, ambientSharp_comp_π]
  rfl

end SquareZeroExtension

end AlgebraicGeometry.Space

end
