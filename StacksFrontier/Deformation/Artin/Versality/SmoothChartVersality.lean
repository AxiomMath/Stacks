module

public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteType.SpecField
public import StacksFrontier.AlgebraicGeometry.Stacks.VersalChartSmoothNeighbourhood
public import StacksFrontier.Deformation.Artin.Versality.Openness

/-!
# Versality at every finite type point gives the condition of Stacks 07XS (Stacks 07XT)

Let `S` be a locally Noetherian scheme, `𝒳` a category fibred in groupoids over the big fppf
site of `S` satisfying (RS), and `x` an object of `𝒳` over a scheme `U` locally of finite type
over `S`. If `x` is versal at every finite type point of `U`, then the 1-morphism
`x : (Sch/U)_{fppf} ⟶ 𝒳` satisfies the condition of Stacks 07XS: at every field-valued point
`Spec l ⟶ U` with `l` of finite type over `S`, the induced map of predeformation categories is
smooth.

The source's argument: the image `u₀` of `Spec l ⟶ U` is a finite type point and `l / κ(u₀)` is
finite (Stacks 01TA), so Stacks 07XG applies. Stacks 07XG is stated for the 2-Yoneda morphism
built from the canonical choice of pullbacks of `𝒳`, while `AlgebraicGeometry.Stack.objectMorphism`
is built from the chosen lifts of the 2-Yoneda lemma; both maps of predeformation categories are
smooth exactly when the lifting property `Deformation.Artin.LiftsAtResiduePoint` holds
(`Deformation.Artin.isSmooth_mapPredeformationCategory_iff_liftsAtResiduePoint`), which does not
mention the choice.

## Main results

* `Deformation.Artin.isFiniteTypePoint_of_locallyOfFiniteType_fieldPoint`: the image of a field
  valued point locally of finite type is a finite type point.
* `AlgebraicGeometry.Stack.isSmoothOnPredeformationCategories_objectMorphism_of_isVersalAt`:
  the statement of Stacks 07XT (used here without the tag).

## References

* [Stacks Project, Tag 07XT](https://stacks.math.columbia.edu/tag/07XT)
* [Stacks Project, Tag 07XG](https://stacks.math.columbia.edu/tag/07XG)
* [Stacks Project, Tag 01TA](https://stacks.math.columbia.edu/tag/01TA)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Deformation.Artin

/-- The image of a field-valued point `g : Spec l ⟶ X` which is locally of finite type is a finite
type point of `X`: by Stacks 01TA it is closed in an affine open of `X`, and the residue field
point of a point closed in an affine open is of finite type by Stacks 01TA again. -/
theorem isFiniteTypePoint_of_locallyOfFiniteType_fieldPoint {l : Type u} [Field l]
    {X : Scheme.{u}} (g : Spec (.of l) ⟶ X) (hg : LocallyOfFiniteType g) :
    IsFiniteTypePoint ((Scheme.SpecToEquivOfField l X) g).1 := by
  set x := ((Scheme.SpecToEquivOfField l X) g).1 with hxdef
  obtain ⟨W, -, w, hw, hwc, -⟩ := ((finiteType_specField_tfae g).out 2 4).mp hg
  let k' : Type u := IsLocalRing.ResidueField (X.presheaf.stalk x)
  let g' : Spec (.of k') ⟶ X := X.fromSpecResidueField x
  have hres : (Scheme.SpecToEquivOfField k' X) g' = ⟨x, CommRingCat.ofHom (RingHom.id k')⟩ := by
    apply (Scheme.SpecToEquivOfField k' X).symm.injective
    rw [Equiv.symm_apply_apply]
    show g' = Spec.map (𝟙 (.of k')) ≫ X.fromSpecResidueField x
    rw [Spec.map_id]
    exact (Category.id_comp _).symm
  refine ((finiteType_specField_tfae g').out 4 1).mp ?_
  refine ⟨W, ?_, w, ?_, hwc, ?_⟩
  · intro y _
    have h : g' y = x := Scheme.fromSpecResidueField_apply x y
    show g' y ∈ W.1
    rw [h, hxdef, ← hw]
    exact w.2
  · rwa [hres]
  · rw [hres]
    show Module.Finite k' k'
    infer_instance

end Deformation.Artin

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Versality at all finite type points gives the condition of Stacks 07XS** (the statement of
Stacks 07XT). Let `S` be a
locally Noetherian scheme, `𝒳` a category fibred in groupoids
over the big fppf site of `S` satisfying (RS), `U` a scheme locally of finite type over `S` and
`x` an object of `𝒳` over `U` which is versal at every finite type point of `U`. Then
`x : (Sch/U)_{fppf} ⟶ 𝒳` satisfies the condition of Stacks 07XS. -/
theorem isSmoothOnPredeformationCategories_objectMorphism_of_isVersalAt [IsLocallyNoetherian S]
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)) (x : 𝒳.val.obj)
    (hU : LocallyOfFiniteType ((𝒳.val.p ⋙ Over.post B.inclusion).obj x).hom)
    (hversal : ∀ u₀ : ((𝒳.val.p ⋙ Over.post B.inclusion).obj x).left,
      IsFiniteTypePoint u₀ →
        Deformation.Artin.IsVersalAt ((𝒳.val.p ⋙ Over.post B.inclusion).obj x)
          (𝒳.val.p ⋙ Over.post B.inclusion) u₀ x rfl)
    (hRS : Deformation.Artin.SatisfiesRS B S hS 𝒳.val.p 𝒳.isFiberedInGroupoids) :
    Deformation.Artin.IsSmoothOnPredeformationCategories B S hS
      (schemeFibredCategory B S hS (𝒳.val.p.obj x)).val.p 𝒳.val.p
      (CatFiberedInGroupoids.homFunctor
        (objectMorphism B S hS 𝒳 (Functor.Fiber.mk (a := x) rfl)))
      (CatFiberedInGroupoids.homFunctor_comp_p _) := by
  intro Λ l _ _ _ iΛ x₀ hx₀ hlft _ _
  let p := 𝒳.val.p
  let U := (p ⋙ Over.post B.inclusion).obj x
  let g := Deformation.Artin.fieldPointMap B S hS p x iΛ x₀ hx₀
  have hgS : g ≫ U.hom = Spec.map (CommRingCat.ofHom (algebraMap Λ l)) ≫ iΛ :=
    Deformation.Artin.fieldPointMap_comp_hom B S hS p x iΛ x₀ hx₀
  have hg : LocallyOfFiniteType g := by
    have : LocallyOfFiniteType (g ≫ U.hom) := by rwa [hgS]
    exact LocallyOfFiniteType.of_comp (f := g) (g := U.hom) this
  set u₀ := ((Scheme.SpecToEquivOfField l U.left) g).1
  set φ := ((Scheme.SpecToEquivOfField l U.left) g).2
  have hu₀ : IsFiniteTypePoint u₀ :=
    Deformation.Artin.isFiniteTypePoint_of_locallyOfFiniteType_fieldPoint g hg
  let : Algebra (U.left.residueField u₀) l := φ.hom.toAlgebra
  have hfin : Module.Finite (U.left.residueField u₀) l := by
    obtain ⟨-, -, -, -, -, h⟩ := ((finiteType_specField_tfae g).out 2 4).mp hg
    exact h
  have hfield : g = Spec.map (CommRingCat.ofHom (algebraMap (U.left.residueField u₀) l)) ≫
      U.left.fromSpecResidueField u₀ :=
    ((Scheme.SpecToEquivOfField l U.left).symm_apply_apply g).symm
  let : p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered
  have h07XG := Deformation.Artin.isSmooth_mapPredeformationCategory_of_isVersalAt B S hS p x
    iΛ x₀ hx₀ 𝒳.isFiberedInGroupoids hU u₀ hu₀ hfield (hversal u₀ hu₀) hRS
  exact (Deformation.Artin.isSmooth_mapPredeformationCategory_iff_liftsAtResiduePoint
    B S hS p x iΛ x₀ hx₀ 𝒳.isFiberedInGroupoids
    (Functor.TwoYoneda.choiceOfPullbacks p 𝒳.isFiberedInGroupoids)).mpr
    ((Deformation.Artin.isSmooth_mapPredeformationCategory_iff_liftsAtResiduePoint
      B S hS p x iΛ x₀ hx₀ 𝒳.isFiberedInGroupoids p.chosenPullbacks).mp h07XG)

end AlgebraicGeometry.Stack

end
