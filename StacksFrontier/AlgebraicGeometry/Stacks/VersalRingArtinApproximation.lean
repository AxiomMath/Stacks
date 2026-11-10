module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.CodimensionOneObstruction.CompletedLocalSpectrum
public import StacksFrontier.AlgebraicGeometry.Stacks.ClosedSubsetSeparationAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.FinitePresentationNoetherian
public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingOfFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingStructureMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingStructureMorphismDescent
public import StacksFrontier.AlgebraicGeometry.Stacks.LisseEtaleSite
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalPropertyAtlasScheme
public import StacksFrontier.AlgebraicGeometry.Stacks.VersalChartSmoothBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.VersalChartSmoothNeighbourhood
public import StacksFrontier.AlgebraicGeometry.Stacks.VersalRingMorphism
public import StacksFrontier.AlgebraicGeometry.Variety.CompleteLocal.Stalk
public import StacksFrontier.Deformation.Artin.FormalObject.ApproximationEssSurj
public import StacksFrontier.Deformation.Artin.FormalObject.BaseContains
public import StacksFrontier.Deformation.Artin.FormalObject.RealizationVersality
public import StacksFrontier.RingTheory.AdicCompletion.PermanenceOfProperties

/-!
# A versal ring is the completion of a smooth chart over a G-ring (Stacks 0DR0)

In the versal situation of **Stacks 0DQU** — an algebraic stack `𝒳` locally of finite type over a
locally Noetherian scheme `S` — let `x₀ : Spec k ⟶ 𝒳` be a point with `Spec k ⟶ S` of finite type
and image `s`, and let `A` be a versal ring to `𝒳` at `x₀`. **Stacks 0DR0**: if `𝒪_{S,s}` is a
G-ring, there are a smooth morphism `U ⟶ 𝒳` from a scheme and a point `u₀ ∈ U` with residue field
`k` such that `Spec k ⟶ U ⟶ 𝒳` is `x₀` and `𝒪^∧_{U,u₀} ≅ A`. Part (4) of **Stacks 0DR1** adds
that the isomorphism can be chosen so that the morphism `Spec A ⟶ 𝒳` of the remark is
`Spec A ≅ Spec 𝒪^∧_{U,u₀} ⟶ U ⟶ 𝒳`.

The proof is the source's: the versal formal object over `A` comes from a morphism
`Spec A ⟶ 𝒳` (a realization, `Deformation.Artin.FormalObject.Realization`), so Artin
approximation (**Stacks 07XH**) produces a chart `U ⟶ 𝒳` versal at a point `u₀` with the same
formal object, which is smooth after shrinking (**Stacks 0DQZ**). The comparison of the realizing
object with the chart is the preimage of an isomorphism of formal objects under the fully faithful
approximation functor (**Stacks 07X8**), and the residue field and completed local ring of `u₀`
are read off it.

## Main results

* `AlgebraicGeometry.Stack.isLimitPreservingOnObjects_structureMorphism`: the structure morphism of
  `𝒳` is limit preserving on objects (Stacks 0DQJ and 0CMY), the input of Artin approximation.
* `AlgebraicGeometry.Stack.exists_smoothObject_hom_of_isVersalAt`: a chart versal at a finite
  type point restricts to a smooth object over an open neighbourhood of it (Stacks 0DQZ).
* `AlgebraicGeometry.Stack.exists_smoothObject_completedLocalRing_realization`: **Stacks 0DR1**,
  part (4), with the conclusions of Stacks 0DR0, for a realized versal formal object.
* `AlgebraicGeometry.Stack.exists_realization_of_predeformationFormalObject`: **Stacks 0DR1**, the
  preamble: the versal formal object comes from a morphism `Spec A ⟶ 𝒳`.
* `AlgebraicGeometry.Stack.exists_smoothObject_completedLocalRing_equiv_versalRing`:
  **Stacks 0DR0**.

## References

* [Stacks Project, Tag 0CMY](https://stacks.math.columbia.edu/tag/0CMY)
* [Stacks Project, Tag 0DQJ](https://stacks.math.columbia.edu/tag/0DQJ)
* [Stacks Project, Tag 0DQZ](https://stacks.math.columbia.edu/tag/0DQZ)
* [Stacks Project, Tag 0DR0](https://stacks.math.columbia.edu/tag/0DR0)
* [Stacks Project, Tag 0DR1](https://stacks.math.columbia.edu/tag/0DR1)
* [Stacks Project, Tag 07X8](https://stacks.math.columbia.edu/tag/07X8)
* [Stacks Project, Tag 07XH](https://stacks.math.columbia.edu/tag/07XH)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing

namespace Deformation.Artin

universe u v w

/-! ### The residue point of a realizing object -/

section ResiduePoint

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k] {S : Scheme.{u}}
  (iΛ : Spec (.of Λ) ⟶ S)

/-- The residue map of a complete local `Λ`-algebra with residue field `k` is surjective. -/
theorem completeResidueMap_surjective (A : CompleteLocalAlgCat.{u, u, u} Λ k) :
    Function.Surjective (completeResidueMap A) :=
  A.residueEquiv.surjective.comp residue_surjective

/-- The residue map of a complete local `Λ`-algebra with residue field `k` is compatible with the
structure maps from `Λ`. -/
theorem completeResidueMap_comp_algebraMap (A : CompleteLocalAlgCat.{u, u, u} Λ k) :
    (completeResidueMap A).comp (algebraMap Λ A) = algebraMap Λ k := by
  ext a
  exact A.residueEquiv.commutes a

/-- **The closed point of a complete local `Λ`-algebra lies over the image of `Spec k`.** The
structure morphism `Spec A ⟶ Spec Λ ⟶ S` of a complete local `Λ`-algebra with residue field `k`
sends the closed point to the image of the point `Spec k ⟶ Spec Λ ⟶ S`. -/
theorem completeLocalAlgFormalBase_toS_closedPoint
    (hfinite : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) ∧
      QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (A : CompleteLocalAlgCat.{u, u, u} Λ k) :
    (completeLocalAlgFormalBase iΛ hfinite A).toS (closedPoint A) =
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) (closedPoint k) := by
  have : IsLocalHom (completeResidueMap A) :=
    IsLocalHom.of_surjective _ (completeResidueMap_surjective A)
  have hpt : (Spec.map (CommRingCat.ofHom (completeResidueMap A))) (closedPoint k) =
      closedPoint A :=
    IsLocalRing.comap_closedPoint (completeResidueMap A)
  have heq : Spec.map (CommRingCat.ofHom (completeResidueMap A)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ iΛ =
        Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ := by
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      completeResidueMap_comp_algebraMap]
  change (Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ iΛ) (closedPoint A) = _
  rw [← hpt]
  exact (Scheme.Hom.comp_apply _ _ _).symm.trans (congrArg (fun g => g (closedPoint k)) heq)

end ResiduePoint

section RealizationResiduePoint

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {F : Type v} [Category.{w} F] (p : F ⥤ BigFppfOver B S hS)

/-- **The residue point of a realization.** Let `y` realize the formal object over the site of a
formal object `ξ` of the predeformation category of `x₀` over `𝒞_Λ`. The arrow
`x₀ ⟶ ξ_0 ⟶ y`, from the point to its first level followed by the realization, lies over the
point `Spec k ⟶ Spec A` of the residue map of the base `A` of `ξ`. -/
theorem schemeMap_closedPointArrow_realization
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    (iΛ : Spec (.of Λ) ⟶ S) {x₀ : F}
    (hx₀ : (p ⋙ Over.post B.inclusion).obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hfinite : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) ∧
      QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (ξ : Deformation.FormalObject
      (predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀).projection)
    {hA : B.Contains (Spec (.of ξ.base))} {y : F}
    {hy : p.obj y = baseOver B S hS (completeLocalAlgFormalBase iΛ hfinite ξ.base) hA}
    (R : (FormalObject.ofPredeformation B S hS iΛ p x₀ hx₀ hfinite ξ).Realization hA y hy) :
    schemeMap (p ⋙ Over.post B.inclusion) hx₀
        (show (p ⋙ Over.post B.inclusion).obj y =
            Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ ξ.base)) ≫ iΛ) from
          congrArg (Over.post B.inclusion).obj hy)
        (((predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀).objects
          (ξ.level 0)).arrow ≫ R.r 0) =
      Spec.map (CommRingCat.ofHom (completeResidueMap ξ.base)) := by
  have qY : (p ⋙ Over.post B.inclusion).obj y =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ ξ.base)) ≫ iΛ) :=
    congrArg (Over.post B.inclusion).obj hy
  let C := predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀
  let := C.category
  have hb0 := deformationPointBase C (ξ.level 0) (AdicTruncation.obj ξ.base 0) (ξ.level_eq 0)
  have hbase0 : eqToHom (congrArg Over.left hb0).symm ≫
      ((p ⋙ Over.post B.inclusion).map (R.r 0)).left ≫ eqToHom (congrArg Over.left qY) =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (AdicTruncation.ideal ξ.base 0))) := by
    change eqToHom _ ≫ (p.map (R.r 0)).left.hom ≫ eqToHom _ = _
    rw [R.map_eq 0, bigFppfOver_left_hom_eqToHom]
    exact eqToHom_comp_comp_eqToHom_of_heq _ _ _ _ _ _
      (adicThickeningι_heq_specMap_truncation ξ.base 0)
  refine (schemeMap_comp _ hx₀ hb0 qY _ _).trans ?_
  refine (congrArg (· ≫ _) (DeformationObject.schemeMap_arrow S
    (C.objects (ξ.level 0)) ((C.object_projection _).symm.trans (ξ.level_eq 0)) hb0)).trans ?_
  refine (congrArg (_ ≫ ·) hbase0).trans ?_
  refine (Spec.map_comp (CommRingCat.ofHom (Ideal.Quotient.mk (AdicTruncation.ideal ξ.base 0)))
    (CommRingCat.ofHom (residueMap (AdicTruncation.obj ξ.base 0)))).symm.trans ?_
  congr 1
  ext a
  exact AdicTruncation.residueEquiv_residue_mk ξ.base 0 a

end RealizationResiduePoint

end Deformation.Artin

namespace AlgebraicGeometry.Scheme

universe u

/-- **Completed local rings along a morphism inducing an isomorphism of local rings.** If
`f : X ⟶ Y` induces an isomorphism `𝒪_{Y, f(x)} ≅ 𝒪_{X, x}`, there is an isomorphism
`c : 𝒪^∧_{X, x} ≅ 𝒪^∧_{Y, f(x)}` of completions for which the canonical morphism
`Spec 𝒪^∧_{Y, f(x)} ⟶ Y` is `Spec c` followed by `Spec 𝒪^∧_{X, x} ⟶ X ⟶ Y`. -/
theorem exists_fromSpecCompletedLocalRing_eq_of_isIso_stalkMap {X Y : Scheme.{u}}
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (f : X ⟶ Y) (x : X)
    [IsIso (f.stalkMap x)] :
    ∃ c : X.completedLocalRing x ≃+* Y.completedLocalRing (f x),
      Y.fromSpecCompletedLocalRing (f x) =
        Spec.map (CommRingCat.ofHom c.toRingHom) ≫ X.fromSpecCompletedLocalRing x ≫ f := by
  let A := Y.presheaf.stalk (f x)
  let B := X.presheaf.stalk x
  let φ : A ≃+* B := (asIso (f.stalkMap x)).commRingCatIsoToRingEquiv
  let : Algebra A B := φ.toRingHom.toAlgebra
  let eL : A ≃ₗ[A] B :=
    { toFun := φ
      invFun := φ.symm
      left_inv := φ.symm_apply_apply
      right_inv := φ.apply_symm_apply
      map_add' := φ.map_add
      map_smul' := φ.map_mul }
  let : Module.Free A B := Module.Free.of_equiv' (inferInstance : Module.Free A A) eL
  let : Module.Flat A B := Module.Flat.of_free
  let : IsLocalHom (algebraMap A B) := IsLocalHom.of_surjective _ φ.surjective
  have hmax : (IsLocalRing.maximalIdeal A).map (algebraMap A B) =
      IsLocalRing.maximalIdeal B :=
    IsLocalRing.map_ringEquiv_maximalIdeal φ
  have hres : Function.Bijective (IsLocalRing.ResidueField.map (algebraMap A B)) :=
    (IsLocalRing.ResidueField.mapEquiv φ).bijective
  obtain ⟨c', hc'⟩ := exists_adicCompletion_ringEquiv_of_flat
    (IsLocalRing.maximalIdeal A).fg_of_isNoetherianRing hmax hres
  refine ⟨c'.symm, ?_⟩
  have hring : CommRingCat.ofHom c'.toRingHom ≫ CommRingCat.ofHom c'.symm.toRingHom = 𝟙 _ :=
    CommRingCat.hom_ext (RingHom.ext fun a => c'.symm_apply_apply a)
  have hcomp : Y.toCompletedLocalRing (f x) ≫ CommRingCat.ofHom c'.toRingHom =
      f.stalkMap x ≫ X.toCompletedLocalRing x :=
    CommRingCat.hom_ext (RingHom.ext fun a => hc' a)
  calc Y.fromSpecCompletedLocalRing (f x)
      = Spec.map (CommRingCat.ofHom c'.symm.toRingHom) ≫
          Spec.map (CommRingCat.ofHom c'.toRingHom) ≫ Y.fromSpecCompletedLocalRing (f x) := by
        rw [← Category.assoc, ← Spec.map_comp, hring, Spec.map_id, Category.id_comp]
    _ = _ := by
        congr 1
        rw [fromSpecCompletedLocalRing, ← Category.assoc, ← Spec.map_comp, hcomp, Spec.map_comp,
          Category.assoc, Scheme.SpecMap_stalkMap_fromSpecStalk, fromSpecCompletedLocalRing,
          Category.assoc]

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Stack

universe u w

/-! ### Shrinking a versal chart to a smooth one -/

section Shrink

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A restriction of a smooth composite is a smooth object.** If `ρ : x' ⟶ x` lies over
`g : U' ⟶ U` and the composite `(Sch/U') ⟶ (Sch/U) ⟶ 𝒳` of `g` with `x` is smooth, then `x'` is a
smooth object of `𝒳`: the 1-morphism it names is 2-isomorphic to that composite. -/
theorem smoothObject_of_isHomLift_of_isRelativelySmooth (𝒳 : AlgebraicStacks.{u, w} B S hS)
    {U U' : BigFppfOver B S hS} (x : 𝒳.val.val.p.Fiber U) (x' : 𝒳.val.val.p.Fiber U')
    (g : U' ⟶ U) (ρ : x'.1 ⟶ x.1) (hρ : 𝒳.val.val.p.IsHomLift g ρ)
    (h : IsRelativelySmooth B S hS
      (schemeFibredCategoryMap B S hS g ≫ objectMorphism B S hS 𝒳.val x)) :
    smoothObject.{u, w} B S hS 𝒳 x'.1 := by
  obtain ⟨e⟩ := nonempty_objectMorphism_iso_of_isHomLift B S hS 𝒳.val x x' g ρ hρ
  obtain ⟨y, rfl⟩ := x'
  exact isSmooth_of_isRelativelySmooth B S hS _
    (isRelativelySmooth_congr_twoIso B S hS e.symm h)

/-- The inclusion of an open, read through an identification of its source, is an open immersion
with image that open. -/
theorem isOpenImmersion_and_range_post_eqToHom_openSubHom {W : BigFppfOver B S hS}
    (T : BigFppfOver B S hS) (V : T.left.obj.Opens) (h : W = BigFppfOver.openSubObj B S hS T V)
    (φ : W ⟶ T) (hφ : φ = eqToHom h ≫ BigFppfOver.openSubHom B S hS T V) :
    _root_.AlgebraicGeometry.IsOpenImmersion ((Over.post B.inclusion).map φ).left ∧
      Set.range ((Over.post B.inclusion).map φ).left = (V : Set T.left.obj) := by
  subst h hφ
  simp only [eqToHom_refl, Category.id_comp]
  exact ⟨inferInstanceAs (_root_.AlgebraicGeometry.IsOpenImmersion V.ι), V.range_ι⟩

end Shrink

/-- **A versal chart is smooth near the point (Stacks 0DQZ, (1) ⟹ (4)), as an arrow of `𝒳`.** In
the versal situation, if `x` over a scheme locally of finite type over `S` is versal at a finite
type point `u₀`, there is an arrow `ρ : x' ⟶ x` from a smooth object of `𝒳`, lying over an open
immersion whose image contains `u₀`. -/
theorem exists_smoothObject_hom_of_isVersalAt (D : VersalSituation.{u, w})
    (x : D.𝒳.val.val.obj)
    [LocallyOfFiniteType ((D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x).hom]
    (u₀ : ((D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x).left)
    (hu₀ : AlgebraicGeometry.IsFiniteTypePoint u₀)
    (hv : Deformation.Artin.IsVersalAt ((D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x)
      (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion) u₀ x rfl) :
    ∃ (x' : D.𝒳.val.val.obj) (ρ : x' ⟶ x),
      smoothObject.{u, w} D.B D.S D.hS D.𝒳 x' ∧
        _root_.AlgebraicGeometry.IsOpenImmersion
          ((D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).map ρ).left ∧
        u₀ ∈ Set.range ((D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).map ρ).left := by
  obtain ⟨V, hu, hsm⟩ := (isVersalAt_iff_exists_isRelativelySmooth_restrict D x u₀ hu₀).mp hv
  let g := BigFppfOver.openSubHom D.B D.S D.hS (D.𝒳.val.val.p.obj x) V
  let c := Functor.TwoYoneda.choiceOfPullbacks D.𝒳.val.val.p D.𝒳.val.isFiberedInGroupoids
  let xf : D.𝒳.val.val.p.Fiber (D.𝒳.val.val.p.obj x) := Functor.Fiber.mk (a := x) rfl
  have hρ : D.𝒳.val.val.p.IsHomLift g (c.map g xf) := (c.isStronglyCartesian g xf).toIsHomLift
  refine ⟨(c.obj g xf).1, c.map g xf,
    smoothObject_of_isHomLift_of_isRelativelySmooth D.B D.S D.hS D.𝒳 xf (c.obj g xf) g
      (c.map g xf) hρ hsm, ?_⟩
  have hmap : D.𝒳.val.val.p.map (c.map g xf) = eqToHom (c.obj g xf).2 ≫ g := by
    refine (IsHomLift.fac' D.𝒳.val.val.p g (c.map g xf)).trans ?_
    congr 1
  obtain ⟨hoi, hr⟩ := isOpenImmersion_and_range_post_eqToHom_openSubHom D.B D.S D.hS
    (D.𝒳.val.val.p.obj x) V (c.obj g xf).2 _ hmap
  exact ⟨hoi, hr ▸ hu⟩

/-- **Lifting an arrow of `𝒳` through an arrow over a factorization.** In a category fibred in
groupoids over the big fppf site, let `ρ : x' ⟶ x` and `m₀ : z ⟶ x` be arrows and let `t` be a
morphism of schemes from the scheme under `z` to the one under `x'` with `t` followed by the
morphism under `ρ` the morphism under `m₀`. Then `m₀` factors as `m ≫ ρ` with `m` over `t`. -/
theorem exists_hom_comp_eq_of_schemeMap_factor {B : BigFppfSite.{u}} {S : Scheme.{u}}
    {hS : B.Contains S} {F : Type*} [Category F] {p : F ⥤ BigFppfOver B S hS}
    (hp : p.IsFiberedInGroupoids) {z x x' : F} (ρ : x' ⟶ x) (m₀ : z ⟶ x)
    (t : ((p ⋙ Over.post B.inclusion).obj z).left ⟶ ((p ⋙ Over.post B.inclusion).obj x').left)
    (ht : t ≫ ((p ⋙ Over.post B.inclusion).map ρ).left =
      ((p ⋙ Over.post B.inclusion).map m₀).left) :
    ∃ m : z ⟶ x', m ≫ ρ = m₀ ∧ ((p ⋙ Over.post B.inclusion).map m).left = t := by
  have hw : t ≫ ((p ⋙ Over.post B.inclusion).obj x').hom =
      ((p ⋙ Over.post B.inclusion).obj z).hom := by
    rw [← Over.w ((p ⋙ Over.post B.inclusion).map ρ), ← Category.assoc, ht,
      Over.w ((p ⋙ Over.post B.inclusion).map m₀)]
  let f : p.obj z ⟶ p.obj x' :=
    Over.homMk (ObjectProperty.homMk t) (by
      apply ObjectProperty.hom_ext
      exact hw)
  have hf : f ≫ p.map ρ = p.map m₀ := by
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    exact ht
  obtain ⟨m, ⟨hm₁, hm₂⟩, -⟩ := hp.unique_lift ρ m₀ f hf
  refine ⟨m, hm₂, ?_⟩
  rw [Functor.comp_map, hm₁]
  rfl

/-- **In the versal situation the structure morphism is limit preserving on objects.** It is
locally of finite type over a locally Noetherian base, hence locally of finite presentation
(**Stacks 0DQJ**), hence limit preserving on objects (**Stacks 0CMY**); read through Artin's
Axioms, Definition 07XL, this is the hypothesis of Artin approximation, **Stacks 07XH**. -/
theorem isLimitPreservingOnObjects_structureMorphism (D : VersalSituation.{u, w}) :
    BigFppfOver.IsLimitPreservingOnObjects.{u, u, u, u, u + 1} D.B D.S D.hS D.𝒳.val
      (Deformation.Artin.Approximation.baseFiberedCategory D.B D.S D.hS)
      (Deformation.Artin.Approximation.structureMorphism D.B D.S D.hS D.𝒳.val) := by
  let : ObjectProperty.IsLocal (fun T : Scheme.{u} => IsLocallyNoetherian T)
      (Scheme.precoverage (@Smooth : MorphismProperty Scheme.{u})) :=
    ObjectProperty.IsLocal.of_le Scheme.smoothPrecoverage_le_fppfPrecoverage
  have hY : HasPropertyOnSomeSchemeAtlas D.B D.S D.hS
      (fun T : Scheme.{u} => IsLocallyNoetherian T)
      (schemeStack.{u, w} D.B D.S D.hS (Over.mk (𝟙 (D.B.obj D.hS)))) :=
    (exists_scheme_atlas_iff_scheme D.B D.S D.hS _ _).mpr D.locallyNoetherian
  have hlfp := AlgebraicStacks.isLocallyOfFinitePresentation_of_isLocallyOfFiniteType D.B D.S D.hS
    (structureMorphism D.B D.S D.hS D.𝒳) hY D.locallyFiniteType
  have hobj := AlgebraicStacks.isLimitPreservingOnObjects_of_isLocallyOfFinitePresentation
    D.B D.S D.hS (structureMorphism D.B D.S D.hS D.𝒳) hlfp
  have hart := AlgebraicStacks.isLimitPreserving_artin_of_structureMorphism D.B D.S D.hS D.𝒳
    hobj D.locallyFiniteType
  exact isLimitPreservingOnObjects_toTerminalCFG_of_isLimitPreserving D.B D.S D.hS D.𝒳.val hart

/-! ### Artin approximation of a realized versal formal object -/

/-- The morphism of schemes under an arrow between objects with their own structure morphisms is
the underlying morphism of the arrow. -/
private theorem schemeMap_rfl_rfl {S : Scheme.{u}} {F : Type*} [Category F] (q : F ⥤ Over S)
    {x y : F} (f : x ⟶ y) :
    (Deformation.Artin.schemeMap q rfl rfl f : (q.obj x).left ⟶ (q.obj y).left) =
      (q.map f).left := by
  simp [Deformation.Artin.schemeMap]

/-- The morphism of schemes under an arrow out of an object over a prescribed object of the site
is the underlying morphism of the arrow precomposed with the identification. -/
theorem schemeMap_post_eq_left_hom {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {F : Type*} [Category F] {p : F ⥤ BigFppfOver B S hS} {z x : F} {W : BigFppfOver B S hS}
    (h : p.obj z = W) (f : z ⟶ x) :
    Deformation.Artin.schemeMap (p ⋙ Over.post B.inclusion)
        (congrArg (Over.post B.inclusion).obj h) rfl f =
      (eqToHom h.symm ≫ p.map f).left.hom := by
  subst h
  rw [schemeMap_rfl_rfl]
  simp only [Functor.comp_map, Over.post_map, ObjectProperty.ι_map, Over.homMk_left,
    eqToHom_refl, Category.id_comp]


/-- The residue field map of a local homomorphism from the local ring at a point to a complete
local `Λ`-algebra with residue field `k`, through its completion, is bijective. -/
theorem bijective_lift_completedLocalRing {X : Scheme.{u}} [IsLocallyNoetherian X] (x : X)
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    (A : Deformation.CompleteLocalAlgCat.{u, u, u} Λ k) (eA : X.completedLocalRing x ≃+* A)
    [IsLocalHom ((Deformation.Artin.completeResidueMap A).comp
      (eA.toRingHom.comp (algebraMap (X.presheaf.stalk x) (X.completedLocalRing x))))] :
    Function.Bijective (ResidueField.lift ((Deformation.Artin.completeResidueMap A).comp
      (eA.toRingHom.comp (algebraMap (X.presheaf.stalk x) (X.completedLocalRing x))))) := by
  have := X.completedLocalRing_isLocal x
  convert A.residueEquiv.bijective.comp ((ResidueField.mapEquiv eA).bijective.comp
    (X.completedLocalRing_residueFieldMap_bijective x)) using 1
  ext z
  obtain ⟨a, rfl⟩ := residue_surjective z
  rfl

/-- A morphism of schemes under an arrow, read through an identification of its source. -/
theorem schemeMap_eq_of_left_eq {S : Scheme.{u}} {F : Type*} [Category F] (q : F ⥤ Over S)
    {z x : F} {Z : Over S} (hz : q.obj z = Z) (f : z ⟶ x) (g : Z.left ⟶ (q.obj x).left)
    (h : (q.map f).left = eqToHom (congrArg Over.left hz) ≫ g) :
    Deformation.Artin.schemeMap q hz rfl f = g := by
  subst hz
  simpa [Deformation.Artin.schemeMap] using h

/-- The converse of `AlgebraicGeometry.Stack.schemeMap_eq_of_left_eq`. -/
theorem left_eq_of_schemeMap_eq {S : Scheme.{u}} {F : Type*} [Category F] (q : F ⥤ Over S)
    {z x : F} {Z : Over S} (hz : q.obj z = Z) (f : z ⟶ x) (g : Z.left ⟶ (q.obj x).left)
    (h : Deformation.Artin.schemeMap q hz rfl f = g) :
    (q.map f).left = eqToHom (congrArg Over.left hz) ≫ g := by
  subst hz
  simpa [Deformation.Artin.schemeMap] using h

/-- **The residue point through a completion.** For an isomorphism `eA : 𝒪^∧_{X, x} ≅ A` onto a
complete local `Λ`-algebra with residue field `k`, the point
`Spec k ⟶ Spec A ⟶ Spec 𝒪^∧_{X, x} ⟶ X` is `Spec k ≅ Spec κ(x) ⟶ X` for the isomorphism `κ(x) ≅ k`
induced by the residue map. -/
theorem specMap_completeResidueMap_comp_fromSpecCompletedLocalRing {X : Scheme.{u}}
    [IsLocallyNoetherian X] (x : X) {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    (A : Deformation.CompleteLocalAlgCat.{u, u, u} Λ k) (eA : X.completedLocalRing x ≃+* A)
    [hloc : IsLocalHom ((Deformation.Artin.completeResidueMap A).comp
      (eA.toRingHom.comp (algebraMap (X.presheaf.stalk x) (X.completedLocalRing x))))]
    (e : X.residueField x ≃+* k)
    (he : ∀ t, e (X.residue x t) = Deformation.Artin.completeResidueMap A
      (eA (algebraMap (X.presheaf.stalk x) (X.completedLocalRing x) t))) :
    Spec.map (CommRingCat.ofHom (Deformation.Artin.completeResidueMap A)) ≫
        Spec.map (CommRingCat.ofHom eA.toRingHom) ≫ X.fromSpecCompletedLocalRing x =
      Spec.map (CommRingCat.ofHom e.toRingHom) ≫ X.fromSpecResidueField x := by
  let ψ : X.presheaf.stalk x ⟶ CommRingCat.of k := CommRingCat.ofHom
    ((Deformation.Artin.completeResidueMap A).comp
      (eA.toRingHom.comp (algebraMap (X.presheaf.stalk x) (X.completedLocalRing x))))
  have : IsLocalHom ψ.hom := hloc
  have h1 : CommRingCat.ofHom e.toRingHom = X.descResidueField ψ := by
    ext t
    obtain ⟨t, rfl⟩ := residue_surjective t
    exact he t
  have h2 : ψ = X.toCompletedLocalRing x ≫ CommRingCat.ofHom eA.toRingHom ≫
      CommRingCat.ofHom (Deformation.Artin.completeResidueMap A) := rfl
  rw [h1, Scheme.descResidueField_fromSpecResidueField, h2, Spec.map_comp, Spec.map_comp,
    Category.assoc, Category.assoc]
  rfl

/-- The morphism of schemes under an isomorphism of `𝒳` is an isomorphism. -/
theorem isIso_schemeMap {S : Scheme.{u}} {F : Type*} [Category F] (q : F ⥤ Over S)
    {y z : F} {Y Z : Over S} (hy : q.obj y = Y) (hz : q.obj z = Z) (f : y ⟶ z) [IsIso f] :
    IsIso (Deformation.Artin.schemeMap q hy hz f) := by
  subst hy hz
  rw [schemeMap_rfl_rfl]
  exact inferInstanceAs (IsIso ((Over.forget S).map (q.map f)))

/-- **Lifting a restriction to a completion through an open immersion.** In a category fibred
in groupoids over the big fppf site, let `ρ : x' ⟶ x` lie over an open immersion `U' ⟶ U` of
locally Noetherian schemes sending `u₀'` to `u₀`, and let `r : z ⟶ x` lie over
`g ≫ (Spec 𝒪^∧_{U, u₀} ⟶ U)`. Then `r` factors through `ρ` by an arrow lying over
`g ≫ Spec c ≫ (Spec 𝒪^∧_{U', u₀'} ⟶ U')` for an isomorphism `c : 𝒪^∧_{U', u₀'} ≅ 𝒪^∧_{U, u₀}`. -/
theorem exists_hom_fromSpecCompletedLocalRing_of_isOpenImmersion {B : BigFppfSite.{u}}
    {S : Scheme.{u}} {hS : B.Contains S} {F : Type*} [Category F] {p : F ⥤ BigFppfOver B S hS}
    (hp : p.IsFiberedInGroupoids) {z x x' : F} (ρ : x' ⟶ x)
    [IsLocallyNoetherian ((p ⋙ Over.post B.inclusion).obj x).left]
    [IsLocallyNoetherian ((p ⋙ Over.post B.inclusion).obj x').left]
    [_root_.AlgebraicGeometry.IsOpenImmersion ((p ⋙ Over.post B.inclusion).map ρ).left]
    (u₀' : ((p ⋙ Over.post B.inclusion).obj x').left)
    {u₀ : ((p ⋙ Over.post B.inclusion).obj x).left}
    (hu : ((p ⋙ Over.post B.inclusion).map ρ).left u₀' = u₀)
    {Z : Over S} (hz : (p ⋙ Over.post B.inclusion).obj z = Z) (r : z ⟶ x)
    (g : Z.left ⟶ Spec (((p ⋙ Over.post B.inclusion).obj x).left.completedLocalRingCat u₀))
    (hr : Deformation.Artin.schemeMap (p ⋙ Over.post B.inclusion) hz rfl r =
      g ≫ ((p ⋙ Over.post B.inclusion).obj x).left.fromSpecCompletedLocalRing u₀) :
    ∃ (r' : z ⟶ x') (c : ((p ⋙ Over.post B.inclusion).obj x').left.completedLocalRing u₀' ≃+*
        ((p ⋙ Over.post B.inclusion).obj x).left.completedLocalRing u₀),
      Deformation.Artin.schemeMap (p ⋙ Over.post B.inclusion) hz rfl r' =
        g ≫ Spec.map (CommRingCat.ofHom c.toRingHom) ≫
          ((p ⋙ Over.post B.inclusion).obj x').left.fromSpecCompletedLocalRing u₀' := by
  subst hu hz
  obtain ⟨c, hc⟩ := Scheme.exists_fromSpecCompletedLocalRing_eq_of_isIso_stalkMap
    ((p ⋙ Over.post B.inclusion).map ρ).left u₀'
  simp only [schemeMap_rfl_rfl] at hr ⊢
  obtain ⟨r', -, hr'⟩ := exists_hom_comp_eq_of_schemeMap_factor hp ρ r
    (g ≫ Spec.map (CommRingCat.ofHom c.toRingHom) ≫
      ((p ⋙ Over.post B.inclusion).obj x').left.fromSpecCompletedLocalRing u₀')
    (by rw [hr, hc]; simp only [Category.assoc])
  exact ⟨r', c, hr'⟩

/-- A local homomorphism from the local ring at a point to the residue field of a complete local
`Λ`-algebra through an isomorphism with the completion. -/
private theorem isLocalHom_completeResidueMap_comp_toCompletedLocalRing {X : Scheme.{u}}
    [IsLocallyNoetherian X] (x : X) {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    (A : Deformation.CompleteLocalAlgCat.{u, u, u} Λ k) (eA : X.completedLocalRing x ≃+* A) :
    IsLocalHom ((Deformation.Artin.completeResidueMap A).comp
      (eA.toRingHom.comp (algebraMap (X.presheaf.stalk x) (X.completedLocalRing x)))) := by
  have := X.completedLocalRing_isLocal x
  have : IsLocalHom (algebraMap (X.presheaf.stalk x) (X.completedLocalRing x)) :=
    Scheme.isLocalHom_toCompletedLocalRing (X := X) x
  have : IsLocalHom eA.toRingHom := IsLocalHom.of_surjective _ eA.surjective
  have : IsLocalHom (Deformation.Artin.completeResidueMap A) :=
    IsLocalHom.of_surjective _ (Deformation.Artin.completeResidueMap_surjective A)
  have : IsLocalHom (eA.toRingHom.comp
      (algebraMap (X.presheaf.stalk x) (X.completedLocalRing x))) :=
    RingHom.isLocalHom_comp _ _
  exact RingHom.isLocalHom_comp _ _

/-- **Artin approximation of a realized versal formal object.** In the setting of
`AlgebraicGeometry.Stack.exists_smoothObject_completedLocalRing_realization`, there are an object
`x` over a scheme `U` locally of finite type over `S` versal at a finite type point `u₀ ∈ U`, an
isomorphism `m : y ⟶ z` onto an object over an affine scheme `Spec R`, and an arrow `z ⟶ x` over
`Spec R ≅ Spec 𝒪^∧_{U, u₀} ⟶ U`. -/
private theorem exists_isVersalAt_hom_schemeMap_eq_of_realization (D : VersalSituation.{u, w})
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    (iΛ : Spec (.of Λ) ⟶ D.S) (hiΛ : _root_.AlgebraicGeometry.IsOpenImmersion iΛ)
    (x₀ : D.𝒳.val.val.obj)
    (hx₀ : (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hfinite : LocallyOfFiniteType
        (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) ∧
      QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (ξ : Deformation.FormalObject (Deformation.Artin.predeformationCategory iΛ
      (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion) x₀ hx₀).projection)
    (hξ : Deformation.IsVersal (Deformation.Artin.predeformationCategory_isPredeformationCategory
      D.B D.hS iΛ D.𝒳.val.val.p x₀ hx₀ D.𝒳.val.property).cofibered ξ)
    (s : D.S) (hs : (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) (closedPoint k) = s)
    (hG : IsGRing (D.S.presheaf.stalk s))
    {hA : D.B.Contains (Spec (.of ξ.base))} {y : D.𝒳.val.val.obj}
    {hy : D.𝒳.val.val.p.obj y = Deformation.Artin.baseOver D.B D.S D.hS
      (Deformation.Artin.completeLocalAlgFormalBase iΛ hfinite ξ.base) hA}
    (Ry : (Deformation.Artin.FormalObject.ofPredeformation D.B D.S D.hS iΛ D.𝒳.val.val.p x₀ hx₀
      hfinite ξ).Realization hA y hy) :
    ∃ (x : D.𝒳.val.val.obj)
      (_ : LocallyOfFiniteType ((D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x).hom)
      (_ : IsLocallyNoetherian ((D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x).left)
      (u₀ : ((D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x).left),
      AlgebraicGeometry.IsFiniteTypePoint u₀ ∧
      Deformation.Artin.IsVersalAt ((D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x)
        (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion) u₀ x rfl ∧
      ∃ (z : D.𝒳.val.val.obj) (R : Type u) (_ : CommRing R)
        (fZ : Spec (.of R) ⟶ D.B.inclusion.obj (D.B.obj D.hS))
        (hz : (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj z = Over.mk fZ) (m : y ⟶ z) (r : z ⟶ x)
        (eR : ((D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x).left.completedLocalRing u₀ ≃+* R),
        IsIso m ∧ Deformation.Artin.schemeMap (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion) hz rfl r =
          Spec.map (CommRingCat.ofHom eR.toRingHom) ≫
            ((D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x).left.fromSpecCompletedLocalRing
              u₀ := by
  classical
  have := hiΛ
  have : IsLocallyNoetherian (D.B.inclusion.obj (D.B.obj D.hS)) :=
    inferInstanceAs (IsLocallyNoetherian D.S)
  let hp := D.𝒳.val.property
  set ζ := Deformation.Artin.FormalObject.ofPredeformation D.B D.S D.hS iΛ D.𝒳.val.val.p x₀ hx₀
    hfinite ξ with hζ
  have heff := Deformation.Artin.FormalObject.isEffective_of_realization hp Ry
  have hs' : ζ.base.toS (closedPoint ζ.base.R) = s :=
    (Deformation.Artin.completeLocalAlgFormalBase_toS_closedPoint iΛ hfinite ξ.base).trans hs
  subst hs'
  let algA : Algebra (D.S.presheaf.stalk (ζ.base.toS (closedPoint ζ.base.R))) ζ.base.R :=
    (Scheme.stalkClosedPointTo ζ.base.toS).hom.toAlgebra
  have hΛ : Spec.map (CommRingCat.ofHom (algebraMap
      (D.S.presheaf.stalk (ζ.base.toS (closedPoint ζ.base.R))) ζ.base.R)) ≫
      D.S.fromSpecStalk (ζ.base.toS (closedPoint ζ.base.R)) = ζ.base.toS :=
    Scheme.Spec_stalkClosedPointTo_fromSpecStalk ζ.base.toS
  have hversal := Deformation.Artin.isVersal_stalk_ofPredeformation_of_realization D.B D.S D.hS
    D.𝒳.val.val.p hp iΛ hx₀ hfinite ξ hξ Ry (ζ.base.toS (closedPoint ζ.base.R)) rfl (algA := algA)
    hΛ
  obtain ⟨U, u₀, V, -, xU, hx, hlft, -, hu₀, -, hvers, xR, e, r, eR, -, hrbase⟩ :=
    Deformation.Artin.exists_finiteType_versal_approximation D.B D.S D.hS D.𝒳.val ζ heff _ rfl hG
      (isLimitPreservingOnObjects_structureMorphism D) (D.S.fromSpecStalk _) rfl hΛ hversal
  subst hx
  have := hlft
  have : IsLocallyNoetherian ((D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj xU.1).left :=
    LocallyOfFiniteType.isLocallyNoetherian
      ((D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj xU.1).hom
  -- the restriction arrow of `x` to the completion, read on schemes
  have hxR := congrArg (Over.post D.B.inclusion).obj
    (Deformation.Artin.chosenBase_eq D.B D.S D.hS D.𝒳.val.val.p xR.obj)
  have hr : Deformation.Artin.schemeMap (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion) hxR rfl r =
      Spec.map (CommRingCat.ofHom eR.toRingHom) ≫
        ((D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj xU.1).left.fromSpecCompletedLocalRing
          u₀ := by
    rw [schemeMap_post_eq_left_hom
      (Deformation.Artin.chosenBase_eq D.B D.S D.hS D.𝒳.val.val.p xR.obj) r]
    exact Eq.trans (Category.comp_id _).symm hrbase
  -- the realizing object is isomorphic to the complete local object of the approximation
  obtain ⟨I⟩ := Ry.nonempty_approximationIso hp
  obtain ⟨e⟩ := e
  have hff := Deformation.Artin.fullyFaithful_approximationFunctor_of_isAlgebraicStack
    D.𝒳.val D.𝒳.property
  have := hff.1
  have := hff.2
  let L := (Functor.FullyFaithful.ofFullyFaithful
    (Deformation.Artin.approximationFunctor D.B D.S D.hS D.𝒳.val.val.p hp)).preimageIso (I ≪≫ e)
  refine ⟨xU.1, hlft, inferInstance, u₀, hu₀, hvers, xR.obj.1,
    (Deformation.Artin.chosenBase D.B D.S D.hS D.𝒳.val.val.p xR.obj).R, inferInstance,
    (Deformation.Artin.chosenBase D.B D.S D.hS D.𝒳.val.val.p xR.obj).toS, hxR, L.hom.1.1, r, eR,
    ⟨L.inv.1.1, congrArg (fun f => f.1.1) L.hom_inv_id, congrArg (fun f => f.1.1) L.inv_hom_id⟩,
    hr⟩

/-- **Shrinking a versal chart to a smooth one, compatibly with a completion.** If `x` is versal
at a finite type point `u₀`, `m : y ⟶ z` is an isomorphism from an object over `Spec A`, and
`r : z ⟶ x` lies over `Spec R ≅ Spec 𝒪^∧_{U, u₀} ⟶ U`, then there are a smooth object `x'` with a
point `u₀'`, an isomorphism `eA : 𝒪^∧_{U', u₀'} ≅ A` and an arrow `y ⟶ x'` over
`Spec A ≅ Spec 𝒪^∧_{U', u₀'} ⟶ U'`. -/
private theorem exists_smoothObject_schemeMap_eq_of_isVersalAt (D : VersalSituation.{u, w})
    (x : D.𝒳.val.val.obj)
    [LocallyOfFiniteType ((D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x).hom]
    [IsLocallyNoetherian ((D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x).left]
    (u₀ : ((D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x).left)
    (hu₀ : AlgebraicGeometry.IsFiniteTypePoint u₀)
    (hv : Deformation.Artin.IsVersalAt ((D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x)
      (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion) u₀ x rfl)
    {y z : D.𝒳.val.val.obj} {A R : Type u} [CommRing A] [CommRing R]
    {fY : Spec (.of A) ⟶ D.B.inclusion.obj (D.B.obj D.hS)}
    {fZ : Spec (.of R) ⟶ D.B.inclusion.obj (D.B.obj D.hS)}
    (hy : (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj y = Over.mk fY)
    (hz : (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj z = Over.mk fZ)
    (m : y ⟶ z) [IsIso m] (r : z ⟶ x)
    (eR : ((D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x).left.completedLocalRing u₀ ≃+* R)
    (hr : Deformation.Artin.schemeMap (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion) hz rfl r =
      Spec.map (CommRingCat.ofHom eR.toRingHom) ≫
        ((D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x).left.fromSpecCompletedLocalRing u₀) :
    ∃ (x' : D.𝒳.val.val.obj) (u₀' : ((D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x').left)
      (_ : IsLocallyNoetherian ((D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x').left)
      (eA : ((D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x').left.completedLocalRing u₀' ≃+* A),
      LocallyOfFiniteType ((D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x').hom ∧
      smoothObject.{u, w} D.B D.S D.hS D.𝒳 x' ∧
      ∃ n : y ⟶ x', Deformation.Artin.schemeMap (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion) hy rfl n =
        Spec.map (CommRingCat.ofHom eA.toRingHom) ≫
          ((D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x').left.fromSpecCompletedLocalRing
            u₀' := by
  have : IsLocallyNoetherian (D.B.inclusion.obj (D.B.obj D.hS)) :=
    inferInstanceAs (IsLocallyNoetherian D.S)
  -- shrink to a smooth object
  obtain ⟨x', ρ, hsm, hoi, u₀', hu₀'⟩ := exists_smoothObject_hom_of_isVersalAt D x u₀ hu₀ hv
  have := hoi
  have : LocallyOfFiniteType ((D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x').hom := by
    rw [← Over.w ((D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).map ρ)]
    infer_instance
  have : IsLocallyNoetherian ((D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x').left :=
    LocallyOfFiniteType.isLocallyNoetherian ((D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x').hom
  obtain ⟨r', c, hr'⟩ := exists_hom_fromSpecCompletedLocalRing_of_isOpenImmersion
    D.𝒳.val.property ρ u₀' hu₀' hz r (Spec.map (CommRingCat.ofHom eR.toRingHom)) hr
  set gm : Spec (.of A) ⟶ Spec (.of R) :=
    Deformation.Artin.schemeMap (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion) hy hz m with hgm
  have : IsIso gm := isIso_schemeMap _ hy hz m
  let ψ : CommRingCat.of R ≅ CommRingCat.of A :=
    { hom := Spec.preimage gm
      inv := Spec.preimage (inv gm)
      hom_inv_id := by rw [← Spec.preimage_comp, IsIso.inv_hom_id, Spec.preimage_id]
      inv_hom_id := by rw [← Spec.preimage_comp, IsIso.hom_inv_id, Spec.preimage_id] }
  let eA : ((D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x').left.completedLocalRing u₀' ≃+* A :=
    c.trans (eR.trans ψ.commRingCatIsoToRingEquiv)
  refine ⟨x', u₀', inferInstance, eA, inferInstance, hsm, m ≫ r', ?_⟩
  rw [Deformation.Artin.schemeMap_comp (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion) hy hz rfl m
    r', hr', ← hgm]
  have heA : CommRingCat.ofHom eA.toRingHom =
      CommRingCat.ofHom c.toRingHom ≫ CommRingCat.ofHom eR.toRingHom ≫ ψ.hom :=
    CommRingCat.hom_ext (RingHom.ext fun t => rfl)
  rw [heA, Spec.map_comp, Spec.map_comp, show Spec.map ψ.hom = gm from Spec.map_preimage gm]
  simp only [Category.assoc]

/-- **The point of a chart through a realization.** If an arrow `y ⟶ x` from the object realizing
`ξ` lies over `Spec A ≅ Spec 𝒪^∧_{U, u₀} ⟶ U`, then there are an isomorphism `e : k ≅ κ(u₀)` and an
arrow `x₀ ⟶ x` over `Spec k ≅ Spec κ(u₀) ⟶ U`. -/
private theorem exists_hom_schemeMap_eq_fromSpecResidueField_of_realization
    (D : VersalSituation.{u, w})
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k] (iΛ : Spec (.of Λ) ⟶ D.S)
    (x₀ : D.𝒳.val.val.obj)
    (hx₀ : (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hfinite : LocallyOfFiniteType
        (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) ∧
      QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (ξ : Deformation.FormalObject (Deformation.Artin.predeformationCategory iΛ
      (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion) x₀ hx₀).projection)
    {hA : D.B.Contains (Spec (.of ξ.base))} {y : D.𝒳.val.val.obj}
    {hy : D.𝒳.val.val.p.obj y = Deformation.Artin.baseOver D.B D.S D.hS
      (Deformation.Artin.completeLocalAlgFormalBase iΛ hfinite ξ.base) hA}
    (Ry : (Deformation.Artin.FormalObject.ofPredeformation D.B D.S D.hS iΛ D.𝒳.val.val.p x₀ hx₀
      hfinite ξ).Realization hA y hy)
    {x : D.𝒳.val.val.obj}
    [IsLocallyNoetherian ((D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x).left]
    (u₀ : ((D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x).left)
    (eA : ((D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x).left.completedLocalRing u₀ ≃+*
      ξ.base)
    {n : y ⟶ x}
    (hn : Deformation.Artin.schemeMap (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion)
        (show (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj y =
            Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ ξ.base)) ≫ iΛ) from
          congrArg (Over.post D.B.inclusion).obj hy) rfl n =
      Spec.map (CommRingCat.ofHom eA.toRingHom) ≫
        ((D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x).left.fromSpecCompletedLocalRing u₀) :
    ∃ (e : k ≃+* ((D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x).left.residueField u₀)
      (a : x₀ ⟶ x),
      Deformation.Artin.schemeMap (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion) hx₀ rfl a =
        Spec.map (CommRingCat.ofHom e.symm.toRingHom) ≫
          ((D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x).left.fromSpecResidueField u₀ := by
  have hyq : (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj y =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ ξ.base)) ≫ iΛ) :=
    congrArg (Over.post D.B.inclusion).obj hy
  -- the point
  have hr₀ := Deformation.Artin.schemeMap_closedPointArrow_realization D.B D.S D.hS
    D.𝒳.val.val.p iΛ hx₀ hfinite ξ Ry
  have := isLocalHom_completeResidueMap_comp_toCompletedLocalRing u₀ ξ.base eA
  let eRes := RingEquiv.ofBijective _ (bijective_lift_completedLocalRing u₀ ξ.base eA)
  refine ⟨eRes.symm, (((Deformation.Artin.predeformationCategory iΛ
    (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion) x₀ hx₀).objects
    (ξ.level 0)).arrow ≫ Ry.r 0) ≫ n, ?_⟩
  rw [Deformation.Artin.schemeMap_comp (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion) hx₀ hyq rfl _
    n, hr₀, hn]
  exact specMap_completeResidueMap_comp_fromSpecCompletedLocalRing u₀ ξ.base eA eRes
    (fun t => rfl)

/-- **Stacks 0DR1, part (4): Artin approximation compatible with the morphism `Spec A ⟶ 𝒳`.**
In the versal situation, let `x₀` be a point of `𝒳` over `Spec k ⟶ Spec Λ ⟶ S`, for an affine open
`Spec Λ ⊆ S` and a field `k` of finite type over `S`, with image `s ∈ S` such that `𝒪_{S,s}` is a
G-ring; let `ξ` be a versal formal object of the predeformation category of `x₀`, with base the
versal ring `A`, and let `y` be an object of `𝒳` over `Spec A ⟶ S` realizing `ξ` (the morphism
`Spec A ⟶ 𝒳` of the remark). Then the data of **Stacks 0DR0** may be chosen compatibly with `y`:
there are a smooth object `x` of `𝒳` over a scheme `U` locally of finite type over `S`, a point
`u₀ ∈ U` with an identification `e : k ≅ κ(u₀)`, an arrow `x₀ ⟶ x` of `𝒳` over
`Spec k ≅ Spec κ(u₀) ⟶ U` (so `Spec k ⟶ U ⟶ 𝒳` is `x₀`), an isomorphism `eA : 𝒪^∧_{U, u₀} ≅ A`,
and an arrow `y ⟶ x` of `𝒳` over `Spec A ≅ Spec 𝒪^∧_{U, u₀} ⟶ U`: the morphism `Spec A ⟶ 𝒳` is,
through `eA`, the canonical `Spec 𝒪^∧_{U, u₀} ⟶ U ⟶ 𝒳` of part (3). As the remark says, the
triangles commute up to a 2-arrow, which is what an arrow of `𝒳` over a morphism of schemes is.

This is Artin approximation, **Stacks 07XH**, at the formal object over the site of `ξ`, which is
effective because it is realized and versal over `𝒪_{S,s}` by
`Deformation.Artin.isVersal_stalk_ofPredeformation_of_realization`; the structure morphism of `𝒳`
is limit preserving by **Stacks 0DQJ** and **Stacks 0CMY**. The chart Artin approximation produces
is versal at `u₀`, hence smooth after shrinking by **Stacks 0DQZ**, (1) ⟹ (4). The arrow `y ⟶ x`
is the preimage, under the fully faithful approximation functor (**Stacks 07X8**), of the
isomorphism of formal objects that Artin approximation produces, followed by the restriction arrow
of the chart to the completion. -/
@[stacks 0DR1 "part (4): in Lemma 0DR0 the isomorphism 𝒪^∧_{U,u₀} ≅ A may be chosen so that \
Spec(A) → 𝒳 corresponds to the canonical map Spec(𝒪^∧_{U,u₀}) → U → 𝒳 of part (3)"]
theorem exists_smoothObject_completedLocalRing_realization (D : VersalSituation.{u, w})
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    (iΛ : Spec (.of Λ) ⟶ D.S) (hiΛ : _root_.AlgebraicGeometry.IsOpenImmersion iΛ)
    (x₀ : D.𝒳.val.val.obj)
    (hx₀ : (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hfinite : LocallyOfFiniteType
        (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) ∧
      QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (ξ : Deformation.FormalObject (Deformation.Artin.predeformationCategory iΛ
      (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion) x₀ hx₀).projection)
    (hξ : Deformation.IsVersal (Deformation.Artin.predeformationCategory_isPredeformationCategory
      D.B D.hS iΛ D.𝒳.val.val.p x₀ hx₀ D.𝒳.val.property).cofibered ξ)
    (s : D.S) (hs : (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) (closedPoint k) = s)
    (hG : IsGRing (D.S.presheaf.stalk s))
    {hA : D.B.Contains (Spec (.of ξ.base))} {y : D.𝒳.val.val.obj}
    {hy : D.𝒳.val.val.p.obj y = Deformation.Artin.baseOver D.B D.S D.hS
      (Deformation.Artin.completeLocalAlgFormalBase iΛ hfinite ξ.base) hA}
    (Ry : (Deformation.Artin.FormalObject.ofPredeformation D.B D.S D.hS iΛ D.𝒳.val.val.p x₀ hx₀
      hfinite ξ).Realization hA y hy) :
    ∃ (x : D.𝒳.val.val.obj) (u₀ : ((D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x).left)
      (e : k ≃+* ((D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x).left.residueField u₀)
      (a : x₀ ⟶ x)
      (eA : ((D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x).left.completedLocalRing u₀ ≃+*
        ξ.base),
      LocallyOfFiniteType ((D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x).hom ∧
      smoothObject.{u, w} D.B D.S D.hS D.𝒳 x ∧
      Deformation.Artin.schemeMap (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion) hx₀ rfl a =
        Spec.map (CommRingCat.ofHom e.symm.toRingHom) ≫
          ((D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x).left.fromSpecResidueField u₀ ∧
      ∃ m : y ⟶ x, Deformation.Artin.schemeMap (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion)
          (congrArg (Over.post D.B.inclusion).obj hy) rfl m =
        Spec.map (CommRingCat.ofHom eA.toRingHom) ≫
          ((D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x).left.fromSpecCompletedLocalRing u₀ := by
  obtain ⟨x, _, _, u₀, hu₀, hv, _, _, _, _, hz, m, r, eR, _, hr⟩ :=
    exists_isVersalAt_hom_schemeMap_eq_of_realization D iΛ hiΛ x₀ hx₀ hfinite ξ hξ s hs hG Ry
  have hyq : (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj y =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ ξ.base)) ≫ iΛ) :=
    congrArg (Over.post D.B.inclusion).obj hy
  obtain ⟨x', u₀', _, eA, hlft, hsm, n, hn⟩ :=
    exists_smoothObject_schemeMap_eq_of_isVersalAt D x u₀ hu₀ hv hyq hz m r eR hr
  obtain ⟨e, a, ha⟩ :=
    exists_hom_schemeMap_eq_fromSpecResidueField_of_realization D iΛ x₀ hx₀ hfinite ξ Ry u₀' eA hn
  exact ⟨x', u₀', e, a, eA, hlft, hsm, ha, n, hn⟩

/-- **Stacks 0DR1, the preamble: the versal formal object comes from a morphism `Spec A ⟶ 𝒳`.**
In the versal situation, let `x₀` be a point of `𝒳` over `Spec k ⟶ Spec Λ ⟶ S`, for an affine open
`Spec Λ ⊆ S` and a field `k` of finite type over `S`, and let `ξ` be a formal object of the
predeformation category of `x₀` with base `A` — in the remark, the versal formal object over a
versal ring `A`, though versality is not needed. Then `ξ` comes from a morphism `Spec A ⟶ 𝒳` over
`S`: there is an object `y` of `𝒳` over `Spec A ⟶ Spec Λ ⟶ S` whose restrictions to the
infinitesimal thickenings of the closed point are the levels of `ξ`, compatibly with the
transitions (a `Deformation.Artin.FormalObject.Realization`); `y` names the 1-morphism
`Spec A ⟶ 𝒳` under the 2-Yoneda lemma.

This is effectivity of formal objects of an algebraic stack, the essential surjectivity half of
**Stacks 07X8** (`Deformation.Artin.FormalObject.isEffective_of_isAlgebraicStack`), read over the
base of `ξ` itself by `Deformation.Artin.FormalObject.exists_realization_of_isEffective`. -/
@[stacks 0DR1 "preamble: the versal formal object over A comes from a morphism Spec(A) → 𝒳 \
over S (Artin's Axioms, Lemma 07X8)"]
theorem exists_realization_of_predeformationFormalObject (D : VersalSituation.{u, w})
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    (iΛ : Spec (.of Λ) ⟶ D.S) (x₀ : D.𝒳.val.val.obj)
    (hx₀ : (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hfinite : LocallyOfFiniteType
        (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) ∧
      QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (ξ : Deformation.FormalObject (Deformation.Artin.predeformationCategory iΛ
      (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion) x₀ hx₀).projection) :
    ∃ (y : D.𝒳.val.val.obj)
      (hy : D.𝒳.val.val.p.obj y = Deformation.Artin.baseOver D.B D.S D.hS
        (Deformation.Artin.completeLocalAlgFormalBase iΛ hfinite ξ.base)
        (Deformation.Artin.FormalObject.ofPredeformation D.B D.S D.hS iΛ D.𝒳.val.val.p x₀ hx₀
          hfinite ξ).contains_spec_base),
      Nonempty ((Deformation.Artin.FormalObject.ofPredeformation D.B D.S D.hS iΛ D.𝒳.val.val.p
        x₀ hx₀ hfinite ξ).Realization
          (Deformation.Artin.FormalObject.ofPredeformation D.B D.S D.hS iΛ D.𝒳.val.val.p x₀ hx₀
            hfinite ξ).contains_spec_base y hy) :=
  Deformation.Artin.FormalObject.exists_realization_of_isEffective D.𝒳.val.property
    (Deformation.Artin.FormalObject.isEffective_of_isAlgebraicStack D.𝒳 _).1

/-- **Stacks 0DR0.** In the versal situation, let `x₀` be a point of `𝒳` over
`Spec k ⟶ Spec Λ ⟶ S`, for an affine open `Spec Λ ⊆ S` and a field `k` with `Spec k ⟶ S` of
finite type and image `s`, and let `A` be a versal ring to `𝒳` at `x₀` (**Stacks 0DQV**). If
`𝒪_{S,s}` is a G-ring, there are a smooth object `x` of `𝒳` (a smooth morphism `U ⟶ 𝒳` from a
scheme `U`, here moreover locally of finite type over `S`) and a point `u₀ ∈ U` with residue field
`k`, through `e : k ≅ κ(u₀)`, such that
1. `Spec k ⟶ U ⟶ 𝒳` is `x₀`: there is an arrow `x₀ ⟶ x` of `𝒳` lying over
   `Spec k ≅ Spec κ(u₀) ⟶ U` (a 2-isomorphism of 1-morphisms out of `Spec k`);
2. there is an isomorphism `𝒪^∧_{U, u₀} ≅ A`.

The proof is the source's: the versal formal object is effective (**Stacks 07X8**), so
`AlgebraicGeometry.Stack.exists_smoothObject_completedLocalRing_realization` (Artin approximation,
**Stacks 07XH**, with **Stacks 0DQJ**, **Stacks 0CMY** and **Stacks 0DQZ**) applies to a
realization of it. -/
@[stacks 0DR0]
theorem exists_smoothObject_completedLocalRing_equiv_versalRing (D : VersalSituation.{u, w})
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    (iΛ : Spec (.of Λ) ⟶ D.S) (hiΛ : _root_.AlgebraicGeometry.IsOpenImmersion iΛ)
    (x₀ : D.𝒳.val.val.obj)
    (hx₀ : (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hfinite : LocallyOfFiniteType
        (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) ∧
      QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (A : Deformation.CompleteLocalAlgCat.{u, u, u} Λ k)
    (hA : IsVersalRingAt D iΛ hiΛ x₀ hx₀ hfinite A)
    (s : D.S) (hs : (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) (closedPoint k) = s)
    (hG : IsGRing (D.S.presheaf.stalk s)) :
    ∃ (x : D.𝒳.val.val.obj) (u₀ : ((D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x).left)
      (e : k ≃+* ((D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x).left.residueField u₀)
      (a : x₀ ⟶ x)
      (_ : ((D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x).left.completedLocalRing u₀ ≃+* A),
      LocallyOfFiniteType ((D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x).hom ∧
      smoothObject.{u, w} D.B D.S D.hS D.𝒳 x ∧
      Deformation.Artin.schemeMap (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion) hx₀ rfl a =
        Spec.map (CommRingCat.ofHom e.symm.toRingHom) ≫
          ((D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x).left.fromSpecResidueField u₀ := by
  obtain ⟨ξ, rfl, hξ⟩ := hA
  obtain ⟨y, hy, ⟨Ry⟩⟩ := exists_realization_of_predeformationFormalObject D iΛ x₀ hx₀ hfinite ξ
  obtain ⟨x, u₀, e, a, eA, hlft, hsm, ha, -⟩ := exists_smoothObject_completedLocalRing_realization
    D iΛ hiΛ x₀ hx₀ hfinite ξ hξ s hs hG Ry
  exact ⟨x, u₀, e, a, eA, hlft, hsm, ha⟩

end AlgebraicGeometry.Stack

end
