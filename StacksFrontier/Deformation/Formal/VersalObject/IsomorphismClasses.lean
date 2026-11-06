module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.FiberedCategory.IsoOver
public import StacksFrontier.Deformation.FormalObject.Associated
public import StacksFrontier.Deformation.FormalObject.Basic
public import StacksFrontier.Deformation.InfinitesimalAutomorphism.Tangent
public import StacksFrontier.Deformation.Predeformation.Basic
public import StacksFrontier.Deformation.Smooth.IsomorphismClasses
public import StacksFrontier.Deformation.Smooth.Pushforward
public import StacksFrontier.Deformation.Smooth.Versal
public import StacksFrontier.Deformation.TangentSpace.BijectiveDifferential
public import StacksFrontier.Deformation.TangentSpace.Predeformation

/-!
# Versal formal objects in the functor of isomorphism classes (Stacks 06IZ)

Let `𝓕` be a predeformation category and let `𝓕 → \overline{𝓕}` be the canonical morphism to
its associated functor of isomorphism classes, which is smooth by Stacks 06HK. If `ξ` is a
versal formal object of `𝓕`, then the composite

    \underline{R}|_{𝒞_Λ} ⟶ 𝓕 ⟶ \overline{𝓕}

is smooth, so the image `\overline{ξ}` of `ξ` in `\overline{𝓕}` is again a versal formal
object. The canonical morphism identifies tangent spaces, so if the differential of `ξ` is
bijective then so is the differential of `\overline{ξ}`; in that case `\overline{ξ}` is a hull
of `\overline{𝓕}`.

## Main definitions

* `Deformation.imageInIsomorphismClasses`: the image of a formal object in the associated
  functor of isomorphism classes, taken levelwise.
* `Deformation.levelwiseImage`: the same image written out level by level.

## Main results

* `Deformation.mapIsomorphismClasses_bijective_of_isIsomorphismClasses`: a morphism realizing
  the functor of isomorphism classes is bijective on isomorphism classes at every object of
  the base.
* `Deformation.differential_toIsomorphismClasses_bijective`: **Stacks 06IZ**, the canonical
  morphism to the functor of isomorphism classes identifies tangent spaces.
* `Deformation.isSmooth_associatedMorphism_toIsomorphismClasses`: **Stacks 06IZ**, the
  composite of the morphism associated to a versal formal object with the canonical morphism
  to isomorphism classes is smooth.
* `Deformation.isVersal_imageInIsomorphismClasses`: **Stacks 06IZ**, the image of a versal
  formal object is versal.
* `Deformation.hasBijectiveDifferential_imageInIsomorphismClasses`: **Stacks 06IZ**, the image
  of a formal object with bijective differential has bijective differential.

## Implementation notes

The image formal object is the levelwise application of the canonical morphism, which is what
`Deformation.completionMap` computes; `Deformation.imageInIsomorphismClasses_eq_levelwiseImage`
identifies it with the explicit levelwise record, which is the form in which its associated
morphism can be compared with the composite.

That comparison is an equality of based functors, not merely an isomorphism: the value of the
associated morphism of the image at an Artinian point is the pushforward of the image of a
level of `ξ`, and the pushforward of an image agrees with the image of a pushforward *on the
nose* because the fibres of the isomorphism-class functor are skeletal. The level and the
factoring map are shared because a truncation factorization is unique, which is
`Deformation.truncationFactorization_eq`.

The tangent-space identification is the case of
`Deformation.mapIsomorphismClasses_bijective_of_isIsomorphismClasses` at the dual numbers. It
is stated separately in the direct dual-number model of Stacks 06II, where
`Deformation.differential` lives, and used at the Artinian dual numbers of Stacks 06IB for the
differential of Stacks 06IM.

`CategoryTheory.BasedCategory.ofFunctor` is made locally `implicit_reducible`, as in
`StacksFrontier.Deformation.Formal.VersalObject.MapsToFormalObject`: a based category and the
based category of its own structure functor are equal only up to unfolding that definition.

## References

* [Stacks Project, Tag 06IZ](https://stacks.math.columbia.edu/tag/06IZ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor

namespace Deformation

attribute [local implicit_reducible] CategoryTheory.BasedCategory.ofFunctor

universe u v w uF vF u₁ v₁ u₂ v₂ u₃ v₃

section

variable {C : Type u} [Category.{v} C]

/-- A based functor realizing the functor of isomorphism classes is bijective on isomorphism
classes over every object of the base: injective because its fibres are skeletal and identify
exactly the isomorphism classes upstairs, surjective because it is essentially surjective on
each fibre. -/
@[stacks 06IZ "bijective on isomorphism classes"]
public theorem mapIsomorphismClasses_bijective_of_isIsomorphismClasses
    {𝓐 : BasedCategory.{v₁, u₁} C} {𝓑 : BasedCategory.{v₂, u₂} C}
    (h𝓐 : IsCofiberedInGroupoids 𝓐.p) (h𝓑 : IsCofiberedInGroupoids 𝓑.p)
    (φ : BasedFunctor 𝓐 𝓑) (hφ : IsIsomorphismClasses φ) (A : C) :
    Function.Bijective (mapIsomorphismClasses h𝓐 h𝓑 φ A) := by
  refine ⟨fun x y hxy => ?_, fun y => ?_⟩
  · obtain ⟨x₀, rfl⟩ := classOf_surjective 𝓐 h𝓐 A x
    obtain ⟨y₀, rfl⟩ := classOf_surjective 𝓐 h𝓐 A y
    have hxy' : classOf 𝓑 h𝓑 ((fiberFunctor φ A).obj x₀) =
        classOf 𝓑 h𝓑 ((fiberFunctor φ A).obj y₀) := by
      simpa only [mapIsomorphismClasses_classOf] using hxy
    have hq : Quotient.mk (isIsomorphicSetoid (Fiber 𝓑.p A))
          ((fiberFunctor φ A).obj x₀) =
        Quotient.mk (isIsomorphicSetoid (Fiber 𝓑.p A))
          ((fiberFunctor φ A).obj y₀) := by
      simpa only [classOf_eq] using
        congrArg (cast (isomorphismClasses_obj 𝓑 h𝓑 A)) hxy'
    exact classOf_eq_of_isIsomorphic 𝓐 h𝓐 x₀ y₀
      ((hφ.obj_eq_iff_isomorphic A x₀ y₀).mp (hφ.fiber_skeletal A (Quotient.exact hq)))
  · obtain ⟨z, rfl⟩ := classOf_surjective 𝓑 h𝓑 A y
    have : (fiberFunctor φ A).EssSurj := hφ.fiber_essSurj A
    obtain ⟨x, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage (fiberFunctor φ A) z
    refine ⟨classOf 𝓐 h𝓐 x, ?_⟩
    rw [mapIsomorphismClasses_classOf]
    exact classOf_eq_of_isIsomorphic 𝓑 h𝓑 _ _ ⟨e⟩

/-- Composing based functors composes the induced maps on isomorphism classes. -/
public theorem mapIsomorphismClasses_comp
    {𝓐 : BasedCategory.{v₁, u₁} C} {𝓑 : BasedCategory.{v₂, u₂} C}
    {𝓒 : BasedCategory.{v₃, u₃} C}
    (h𝓐 : IsCofiberedInGroupoids 𝓐.p) (h𝓑 : IsCofiberedInGroupoids 𝓑.p)
    (h𝓒 : IsCofiberedInGroupoids 𝓒.p)
    (F : BasedFunctor 𝓐 𝓑) (G : BasedFunctor 𝓑 𝓒) (A : C) :
    mapIsomorphismClasses h𝓐 h𝓒 (BasedFunctor.comp F G) A =
      fun z => mapIsomorphismClasses h𝓑 h𝓒 G A (mapIsomorphismClasses h𝓐 h𝓑 F A z) := by
  funext z
  obtain ⟨x, rfl⟩ := classOf_surjective 𝓐 h𝓐 A z
  simp only [mapIsomorphismClasses_classOf]
  have hobj : (fiberFunctor (BasedFunctor.comp F G) A).obj x =
      (fiberFunctor G A).obj ((fiberFunctor F A).obj x) := Subtype.ext rfl
  exact classOf_eq_of_isIsomorphic 𝓒 h𝓒 _ _ ⟨eqToIso hobj⟩

end

section

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

/-- Two maps from the same adic truncation that both factor an Artinian point agree. -/
public theorem truncationMap_eq
    {R : CompleteLocalAlgCat.{u, v, w} Λ k}
    (α : (restrictedCoyoneda R).Elements) (n : ℕ)
    (a b : AdicTruncation.obj R n ⟶ α.1)
    (ha : IsTruncationFactorization α.2 n a)
    (hb : IsTruncationFactorization α.2 n b) : a = b := by
  refine ArtinianLocalAlgCat.hom_ext (AlgHom.ext fun x => ?_)
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mkₐ_surjective Λ (AdicTruncation.ideal R n) x
  have h₁ := congrArg (fun f => f r) ha.2.2
  have h₂ := congrArg (fun f => f r) hb.2.2
  change a.hom (Ideal.Quotient.mkₐ Λ (AdicTruncation.ideal R n) r) = α.2.hom r at h₁
  change b.hom (Ideal.Quotient.mkₐ Λ (AdicTruncation.ideal R n) r) = α.2.hom r at h₂
  exact h₁.trans h₂.symm

/-- A truncation factorization of an Artinian point is unique, level and map together. -/
public theorem truncationFactorization_eq
    {R : CompleteLocalAlgCat.{u, v, w} Λ k}
    (α : (restrictedCoyoneda R).Elements) (n m : ℕ)
    (a : AdicTruncation.obj R n ⟶ α.1) (b : AdicTruncation.obj R m ⟶ α.1)
    (ha : IsTruncationFactorization α.2 n a)
    (hb : IsTruncationFactorization α.2 m b) :
    (⟨n, a⟩ : Σ l, AdicTruncation.obj R l ⟶ α.1) = ⟨m, b⟩ := by
  obtain rfl : n = m := Nat.le_antisymm (ha.2.1 m hb.1) (hb.2.1 n ha.1)
  exact congrArg (Sigma.mk n) (truncationMap_eq α n a b ha hb)

end

section

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
variable (𝓕 : BasedCategory.{vF, uF} (ArtinianLocalAlgCat.{u, max v w, w} Λ k))
variable (hpre : IsPredeformationCategory 𝓕.p)

/-- The image of a formal object in the associated functor of isomorphism classes, obtained by
applying the canonical morphism at every level. -/
public noncomputable abbrev imageInIsomorphismClasses (ξ : FormalObject 𝓕.p) :
    FormalObject (CategoryOfElements.π (isomorphismClasses 𝓕 hpre.cofibered)) :=
  (formalObjectMapOfCompEq (toIsomorphismClasses 𝓕 hpre.cofibered).toFunctor
    (toIsomorphismClasses 𝓕 hpre.cofibered).w).obj ξ

/-- The image of a formal object in the associated functor of isomorphism classes, written out
level by level: the canonical morphism applied to each level, with the transition maps and
their liftings transported along it. -/
public noncomputable abbrev levelwiseImage (ξ : FormalObject 𝓕.p) :
    FormalObject (CategoryOfElements.π (isomorphismClasses 𝓕 hpre.cofibered)) :=
  letI φ := toIsomorphismClasses 𝓕 hpre.cofibered
  { base := ξ.base
    level := fun n => φ.toFunctor.obj (ξ.level n)
    level_eq := fun n => (Functor.congr_obj φ.w (ξ.level n)).trans (ξ.level_eq n)
    transition := fun n => φ.toFunctor.map (ξ.transition n)
    transition_lift := fun n => by
      have := ξ.transition_lift n
      exact BasedFunctor.preserves_isHomLift φ
        ((AdicTruncation.transitionNat n).app ξ.base) (ξ.transition n) }

/-- The levelwise functor on formal objects is computed levelwise. -/
private theorem formalObjectMapOfCompEq_obj_eq
    {F : Type u₁} [Category.{v₁} F] {G : Type u₂} [Category.{v₂} G]
    {p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k}
    {q : G ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k}
    (φ : F ⥤ G) (hφ : φ ⋙ q = p) (ξ : FormalObject p) :
    (formalObjectMapOfCompEq φ hφ).obj ξ =
      { base := ξ.base
        level := fun n => φ.obj (ξ.level n)
        level_eq := fun n => (Functor.congr_obj hφ (ξ.level n)).trans (ξ.level_eq n)
        transition := fun n => φ.map (ξ.transition n)
        transition_lift := fun n => by
          cases hφ
          apply IsHomLift.of_fac q _ _ (ξ.level_eq (n + 1)) (ξ.level_eq n)
          have := ξ.transition_lift n
          simpa only [Functor.comp_map] using
            IsHomLift.fac (φ ⋙ q) ((AdicTruncation.transitionNat n).app ξ.base)
              (ξ.transition n) } := by
  cases hφ
  rfl

/-- The image of a formal object is its explicit levelwise image. -/
public theorem imageInIsomorphismClasses_eq_levelwiseImage (ξ : FormalObject 𝓕.p) :
    imageInIsomorphismClasses 𝓕 hpre ξ = levelwiseImage 𝓕 hpre ξ :=
  formalObjectMapOfCompEq_obj_eq (toIsomorphismClasses 𝓕 hpre.cofibered).toFunctor
    (toIsomorphismClasses 𝓕 hpre.cofibered).w ξ

/-- At an Artinian point, the associated morphism of the levelwise image takes the value the
canonical morphism gives to the value of the associated morphism of the original object. -/
private theorem associatedImage_obj_eq (ξ : FormalObject 𝓕.p)
    (P : ChosenPushforwards 𝓕.p)
    (Q : ChosenPushforwards (CategoryOfElements.π (isomorphismClasses 𝓕 hpre.cofibered)))
    (α : (restrictedCoyoneda ξ.base).Elements) :
    (associatedMorphism
      (categoryOfElements_projection_isCofibered (isomorphismClasses 𝓕 hpre.cofibered))
      (levelwiseImage 𝓕 hpre ξ) Q).toBasedFunctor.obj α =
      (toIsomorphismClasses 𝓕 hpre.cofibered).toFunctor.obj
        ((associatedMorphism hpre.cofibered ξ P).toBasedFunctor.obj α) := by
  classical
  let φ := toIsomorphismClasses 𝓕 hpre.cofibered
  let ξ' := levelwiseImage 𝓕 hpre ξ
  let α' : (BasedCategory.ofFunctor
      (CategoryOfElements.π (restrictedCoyoneda ξ'.base))).obj := α
  let hq := categoryOfElements_projection_isCofibered (isomorphismClasses 𝓕 hpre.cofibered)
  let a := associatedMorphism hpre.cofibered ξ P
  let b := associatedMorphism hq ξ' Q
  have hfactor := truncationFactorization_eq α (a.level α) (b.level α')
    (a.factor α) (b.factor α') (a.factor_spec α) (b.factor_spec α')
  have hpushforward := congrArg
    (fun t : Σ n, AdicTruncation.obj ξ.base n ⟶ α.1 =>
      ((Q t.2).obj ⟨ξ'.level t.1, ξ'.level_eq t.1⟩).1) hfactor
  let x : Fiber 𝓕.p (AdicTruncation.obj ξ.base (a.level α)) :=
    ⟨ξ.level (a.level α), ξ.level_eq (a.level α)⟩
  let φB := fiberFunctor φ (AdicTruncation.obj ξ.base (a.level α))
  let φA := fiberFunctor φ α.1
  let Pα := P (a.factor α)
  let Qα := Q (a.factor α)
  obtain ⟨sq⟩ := pushforwardFunctorsFormTwoCommutativeSquare
    𝓕.p (CategoryOfElements.π (isomorphismClasses 𝓕 hpre.cofibered)) hq
    φ.toFunctor φ.w Pα Qα
  have hinput : φB.obj x =
      (⟨ξ'.level (a.level α), ξ'.level_eq (a.level α)⟩ :
        (CategoryOfElements.π (isomorphismClasses 𝓕 hpre.cofibered)).Fiber
          (AdicTruncation.obj ξ.base (a.level α))) := Subtype.ext rfl
  have hEq : φA.obj (Pα.obj x) = Qα.obj (φB.obj x) :=
    (isomorphismClassesData 𝓕 hpre.cofibered).quotient.fiber_skeletal α.1 ⟨sq.comm.app x⟩
  change b.toBasedFunctor.obj α' = φ.toFunctor.obj (a.toBasedFunctor.obj α)
  rw [a.obj_eq α, b.obj_eq α', ← hpushforward]
  change (Qα.obj
      (⟨ξ'.level (a.level α), ξ'.level_eq (a.level α)⟩ :
        (CategoryOfElements.π (isomorphismClasses 𝓕 hpre.cofibered)).Fiber
          (AdicTruncation.obj ξ.base (a.level α)))).1 = (φA.obj (Pα.obj x)).1
  rw [hinput] at hEq
  exact (congrArg Subtype.val hEq).symm

/-- The associated morphism of the levelwise image is the associated morphism of the original
object followed by the canonical morphism. -/
private theorem associatedImage_eq_comp (ξ : FormalObject 𝓕.p)
    (P : ChosenPushforwards 𝓕.p)
    (Q : ChosenPushforwards (CategoryOfElements.π (isomorphismClasses 𝓕 hpre.cofibered))) :
    (associatedMorphism
      (categoryOfElements_projection_isCofibered (isomorphismClasses 𝓕 hpre.cofibered))
      (levelwiseImage 𝓕 hpre ξ) Q).toBasedFunctor =
      BasedFunctor.comp (associatedMorphism hpre.cofibered ξ P).toBasedFunctor
        (toIsomorphismClasses 𝓕 hpre.cofibered) := by
  classical
  refine BasedCategory.BasedFunctor.ext' ?_
  let φ := toIsomorphismClasses 𝓕 hpre.cofibered
  let hq := categoryOfElements_projection_isCofibered (isomorphismClasses 𝓕 hpre.cofibered)
  let a := associatedMorphism hpre.cofibered ξ P
  let b := associatedMorphism hq (levelwiseImage 𝓕 hpre ξ) Q
  let c := BasedFunctor.comp a.toBasedFunctor φ
  have hObj (α : (restrictedCoyoneda ξ.base).Elements) :
      b.toBasedFunctor.obj α = c.obj α :=
    associatedImage_obj_eq 𝓕 hpre ξ P Q α
  refine CategoryTheory.Functor.ext (h_obj := hObj) (h_map := fun α β g => ?_)
  apply CategoryOfElements.ext
  let q := (BasedCategory.ofFunctor
    (CategoryOfElements.π (isomorphismClasses 𝓕 hpre.cofibered))).p
  have hproj := b.toBasedFunctor.w.trans c.w.symm
  change q.map (b.toBasedFunctor.map g) =
    q.map (eqToHom (hObj α) ≫ c.map g ≫ eqToHom (hObj β).symm)
  calc
    q.map (b.toBasedFunctor.map g) =
        eqToHom (Functor.congr_obj hproj α) ≫ q.map (c.map g) ≫
          eqToHom (Functor.congr_obj hproj β).symm := by
      exact Functor.congr_hom hproj g
    _ = q.map (eqToHom (hObj α) ≫ c.map g ≫ eqToHom (hObj β).symm) := by
      rw [Functor.map_comp, Functor.map_comp, CategoryTheory.eqToHom_map,
        CategoryTheory.eqToHom_map]
      rfl

-- A based functor is determined by its underlying functor:
-- `CategoryTheory.BasedCategory.BasedFunctor.ext'`, public in
-- `StacksFrontier.CategoryTheory.FiberedCategory.IsoOver`. A `private` re-declaration,
-- one of ten across the library, stood here.

/-- **Stacks Project, Tag 06IZ.** The composite of the morphism associated to a versal formal
object with the canonical morphism to the functor of isomorphism classes is smooth. -/
@[stacks 06IZ "smooth composite"]
public theorem isSmooth_associatedMorphism_toIsomorphismClasses
    (ξ : FormalObject 𝓕.p) (hξ : IsVersal hpre.cofibered ξ)
    (pushforwards : ChosenPushforwards 𝓕.p) :
    IsSmooth (BasedFunctor.comp
      (associatedMorphism hpre.cofibered ξ pushforwards).toBasedFunctor
      (toIsomorphismClasses 𝓕 hpre.cofibered)) :=
  isSmooth_comp
    (associatedMorphism hpre.cofibered ξ pushforwards).toBasedFunctor
    (toIsomorphismClasses 𝓕 hpre.cofibered)
    (hξ pushforwards)
    (isSmooth_toIsomorphismClasses 𝓕 hpre.cofibered)

/-- **Stacks Project, Tag 06IZ.** The image of a versal formal object in the functor of
isomorphism classes is versal. -/
@[stacks 06IZ "versal image"]
public theorem isVersal_imageInIsomorphismClasses
    (ξ : FormalObject 𝓕.p) (hξ : IsVersal hpre.cofibered ξ) :
    IsVersal
      (categoryOfElements_projection_isCofibered (isomorphismClasses 𝓕 hpre.cofibered))
      (imageInIsomorphismClasses 𝓕 hpre ξ) := by
  rw [imageInIsomorphismClasses_eq_levelwiseImage]
  intro Q
  let P := chosenPushforwardsOfCofibered 𝓕.p hpre.cofibered
  let φ := toIsomorphismClasses 𝓕 hpre.cofibered
  let a := associatedMorphism hpre.cofibered ξ P
  let b := associatedMorphism
    (categoryOfElements_projection_isCofibered (isomorphismClasses 𝓕 hpre.cofibered))
    (levelwiseImage 𝓕 hpre ξ) Q
  have hbf := associatedImage_eq_comp 𝓕 hpre ξ P Q
  rw [hbf]
  exact isSmooth_associatedMorphism_toIsomorphismClasses 𝓕 hpre ξ hξ P

/-- **Stacks Project, Tag 06IZ.** The image in the functor of isomorphism classes of a formal
object with bijective differential has bijective differential: the canonical morphism
identifies the two tangent spaces. -/
@[stacks 06IZ "tangent isomorphism", sga "7 VI 1.13" "tangent iso for [A]"]
public theorem hasBijectiveDifferential_imageInIsomorphismClasses
    (ξ : FormalObject 𝓕.p) (hξ : HasBijectiveDifferential hpre.cofibered ξ) :
    HasBijectiveDifferential
      (categoryOfElements_projection_isCofibered (isomorphismClasses 𝓕 hpre.cofibered))
      (imageInIsomorphismClasses 𝓕 hpre ξ) := by
  rw [imageInIsomorphismClasses_eq_levelwiseImage]
  obtain ⟨P, hP⟩ := hξ
  let φ := toIsomorphismClasses 𝓕 hpre.cofibered
  let hT := categoryOfElements_projection_isCofibered (isomorphismClasses 𝓕 hpre.cofibered)
  let hR := categoryOfElements_projection_isCofibered (restrictedCoyoneda ξ.base)
  let A₂ := artinianDualNumbers.{u, w, v} Λ k
  let mφ := mapIsomorphismClasses hpre.cofibered hT φ A₂
  let Q := chosenPushforwardsOfCofibered
    (CategoryOfElements.π (isomorphismClasses 𝓕 hpre.cofibered)) hT
  let a := associatedMorphism hpre.cofibered ξ P
  let b := associatedMorphism hT (levelwiseImage 𝓕 hpre ξ) Q
  have hbf := associatedImage_eq_comp 𝓕 hpre ξ P Q
  have hderiv : derivationToTangent hT (levelwiseImage 𝓕 hpre ξ) Q =
      fun d => mφ (derivationToTangent hpre.cofibered ξ P d) := by
    funext d
    let x := (tangentSpaceDerivationsLinearEquiv ξ.base).symm d
    let z : Fiber (CategoryOfElements.π (restrictedCoyoneda ξ.base)) A₂ :=
      ⟨(restrictedCoyoneda ξ.base).elementsMk A₂ x, rfl⟩
    change mapIsomorphismClasses hR hT b.toBasedFunctor A₂
        (classOf (BasedCategory.ofFunctor
          (CategoryOfElements.π (restrictedCoyoneda ξ.base))) hR z) =
      mφ (mapIsomorphismClasses hR hpre.cofibered a.toBasedFunctor A₂
        (classOf (BasedCategory.ofFunctor
          (CategoryOfElements.π (restrictedCoyoneda ξ.base))) hR z))
    rw [congrArg (fun G => mapIsomorphismClasses hR hT G A₂) hbf]
    exact congrFun (mapIsomorphismClasses_comp hR hpre.cofibered hT a.toBasedFunctor φ A₂) _
  refine ⟨Q, ?_⟩
  exact (congrArg Function.Bijective hderiv).mpr
    ((mapIsomorphismClasses_bijective_of_isIsomorphismClasses hpre.cofibered hT φ
      (isomorphismClassesData 𝓕 hpre.cofibered).quotient A₂).comp hP)

end

section

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
variable (𝓕 : BasedCategory.{vF, uF} (ArtinianLocalAlgCat.{u, w, w} Λ k))
variable (hpre : IsPredeformationCategory 𝓕.p)

/-- **Stacks Project, Tag 06IZ.** The canonical morphism from a predeformation category to its
functor of isomorphism classes identifies tangent spaces. -/
@[stacks 06IZ "tangent spaces of the canonical morphism"]
public theorem differential_toIsomorphismClasses_bijective :
    Function.Bijective
      (differential hpre.cofibered
        (categoryOfElements_projection_isCofibered (isomorphismClasses 𝓕 hpre.cofibered))
        (toIsomorphismClasses 𝓕 hpre.cofibered)) :=
  mapIsomorphismClasses_bijective_of_isIsomorphismClasses hpre.cofibered
    (categoryOfElements_projection_isCofibered (isomorphismClasses 𝓕 hpre.cofibered))
    (toIsomorphismClasses 𝓕 hpre.cofibered)
    (isomorphismClassesData 𝓕 hpre.cofibered).quotient
    (augmentedDualNumbers (Λ := Λ) (k := k))

end

end Deformation

end
