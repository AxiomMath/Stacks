module

public import StacksFrontier.Deformation.FormalObject.AssociatedMorphismMap
public import StacksFrontier.Deformation.FormalObject.Completion
public import StacksFrontier.Deformation.FormalObject.RepresentableMorphism
public import StacksFrontier.Deformation.FormalObject.YonedaEquivalence
public import StacksFrontier.Deformation.Predeformation.ProrepresentableLimits
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Formal objects are prorepresentable functors with a morphism to the category

Let `p : F ⥤ 𝒞_Λ` be cofibered in groupoids. Spelling out the Yoneda description of Stacks
06HC, giving a formal object `ξ` of `F` is the same as giving a prorepresentable functor
`U : 𝒞_Λ ⥤ Sets` together with a morphism `U → F` over `𝒞_Λ`. This file makes that pair into
a category and proves it equivalent to the category of formal objects.

## Main definitions

* `Deformation.ProrepresentableMorphism`: a prorepresentable functor on `𝒞_Λ` together with a
  morphism from its category of elements to `F` over `𝒞_Λ`.
* `Deformation.ProrepresentableMorphism.Hom`: a morphism of such pairs — a natural
  transformation of the functors, in the Yoneda direction, together with a morphism over
  `𝒞_Λ` from the restricted first morphism to the second.
* `Deformation.ProrepresentableMorphism.elementsMap`: the morphism of based categories over
  `𝒞_Λ` induced on categories of elements by a natural transformation of functors.

## Main results

* `Deformation.formalObjectsProrepresentableMorphismEquivalence`: **Stacks 06HD**, there is a
  category structure on the pairs whose homs are `ProrepresentableMorphism.Hom`, and the
  category of formal objects of `p` is equivalent to it.

## Implementation notes

A functor `U` is viewed as the based category of its elements over `𝒞_Λ`, so that a morphism
`U → F` is a `BasedFunctor`. A morphism of pairs from `(U, φ)` to `(V, ψ)` consists of a
natural transformation `V ⟶ U` and a morphism from the restriction of `φ` along it to `ψ`: the
reversal is the Yoneda reversal, a map `R ⟶ S` of representing complete local algebras
inducing `Hom(S, -) ⟶ Hom(R, -)`. The equivalence is proved for the total categories, not
merely fibrewise over one representing algebra, which is what Stacks 06SK already gives.

For a map of representing algebras, `ProrepresentableMorphism.elementsMap` of
`Deformation.restrictedCoyonedaMap` is `Deformation.restrictedRepresentableMap`; the general
form is needed because the base of a morphism of pairs is an arbitrary natural
transformation.

The category structure is transported from the category of formal objects along the hom
bijections, because there is no formula for the composite of two morphisms of pairs: the
composite of the base transformations is forced, but the comparison morphism is obtained from
the Yoneda bijection. This is why the result is stated as the existence of a category
structure with prescribed hom types rather than as an `instance`.

Three ingredients carry the proof. Every point of `U = underline S|_{𝒞_Λ}` factors through an
adic truncation of `S` (Stacks 06IC), so a natural transformation out of `U` is determined by
its values on the canonical quotient points; with the completion description of Stacks 06HE
this makes `R ⟶ S ↦ restrictedCoyonedaMap` a bijection, which is the fully faithfulness of
Yoneda for `𝒞_Λ`. Over a fixed representing algebra, morphisms into `F` are formal objects by
Stacks 06SK, and the quasi-inverse is pushforward along Artinian points (Stacks 06HC); the
2-cell comparing the associated morphisms of a morphism of formal objects is Stacks 06SL.

## References

* [Stacks Project, Tag 06HD](https://stacks.math.columbia.edu/tag/06HD)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor IsLocalRing

namespace Deformation

universe u v w uF vF

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
variable {F : Type uF} [Category.{vF} F]

/-- **Stacks 06HD.** A prorepresentable functor on `𝒞_Λ` together with a morphism from its
category of elements to a category cofibered over `𝒞_Λ`. This is the data Stacks 06HD
exhibits as equivalent to a formal object. -/
@[stacks 06HD "the data equivalent to a formal object"]
structure ProrepresentableMorphism (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k) where
  /-- The functor on `𝒞_Λ`. -/
  functor : ArtinianLocalAlgCat.{u, v, w} Λ k ⥤ Type v
  /-- It is prorepresentable. -/
  prorepresentable : IsProrepresentable functor
  /-- The morphism from its category of elements to `F`, over `𝒞_Λ`. -/
  toF : BasedFunctor
    (BasedCategory.ofFunctor (Functor.Elements.π functor))
    (BasedCategory.ofFunctor p)

namespace ProrepresentableMorphism

/-- The morphism of based categories over `𝒞_Λ` induced on categories of elements by a natural
transformation of functors. For a map of representing complete local algebras this is
`Deformation.restrictedRepresentableMap` of `Deformation.restrictedCoyonedaMap`. -/
def elementsMap {U V : ArtinianLocalAlgCat.{u, v, w} Λ k ⥤ Type v} (a : U ⟶ V) :
    BasedFunctor (BasedCategory.ofFunctor (Functor.Elements.π U))
      (BasedCategory.ofFunctor (Functor.Elements.π V)) where
  toFunctor := NatTrans.mapElements a
  w := rfl

/-- **Stacks 06HD.** A morphism of prorepresentable pairs: a natural transformation of the
functors in the Yoneda direction, together with a morphism over `𝒞_Λ` from the restriction of
the source's morphism along it to the target's morphism. -/
@[stacks 06HD "morphisms of the data"]
structure Hom {p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k}
    (X Y : ProrepresentableMorphism p) where
  /-- The natural transformation of functors, in the Yoneda direction. -/
  base : Y.functor ⟶ X.functor
  /-- The comparison over `𝒞_Λ`. -/
  comparison : (elementsMap base).comp X.toF ⟶ Y.toF

end ProrepresentableMorphism

/-- Every Artinian point of the functor represented by `S` factors through the canonical
quotient point of some adic truncation of `S`: the maximal ideal of an Artinian local algebra
is nilpotent, so the point kills a power of the maximal ideal of `S`. -/
private lemma exists_canonicalQuotientPoint_factorization
    {S : CompleteLocalAlgCat.{u, v, w} Λ k} {A : ArtinianLocalAlgCat.{u, v, w} Λ k}
    (α : (restrictedCoyoneda S).obj A) :
    ∃ n, ∃ f : AdicTruncation.obj S n ⟶ A,
      (restrictedCoyoneda S).map f (canonicalQuotientPoint S n) = α := by
  obtain ⟨n, hn⟩ := exists_pow_maximalIdeal_eq_bot A
  obtain ⟨f, hf⟩ := exists_factorThroughAdicTruncation α hn
  refine ⟨n, f, CompleteLocalAlgCat.Hom.ext ?_⟩
  rw [restrictedCoyoneda_map_hom, canonicalQuotientPoint_hom]
  exact hf

/-- A natural transformation out of a restricted representable functor is determined by its
values on the canonical quotient points, every Artinian point factoring through one of
them. -/
private lemma restrictedCoyoneda_natTrans_ext
    {R S : CompleteLocalAlgCat.{u, v, w} Λ k}
    {a b : restrictedCoyoneda S ⟶ restrictedCoyoneda R}
    (h : ∀ n, a.app _ (canonicalQuotientPoint S n) =
      b.app _ (canonicalQuotientPoint S n)) : a = b := by
  ext A α
  obtain ⟨n, f, rfl⟩ := exists_canonicalQuotientPoint_factorization α
  have ha := congrArg (fun t => t (canonicalQuotientPoint S n)) (a.naturality f)
  have hb := congrArg (fun t => t (canonicalQuotientPoint S n)) (b.naturality f)
  exact ha.trans ((congrArg ((restrictedCoyoneda R).map f) (h n)).trans hb.symm)

/-- **Stacks 06HD.** Yoneda for `𝒞_Λ`: precomposition is a bijection from maps `R ⟶ S` of
complete local algebras onto natural transformations of the restricted representable functors
in the opposite direction. The inverse reads off the compatible system of quotient points
determined by a natural transformation and uses the completion description of Stacks 06HE. -/
@[stacks 06HD "Yoneda for the restricted representable functors"]
theorem restrictedCoyonedaMap_bijective (R S : CompleteLocalAlgCat.{u, v, w} Λ k) :
    Function.Bijective (restrictedCoyonedaMap (R := R) (S := S)) := by
  let e := (coyonedaIsoAdicCompletion R).app S
  have eqv (f : R ⟶ S) (n : ℕ) :
      (e.hom f).value n = (restrictedCoyonedaMap f).app _ (canonicalQuotientPoint S n) := by
    apply CompleteLocalAlgCat.Hom.ext
    dsimp [e]
    rw [coyonedaIsoAdicCompletion_hom_apply]
    change _ = (canonicalQuotientPoint S n).hom.comp f.hom
    rw [canonicalQuotientPoint_hom]
    rfl
  constructor
  · intro f g h
    apply ((isIso_iff_bijective e.hom).mp inferInstance).injective
    apply AdicSection.ext
    intro n
    rw [eqv, eqv, h]
  · intro a
    let x : AdicSection (restrictedCoyoneda R) S :=
      { value := fun n => a.app _ (canonicalQuotientPoint S n)
        compatible := fun n => by
          have h := congrArg (fun t => t (canonicalQuotientPoint S (n + 1)))
            (a.naturality (AdicTruncation.transition S n))
          change a.app _ ((restrictedCoyoneda S).map _ _) =
            (restrictedCoyoneda R).map _ (a.app _ _) at h
          rw [← h, canonicalQuotientPoint_transition] }
    obtain ⟨f, hf⟩ := ((isIso_iff_bijective e.hom).mp inferInstance).surjective x
    refine ⟨f, restrictedCoyoneda_natTrans_ext (fun n => ?_)⟩
    rw [← eqv, hf]

/-- The morphism of restricted representable categories associated with a formal object, for
the canonical choice of pushforwards supplied by the cofibered condition. -/
private noncomputable abbrev associated {p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k}
    (hp : IsCofiberedInGroupoids p) (ξ : FormalObject p) :=
  (associatedMorphism hp ξ (chosenPushforwardsOfCofibered p hp)).toBasedFunctor

/-- A morphism of formal objects with base `f` lies over `f` for the projection to the base. -/
private lemma isHomLift_projection_of_base_eq {p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k}
    {ξ η : FormalObject p} {f : ξ.base ⟶ η.base} {a : ξ ⟶ η} (h : a.base = f) :
    (FormalObject.projection (p := p)).IsHomLift f a :=
  IsHomLift.of_fac' _ f a rfl rfl (by simpa using h)

/-- The equivalence between morphisms of pairs and pairs of a base transformation and a
comparison. -/
private def homSigmaEquiv {p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k}
    (X Y : ProrepresentableMorphism p) :
    (Σ a : Y.functor ⟶ X.functor, (ProrepresentableMorphism.elementsMap a).comp X.toF ⟶ Y.toF) ≃
      ProrepresentableMorphism.Hom X Y where
  toFun a := ⟨a.1, a.2⟩
  invFun a := ⟨a.base, a.comparison⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Morphisms of formal objects over a fixed morphism of representing algebras are the
morphisms of the associated represented pairs: pushing `ξ` forward along the base map lands in
the fibre over `η.base`, where Stacks 06SK identifies morphisms into `F` with formal
objects. -/
private lemma represented_hom_over_equiv
    {p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k}
    (hp : IsCofiberedInGroupoids p) (ξ η : FormalObject p) (f : ξ.base ⟶ η.base) :
    Nonempty ({a : ξ ⟶ η // a.base = f} ≃
      ((ProrepresentableMorphism.elementsMap (restrictedCoyonedaMap f)).comp
        (associated hp ξ) ⟶ associated hp η)) := by
  classical
  let q := FormalObject.projection (p := p)
  have hq := formalObjectProjection_isCofiberedInGroupoids p hp
  obtain ⟨S, yl, ye, yt, ytl⟩ := η
  obtain ⟨⟨T, zl, ze, zt, ztl⟩, j, hj⟩ : ∃ z : FormalObject p, ∃ j : ξ ⟶ z, q.IsHomLift f j :=
    exists_pushforward hq f ξ rfl
  have hT : T = S := IsHomLift.codomain_eq q f j
  subst T
  let z : FormalObject p := ⟨S, zl, ze, zt, ztl⟩
  let y : FormalObject p := ⟨S, yl, ye, yt, ytl⟩
  have hj' : j.base = f := (IsHomLift.eq_of_isHomLift q (a := ξ) (b := z) f j).symm
  have hc := isStronglyCocartesian_of_isCofiberedInGroupoids hq f j hj
  let z' : q.Fiber S := Functor.Fiber.mk (a := z) rfl
  let y' : q.Fiber S := Functor.Fiber.mk (a := y) rfl
  let g : (z' ⟶ y') → {a : ξ ⟶ y // a.base = f} := fun a =>
    ⟨j ≫ Functor.Fiber.fiberInclusion.map a, by
      let φ : z ⟶ y := Functor.Fiber.fiberInclusion.map a
      have hlift : q.IsHomLift (𝟙 S) φ := a.2
      have ha' : φ.base = 𝟙 S :=
        (IsHomLift.eq_of_isHomLift q (a := z) (b := y) (𝟙 S) φ).symm
      change j.base ≫ φ.base = f
      rw [hj', ha', Category.comp_id]⟩
  have hg : Function.Bijective g := by
    constructor
    · intro a b hab
      let φ : z ⟶ y := Functor.Fiber.fiberInclusion.map a
      let ψ : z ⟶ y := Functor.Fiber.fiberInclusion.map b
      have hlφ : q.IsHomLift (𝟙 S) φ := a.2
      have hlψ : q.IsHomLift (𝟙 S) ψ := b.2
      apply Functor.Fiber.hom_ext
      change φ = ψ
      apply IsStronglyCocartesian.ext q f j (𝟙 S)
      exact congrArg Subtype.val hab
    · intro a
      have ha := isHomLift_projection_of_base_eq a.2
      obtain ⟨b, ⟨hb, hfac⟩, _⟩ := IsStronglyCocartesian.universal_property
        q f j (𝟙 S) f (Category.comp_id f).symm a.1
      exact ⟨⟨b, hb⟩, Subtype.ext hfac⟩
  let E := representableMorphismFormalObjectEquivalence p hp S
  let iz : E.equivalence.inverse.obj z' ≅ associated hp z :=
    inverseObjIsoAssociatedMorphism hp z E (chosenPushforwardsOfCofibered p hp)
  let iy : E.equivalence.inverse.obj y' ≅ associated hp y :=
    inverseObjIsoAssociatedMorphism hp y E (chosenPushforwardsOfCofibered p hp)
  obtain ⟨t, _⟩ := associatedMorphism_map hp j (chosenPushforwardsOfCofibered p hp)
  have ht : (ProrepresentableMorphism.elementsMap
      (restrictedCoyonedaMap f)).comp (associated hp ξ) ≅ associated hp z := by
    rw [← hj']
    exact t
  exact ⟨(Equiv.ofBijective g hg).symm |>.trans
    (E.equivalence.fullyFaithfulInverse.homEquiv.trans
      ((iz.homCongr iy).trans (ht.symm.homCongr (Iso.refl _))))⟩

/-- The prorepresentable pair determined by a formal object: the functor represented by its
base, together with its associated morphism. -/
@[sga "7 VI 2.2(d)"]
private noncomputable abbrev representedPair {p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k}
    (hp : IsCofiberedInGroupoids p) (ξ : FormalObject p) : ProrepresentableMorphism p :=
  ⟨restrictedCoyoneda ξ.base, ⟨ξ.base, ⟨Iso.refl _⟩⟩, associated hp ξ⟩

/-- Morphisms of formal objects are morphisms of the associated prorepresentable pairs: the
base components correspond by Yoneda, and the fibres over a fixed base map correspond by
`represented_hom_over_equiv`. -/
private lemma represented_hom_equiv
    {p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k}
    (hp : IsCofiberedInGroupoids p) (ξ η : FormalObject p) :
    Nonempty ((ξ ⟶ η) ≃ ProrepresentableMorphism.Hom
      (representedPair hp ξ) (representedPair hp η)) := by
  classical
  let e : (ξ.base ⟶ η.base) ≃ (restrictedCoyoneda η.base ⟶ restrictedCoyoneda ξ.base) :=
    Equiv.ofBijective _ (restrictedCoyonedaMap_bijective ξ.base η.base)
  let s : (ξ ⟶ η) ≃ (Σ f : ξ.base ⟶ η.base, {a : ξ ⟶ η // a.base = f}) :=
    { toFun := fun a => ⟨a.base, a, rfl⟩
      invFun := fun a => a.2.1
      left_inv := fun _ => rfl
      right_inv := by rintro ⟨f, a, rfl⟩; rfl }
  exact ⟨s.trans ((Equiv.sigmaCongr e (fun f =>
    Classical.choice (represented_hom_over_equiv hp ξ η f))).trans
    (homSigmaEquiv (representedPair hp ξ) (representedPair hp η)))⟩

/-- Restriction of morphisms into `F` along a natural transformation of functors on `𝒞_Λ`. -/
private def precompose {p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k}
    {U V : ArtinianLocalAlgCat.{u, v, w} Λ k ⥤ Type v} (a : U ⟶ V) :
    BasedFunctor (BasedCategory.ofFunctor (Functor.Elements.π V))
      (BasedCategory.ofFunctor p) ⥤
    BasedFunctor (BasedCategory.ofFunctor (Functor.Elements.π U))
      (BasedCategory.ofFunctor p) where
  obj φ := (ProrepresentableMorphism.elementsMap a).comp φ
  map t := BasedCategory.whiskerLeft (ProrepresentableMorphism.elementsMap a) t
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Restriction is contravariantly functorial in the natural transformation. -/
private lemma precompose_comp {p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k}
    {U V W : ArtinianLocalAlgCat.{u, v, w} Λ k ⥤ Type v} (a : U ⟶ V) (b : V ⟶ W) :
    precompose (p := p) (a ≫ b) = precompose b ⋙ precompose a := rfl

/-- Restriction along an isomorphism of functors is an equivalence of the categories of
morphisms into `F`. -/
private noncomputable def precomposeEquivalence
    {p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k}
    {U V : ArtinianLocalAlgCat.{u, v, w} Λ k ⥤ Type v} (e : U ≅ V) :
    BasedFunctor (BasedCategory.ofFunctor (Functor.Elements.π V))
      (BasedCategory.ofFunctor p) ≌
    BasedFunctor (BasedCategory.ofFunctor (Functor.Elements.π U))
      (BasedCategory.ofFunctor p) :=
  CategoryTheory.Equivalence.mk (precompose (p := p) e.hom) (precompose e.inv)
    (eqToIso (by rw [← precompose_comp, e.inv_hom_id]; rfl))
    (eqToIso (by rw [← precompose_comp, e.hom_inv_id]; rfl))

/-- A presentation of a prorepresentable pair by a formal object: an identification of its
functor with a restricted representable functor, under which its morphism to `F` becomes the
associated morphism of a formal object. -/
private structure Presentation {p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k}
    (hp : IsCofiberedInGroupoids p) (X : ProrepresentableMorphism p) where
  /-- The presenting formal object. -/
  object : FormalObject p
  /-- The identification of the functor with a restricted representable one. -/
  iso : X.functor ≅ restrictedCoyoneda object.base
  /-- The identification of the morphism to `F` with the associated morphism. -/
  comparison : (precompose iso.hom).obj (associated hp object) ≅ X.toF

/-- Every prorepresentable pair is presented by a formal object: prorepresentability supplies
the identification of the functor, and Stacks 06SK turns the restricted morphism into a formal
object over the representing algebra. -/
private lemma presentation_nonempty {p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k}
    (hp : IsCofiberedInGroupoids p) (X : ProrepresentableMorphism p) :
    Nonempty (Presentation hp X) := by
  classical
  obtain ⟨R, ⟨e⟩⟩ := X.prorepresentable
  let φ := (precompose e.inv).obj X.toF
  let E := representableMorphismFormalObjectEquivalence p hp R
  generalize hx : E.equivalence.functor.obj φ = x
  obtain ⟨⟨S, xl, xe, xt, xtl⟩, hS⟩ := x
  change S = R at hS
  subst S
  let ξ : FormalObject p := ⟨R, xl, xe, xt, xtl⟩
  let t : φ ≅ associated hp ξ :=
    E.equivalence.unitIso.app φ ≪≫ E.equivalence.inverse.mapIso (eqToIso hx) ≪≫
      inverseObjIsoAssociatedMorphism hp ξ E (chosenPushforwardsOfCofibered p hp)
  refine ⟨⟨ξ, e, (precompose e.hom).mapIso t.symm ≪≫ ?_⟩⟩
  change (precompose (e.hom ≫ e.inv)).obj X.toF ≅ X.toF
  rw [e.hom_inv_id]
  exact Iso.refl _

/-- Two presented prorepresentable pairs have the same morphisms as the represented pairs of
their presenting formal objects. -/
private lemma presentation_hom_equiv
    {p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k}
    {hp : IsCofiberedInGroupoids p} {X Y : ProrepresentableMorphism p}
    (PX : Presentation hp X) (PY : Presentation hp Y) :
    Nonempty (ProrepresentableMorphism.Hom X Y ≃
      ProrepresentableMorphism.Hom (representedPair hp PX.object)
        (representedPair hp PY.object)) := by
  classical
  let e := PY.iso.homCongr PX.iso
  let s := (homSigmaEquiv X Y).symm
  refine ⟨s.trans ((Equiv.sigmaCongr e (fun a => ?_)).trans
    (homSigmaEquiv (representedPair hp PX.object) (representedPair hp PY.object)))⟩
  let l : (precompose PY.iso.hom).obj ((precompose (e a)).obj
      (associated hp PX.object)) ≅ (precompose a).obj X.toF := by
    change (precompose (PY.iso.hom ≫ (PY.iso.inv ≫ a ≫ PX.iso.hom))).obj
      (associated hp PX.object) ≅ _
    simp only [Iso.hom_inv_id_assoc]
    exact (precompose a).mapIso PX.comparison
  exact ((precomposeEquivalence PY.iso).fullyFaithfulFunctor.homEquiv.trans
    (l.homCongr PY.comparison)).symm

/-- Yoneda reflects isomorphisms: a map of complete local algebras inducing an isomorphism of
the restricted representable functors is an isomorphism. -/
private lemma isIso_of_restrictedCoyonedaMap
    {R S : CompleteLocalAlgCat.{u, v, w} Λ k} (f : R ⟶ S)
    [IsIso (restrictedCoyonedaMap f)] : IsIso f := by
  obtain ⟨g, hg⟩ := (restrictedCoyonedaMap_bijective S R).surjective
    (inv (restrictedCoyonedaMap f))
  refine ⟨⟨g, ?_, ?_⟩⟩
  · apply (restrictedCoyonedaMap_bijective R R).injective
    change restrictedCoyonedaMap g ≫ restrictedCoyonedaMap f = 𝟙 _
    rw [hg, IsIso.inv_hom_id]
  · apply (restrictedCoyonedaMap_bijective S S).injective
    change restrictedCoyonedaMap f ≫ restrictedCoyonedaMap g = 𝟙 _
    rw [hg, IsIso.hom_inv_id]

/-- A presentation of the pair represented by a formal object presents it by an isomorphic
formal object. -/
private lemma presentation_object_iso
    {p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k}
    (hp : IsCofiberedInGroupoids p) (η : FormalObject p)
    (P : Presentation hp (representedPair hp η)) : Nonempty (P.object ≅ η) := by
  classical
  obtain ⟨f, hf⟩ := (restrictedCoyonedaMap_bijective P.object.base η.base).surjective P.iso.hom
  have hfi : IsIso (restrictedCoyonedaMap f) := by rw [hf]; infer_instance
  have fi := isIso_of_restrictedCoyonedaMap f
  have t : (ProrepresentableMorphism.elementsMap (restrictedCoyonedaMap f)).comp
      (associated hp P.object) ⟶ associated hp η := by
    rw [hf]
    exact P.comparison.hom
  let a := (Classical.choice (represented_hom_over_equiv hp P.object η f)).symm t
  let q := FormalObject.projection (p := p)
  have ha := isHomLift_projection_of_base_eq a.2
  have hc := isStronglyCocartesian_of_isCofiberedInGroupoids
    (formalObjectProjection_isCofiberedInGroupoids p hp) f a.1 ha
  have hi := IsStronglyCocartesian.isIso_of_base_isIso q f a.1
  exact ⟨asIso a.1⟩

/-- **Stacks 06HD.** Spelling out Stacks 06HC: the prorepresentable pairs over `p` carry a
category structure whose morphisms are `ProrepresentableMorphism.Hom`, and the category of
formal objects of `p` is equivalent to it. The hom equivalence is for the total categories, so
it pins down the morphisms between pairs with *different* prorepresentable functors, not only
those over a fixed one. -/
@[stacks 06HD "the equivalence with formal objects"]
theorem formalObjectsProrepresentableMorphismEquivalence
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k) (hp : IsCofiberedInGroupoids p) :
    ∃ c : Category (ProrepresentableMorphism p),
      letI := c
      c.Hom = (fun X Y => ProrepresentableMorphism.Hom X Y) ∧
      Nonempty (FormalObject p ≌ ProrepresentableMorphism p) := by
  classical
  let P (X : ProrepresentableMorphism p) : Presentation hp X :=
    Classical.choice (presentation_nonempty hp X)
  let O (X : ProrepresentableMorphism p) := (P X).object
  let e (X Y : ProrepresentableMorphism p) :
      ProrepresentableMorphism.Hom X Y ≃ (O X ⟶ O Y) :=
    (Classical.choice (presentation_hom_equiv (P X) (P Y))).trans
      (Classical.choice (represented_hom_equiv hp (O X) (O Y))).symm
  let c : Category (ProrepresentableMorphism p) :=
    { Hom := ProrepresentableMorphism.Hom
      id X := (e X X).symm (𝟙 (O X))
      comp {X Y Z} f g := (e X Z).symm (e X Y f ≫ e Y Z g)
      id_comp := by
        intro X Y f
        apply (e X Y).injective
        simp
      comp_id := by
        intro X Y f
        apply (e X Y).injective
        simp
      assoc := by
        intro W X Y Z f g h
        apply (e W Z).injective
        simp [Category.assoc] }
  let := c
  let T : ProrepresentableMorphism p ⥤ FormalObject p :=
    { obj := O
      map {X Y} f := e X Y f
      map_id X := (e X X).apply_symm_apply _
      map_comp {X Y Z} f g := (e X Z).apply_symm_apply _ }
  have hfull : T.Full := ⟨fun {X Y} => (e X Y).surjective⟩
  have hfaithful : T.Faithful := ⟨fun {X Y} => (e X Y).injective⟩
  have hsurj : T.EssSurj := ⟨fun ξ =>
    ⟨representedPair hp ξ, presentation_object_iso hp ξ (P (representedPair hp ξ))⟩⟩
  have heq : T.IsEquivalence := ⟨hfaithful, hfull, hsurj⟩
  exact ⟨c, rfl, ⟨T.asEquivalence.symm⟩⟩

end Deformation

end
