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

* `Deformation.ProrepresentableMorphism.category`: the category of pairs, with composite of
  `(a, s)` and `(b, t)` given by `b ≫ a` and `b^* s ≫ t`.
* `Deformation.formalObjectToProrepresentableMorphism`: the functor
  `ξ ↦ (underline R|_{𝒞_Λ}, ξ̲)` of Stacks 06HC, with the comparisons of Stacks 06SL
  (`ProrepresentableMorphism.associatedComparison`) on morphisms.
* `Deformation.formalObjectToProrepresentableMorphism_isEquivalence`: **Stacks 06HD**, that
  functor is an equivalence; `Deformation.formalObjectProrepresentableMorphismEquivalence` is
  the resulting equivalence.
* `Deformation.formalObjectsProrepresentableMorphismEquivalence`: the earlier, weaker form,
  with a transported category structure and an unspecified equivalence.

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

The comparison of a morphism of formal objects is characterized by its square with the level
maps (Stacks 06SL), which makes the functor `formalObjectToProrepresentableMorphism`
functorial. It is faithful and full because over a fixed base map every morphism `ξ̲ ⟶ η̲`
is the comparison of exactly one morphism of formal objects: pushing forward along the base
map reduces this to morphisms over the identity, where the equivalence of Stacks 06SK, which
is faithful and sends a comparison back to its morphism of formal objects up to the
evaluation isomorphism `associatedMorphismEvaluationIso`, decides it. It is essentially
surjective because every prorepresentable functor is isomorphic to a restricted
representable one, over which Stacks 06SK produces a formal object.

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

/-- Some category structure on the prorepresentable pairs over `p`, with hom types
`ProrepresentableMorphism.Hom`, makes them equivalent to the formal objects of `p`. The
structure here is transported from formal objects along non-canonical hom bijections, and the
equivalence is not a specified functor, so this is weaker than Stacks 06HD; the statement of
06HD is `formalObjectToProrepresentableMorphism_isEquivalence`, for the natural composition of
pairs (`ProrepresentableMorphism.category`) and the explicit functor
`formalObjectToProrepresentableMorphism`. -/
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


/-! ### The category of prorepresentable pairs -/

section Category

-- The comparisons below compose point inclusions of associated morphisms with components of
-- based natural transformations, whose objects are the objects of the category of elements
-- of a restricted representable functor only after unfolding `BasedCategory.ofFunctor`; this
-- lets `simp` and `rw` see through that presentation, as in `AssociatedMorphismMap`.
attribute [local implicit_reducible] Deformation.restrictedRepresentable
  CategoryTheory.BasedCategory.ofFunctor CategoryTheory.BasedFunctor.comp

variable {p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k}

namespace ProrepresentableMorphism

/-- Morphisms of prorepresentable pairs are equal when their natural transformations are equal
and their comparisons are, after identifying the restrictions along the two transformations. -/
theorem Hom.ext_heq {X Y : ProrepresentableMorphism p} {f g : Hom X Y} (h : f.base = g.base)
    (h' : f.comparison ≍ g.comparison) : f = g := by
  cases f
  cases g
  dsimp only at h h'
  subst h
  obtain rfl := eq_of_heq h'
  rfl

/-- Equal morphisms of prorepresentable pairs have equal natural transformations and
heterogeneously equal comparisons. -/
theorem Hom.base_eq_and_comparison_heq {X Y : ProrepresentableMorphism p} {f g : Hom X Y}
    (h : f = g) : f.base = g.base ∧ f.comparison ≍ g.comparison := by
  subst h
  exact ⟨rfl, HEq.rfl⟩

/-- **Stacks 06HD.** The category of pairs `(U, U → F)` of a prorepresentable functor and a
morphism to `F` over `𝒞_Λ`. The identity of `(U, φ)` is the identity transformation with the
identity comparison; the composite of `(a, s) : (U, φ) ⟶ (V, ψ)` and
`(b, t) : (V, ψ) ⟶ (W, χ)` is `b ≫ a : W ⟶ U` with the comparison `b^* s` followed by `t`. -/
@[stacks 06HD "the category of pairs of a prorepresentable functor and a morphism to `F`"]
instance category : Category (ProrepresentableMorphism p) where
  Hom := Hom
  id X := ⟨𝟙 X.functor, 𝟙 X.toF⟩
  comp f g := ⟨g.base ≫ f.base,
    BasedCategory.whiskerLeft (elementsMap g.base) f.comparison ≫ g.comparison⟩
  id_comp f := Hom.ext_heq (Category.comp_id _) (heq_of_eq (by ext; exact Category.id_comp _))
  comp_id f := Hom.ext_heq (Category.id_comp _) (heq_of_eq (by ext; exact Category.comp_id _))
  assoc f g h := Hom.ext_heq (Category.assoc _ _ _).symm
    (heq_of_eq (by ext; exact Category.assoc _ _ _))

/-- The pair of a formal object `ξ` (Stacks 06HC): the restriction to `𝒞_Λ` of the functor
represented by the base of `ξ`, together with the associated morphism `ξ̲`, for the canonical
choice of pushforwards supplied by the cofibered condition. -/
noncomputable abbrev ofFormalObject (hp : IsCofiberedInGroupoids p) (ξ : FormalObject p) :
    ProrepresentableMorphism p :=
  ⟨restrictedCoyoneda ξ.base, ⟨ξ.base, ⟨Iso.refl _⟩⟩,
    (associatedMorphism hp ξ (chosenPushforwardsOfCofibered p hp)).toBasedFunctor⟩

/-- **Stacks 06SL.** The comparison between the associated morphisms of two formal objects
induced by a morphism `a` of formal objects: the natural isomorphism of Stacks 06SL from the
restriction of `ξ̲` along `a` to `η̲`, whose component at an Artinian point is the pushforward
of the corresponding level map of `a`. -/
noncomputable def associatedComparison (hp : IsCofiberedInGroupoids p) {ξ η : FormalObject p}
    (a : ξ ⟶ η) :
    (elementsMap (restrictedCoyonedaMap a.base)).comp (ofFormalObject hp ξ).toF ⟶
      (ofFormalObject hp η).toF :=
  (Classical.choose (associatedMorphism_map hp a (chosenPushforwardsOfCofibered p hp))).hom

/-- The morphism of pairs induced by a morphism `a` of formal objects: the natural
transformation `restrictedCoyonedaMap a.base` of the represented functors, with the comparison
of Stacks 06SL. -/
noncomputable def homOfFormalObject (hp : IsCofiberedInGroupoids p) {ξ η : FormalObject p}
    (a : ξ ⟶ η) : ofFormalObject hp ξ ⟶ ofFormalObject hp η :=
  ⟨restrictedCoyonedaMap a.base, associatedComparison hp a⟩

end ProrepresentableMorphism

open ProrepresentableMorphism

/-- The point inclusions of the associated morphism, for the canonical pushforwards. -/
private noncomputable abbrev assoc (hp : IsCofiberedInGroupoids p) (ξ : FormalObject p) :=
  associatedMorphism hp ξ (chosenPushforwardsOfCofibered p hp)

/-- `τ` is the comparison of Stacks 06SL of the morphism of formal objects `a`, over the base
map `f`: at every Artinian point its component, after the point inclusion of `ξ̲`, is the level
map of `a` followed by the point inclusion of `η̲`. -/
private def IsComparison (hp : IsCofiberedInGroupoids p) {ξ η : FormalObject p} (a : ξ ⟶ η)
    {f : ξ.base ⟶ η.base}
    (τ : (elementsMap (restrictedCoyonedaMap f)).comp (associated hp ξ) ⟶ associated hp η) :
    Prop :=
  ∀ α : (restrictedCoyoneda η.base).Elements,
    ∃ h : (assoc hp ξ).level ((elementsMap (restrictedCoyonedaMap f)).obj α) =
        (assoc hp η).level α,
      (assoc hp ξ).pointInclusion ((elementsMap (restrictedCoyonedaMap f)).obj α) ≫
          τ.toNatTrans.app α =
        a.app _ ≫ eqToHom (congrArg η.level h) ≫ (assoc hp η).pointInclusion α

/-- The comparison property transports along an identification of base maps. -/
private lemma IsComparison.congr {hp : IsCofiberedInGroupoids p} {ξ η : FormalObject p}
    {a : ξ ⟶ η} {f f' : ξ.base ⟶ η.base}
    {τ : (elementsMap (restrictedCoyonedaMap f)).comp (associated hp ξ) ⟶ associated hp η}
    {τ' : (elementsMap (restrictedCoyonedaMap f')).comp (associated hp ξ) ⟶ associated hp η}
    (h : IsComparison hp a τ) (hf : f = f') (hτ : τ ≍ τ') : IsComparison hp a τ' := by
  subst hf
  obtain rfl := eq_of_heq hτ
  exact h

/-- A comparison along one natural transformation transports to an equal one. -/
private lemma exists_heq_comparison {U V : ArtinianLocalAlgCat.{u, v, w} Λ k ⥤ Type v}
    {b b' : U ⟶ V} (h : b = b')
    {G : BasedFunctor (BasedCategory.ofFunctor (Functor.Elements.π V))
      (BasedCategory.ofFunctor p)}
    {H : BasedFunctor (BasedCategory.ofFunctor (Functor.Elements.π U))
      (BasedCategory.ofFunctor p)}
    (c : (elementsMap b').comp G ⟶ H) : ∃ c' : (elementsMap b).comp G ⟶ H, c' ≍ c := by
  subst h
  exact ⟨c, HEq.rfl⟩

/-- **Stacks 06SL.** Every morphism of formal objects has a comparison, and it is an
isomorphism. -/
private lemma exists_isComparison (hp : IsCofiberedInGroupoids p) {ξ η : FormalObject p}
    (a : ξ ⟶ η) {f : ξ.base ⟶ η.base} (hf : a.base = f) :
    ∃ τ : (elementsMap (restrictedCoyonedaMap f)).comp (associated hp ξ) ≅ associated hp η,
      IsComparison hp a τ.hom := by
  subst hf
  obtain ⟨τ, hτ⟩ := associatedMorphism_map hp a (chosenPushforwardsOfCofibered p hp)
  exact ⟨τ, hτ⟩

/-- `associatedComparison` is a comparison. -/
private lemma isComparison_associatedComparison (hp : IsCofiberedInGroupoids p)
    {ξ η : FormalObject p} (a : ξ ⟶ η) :
    IsComparison hp a (associatedComparison hp a) :=
  Classical.choose_spec (associatedMorphism_map hp a (chosenPushforwardsOfCofibered p hp))

/-- **Stacks 06SL.** The comparison of a morphism of formal objects over a given base map is
unique: the point inclusions of `ξ̲` are strongly cocartesian. -/
private lemma IsComparison.ext {hp : IsCofiberedInGroupoids p} {ξ η : FormalObject p}
    {a : ξ ⟶ η} {f : ξ.base ⟶ η.base}
    {τ σ : (elementsMap (restrictedCoyonedaMap f)).comp (associated hp ξ) ⟶ associated hp η}
    (hτ : IsComparison hp a τ) (hσ : IsComparison hp a σ) : τ = σ := by
  ext α
  obtain ⟨h₁, s₁⟩ := hτ α
  obtain ⟨h₂, s₂⟩ := hσ α
  let β := (elementsMap (restrictedCoyonedaMap f)).obj α
  have := associatedPointInclusion_stronglyCocartesian hp (chosenPushforwardsOfCofibered p hp)
    (assoc hp ξ) β
  have cancel : ∀ ψ ψ' : (associated hp ξ).obj β ⟶ (associated hp η).obj α,
      p.IsHomLift (𝟙 β.1) ψ → p.IsHomLift (𝟙 β.1) ψ' →
      (assoc hp ξ).pointInclusion β ≫ ψ = (assoc hp ξ).pointInclusion β ≫ ψ' → ψ = ψ' := by
    intro ψ ψ' hψ hψ' hfac
    have := hψ
    have := hψ'
    exact Functor.IsStronglyCocartesian.ext p ((assoc hp ξ).factor β)
      ((assoc hp ξ).pointInclusion β) (𝟙 β.1) hfac
  exact cancel _ _ (τ.isHomLift' α) (σ.isHomLift' α) (s₁.trans s₂.symm)

/-- The identity of the associated morphism is the comparison of the identity. -/
private lemma isComparison_id (hp : IsCofiberedInGroupoids p) (ξ : FormalObject p) :
    IsComparison hp (𝟙 ξ) (f := 𝟙 ξ.base) (𝟙 (associated hp ξ)) := by
  intro α
  refine ⟨rfl, ?_⟩
  change (assoc hp ξ).pointInclusion α ≫ 𝟙 _ = 𝟙 _ ≫ 𝟙 _ ≫ (assoc hp ξ).pointInclusion α
  simp

/-- Level maps of a composite, with casts of levels. -/
private lemma app_comp_eqToHom {ξ η ζ : FormalObject p} (a : ξ ⟶ η) (b : η ⟶ ζ) {n m l : ℕ}
    (e : n = m) (e' : m = l) {Z : F} (i : ζ.level l ⟶ Z) :
    (a ≫ b).app n ≫ eqToHom (congrArg ζ.level (e.trans e')) ≫ i =
      a.app n ≫ eqToHom (congrArg η.level e) ≫ b.app m ≫ eqToHom (congrArg ζ.level e') ≫ i := by
  subst e e'
  simp only [eqToHom_refl, Category.id_comp]
  exact Category.assoc _ _ _

/-- Comparisons compose: the restriction of the comparison of `a` followed by the comparison
of `b` is a comparison of `a ≫ b`. -/
private lemma isComparison_comp (hp : IsCofiberedInGroupoids p) {ξ η ζ : FormalObject p}
    {a : ξ ⟶ η} {b : η ⟶ ζ} {f : ξ.base ⟶ η.base} {g : η.base ⟶ ζ.base}
    {τ : (elementsMap (restrictedCoyonedaMap f)).comp (associated hp ξ) ⟶ associated hp η}
    {σ : (elementsMap (restrictedCoyonedaMap g)).comp (associated hp η) ⟶ associated hp ζ}
    (hτ : IsComparison hp a τ) (hσ : IsComparison hp b σ) :
    IsComparison hp (a ≫ b) (f := f ≫ g)
      (BasedCategory.whiskerLeft (elementsMap (restrictedCoyonedaMap g)) τ ≫ σ) := by
  intro α
  obtain ⟨h₁, s₁⟩ := hτ ((elementsMap (restrictedCoyonedaMap g)).obj α)
  obtain ⟨h₂, s₂⟩ := hσ α
  refine ⟨h₁.trans h₂, ?_⟩
  let β := (elementsMap (restrictedCoyonedaMap g)).obj α
  calc _ = (assoc hp ξ).pointInclusion ((elementsMap (restrictedCoyonedaMap f)).obj β) ≫
          τ.toNatTrans.app β ≫ σ.toNatTrans.app α := rfl
    _ = ((assoc hp ξ).pointInclusion ((elementsMap (restrictedCoyonedaMap f)).obj β) ≫
          τ.toNatTrans.app β) ≫ σ.toNatTrans.app α := (Category.assoc _ _ _).symm
    _ = (a.app _ ≫ eqToHom (congrArg η.level h₁) ≫ (assoc hp η).pointInclusion β) ≫
          σ.toNatTrans.app α := by rw [s₁]
    _ = a.app _ ≫ eqToHom (congrArg η.level h₁) ≫
          ((assoc hp η).pointInclusion β ≫ σ.toNatTrans.app α) := by
        simp only [Category.assoc]
    _ = a.app _ ≫ eqToHom (congrArg η.level h₁) ≫
          (b.app _ ≫ eqToHom (congrArg ζ.level h₂) ≫ (assoc hp ζ).pointInclusion α) := by
        rw [s₂]
    _ = _ := (app_comp_eqToHom a b h₁ h₂ _).symm

namespace ProrepresentableMorphism

/-- The comparison of an identity of formal objects is the identity. -/
theorem homOfFormalObject_id (hp : IsCofiberedInGroupoids p) (ξ : FormalObject p) :
    homOfFormalObject hp (𝟙 ξ) = 𝟙 (ofFormalObject hp ξ) :=
  Hom.ext_heq rfl (heq_of_eq
    ((isComparison_associatedComparison hp (𝟙 ξ)).ext (isComparison_id hp ξ)))

/-- Comparisons of morphisms of formal objects compose. -/
theorem homOfFormalObject_comp (hp : IsCofiberedInGroupoids p) {ξ η ζ : FormalObject p}
    (a : ξ ⟶ η) (b : η ⟶ ζ) :
    homOfFormalObject hp (a ≫ b) = homOfFormalObject hp a ≫ homOfFormalObject hp b :=
  Hom.ext_heq rfl (heq_of_eq ((isComparison_associatedComparison hp (a ≫ b)).ext
    (isComparison_comp hp (isComparison_associatedComparison hp a)
      (isComparison_associatedComparison hp b))))

end ProrepresentableMorphism

/-- **Stacks 06HD.** The functor from formal objects of `p` to prorepresentable pairs of Stacks
06HC, `ξ ↦ (underline R|_{𝒞_Λ}, ξ̲)` with `R` the base of `ξ`: a morphism `a` of formal objects
goes to the natural transformation induced by its base map together with the comparison of
Stacks 06SL. -/
@[stacks 06HD "the functor `ξ ↦ (R|_{𝒞_Λ}, ξ̲)`"]
noncomputable def formalObjectToProrepresentableMorphism
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k) (hp : IsCofiberedInGroupoids p) :
    FormalObject p ⥤ ProrepresentableMorphism p where
  obj ξ := ofFormalObject hp ξ
  map a := homOfFormalObject hp a
  map_id ξ := homOfFormalObject_id hp ξ
  map_comp a b := homOfFormalObject_comp hp a b

/-- A square of arrows from a level of a formal object to the value of an associated morphism,
in the shape used by `existsUnique_vertical`. -/
private lemma square_aux {A₁ A₂ B₁ B₂ B₂' P₁ P₂ Q₁ Q₂ : F} {t₁ : A₁ ⟶ B₁} {i₁ : B₁ ⟶ P₁}
    {L₁ : P₁ ⟶ Q₁} {M : Q₁ ⟶ Q₂} {s : P₁ ⟶ P₂} {L₂ : P₂ ⟶ Q₂} {φℓ : B₁ ⟶ B₂} {e : B₂ ⟶ B₂'}
    {i₂ : B₂' ⟶ P₂} {φn : A₁ ⟶ A₂} {t₂ : A₂ ⟶ B₂'} (mc : s ≫ L₂ = L₁ ≫ M)
    (sq : i₁ ≫ s = φℓ ≫ e ≫ i₂) (tr : t₁ ≫ φℓ ≫ e ≫ i₂ ≫ L₂ = φn ≫ t₂ ≫ i₂ ≫ L₂) :
    (t₁ ≫ i₁ ≫ L₁) ≫ M = φn ≫ t₂ ≫ i₂ ≫ L₂ := by
  simp only [Category.assoc]
  rw [← mc, reassoc_of% sq, tr]

/-- Conjugating a square by isomorphisms given by their two components. -/
private lemma conj_aux {X Y X₂ Y₂ : F} {a : X ⟶ Y} {a' : Y ⟶ X} {b : X₂ ⟶ Y₂} {b' : Y₂ ⟶ X₂}
    {M : X ⟶ X₂} {φ : Y ⟶ Y₂} (ha : a ≫ a' = 𝟙 X) (hb : b' ≫ b = 𝟙 Y₂)
    (h : a' ≫ M = φ ≫ b') : M ≫ b = a ≫ φ := by
  calc M ≫ b = (a ≫ a') ≫ M ≫ b := by rw [ha, Category.id_comp]
    _ = a ≫ (a' ≫ M) ≫ b := by simp only [Category.assoc]
    _ = a ≫ φ := by rw [h, Category.assoc, hb, Category.comp_id]

/-- A morphism in the fibre of formal objects over `S` has base the identity, up to the casts of
its endpoints. -/
private lemma fiber_hom_base {S : CompleteLocalAlgCat.{u, v, w} Λ k}
    {A B : (FormalObject.projection (p := p)).Fiber S} (ψ : A ⟶ B) :
    ψ.1.base = eqToHom (A.2.trans B.2.symm) := by
  have := ψ.2
  have h := IsHomLift.fac' (FormalObject.projection (p := p)) (𝟙 S) ψ.1
  simpa using h

/-- The components of the evaluation isomorphism compose to the identity. -/
private lemma evaluationIso_hom_inv_app (hp : IsCofiberedInGroupoids p) (ξ : FormalObject p)
    (E : RepresentableMorphismFormalObjectEquivalence p ξ.base) (n : ℕ) :
    (associatedMorphismEvaluationIso hp ξ E (chosenPushforwardsOfCofibered p hp)).hom.1.app n ≫
      (associatedMorphismEvaluationIso hp ξ E (chosenPushforwardsOfCofibered p hp)).inv.1.app n =
        𝟙 _ :=
  congrArg (fun ψ => ψ.1.app n)
    (associatedMorphismEvaluationIso hp ξ E (chosenPushforwardsOfCofibered p hp)).hom_inv_id

/-- The components of the evaluation isomorphism compose to the identity. -/
private lemma evaluationIso_inv_hom_app (hp : IsCofiberedInGroupoids p) (ξ : FormalObject p)
    (E : RepresentableMorphismFormalObjectEquivalence p ξ.base) (n : ℕ) :
    (associatedMorphismEvaluationIso hp ξ E (chosenPushforwardsOfCofibered p hp)).inv.1.app n ≫
      (associatedMorphismEvaluationIso hp ξ E (chosenPushforwardsOfCofibered p hp)).hom.1.app n =
        𝟙 _ :=
  congrArg (fun ψ => ψ.1.app n)
    (associatedMorphismEvaluationIso hp ξ E (chosenPushforwardsOfCofibered p hp)).inv_hom_id

/-- The inverse of the evaluation isomorphism at level `n` is the canonical arrow from `ξ_n` to
the value of `ξ̲` at the `n`-th quotient point, followed by the evaluation isomorphism of `E`. -/
private lemma evaluationIso_inv_app (hp : IsCofiberedInGroupoids p) (ξ : FormalObject p)
    (E : RepresentableMorphismFormalObjectEquivalence p ξ.base) (n : ℕ)
    (h : (assoc hp ξ).level
      (Functor.elementsMk _ (AdicTruncation.obj ξ.base n) (E.quotientPoint n)) ≤ n) :
    transitionTo ξ h ≫
        (assoc hp ξ).pointInclusion
          (Functor.elementsMk _ (AdicTruncation.obj ξ.base n) (E.quotientPoint n)) ≫
          (E.levelIso (associated hp ξ) n).hom =
      (associatedMorphismEvaluationIso hp ξ E
        (chosenPushforwardsOfCofibered p hp)).inv.1.app n := by
  have e := associatedMorphismEvaluationIso_hom_app hp ξ E
    (chosenPushforwardsOfCofibered p hp) n h
  calc _ = (transitionTo ξ h ≫ (assoc hp ξ).pointInclusion
          (Functor.elementsMk _ (AdicTruncation.obj ξ.base n) (E.quotientPoint n)) ≫
            (E.levelIso (associated hp ξ) n).hom) ≫
        (associatedMorphismEvaluationIso hp ξ E (chosenPushforwardsOfCofibered p hp)).hom.1.app n ≫
        (associatedMorphismEvaluationIso hp ξ E
          (chosenPushforwardsOfCofibered p hp)).inv.1.app n := by
        rw [evaluationIso_hom_inv_app, Category.comp_id]
    _ = _ := by
        simp only [Category.assoc]
        rw [reassoc_of% e]
        exact Category.id_comp _

/-- **Stacks 06SK, 06SL.** Over a fixed representing algebra, morphisms of formal objects over
the identity correspond to morphisms of their associated morphisms: every morphism
`ξ̲ ⟶ η̲` is the comparison of exactly one such morphism of formal objects. The proof goes
through the equivalence of Stacks 06SK, which is faithful and sends the comparison of a
morphism of formal objects to that morphism, up to the evaluation isomorphisms. -/
private lemma existsUnique_vertical (hp : IsCofiberedInGroupoids p) (z η : FormalObject p)
    (hb : z.base = η.base)
    (t : (elementsMap (restrictedCoyonedaMap (eqToHom hb))).comp (associated hp z) ⟶
      associated hp η) :
    ∃! φ : z ⟶ η, φ.base = eqToHom hb ∧ IsComparison hp φ t := by
  classical
  obtain ⟨S, zl, ze, zt, ztl⟩ := z
  obtain ⟨S', yl, ye, yt, ytl⟩ := η
  dsimp only at hb
  subst hb
  set z : FormalObject p := ⟨S, zl, ze, zt, ztl⟩ with hz_def
  set η : FormalObject p := ⟨S, yl, ye, yt, ytl⟩ with hη_def
  let E := representableMorphismFormalObjectEquivalence p hp S
  let θz := associatedMorphismEvaluationIso hp z E (chosenPushforwardsOfCofibered p hp)
  let θη := associatedMorphismEvaluationIso hp η E (chosenPushforwardsOfCofibered p hp)
  let t' : associated hp z ⟶ associated hp η := t
  have N : ∀ (s : associated hp z ⟶ associated hp η) (φ : z ⟶ η) (hφb : φ.base = 𝟙 S),
      IsComparison hp φ (f := eqToHom rfl) s →
      E.equivalence.functor.map s ≫ θη.hom =
        θz.hom ≫ (⟨φ, isHomLift_projection_of_base_eq hφb⟩ :
          (Functor.Fiber.mk rfl : (FormalObject.projection (p := p)).Fiber z.base) ⟶
            (Functor.Fiber.mk rfl : (FormalObject.projection (p := p)).Fiber η.base)) := by
    intro s φ hφb hφ
    apply Functor.Fiber.hom_ext
    apply FormalObject.Hom.ext
    · exact (fiber_hom_base (E.equivalence.functor.map s ≫ θη.hom)).trans
        (fiber_hom_base (θz.hom ≫ (⟨φ, isHomLift_projection_of_base_eq hφb⟩ :
          (Functor.Fiber.mk rfl : (FormalObject.projection (p := p)).Fiber z.base) ⟶
            (Functor.Fiber.mk rfl : (FormalObject.projection (p := p)).Fiber η.base)))).symm
    · intro n
      change (E.equivalence.functor.map s).1.app n ≫ θη.hom.1.app n = θz.hom.1.app n ≫ φ.app n
      let q : (restrictedCoyoneda S).Elements :=
        Functor.elementsMk _ (AdicTruncation.obj S n) (E.quotientPoint n)
      have hz : (assoc hp z).level q ≤ n := ((assoc hp z).factor_spec q).2.1 n
        (maximalIdeal_adicTruncation_pow_succ_eq_bot S n)
      have hη : (assoc hp η).level q ≤ n := ((assoc hp η).factor_spec q).2.1 n
        (maximalIdeal_adicTruncation_pow_succ_eq_bot S n)
      obtain ⟨hl, sq⟩ := hφ q
      have hl' : (assoc hp z).level q = (assoc hp η).level q := hl
      have sq' : (assoc hp z).pointInclusion q ≫ s.toNatTrans.app q =
          φ.app ((assoc hp z).level q) ≫ eqToHom (congrArg η.level hl') ≫
            (assoc hp η).pointInclusion q := sq
      have mc : s.toNatTrans.app q ≫ (E.levelIso (associated hp η) n).hom =
          (E.levelIso (associated hp z) n).hom ≫ (E.equivalence.functor.map s).1.app n :=
        E.map_comm s n
      have Bz : transitionTo z hz ≫ (assoc hp z).pointInclusion q ≫
          (E.levelIso (associated hp z) n).hom = θz.inv.1.app n :=
        evaluationIso_inv_app hp z E n hz
      have Bη : transitionTo η hη ≫ (assoc hp η).pointInclusion q ≫
          (E.levelIso (associated hp η) n).hom = θη.inv.1.app n :=
        evaluationIso_inv_app hp η E n hη
      have hiz : θz.hom.1.app n ≫ θz.inv.1.app n = 𝟙 _ := evaluationIso_hom_inv_app hp z E n
      have hiη : θη.inv.1.app n ≫ θη.hom.1.app n = 𝟙 _ := evaluationIso_inv_hom_app hp η E n
      have key : θz.inv.1.app n ≫ (E.equivalence.functor.map s).1.app n =
          φ.app n ≫ θη.inv.1.app n :=
        (congrArg (· ≫ (E.equivalence.functor.map s).1.app n) Bz.symm).trans
          ((square_aux mc sq' (transitionTo_comp_app_eqToHom φ hl' hz hη _)).trans
            (congrArg (φ.app n ≫ ·) Bη))
      exact conj_aux hiz hiη key
  let ψ := θz.inv ≫ E.equivalence.functor.map t' ≫ θη.hom
  have hψb : ψ.1.base = 𝟙 S := (fiber_hom_base ψ).trans (eqToHom_refl _ _)
  refine ⟨ψ.1, ⟨fiber_hom_base ψ, ?_⟩, ?_⟩
  · obtain ⟨s, hs⟩ := exists_isComparison hp ψ.1 (f := eqToHom rfl) (fiber_hom_base ψ)
    have hN := N s.hom ψ.1 hψb hs
    have h2 : E.equivalence.functor.map t' ≫ θη.hom = θz.hom ≫ ψ :=
      (Iso.hom_inv_id_assoc θz _).symm
    have h3 : E.equivalence.functor.map s.hom ≫ θη.hom =
        E.equivalence.functor.map t' ≫ θη.hom := hN.trans h2.symm
    have hst : s.hom = t' :=
      E.equivalence.functor.map_injective ((Iso.cancel_iso_hom_right _ _ θη).mp h3)
    rw [hst] at hs
    exact hs
  · rintro φ ⟨hφb, hφ⟩
    have hφ1 : φ.base = 𝟙 S := hφb.trans (eqToHom_refl _ _)
    have hN := N t' φ hφ1 hφ
    exact congrArg Subtype.val ((Iso.eq_inv_comp θz).mpr hN.symm)

/-- Restricting a based natural isomorphism along a functor, then composing with the inverse,
gives the identity. -/
private lemma whiskerLeft_hom_inv_comp
    {𝒳 𝒴 𝒵 : BasedCategory (ArtinianLocalAlgCat.{u, v, w} Λ k)} (K : 𝒳 ⥤ᵇ 𝒴) {G H : 𝒴 ⥤ᵇ 𝒵}
    (e : G ≅ H) {L : 𝒳 ⥤ᵇ 𝒵} (c : K.comp G ⟶ L) :
    BasedCategory.whiskerLeft K e.hom ≫ BasedCategory.whiskerLeft K e.inv ≫ c = c := by
  rw [← Category.assoc]
  convert Category.id_comp c
  ext x
  exact congrArg (fun α => α.toNatTrans.app (K.obj x)) e.hom_inv_id

/-- Restricting a based natural isomorphism along a functor, then composing with the inverse,
gives the identity. -/
private lemma whiskerLeft_inv_hom_comp
    {𝒳 𝒴 𝒵 : BasedCategory (ArtinianLocalAlgCat.{u, v, w} Λ k)} (K : 𝒳 ⥤ᵇ 𝒴) {G H : 𝒴 ⥤ᵇ 𝒵}
    (e : G ≅ H) {L : 𝒳 ⥤ᵇ 𝒵} (c : K.comp H ⟶ L) :
    BasedCategory.whiskerLeft K e.inv ≫ BasedCategory.whiskerLeft K e.hom ≫ c = c :=
  whiskerLeft_hom_inv_comp K e.symm c

/-- **Stacks 06HC, 06SL.** Every morphism from the restriction of `ξ̲` along a base map `f`
to `η̲` is the comparison of exactly one morphism of formal objects over `f`. Pushing `ξ`
forward along `f` reduces this to morphisms over the identity, `existsUnique_vertical`. -/
private lemma existsUnique_isComparison (hp : IsCofiberedInGroupoids p) (ξ η : FormalObject p)
    (f : ξ.base ⟶ η.base)
    (t : (elementsMap (restrictedCoyonedaMap f)).comp (associated hp ξ) ⟶ associated hp η) :
    ∃! a : ξ ⟶ η, a.base = f ∧ IsComparison hp a t := by
  classical
  let q := FormalObject.projection (p := p)
  have hq := formalObjectProjection_isCofiberedInGroupoids p hp
  obtain ⟨z, j, hj⟩ : ∃ z : FormalObject p, ∃ j : ξ ⟶ z, q.IsHomLift f j :=
    exists_pushforward hq f ξ rfl
  have hzb : z.base = η.base := IsHomLift.codomain_eq q f j
  have hfj : f = j.base ≫ eqToHom hzb := by
    have h := IsHomLift.fac q f j
    simpa [q] using h
  have hc := isStronglyCocartesian_of_isCofiberedInGroupoids hq f j hj
  obtain ⟨τ, hτ⟩ := exists_isComparison hp j rfl
  obtain ⟨t'', ht''⟩ := exists_heq_comparison (congrArg restrictedCoyonedaMap hfj).symm t
  have hat'' : ∀ a : ξ ⟶ η, a.base = f → IsComparison hp a t → IsComparison hp a t'' :=
    fun a _ h => h.congr hfj ht''.symm
  let t' : (elementsMap (restrictedCoyonedaMap (eqToHom hzb))).comp (associated hp z) ⟶
      associated hp η :=
    BasedCategory.whiskerLeft (elementsMap (restrictedCoyonedaMap (eqToHom hzb))) τ.inv ≫ t''
  obtain ⟨φ, ⟨hφb, hφ⟩, huniq⟩ := existsUnique_vertical hp z η hzb t'
  refine ⟨j ≫ φ, ⟨?_, ?_⟩, ?_⟩
  · change j.base ≫ φ.base = f
    rw [hφb, hfj]
  · have h := isComparison_comp hp hτ hφ
    refine h.congr hfj.symm ?_
    refine HEq.trans (heq_of_eq ?_) ht''
    exact whiskerLeft_hom_inv_comp (elementsMap (restrictedCoyonedaMap (eqToHom hzb))) τ t''
  · rintro a ⟨ha, hat⟩
    have hlift : q.IsHomLift f a := isHomLift_projection_of_base_eq ha
    obtain ⟨b, ⟨hb, hfac⟩, _⟩ := IsStronglyCocartesian.universal_property
      q f j (𝟙 η.base) f (Category.comp_id f).symm a
    have hbb : b.base = eqToHom hzb := by
      have h := IsHomLift.fac' q (𝟙 η.base) b
      simpa [q] using h
    obtain ⟨s, hs⟩ := exists_isComparison hp b hbb
    have h := isComparison_comp hp hτ hs
    rw [hfac] at h
    have e : BasedCategory.whiskerLeft (elementsMap (restrictedCoyonedaMap (eqToHom hzb)))
        τ.hom ≫ s.hom = t'' := h.ext (hat'' a ha hat)
    have hst : s.hom = t' := by
      change s.hom = BasedCategory.whiskerLeft _ τ.inv ≫ t''
      rw [← e]
      exact (whiskerLeft_inv_hom_comp _ τ s.hom).symm
    rw [hst] at hs
    rw [← hfac, huniq b ⟨hbb, hs⟩]

/-- Whiskering a cast of based functors gives a cast. -/
private lemma whiskerLeft_eqToHom_comp_id_heq
    {𝒳 𝒴 𝒵 : BasedCategory (ArtinianLocalAlgCat.{u, v, w} Λ k)} (K : 𝒳 ⥤ᵇ 𝒴) {G H : 𝒴 ⥤ᵇ 𝒵}
    (h : G = H) : BasedCategory.whiskerLeft K (eqToHom h) ≫ 𝟙 (K.comp H) ≍ 𝟙 (K.comp H) := by
  subst h
  exact heq_of_eq (by ext; simp; rfl)

/-- The identity whiskered and followed by a cast is a cast. -/
private lemma whiskerLeft_id_comp_eqToHom_heq
    {𝒳 𝒴 𝒵 : BasedCategory (ArtinianLocalAlgCat.{u, v, w} Λ k)} (K : 𝒳 ⥤ᵇ 𝒴) (G : 𝒴 ⥤ᵇ 𝒵)
    {H : 𝒳 ⥤ᵇ 𝒵} (h : K.comp G = H) :
    BasedCategory.whiskerLeft K (𝟙 G) ≫ eqToHom h ≍ 𝟙 H := by
  subst h
  exact heq_of_eq (by ext; simp; rfl)

/-- Replacing the functor of a prorepresentable pair by an isomorphic one, and the morphism to
`F` by its restriction along the isomorphism, gives an isomorphic pair. -/
private def isoOfFunctorIso (Y : ProrepresentableMorphism p)
    {U : ArtinianLocalAlgCat.{u, v, w} Λ k ⥤ Type v} (hU : IsProrepresentable U)
    (e : U ≅ Y.functor) :
    (⟨U, hU, (elementsMap e.hom).comp Y.toF⟩ : ProrepresentableMorphism p) ≅ Y where
  hom := ⟨e.inv, eqToHom (congrArg (fun b => (elementsMap b).comp Y.toF) e.inv_hom_id)⟩
  inv := ⟨e.hom, 𝟙 _⟩
  hom_inv_id := Hom.ext_heq e.hom_inv_id (whiskerLeft_eqToHom_comp_id_heq (elementsMap e.hom)
    (congrArg (fun b => (elementsMap b).comp Y.toF) e.inv_hom_id))
  inv_hom_id := Hom.ext_heq e.inv_hom_id (whiskerLeft_id_comp_eqToHom_heq (elementsMap e.inv)
    ((elementsMap e.hom).comp Y.toF) (congrArg (fun b => (elementsMap b).comp Y.toF) e.inv_hom_id))

/-- A pair is isomorphic to the pair with the same functor and an isomorphic morphism to
`F`. -/
private def isoOfToFIso (X : ProrepresentableMorphism p)
    (ψ : BasedFunctor (BasedCategory.ofFunctor (Functor.Elements.π X.functor))
      (BasedCategory.ofFunctor p)) (c : ψ ≅ X.toF) :
    (⟨X.functor, X.prorepresentable, ψ⟩ : ProrepresentableMorphism p) ≅ X where
  hom := ⟨𝟙 _, c.hom⟩
  inv := ⟨𝟙 _, c.inv⟩
  hom_inv_id := Hom.ext_heq (Category.id_comp _) (heq_of_eq (by
    change c.hom ≫ c.inv = 𝟙 _
    simp))
  inv_hom_id := Hom.ext_heq (Category.id_comp _) (heq_of_eq (by
    change c.inv ≫ c.hom = 𝟙 _
    simp))

/-- **Stacks 06HD.** Giving a formal object of `p` is equivalent to giving a prorepresentable
functor `U : 𝒞_Λ ⥤ Sets` together with a morphism `U → F` over `𝒞_Λ`: the explicit functor
`ξ ↦ (underline R|_{𝒞_Λ}, ξ̲)` of Stacks 06HC, with the comparisons of Stacks 06SL on
morphisms, is an equivalence onto the category of such pairs. It is fully faithful by Stacks
06SK and 06SL, and essentially surjective because every prorepresentable functor is
isomorphic to a restricted representable one, over which Stacks 06SK produces the formal
object. -/
@[stacks 06HD "the functor `ξ ↦ (R|_{𝒞_Λ}, ξ̲)` is an equivalence"]
theorem formalObjectToProrepresentableMorphism_isEquivalence
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k) (hp : IsCofiberedInGroupoids p) :
    (formalObjectToProrepresentableMorphism p hp).IsEquivalence := by
  classical
  have hfaithful : (formalObjectToProrepresentableMorphism p hp).Faithful := by
    refine ⟨fun {ξ η} {a b} h => ?_⟩
    obtain ⟨hb, hc⟩ := Hom.base_eq_and_comparison_heq h
    have hb' : restrictedCoyonedaMap a.base = restrictedCoyonedaMap b.base := hb
    have hab : a.base = b.base := (restrictedCoyonedaMap_bijective _ _).injective hb'
    have hsb : IsComparison hp b (associatedComparison hp a) :=
      (isComparison_associatedComparison hp b).congr hab.symm hc.symm
    exact (existsUnique_isComparison hp ξ η a.base (associatedComparison hp a)).unique
      ⟨rfl, isComparison_associatedComparison hp a⟩ ⟨hab.symm, hsb⟩
  have hfull : (formalObjectToProrepresentableMorphism p hp).Full := by
    refine ⟨fun {ξ η} g => ?_⟩
    obtain ⟨f, hf⟩ := (restrictedCoyonedaMap_bijective ξ.base η.base).surjective g.base
    obtain ⟨t, ht⟩ := exists_heq_comparison hf g.comparison
    obtain ⟨a, ⟨ha, hat⟩, -⟩ := existsUnique_isComparison hp ξ η f t
    obtain ⟨t₀, ht₀⟩ := exists_heq_comparison (congrArg restrictedCoyonedaMap ha) t
    have h₀ : IsComparison hp a t₀ := hat.congr ha.symm ht₀.symm
    refine ⟨a, Hom.ext_heq ?_ ?_⟩
    · change restrictedCoyonedaMap a.base = g.base
      rw [ha, hf]
    · exact (heq_of_eq ((isComparison_associatedComparison hp a).ext h₀)).trans (ht₀.trans ht)
  have hsurj : (formalObjectToProrepresentableMorphism p hp).EssSurj := by
    refine ⟨fun X => ?_⟩
    obtain ⟨P⟩ := presentation_nonempty hp X
    exact ⟨P.object, ⟨(isoOfFunctorIso (ofFormalObject hp P.object) X.prorepresentable
      P.iso).symm ≪≫ isoOfToFIso X _ P.comparison⟩⟩
  exact ⟨hfaithful, hfull, hsurj⟩

instance (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k) (hp : IsCofiberedInGroupoids p) :
    (formalObjectToProrepresentableMorphism p hp).IsEquivalence :=
  formalObjectToProrepresentableMorphism_isEquivalence p hp

/-- **Stacks 06HD.** The equivalence between formal objects of `p` and prorepresentable
functors on `𝒞_Λ` with a morphism to `F`, whose functor is
`formalObjectToProrepresentableMorphism`. -/
@[stacks 06HD "the equivalence of formal objects with pairs `(U, U → F)`"]
noncomputable def formalObjectProrepresentableMorphismEquivalence
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k) (hp : IsCofiberedInGroupoids p) :
    FormalObject p ≌ ProrepresentableMorphism p :=
  (formalObjectToProrepresentableMorphism p hp).asEquivalence

/-- The functor of `formalObjectProrepresentableMorphismEquivalence` is the explicit functor
`ξ ↦ (underline R|_{𝒞_Λ}, ξ̲)`. -/
theorem formalObjectProrepresentableMorphismEquivalence_functor
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k) (hp : IsCofiberedInGroupoids p) :
    (formalObjectProrepresentableMorphismEquivalence p hp).functor =
      formalObjectToProrepresentableMorphism p hp :=
  rfl

end Category

end Deformation

end
