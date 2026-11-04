module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import StacksFrontier.RingTheory.MilnorPatching.Algebras

/-!
# Flat and étale descent for the sections of a cartesian square of schemes

Let `W ⟶ X ⟶ Z` and `W ⟶ Y ⟶ Z` be a cartesian square of schemes.  On affine charts it gives a
*pushout* square of rings of sections, so that the four section rings form a Milnor patching
datum.  Over such a datum, flatness and étaleness of a ring map into a fibre product are
detected on the two factors, and a map of flat algebras over the base is an isomorphism as soon
as both of its base changes are.

This is the affine input for descent of flatness and étaleness along a pushout of schemes glued
from a closed immersion and an integral morphism.

## Main results

* `AlgebraicGeometry.isPushout_appLE_of_isPullback_of_isAffineOpen`: affine charts of a
  cartesian square of schemes give a pushout square of rings of sections.
* `MilnorPatching.flat_pullbackMap_of_ringPushout` and
  `MilnorPatching.etale_pullbackMap_of_ringPushout`: the canonical map from a ring fibre product
  to the fibre product of two glued algebras is flat, respectively étale, as soon as both glued
  algebras are.
* `MilnorPatching.bijective_toRelativePullback_of_flat`: a flat algebra over a ring fibre
  product is recovered from its two base changes.
* `MilnorPatching.isIso_of_isIso_baseChange` and
  `MilnorPatching.isIso_of_isIso_baseChange_of_isPullback`: a map of flat algebras over a ring
  fibre product is an isomorphism once both of its base changes are.
* `AlgebraicGeometry.isIso_sectionsPushoutMap_of_isIso_pullback`: the geometric input for the
  previous result — if base change of a morphism of schemes along `j` is an isomorphism, then
  the induced map on the relevant pushouts of section rings is an isomorphism.
* `AlgebraicGeometry.universallyClosed_of_jointly_surjective`: a morphism is universally closed
  as soon as its composites with two jointly surjective morphisms are.

## Implementation notes

The ring-level statements are read off from Milnor patching for algebras over a ring fibre
product, [Stacks Project, Tag 08KQ], as developed in
`StacksFrontier.RingTheory.MilnorPatching.Algebras`; the fibre product itself is the one of
`RingFibreProduct.Situation`, whose surjectivity hypothesis is supplied geometrically by a
closed immersion.

`AlgebraicGeometry.isIso_sectionsPushoutMap_of_isIso_pullback` compares a categorical pushout of
section rings with the sections of a fibre product of schemes through Mathlib's
`AlgebraicGeometry.pushoutSection`, which is an isomorphism on affine charts.

## References

* [Stacks Project, Tag 08KQ](https://stacks.math.columbia.edu/tag/08KQ)
* [Stacks Project, Tag 0ECL](https://stacks.math.columbia.edu/tag/0ECL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- Equal morphisms of schemes induce equal maps on sections over a fixed pair of opens. -/
theorem Scheme.Hom.appLE_congr_hom {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g)
    (U : Y.Opens) (V : X.Opens) (hf : V ≤ f ⁻¹ᵁ U) (hg : V ≤ g ⁻¹ᵁ U) :
    f.appLE U V hf = g.appLE U V hg := by
  subst h
  rfl

/-- Affine charts of a cartesian square of schemes give a pushout square of rings of sections:
if `W` is the fibre product of `X` and `Y` over `Z` and the four opens are affine and compatible,
with the open in `W` the intersection of the preimages of the opens in `X` and `Y`, then the
square of restriction maps on sections is a pushout square of rings. -/
theorem isPushout_appLE_of_isPullback_of_isAffineOpen
    {X Y Z W : Scheme.{u}} {g : W ⟶ X} {iY : W ⟶ Y}
    {iX : X ⟶ Z} {f : Y ⟶ Z} (H : IsPullback g iY iX f)
    (UZ : Z.Opens) (hUZ : IsAffineOpen UZ)
    (UY : Y.Opens) (hUY : IsAffineOpen UY) (hUYle : UY ≤ f ⁻¹ᵁ UZ)
    (UX : X.Opens) (hUX : IsAffineOpen UX) (hUXle : UX ≤ iX ⁻¹ᵁ UZ)
    (UW : W.Opens) (hUW : UW = g ⁻¹ᵁ UX ⊓ iY ⁻¹ᵁ UY)
    (hUWaff : IsAffineOpen UW) :
    IsPushout (CommRingCat.ofHom (f.appLE UZ UY hUYle).hom)
      (CommRingCat.ofHom (iX.appLE UZ UX hUXle).hom)
      (CommRingCat.ofHom (iY.appLE UY UW (by rw [hUW]; simp)).hom)
      (CommRingCat.ofHom (g.appLE UX UW (by rw [hUW]; simp)).hom) := by
  have hSpec : IsPullback
      (Scheme.Spec.map ((iY.appLE UY UW (hUW.trans_le inf_le_right)).op))
      (Scheme.Spec.map ((g.appLE UX UW (hUW.trans_le inf_le_left)).op))
      (Scheme.Spec.map ((f.appLE UZ UY hUYle).op))
      (Scheme.Spec.map ((iX.appLE UZ UX hUXle).op)) :=
    .of_iso (Scheme.Hom.isPullback_resLE H hUYle hUXle hUW).flip hUWaff.isoSpec hUY.isoSpec
      hUX.isoSpec hUZ.isoSpec
      (by rw [IsAffineOpen.isoSpec_hom, IsAffineOpen.isoSpec_hom]
          exact (Scheme.Opens.toSpecΓ_SpecMap_appLE iY UY UW (hUW.trans_le inf_le_right)).symm)
      (by rw [IsAffineOpen.isoSpec_hom, IsAffineOpen.isoSpec_hom]
          exact (Scheme.Opens.toSpecΓ_SpecMap_appLE g UX UW (hUW.trans_le inf_le_left)).symm)
      (by rw [IsAffineOpen.isoSpec_hom, IsAffineOpen.isoSpec_hom]
          exact (Scheme.Opens.toSpecΓ_SpecMap_appLE f UZ UY hUYle).symm)
      (by rw [IsAffineOpen.isoSpec_hom, IsAffineOpen.isoSpec_hom]
          exact (Scheme.Opens.toSpecΓ_SpecMap_appLE iX UZ UX hUXle).symm)
  exact (IsPullback.of_map_of_faithful Scheme.Spec hSpec).unop.flip

/-- A morphism of schemes is universally closed as soon as its composites with two jointly
surjective morphisms are. -/
theorem universallyClosed_of_jointly_surjective
    {X A B Y : Scheme.{u}} (i : A ⟶ X) (j : B ⟶ X) (f : X ⟶ Y)
    (hcover : ∀ x : X, x ∈ Set.range i ∨ x ∈ Set.range j)
    [UniversallyClosed (i ≫ f)] [UniversallyClosed (j ≫ f)] :
    UniversallyClosed f := by
  constructor
  intro X' Y' i₁ i₂ f' H
  let p₁ := pullback.fst i₁ i
  let p₂ := pullback.fst i₁ j
  have hc₁ (x : X') : x ∈ Set.range p₁ ∨ x ∈ Set.range p₂ := by
    rcases hcover (i₁ x) with ⟨a, ha⟩ | ⟨b, hb⟩
    · exact .inl (by rw [Scheme.Pullback.range_fst]; exact ⟨a, ha⟩)
    · exact .inr (by rw [Scheme.Pullback.range_fst]; exact ⟨b, hb⟩)
  have H₁ : IsPullback (p₁ ≫ f') (pullback.snd i₁ i) i₂ (i ≫ f) :=
    (IsPullback.of_hasPullback i₁ i).paste_horiz H
  have H₂ : IsPullback (p₂ ≫ f') (pullback.snd i₁ j) i₂ (j ≫ f) :=
    (IsPullback.of_hasPullback i₁ j).paste_horiz H
  intro C hC
  have hEq : f' '' C = (p₁ ≫ f') '' (p₁ ⁻¹' C) ∪ (p₂ ≫ f') '' (p₂ ⁻¹' C) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rcases hc₁ x with ⟨z, hz⟩ | ⟨z, hz⟩
      · exact .inl ⟨z, by simpa [hz] using hx, by change f' (p₁ z) = f' x; rw [← hz]⟩
      · exact .inr ⟨z, by simpa [hz] using hx, by change f' (p₂ z) = f' x; rw [← hz]⟩
    · rintro (⟨z, hz, rfl⟩ | ⟨z, hz, rfl⟩)
      · exact ⟨p₁ z, hz, rfl⟩
      · exact ⟨p₂ z, hz, rfl⟩
  rw [hEq]
  exact (UniversallyClosed.universally_isClosedMap _ _ _ H₁ _ (hC.preimage p₁.continuous)).union
    (UniversallyClosed.universally_isClosedMap _ _ _ H₂ _ (hC.preimage p₂.continuous))

end AlgebraicGeometry

namespace MilnorPatching

/-- The canonical map from a ring fibre product `B ×_A A'` to the fibre product `D ×_C C'` of two
algebras glued over `A` is flat as soon as both `B ⟶ D` and `A' ⟶ C'` are. -/
theorem flat_pullbackMap_of_ringPushout
    {A A' B D C' C : Type u}
    [CommRing A] [CommRing A'] [CommRing B] [CommRing D] [CommRing C'] [CommRing C]
    (toBase : B →+* A) (surjection : A' →+* A) (I : Ideal A')
    (base : RingFibreProduct.Situation toBase surjection I)
    (BtoD : B →+* D) (A'toC' : A' →+* C') (AtoC : A →+* C)
    (DtoC : D →+* C) (C'toC : C' →+* C)
    (hD : ringPushout BtoD toBase DtoC AtoC)
    (hC' : ringPushout A'toC' surjection C'toC AtoC)
    (hBflat : BtoD.Flat) (hA'flat : A'toC'.Flat) :
    let toB : base.fibreProduct →+* B := base.pullbackCone.fst.hom
    let toA' : base.fibreProduct →+* A' := base.pullbackCone.snd.hom
    let toD' : base.fibreProduct →+* RingHom.pullback DtoC C'toC :=
      RingHom.codRestrict ((BtoD.comp toB).prod (A'toC'.comp toA'))
        (RingHom.pullback DtoC C'toC) (fun x ↦ by
          change DtoC (BtoD (toB x)) = C'toC (A'toC' (toA' x))
          have hd : DtoC.comp BtoD = AtoC.comp toBase := ringPushout_comm hD
          have hc : C'toC.comp A'toC' = AtoC.comp surjection := ringPushout_comm hC'
          calc
            _ = AtoC (toBase (toB x)) := DFunLike.congr_fun hd (toB x)
            _ = AtoC (surjection (toA' x)) := congrArg AtoC
              (DFunLike.congr_fun
                (congrArg CommRingCat.Hom.hom base.pullbackCone.condition) x)
            _ = _ := (DFunLike.congr_fun hc (toA' x)).symm)
    toD'.Flat :=
  (ringHom_properties_pullback_iff_and_flatAlgebra_equivalence
    toBase surjection I base BtoD A'toC' AtoC DtoC C'toC hD hC').2.1.mpr ⟨hBflat, hA'flat⟩

/-- The canonical map from a ring fibre product `B ×_A A'` to the fibre product `D ×_C C'` of two
algebras glued over `A` is étale as soon as both `B ⟶ D` and `A' ⟶ C'` are. -/
theorem etale_pullbackMap_of_ringPushout
    {A A' B D C' C : Type u}
    [CommRing A] [CommRing A'] [CommRing B] [CommRing D] [CommRing C'] [CommRing C]
    (toBase : B →+* A) (surjection : A' →+* A) (I : Ideal A')
    (base : RingFibreProduct.Situation toBase surjection I)
    (BtoD : B →+* D) (A'toC' : A' →+* C') (AtoC : A →+* C)
    (DtoC : D →+* C) (C'toC : C' →+* C)
    (hD : ringPushout BtoD toBase DtoC AtoC)
    (hC' : ringPushout A'toC' surjection C'toC AtoC)
    (hBetale : BtoD.Etale) (hA'etale : A'toC'.Etale) :
    let toB : base.fibreProduct →+* B := base.pullbackCone.fst.hom
    let toA' : base.fibreProduct →+* A' := base.pullbackCone.snd.hom
    let toD' : base.fibreProduct →+* RingHom.pullback DtoC C'toC :=
      RingHom.codRestrict ((BtoD.comp toB).prod (A'toC'.comp toA'))
        (RingHom.pullback DtoC C'toC) (fun x ↦ by
          change DtoC (BtoD (toB x)) = C'toC (A'toC' (toA' x))
          have hd : DtoC.comp BtoD = AtoC.comp toBase := ringPushout_comm hD
          have hc : C'toC.comp A'toC' = AtoC.comp surjection := ringPushout_comm hC'
          calc
            _ = AtoC (toBase (toB x)) := DFunLike.congr_fun hd (toB x)
            _ = AtoC (surjection (toA' x)) := congrArg AtoC
              (DFunLike.congr_fun
                (congrArg CommRingCat.Hom.hom base.pullbackCone.condition) x)
            _ = _ := (DFunLike.congr_fun hc (toA' x)).symm)
    toD'.Etale :=
  (ringHom_properties_pullback_iff_and_flatAlgebra_equivalence
    toBase surjection I base BtoD A'toC' AtoC DtoC C'toC hD hC').2.2.2.2.1.mpr
    ⟨hBetale, hA'etale⟩

/-- A flat algebra over a ring fibre product is recovered from its two base changes: the
canonical comparison with the fibre product of the base changes is bijective. -/
theorem bijective_toRelativePullback_of_flat
    {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
    (toBase : B →+* A) (surjection : A' →+* A) (I : Ideal A')
    (base : RingFibreProduct.Situation toBase surjection I)
    {E : Type u} [CommRing E] (f : base.fibreProduct →+* E) (hf : f.Flat) :
    let s : RelativeModuleFibreProductSituation (D' := E) base := ⟨f⟩
    Function.Bijective s.toRelativePullback :=
  (ringHom_properties_pullback_iff_and_flatAlgebra_equivalence
      toBase surjection I base (RingHom.id B) (RingHom.id A') (RingHom.id A)
      toBase surjection
      (ringPushout_of_isPushout _ _ _ _ <| by
        have hi : IsPushout (𝟙 (CommRingCat.of B)) (CommRingCat.ofHom toBase)
            (CommRingCat.ofHom toBase) (𝟙 (CommRingCat.of A)) := IsPushout.of_id_fst
        simpa using hi)
      (ringPushout_of_isPushout _ _ _ _ <| by
        have hi : IsPushout (𝟙 (CommRingCat.of A')) (CommRingCat.ofHom surjection)
            (CommRingCat.ofHom surjection) (𝟙 (CommRingCat.of A)) := IsPushout.of_id_fst
        simpa using hi)).2.2.2.2.2.1 E f hf

/-- A morphism of flat algebras over a ring is an isomorphism as soon as the underlying map of
rings is. -/
theorem isIso_of_isIso_right
    {R : CommRingCat.{u}} {C D : CommRingCat.flat.Under ⊤ R} (f : C ⟶ D)
    (hf : IsIso f.right) : IsIso f := by
  refine ⟨MorphismProperty.Under.homMk (inv f.right) ?_, ?_, ?_⟩
  · calc
      D.hom ≫ inv f.right = (C.hom ≫ f.right) ≫ inv f.right := by
        rw [← MorphismProperty.Under.w f]
      _ = C.hom := by simp [Category.assoc]
  · apply MorphismProperty.Under.Hom.ext
    ext x
    show (f.right ≫ inv f.right) x = x
    exact congrArg (fun k : C.right ⟶ C.right => k x) (IsIso.hom_inv_id f.right)
  · apply MorphismProperty.Under.Hom.ext
    ext x
    show (inv f.right ≫ f.right) x = x
    exact congrArg (fun k : D.right ⟶ D.right => k x) (IsIso.inv_hom_id f.right)

/-- A morphism of flat algebras over a ring fibre product is an isomorphism as soon as both of
its base changes, to the two factors of the fibre product, are isomorphisms. -/
theorem isIso_of_isIso_baseChange
    {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
    (toBase : B →+* A) (surjection : A' →+* A) (I : Ideal A')
    (base : RingFibreProduct.Situation toBase surjection I)
    {C D : CommRingCat.flat.Under ⊤ (CommRingCat.of base.fibreProduct)}
    (f : C ⟶ D)
    (hB : IsIso ((MorphismProperty.Under.pushout CommRingCat.flat ⊤
      base.pullbackCone.fst).map f))
    (hA' : IsIso ((MorphismProperty.Under.pushout CommRingCat.flat ⊤
      base.pullbackCone.snd).map f)) : IsIso f := by
  classical
  obtain ⟨q, hqB, hqA'⟩ :=
    flatAlgebrasOverFibreProduct_equivalence toBase surjection I base
  have hq : IsIso (q.functor.map f) := by
    have h₁ : IsIso ((CategoricalPullback.π₁ _ _).map (q.functor.map f)) :=
      (NatIso.isIso_map_iff hqB.some f).mpr hB
    have h₂ : IsIso ((CategoricalPullback.π₂ _ _).map (q.functor.map f)) :=
      (NatIso.isIso_map_iff hqA'.some f).mpr hA'
    have : IsIso (q.functor.map f).fst := h₁
    have : IsIso (q.functor.map f).snd := h₂
    exact ⟨⟨inv (q.functor.map f).fst, inv (q.functor.map f).snd, by cat_disch⟩, by cat_disch⟩
  exact q.fullyFaithfulFunctor.isIso_of_isIso_map f

/-- A morphism of flat algebras over the vertex of a cartesian square of rings whose right-hand
map is surjective is an isomorphism as soon as both of its base changes, to the two factors of
the square, are isomorphisms. -/
theorem isIso_of_isIso_baseChange_of_isPullback
    {R B A' A : Type u} [CommRing R] [CommRing B] [CommRing A'] [CommRing A]
    (toB : R →+* B) (toA' : R →+* A')
    (toBase : B →+* A) (surjection : A' →+* A)
    (hsq : IsPullback (CommRingCat.ofHom toB) (CommRingCat.ofHom toA')
      (CommRingCat.ofHom toBase) (CommRingCat.ofHom surjection))
    (hsurj : Function.Surjective surjection)
    {C D : CommRingCat.flat.Under ⊤ (CommRingCat.of R)}
    (f : C ⟶ D)
    (hB : IsIso ((MorphismProperty.Under.pushout CommRingCat.flat ⊤
      (CommRingCat.ofHom toB)).map f))
    (hA' : IsIso ((MorphismProperty.Under.pushout CommRingCat.flat ⊤
      (CommRingCat.ofHom toA')).map f)) : IsIso f := by
  classical
  have : MorphismProperty.ContainsIdentities CommRingCat.flat.{u} := ⟨fun X => by
    rw [CommRingCat.flat_iff]
    exact RingHom.Flat.of_bijective Function.bijective_id⟩
  have : MorphismProperty.IsStableUnderComposition CommRingCat.flat.{u} := ⟨by
    intro X Y Z f g hf hg
    rw [CommRingCat.flat_iff] at hf hg ⊢
    exact RingHom.Flat.comp hf hg⟩
  let I : Ideal A' := RingHom.ker surjection
  let base : RingFibreProduct.Situation toBase surjection I := ⟨hsurj, rfl⟩
  let e : CommRingCat.of R ≅ CommRingCat.of base.fibreProduct :=
    IsLimit.conePointUniqueUpToIso hsq.isLimit base.pullbackConeIsLimit
  let pB : CommRingCat.of base.fibreProduct ⟶ CommRingCat.of B := base.pullbackCone.fst
  let pA' : CommRingCat.of base.fibreProduct ⟶ CommRingCat.of A' := base.pullbackCone.snd
  have heB : e.hom ≫ pB = CommRingCat.ofHom toB :=
    IsLimit.conePointUniqueUpToIso_hom_comp hsq.isLimit base.pullbackConeIsLimit
      WalkingCospan.left
  have heA' : e.hom ≫ pA' = CommRingCat.ofHom toA' :=
    IsLimit.conePointUniqueUpToIso_hom_comp hsq.isLimit base.pullbackConeIsLimit
      WalkingCospan.right
  let F₀ := MorphismProperty.Under.pushout CommRingCat.flat ⊤ e.hom
  let FBaseB := MorphismProperty.Under.pushout CommRingCat.flat ⊤ pB
  let FBaseA' := MorphismProperty.Under.pushout CommRingCat.flat ⊤ pA'
  let αB := (MorphismProperty.Under.pushoutComp (P := CommRingCat.flat) (Q := ⊤)
      e.hom pB).symm ≪≫
    MorphismProperty.Under.pushoutCongr (P := CommRingCat.flat) (Q := ⊤) heB
  let αA := (MorphismProperty.Under.pushoutComp (P := CommRingCat.flat) (Q := ⊤)
      e.hom pA').symm ≪≫
    MorphismProperty.Under.pushoutCongr (P := CommRingCat.flat) (Q := ⊤) heA'
  have hB' : IsIso (FBaseB.map (F₀.map f)) := (NatIso.isIso_map_iff αB f).mpr hB
  have hA'' : IsIso (FBaseA'.map (F₀.map f)) := (NatIso.isIso_map_iff αA f).mpr hA'
  have hF₀ : IsIso (F₀.map f) :=
    isIso_of_isIso_baseChange toBase surjection I base (F₀.map f) hB' hA''
  have hmap : IsIso (F₀.map f).right := by
    have h₂ : IsIso ((CategoryTheory.Under.forget (CommRingCat.of base.fibreProduct)).map
        ((MorphismProperty.Under.forget CommRingCat.flat ⊤
          (CommRingCat.of base.fibreProduct)).map (F₀.map f))) :=
      Functor.map_isIso _ _
    exact h₂
  have hιC : IsIso (pushout.inl C.hom e.hom) :=
    (IsPushout.of_hasPushout C.hom e.hom).isIso_inl_of_isIso
  have hιD : IsIso (pushout.inl D.hom e.hom) :=
    (IsPushout.of_hasPushout D.hom e.hom).isIso_inl_of_isIso
  have hnat : pushout.inl C.hom e.hom ≫ (F₀.map f).right =
      f.right ≫ pushout.inl D.hom e.hom := by
    show pushout.inl C.hom e.hom ≫ pushout.desc (f.right ≫ pushout.inl D.hom e.hom)
      (pushout.inr D.hom e.hom) _ = f.right ≫ pushout.inl D.hom e.hom
    exact pushout.inl_desc _ _ _
  have hcomp' : IsIso (f.right ≫ pushout.inl D.hom e.hom) := by
    rw [← hnat]
    exact IsIso.comp_isIso' hιC hmap
  exact isIso_of_isIso_right f
    (@IsIso.of_isIso_comp_right _ _ _ _ _ f.right (pushout.inl D.hom e.hom) hιD hcomp')

end MilnorPatching

namespace AlgebraicGeometry

/-- If `U ≤ a ⁻¹ᵁ V`, the preimage of `U` under the first projection of `pullback a b` lies in
the preimage of `b ⁻¹ᵁ V` under the second projection. -/
private theorem preimage_fst_le_preimage_snd {X Y P : Scheme.{u}} (a : X ⟶ P) (b : Y ⟶ P)
    {U : X.Opens} {V : P.Opens} (h : U ≤ a ⁻¹ᵁ V) :
    pullback.fst a b ⁻¹ᵁ U ≤ pullback.snd a b ⁻¹ᵁ (b ⁻¹ᵁ V) := by
  intro x hx
  change b (pullback.snd a b x) ∈ V
  rw [← Scheme.Hom.comp_apply, ← pullback.condition, Scheme.Hom.comp_apply]
  exact h hx

/-- Base change of the sections of a flat morphism along an affine morphism, computed as a
pushout of rings: if `c : G ⟶ W` is a morphism over `P` between two flat schemes over `P` whose
base change along `j : Z ⟶ P` is an isomorphism, then the induced map between the pushouts of
sections over an affine open `V ⊆ P` and an affine open `U ⊆ w ⁻¹ V` is an isomorphism. -/
theorem isIso_sectionsPushoutMap_of_isIso_pullback
    {P Z G W : Scheme.{u}} (g : G ⟶ P) (w : W ⟶ P) (c : G ⟶ W)
    (j : Z ⟶ P) (hc : c ≫ w = g)
    [Flat g] [Flat w] [IsAffineHom c] [IsAffineHom j]
    {V : P.Opens} (hV : IsAffineOpen V)
    {U : W.Opens} (hU : IsAffineOpen U) (hUV : U ≤ w ⁻¹ᵁ V)
    (hPB : IsIso (((Over.pullback j).map
      (Over.homMk (U := Over.mk g) (V := Over.mk w) c hc)).left)) :
    let S := c ⁻¹ᵁ U
    let VZ := j ⁻¹ᵁ V
    let hSV : S ≤ g ⁻¹ᵁ V := by
      calc
        S = c ⁻¹ᵁ U := rfl
        _ ≤ c ⁻¹ᵁ (w ⁻¹ᵁ V) := c.preimage_mono hUV
        _ = (c ≫ w) ⁻¹ᵁ V := (Scheme.Hom.comp_preimage c w V).symm
        _ = g ⁻¹ᵁ V := by rw [hc]
    let cObj : CommRingCat.flat.Under ⊤ (CommRingCat.of Γ(P, V)) :=
      MorphismProperty.Under.mk ⊤ (w.appLE V U hUV) (by
        rw [CommRingCat.flat_iff]
        exact w.flat_appLE hV hU hUV)
    let dObj : CommRingCat.flat.Under ⊤ (CommRingCat.of Γ(P, V)) :=
      MorphismProperty.Under.mk ⊤ (g.appLE V S hSV) (by
          rw [CommRingCat.flat_iff]
          exact g.flat_appLE hV (by
            dsimp [S]
            exact ‹IsAffineHom c›.isAffine_preimage U hU) (by
              exact hSV))
    let fObj : cObj ⟶ dObj :=
      MorphismProperty.Under.homMk (c.appLE U S (by rfl)) (by
        show w.appLE V U hUV ≫ c.appLE U S (by rfl) = g.appLE V S _
        cases hc
        exact Scheme.Hom.appLE_comp_appLE c w V U S hUV (by rfl))
    IsIso ((MorphismProperty.Under.pushout CommRingCat.flat ⊤
      (j.appLE V VZ le_rfl)).map fObj) := by
  classical
  intro S VZ hSV Cobj Dobj fObj
  have hVZ : IsAffineOpen VZ := hV.preimage j
  let Fprop := MorphismProperty.Under.pushout CommRingCat.flat ⊤
    (j.appLE V VZ le_rfl)
  let q : pullback g j ⟶ pullback w j := ((Over.pullback j).map
    (Over.homMk (U := Over.mk g) (V := Over.mk w) c hc)).left
  let targetOpen : (pullback w j).Opens := (pullback.fst w j) ⁻¹ᵁ U
  let sourceOpen : (pullback g j).Opens := q ⁻¹ᵁ targetOpen
  have hqFst : q ≫ pullback.fst w j = pullback.fst g j ≫ c := by
    dsimp [q]
    simp [Over.pullback, pullback.lift_fst]
  have hqSnd : q ≫ pullback.snd w j = pullback.snd g j := by
    dsimp [q]
    simp [Over.pullback, pullback.lift_snd]
  have hTargetEq : targetOpen =
      (pullback.fst w j) ⁻¹ᵁ U ⊓ (pullback.snd w j) ⁻¹ᵁ VZ :=
    (le_inf le_rfl (preimage_fst_le_preimage_snd w j hUV)).antisymm inf_le_left
  have hSourceEq : sourceOpen =
      (pullback.fst g j) ⁻¹ᵁ S ⊓ (pullback.snd g j) ⁻¹ᵁ VZ := by
    have hSourceLe := preimage_fst_le_preimage_snd g j hSV
    dsimp [sourceOpen, targetOpen]
    rw [← Scheme.Hom.comp_preimage q (pullback.fst w j) U, hqFst]
    have heq : (pullback.fst g j ≫ c) ⁻¹ᵁ U = (pullback.fst g j) ⁻¹ᵁ S := by
      simp [S]
    rw [heq]
    exact (le_inf le_rfl hSourceLe).antisymm inf_le_left
  have : IsIso q := hPB
  let τW := pushoutSection (IsPullback.of_hasPullback w j) le_rfl hUV hTargetEq
  let τG := pushoutSection (IsPullback.of_hasPullback g j) le_rfl hSV hSourceEq
  have hτW : IsIso τW := isIso_pushoutSection_of_isAffineOpen
    (IsPullback.of_hasPullback w j) le_rfl hUV hTargetEq hV hVZ hU
  have hτG : IsIso τG := isIso_pushoutSection_of_isAffineOpen
    (IsPullback.of_hasPullback g j) le_rfl hSV hSourceEq hV hVZ (hU.preimage c)
  have hqApp : IsIso (q.appLE targetOpen sourceOpen le_rfl) := by
    simpa only [Scheme.Hom.app_eq_appLE] using (inferInstance : IsIso (q.app targetOpen))
  have hfstG : sourceOpen ≤ (pullback.fst g j) ⁻¹ᵁ S := hSourceEq.trans_le inf_le_left
  have hfstW : targetOpen ≤ (pullback.fst w j) ⁻¹ᵁ U := le_rfl
  have hFst : c.appLE U S le_rfl ≫
        (pullback.fst g j).appLE S sourceOpen hfstG =
      (pullback.fst w j).appLE U targetOpen hfstW ≫
        q.appLE targetOpen sourceOpen le_rfl := by
    calc
      _ = (pullback.fst g j ≫ c).appLE U sourceOpen _ :=
        Scheme.Hom.appLE_comp_appLE (pullback.fst g j) c U S sourceOpen le_rfl hfstG
      _ = (q ≫ pullback.fst w j).appLE U sourceOpen _ := by simp only [hqFst]
      _ = _ := (Scheme.Hom.appLE_comp_appLE q (pullback.fst w j)
        U targetOpen sourceOpen hfstW le_rfl).symm
  have hsndG : sourceOpen ≤ (pullback.snd g j) ⁻¹ᵁ VZ := hSourceEq.trans_le inf_le_right
  have hsndW : targetOpen ≤ (pullback.snd w j) ⁻¹ᵁ VZ := hTargetEq.trans_le inf_le_right
  have hsndComp : sourceOpen ≤ (q ≫ pullback.snd w j) ⁻¹ᵁ VZ := q.preimage_mono hsndW
  have hSnd : (pullback.snd g j).appLE VZ sourceOpen hsndG =
      (pullback.snd w j).appLE VZ targetOpen hsndW ≫
        q.appLE targetOpen sourceOpen le_rfl := by
    calc
      _ = (q ≫ pullback.snd w j).appLE VZ sourceOpen hsndComp :=
        (Scheme.Hom.appLE_congr_hom hqSnd VZ sourceOpen hsndComp hsndG).symm
      _ = _ := (Scheme.Hom.appLE_comp_appLE q (pullback.snd w j)
        VZ targetOpen sourceOpen hsndW le_rfl).symm
  have hmapInl : pushout.inl Cobj.hom (j.appLE V VZ le_rfl) ≫ (Fprop.map fObj).right =
      (c.appLE U S le_rfl) ≫ pushout.inl Dobj.hom (j.appLE V VZ le_rfl) := by
    simp only [Fprop, MorphismProperty.Under.pushout_map_right]
    exact pushout.inl_desc _ _ _
  have hmapInr : pushout.inr Cobj.hom (j.appLE V VZ le_rfl) ≫ (Fprop.map fObj).right =
      pushout.inr Dobj.hom (j.appLE V VZ le_rfl) := by
    simp only [Fprop, MorphismProperty.Under.pushout_map_right]
    exact pushout.inr_desc _ _ _
  let incl : Cobj.right ⟶ Γ(pullback w j, targetOpen) :=
    (pullback.fst w j).appLE U targetOpen hfstW
  have hinlW : pushout.inl Cobj.hom (j.appLE V VZ le_rfl) ≫ τW = incl :=
    pushout.inl_desc _ _ _
  have hinrW : pushout.inr Cobj.hom (j.appLE V VZ le_rfl) ≫ τW =
      (pullback.snd w j).appLE VZ targetOpen hsndW := pushout.inr_desc _ _ _
  have hinlG : pushout.inl Dobj.hom (j.appLE V VZ le_rfl) ≫ τG =
      (pullback.fst g j).appLE S sourceOpen hfstG := pushout.inl_desc _ _ _
  have hinrG : pushout.inr Dobj.hom (j.appLE V VZ le_rfl) ≫ τG =
      (pullback.snd g j).appLE VZ sourceOpen hsndG := pushout.inr_desc _ _ _
  have hFst' : (c.appLE U S le_rfl) ≫ (pullback.fst g j).appLE S sourceOpen hfstG =
      incl ≫ q.appLE targetOpen sourceOpen le_rfl := hFst
  have hcomm : (Fprop.map fObj).right ≫ τG = τW ≫ q.appLE targetOpen sourceOpen le_rfl :=
    pushout.hom_ext
      (((reassoc_of% hmapInl) τG).trans (((c.appLE U S le_rfl) ≫= hinlG).trans
        (hFst'.trans ((reassoc_of% hinlW) _).symm)))
      (((reassoc_of% hmapInr) τG).trans (hinrG.trans (hSnd.trans ((reassoc_of% hinrW) _).symm)))
  have hComp : IsIso ((Fprop.map fObj).right ≫ τG) := by
    rw [hcomm]
    exact IsIso.comp_isIso' hτW hqApp
  have hRight : IsIso (Fprop.map fObj).right :=
    @IsIso.of_isIso_comp_right _ _ _ _ _ (Fprop.map fObj).right τG hτG hComp
  exact MilnorPatching.isIso_of_isIso_right (Fprop.map fObj) hRight

end AlgebraicGeometry

end
