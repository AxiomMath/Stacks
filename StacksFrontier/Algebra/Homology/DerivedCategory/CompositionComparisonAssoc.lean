module

public import StacksFrontier.Algebra.Homology.DerivedCategory.CompositionComparisonIso

/-!
# The comparison `R(G ∘ F) ≅ RF ⋙ RG` is associative

Let `F : 𝒜 ⥤ ℬ`, `G : ℬ ⥤ 𝒞` and `H : 𝒞 ⥤ 𝒟` be additive functors between abelian categories
with derived categories, the first three categories having enough injectives.  The canonical
comparison of [Stacks, Tag 05T2], `CategoryTheory.Functor.rightDerivedFunctorPlusComp`, is
available for each of the four composable pairs `(F, G)`, `(G, H)`, `(F ⋙ G, H)` and
`(F, G ⋙ H)`, and this module proves that the two ways of taking `R(H ∘ G ∘ F)` apart into
`RF ⋙ RG ⋙ RH` agree.

## Main results

* `CategoryTheory.Functor.rightDerivedFunctorPlusComp_assoc` — the associativity of the
  canonical comparison transformation.  No preservation of injectives is assumed, so this is a
  statement about the transformation of [Stacks, Tag 05T2] itself.
* `CategoryTheory.Functor.rightDerivedFunctorPlusComp_assoc_app` — the same, read at an object
  of `D⁺(𝒜)`.
* `CategoryTheory.Functor.rightDerivedFunctorPlusCompIso_assoc` and
  `CategoryTheory.Functor.rightDerivedFunctorPlusCompIso_assoc_app` — the same identity for the
  isomorphisms of `CategoryTheory.Functor.rightDerivedFunctorPlusCompIso`, available when `F` and
  `G` preserve injective objects.
* `CategoryTheory.Functor.mapHomotopyCategoryPlusCompIso_refl_inv_app` and
  `CategoryTheory.Functor.qhMapCompIsoReflInv_comp` — the coherence isomorphism for the
  identity comparison of a composite is the identity, and so drops out of
  `CategoryTheory.Functor.rightDerivedFunctorPlusComp_fac_app`.

## Implementation notes

Every proof below is in term mode, and deliberately so.  The source of the two sides has the
two spellings `((F ⋙ G) ⋙ H).mapHomotopyCategoryPlus.obj K` and
`H.mapHomotopyCategoryPlus.obj ((F ⋙ G).mapHomotopyCategoryPlus.obj K)`; they are equal, but
`DerivedCategory.Plus.Qh` is not exposed, so they are not equal at the transparency at which
`rw` re-checks the goal it builds, and every `rw` across that boundary fails — including the
`rw` that `conv` and `reassoc_of%` perform.  `CategoryTheory.eq_whisker`,
`CategoryTheory.whisker_eq` and `congrArg` build the composites afresh and are checked at the
default transparency, where the two spellings do agree.

No `@[stacks]` attribute is placed.  [Stacks, Tag 05T2] is tagged at
`CategoryTheory.Functor.DerivedFunctorComposition.exists_rightDerived_comparison`, where the
source states the comparison, and the source does not state this coherence.

## References

* [Stacks, Tag 05T2](https://stacks.math.columbia.edu/tag/05T2), the comparison transformation
* [Stacks, Tag 015M](https://stacks.math.columbia.edu/tag/015M), when it is an isomorphism
-/

@[expose] public section

universe w w₁ w₂ w₃ v v₁ v₂ v₃ u u₁ u₂ u₃

open CategoryTheory Limits

namespace CategoryTheory.Functor

-- As in `StacksFrontier.Algebra.Homology.DerivedCategory.CompositionComparisonIso`: everything
-- below mentions `Functor.rightDerivedFunctorPlus`, which needs pointwise right derivability at
-- every object, so the cheap instance that gets it from `EnoughInjectives` is given precedence
-- over the one that would embark on proving termwise injectivity of an unknown complex.
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-! ### The coherence isomorphism for the identity comparison of a composite -/

section Coherence

variable {A : Type*} {B : Type*} {C : Type*} [Category* A] [Category* B] [Category* C]
  [Abelian A] [Abelian B] [Abelian C]

/-- The coherence isomorphism identifying the functor induced on bounded below homotopy
categories by a composite with the composite of the induced functors is the identity, for the
identity isomorphism of the composite. -/
lemma mapHomotopyCategoryPlusCompIso_refl_inv_app (P : A ⥤ B) (Q : B ⥤ C)
    [P.Additive] [Q.Additive] (K : HomotopyCategory.Plus A) :
    (mapHomotopyCategoryPlusCompIso (Iso.refl (P ⋙ Q))).inv.app K =
      𝟙 ((P ⋙ Q).mapHomotopyCategoryPlus.obj K) :=
  rfl

variable [HasDerivedCategory C]

/-- **The coherence isomorphism drops out of the factorization of [Stacks, Tag 05T2].**
Precomposition with the image under `Qh` of the coherence isomorphism for the identity
comparison of a composite, the first factor of the right-hand side of
`CategoryTheory.Functor.rightDerivedFunctorPlusComp_fac_app`, is the identity. -/
lemma qhMapCompIsoReflInv_comp (P : A ⥤ B) (Q : B ⥤ C) [P.Additive] [Q.Additive]
    (K : HomotopyCategory.Plus A) {Z : DerivedCategory.Plus C}
    (f : (Q.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).obj
      (P.mapHomotopyCategoryPlus.obj K) ⟶ Z) :
    DerivedCategory.Plus.Qh.map
        ((mapHomotopyCategoryPlusCompIso (Iso.refl (P ⋙ Q))).inv.app K) ≫ f = f :=
  (CategoryTheory.eq_whisker
      ((congrArg DerivedCategory.Plus.Qh.map
          (mapHomotopyCategoryPlusCompIso_refl_inv_app P Q K)).trans
        (DerivedCategory.Plus.Qh.map_id _)) f).trans (Category.id_comp f)

end Coherence

/-! ### The associativity -/

variable {A : Type u} {B : Type u₁} {C : Type u₂} {D : Type u₃}
  [Category.{v} A] [Category.{v₁} B] [Category.{v₂} C] [Category.{v₃} D]
  [Abelian A] [Abelian B] [Abelian C] [Abelian D]
  [HasDerivedCategory.{w} A] [HasDerivedCategory.{w₁} B] [HasDerivedCategory.{w₂} C]
  [HasDerivedCategory.{w₃} D]
  (F : A ⥤ B) (G : B ⥤ C) (H : C ⥤ D) [F.Additive] [G.Additive] [H.Additive]
  [EnoughInjectives A] [EnoughInjectives B] [EnoughInjectives C]

omit [HasDerivedCategory B] [EnoughInjectives B] in
/-- The composite of the unit of `R(H ∘ G ∘ F)` with the comparison taken apart as `F ⋙ G`
against `H`: the coherence isomorphism drops out and what is left is the unit of `RH` followed
by `RH` of the unit of `R(G ∘ F)`. -/
private lemma assoc_unit_left (K : HomotopyCategory.Plus A) :
    ((F ⋙ G) ⋙ H).rightDerivedFunctorPlusUnith.app K ≫
        (rightDerivedFunctorPlusComp (F ⋙ G) H).app (DerivedCategory.Plus.Qh.obj K) =
      H.rightDerivedFunctorPlusUnith.app ((F ⋙ G).mapHomotopyCategoryPlus.obj K) ≫
        H.rightDerivedFunctorPlus.map ((F ⋙ G).rightDerivedFunctorPlusUnith.app K) :=
  (rightDerivedFunctorPlusComp_fac_app (F ⋙ G) H K).trans
    (qhMapCompIsoReflInv_comp (F ⋙ G) H K
      (H.rightDerivedFunctorPlusUnith.app ((F ⋙ G).mapHomotopyCategoryPlus.obj K) ≫
        H.rightDerivedFunctorPlus.map ((F ⋙ G).rightDerivedFunctorPlusUnith.app K)))

omit [EnoughInjectives C] in
/-- The same for the inner pair `(F, G)`. -/
private lemma assoc_unit_inner (K : HomotopyCategory.Plus A) :
    (F ⋙ G).rightDerivedFunctorPlusUnith.app K ≫
        (rightDerivedFunctorPlusComp F G).app (DerivedCategory.Plus.Qh.obj K) =
      G.rightDerivedFunctorPlusUnith.app (F.mapHomotopyCategoryPlus.obj K) ≫
        G.rightDerivedFunctorPlus.map (F.rightDerivedFunctorPlusUnith.app K) :=
  (rightDerivedFunctorPlusComp_fac_app F G K).trans
    (qhMapCompIsoReflInv_comp F G K
      (G.rightDerivedFunctorPlusUnith.app (F.mapHomotopyCategoryPlus.obj K) ≫
        G.rightDerivedFunctorPlus.map (F.rightDerivedFunctorPlusUnith.app K)))

omit [HasDerivedCategory C] [EnoughInjectives C] in
/-- The composite of the unit of `R(H ∘ G ∘ F)` with the comparison taken apart as `F` against
`G ⋙ H`. -/
private lemma assoc_unit_right (K : HomotopyCategory.Plus A) :
    ((F ⋙ G) ⋙ H).rightDerivedFunctorPlusUnith.app K ≫
        (rightDerivedFunctorPlusComp F (G ⋙ H)).app (DerivedCategory.Plus.Qh.obj K) =
      (G ⋙ H).rightDerivedFunctorPlusUnith.app (F.mapHomotopyCategoryPlus.obj K) ≫
        (G ⋙ H).rightDerivedFunctorPlus.map (F.rightDerivedFunctorPlusUnith.app K) :=
  (rightDerivedFunctorPlusComp_fac_app F (G ⋙ H) K).trans
    (qhMapCompIsoReflInv_comp F (G ⋙ H) K
      ((G ⋙ H).rightDerivedFunctorPlusUnith.app (F.mapHomotopyCategoryPlus.obj K) ≫
        (G ⋙ H).rightDerivedFunctorPlus.map (F.rightDerivedFunctorPlusUnith.app K)))

omit [HasDerivedCategory A] [EnoughInjectives A] in
/-- The same for the outer pair `(G, H)`, read at the image of `K` under `F`. -/
private lemma assoc_unit_outer (K : HomotopyCategory.Plus A) :
    (G ⋙ H).rightDerivedFunctorPlusUnith.app (F.mapHomotopyCategoryPlus.obj K) ≫
        (rightDerivedFunctorPlusComp G H).app
          (DerivedCategory.Plus.Qh.obj (F.mapHomotopyCategoryPlus.obj K)) =
      H.rightDerivedFunctorPlusUnith.app
          (G.mapHomotopyCategoryPlus.obj (F.mapHomotopyCategoryPlus.obj K)) ≫
        H.rightDerivedFunctorPlus.map
          (G.rightDerivedFunctorPlusUnith.app (F.mapHomotopyCategoryPlus.obj K)) :=
  (rightDerivedFunctorPlusComp_fac_app G H (F.mapHomotopyCategoryPlus.obj K)).trans
    (qhMapCompIsoReflInv_comp G H (F.mapHomotopyCategoryPlus.obj K)
      (H.rightDerivedFunctorPlusUnith.app
          (G.mapHomotopyCategoryPlus.obj (F.mapHomotopyCategoryPlus.obj K)) ≫
        H.rightDerivedFunctorPlus.map
          (G.rightDerivedFunctorPlusUnith.app (F.mapHomotopyCategoryPlus.obj K))))

/-- Under `RH`, the inner factorization of the comparison for `(F, G)`. -/
private lemma assoc_unit_inner_map (K : HomotopyCategory.Plus A) :
    H.rightDerivedFunctorPlus.map ((F ⋙ G).rightDerivedFunctorPlusUnith.app K) ≫
        H.rightDerivedFunctorPlus.map
          ((rightDerivedFunctorPlusComp F G).app (DerivedCategory.Plus.Qh.obj K)) =
      H.rightDerivedFunctorPlus.map
          (G.rightDerivedFunctorPlusUnith.app (F.mapHomotopyCategoryPlus.obj K)) ≫
        H.rightDerivedFunctorPlus.map
          (G.rightDerivedFunctorPlus.map (F.rightDerivedFunctorPlusUnith.app K)) :=
  (H.rightDerivedFunctorPlus.map_comp _ _).symm.trans
    ((congrArg H.rightDerivedFunctorPlus.map (assoc_unit_inner F G K)).trans
      (H.rightDerivedFunctorPlus.map_comp _ _))

/-- **The associativity, read against the unit of `R(H ∘ G ∘ F)` at a bounded below complex.** -/
private lemma assoc_unit_app (K : HomotopyCategory.Plus A) :
    ((F ⋙ G) ⋙ H).rightDerivedFunctorPlusUnith.app K ≫
        (rightDerivedFunctorPlusComp (F ⋙ G) H).app (DerivedCategory.Plus.Qh.obj K) ≫
          H.rightDerivedFunctorPlus.map
            ((rightDerivedFunctorPlusComp F G).app (DerivedCategory.Plus.Qh.obj K)) =
      ((F ⋙ G) ⋙ H).rightDerivedFunctorPlusUnith.app K ≫
        (rightDerivedFunctorPlusComp F (G ⋙ H)).app (DerivedCategory.Plus.Qh.obj K) ≫
          (rightDerivedFunctorPlusComp G H).app
            (F.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Qh.obj K)) :=
  have hleft : ((F ⋙ G) ⋙ H).rightDerivedFunctorPlusUnith.app K ≫
      (rightDerivedFunctorPlusComp (F ⋙ G) H).app (DerivedCategory.Plus.Qh.obj K) ≫
        H.rightDerivedFunctorPlus.map
          ((rightDerivedFunctorPlusComp F G).app (DerivedCategory.Plus.Qh.obj K)) =
      H.rightDerivedFunctorPlusUnith.app ((F ⋙ G).mapHomotopyCategoryPlus.obj K) ≫
        H.rightDerivedFunctorPlus.map
            (G.rightDerivedFunctorPlusUnith.app (F.mapHomotopyCategoryPlus.obj K)) ≫
          H.rightDerivedFunctorPlus.map
            (G.rightDerivedFunctorPlus.map (F.rightDerivedFunctorPlusUnith.app K)) :=
    (Category.assoc _ _ _).symm.trans
      ((CategoryTheory.eq_whisker (assoc_unit_left F G H K)
            (H.rightDerivedFunctorPlus.map
              ((rightDerivedFunctorPlusComp F G).app
                (DerivedCategory.Plus.Qh.obj K)))).trans
        ((Category.assoc _ _ _).trans
          (CategoryTheory.whisker_eq
            (H.rightDerivedFunctorPlusUnith.app ((F ⋙ G).mapHomotopyCategoryPlus.obj K))
            (assoc_unit_inner_map F G H K))))
  have hright : ((F ⋙ G) ⋙ H).rightDerivedFunctorPlusUnith.app K ≫
      (rightDerivedFunctorPlusComp F (G ⋙ H)).app (DerivedCategory.Plus.Qh.obj K) ≫
        (rightDerivedFunctorPlusComp G H).app
          (F.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Qh.obj K)) =
      H.rightDerivedFunctorPlusUnith.app
          (G.mapHomotopyCategoryPlus.obj (F.mapHomotopyCategoryPlus.obj K)) ≫
        H.rightDerivedFunctorPlus.map
            (G.rightDerivedFunctorPlusUnith.app (F.mapHomotopyCategoryPlus.obj K)) ≫
          (G.rightDerivedFunctorPlus ⋙ H.rightDerivedFunctorPlus).map
            (F.rightDerivedFunctorPlusUnith.app K) :=
    (Category.assoc _ _ _).symm.trans
      ((CategoryTheory.eq_whisker (assoc_unit_right F G H K)
            ((rightDerivedFunctorPlusComp G H).app
              (F.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Qh.obj K)))).trans
        ((Category.assoc _ _ _).trans
          ((CategoryTheory.whisker_eq
                ((G ⋙ H).rightDerivedFunctorPlusUnith.app
                  (F.mapHomotopyCategoryPlus.obj K))
                ((rightDerivedFunctorPlusComp G H).naturality
                  (F.rightDerivedFunctorPlusUnith.app K))).trans
            ((Category.assoc _ _ _).symm.trans
              ((CategoryTheory.eq_whisker (assoc_unit_outer F G H K)
                    ((G.rightDerivedFunctorPlus ⋙ H.rightDerivedFunctorPlus).map
                      (F.rightDerivedFunctorPlusUnith.app K))).trans
                (Category.assoc _ _ _))))))
  hleft.trans hright.symm

/-- **The canonical comparison of [Stacks, Tag 05T2] is associative.**  For additive
`F : 𝒜 ⥤ ℬ`, `G : ℬ ⥤ 𝒞` and `H : 𝒞 ⥤ 𝒟` the two ways of comparing `R(H ∘ G ∘ F)` with
`RF ⋙ RG ⋙ RH` agree: taking `F ⋙ G` apart from `H` first and then `F` from `G`, or taking `F`
apart from `G ⋙ H` first and then `G` from `H`.

Nothing is assumed beyond additivity and enough injectives, so this is a statement about the
canonical transformation and not only about the isomorphism it becomes when `F` and `G`
preserve injective objects. -/
theorem rightDerivedFunctorPlusComp_assoc :
    rightDerivedFunctorPlusComp (F ⋙ G) H ≫
        Functor.whiskerRight (rightDerivedFunctorPlusComp F G) H.rightDerivedFunctorPlus =
      rightDerivedFunctorPlusComp F (G ⋙ H) ≫
        Functor.whiskerLeft F.rightDerivedFunctorPlus (rightDerivedFunctorPlusComp G H) :=
  ((F ⋙ G) ⋙ H).rightDerivedFunctorPlus.rightDerived_ext
    ((F ⋙ G) ⋙ H).rightDerivedFunctorPlusUnith (HomotopyCategory.Plus.quasiIso A) _ _ _
    (NatTrans.ext (funext fun K ↦ assoc_unit_app F G H K))

/-- The associativity of the canonical comparison, read at an object of `D⁺(𝒜)`. -/
theorem rightDerivedFunctorPlusComp_assoc_app (K : DerivedCategory.Plus A) :
    (rightDerivedFunctorPlusComp (F ⋙ G) H).app K ≫
        H.rightDerivedFunctorPlus.map ((rightDerivedFunctorPlusComp F G).app K) =
      (rightDerivedFunctorPlusComp F (G ⋙ H)).app K ≫
        (rightDerivedFunctorPlusComp G H).app (F.rightDerivedFunctorPlus.obj K) :=
  NatTrans.congr_app (rightDerivedFunctorPlusComp_assoc F G H) K

section PreservesInjectiveObjects

variable [F.PreservesInjectiveObjects] [G.PreservesInjectiveObjects]

/-- **The comparison isomorphism `R(G ∘ F) ≅ RF ⋙ RG` is associative.**  This is
`rightDerivedFunctorPlusComp_assoc` for the isomorphisms of
`CategoryTheory.Functor.rightDerivedFunctorPlusCompIso`, whose `hom` is the canonical
comparison. -/
theorem rightDerivedFunctorPlusCompIso_assoc :
    (rightDerivedFunctorPlusCompIso (F ⋙ G) H).hom ≫
        Functor.whiskerRight (rightDerivedFunctorPlusCompIso F G).hom
          H.rightDerivedFunctorPlus =
      (rightDerivedFunctorPlusCompIso F (G ⋙ H)).hom ≫
        Functor.whiskerLeft F.rightDerivedFunctorPlus
          (rightDerivedFunctorPlusCompIso G H).hom :=
  rightDerivedFunctorPlusComp_assoc F G H

/-- The associativity of the comparison isomorphism, read at an object of `D⁺(𝒜)`. -/
theorem rightDerivedFunctorPlusCompIso_assoc_app (K : DerivedCategory.Plus A) :
    (rightDerivedFunctorPlusCompIso (F ⋙ G) H).hom.app K ≫
        H.rightDerivedFunctorPlus.map ((rightDerivedFunctorPlusCompIso F G).hom.app K) =
      (rightDerivedFunctorPlusCompIso F (G ⋙ H)).hom.app K ≫
        (rightDerivedFunctorPlusCompIso G H).hom.app (F.rightDerivedFunctorPlus.obj K) :=
  rightDerivedFunctorPlusComp_assoc_app F G H K

end PreservesInjectiveObjects

end CategoryTheory.Functor

end
