module

public import StacksFrontier.Deformation.Applications.TwoFibreProductInfRow
public import StacksFrontier.Deformation.Applications.TwoFibreProductSixTermExact
public import StacksFrontier.Deformation.Applications.TwoFibreProductSixTermFull
public import StacksFrontier.Deformation.Applications.TangentModuleEquivalence
public import StacksFrontier.Deformation.Cofibered.BasedEquivalenceFibre
public import StacksFrontier.Deformation.Artin.Predeformation.FibreProduct
public import StacksFrontier.Deformation.Artin.RimSchlessinger
public import StacksFrontier.Deformation.ArtinCriteria.RimSchlessinger

/-!
# Transporting the six-term sequence along a mediating equivalence

Fibres and tangent modules along a based functor that is an equivalence, functoriality of the
map induced on tangent modules, and the five exactness/injectivity claims of Stacks 06L5's
six-term sequence transported along an arbitrary mediating
`CategoryTheory.TwoFibreProductOver.lift`-equivalence, together with the boundary map
`Deformation.infBoundaryLinearMapOfLift`.
-/

@[expose] public noncomputable section

namespace Deformation

/-! ### Fibres and tangent modules along a based functor that is an equivalence -/

section Transfer
open CategoryTheory CategoryTheory.Functor
universe uC vC u₁ v₁ u₂ v₂

variable {C : Type uC} [Category.{vC} C]

/-- A based functor whose underlying functor is essentially surjective is essentially
surjective on each fibre, as soon as its source is cofibered in groupoids.

An object `y` of the fibre over `A` is, up to isomorphism, the image of some object `s`; that
isomorphism makes the base `𝓔.p.obj s` isomorphic to `A`, and pushing `s` forward along that
isomorphism of the base produces an object of the fibre over `A` whose image is isomorphic
to `y` *in the fibre*. -/
public theorem exists_fiber_isIsomorphic_of_essSurj
    {𝓔 : BasedCategory.{v₁, u₁} C} {𝓕 : BasedCategory.{v₂, u₂} C}
    (h𝓔 : IsCofiberedInGroupoids 𝓔.p) (φ : 𝓔 ⥤ᵇ 𝓕) [φ.toFunctor.EssSurj] (A : C)
    (y : 𝓕.p.Fiber A) :
    ∃ x : 𝓔.p.Fiber A, IsIsomorphic ((fiberFunctor φ A).obj x) y := by
  obtain ⟨s, ⟨i⟩⟩ := Functor.EssSurj.mem_essImage φ.toFunctor y.1
  let b : 𝓔.p.obj s ⟶ A :=
    eqToHom (BasedFunctor.w_obj φ s).symm ≫ 𝓕.p.map i.hom ≫ eqToHom y.2
  have : IsIso b := by
    dsimp only [b]
    infer_instance
  obtain ⟨t, ψ, hψ⟩ := exists_pushforward h𝓔 b s rfl
  have := hψ
  have ht : 𝓔.p.obj t = A := IsHomLift.codomain_eq 𝓔.p b ψ
  have : 𝓕.p.IsHomLift b (φ.toFunctor.map ψ) := BasedFunctor.preserves_isHomLift φ b ψ
  have : IsIso ψ := by
    have := isStronglyCocartesian_of_isCofiberedInGroupoids h𝓔 b ψ hψ
    exact Functor.IsStronglyCocartesian.isIso_of_base_isIso 𝓔.p b ψ
  let e : φ.toFunctor.obj t ≅ y.1 := (asIso (φ.toFunctor.map ψ)).symm ≪≫ i
  have hA : 𝓕.p.obj (φ.toFunctor.obj t) = A := (BasedFunctor.w_obj φ t).trans ht
  have he : 𝓕.p.IsHomLift (𝟙 A) e.hom := by
    refine IsHomLift.of_fac' 𝓕.p (𝟙 A) e.hom hA y.2 ?_
    have hfac := IsHomLift.fac' 𝓕.p b (φ.toFunctor.map ψ)
    simp only [e, Iso.trans_hom, Iso.symm_hom, asIso_inv, Functor.map_comp, Functor.map_inv,
      hfac, b]
    simp
  have := he
  refine ⟨⟨t, ht⟩, ⟨?_⟩⟩
  exact
    { hom := ⟨e.hom, he⟩
      inv := ⟨e.inv, IsHomLift.lift_id_inv 𝓕.p A e⟩
      hom_inv_id := Functor.Fiber.hom_ext e.hom_inv_id
      inv_hom_id := Functor.Fiber.hom_ext e.inv_hom_id }

end Transfer

/-! ### Tangent modules along a composite and along an equivalence -/

section TangentTransfer
open CategoryTheory CategoryTheory.Functor
universe u v w u₁ v₁ u₂ v₂ u₃ v₃

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
  {𝓔 : BasedCategory.{v₁, u₁} (ArtinianLocalAlgCat.{u, max v w, w} Λ k)}
  {𝓕 : BasedCategory.{v₂, u₂} (ArtinianLocalAlgCat.{u, max v w, w} Λ k)}
  {𝓖 : BasedCategory.{v₃, u₃} (ArtinianLocalAlgCat.{u, max v w, w} Λ k)}

/-- The map induced on tangent modules by a composite of `1`-morphisms is the composite of the
induced maps. Both sides send the class of an object of the fibre over `k[M]` to the class of
its image, and every element of a tangent module is such a class. -/
public theorem tangentMapAt_comp
    (h𝓔 : IsDeformationCategory.{u, v, w} 𝓔.p) (h𝓕 : IsDeformationCategory.{u, v, w} 𝓕.p)
    (h𝓖 : IsDeformationCategory.{u, v, w} 𝓖.p) (φ : 𝓔 ⥤ᵇ 𝓕) (χ : 𝓕 ⥤ᵇ 𝓖)
    (M : FGModuleCat.{max v w} k) :
    tangentMapAt.{u, v, w} h𝓔 h𝓖 (BasedFunctor.comp φ χ) M =
      (tangentMapAt.{u, v, w} h𝓕 h𝓖 χ M).comp (tangentMapAt.{u, v, w} h𝓔 h𝓕 φ M) := by
  refine LinearMap.ext fun s => ?_
  obtain ⟨x, rfl⟩ := tangentClassAt_surjective.{u, v, w} 𝓔 h𝓔 M s
  have hobj : (fiberFunctor (BasedFunctor.comp φ χ)
        ((squareZeroExtensionArtinian.{u, w, max v w} Λ k).obj M)).obj x =
      (fiberFunctor χ ((squareZeroExtensionArtinian.{u, w, max v w} Λ k).obj M)).obj
        ((fiberFunctor φ ((squareZeroExtensionArtinian.{u, w, max v w} Λ k).obj M)).obj x) :=
    Subtype.ext rfl
  rw [tangentMapAt_tangentClassAt.{u, v, w}, hobj, LinearMap.comp_apply,
    tangentMapAt_tangentClassAt.{u, v, w}, tangentMapAt_tangentClassAt.{u, v, w}]

/-- A `1`-morphism whose underlying functor is essentially surjective induces a surjection on
tangent modules: every class in the target is the class of an object of the target fibre, that
object is isomorphic in its fibre to the image of an object of the source fibre, and isomorphic
objects of a fibre have the same class. -/
public theorem tangentMapAt_surjective_of_essSurj
    (h𝓔 : IsDeformationCategory.{u, v, w} 𝓔.p) (h𝓕 : IsDeformationCategory.{u, v, w} 𝓕.p)
    (φ : 𝓔 ⥤ᵇ 𝓕) [φ.toFunctor.EssSurj] (M : FGModuleCat.{max v w} k) :
    Function.Surjective (tangentMapAt.{u, v, w} h𝓔 h𝓕 φ M) := by
  intro s
  obtain ⟨y, rfl⟩ := tangentClassAt_surjective.{u, v, w} 𝓕 h𝓕 M s
  obtain ⟨x, hx⟩ := exists_fiber_isIsomorphic_of_essSurj h𝓔.predeformation.cofibered φ
    ((squareZeroExtensionArtinian.{u, w, max v w} Λ k).obj M) y
  refine ⟨tangentClassAt.{u, v, w} 𝓔 h𝓔 M x, ?_⟩
  rw [tangentMapAt_tangentClassAt.{u, v, w}]
  exact (tangentClassAt_eq_iff.{u, v, w} 𝓕 h𝓕 M _ _).mpr hx

end TangentTransfer

/-! ### The tangent row for a category equivalent to the 2-fibre product -/

section TangentRowTransfer
open CategoryTheory CategoryTheory.Functor
universe u v w u₁ v₁ u₂ v₂ u₃ v₃ u₄ v₄

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
  {H : Type u₁} [Category.{v₁} H] {G : Type u₂} [Category.{v₂} G]
  {F : Type u₃} [Category.{v₃} F] {W : Type u₄} [Category.{v₄} W]

/-- The mediating `1`-morphism into the literal 2-fibre product, as a based functor. -/
private def liftBased
    (pF : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k)
    (pW : W ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k)
    (f : H ⥤ F) (g : G ⥤ F) (A : W ⥤ H) (B : W ⥤ G)
    (hA : A ⋙ (f ⋙ pF) = pW) (hB : B ⋙ (g ⋙ pF) = pW)
    (t : A ⋙ f ≅ B ⋙ g)
    (ht : ∀ x, pF.IsHomLift (𝟙 (pW.obj x)) (t.hom.app x)) :
    BasedCategory.ofFunctor pW ⥤ᵇ productBased.{u, v, w} pF f g :=
  { toFunctor := TwoFibreProductOver.lift (f ⋙ pF) (g ⋙ pF) pF f g pW A B hA hB t ht
    w := TwoFibreProductOver.lift_comp_structureFunctor .. }

/-- The pair of maps induced by `A` and `B` is the pair of projections after the map induced by
the mediating `1`-morphism. -/
private theorem prod_tangentMapAt_eq_tangentProjPair_comp
    (pF : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k)
    (pW : W ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k)
    (f : H ⥤ F) (g : G ⥤ F) (A : W ⥤ H) (B : W ⥤ G)
    (hA : A ⋙ (f ⋙ pF) = pW) (hB : B ⋙ (g ⋙ pF) = pW)
    (t : A ⋙ f ≅ B ⋙ g)
    (ht : ∀ x, pF.IsHomLift (𝟙 (pW.obj x)) (t.hom.app x))
    (hW : IsDeformationCategory.{u, v, w} pW) (hH : IsDeformationCategory.{u, v, w} (f ⋙ pF))
    (hG : IsDeformationCategory.{u, v, w} (g ⋙ pF)) (hF : IsDeformationCategory.{u, v, w} pF)
    (M : FGModuleCat.{max v w} k) :
    LinearMap.prod
      (tangentMapAt.{u, v, w} hW hH
        ({ toFunctor := A, w := hA } :
          BasedCategory.ofFunctor pW ⥤ᵇ BasedCategory.ofFunctor (f ⋙ pF)) M)
      (tangentMapAt.{u, v, w} hW hG
        ({ toFunctor := B, w := hB } :
          BasedCategory.ofFunctor pW ⥤ᵇ BasedCategory.ofFunctor (g ⋙ pF)) M) =
    (tangentProjPair.{u, v, w} pF f g hH hG hF M).comp
      (tangentMapAt.{u, v, w} hW (isDeformationCategory_productBased.{u, v, w} pF f g hH hG hF)
        (liftBased pF pW f g A B hA hB t ht) M) := by
  have hP := isDeformationCategory_productBased.{u, v, w} pF f g hH hG hF
  refine LinearMap.ext fun s => Prod.ext ?_ ?_
  · exact LinearMap.congr_fun (tangentMapAt_comp.{u, v, w} hW hP hH
      (liftBased pF pW f g A B hA hB t ht) (productFst.{u, v, w} pF f g) M) s
  · exact LinearMap.congr_fun (tangentMapAt_comp.{u, v, w} hW hP hG
      (liftBased pF pW f g A B hA hB t ht) (productSnd.{u, v, w} pF f g) M) s

/-- **The tangent row of the six-term sequence of a 2-fibre product, read on an equivalent
category.** Let `f : ℋ → ℱ` and `g : 𝒢 → ℱ` be `1`-morphisms of deformation categories over
`𝒞_Λ`, and let `𝒲` be a deformation category equipped with `1`-morphisms `A : 𝒲 → ℋ` and
`B : 𝒲 → 𝒢` and a vertical `2`-cell `A ⋙ f ≅ B ⋙ g` exhibiting `𝒲` as a `2`-fibre product of
`f` and `g`, in the sense that the mediating `1`-morphism into
`CategoryTheory.TwoFibreProductOver` is an equivalence. Then

`T𝒲 → Tℋ ⊕ T𝒢 → Tℱ`,

with the first map the pair of the maps induced by `A` and `B` and the second the difference of
the maps induced by `f` and `g`, is exact at `Tℋ ⊕ T𝒢`.

This is part (2) of Tag 06L5, `Deformation.exact_tangentProjPair_tangentLegDiff`, transported
along the mediating equivalence: the pair of the maps induced by `A` and `B` factors through the
map induced by that equivalence, which is surjective on tangent modules
(`Deformation.tangentMapAt_surjective_of_essSurj`), and exactness is inherited by
precomposition with a surjection. Only surjectivity of the comparison is used, so neither
fullness nor faithfulness of the mediating `1`-morphism enters. -/
public theorem exact_tangentPairOfLift_tangentLegDiffOfEq
    (pF : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k)
    (pH : H ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k)
    (pG : G ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k)
    (pW : W ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k)
    (f : H ⥤ F) (g : G ⥤ F) (A : W ⥤ H) (B : W ⥤ G)
    (hf : f ⋙ pF = pH) (hg : g ⋙ pF = pG) (hA : A ⋙ pH = pW) (hB : B ⋙ pG = pW)
    (t : A ⋙ f ≅ B ⋙ g)
    (ht : ∀ x, pF.IsHomLift (𝟙 (pW.obj x)) (t.hom.app x))
    (hlift : (TwoFibreProductOver.lift pH pG pF f g pW A B hA hB t ht).IsEquivalence)
    (hW : IsDeformationCategory.{u, v, w} pW) (hH : IsDeformationCategory.{u, v, w} pH)
    (hG : IsDeformationCategory.{u, v, w} pG) (hF : IsDeformationCategory.{u, v, w} pF)
    (M : FGModuleCat.{max v w} k) :
    Function.Exact
      (LinearMap.prod
        (tangentMapAt.{u, v, w} hW hH
          ({ toFunctor := A, w := hA } :
            BasedCategory.ofFunctor pW ⥤ᵇ BasedCategory.ofFunctor pH) M)
        (tangentMapAt.{u, v, w} hW hG
          ({ toFunctor := B, w := hB } :
            BasedCategory.ofFunctor pW ⥤ᵇ BasedCategory.ofFunctor pG) M))
      ((tangentMapAt.{u, v, w} hH hF
            ({ toFunctor := f, w := hf } :
              BasedCategory.ofFunctor pH ⥤ᵇ BasedCategory.ofFunctor pF) M).comp
          (LinearMap.fst k ↥(tangentModuleAt.{u, v, w} (BasedCategory.ofFunctor pH) hH M)
            ↥(tangentModuleAt.{u, v, w} (BasedCategory.ofFunctor pG) hG M)) -
        (tangentMapAt.{u, v, w} hG hF
            ({ toFunctor := g, w := hg } :
              BasedCategory.ofFunctor pG ⥤ᵇ BasedCategory.ofFunctor pF) M).comp
          (LinearMap.snd k ↥(tangentModuleAt.{u, v, w} (BasedCategory.ofFunctor pH) hH M)
            ↥(tangentModuleAt.{u, v, w} (BasedCategory.ofFunctor pG) hG M))) := by
  subst hf
  subst hg
  have hP := isDeformationCategory_productBased.{u, v, w} pF f g hH hG hF
  have : (liftBased pF pW f g A B hA hB t ht).toFunctor.IsEquivalence := hlift
  rw [prod_tangentMapAt_eq_tangentProjPair_comp pF pW f g A B hA hB t ht hW hH hG hF M]
  exact exact_comp_of_surjective
    (exact_tangentProjPair_tangentLegDiff.{u, v, w} pF f g hH hG hF M)
    (tangentMapAt_surjective_of_essSurj.{u, v, w} hW hP (liftBased pF pW f g A B hA hB t ht) M)

end TangentRowTransfer

/-! ### Injectivity of the infinitesimal projection pair for a category equivalent to the
2-fibre product -/

section InfProjPairTransfer
open CategoryTheory CategoryTheory.Functor
universe u v w u₁ v₁ u₂ v₂ u₃ v₃ u₄ v₄

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
  {H : Type u₁} [Category.{v₁} H] {G : Type u₂} [Category.{v₂} G]
  {F : Type u₃} [Category.{v₃} F] {W : Type u₄} [Category.{v₄} W]

/-- The pair of maps on `Inf` induced by `A` and `B` is `Deformation.infProjPair` after the map
induced by the mediating `1`-morphism. -/
private theorem prod_inducedInfinitesimalLinearMapOfEq_eq_infProjPair_comp
    (pF : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k)
    (pW : W ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k)
    (f : H ⥤ F) (g : G ⥤ F) (A : W ⥤ H) (B : W ⥤ G)
    (hA : A ⋙ (f ⋙ pF) = pW) (hB : B ⋙ (g ⋙ pF) = pW)
    (t : A ⋙ f ≅ B ⋙ g)
    (ht : ∀ x, pF.IsHomLift (𝟙 (pW.obj x)) (t.hom.app x))
    (hW : IsDeformationCategory.{u, v, w} pW) (hH : IsDeformationCategory.{u, v, w} (f ⋙ pF))
    (hG : IsDeformationCategory.{u, v, w} (g ⋙ pF)) (hF : IsDeformationCategory.{u, v, w} pF)
    {w₀ : W} (PW : ChosenPushforwardsAt pW w₀) (QH : ChosenPushforwardsAt (f ⋙ pF) (A.obj w₀))
    (QG : ChosenPushforwardsAt (g ⋙ pF) (B.obj w₀))
    (PL : ChosenPushforwardsAt
      (TwoFibreProductOver.structureFunctor (f ⋙ pF) (g ⋙ pF) pF f g)
      ((TwoFibreProductOver.lift (f ⋙ pF) (g ⋙ pF) pF f g pW A B hA hB t ht).obj w₀)) :
    letI := naturalLocalizedTangentAddCommGroup PW hW.satisfiesRS
    letI := naturalLocalizedTangentModule PW hW.satisfiesRS
    letI := naturalLocalizedTangentAddCommGroup QH hH.satisfiesRS
    letI := naturalLocalizedTangentModule QH hH.satisfiesRS
    letI := naturalLocalizedTangentAddCommGroup QG hG.satisfiesRS
    letI := naturalLocalizedTangentModule QG hG.satisfiesRS
    letI := naturalLocalizedTangentAddCommGroup PL
      (isDeformationCategory_productBased.{u, v, w} pF f g hH hG hF).satisfiesRS
    letI := naturalLocalizedTangentModule PL
      (isDeformationCategory_productBased.{u, v, w} pF f g hH hG hF).satisfiesRS
    ⇑(LinearMap.prod
        (inducedInfinitesimalLinearMapOfEq A hA hW.satisfiesRS hH.satisfiesRS PW QH)
        (inducedInfinitesimalLinearMapOfEq B hB hW.satisfiesRS hG.satisfiesRS PW QG)) =
      infProjPair.{u, v, w} pF f g hH hG hF PL QH QG ∘
        inducedInfinitesimalLinearMapOfEq (p := pW) (liftBased pF pW f g A B hA hB t ht).toFunctor
          (liftBased pF pW f g A B hA hB t ht).w hW.satisfiesRS
          (isDeformationCategory_productBased.{u, v, w} pF f g hH hG hF).satisfiesRS PW PL := by
  let := naturalLocalizedTangentAddCommGroup PW hW.satisfiesRS
  let := naturalLocalizedTangentModule PW hW.satisfiesRS
  let := naturalLocalizedTangentAddCommGroup QH hH.satisfiesRS
  let := naturalLocalizedTangentModule QH hH.satisfiesRS
  let := naturalLocalizedTangentAddCommGroup QG hG.satisfiesRS
  let := naturalLocalizedTangentModule QG hG.satisfiesRS
  have hP := isDeformationCategory_productBased.{u, v, w} pF f g hH hG hF
  let := naturalLocalizedTangentAddCommGroup PL hP.satisfiesRS
  let := naturalLocalizedTangentModule PL hP.satisfiesRS
  refine funext fun s => Prod.ext ?_ ?_
  · exact DFunLike.congr_fun
      (inducedInfinitesimalLinearMapOfEq_comp (liftBased pF pW f g A B hA hB t ht).toFunctor
        (productFst.{u, v, w} pF f g).toFunctor (liftBased pF pW f g A B hA hB t ht).w
        (productFst.{u, v, w} pF f g).w hW.satisfiesRS hP.satisfiesRS hH.satisfiesRS PW PL QH) s
  · exact DFunLike.congr_fun
      (inducedInfinitesimalLinearMapOfEq_comp (liftBased pF pW f g A B hA hB t ht).toFunctor
        (productSnd.{u, v, w} pF f g).toFunctor (liftBased pF pW f g A B hA hB t ht).w
        (productSnd.{u, v, w} pF f g).w hW.satisfiesRS hP.satisfiesRS hG.satisfiesRS PW PL QG) s

/-- **Injectivity of the `Inf`-pair of the six-term sequence of a 2-fibre product, read on an
equivalent category.** With the data of `Deformation.exact_tangentPairOfLift_tangentLegDiffOfEq`
and a choice of pushforwards `PW`, `QH`, `QG` at `w₀`, `A(w₀)`, `B(w₀)`, the map
`Inf(𝒲) → Inf(ℋ) ⊕ Inf(𝒢)` induced by `A` and `B` is injective.

This is part (2) of Tag 06L5, `Deformation.injective_infProjPair`, transported along the
mediating equivalence: the pair of the maps induced by `A` and `B` factors through the map
induced by that equivalence (`Deformation.inducedInfinitesimalLinearMapOfEq_comp`), which is
*bijective* on infinitesimal automorphisms because the mediating `1`-morphism is fully faithful
(`Deformation.bijective_inducedInfinitesimalLinearMapOfEq`), and injectivity is inherited by
postcomposition with an injective map and precomposition with a bijective one. The extra
pushforward choice `PL`, at the image of `w₀` under the mediating equivalence, has no further
constraint on it. -/
public theorem injective_infProjPairOfLift
    (pF : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k)
    (pH : H ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k)
    (pG : G ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k)
    (pW : W ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k)
    (f : H ⥤ F) (g : G ⥤ F) (A : W ⥤ H) (B : W ⥤ G)
    (hf : f ⋙ pF = pH) (hg : g ⋙ pF = pG) (hA : A ⋙ pH = pW) (hB : B ⋙ pG = pW)
    (t : A ⋙ f ≅ B ⋙ g)
    (ht : ∀ x, pF.IsHomLift (𝟙 (pW.obj x)) (t.hom.app x))
    (hlift : (TwoFibreProductOver.lift pH pG pF f g pW A B hA hB t ht).IsEquivalence)
    (hW : IsDeformationCategory.{u, v, w} pW) (hH : IsDeformationCategory.{u, v, w} pH)
    (hG : IsDeformationCategory.{u, v, w} pG) (hF : IsDeformationCategory.{u, v, w} pF)
    {w₀ : W} (PW : ChosenPushforwardsAt pW w₀) (QH : ChosenPushforwardsAt pH (A.obj w₀))
    (QG : ChosenPushforwardsAt pG (B.obj w₀))
    (PL : ChosenPushforwardsAt
      (TwoFibreProductOver.structureFunctor pH pG pF f g)
      ((TwoFibreProductOver.lift pH pG pF f g pW A B hA hB t ht).obj w₀)) :
    letI := naturalLocalizedTangentAddCommGroup PW hW.satisfiesRS
    letI := naturalLocalizedTangentModule PW hW.satisfiesRS
    letI := naturalLocalizedTangentAddCommGroup QH hH.satisfiesRS
    letI := naturalLocalizedTangentModule QH hH.satisfiesRS
    letI := naturalLocalizedTangentAddCommGroup QG hG.satisfiesRS
    letI := naturalLocalizedTangentModule QG hG.satisfiesRS
    Function.Injective
      (LinearMap.prod
        (inducedInfinitesimalLinearMapOfEq A hA hW.satisfiesRS hH.satisfiesRS PW QH)
        (inducedInfinitesimalLinearMapOfEq B hB hW.satisfiesRS hG.satisfiesRS PW QG)) := by
  subst hf
  subst hg
  let := naturalLocalizedTangentAddCommGroup PW hW.satisfiesRS
  let := naturalLocalizedTangentModule PW hW.satisfiesRS
  let := naturalLocalizedTangentAddCommGroup QH hH.satisfiesRS
  let := naturalLocalizedTangentModule QH hH.satisfiesRS
  let := naturalLocalizedTangentAddCommGroup QG hG.satisfiesRS
  let := naturalLocalizedTangentModule QG hG.satisfiesRS
  have hP := isDeformationCategory_productBased.{u, v, w} pF f g hH hG hF
  let := naturalLocalizedTangentAddCommGroup PL hP.satisfiesRS
  let := naturalLocalizedTangentModule PL hP.satisfiesRS
  let L := liftBased pF pW f g A B hA hB t ht
  have : L.toFunctor.IsEquivalence := hlift
  have hLbij := bijective_inducedInfinitesimalLinearMapOfEq L.toFunctor L.w hW.satisfiesRS
    hP.satisfiesRS PW PL
  rw [prod_inducedInfinitesimalLinearMapOfEq_eq_infProjPair_comp pF pW f g A B hA hB t ht
    hW hH hG hF PW QH QG PL]
  exact (injective_infProjPair.{u, v, w} pF f g hH hG hF PL QH QG).comp hLbij.1

end InfProjPairTransfer

/-! ### Exactness at `Inf(ℋ) ⊕ Inf(𝒢)` for a category equivalent to the 2-fibre product -/

section InfProjPairExactTransfer
open CategoryTheory CategoryTheory.Functor
universe u v w u₁ v₁ u₂ v₂ u₃ v₃ u₄ v₄

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
  {H : Type u₁} [Category.{v₁} H] {G : Type u₂} [Category.{v₂} G]
  {F : Type u₃} [Category.{v₃} F] {W : Type u₄} [Category.{v₄} W]

/-- **Exactness of the `Inf`-row of the six-term sequence of a 2-fibre product at
`Inf(ℋ) ⊕ Inf(𝒢)`, read on an equivalent category.** With the data of
`Deformation.injective_infProjPairOfLift`, a basepoint `w₀ : 𝒲(k)` (`hw₀`), and chosen
pushforwards `PF`, `PF'` at the images of `w₀` in `ℱ` through the two legs, the kernel of the
difference of the maps induced by `f ∘ A` and (the comparison of) `g ∘ B` is the image of the
pair of the maps induced by `A` and `B`.

This is part (2) of Tag 06L5, `Deformation.exact_infProjPair_infLegDiff`, transported along the
mediating equivalence: the pair of the maps induced by `A` and `B` factors through the map
induced by that equivalence (exactly as in `Deformation.injective_infProjPairOfLift`), which is
*surjective* because the mediating `1`-morphism is an equivalence
(`Deformation.bijective_inducedInfinitesimalLinearMapOfEq`), and exactness is inherited by
precomposition with a surjection (`Deformation.exact_comp_of_surjective`). The map
`Deformation.infLegDiff` out of `Inf(ℋ) ⊕ Inf(𝒢)` does not mention `𝒲` or the mediating
equivalence at all, so it is reused unchanged. -/
public theorem exact_infProjPairOfLift
    (pF : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k)
    (pW : W ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k)
    (f : H ⥤ F) (g : G ⥤ F) (A : W ⥤ H) (B : W ⥤ G)
    (hA : A ⋙ (f ⋙ pF) = pW) (hB : B ⋙ (g ⋙ pF) = pW)
    (t : A ⋙ f ≅ B ⋙ g)
    (ht : ∀ x, pF.IsHomLift (𝟙 (pW.obj x)) (t.hom.app x))
    (hlift :
      (TwoFibreProductOver.lift (f ⋙ pF) (g ⋙ pF) pF f g pW A B hA hB t ht).IsEquivalence)
    (hW : IsDeformationCategory.{u, v, w} pW) (hH : IsDeformationCategory.{u, v, w} (f ⋙ pF))
    (hG : IsDeformationCategory.{u, v, w} (g ⋙ pF)) (hF : IsDeformationCategory.{u, v, w} pF)
    {w₀ : W} (PW : ChosenPushforwardsAt pW w₀) (QH : ChosenPushforwardsAt (f ⋙ pF) (A.obj w₀))
    (QG : ChosenPushforwardsAt (g ⋙ pF) (B.obj w₀))
    (PL : ChosenPushforwardsAt
      (TwoFibreProductOver.structureFunctor (f ⋙ pF) (g ⋙ pF) pF f g)
      ((TwoFibreProductOver.lift (f ⋙ pF) (g ⋙ pF) pF f g pW A B hA hB t ht).obj w₀))
    (PF : ChosenPushforwardsAt pF (f.obj (A.obj w₀)))
    (PF' : ChosenPushforwardsAt pF (g.obj (B.obj w₀)))
    (hw₀ : (f ⋙ pF).obj (A.obj w₀) = residueFieldObject.{u, v, w} Λ k) :
    letI := naturalLocalizedTangentAddCommGroup.{u, v, w, u₄, v₄} PW hW.satisfiesRS
    letI := naturalLocalizedTangentModule.{u, v, w, u₄, v₄} PW hW.satisfiesRS
    letI := naturalLocalizedTangentAddCommGroup.{u, v, w, u₁, v₁} QH hH.satisfiesRS
    letI := naturalLocalizedTangentModule.{u, v, w, u₁, v₁} QH hH.satisfiesRS
    letI := naturalLocalizedTangentAddCommGroup.{u, v, w, u₂, v₂} QG hG.satisfiesRS
    letI := naturalLocalizedTangentModule.{u, v, w, u₂, v₂} QG hG.satisfiesRS
    letI := naturalLocalizedTangentAddCommGroup.{u, v, w, u₃, v₃} PF hF.satisfiesRS
    letI := naturalLocalizedTangentModule.{u, v, w, u₃, v₃} PF hF.satisfiesRS
    Function.Exact
      (LinearMap.prod
        (inducedInfinitesimalLinearMapOfEq A hA hW.satisfiesRS hH.satisfiesRS PW QH)
        (inducedInfinitesimalLinearMapOfEq B hB hW.satisfiesRS hG.satisfiesRS PW QG))
      (infLegDiff pF f g hH hG hF
        (w₀ :=
          (⟨pW.obj w₀, A.obj w₀, B.obj w₀, Functor.congr_obj hA w₀, Functor.congr_obj hB w₀,
              t.app w₀, ht w₀⟩ :
            TwoFibreProductOver (f ⋙ pF) (g ⋙ pF) pF f g))
        QH QG PF PF' hw₀) := by
  let := naturalLocalizedTangentAddCommGroup.{u, v, w, u₄, v₄} PW hW.satisfiesRS
  let := naturalLocalizedTangentModule.{u, v, w, u₄, v₄} PW hW.satisfiesRS
  let := naturalLocalizedTangentAddCommGroup.{u, v, w, u₁, v₁} QH hH.satisfiesRS
  let := naturalLocalizedTangentModule.{u, v, w, u₁, v₁} QH hH.satisfiesRS
  let := naturalLocalizedTangentAddCommGroup.{u, v, w, u₂, v₂} QG hG.satisfiesRS
  let := naturalLocalizedTangentModule.{u, v, w, u₂, v₂} QG hG.satisfiesRS
  let := naturalLocalizedTangentAddCommGroup.{u, v, w, u₃, v₃} PF hF.satisfiesRS
  let := naturalLocalizedTangentModule.{u, v, w, u₃, v₃} PF hF.satisfiesRS
  have hP := isDeformationCategory_productBased.{u, v, w} pF f g hH hG hF
  let := naturalLocalizedTangentAddCommGroup.{u, v, w} PL hP.satisfiesRS
  let := naturalLocalizedTangentModule.{u, v, w} PL hP.satisfiesRS
  let L := liftBased pF pW f g A B hA hB t ht
  have : L.toFunctor.IsEquivalence := hlift
  have hLbij := bijective_inducedInfinitesimalLinearMapOfEq L.toFunctor L.w hW.satisfiesRS
    hP.satisfiesRS PW PL
  rw [prod_inducedInfinitesimalLinearMapOfEq_eq_infProjPair_comp pF pW f g A B hA hB t ht
    hW hH hG hF PW QH QG PL]
  refine exact_comp_of_surjective ?_ hLbij.2
  exact exact_infProjPair_infLegDiff.{u, v, w} pF f g hH hG hF PL QH QG PF PF' hw₀

end InfProjPairExactTransfer

/-! ### Fibrewise fullness and faithfulness from a based functor -/

section FiberFunctorFullFaithful
open CategoryTheory CategoryTheory.Functor
universe u v u₁ v₁ u₂ v₂

variable {C : Type u} [Category.{v} C] {𝓐 : BasedCategory.{v₁, u₁} C}
  {𝓑 : BasedCategory.{v₂, u₂} C}

/-- The functor induced on a strict fibre by a faithful based functor is faithful. -/
theorem faithful_fiberFunctorOfLift (φ : BasedFunctor 𝓐 𝓑) [φ.toFunctor.Faithful]
    (A : C) : (fiberFunctor φ A).Faithful where
  map_injective {_ _} _ _ h :=
    Functor.Fiber.hom_ext (φ.toFunctor.map_injective (congrArg Functor.Fiber.fiberInclusion.map h))

/-- The functor induced on a strict fibre by a fully faithful based functor is full. -/
theorem full_fiberFunctorOfLift (φ : BasedFunctor 𝓐 𝓑) [φ.toFunctor.Full]
    [φ.toFunctor.Faithful] (A : C) : (fiberFunctor φ A).Full where
  map_surjective {x y} g := by
    obtain ⟨h, hh⟩ := φ.toFunctor.map_surjective g.val
    have htarget : 𝓑.p.IsHomLift (𝟙 A) (φ.toFunctor.map h) := by
      rw [hh]
      exact g.2
    have hsource : 𝓐.p.IsHomLift (𝟙 A) h := BasedFunctor.isHomLift_map φ (𝟙 A) h
    exact ⟨⟨h, hsource⟩, Functor.Fiber.hom_ext hh⟩

end FiberFunctorFullFaithful

/-! ### The boundary map for a category equivalent to the 2-fibre product -/

section InfBoundaryTransfer
open CategoryTheory CategoryTheory.Functor
universe u v w u₁ v₁ u₂ v₂ u₃ v₃ u₄ v₄

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
  {H : Type u₁} [Category.{v₁} H] {G : Type u₂} [Category.{v₂} G]
  {F : Type u₃} [Category.{v₃} F] {W : Type u₄} [Category.{v₄} W]

/-- The linear equivalence on tangent modules at the rank-one coordinate module induced by the
mediating equivalence `Deformation.liftBased`. -/
private noncomputable def tangentEquivOfLift
    (pF : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k)
    (pW : W ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k)
    (f : H ⥤ F) (g : G ⥤ F) (A : W ⥤ H) (B : W ⥤ G)
    (hA : A ⋙ (f ⋙ pF) = pW) (hB : B ⋙ (g ⋙ pF) = pW)
    (t : A ⋙ f ≅ B ⋙ g)
    (ht : ∀ x, pF.IsHomLift (𝟙 (pW.obj x)) (t.hom.app x))
    (hlift :
      (TwoFibreProductOver.lift (f ⋙ pF) (g ⋙ pF) pF f g pW A B hA hB t ht).IsEquivalence)
    (hW : IsDeformationCategory.{u, v, w} pW) (hH : IsDeformationCategory.{u, v, w} (f ⋙ pF))
    (hG : IsDeformationCategory.{u, v, w} (g ⋙ pF)) (hF : IsDeformationCategory.{u, v, w} pF) :
    ↥(tangentModuleAt.{u, v, w} (BasedCategory.ofFunctor pW) hW
        (FGModuleCat.of k (ULift.{v} k))) ≃ₗ[k]
      ↥(tangentModuleAt.{u, v, w} (productBased.{u, v, w} pF f g)
        (isDeformationCategory_productBased.{u, v, w} pF f g hH hG hF)
        (FGModuleCat.of k (ULift.{v} k))) :=
  have _ : (liftBased pF pW f g A B hA hB t ht).toFunctor.IsEquivalence := hlift
  tangentLinearEquivOfFiberEquivalence.{u, v, w} hW
    (isDeformationCategory_productBased.{u, v, w} pF f g hH hG hF)
    (liftBased pF pW f g A B hA hB t ht) (FGModuleCat.of k (ULift.{v} k))
    (full_fiberFunctorOfLift _ _) (faithful_fiberFunctorOfLift _ _)
    (essSurj_fiberFunctor hW.predeformation.cofibered _ _)

/-- **The boundary map `δ : Inf(ℱ) → T𝒲` of the six-term sequence, read on a category
equivalent to the 2-fibre product.** With the data of `Deformation.injective_infProjPairOfLift`,
this is `Deformation.infBoundaryLinearMap` — the boundary map out of `Inf(ℱ)` landing in the
tangent module of the 2-fibre product itself — carried across the mediating equivalence to land
in `T𝒲` instead, using that the equivalence is bijective on tangent modules at the rank-one
coordinate module (`Deformation.tangentLinearEquivOfFiberEquivalence`): fullness and
faithfulness of the fibre comparison come from fullness and faithfulness of the mediating
`1`-morphism, and essential surjectivity of the fibre comparison from essential surjectivity of
the mediating `1`-morphism together with `𝒲` being cofibered in groupoids
(`Deformation.essSurj_fiberFunctor`). -/
public noncomputable def infBoundaryLinearMapOfLift
    (pF : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k)
    (pW : W ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k)
    (f : H ⥤ F) (g : G ⥤ F) (A : W ⥤ H) (B : W ⥤ G)
    (hA : A ⋙ (f ⋙ pF) = pW) (hB : B ⋙ (g ⋙ pF) = pW)
    (t : A ⋙ f ≅ B ⋙ g)
    (ht : ∀ x, pF.IsHomLift (𝟙 (pW.obj x)) (t.hom.app x))
    (hlift :
      (TwoFibreProductOver.lift (f ⋙ pF) (g ⋙ pF) pF f g pW A B hA hB t ht).IsEquivalence)
    (hW : IsDeformationCategory.{u, v, w} pW) (hH : IsDeformationCategory.{u, v, w} (f ⋙ pF))
    (hG : IsDeformationCategory.{u, v, w} (g ⋙ pF)) (hF : IsDeformationCategory.{u, v, w} pF)
    {w₀ : W} (QH : ChosenPushforwardsAt (f ⋙ pF) (A.obj w₀))
    (QG : ChosenPushforwardsAt (g ⋙ pF) (B.obj w₀))
    (PF : ChosenPushforwardsAt pF (f.obj (A.obj w₀))) :
    letI := naturalLocalizedTangentAddCommGroup.{u, v, w, u₃, v₃} PF hF.satisfiesRS
    letI := naturalLocalizedTangentModule.{u, v, w, u₃, v₃} PF hF.satisfiesRS
    localizedAutomorphismFunctorTangent.{u, v, w, u₃, v₃} PF →ₗ[k]
      ↥(tangentModuleAt.{u, v, w} (BasedCategory.ofFunctor pW) hW
        (FGModuleCat.of k (ULift.{v} k))) :=
  letI := naturalLocalizedTangentAddCommGroup.{u, v, w, u₃, v₃} PF hF.satisfiesRS
  letI := naturalLocalizedTangentModule.{u, v, w, u₃, v₃} PF hF.satisfiesRS
  have hP := isDeformationCategory_productBased.{u, v, w} pF f g hH hG hF
  let L : BasedCategory.ofFunctor pW ⥤ᵇ productBased.{u, v, w} pF f g :=
    { toFunctor := TwoFibreProductOver.lift (f ⋙ pF) (g ⋙ pF) pF f g pW A B hA hB t ht
      w := TwoFibreProductOver.lift_comp_structureFunctor .. }
  have _ : L.toFunctor.IsEquivalence := hlift
  have hfull := full_fiberFunctorOfLift L
    ((squareZeroExtensionArtinian.{u, w, max v w} Λ k).obj (FGModuleCat.of k (ULift.{v} k)))
  have hfaithful := faithful_fiberFunctorOfLift L
    ((squareZeroExtensionArtinian.{u, w, max v w} Λ k).obj (FGModuleCat.of k (ULift.{v} k)))
  have hess := essSurj_fiberFunctor hW.predeformation.cofibered L
    ((squareZeroExtensionArtinian.{u, w, max v w} Λ k).obj (FGModuleCat.of k (ULift.{v} k)))
  ((tangentLinearEquivOfFiberEquivalence.{u, v, w} hW hP L
      (FGModuleCat.of k (ULift.{v} k)) hfull hfaithful hess).symm.toLinearMap).comp
    (infBoundaryLinearMap.{u, v, w} pF f g hH hG hF
      (w₀ :=
        (⟨pW.obj w₀, A.obj w₀, B.obj w₀, Functor.congr_obj hA w₀, Functor.congr_obj hB w₀,
            t.app w₀, ht w₀⟩ :
          TwoFibreProductOver (f ⋙ pF) (g ⋙ pF) pF f g))
      QH QG PF)

/-- **Exactness of the six-term sequence of a 2-fibre product at `Inf(ℱ)`, read on a category
equivalent to the 2-fibre product.** With the data of `Deformation.infBoundaryLinearMapOfLift`
and a chosen pushforward `PL` of the image of `w₀` in the abstract 2-fibre product, the kernel
of the boundary map `Deformation.infBoundaryLinearMapOfLift` is the image of the leg difference
`Deformation.infLegDiff`.

This is part (2) of Tag 06L5, `Deformation.exact_infLegDiff_infBoundaryLinearMap`, transported
along the mediating equivalence: `Deformation.infBoundaryLinearMapOfLift` is, by construction,
the postcomposition of `Deformation.infBoundaryLinearMap` with the (bijective) linear
equivalence `Deformation.tangentLinearEquivOfFiberEquivalence` on tangent modules, and
postcomposing the second map of an exact pair with a linear equivalence does not change
exactness (`LinearEquiv.postcomp_exact_iff_exact`). The map `Deformation.infLegDiff` out of
`Inf(ℋ) ⊕ Inf(𝒢)` does not mention `𝒲` or the mediating equivalence at all, so it is reused
unchanged. -/
public theorem exact_infLegDiff_infBoundaryLinearMapOfLift
    (pF : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k)
    (pW : W ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k)
    (f : H ⥤ F) (g : G ⥤ F) (A : W ⥤ H) (B : W ⥤ G)
    (hA : A ⋙ (f ⋙ pF) = pW) (hB : B ⋙ (g ⋙ pF) = pW)
    (t : A ⋙ f ≅ B ⋙ g)
    (ht : ∀ x, pF.IsHomLift (𝟙 (pW.obj x)) (t.hom.app x))
    (hlift :
      (TwoFibreProductOver.lift (f ⋙ pF) (g ⋙ pF) pF f g pW A B hA hB t ht).IsEquivalence)
    (hW : IsDeformationCategory.{u, v, w} pW) (hH : IsDeformationCategory.{u, v, w} (f ⋙ pF))
    (hG : IsDeformationCategory.{u, v, w} (g ⋙ pF)) (hF : IsDeformationCategory.{u, v, w} pF)
    {w₀ : W}
    (PL : ChosenPushforwardsAt
      (TwoFibreProductOver.structureFunctor (f ⋙ pF) (g ⋙ pF) pF f g)
      ((TwoFibreProductOver.lift (f ⋙ pF) (g ⋙ pF) pF f g pW A B hA hB t ht).obj w₀))
    (QH : ChosenPushforwardsAt (f ⋙ pF) (A.obj w₀))
    (QG : ChosenPushforwardsAt (g ⋙ pF) (B.obj w₀))
    (PF : ChosenPushforwardsAt pF (f.obj (A.obj w₀)))
    (PF' : ChosenPushforwardsAt pF (g.obj (B.obj w₀)))
    (hw₀ : (f ⋙ pF).obj (A.obj w₀) = residueFieldObject.{u, v, w} Λ k) :
    letI := naturalLocalizedTangentAddCommGroup.{u, v, w, u₁, v₁} QH hH.satisfiesRS
    letI := naturalLocalizedTangentModule.{u, v, w, u₁, v₁} QH hH.satisfiesRS
    letI := naturalLocalizedTangentAddCommGroup.{u, v, w, u₂, v₂} QG hG.satisfiesRS
    letI := naturalLocalizedTangentModule.{u, v, w, u₂, v₂} QG hG.satisfiesRS
    letI := naturalLocalizedTangentAddCommGroup.{u, v, w, u₃, v₃} PF hF.satisfiesRS
    letI := naturalLocalizedTangentModule.{u, v, w, u₃, v₃} PF hF.satisfiesRS
    Function.Exact
      (infLegDiff.{u, v, w} pF f g hH hG hF
        (w₀ :=
          (⟨pW.obj w₀, A.obj w₀, B.obj w₀, Functor.congr_obj hA w₀, Functor.congr_obj hB w₀,
              t.app w₀, ht w₀⟩ :
            TwoFibreProductOver (f ⋙ pF) (g ⋙ pF) pF f g))
        QH QG PF PF' hw₀)
      (infBoundaryLinearMapOfLift pF pW f g A B hA hB t ht hlift hW hH hG hF QH QG PF) := by
  let := naturalLocalizedTangentAddCommGroup.{u, v, w, u₁, v₁} QH hH.satisfiesRS
  let := naturalLocalizedTangentModule.{u, v, w, u₁, v₁} QH hH.satisfiesRS
  let := naturalLocalizedTangentAddCommGroup.{u, v, w, u₂, v₂} QG hG.satisfiesRS
  let := naturalLocalizedTangentModule.{u, v, w, u₂, v₂} QG hG.satisfiesRS
  let := naturalLocalizedTangentAddCommGroup.{u, v, w, u₃, v₃} PF hF.satisfiesRS
  let := naturalLocalizedTangentModule.{u, v, w, u₃, v₃} PF hF.satisfiesRS
  exact (LinearEquiv.postcomp_exact_iff_exact
    (e := (tangentEquivOfLift pF pW f g A B hA hB t ht hlift hW hH hG hF).symm)).mpr
    (exact_infLegDiff_infBoundaryLinearMap.{u, v, w} pF f g hH hG hF PL QH QG PF PF' hw₀)

/-- **Exactness of the six-term sequence of a 2-fibre product at `T𝒲`, read on a category
equivalent to the 2-fibre product.** The kernel of `Deformation.infBoundaryLinearMapOfLift` is
the image of the pair of the maps induced by `A` and `B`.

This is part (2) of Tag 06L5 at the term `T𝒲`,
`Deformation.exact_boundaryLinearMap_tangentProjPair`, transported along the mediating
equivalence `L`: that lemma gives exactness of `δ : Inf(ℱ) → T(ℋ ×_ℱ 𝒢)` followed by the pair
`c` of the two projections, at the literal `2`-fibre product. Changing the middle term along the
linear equivalence `Deformation.tangentLinearEquivOfFiberEquivalence` induced by `L`
(`LinearEquiv.conj_exact_iff_exact`) turns `δ` into the postcomposition that is, by
construction, `Deformation.infBoundaryLinearMapOfLift` once the extra identification of the
`Inf`-term with its own model is absorbed by precomposition with a linear equivalence
(`LinearEquiv.precomp_exact_iff_exact`), and turns `c` into `c` precomposed with the comparison.
That `c` precomposed with the comparison is the pair of the maps induced by `A` and `B` is the
same factoring argument as in `Deformation.exact_tangentPairOfLift_tangentLegDiffOfEq`: the
mediating `1`-morphism composed with each projection is, up to the defining identifications,
literally `A` (respectively `B`), since `CategoryTheory.TwoFibreProductOver.liftCompFst` and
`CategoryTheory.TwoFibreProductOver.liftCompSnd` are literal identities. -/
public theorem exact_infBoundaryLinearMapOfLift_tangentProjPairOfLift
    (pF : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k)
    (pW : W ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k)
    (f : H ⥤ F) (g : G ⥤ F) (A : W ⥤ H) (B : W ⥤ G)
    (hA : A ⋙ (f ⋙ pF) = pW) (hB : B ⋙ (g ⋙ pF) = pW)
    (t : A ⋙ f ≅ B ⋙ g)
    (ht : ∀ x, pF.IsHomLift (𝟙 (pW.obj x)) (t.hom.app x))
    (hlift :
      (TwoFibreProductOver.lift (f ⋙ pF) (g ⋙ pF) pF f g pW A B hA hB t ht).IsEquivalence)
    (hW : IsDeformationCategory.{u, v, w} pW) (hH : IsDeformationCategory.{u, v, w} (f ⋙ pF))
    (hG : IsDeformationCategory.{u, v, w} (g ⋙ pF)) (hF : IsDeformationCategory.{u, v, w} pF)
    {w₀ : W} (QH : ChosenPushforwardsAt (f ⋙ pF) (A.obj w₀))
    (QG : ChosenPushforwardsAt (g ⋙ pF) (B.obj w₀))
    (PF : ChosenPushforwardsAt pF (f.obj (A.obj w₀))) :
    letI := naturalLocalizedTangentAddCommGroup.{u, v, w, u₃, v₃} PF hF.satisfiesRS
    letI := naturalLocalizedTangentModule.{u, v, w, u₃, v₃} PF hF.satisfiesRS
    Function.Exact
      (infBoundaryLinearMapOfLift pF pW f g A B hA hB t ht hlift hW hH hG hF QH QG PF)
      (LinearMap.prod
        (tangentMapAt.{u, v, w} hW hH
          ({ toFunctor := A, w := hA } :
            BasedCategory.ofFunctor pW ⥤ᵇ BasedCategory.ofFunctor (f ⋙ pF))
          (FGModuleCat.of k (ULift.{v} k)))
        (tangentMapAt.{u, v, w} hW hG
          ({ toFunctor := B, w := hB } :
            BasedCategory.ofFunctor pW ⥤ᵇ BasedCategory.ofFunctor (g ⋙ pF))
          (FGModuleCat.of k (ULift.{v} k)))) := by
  let := naturalLocalizedTangentAddCommGroup.{u, v, w, u₃, v₃} PF hF.satisfiesRS
  let := naturalLocalizedTangentModule.{u, v, w, u₃, v₃} PF hF.satisfiesRS
  let e := tangentEquivOfLift pF pW f g A B hA hB t ht hlift hW hH hG hF
  have hzy : (g ⋙ pF).obj (B.obj w₀) = (f ⋙ pF).obj (A.obj w₀) :=
    (Functor.congr_obj hB w₀).trans (Functor.congr_obj hA w₀).symm
  have hcmp : pF.IsHomLift (𝟙 ((f ⋙ pF).obj (A.obj w₀))) (t.app w₀).hom :=
    isHomLift_fibreProduct_iso_hom.{u, v, w} pF f g
      (⟨pW.obj w₀, A.obj w₀, B.obj w₀, Functor.congr_obj hA w₀, Functor.congr_obj hB w₀,
          t.app w₀, ht w₀⟩ :
        TwoFibreProductOver (f ⋙ pF) (g ⋙ pF) pF f g)
  have habs1 := exact_boundaryLinearMap_tangentProjPair.{u, v, w} pF f g hH hG hF hzy hcmp
    QH QG PF (FGModuleCat.of k (ULift.{v} k))
  have habs2 := (LinearEquiv.conj_exact_iff_exact
    (boundaryLinearMap.{u, v, w} pF f g hH hG hF hzy hcmp QH QG PF
      (FGModuleCat.of k (ULift.{v} k)))
    (tangentProjPair.{u, v, w} pF f g hH hG hF (FGModuleCat.of k (ULift.{v} k))) e.symm).mpr habs1
  have habs3 := (LinearEquiv.precomp_exact_iff_exact
    (e := (tangentCarrierLinearEquiv.{u, v, w} PF hF.satisfiesRS).symm)).mpr habs2
  rw [prod_tangentMapAt_eq_tangentProjPair_comp pF pW f g A B hA hB t ht hW hH hG hF
    (FGModuleCat.of k (ULift.{v} k))]
  exact habs3

end InfBoundaryTransfer

end Deformation

end
