module

public import StacksFrontier.AlgebraicGeometry.Pullback.StalkTensor

/-!
# The local rings of a fibre product of two schemes over an affine base

Let `A` be a commutative ring and let `X` and `Y` be schemes over `Spec A`, with fibre product
`W = X ×_{Spec A} Y` and projections `pr₁ : W ⟶ X`, `pr₂ : W ⟶ Y`.  For a point `w` of `W`,
**the local ring `𝒪_{W, w}` is a localization of `𝒪_{X, pr₁ w} ⊗[A] 𝒪_{Y, pr₂ w}` at a prime
ideal**, namely at the contraction of the maximal ideal of `𝒪_{W, w}` along the canonical map
`a ⊗ b ↦ pr₁^♯ a · pr₂^♯ b`.

## Main results

* `AlgebraicGeometry.exists_isLocalization_atPrime_stalk_pullback_tensorProduct`.

## Implementation notes

This is the argument of `AlgebraicGeometry.exists_isLocalization_atPrime_stalk_tensorProduct`
(the case `Y = Spec B`) with both factors localized: the morphism
`Spec (𝒪_{X, x} ⊗[A] 𝒪_{Y, y}) ⟶ W` is, up to the isomorphism of `Spec` of a pushout with a fibre
product, the map `pullback.map` of the two canonical morphisms `Spec 𝒪_{X, x} ⟶ X` and
`Spec 𝒪_{Y, y} ⟶ Y`.  Both are flat preimmersions, so `pullback.map` of them is one
(`CategoryTheory.MorphismProperty.pullbackMap`), and a flat preimmersion is an isomorphism on
local rings.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

open scoped TensorProduct

universe u

namespace AlgebraicGeometry

/-- The composite `R → Γ(X, ⊤) → 𝒪_{X, x}` has `Spec` the canonical morphism
`Spec 𝒪_{X, x} ⟶ X` followed by `f`. -/
alias specMap_stalkStructureMap' := AlgebraicGeometry.specMap_stalkStructureMap

/-- **The local ring of a fibre product over an affine base is a localization of the tensor
product of the local rings.**  Let `X` and `Y` be schemes over `Spec A` and `w` a point of
`W = X ×_{Spec A} Y`.  There is a ring homomorphism
`ψ : 𝒪_{X, pr₁ w} ⊗[A] 𝒪_{Y, pr₂ w} → 𝒪_{W, w}` restricting on the two factors to the maps on
local rings induced by the projections, and `ψ` exhibits `𝒪_{W, w}` as the localization of the
tensor product at the contraction of the maximal ideal of `𝒪_{W, w}`. -/
theorem exists_isLocalization_atPrime_stalk_pullback_tensorProduct
    (A : Type u) [CommRing A] {X Y : Scheme.{u}} (f : X ⟶ Spec (.of A)) (g : Y ⟶ Spec (.of A))
    (w : (pullback f g : Scheme.{u})) :
    letI : Algebra A (X.presheaf.stalk (pullback.fst f g w)) :=
      ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop ≫
        X.presheaf.germ ⊤ (pullback.fst f g w) trivial).hom.toAlgebra
    letI : Algebra A (Y.presheaf.stalk (pullback.snd f g w)) :=
      ((Scheme.ΓSpecIso (.of A)).inv ≫ g.appTop ≫
        Y.presheaf.germ ⊤ (pullback.snd f g w) trivial).hom.toAlgebra
    ∃ ψ : X.presheaf.stalk (pullback.fst f g w) ⊗[A] Y.presheaf.stalk (pullback.snd f g w) →+*
        (pullback f g).presheaf.stalk w,
      ψ.comp Algebra.TensorProduct.includeLeftRingHom = ((pullback.fst f g).stalkMap w).hom ∧
      ψ.comp Algebra.TensorProduct.includeRight.toRingHom =
        ((pullback.snd f g).stalkMap w).hom ∧
      letI : Algebra (X.presheaf.stalk (pullback.fst f g w) ⊗[A]
        Y.presheaf.stalk (pullback.snd f g w)) ((pullback f g).presheaf.stalk w) := ψ.toAlgebra
      IsLocalization.AtPrime ((pullback f g).presheaf.stalk w)
        (Ideal.comap ψ (IsLocalRing.maximalIdeal ((pullback f g).presheaf.stalk w))) := by
  let W := (pullback f g : Scheme.{u})
  let p₁ : W ⟶ X := pullback.fst f g
  let p₂ : W ⟶ Y := pullback.snd f g
  let ax : CommRingCat.of A ⟶ X.presheaf.stalk (p₁ w) :=
    (Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop ≫ X.presheaf.germ ⊤ (p₁ w) trivial
  let ay : CommRingCat.of A ⟶ Y.presheaf.stalk (p₂ w) :=
    (Scheme.ΓSpecIso (.of A)).inv ≫ g.appTop ≫ Y.presheaf.germ ⊤ (p₂ w) trivial
  let : Algebra A (X.presheaf.stalk (p₁ w)) := ax.hom.toAlgebra
  let : Algebra A (Y.presheaf.stalk (p₂ w)) := ay.hom.toAlgebra
  let P : CommRingCat.{u} :=
    CommRingCat.of (X.presheaf.stalk (p₁ w) ⊗[A] Y.presheaf.stalk (p₂ w))
  let il : X.presheaf.stalk (p₁ w) ⟶ P :=
    CommRingCat.ofHom (R := X.presheaf.stalk (p₁ w))
      (S := X.presheaf.stalk (p₁ w) ⊗[A] Y.presheaf.stalk (p₂ w))
      Algebra.TensorProduct.includeLeftRingHom
  let ir : Y.presheaf.stalk (p₂ w) ⟶ P :=
    CommRingCat.ofHom (R := Y.presheaf.stalk (p₂ w))
      (S := X.presheaf.stalk (p₁ w) ⊗[A] Y.presheaf.stalk (p₂ w))
      Algebra.TensorProduct.includeRight.toRingHom
  have hpo : IsPushout ax ay il ir :=
    CommRingCat.isPushout_tensorProduct A (X.presheaf.stalk (p₁ w)) (Y.presheaf.stalk (p₂ w))
  have hax : Spec.map ax = X.fromSpecStalk (p₁ w) ≫ f := specMap_stalkStructureMap' f (p₁ w)
  have hay : Spec.map ay = Y.fromSpecStalk (p₂ w) ≫ g := specMap_stalkStructureMap' g (p₂ w)
  have hab : ax ≫ p₁.stalkMap w = ay ≫ p₂.stalkMap w := by
    apply Spec.map_injective
    rw [Spec.map_comp ax, Spec.map_comp ay, hax, hay, ← Category.assoc, ← Category.assoc,
      Scheme.SpecMap_stalkMap_fromSpecStalk, Scheme.SpecMap_stalkMap_fromSpecStalk,
      Category.assoc, Category.assoc]
    exact congrArg (W.fromSpecStalk w ≫ ·) pullback.condition
  let Φ : P ⟶ W.presheaf.stalk w := hpo.desc (p₁.stalkMap w) (p₂.stalkMap w) hab
  have hleft : il ≫ Φ = p₁.stalkMap w := hpo.inl_desc _ _ _
  have hright : ir ≫ Φ = p₂.stalkMap w := hpo.inr_desc _ _ _
  refine ⟨Φ.hom, ?_, ?_, ?_⟩
  · exact congrArg CommRingCat.Hom.hom hleft
  · exact congrArg CommRingCat.Hom.hom hright
  have hsq : IsPullback (Spec.map il) (Spec.map ir) (Spec.map ax) (Spec.map ay) :=
    isPullback_SpecMap_of_isPushout ax ay il ir hpo
  let m : pullback (Spec.map ax) (Spec.map ay) ⟶ W :=
    pullback.map (Spec.map ax) (Spec.map ay) f g (X.fromSpecStalk (p₁ w))
      (Y.fromSpecStalk (p₂ w)) (𝟙 _) ((Category.comp_id _).trans hax)
      ((Category.comp_id _).trans hay)
  have : Flat (X.fromSpecStalk (p₁ w)) := flat_fromSpecStalk X (p₁ w)
  have : Flat (Y.fromSpecStalk (p₂ w)) := flat_fromSpecStalk Y (p₂ w)
  have hmflat : Flat m :=
    MorphismProperty.pullbackMap (P := @Flat) (f := Spec.map ax) (g := Spec.map ay)
      (f' := f) (g' := g) inferInstance inferInstance hax hay
  have : MorphismProperty.IsStableUnderComposition @IsPreimmersion :=
    MorphismProperty.IsMultiplicative.toIsStableUnderComposition
  have hmpre : IsPreimmersion m :=
    MorphismProperty.pullbackMap (P := @IsPreimmersion) (f := Spec.map ax) (g := Spec.map ay)
      (f' := f) (g' := g) inferInstance inferInstance hax hay
  let v : Spec P ⟶ W := hsq.isoPullback.hom ≫ m
  have hvleft : v ≫ p₁ = Spec.map il ≫ X.fromSpecStalk (p₁ w) := by
    simp only [v, m, p₁, pullback.map, Category.assoc, pullback.lift_fst,
      IsPullback.isoPullback_hom_fst_assoc]
  have hvright : v ≫ p₂ = Spec.map ir ≫ Y.fromSpecStalk (p₂ w) := by
    simp only [v, m, p₂, pullback.map, Category.assoc, pullback.lift_snd,
      IsPullback.isoPullback_hom_snd_assoc]
  have : Flat v := inferInstance
  have : IsPreimmersion v := inferInstance
  have hfac : Spec.map Φ ≫ v = W.fromSpecStalk w := by
    apply pullback.hom_ext
    · rw [Category.assoc, hvleft, ← Category.assoc, ← Spec.map_comp, hleft,
        Scheme.SpecMap_stalkMap_fromSpecStalk]
    · rw [Category.assoc, hvright, ← Category.assoc, ← Spec.map_comp, hright,
        Scheme.SpecMap_stalkMap_fromSpecStalk]
  let q : Spec P := Spec.map Φ (IsLocalRing.closedPoint (W.presheaf.stalk w))
  have : IsIso (v.stalkMap q) := isIso_stalkMap_of_flat_isPreimmersion v q
  let ρ : (Spec P).presheaf.stalk q ⟶ W.presheaf.stalk w :=
    Scheme.stalkClosedPointTo (Spec.map Φ)
  have hρcomp : IsIso (v.stalkMap q ≫ ρ) := by
    have h : IsIso (Scheme.stalkClosedPointTo (Spec.map Φ ≫ v)) := by
      rw [hfac, Scheme.stalkClosedPointTo_fromSpecStalk]
      infer_instance
    change IsIso (v.stalkMap ((Spec.map Φ) (IsLocalRing.closedPoint (W.presheaf.stalk w))) ≫
      Scheme.stalkClosedPointTo (Spec.map Φ))
    rwa [← Scheme.stalkClosedPointTo_comp]
  have : IsIso ρ := (isIso_comp_left_iff _ _).mp hρcomp
  let : Algebra P ((Spec P).presheaf.stalk q) := StructureSheaf.stalkAlgebra P q
  have hmap : CommRingCat.ofHom (algebraMap P ((Spec P).presheaf.stalk q)) ≫ ρ = Φ := by
    change StructureSheaf.toStalk P q ≫ ρ = Φ
    change ((Scheme.ΓSpecIso P).inv ≫ (Spec P).presheaf.germ ⊤ q trivial) ≫ ρ = Φ
    rw [Category.assoc, Scheme.germ_stalkClosedPointTo_Spec]
    simp
  let e : ((Spec P).presheaf.stalk q : Type u) ≃+* W.presheaf.stalk w :=
    (asIso ρ).commRingCatIsoToRingEquiv
  let : Algebra P (W.presheaf.stalk w) := Φ.hom.toAlgebra
  let ae : ((Spec P).presheaf.stalk q : Type u) ≃ₐ[P] W.presheaf.stalk w :=
    AlgEquiv.ofRingEquiv (f := e) (fun r => DFunLike.congr_fun (CommRingCat.hom_ext_iff.mp hmap) r)
  have : q.asIdeal.IsPrime := q.2
  have : IsLocalization.AtPrime ((Spec P).presheaf.stalk q) q.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk P q
  exact IsLocalization.isLocalization_of_algEquiv q.asIdeal.primeCompl ae

end AlgebraicGeometry

end
