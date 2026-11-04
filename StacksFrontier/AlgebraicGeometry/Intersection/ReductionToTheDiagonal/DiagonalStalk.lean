module

public import Mathlib.RingTheory.TensorProduct.Maps
public import StacksFrontier.AlgebraicGeometry.Perfect.BaseChangeStalk

/-!
# The local ring of `X ×_Y X` at a point of the diagonal

Let `f : X ⟶ Y` be a morphism of schemes, let `x` be a point of `X`, write `R` for the local
ring of `Y` at `f x` and `A` for the local ring of `X` at `x`. The local ring of the product
`X ×_Y X` at the image `Δ(x)` of `x` under the diagonal is a localization of `A ⊗_R A`, and the
map it induces on local rings along the diagonal is, through that presentation, the
multiplication map `A ⊗_R A → A`.

## Main results

* `Stacks.Intersection.Diagonal.diagonal_stalk_isLocalization` — the local ring of `X ×_Y X` at
  `Δ(x)` is a localization of `A ⊗_R A`, compatibly with the diagonal: the composite of the
  structural map `A ⊗_R A → 𝒪_{X ×_Y X, Δ(x)}` with the local ring map of the diagonal is the
  multiplication map `A ⊗_R A → A`, and its restrictions to the two factors are the local ring
  maps of the two projections.
* `Stacks.Intersection.Diagonal.stalkMap_comp_of_retraction` — a section followed by its
  retraction induces the identity on local rings.

## References

* [Stacks Project, Tag 0B0T](https://stacks.math.columbia.edu/tag/0B0T)
* [Stacks Project, Tag 0B0U](https://stacks.math.columbia.edu/tag/0B0U)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Intersection.Diagonal

variable {X Y Z : AlgebraicGeometry.Scheme.{u}}

/-- A morphism equal to the identity induces the evident transport on local rings. -/
theorem stalkMap_eq_eqToHom_of_eq_id (k : X ⟶ X) (h : k = 𝟙 X) (x : X) :
    k.stalkMap x =
      eqToHom (congrArg X.presheaf.stalk (congrArg (fun m : X ⟶ X => m x) h)) := by
  subst h
  rw [AlgebraicGeometry.Scheme.Hom.stalkMap_id, eqToHom_refl]
  rfl

/-- **A section followed by its retraction induces the identity on local rings.** If
`i : X ⟶ Z` and `p : Z ⟶ X` satisfy `i ≫ p = 𝟙 X`, then the local ring map of `p` at `i x`
followed by that of `i` at `x` is the transport along the resulting equality of points. -/
theorem stalkMap_comp_of_retraction (i : X ⟶ Z) (p : Z ⟶ X) (h : i ≫ p = 𝟙 X) (x : X) :
    p.stalkMap (i x) ≫ i.stalkMap x =
      eqToHom (congrArg X.presheaf.stalk (congrArg (fun m : X ⟶ X => m x) h)) := by
  rw [← AlgebraicGeometry.Scheme.Hom.stalkMap_comp]
  exact stalkMap_eq_eqToHom_of_eq_id (i ≫ p) h x

/-- A presentation of a ring `C` as a localization of the tensor product of the local rings at
two points `a`, `b` of `X`, both equal to `x`, together with a common retraction
`d : C ⟶ 𝒪_{X, x}` of the two structural maps, is a presentation of `C` as a localization of
`A ⊗_R A` whose composite with `d` is the multiplication map, and whose restrictions to the two
factors are `p` and `q` transported along `ha` and `hb`. -/
theorem tensorProduct_localization_of_diagonal (f : X ⟶ Y) (a b x : X) (ha : a = x) (hb : b = x)
    (hab : f a = f b) (C : CommRingCat.{u}) (p : X.presheaf.stalk a ⟶ C)
    (q : X.presheaf.stalk b ⟶ C) (d : C ⟶ X.presheaf.stalk x)
    (hp : p ≫ d = eqToHom (congrArg X.presheaf.stalk ha))
    (hq : q ≫ d = eqToHom (congrArg X.presheaf.stalk hb))
    (H : letI := (f.stalkMap a).hom.toAlgebra
      letI := ((eqToHom (congrArg Y.presheaf.stalk hab)) ≫ f.stalkMap b).hom.toAlgebra
      ∃ φ : TensorProduct (Y.presheaf.stalk (f a))
          (X.presheaf.stalk a) (X.presheaf.stalk b) →+* C,
        φ.comp Algebra.TensorProduct.includeLeftRingHom = p.hom ∧
        φ.comp Algebra.TensorProduct.includeRight.toRingHom = q.hom ∧
        letI := φ.toAlgebra
        ∃ M : Submonoid (TensorProduct (Y.presheaf.stalk (f a))
          (X.presheaf.stalk a) (X.presheaf.stalk b)), IsLocalization M C) :
    letI := (f.stalkMap x).hom.toAlgebra
    ∃ φ : TensorProduct (Y.presheaf.stalk (f x))
        (X.presheaf.stalk x) (X.presheaf.stalk x) →+* C,
      φ.comp Algebra.TensorProduct.includeLeftRingHom =
        (eqToHom (congrArg X.presheaf.stalk ha.symm) ≫ p).hom ∧
      φ.comp Algebra.TensorProduct.includeRight.toRingHom =
        (eqToHom (congrArg X.presheaf.stalk hb.symm) ≫ q).hom ∧
      d.hom.comp φ = (Algebra.TensorProduct.lmul' (Y.presheaf.stalk (f x))
        (S := X.presheaf.stalk x)).toRingHom ∧
      letI := φ.toAlgebra
      ∃ M : Submonoid (TensorProduct (Y.presheaf.stalk (f x))
        (X.presheaf.stalk x) (X.presheaf.stalk x)), IsLocalization M C := by
  subst a b
  simp only [eqToHom_refl] at H hp hq
  let := (f.stalkMap x).hom.toAlgebra
  obtain ⟨φ, hleft, hright, M, hM⟩ := H
  refine ⟨φ, ?_, ?_, ?_, M, hM⟩
  · rwa [eqToHom_refl, Category.id_comp]
  · rwa [eqToHom_refl, Category.id_comp]
  · apply Algebra.TensorProduct.ringHom_ext
    · have key : (d.hom.comp φ).comp Algebra.TensorProduct.includeLeftRingHom =
          d.hom.comp p.hom := by rw [← hleft]; rfl
      exact key.trans ((congrArg CommRingCat.Hom.hom hp).trans
        (congrArg AlgHom.toRingHom
          (Algebra.TensorProduct.lmul'_comp_includeLeft
            (R := Y.presheaf.stalk (f x)) (S := X.presheaf.stalk x))).symm)
    · have key : (d.hom.comp φ).comp Algebra.TensorProduct.includeRight.toRingHom =
          d.hom.comp q.hom := by rw [← hright]; rfl
      exact key.trans ((congrArg CommRingCat.Hom.hom hq).trans
        (congrArg AlgHom.toRingHom
          (Algebra.TensorProduct.lmul'_comp_includeRight
            (R := Y.presheaf.stalk (f x)) (S := X.presheaf.stalk x))).symm)

/-- The first projection sends the diagonal point `Δ(x)` to `x`. -/
theorem pullback_fst_diagonal_apply (f : X ⟶ Y) (x : X) :
    pullback.fst f f ((pullback.diagonal f) x) = x := by
  rw [← AlgebraicGeometry.Scheme.Hom.comp_apply, pullback.diagonal_fst]; rfl

/-- The second projection sends the diagonal point `Δ(x)` to `x`. -/
theorem pullback_snd_diagonal_apply (f : X ⟶ Y) (x : X) :
    pullback.snd f f ((pullback.diagonal f) x) = x := by
  rw [← AlgebraicGeometry.Scheme.Hom.comp_apply, pullback.diagonal_snd]; rfl

/-- **The local ring of `X ×_Y X` at a point of the diagonal.** Let `f : X ⟶ Y` be a morphism of
schemes and `x` a point of `X`. Write `R = 𝒪_{Y, f x}`, `A = 𝒪_{X, x}` and
`B = 𝒪_{X ×_Y X, Δ(x)}`. Then `B` is a localization of `A ⊗_R A`: there is a ring map
`φ : A ⊗_R A → B` making `B` a localization of `A ⊗_R A` at a multiplicative set, whose
restrictions to the two factors are the two stalk maps of the projections `pr₁`, `pr₂` of
`X ×_Y X` at `Δ(x)` (transported along `pr_i(Δ(x)) = x`), and whose composite with the local
ring map `B → A` of the diagonal is the multiplication map `lmul' : A ⊗_R A → A`. -/
theorem diagonal_stalk_isLocalization (f : X ⟶ Y) (x : X) :
    letI := (f.stalkMap x).hom.toAlgebra
    ∃ φ : TensorProduct (Y.presheaf.stalk (f x))
        (X.presheaf.stalk x) (X.presheaf.stalk x) →+*
          (pullback f f).presheaf.stalk (pullback.diagonal f x),
      φ.comp Algebra.TensorProduct.includeLeftRingHom =
        (eqToHom (congrArg X.presheaf.stalk (pullback_fst_diagonal_apply f x).symm) ≫
          (pullback.fst f f).stalkMap ((pullback.diagonal f) x)).hom ∧
      φ.comp Algebra.TensorProduct.includeRight.toRingHom =
        (eqToHom (congrArg X.presheaf.stalk (pullback_snd_diagonal_apply f x).symm) ≫
          (pullback.snd f f).stalkMap ((pullback.diagonal f) x)).hom ∧
      ((pullback.diagonal f).stalkMap x).hom.comp φ =
        (Algebra.TensorProduct.lmul' (Y.presheaf.stalk (f x))
          (S := X.presheaf.stalk x)).toRingHom ∧
      letI := φ.toAlgebra
      ∃ M : Submonoid (TensorProduct (Y.presheaf.stalk (f x))
        (X.presheaf.stalk x) (X.presheaf.stalk x)),
        IsLocalization M ((pullback f f).presheaf.stalk (pullback.diagonal f x)) :=
  tensorProduct_localization_of_diagonal f _ _ x (pullback_fst_diagonal_apply f x)
    (pullback_snd_diagonal_apply f x)
    (congrArg (fun m : pullback f f ⟶ Y ↦ m ((pullback.diagonal f) x)) pullback.condition)
    _ _ _ ((pullback.diagonal f).stalkMap x)
    (stalkMap_comp_of_retraction _ _ (pullback.diagonal_fst f) x)
    (stalkMap_comp_of_retraction _ _ (pullback.diagonal_snd f) x)
    (AlgebraicGeometry.BaseChangeStalk.pullback_stalk_isLocalization f f
      ((pullback.diagonal f) x))

end Stacks.Intersection.Diagonal

end
