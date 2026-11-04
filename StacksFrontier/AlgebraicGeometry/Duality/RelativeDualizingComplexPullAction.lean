module

public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingComplex
public import StacksFrontier.AlgebraicGeometry.Duality.OpenImmersion.SheafHomRestrictionCurry

/-!
# The map defined by `ξ` under restriction along an open immersion

Let `(K, ξ)` consist of an object `K` of `D(𝒪_X)` and a map `ξ : Δ_*𝒪_X ⟶ L pr₁^*K|_W`, for a
diagonal open `W` of `f : X ⟶ S`. The second condition of a relative dualizing complex
(Stacks 0E2T) is that the map `Δ_*𝒪_X ⟶ R𝓗om(Δ_*𝒪_X, L pr₁^*K|_W)` defined by `ξ` is an
isomorphism; that map is the transpose of the derived multiplication followed by `ξ`.

Let `g : W' ⟶ W` be an open immersion from a diagonal open `W'` of a second morphism, together
with identifications `Lg^*(Δ_*𝒪_X) ≅ Δ'_*𝒪_{X'}` and `Lg^*(L pr₁^*K|_W) ≅ L pr₁'^*K'|_{W'}`, the
first carrying the derived multiplication of `Δ_*𝒪_X` to that of `Δ'_*𝒪_{X'}`. This file shows
that the map defined by the transported `ξ` is `Lg^*` of the map defined by `ξ`, read through
the canonical isomorphism `Lg^* R𝓗om(P, Z) ≅ R𝓗om(Lg^*P, Lg^*Z)` of Stacks 08DL. So the second
condition passes from `W` to `W'`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.DiagonalOpen.curry_diagonalAction`: the transpose of the map
  defined by `ξ` is the derived multiplication followed by `ξ`.
* `AlgebraicGeometry.Scheme.Hom.DiagonalOpen.curry_symm_transport`: the transported map, for
  arbitrary objects of `D(𝒪)`.
* `AlgebraicGeometry.Scheme.Hom.DiagonalOpen.isIso_diagonalAction_transport`: the second
  condition passes along `g`.

## References

* [Stacks Project, Definition 48.28.1 (Tag 0E2T)](https://stacks.math.columbia.edu/tag/0E2T)
* [Stacks Project, Tag 08DL](https://stacks.math.columbia.edu/tag/08DL)
* [Stacks Project, Tag 08J8](https://stacks.math.columbia.edu/tag/08J8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite StrictlyPerfect
open Stacks.Duality.TwistedInverseImageDuality

universe u

namespace AlgebraicGeometry.Scheme.Hom.DiagonalOpen

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance] Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorObjAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.hasMapBifunctorSheafTensor

variable {X S : Scheme.{u}} {f : X ⟶ S} (D : DiagonalOpen f)
  (K : DerivedCategory (OXMod.{u, u} X.toRingedSpace))

/-- The derived multiplication of `Δ_*𝒪_X`, `Δ_*𝒪_X ⊗ᴸ Δ_*𝒪_X ⟶ Δ_*𝒪_X`. -/
abbrev diagonalMul :
    ((tensor D.W).obj D.diagonalObject).obj D.diagonalObject ⟶ D.diagonalObject :=
  Stacks.RelativeSpec.AlgebraSheaf.derivedMul D.diagonalAlgebra

/-- The map defined by `ξ`, read through the bijection of Stacks 08DI it is defined by, is the
derived multiplication of `Δ_*𝒪_X` followed by `ξ`. -/
theorem derivedSheafHomTensorEquiv_diagonalAction
    (ξ : D.diagonalObject ⟶ D.derivedPullbackProj K) :
    (Stacks.SheafOfModules.derivedSheafHomTensorEquiv D.W.sheaf _ _ _) (D.diagonalAction K ξ) =
      Stacks.RelativeSpec.AlgebraSheaf.derivedMul D.diagonalAlgebra ≫ ξ := by
  unfold diagonalAction
  simp only [AddEquiv.apply_symm_apply]

/-- **The transpose of the map defined by `ξ`** under the tensor–internal-Hom bijection of
Stacks 08J8 is the derived multiplication of `Δ_*𝒪_X` followed by `ξ`.

The bijection of Stacks 08J8 is defined from that of Stacks 08DI; the two spellings of the
derived internal Hom meet in the instance arguments of the coercion, which `congr 1` compares
one at a time. -/
theorem curry_diagonalAction (ξ : D.diagonalObject ⟶ D.derivedPullbackProj K) :
    curry D.W _ _ _ (D.diagonalAction K ξ) = D.diagonalMul ≫ ξ := by
  simp only [curry, tensorHomAdjunction, RingedSite.derivedTensorSheafHomAdjunction,
    Adjunction.mkOfHomEquiv_homEquiv, Equiv.symm_mk, Equiv.coe_fn_mk]
  refine (Eq.congr_left ?_).mpr (derivedSheafHomTensorEquiv_diagonalAction D K ξ)
  congr 1

/-- The tensor–internal-Hom bijection is natural in the target. -/
theorem curry_naturality_right {Y : Scheme.{u}} {A B Z Z' : Std Y}
    (θ : A ⟶ ((sheafHom Y).obj (op B)).obj Z) (w : Z ⟶ Z') :
    curry Y A B Z' (θ ≫ ((sheafHom Y).obj (op B)).map w) = curry Y A B Z θ ≫ w :=
  (tensorHomAdjunction Y B).homEquiv_naturality_right_symm θ w

section Transport

variable {A B : Scheme.{u}} (g : A ⟶ B) [IsOpenImmersion g]
  {Δ L : Std B} (μ : ((tensor B).obj Δ).obj Δ ⟶ Δ) (ξ : Δ ⟶ L)
  {Δ' L' : Std A} (μ' : ((tensor A).obj Δ').obj Δ' ⟶ Δ')
  (eΔ : (pull g).obj Δ ≅ Δ') (eP : (pull g).obj L ≅ L')

omit [IsOpenImmersion g] in
/-- **Transposes along an open immersion.** Let `μ : Δ ⊗ᴸ Δ ⟶ Δ` on `B`, `μ'` on `A`, and
`eΔ : Lg^*Δ ≅ Δ'` carrying `Lg^*μ` to `μ'`. For `ξ : Δ ⟶ L` and `eP : Lg^*L ≅ L'`, the inverse
transpose of `μ' ≫ eΔ⁻¹ ≫ Lg^*ξ ≫ eP` is `Lg^*` of the inverse transpose of `μ ≫ ξ`, read through
the canonical map `Lg^* R𝓗om(Δ, L) ⟶ R𝓗om(Lg^*Δ, Lg^*L)` and the two identifications. -/
theorem curry_symm_transport
    (hmul : μ' ≫ eΔ.inv = ((tensor A).map eΔ.inv).app Δ' ≫
      ((tensor A).obj ((pull g).obj Δ)).map eΔ.inv ≫ (pullTensorIso g Δ Δ).inv ≫ (pull g).map μ) :
    (curry A _ _ _).symm (μ' ≫ eΔ.inv ≫ (pull g).map ξ ≫ eP.hom) =
      eΔ.inv ≫ ((((pull g).map ((curry B _ _ _).symm (μ ≫ ξ)) ≫ pullSheafHomMap g Δ L) ≫
          ((sheafHom A).map eΔ.inv.op).app ((pull g).obj L)) ≫
            ((sheafHom A).obj (op Δ')).map eP.hom) := by
  rw [Equiv.symm_apply_eq, curry_naturality_left, curry_naturality_right, curry_naturality_middle,
    curry_pull_map_comp_pullSheafHomMap, Equiv.apply_symm_apply, Functor.map_comp]
  simp only [Category.assoc, reassoc_of% hmul]

/-- **Invertibility passes along an open immersion**, in the situation of
`curry_symm_transport`: if the transpose of `θ` is `μ ≫ ξ` and `θ` is invertible, then so is
any `θ'` whose transpose is `μ' ≫ eΔ⁻¹ ≫ Lg^*ξ ≫ eP`. -/
theorem isIso_of_curry_transport
    (hmul : μ' ≫ eΔ.inv = ((tensor A).map eΔ.inv).app Δ' ≫
      ((tensor A).obj ((pull g).obj Δ)).map eΔ.inv ≫ (pullTensorIso g Δ Δ).inv ≫ (pull g).map μ)
    (θ : Δ ⟶ ((sheafHom B).obj (op Δ)).obj L) (hθ : curry B _ _ _ θ = μ ≫ ξ)
    (θ' : Δ' ⟶ ((sheafHom A).obj (op Δ')).obj L')
    (hθ' : curry A _ _ _ θ' = μ' ≫ eΔ.inv ≫ (pull g).map ξ ≫ eP.hom) (h : IsIso θ) :
    IsIso θ' := by
  rw [← (curry A _ _ _).symm_apply_apply θ', hθ', curry_symm_transport g μ ξ μ' eΔ eP hmul,
    ← hθ, Equiv.symm_apply_apply]
  have := isIso_pullSheafHomMap g Δ L
  infer_instance

/-- **Conversely, invertibility comes back along an open immersion**: in the situation of
`isIso_of_curry_transport`, if `θ'` is invertible then so is `Lg^*θ`. -/
theorem isIso_pull_of_curry_transport
    (hmul : μ' ≫ eΔ.inv = ((tensor A).map eΔ.inv).app Δ' ≫
      ((tensor A).obj ((pull g).obj Δ)).map eΔ.inv ≫ (pullTensorIso g Δ Δ).inv ≫ (pull g).map μ)
    (θ : Δ ⟶ ((sheafHom B).obj (op Δ)).obj L) (hθ : curry B _ _ _ θ = μ ≫ ξ)
    (θ' : Δ' ⟶ ((sheafHom A).obj (op Δ')).obj L')
    (hθ' : curry A _ _ _ θ' = μ' ≫ eΔ.inv ≫ (pull g).map ξ ≫ eP.hom) (h : IsIso θ') :
    IsIso ((pull g).map θ) := by
  rw [← (curry A _ _ _).symm_apply_apply θ', hθ', curry_symm_transport g μ ξ μ' eΔ eP hmul,
    ← hθ, Equiv.symm_apply_apply] at h
  have := isIso_pullSheafHomMap g Δ L
  have := h
  have : IsIso ((((pull g).map θ ≫ pullSheafHomMap g Δ L) ≫
      ((sheafHom A).map eΔ.inv.op).app ((pull g).obj L)) ≫
        ((sheafHom A).obj (op Δ')).map eP.hom) :=
    IsIso.of_isIso_comp_left eΔ.inv _
  have : IsIso (((pull g).map θ ≫ pullSheafHomMap g Δ L) ≫
      ((sheafHom A).map eΔ.inv.op).app ((pull g).obj L)) :=
    IsIso.of_isIso_comp_right _ (((sheafHom A).obj (op Δ')).map eP.hom)
  have : IsIso ((pull g).map θ ≫ pullSheafHomMap g Δ L) :=
    IsIso.of_isIso_comp_right _ (((sheafHom A).map eΔ.inv.op).app ((pull g).obj L))
  exact IsIso.of_isIso_comp_right _ (pullSheafHomMap g Δ L)

end Transport

variable {X' S' : Scheme.{u}} {f' : X' ⟶ S'} (D' : DiagonalOpen f')
  (K' : DerivedCategory (OXMod.{u, u} X'.toRingedSpace))
  (g : D'.W ⟶ D.W) [IsOpenImmersion g]

/-- **The second condition of Stacks 0E2T passes along an open immersion of diagonal opens.**
Let `eΔ : Lg^*(Δ_*𝒪_X) ≅ Δ'_*𝒪_{X'}` carry the derived multiplication of `Δ_*𝒪_X` to that of
`Δ'_*𝒪_{X'}`, and let `eP : Lg^*(L pr₁^*K|_W) ≅ L pr₁'^*K'|_{W'}`. If the map defined by `ξ`
is an isomorphism, so is the map defined by the transported `eΔ⁻¹ ≫ Lg^*ξ ≫ eP`. -/
theorem isIso_diagonalAction_transport (ξ : D.diagonalObject ⟶ D.derivedPullbackProj K)
    (eΔ : (pull g).obj D.diagonalObject ≅ D'.diagonalObject)
    (eP : (pull g).obj (D.derivedPullbackProj K) ≅ D'.derivedPullbackProj K')
    (hmul : D'.diagonalMul ≫ eΔ.inv =
      ((tensor D'.W).map eΔ.inv).app D'.diagonalObject ≫
        ((tensor D'.W).obj ((pull g).obj D.diagonalObject)).map eΔ.inv ≫
          (pullTensorIso g D.diagonalObject D.diagonalObject).inv ≫ (pull g).map D.diagonalMul)
    (h : IsIso (D.diagonalAction K ξ)) :
    IsIso (D'.diagonalAction K' (eΔ.inv ≫ (pull g).map ξ ≫ eP.hom)) :=
  isIso_of_curry_transport (Δ := D.diagonalObject) (L := D.derivedPullbackProj K)
    (Δ' := D'.diagonalObject) (L' := D'.derivedPullbackProj K') g D.diagonalMul ξ
    D'.diagonalMul eΔ eP hmul (D.diagonalAction K ξ) (curry_diagonalAction D K ξ)
    (D'.diagonalAction K' (eΔ.inv ≫ (pull g).map ξ ≫ eP.hom))
    (curry_diagonalAction D' K' _) h

/-- **Invertibility of the restricted map gives invertibility of `Lg^*` of the map defined by
`ξ`**, the converse direction of `isIso_diagonalAction_transport`, for local-to-global
arguments. -/
theorem isIso_pull_diagonalAction_of_transport (ξ : D.diagonalObject ⟶ D.derivedPullbackProj K)
    (eΔ : (pull g).obj D.diagonalObject ≅ D'.diagonalObject)
    (eP : (pull g).obj (D.derivedPullbackProj K) ≅ D'.derivedPullbackProj K')
    (hmul : D'.diagonalMul ≫ eΔ.inv =
      ((tensor D'.W).map eΔ.inv).app D'.diagonalObject ≫
        ((tensor D'.W).obj ((pull g).obj D.diagonalObject)).map eΔ.inv ≫
          (pullTensorIso g D.diagonalObject D.diagonalObject).inv ≫ (pull g).map D.diagonalMul)
    (h : IsIso (D'.diagonalAction K' (eΔ.inv ≫ (pull g).map ξ ≫ eP.hom))) :
    IsIso ((pull g).map (D.diagonalAction K ξ)) :=
  isIso_pull_of_curry_transport (Δ := D.diagonalObject) (L := D.derivedPullbackProj K)
    (Δ' := D'.diagonalObject) (L' := D'.derivedPullbackProj K') g D.diagonalMul ξ
    D'.diagonalMul eΔ eP hmul (D.diagonalAction K ξ) (curry_diagonalAction D K ξ)
    (D'.diagonalAction K' (eΔ.inv ≫ (pull g).map ξ ≫ eP.hom))
    (curry_diagonalAction D' K' _) h

end AlgebraicGeometry.Scheme.Hom.DiagonalOpen

end
