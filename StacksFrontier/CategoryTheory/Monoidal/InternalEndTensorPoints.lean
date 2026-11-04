module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BrauerGroupScheme.TensorPowerPullback
public import StacksFrontier.CategoryTheory.Monoidal.InternalEndPoints

/-!
# The points of an internal endomorphism monoid and the external tensor product

Let `C` be a symmetric monoidal closed category. The internal hom `X ⟶[C] X` of an object is a
monoid object `CategoryTheory.MonoidalClosed.internalEnd X`, its points `𝟙_ C ⟶ X ⟶[C] X` are the
endomorphisms of `X` (`CategoryTheory.MonoidalClosed.curry'`), and a morphism of internal
endomorphism monoids therefore induces a map on endomorphisms,
`CategoryTheory.MonoidalClosed.pointMap`. This file computes that map on the external tensor
product.

The computation rests on one identity, `curry'_tensorHom_comp_tensorInternalEnd`: the comparison
`End X ⊗ End Y ⟶ End (X ⊗ Y)` of `CategoryTheory.MonoidalClosed.tensorInternalEnd` carries the
tensor product of the point of `f : X ⟶ X` and the point of `g : Y ⟶ Y` to the point of `f ⊗ₘ g`.
It is the statement that the comparison really is the external tensor product of endomorphisms,
read on sections, and the proof is one application of
`CategoryTheory.MonoidalClosed.uncurry_injective` followed by the coherence identity
`CategoryTheory.MonoidalCategory.tensor_right_unitality`, exactly as in the unit law of
`CategoryTheory.MonoidalClosed.isMonHom_tensorInternalEnd`. Its consequence is that a morphism of
internal endomorphism monoids conjugated through the comparison acts on a tensor product of
endomorphisms factorwise.

For sheaves of `𝒪_S`-modules on a scheme this is the computation the proof of [Stacks, Tag 0A2L]
needs. There the identification `𝓗om(E,E)^{⊗ (n+1)} ≅ 𝓗om(E^{⊗ (n+1)}, E^{⊗ (n+1)})` of
`Stacks.EtaleCohomology.BrauerScheme.natTensorPowEndAlgebraIso` turns the `(n+1)`-fold tensor
power of an automorphism `Ψ` of `𝓗om(E,E)` into an automorphism of
`𝓗om(E^{⊗ (n+1)}, E^{⊗ (n+1)})`, and the content of `pointMap_natTensorPowEndConj` is that this
automorphism acts on a tensor product of `n+1` endomorphisms of `E` factor by factor, each factor
by the action of `Ψ`. Applied to the comparison automorphism of two trivialisations of an Azumaya
algebra, this is what reduces the invariance of the Saltman projector to the one-factor
computation.

## Main definitions

* `Stacks.EtaleCohomology.BrauerScheme.natTensorPowFam`: the tensor product of a family of
  endomorphisms of a sheaf of modules, as an endomorphism of its tensor power.
* `Stacks.EtaleCohomology.BrauerScheme.natTensorPowEndConj`: the `(n+1)`-fold tensor power of an
  automorphism of `𝓗om(E,E)`, read on `𝓗om(E^{⊗ (n+1)}, E^{⊗ (n+1)})`.

## Main results

* `CategoryTheory.MonoidalClosed.curry'_tensorHom_comp_tensorInternalEnd` and
  `CategoryTheory.MonoidalClosed.curry'_tensorHom`: **the comparison
  `End X ⊗ End Y ⟶ End (X ⊗ Y)` carries the tensor product of the points of `f` and `g` to the
  point of `f ⊗ₘ g`.**
* `CategoryTheory.MonoidalClosed.pointMap_internalEndCongr_conj`: conjugating a morphism of
  internal endomorphism monoids by the isomorphism induced by an isomorphism of objects conjugates
  the induced map on endomorphisms.
* `CategoryTheory.MonoidalClosed.pointMap_tensorInternalEndIso_conj` and its sheaf-of-modules
  spelling `Stacks.EtaleCohomology.BrauerScheme.pointMap_endAlgebraTensorIso_conj`: **a tensor
  product of morphisms of internal endomorphism monoids, conjugated through the comparison, acts
  on a tensor product of endomorphisms factorwise.**
* **`Stacks.EtaleCohomology.BrauerScheme.pointMap_natTensorPowEndConj`: the `(n+1)`-fold tensor
  power of an automorphism of `𝓗om(E,E)` acts on endomorphisms of `E^{⊗ (n+1)}` factorwise.**

## Implementation notes

`Stacks.TensorPowers.natTensorPow E (m + 1)` is `natTensorPow E m ⊗ E` only *definitionally*, so
no `simp` or `rw` lemma keyed on a tensor product fires in a goal carrying the power's spelling,
and no `simp` lemma can be rewritten *underneath* an isomorphism whose stored middle object is
written in the one spelling while its two factors are written in the other — the rewritten proof
would not typecheck. Every step of `pointMap_natTensorPowEndConj` that needs either shape is
therefore stated separately, with the objects as variables (`conj_leftUnitorTrans_hom` and
`conj_tensorIsoTrans_hom` for the two shapes of the conjugating isomorphism), and transported to
the goal by `exact` or `refine`, which check definitional equality at full transparency. This is
the discipline recorded in the implementation notes of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.BrauerGroupScheme.TensorPowerFreeMatrix`.

## References

* [Stacks Project, Tag 0A2L](https://stacks.math.columbia.edu/tag/0A2L)
-/

@[expose] public section

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v u

noncomputable section

namespace CategoryTheory.MonoidalClosed

section Conjugation

variable {M : Type*} [Category M] [MonoidalCategory M]

/-- **The conjugate of a tensor product of isomorphisms by `λ_ A ≪≫ c`**, with the first factor
the identity of the unit: it is the conjugate of the second factor by `c`. This is the degree-one
case of `Stacks.EtaleCohomology.BrauerScheme.pointMap_natTensorPowEndConj`, stated with the
objects as variables so that the naturality of the left unitor applies to it. -/
lemma conj_leftUnitorTrans_hom {A B : M} (c : A ≅ B) (e : A ≅ A) :
    ((λ_ A ≪≫ c).symm ≪≫ tensorIso (Iso.refl (𝟙_ M)) e ≪≫ (λ_ A ≪≫ c)).hom
      = c.inv ≫ e.hom ≫ c.hom := by
  simp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, tensorIso_hom, Iso.refl_hom,
    Category.assoc]
  rw [id_tensorHom, leftUnitor_naturality_assoc, Iso.inv_hom_id_assoc]

/-- **The conjugate of a tensor product of isomorphisms by `(P ⊗ᵢ 𝟙) ≪≫ T`**: it is the tensor
product of the conjugate of the first factor by `P` with the second factor, conjugated by `T`.
This is the induction step of
`Stacks.EtaleCohomology.BrauerScheme.pointMap_natTensorPowEndConj`, stated with the objects as
variables so that the interchange law applies to it. -/
lemma conj_tensorIsoTrans_hom {A B D Z : M} (P : A ≅ B) (T : B ⊗ D ≅ Z) (e : A ≅ A) (d : D ≅ D) :
    ((tensorIso P (Iso.refl D) ≪≫ T).symm ≪≫ tensorIso e d ≪≫
          (tensorIso P (Iso.refl D) ≪≫ T)).hom
      = T.inv ≫ ((P.symm ≪≫ e ≪≫ P).hom ⊗ₘ d.hom) ≫ T.hom := by
  simp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, tensorIso_hom, tensorIso_inv,
    Iso.refl_hom, Iso.refl_inv, Category.assoc, tensorHom_comp_tensorHom_assoc,
    Category.id_comp, Category.comp_id]

end Conjugation

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]

/-- The inverse of the isomorphism of internal endomorphism monoids induced by an isomorphism of
objects is the isomorphism induced by the inverse. -/
lemma internalEndCongr_inv {X Y : C} (e : X ≅ Y) :
    (internalEndCongr e).inv = (internalEndCongr e.symm).hom :=
  rfl

/-- **Conjugating a morphism of internal endomorphism monoids by the isomorphism induced by an
isomorphism `e : X ≅ Y` of objects conjugates the induced map on endomorphisms by `e`.** -/
theorem pointMap_internalEndCongr_conj {X Y : C} (e : X ≅ Y)
    (Θ : internalEnd X ⟶ internalEnd X) (h : Y ⟶ Y) :
    pointMap ((internalEndCongr e).inv ≫ Θ ≫ (internalEndCongr e).hom) h
      = e.inv ≫ pointMap Θ (e.hom ≫ h ≫ e.inv) ≫ e.hom := by
  rw [pointMap_trans, pointMap_trans, internalEndCongr_inv, pointMap_internalEndCongr,
    pointMap_internalEndCongr]
  rfl

section Symmetric

variable [SymmetricCategory C]

/-- **The external tensor product of endomorphisms, read on points**: the comparison
`End X ⊗ End Y ⟶ End (X ⊗ Y)` carries the tensor product of the point of `f` and the point of `g`
to the point of `f ⊗ₘ g`. -/
theorem curry'_tensorHom_comp_tensorInternalEnd {X Y : C} (f : X ⟶ X) (g : Y ⟶ Y) :
    (curry' f ⊗ₘ curry' g) ≫ tensorInternalEnd X Y = (λ_ (𝟙_ C)).hom ≫ curry' (f ⊗ₘ g) := by
  apply uncurry_injective
  rw [uncurry_natural_left, uncurry_natural_left, uncurry_tensorInternalEnd,
    tensorμ_natural_right_assoc, tensorHom_comp_tensorHom, whiskerLeft_curry'_ihom_ev_app,
    whiskerLeft_curry'_ihom_ev_app, ← tensorHom_comp_tensorHom, curry',
    uncurry_curry, tensor_right_unitality X Y]
  simp

/-- **The point of a tensor product of endomorphisms**, in the form in which the comparison
`End X ⊗ End Y ⟶ End (X ⊗ Y)` can be cancelled against its inverse. -/
theorem curry'_tensorHom {X Y : C} (f : X ⟶ X) (g : Y ⟶ Y) :
    curry' (f ⊗ₘ g) = (λ_ (𝟙_ C)).inv ≫ (curry' f ⊗ₘ curry' g) ≫ tensorInternalEnd X Y := by
  rw [curry'_tensorHom_comp_tensorInternalEnd, Iso.inv_hom_id_assoc]

/-- **A tensor product of morphisms of internal endomorphism monoids, conjugated through the
comparison `End X ⊗ End Y ≅ End (X ⊗ Y)`, acts on a tensor product of endomorphisms
factorwise.** -/
theorem pointMap_tensorInternalEndIso_conj {X Y X' Y' : C}
    [IsIso (tensorInternalEnd X Y)] [IsIso (tensorInternalEnd X' Y')]
    (θ₁ : internalEnd X ⟶ internalEnd X') (θ₂ : internalEnd Y ⟶ internalEnd Y')
    (f : X ⟶ X) (g : Y ⟶ Y) :
    pointMap ((tensorInternalEndIso X Y).inv ≫ (θ₁ ⊗ₘ θ₂) ≫ (tensorInternalEndIso X' Y').hom)
        (f ⊗ₘ g)
      = pointMap θ₁ f ⊗ₘ pointMap θ₂ g := by
  have hT : tensorInternalEnd X Y ≫ (tensorInternalEndIso X Y).inv.hom = 𝟙 _ :=
    congrArg Mon.Hom.hom (tensorInternalEndIso X Y).hom_inv_id
  have hθ : (θ₁ ⊗ₘ θ₂).hom = θ₁.hom ⊗ₘ θ₂.hom := rfl
  have hT' : (tensorInternalEndIso X' Y').hom.hom = tensorInternalEnd X' Y' := rfl
  apply curry'_injective
  rw [curry'_pointMap, curry'_tensorHom f g,
    curry'_tensorHom (pointMap θ₁ f) (pointMap θ₂ g), curry'_pointMap, curry'_pointMap]
  simp only [Mon.comp_hom', Category.assoc]
  rw [reassoc_of% hT, hθ, hT', tensorHom_comp_tensorHom_assoc]

end Symmetric

end CategoryTheory.MonoidalClosed

namespace Stacks.EtaleCohomology.BrauerScheme

open AlgebraicGeometry TopologicalSpace
open Stacks.SheafOfModules

variable {S : Scheme.{u}}

/-- **A tensor product of morphisms of endomorphism algebra sheaves, conjugated through the
comparison `𝓗om(E,E) ⊗ 𝓗om(F,F) ≅ 𝓗om(E ⊗ F, E ⊗ F)`, acts on a tensor product of endomorphisms
factorwise.** This is `CategoryTheory.MonoidalClosed.pointMap_tensorInternalEndIso_conj` with the
invertibility of the comparison supplied by the finite local freeness of the four sheaves of
modules. -/
theorem pointMap_endAlgebraTensorIso_conj {E F E' F' : ModuleSheaf S}
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree (C := Opens S)
      (J := Opens.grothendieckTopology S) E)
    (hF : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree (C := Opens S)
      (J := Opens.grothendieckTopology S) F)
    (hE' : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree (C := Opens S)
      (J := Opens.grothendieckTopology S) E')
    (hF' : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree (C := Opens S)
      (J := Opens.grothendieckTopology S) F')
    (θ₁ : endAlgebra E ⟶ endAlgebra E') (θ₂ : endAlgebra F ⟶ endAlgebra F')
    (f : E ⟶ E) (g : F ⟶ F) :
    MonoidalClosed.pointMap
        ((endAlgebraTensorIso hE hF).inv ≫ (θ₁ ⊗ₘ θ₂) ≫ (endAlgebraTensorIso hE' hF').hom)
        (f ⊗ₘ g)
      = MonoidalClosed.pointMap θ₁ f ⊗ₘ MonoidalClosed.pointMap θ₂ g :=
  let := isIso_tensorInternalEnd_of_isFiniteLocallyFree hE hF
  let := isIso_tensorInternalEnd_of_isFiniteLocallyFree hE' hF'
  MonoidalClosed.pointMap_tensorInternalEndIso_conj θ₁ θ₂ f g

/-- The tensor product of a **family** of endomorphisms of a sheaf of `𝒪_S`-modules `E`, as an
endomorphism of the `m`-fold tensor power of `E`. `Stacks.TensorPowers.natTensorPow` adds its
factors on the right, so the recursion puts `f (Fin.last m)` on the right. -/
def natTensorPowFam {E : ModuleSheaf S} :
    ∀ (m : ℕ), (Fin m → (E ⟶ E)) →
      (Stacks.TensorPowers.natTensorPow E m ⟶ Stacks.TensorPowers.natTensorPow E m)
  | 0, _ => 𝟙 _
  | m + 1, f => natTensorPowFam m (Fin.init f) ⊗ₘ f (Fin.last m)

/-- The empty tensor product of endomorphisms is the identity of the unit. -/
@[simp]
lemma natTensorPowFam_zero {E : ModuleSheaf S} (f : Fin 0 → (E ⟶ E)) :
    natTensorPowFam 0 f = 𝟙 (Stacks.TensorPowers.natTensorPow E 0) :=
  rfl

/-- One more factor, added on the right. -/
@[simp]
lemma natTensorPowFam_succ {E : ModuleSheaf S} {m : ℕ} (f : Fin (m + 1) → (E ⟶ E)) :
    natTensorPowFam (m + 1) f = natTensorPowFam m (Fin.init f) ⊗ₘ f (Fin.last m) :=
  rfl

/-- **The conjugate of the `(n+1)`-fold tensor power of an automorphism of the endomorphism
algebra of `E`, read on the endomorphism algebra of the `(n+1)`-fold tensor power of `E`**,
through the identification `natTensorPowEndAlgebraIso`. -/
def natTensorPowEndConj {E : ModuleSheaf S}
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree (C := Opens S)
      (J := Opens.grothendieckTopology S) E)
    (Ψ : endAlgebra E ≅ endAlgebra E) (n : ℕ) :
    endAlgebra (Stacks.TensorPowers.natTensorPow E (n + 1)) ≅
      endAlgebra (Stacks.TensorPowers.natTensorPow E (n + 1)) :=
  (natTensorPowEndAlgebraIso hE n).symm ≪≫ natTensorPowCongr Ψ (n + 1) ≪≫
    natTensorPowEndAlgebraIso hE n

/-- **THE MAIN RESULT: the `(n+1)`-fold tensor power of an automorphism of `𝓗om(E,E)` acts on
endomorphisms of `E^{⊗ (n+1)}` factorwise.** The induction step is
`pointMap_endAlgebraTensorIso_conj`, the degree-one case the naturality of the left unitor. -/
theorem pointMap_natTensorPowEndConj {E : ModuleSheaf S}
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree (C := Opens S)
      (J := Opens.grothendieckTopology S) E)
    (Ψ : endAlgebra E ≅ endAlgebra E) :
    ∀ (n : ℕ) (f : Fin (n + 1) → (E ⟶ E)),
      MonoidalClosed.pointMap (natTensorPowEndConj hE Ψ n).hom (natTensorPowFam (n + 1) f)
        = natTensorPowFam (n + 1) (fun j => MonoidalClosed.pointMap Ψ.hom (f j))
  | 0, f => by
    have hconj : (natTensorPowEndConj hE Ψ 0).hom =
        (MonoidalClosed.internalEndCongr (λ_ E).symm).inv ≫ Ψ.hom ≫
          (MonoidalClosed.internalEndCongr (λ_ E).symm).hom :=
      MonoidalClosed.conj_leftUnitorTrans_hom (MonoidalClosed.internalEndCongr (λ_ E).symm) Ψ
    have h3 := MonoidalClosed.pointMap_internalEndCongr_conj (λ_ E).symm Ψ.hom
      (𝟙 (𝟙_ (ModuleSheaf S)) ⊗ₘ f (Fin.last 0))
    have key : MonoidalClosed.pointMap (natTensorPowEndConj hE Ψ 0).hom
          (𝟙 (𝟙_ (ModuleSheaf S)) ⊗ₘ f (Fin.last 0))
        = 𝟙 (𝟙_ (ModuleSheaf S)) ⊗ₘ MonoidalClosed.pointMap Ψ.hom (f (Fin.last 0)) := by
      rw [hconj]
      refine h3.trans ?_
      simp
    exact key
  | n + 1, f => by
    have hconj : (natTensorPowEndConj hE Ψ (n + 1)).hom =
        (endAlgebraTensorIso (isFiniteLocallyFree_natTensorPow hE n) hE).inv ≫
          ((natTensorPowEndConj hE Ψ n).hom ⊗ₘ Ψ.hom) ≫
          (endAlgebraTensorIso (isFiniteLocallyFree_natTensorPow hE n) hE).hom :=
      MonoidalClosed.conj_tensorIsoTrans_hom (natTensorPowEndAlgebraIso hE n)
        (endAlgebraTensorIso (isFiniteLocallyFree_natTensorPow hE n) hE)
        (natTensorPowCongr Ψ (n + 1)) Ψ
    have h2 := pointMap_endAlgebraTensorIso_conj (isFiniteLocallyFree_natTensorPow hE n) hE
      (isFiniteLocallyFree_natTensorPow hE n) hE (natTensorPowEndConj hE Ψ n).hom Ψ.hom
      (natTensorPowFam (n + 1) (Fin.init f)) (f (Fin.last (n + 1)))
    rw [hconj]
    refine h2.trans ?_
    rw [pointMap_natTensorPowEndConj hE Ψ n (Fin.init f)]
    rfl

end Stacks.EtaleCohomology.BrauerScheme

end

end
