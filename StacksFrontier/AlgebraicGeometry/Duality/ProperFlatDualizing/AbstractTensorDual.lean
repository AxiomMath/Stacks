module

public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# `R(E ⊗ a(𝟙)) ≅ R(E^∨)^∨`, abstractly

Let `L : D ⥤ C` be left adjoint to `R : C ⥤ D` between monoidal categories, `D` braided. Let
`QC`, `QD` be full subcategories with `R(QC) ⊆ QD`, and let `a` be a right adjoint of the
restriction `R : QC ⥤ QD`. Write `ω = a(𝟙)`. For an object `E` of `C` with a right dual `E^∨`
such that the projection formula `R(E^∨) ⊗ M ≅ R(E^∨ ⊗ L M)` holds naturally in `M ∈ QD`, and such
that `R(E^∨)` has a right dual `R(E^∨)^∨`, the chain of bijections

  `Hom(M, R(E ⊗ ω)) = Hom(LM, E ⊗ ω) = Hom(E^∨ ⊗ LM, ω) = Hom(R(E^∨ ⊗ LM), 𝟙)`
  `               = Hom(R(E^∨) ⊗ M, 𝟙) = Hom(M ⊗ R(E^∨), 𝟙) = Hom(M, R(E^∨)^∨)`

is natural in `M ∈ QD`, so `R(E ⊗ ω) ≅ R(E^∨)^∨` when both lie in `QD`. This is the abstract form
of the first display of the proof of [Stacks, Tag 0E4L], with `L = Lf^*`, `R = Rf_*` and `a` the
right adjoint of [Stacks, Tag 0A9E].

## Main results

* `CategoryTheory.MonoidalCategory.isoOfHomEquiv` — Yoneda in a full subcategory.
* `CategoryTheory.MonoidalCategory.RelativeDuality.homEquiv` — the chain of bijections.
* `CategoryTheory.MonoidalCategory.RelativeDuality.homEquiv_naturality` — its naturality.
* `CategoryTheory.MonoidalCategory.RelativeDuality.tensorDualIso` — the isomorphism.
-/

@[expose] public noncomputable section

namespace CategoryTheory.MonoidalCategory

universe v₁ v₂ u₁ u₂ v w

/-- **Yoneda in a full subcategory.** Two objects `A`, `B` with property `P` are isomorphic as
soon as the functors `Hom(-, A)` and `Hom(-, B)` on the objects with property `P` are naturally
isomorphic. -/
def isoOfHomEquiv {C : Type w} [Category.{v} C] (P : ObjectProperty C) {A B : C} (hA : P A)
    (hB : P B) (e : ∀ M : C, P M → ((M ⟶ A) ≃ (M ⟶ B)))
    (he : ∀ (M M' : C) (hM : P M) (hM' : P M') (g : M' ⟶ M) (x : M ⟶ A),
      e M' hM' (g ≫ x) = g ≫ e M hM x) : A ≅ B where
  hom := e A hA (𝟙 A)
  inv := (e B hB).symm (𝟙 B)
  hom_inv_id := by
    apply (e A hA).injective
    rw [he B A hB hA, Equiv.apply_symm_apply, Category.comp_id]
  inv_hom_id := by
    have h := he A B hA hB ((e B hB).symm (𝟙 B)) (𝟙 A)
    rw [Category.comp_id, Equiv.apply_symm_apply] at h
    exact h.symm

/-- The forward morphism of `isoOfHomEquiv P hA hB e he` is the image `e A hA (𝟙 A)` of the
identity of `A`. -/
theorem isoOfHomEquiv_hom {C : Type w} [Category.{v} C] (P : ObjectProperty C) {A B : C}
    (hA : P A) (hB : P B) (e : ∀ M : C, P M → ((M ⟶ A) ≃ (M ⟶ B)))
    (he : ∀ (M M' : C) (hM : P M) (hM' : P M') (g : M' ⟶ M) (x : M ⟶ A),
      e M' hM' (g ≫ x) = g ≫ e M hM x) :
    (isoOfHomEquiv P hA hB e he).hom = e A hA (𝟙 A) := rfl

namespace RelativeDuality

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D] [MonoidalCategory C]
  [MonoidalCategory D] [BraidedCategory D]
  {L : D ⥤ C} {R : C ⥤ D} (adj : L ⊣ R)
  {QC : ObjectProperty C} {QD : ObjectProperty D}
  (hR : ∀ K : QC.FullSubcategory, QD (R.obj K.obj))
  {a : QD.FullSubcategory ⥤ QC.FullSubcategory}
  (adjA : QD.lift (QC.ι ⋙ R) hR ⊣ a)
  (O : QD.FullSubcategory) (eO : O.obj ≅ 𝟙_ D)
  (E Ed : C) [ExactPairing E Ed] (Pd : D) [ExactPairing (R.obj Ed) Pd]
  (hK : ∀ M : D, QD M → QC (Ed ⊗ L.obj M))
  (π : ∀ (M : D) (_ : QD M), R.obj Ed ⊗ M ≅ R.obj (Ed ⊗ L.obj M))
  (hπ : ∀ (M M' : D) (hM : QD M) (hM' : QD M') (g : M' ⟶ M),
    R.obj Ed ◁ g ≫ (π M hM).hom = (π M' hM').hom ≫ R.map (Ed ◁ L.map g))

/-- **The chain of bijections** `Hom(M, R(E ⊗ ω)) ≃ Hom(M, R(E^∨)^∨)`, for `M ∈ QD`. -/
def homEquiv (M : D) (hM : QD M) :
    (M ⟶ R.obj (E ⊗ (a.obj O).obj)) ≃ (M ⟶ Pd) :=
  (adj.homEquiv M _).symm.trans <|
  (tensorLeftHomEquiv (L.obj M) E Ed (a.obj O).obj).symm.trans <|
  (QC.fullyFaithfulι.homEquiv (X := ⟨Ed ⊗ L.obj M, hK M hM⟩) (Y := a.obj O)).symm.trans <|
  ((adjA.homEquiv ⟨Ed ⊗ L.obj M, hK M hM⟩ O).symm.trans QD.fullyFaithfulι.homEquiv).trans <|
  (Iso.homCongr (π M hM).symm eO).trans <|
  (Iso.homCongr (β_ (R.obj Ed) M) (Iso.refl _)).trans <|
  (tensorRightHomEquiv M (R.obj Ed) Pd (𝟙_ D)).trans <|
  Iso.homCongr (Iso.refl _) (λ_ Pd)

include hπ in
/-- The bijection `homEquiv` is natural in `M ∈ QD`: for `g : M' ⟶ M` and `x : M ⟶ R(E ⊗ ω)`, it
sends `g ≫ x` to `g` composed with the image of `x`. -/
theorem homEquiv_naturality (M M' : D) (hM : QD M) (hM' : QD M') (g : M' ⟶ M)
    (x : M ⟶ R.obj (E ⊗ (a.obj O).obj)) :
    homEquiv adj hR adjA O eO E Ed Pd hK π M' hM' (g ≫ x) =
      g ≫ homEquiv adj hR adjA O eO E Ed Pd hK π M hM x := by
  have h₁ : (adjA.homEquiv ⟨Ed ⊗ L.obj M', hK M' hM'⟩ O).symm
      (QC.fullyFaithfulι.homEquiv.symm (Ed ◁ L.map g ≫ (tensorLeftHomEquiv (L.obj M) E Ed
        (a.obj O).obj).symm ((adj.homEquiv M _).symm x))) =
      (QD.lift (QC.ι ⋙ R) hR).map (ObjectProperty.homMk (Ed ◁ L.map g)) ≫
        (adjA.homEquiv ⟨Ed ⊗ L.obj M, hK M hM⟩ O).symm (QC.fullyFaithfulι.homEquiv.symm
          ((tensorLeftHomEquiv (L.obj M) E Ed (a.obj O).obj).symm
            ((adj.homEquiv M _).symm x))) := by
    rw [← Adjunction.homEquiv_naturality_left_symm]
    rfl
  simp only [homEquiv, Equiv.trans_apply, Adjunction.homEquiv_naturality_left_symm,
    tensorLeftHomEquiv_symm_naturality, Functor.FullyFaithful.homEquiv_symm_apply,
    Functor.FullyFaithful.homEquiv_apply, Iso.homCongr_apply, Iso.symm_inv, Iso.refl_inv,
    Iso.refl_hom, Category.id_comp, Category.comp_id]
  rw [h₁]
  simp only [ObjectProperty.ι_map, ObjectProperty.FullSubcategory.comp_hom, Functor.map_comp,
    ObjectProperty.lift_map, Functor.comp_map, ObjectProperty.homMk_hom, Category.assoc]
  rw [← reassoc_of% (hπ M M' hM hM' g)]
  have h₂ : ∀ t : M ⊗ R.obj Ed ⟶ 𝟙_ D, (tensorRightHomEquiv M' (R.obj Ed) Pd (𝟙_ D))
      (g ▷ R.obj Ed ≫ t) = g ≫ (tensorRightHomEquiv M (R.obj Ed) Pd (𝟙_ D)) t := by
    intro t
    apply (tensorRightHomEquiv M' (R.obj Ed) Pd (𝟙_ D)).symm.injective
    rw [Equiv.symm_apply_apply, tensorRightHomEquiv_symm_naturality, Equiv.symm_apply_apply]
  have h₃ : (β_ (R.obj Ed) M').inv ≫ R.obj Ed ◁ g = g ▷ R.obj Ed ≫ (β_ (R.obj Ed) M).inv :=
    (BraidedCategory.braiding_inv_naturality_left g (R.obj Ed)).symm
  rw [reassoc_of% h₃, h₂, Category.assoc]

/-- **`R(E ⊗ ω) ≅ R(E^∨)^∨`**, when both lie in `QD`. -/
def tensorDualIso (hA : QD (R.obj (E ⊗ (a.obj O).obj))) (hB : QD Pd) :
    R.obj (E ⊗ (a.obj O).obj) ≅ Pd :=
  isoOfHomEquiv QD hA hB (homEquiv adj hR adjA O eO E Ed Pd hK π)
    (homEquiv_naturality adj hR adjA O eO E Ed Pd hK π hπ)

/-- **`R(E ⊗ ω) ≅ R(E^∨)^∨`**, with the projection formula read through arbitrary bifunctors
`TC`, `TD` equal to the tensor products. -/
def tensorDualIsoOfEq {TC : C ⥤ C ⥤ C} (hTC : curriedTensor C = TC) {TD : D ⥤ D ⥤ D}
    (hTD : curriedTensor D = TD)
    (hK' : ∀ M : D, QD M → QC ((TC.obj Ed).obj (L.obj M)))
    (π' : ∀ (M : D) (_ : QD M), (TD.obj (R.obj Ed)).obj M ≅ R.obj ((TC.obj Ed).obj (L.obj M)))
    (hπ' : ∀ (M M' : D) (hM : QD M) (hM' : QD M') (g : M' ⟶ M),
      (TD.obj (R.obj Ed)).map g ≫ (π' M hM).hom =
        (π' M' hM').hom ≫ R.map ((TC.obj Ed).map (L.map g)))
    (hA : QD (R.obj (E ⊗ (a.obj O).obj))) (hB : QD Pd) :
    R.obj (E ⊗ (a.obj O).obj) ≅ Pd := by
  subst hTC hTD
  exact tensorDualIso adj hR adjA O eO E Ed Pd hK' π' hπ' hA hB

end RelativeDuality

end CategoryTheory.MonoidalCategory

end
