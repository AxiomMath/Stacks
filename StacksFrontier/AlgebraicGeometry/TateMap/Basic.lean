module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.RingHomProperty
public import StacksFrontier.RingTheory.TateMap.ChartBaseChange

/-!
# The category of Stacks, Section 0FKB

The objects are the locally quasi-finite syntomic morphisms `Y ⟶ X`, and a morphism
`b/a : Y'/X' → Y/X` is a commutative square identifying `Y'` with an open subscheme of
`X' ×_X Y`. Restriction to opens and base change are the two special cases.

## Main definitions

* `AlgebraicGeometry.TateMap.IsQuasiFiniteSyntomic`: the objects.
* `AlgebraicGeometry.TateMap.OpenBaseChangeSquare f f'`: the morphisms from `f'` to `f`.
* `AlgebraicGeometry.TateMap.OpenBaseChangeSquare.ofIsPullback`: a cartesian square.
* `AlgebraicGeometry.TateMap.OpenBaseChangeSquare.ofOpens`: restriction to opens.
* `AlgebraicGeometry.TateMap.OpenBaseChangeSquare.ofSpec`: the spectrum of a chart base change.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.TateMap

/-- A morphism of schemes is locally quasi-finite syntomic when it is locally quasi-finite and
syntomic. These are the objects `Y/X` of the category of Section 0FKB. -/
abbrev IsQuasiFiniteSyntomic {X Y : Scheme.{u}} (f : Y ⟶ X) : Prop :=
  LocallyQuasiFinite f ∧ Syntomic f

/-- The spectrum of a quasi-finite syntomic algebra is an object of the category of
Section 0FKB. -/
theorem isQuasiFiniteSyntomic_specMap (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.QuasiFinite A B] [Algebra.Syntomic A B] :
    IsQuasiFiniteSyntomic (Spec.map (CommRingCat.ofHom (algebraMap A B))) := by
  refine ⟨?_, ?_⟩
  · rw [HasRingHomProperty.Spec_iff (P := @LocallyQuasiFinite)]
    exact RingHom.quasiFinite_algebraMap.mpr inferInstance
  · rw [HasRingHomProperty.Spec_iff (P := @Syntomic)]
    show RingHom.Syntomic (algebraMap A B)
    have h : (algebraMap A B).toAlgebra = ‹Algebra A B› := Algebra.algebra_ext _ _ fun _ ↦ rfl
    rw [RingHom.syntomic_iff, h]
    infer_instance

/-- A morphism `b/a : Y'/X' → Y/X` of the category of Section 0FKB: a commutative square whose
induced morphism `Y' ⟶ X' ×_X Y` is an open immersion. -/
structure OpenBaseChangeSquare {X Y X' Y' : Scheme.{u}} (f : Y ⟶ X) (f' : Y' ⟶ X') where
  /-- The morphism of bases. -/
  base : X' ⟶ X
  /-- The morphism of sources. -/
  cover : Y' ⟶ Y
  /-- The square commutes. -/
  w : cover ≫ f = f' ≫ base
  /-- `Y'` is an open subscheme of `X' ×_X Y`. -/
  isOpenImmersion : IsOpenImmersion (pullback.lift f' cover w.symm)

namespace OpenBaseChangeSquare

/-- A cartesian square is a morphism of the category of Section 0FKB. -/
def ofIsPullback {X Y X' Y' : Scheme.{u}} (f : Y ⟶ X) (f' : Y' ⟶ X') (g : X' ⟶ X)
    (g' : Y' ⟶ Y) (h : IsPullback g' f' f g) : OpenBaseChangeSquare f f' where
  base := g
  cover := g'
  w := h.w
  isOpenImmersion := by
    have he : pullback.lift f' g' h.w.symm = h.flip.isoPullback.hom := by
      apply pullback.hom_ext
      · rw [pullback.lift_fst, IsPullback.isoPullback_hom_fst]
      · rw [pullback.lift_snd, IsPullback.isoPullback_hom_snd]
    rw [he]
    infer_instance

/-- Restriction to opens: for opens `U ⊆ X` and `V ⊆ f⁻¹(U)` the square of the inclusions is
a morphism of the category of Section 0FKB. -/
def ofOpens {X Y : Scheme.{u}} (f : Y ⟶ X) (U : X.Opens) (V : Y.Opens) (hVU : V ≤ f ⁻¹ᵁ U) :
    OpenBaseChangeSquare f (f.resLE U V hVU) where
  base := U.ι
  cover := V.ι
  w := by simp
  isOpenImmersion := by
    have : IsOpenImmersion (pullback.lift (f.resLE U V hVU) V.ι (by simp) ≫
        pullback.snd U.ι f) := by
      rw [pullback.lift_snd]
      infer_instance
    exact IsOpenImmersion.of_comp _ (pullback.snd U.ι f)

/-- The spectrum of a chart base change `A → B` to `A' → B'` is a morphism of the category of
Section 0FKB from `Spec B' → Spec A'` to `Spec B → Spec A`. -/
def ofSpec {A B A' B' : Type u} [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
    [Algebra A B] [Algebra A A'] [Algebra A' B'] [Algebra B B']
    (D : Stacks.TateMap.ChartBaseChange A B A' B') :
    OpenBaseChangeSquare (Spec.map (CommRingCat.ofHom (algebraMap A B)))
      (Spec.map (CommRingCat.ofHom (algebraMap A' B'))) where
  base := Spec.map (CommRingCat.ofHom (algebraMap A A'))
  cover := Spec.map (CommRingCat.ofHom (algebraMap B B'))
  w := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext a
    exact D.algebraMap_comm a
  isOpenImmersion := by
    let := D.algebra
    have := D.isLocalization
    have he : pullback.lift (Spec.map (CommRingCat.ofHom (algebraMap A' B')))
        (Spec.map (CommRingCat.ofHom (algebraMap B B')))
        (by
          rw [← Spec.map_comp, ← Spec.map_comp]
          congr 1
          ext a
          exact (D.algebraMap_comm a).symm) =
        Spec.map (CommRingCat.ofHom (algebraMap (A' ⊗[A] B) B')) ≫
          (pullbackSpecIso A A' B).inv := by
      apply pullback.hom_ext
      · rw [pullback.lift_fst, Category.assoc, pullbackSpecIso_inv_fst', ← Spec.map_comp]
        congr 1
        ext y
        exact (D.base_left y).symm
      · rw [pullback.lift_snd, Category.assoc, pullbackSpecIso_inv_snd, ← Spec.map_comp]
        congr 1
        ext x
        exact (D.base_right x).symm
    rw [he]
    let e : Localization.Away D.elt ≃ₐ[A' ⊗[A] B] B' :=
      IsLocalization.algEquiv (Submonoid.powers D.elt) _ _
    have he' : Spec.map (CommRingCat.ofHom (algebraMap (A' ⊗[A] B) B')) =
        Spec.map (CommRingCat.ofHom e.toRingEquiv.toRingHom) ≫
          Spec.map (CommRingCat.ofHom (algebraMap (A' ⊗[A] B) (Localization.Away D.elt))) := by
      rw [← Spec.map_comp]
      congr 1
      exact CommRingCat.hom_ext (RingHom.ext fun z ↦ (e.commutes z).symm)
    rw [he']
    have : IsIso (Spec.map (CommRingCat.ofHom e.toRingEquiv.toRingHom)) := by
      have : IsIso (CommRingCat.ofHom e.toRingEquiv.toRingHom) :=
        (RingEquiv.toCommRingCatIso e.toRingEquiv).isIso_hom
      infer_instance
    infer_instance

/-- An affine chart `(U, V)` of `f` exhibits `Spec Γ(Y, V) → Spec Γ(X, U)` as an object of the
category of Section 0FKB mapping to `f`, by the canonical open immersions. -/
def ofAffineChart {X Y : Scheme.{u}} (f : Y ⟶ X) (U : X.affineOpens) (V : Y.affineOpens)
    (hVU : V.1 ≤ f ⁻¹ᵁ U.1) : OpenBaseChangeSquare f (Spec.map (f.appLE U.1 V.1 hVU)) where
  base := U.2.fromSpec
  cover := V.2.fromSpec
  w := (IsAffineOpen.SpecMap_appLE_fromSpec f U.2 V.2 hVU).symm
  isOpenImmersion := by
    have := U.2.isOpenImmersion_fromSpec
    have := V.2.isOpenImmersion_fromSpec
    have : IsOpenImmersion (pullback.lift (Spec.map (f.appLE U.1 V.1 hVU)) V.2.fromSpec
        (IsAffineOpen.SpecMap_appLE_fromSpec f U.2 V.2 hVU) ≫ pullback.snd U.2.fromSpec f) := by
      rw [pullback.lift_snd]
      infer_instance
    exact IsOpenImmersion.of_comp _ (pullback.snd U.2.fromSpec f)

end OpenBaseChangeSquare

/-- The restriction of an affine chart `(U, V)` of `f` to opens `U₀ = D(a) ⊆ U` and
`V₀ = D(b) ⊆ V` with `V₀ ⊆ f⁻¹(U₀)` is a chart base change, for the algebra structures given by
`f.appLE` on the two charts and by restriction of sections from `U` to `U₀` and from `V` to
`V₀`. The opens are taken with their presentations as principal opens, so that the same open
can be presented in several charts. -/
def chartBaseChangeBasicOpen {X Y : Scheme.{u}} (f : Y ⟶ X) (U : X.affineOpens)
    (V : Y.affineOpens) (hVU : V.1 ≤ f ⁻¹ᵁ U.1) (U₀ : X.Opens) (V₀ : Y.Opens)
    (a : Γ(X, U.1)) (b : Γ(Y, V.1)) (ha : U₀ = X.basicOpen a) (hb : V₀ = Y.basicOpen b)
    (hU₀ : U₀ ≤ U.1) (hV₀ : V₀ ≤ V.1) (hV₀U₀ : V₀ ≤ f ⁻¹ᵁ U₀) :
    letI : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U.1 V.1 hVU).hom.toAlgebra
    letI : Algebra Γ(X, U₀) Γ(Y, V₀) := (f.appLE U₀ V₀ hV₀U₀).hom.toAlgebra
    letI : Algebra Γ(X, U.1) Γ(X, U₀) := (X.presheaf.map (homOfLE hU₀).op).hom.toAlgebra
    letI : Algebra Γ(Y, V.1) Γ(Y, V₀) := (Y.presheaf.map (homOfLE hV₀).op).hom.toAlgebra
    Stacks.TateMap.ChartBaseChange Γ(X, U.1) Γ(Y, V.1) Γ(X, U₀) Γ(Y, V₀) :=
  letI : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U.1 V.1 hVU).hom.toAlgebra
  letI : Algebra Γ(X, U₀) Γ(Y, V₀) := (f.appLE U₀ V₀ hV₀U₀).hom.toAlgebra
  letI : Algebra Γ(X, U.1) Γ(X, U₀) := (X.presheaf.map (homOfLE hU₀).op).hom.toAlgebra
  letI : Algebra Γ(Y, V.1) Γ(Y, V₀) := (Y.presheaf.map (homOfLE hV₀).op).hom.toAlgebra
  haveI : IsLocalization.Away a Γ(X, U₀) :=
    U.2.isLocalization_of_eq_basicOpen a (homOfLE hU₀) ha
  haveI : IsLocalization.Away b Γ(Y, V₀) :=
    V.2.isLocalization_of_eq_basicOpen b (homOfLE hV₀) hb
  Stacks.TateMap.ChartBaseChange.ofAway a b fun x ↦ by
    change (f.appLE U.1 V.1 hVU ≫ Y.presheaf.map (homOfLE hV₀).op) x =
      (X.presheaf.map (homOfLE hU₀).op ≫ f.appLE U₀ V₀ hV₀U₀) x
    rw [Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]

/-- A principal open of a principal open of an affine open `V` is a principal open of `V`. -/
theorem exists_basicOpen_eq_of_le_basicOpen {Y : Scheme.{u}} (V : Y.affineOpens) (b : Γ(Y, V.1))
    {W : Y.Opens} (hW : W = Y.basicOpen b) (c : Γ(Y, W)) :
    ∃ b' : Γ(Y, V.1), Y.basicOpen b' = Y.basicOpen c := by
  subst hW
  exact V.2.basicOpen_basicOpen_is_basicOpen b c

/-- **Common principal refinements of two affine charts.** Around a point `y` lying in the
source opens of two affine charts `(U₁, V₁)` and `(U₂, V₂)` of `f`, and inside any open `W`
containing `y`, there is an open which is a principal open of both `V₁` and `V₂`, lying over an
open which is a principal open of both `U₁` and `U₂`. -/
theorem exists_common_basicOpen {X Y : Scheme.{u}} (f : Y ⟶ X) (U₁ U₂ : X.affineOpens)
    (V₁ V₂ : Y.affineOpens) (h₁ : V₁.1 ≤ f ⁻¹ᵁ U₁.1) (h₂ : V₂.1 ≤ f ⁻¹ᵁ U₂.1) (y : Y)
    (hy₁ : y ∈ V₁.1) (hy₂ : y ∈ V₂.1) (W : Y.Opens) (hyW : y ∈ W) :
    ∃ (a₁ : Γ(X, U₁.1)) (a₂ : Γ(X, U₂.1)) (b₁ : Γ(Y, V₁.1)) (b₂ : Γ(Y, V₂.1)),
      X.basicOpen a₁ = X.basicOpen a₂ ∧ Y.basicOpen b₁ = Y.basicOpen b₂ ∧
        y ∈ Y.basicOpen b₁ ∧ Y.basicOpen b₁ ≤ f ⁻¹ᵁ X.basicOpen a₁ ∧ Y.basicOpen b₁ ≤ W := by
  obtain ⟨a₁, a₂, ha, hya⟩ := exists_basicOpen_le_affine_inter U₁.2 U₂.2 (f.base y)
    ⟨h₁ hy₁, h₂ hy₂⟩
  obtain ⟨c₁, c₂, hc, hyc⟩ := exists_basicOpen_le_affine_inter V₁.2 V₂.2 y ⟨hy₁, hy₂⟩
  obtain ⟨d, hd, hyd⟩ := (V₁.2.basicOpen c₁).exists_basicOpen_le
    (V := W ⊓ f ⁻¹ᵁ X.basicOpen a₁) ⟨y, ⟨hyW, hya⟩⟩ hyc
  obtain ⟨b₁, hb₁⟩ := exists_basicOpen_eq_of_le_basicOpen V₁ c₁ rfl d
  obtain ⟨b₂, hb₂⟩ := exists_basicOpen_eq_of_le_basicOpen V₂ c₂ hc d
  exact ⟨a₁, a₂, b₁, b₂, ha, hb₁.trans hb₂.symm, hb₁ ▸ hyd,
    hb₁.le.trans (hd.trans inf_le_right), hb₁.le.trans (hd.trans inf_le_left)⟩

end AlgebraicGeometry.TateMap
