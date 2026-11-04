module

public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import StacksFrontier.Algebra.Homology.DerivedFunctorLongExact
public import StacksFrontier.Algebra.Homology.Resolution.NatHorseshoe

/-!
# The long exact sequence of right derived functors in the object variable

Let `Q : B ⥤ D` be an additive functor between abelian categories with `B` having enough
injectives, and let `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` be a short exact sequence of objects of `B`. There
is then a long exact sequence

  `0 ⟶ Q X₁ ⟶ Q X₂ ⟶ Q X₃ ⟶ R¹Q X₁ ⟶ ⋯ ⟶ RⁿQ X₁ ⟶ RⁿQ X₂ ⟶ RⁿQ X₃ ⟶ Rⁿ⁺¹Q X₁ ⟶ ⋯`

of right derived functors, in every degree.

Given a short exact sequence `0 ⟶ J₁ ⟶ J₂ ⟶ J₃ ⟶ 0` of cochain complexes, with `Jᵢ` an injective
resolution of `Xᵢ` and the two squares built from the augmentations commuting, applying `Q`
degreewise gives a short exact sequence of complexes in `D`. The connecting morphism is the
snake-lemma connecting morphism of that sequence, transported along
`CategoryTheory.InjectiveResolution.isoRightDerivedObj'`.

## Main definitions

* `Stacks.Cohomology.RightDerivedDelta.Horseshoe`: a resolution of a short exact sequence of
  objects by a short exact sequence of injective resolutions.
* `Stacks.Cohomology.RightDerivedDelta.Horseshoe.delta`: the connecting morphism
  `RⁿQ X₃ ⟶ Rⁿ⁺¹Q X₁`.

## Main results

* `Stacks.Cohomology.RightDerivedDelta.Horseshoe.exact_composableArrows₅`: the long exact
  sequence, as exactness of the six-term window
  `RⁿQ X₁ ⟶ RⁿQ X₂ ⟶ RⁿQ X₃ ⟶ Rⁿ⁺¹Q X₁ ⟶ Rⁿ⁺¹Q X₂ ⟶ Rⁿ⁺¹Q X₃` for every `n`.
* `Stacks.Cohomology.RightDerivedDelta.Horseshoe.delta_naturality`: the connecting morphism is
  natural in the short exact sequence, for a morphism of short exact sequences lifted to the
  resolving complexes.
* `Stacks.Cohomology.RightDerivedDelta.exists_delta_exact_composableArrows₅`: the long exact
  sequence of a short exact sequence, with no resolution mentioned.
* `Stacks.Cohomology.RightDerivedDelta.isZero_rightDerived_X₂`,
  `Stacks.Cohomology.RightDerivedDelta.isZero_rightDerived_X₃` and
  `Stacks.Cohomology.RightDerivedDelta.isZero_rightDerived_succ_X₁`: the three vanishing
  transfers read off the sequence, and
  `Stacks.Cohomology.RightDerivedDelta.nonempty_iso_rightDerived`, the isomorphism
  `RⁿQ X₃ ≅ Rⁿ⁺¹Q X₁` obtained when the two middle terms vanish.
* `Stacks.Cohomology.RightDerivedDelta.isIso_rightDerived_map_g`: `RⁿQ X₂ ⟶ RⁿQ X₃` is an
  isomorphism when `RⁿQ X₁` and `Rⁿ⁺¹Q X₁` vanish.

## References

* [Stacks Project, Tag 013T](https://stacks.math.columbia.edu/tag/013T)
* [Stacks Project, Tag 015B](https://stacks.math.columbia.edu/tag/015B)
* [Stacks Project, Tag 0111](https://stacks.math.columbia.edu/tag/0111)
-/

@[expose] public noncomputable section

open CategoryTheory Category Limits

universe v₁ v₂ u₁ u₂

namespace Stacks.Cohomology.RightDerivedDelta

variable {B : Type u₁} [Category.{v₁} B] [Abelian B]
  {D : Type u₂} [Category.{v₂} D] [Abelian D]

/-- A resolution of a short exact sequence `S` of objects by a short exact sequence of injective
resolutions: an injective resolution of each of the three terms of `S` together with a short exact
sequence of the three resolving complexes whose two squares, built from the augmentations,
commute. -/
structure Horseshoe (S : ShortComplex B) where
  /-- an injective resolution of the first term -/
  J₁ : InjectiveResolution S.X₁
  /-- an injective resolution of the middle term -/
  J₂ : InjectiveResolution S.X₂
  /-- an injective resolution of the last term -/
  J₃ : InjectiveResolution S.X₃
  /-- the first morphism of resolving complexes -/
  f : J₁.cocomplex ⟶ J₂.cocomplex
  /-- the second morphism of resolving complexes -/
  g : J₂.cocomplex ⟶ J₃.cocomplex
  /-- the two morphisms of resolving complexes compose to zero -/
  w : f ≫ g = 0
  /-- the sequence of resolving complexes is short exact -/
  shortExact : (ShortComplex.mk f g w).ShortExact
  /-- the square built from the first morphism and the augmentations commutes -/
  comm₁ : J₁.ι.f 0 ≫ f.f 0 = S.f ≫ J₂.ι.f 0
  /-- the square built from the second morphism and the augmentations commutes -/
  comm₂ : J₂.ι.f 0 ≫ g.f 0 = S.g ≫ J₃.ι.f 0

namespace Horseshoe

variable {S : ShortComplex B} (H : Horseshoe S) (Q : B ⥤ D) [Q.Additive]

/-- The image of the short exact sequence of resolving complexes under `Q`, applied degreewise. -/
@[reducible]
def mapSequence : ShortComplex (CochainComplex D ℕ) :=
  ShortComplex.mk ((Q.mapHomologicalComplex (ComplexShape.up ℕ)).map H.f)
    ((Q.mapHomologicalComplex (ComplexShape.up ℕ)).map H.g)
    (by rw [← Functor.map_comp, H.w, Functor.map_zero])

/-- Applying an additive functor `Q` degreewise to the resolution of a short exact sequence
leaves it short exact. -/
theorem shortExact_mapSequence : (H.mapSequence Q).ShortExact := by
  refine HomologicalComplex.shortExact_of_degreewise_shortExact _ fun n ↦ ?_
  have hn := (HomologicalComplex.shortExact_iff_degreewise_shortExact
    (ShortComplex.mk H.f H.g H.w)).1 H.shortExact n
  have hinj : Injective ((ShortComplex.mk H.f H.g H.w).map
      (HomologicalComplex.eval B (ComplexShape.up ℕ) n)).X₁ := H.J₁.injective n
  exact (hn.splittingOfInjective.map Q).shortExact

variable [HasInjectiveResolutions B]

/-- The connecting morphism `RⁿQ X₃ ⟶ Rⁿ⁺¹Q X₁` of a short exact sequence
`0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0`, computed from a resolution of that sequence: the snake-lemma
connecting morphism of the short exact sequence of complexes obtained by applying `Q` degreewise
to the resolving complexes, read through the identification of the homology of those complexes
with the right derived functors. -/
def delta (n : ℕ) : (Q.rightDerived n).obj S.X₃ ⟶ (Q.rightDerived (n + 1)).obj S.X₁ :=
  (H.J₃.isoRightDerivedObj' Q n).hom ≫
    (H.shortExact_mapSequence Q).δ n (n + 1) (ComplexShape.up_rel_succ n) ≫
      (H.J₁.isoRightDerivedObj' Q (n + 1)).inv

/-- `RⁿQ` applied to the first morphism of `S`, computed on the resolution. -/
theorem rightDerived_map_f (n : ℕ) :
    (Q.rightDerived n).map S.f = (H.J₁.isoRightDerivedObj' Q n).hom ≫
      HomologicalComplex.homologyMap
          ((Q.mapHomologicalComplex (ComplexShape.up ℕ)).map H.f) n ≫
        (H.J₂.isoRightDerivedObj' Q n).inv := by
  rw [← assoc, Iso.eq_comp_inv]
  exact InjectiveResolution.isoRightDerivedObj_hom_naturality S.f H.J₁ H.J₂ H.f H.comm₁ Q n

/-- `RⁿQ` applied to the second morphism of `S`, computed on the resolution. -/
theorem rightDerived_map_g (n : ℕ) :
    (Q.rightDerived n).map S.g = (H.J₂.isoRightDerivedObj' Q n).hom ≫
      HomologicalComplex.homologyMap
          ((Q.mapHomologicalComplex (ComplexShape.up ℕ)).map H.g) n ≫
        (H.J₃.isoRightDerivedObj' Q n).inv := by
  rw [← assoc, Iso.eq_comp_inv]
  exact InjectiveResolution.isoRightDerivedObj_hom_naturality S.g H.J₂ H.J₃ H.g H.comm₂ Q n

/-- The long exact sequence of the right derived functors of a fixed additive functor, in the
object variable: for a short exact sequence `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` of objects of `B`, the
six-term window

  `RⁿQ X₁ ⟶ RⁿQ X₂ ⟶ RⁿQ X₃ ⟶ Rⁿ⁺¹Q X₁ ⟶ Rⁿ⁺¹Q X₂ ⟶ Rⁿ⁺¹Q X₃`

is exact, with `Stacks.Cohomology.RightDerivedDelta.Horseshoe.delta` as the connecting morphism.
-/
theorem exact_composableArrows₅ (n : ℕ) :
    (ComposableArrows.mk₅ ((Q.rightDerived n).map S.f) ((Q.rightDerived n).map S.g)
      (H.delta Q n) ((Q.rightDerived (n + 1)).map S.f)
      ((Q.rightDerived (n + 1)).map S.g)).Exact :=
  ComposableArrows.exact_of_iso
    (ComposableArrows.isoMk₅
      (H.J₁.isoRightDerivedObj' Q n).symm (H.J₂.isoRightDerivedObj' Q n).symm
      (H.J₃.isoRightDerivedObj' Q n).symm (H.J₁.isoRightDerivedObj' Q (n + 1)).symm
      (H.J₂.isoRightDerivedObj' Q (n + 1)).symm (H.J₃.isoRightDerivedObj' Q (n + 1)).symm
      (InjectiveResolution.isoRightDerivedObj_inv_naturality S.f H.J₁ H.J₂ H.f H.comm₁ Q n).symm
      (InjectiveResolution.isoRightDerivedObj_inv_naturality S.g H.J₂ H.J₃ H.g H.comm₂ Q n).symm
      (Iso.inv_hom_id_assoc (H.J₃.isoRightDerivedObj' Q n) _).symm
      (InjectiveResolution.isoRightDerivedObj_inv_naturality S.f H.J₁ H.J₂ H.f H.comm₁ Q
        (n + 1)).symm
      (InjectiveResolution.isoRightDerivedObj_inv_naturality S.g H.J₂ H.J₃ H.g H.comm₂ Q
        (n + 1)).symm)
    (HomologicalComplex.HomologySequence.composableArrows₅_exact
      (H.shortExact_mapSequence Q) n (n + 1) (ComplexShape.up_rel_succ n))

include H in
/-- The morphism `R⁰Q X₁ ⟶ R⁰Q X₂` is a monomorphism. -/
theorem mono_rightDerived_zero_map_f : Mono ((Q.rightDerived 0).map S.f) := by
  have hmono : Mono ((H.mapSequence Q).f.f 0) :=
    ((HomologicalComplex.shortExact_iff_degreewise_shortExact _).1
      (H.shortExact_mapSequence Q) 0).mono_f
  have h1 : Mono (HomologicalComplex.homologyMap (H.mapSequence Q).f 0 ≫
      (CochainComplex.isoHomologyπ₀ (H.mapSequence Q).X₂).inv) := by
    rw [CochainComplex.isoHomologyπ₀_inv_naturality]
    infer_instance
  have h2 : Mono (HomologicalComplex.homologyMap (H.mapSequence Q).f 0) :=
    mono_of_mono (HomologicalComplex.homologyMap (H.mapSequence Q).f 0)
      (CochainComplex.isoHomologyπ₀ (H.mapSequence Q).X₂).inv
  rw [H.rightDerived_map_f Q 0]
  infer_instance

omit [HasInjectiveResolutions B] in
/-- Naturality of the snake-lemma connecting morphism of the resolved sequences, for a morphism
of resolutions of short exact sequences. -/
@[reassoc]
theorem delta_mapSequence_naturality {S' : ShortComplex B} (H' : Horseshoe S')
    (τ₁ : H.J₁.cocomplex ⟶ H'.J₁.cocomplex) (τ₂ : H.J₂.cocomplex ⟶ H'.J₂.cocomplex)
    (τ₃ : H.J₃.cocomplex ⟶ H'.J₃.cocomplex) (hf : H.f ≫ τ₂ = τ₁ ≫ H'.f)
    (hg : H.g ≫ τ₃ = τ₂ ≫ H'.g) (n : ℕ) :
    (H.shortExact_mapSequence Q).δ n (n + 1) (ComplexShape.up_rel_succ n) ≫
        HomologicalComplex.homologyMap
          ((Q.mapHomologicalComplex (ComplexShape.up ℕ)).map τ₁) (n + 1) =
      HomologicalComplex.homologyMap
          ((Q.mapHomologicalComplex (ComplexShape.up ℕ)).map τ₃) n ≫
        (H'.shortExact_mapSequence Q).δ n (n + 1) (ComplexShape.up_rel_succ n) :=
  HomologicalComplex.HomologySequence.δ_naturality
    { τ₁ := (Q.mapHomologicalComplex (ComplexShape.up ℕ)).map τ₁
      τ₂ := (Q.mapHomologicalComplex (ComplexShape.up ℕ)).map τ₂
      τ₃ := (Q.mapHomologicalComplex (ComplexShape.up ℕ)).map τ₃
      comm₁₂ := by rw [← Functor.map_comp, ← Functor.map_comp, hf]
      comm₂₃ := by rw [← Functor.map_comp, ← Functor.map_comp, hg] }
    (H.shortExact_mapSequence Q) (H'.shortExact_mapSequence Q) n (n + 1)
    (ComplexShape.up_rel_succ n)

/-- The connecting morphism is natural in the short exact sequence: let `σ : S ⟶ S'` be a
morphism of short complexes and let `τ₁, τ₂, τ₃` lift it to the resolving complexes of two
resolutions `H` of `S` and `H'` of `S'`, compatibly with the two morphisms of resolving
complexes and with the augmentations of the outer terms. Then the square built from `σ` and the
two connecting morphisms commutes. -/
theorem delta_naturality {S' : ShortComplex B} (H' : Horseshoe S') (σ : S ⟶ S')
    (τ₁ : H.J₁.cocomplex ⟶ H'.J₁.cocomplex) (τ₂ : H.J₂.cocomplex ⟶ H'.J₂.cocomplex)
    (τ₃ : H.J₃.cocomplex ⟶ H'.J₃.cocomplex)
    (hτ₁ : H.J₁.ι.f 0 ≫ τ₁.f 0 = σ.τ₁ ≫ H'.J₁.ι.f 0)
    (hτ₃ : H.J₃.ι.f 0 ≫ τ₃.f 0 = σ.τ₃ ≫ H'.J₃.ι.f 0)
    (hf : H.f ≫ τ₂ = τ₁ ≫ H'.f) (hg : H.g ≫ τ₃ = τ₂ ≫ H'.g) (n : ℕ) :
    (Q.rightDerived n).map σ.τ₃ ≫ H'.delta Q n =
      H.delta Q n ≫ (Q.rightDerived (n + 1)).map σ.τ₁ := by
  simp only [delta, assoc]
  exact (InjectiveResolution.isoRightDerivedObj_hom_naturality_assoc σ.τ₃ H.J₃ H'.J₃ τ₃ hτ₃ Q n
    _).trans (_ ≫= ((H.delta_mapSequence_naturality_assoc Q H' τ₁ τ₂ τ₃ hf hg n _).symm.trans
      (_ ≫= (InjectiveResolution.isoRightDerivedObj_inv_naturality σ.τ₁ H.J₁ H'.J₁ τ₁ hτ₁ Q
        (n + 1)).symm)))

/-- The connecting morphism is a monomorphism when `RⁿQ X₂` vanishes. -/
theorem mono_delta (n : ℕ) (h : IsZero ((Q.rightDerived n).obj S.X₂)) : Mono (H.delta Q n) := by
  have := (H.shortExact_mapSequence Q).mono_δ n (n + 1) (ComplexShape.up_rel_succ n)
    (h.of_iso (H.J₂.isoRightDerivedObj' Q n).symm)
  dsimp only [delta]
  infer_instance

/-- The connecting morphism is an epimorphism when `Rⁿ⁺¹Q X₂` vanishes. -/
theorem epi_delta (n : ℕ) (h : IsZero ((Q.rightDerived (n + 1)).obj S.X₂)) :
    Epi (H.delta Q n) := by
  have := (H.shortExact_mapSequence Q).epi_δ n (n + 1) (ComplexShape.up_rel_succ n)
    (h.of_iso (H.J₂.isoRightDerivedObj' Q (n + 1)).symm)
  dsimp only [delta]
  infer_instance

/-- The connecting morphism `RⁿQ X₃ ⟶ Rⁿ⁺¹Q X₁` is an isomorphism when `RⁿQ X₂` and
`Rⁿ⁺¹Q X₂` vanish. -/
theorem isIso_delta (n : ℕ) (h : IsZero ((Q.rightDerived n).obj S.X₂))
    (h' : IsZero ((Q.rightDerived (n + 1)).obj S.X₂)) : IsIso (H.delta Q n) :=
  have := H.mono_delta Q n h
  have := H.epi_delta Q n h'
  isIso_of_mono_of_epi _

include H in
/-- `RⁿQ X₂ ⟶ RⁿQ X₃` is an isomorphism when `RⁿQ X₁` and `Rⁿ⁺¹Q X₁` both vanish. -/
theorem isIso_rightDerived_map_g (n : ℕ) (h : IsZero ((Q.rightDerived n).obj S.X₁))
    (h' : IsZero ((Q.rightDerived (n + 1)).obj S.X₁)) :
    IsIso ((Q.rightDerived n).map S.g) := by
  have hse := H.shortExact_mapSequence Q
  have hmono : Mono (HomologicalComplex.homologyMap (H.mapSequence Q).g n) :=
    (ShortComplex.exact_iff_mono _
      ((h.of_iso (H.J₁.isoRightDerivedObj' Q n).symm).eq_of_src _ 0)).1 (hse.homology_exact₂ n)
  have hepi : Epi (HomologicalComplex.homologyMap (H.mapSequence Q).g n) :=
    (ShortComplex.exact_iff_epi _
      ((h'.of_iso (H.J₁.isoRightDerivedObj' Q (n + 1)).symm).eq_of_tgt _ 0)).1
      (hse.homology_exact₃ n (n + 1) (ComplexShape.up_rel_succ n))
  have := isIso_of_mono_of_epi (HomologicalComplex.homologyMap (H.mapSequence Q).g n)
  rw [H.rightDerived_map_g Q n]
  infer_instance

/-- When the middle term of `S` is injective, the connecting morphism
`Rⁿ⁺¹Q X₃ ⟶ Rⁿ⁺²Q X₁` is an isomorphism. -/
theorem isIso_delta_of_injective [Injective S.X₂] (n : ℕ) : IsIso (H.delta Q (n + 1)) :=
  H.isIso_delta Q (n + 1) (Q.isZero_rightDerived_obj_injective_succ n S.X₂)
    (Q.isZero_rightDerived_obj_injective_succ (n + 1) S.X₂)

/-- The connecting morphism `Rⁿ⁺¹Q X₃ ≅ Rⁿ⁺²Q X₁` as an isomorphism, when the middle term of `S`
is injective. -/
def deltaIsoOfInjective [Injective S.X₂] (n : ℕ) :
    (Q.rightDerived (n + 1)).obj S.X₃ ≅ (Q.rightDerived (n + 1 + 1)).obj S.X₁ :=
  @asIso _ _ _ _ (H.delta Q (n + 1)) (H.isIso_delta_of_injective Q n)

end Horseshoe

section Vanishing

variable {T : ShortComplex D}

/-- Transfer of vanishing along an exact short complex: if the outer terms of `T` are isomorphic to
zero objects, so is the middle term. -/
private theorem isZero_of_exact_of_iso (hT : T.Exact) {A₁ A₂ A₃ : D} (e₁ : A₁ ≅ T.X₁)
    (e₂ : A₂ ≅ T.X₂) (e₃ : A₃ ≅ T.X₃) (h₁ : IsZero A₁) (h₃ : IsZero A₃) : IsZero A₂ := by
  have hm : Mono T.g := (T.exact_iff_mono ((h₁.of_iso e₁.symm).eq_of_src T.f 0)).1 hT
  refine IsZero.of_iso ?_ e₂
  rw [IsZero.iff_id_eq_zero, ← cancel_mono T.g, id_comp, zero_comp]
  exact (h₃.of_iso e₃.symm).eq_of_tgt _ _

end Vanishing

namespace Horseshoe

variable {S : ShortComplex B} (H : Horseshoe S) (Q : B ⥤ D) [Q.Additive]
  [HasInjectiveResolutions B]

include H in
/-- `RⁿQ X₂` vanishes when `RⁿQ X₁` and `RⁿQ X₃` do. -/
theorem isZero_rightDerived_X₂ (n : ℕ) (h₁ : IsZero ((Q.rightDerived n).obj S.X₁))
    (h₃ : IsZero ((Q.rightDerived n).obj S.X₃)) : IsZero ((Q.rightDerived n).obj S.X₂) :=
  isZero_of_exact_of_iso ((H.shortExact_mapSequence Q).homology_exact₂ n)
    (H.J₁.isoRightDerivedObj' Q n) (H.J₂.isoRightDerivedObj' Q n)
    (H.J₃.isoRightDerivedObj' Q n) h₁ h₃

include H in
/-- `RⁿQ X₃` vanishes when `RⁿQ X₂` and `Rⁿ⁺¹Q X₁` do. -/
theorem isZero_rightDerived_X₃ (n : ℕ) (h₂ : IsZero ((Q.rightDerived n).obj S.X₂))
    (h₁ : IsZero ((Q.rightDerived (n + 1)).obj S.X₁)) :
    IsZero ((Q.rightDerived n).obj S.X₃) :=
  isZero_of_exact_of_iso
    ((H.shortExact_mapSequence Q).homology_exact₃ n (n + 1) (ComplexShape.up_rel_succ n))
    (H.J₂.isoRightDerivedObj' Q n) (H.J₃.isoRightDerivedObj' Q n)
    (H.J₁.isoRightDerivedObj' Q (n + 1)) h₂ h₁

include H in
/-- `Rⁿ⁺¹Q X₁` vanishes when `RⁿQ X₃` and `Rⁿ⁺¹Q X₂` do. -/
theorem isZero_rightDerived_succ_X₁ (n : ℕ) (h₃ : IsZero ((Q.rightDerived n).obj S.X₃))
    (h₂ : IsZero ((Q.rightDerived (n + 1)).obj S.X₂)) :
    IsZero ((Q.rightDerived (n + 1)).obj S.X₁) :=
  isZero_of_exact_of_iso
    ((H.shortExact_mapSequence Q).homology_exact₁ n (n + 1) (ComplexShape.up_rel_succ n))
    (H.J₃.isoRightDerivedObj' Q n) (H.J₁.isoRightDerivedObj' Q (n + 1))
    (H.J₂.isoRightDerivedObj' Q (n + 1)) h₃ h₂

include H in
/-- `Rⁿ⁺¹Q X₁` vanishes when `RⁿQ X₂ ⟶ RⁿQ X₃` is an epimorphism and `Rⁿ⁺¹Q X₂` vanishes. -/
theorem isZero_rightDerived_succ_X₁_of_epi (n : ℕ) (hg : Epi ((Q.rightDerived n).map S.g))
    (h₂ : IsZero ((Q.rightDerived (n + 1)).obj S.X₂)) :
    IsZero ((Q.rightDerived (n + 1)).obj S.X₁) := by
  have hzero : H.delta Q n = 0 := zero_of_epi_comp ((Q.rightDerived n).map S.g) (by
    rw [H.rightDerived_map_g Q n]
    simp [delta, reassoc_of% ((H.shortExact_mapSequence Q).comp_δ n (n + 1)
      (ComplexShape.up_rel_succ n))])
  have := H.epi_delta Q n h₂
  rw [hzero] at this
  exact IsZero.of_epi_zero ((Q.rightDerived n).obj S.X₃) _

end Horseshoe

section Existence

variable [EnoughInjectives B] {S : ShortComplex B} (hS : S.ShortExact) (Q : B ⥤ D) [Q.Additive]

/-- A resolution of a short exact sequence of objects by a short exact sequence of injective
resolutions, chosen by the horseshoe lemma. -/
noncomputable def horseshoe : Horseshoe S :=
  Classical.choice (by
    obtain ⟨J₁, J₂, J₃, f, g, w, hse, h₁, h₂, -⟩ := hS.exists_injectiveResolution_shortExact
    exact ⟨⟨J₁, J₂, J₃, f, g, w, hse, h₁, h₂⟩⟩)

include hS in
/-- The long exact sequence of the right derived functors of a fixed additive functor, in the
object variable: for a short exact sequence
`0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` of objects of an abelian category with enough injectives and an additive
`Q`, there are connecting morphisms `δⁿ : RⁿQ X₃ ⟶ Rⁿ⁺¹Q X₁` such that `R⁰Q X₁ ⟶ R⁰Q X₂` is a
monomorphism and

  `RⁿQ X₁ ⟶ RⁿQ X₂ ⟶ RⁿQ X₃ ⟶ Rⁿ⁺¹Q X₁ ⟶ Rⁿ⁺¹Q X₂ ⟶ Rⁿ⁺¹Q X₃`

is exact for every `n`. -/
theorem exists_delta_exact_composableArrows₅ :
    ∃ delta : ∀ n : ℕ, (Q.rightDerived n).obj S.X₃ ⟶ (Q.rightDerived (n + 1)).obj S.X₁,
      Mono ((Q.rightDerived 0).map S.f) ∧
        ∀ n : ℕ, (ComposableArrows.mk₅ ((Q.rightDerived n).map S.f)
          ((Q.rightDerived n).map S.g) (delta n) ((Q.rightDerived (n + 1)).map S.f)
          ((Q.rightDerived (n + 1)).map S.g)).Exact :=
  ⟨(horseshoe hS).delta Q, (horseshoe hS).mono_rightDerived_zero_map_f Q,
    (horseshoe hS).exact_composableArrows₅ Q⟩

include hS in
/-- `RⁿQ X₂` vanishes when `RⁿQ X₁` and `RⁿQ X₃` do. -/
theorem isZero_rightDerived_X₂ (n : ℕ) (h₁ : IsZero ((Q.rightDerived n).obj S.X₁))
    (h₃ : IsZero ((Q.rightDerived n).obj S.X₃)) : IsZero ((Q.rightDerived n).obj S.X₂) :=
  (horseshoe hS).isZero_rightDerived_X₂ Q n h₁ h₃

include hS in
/-- `RⁿQ X₃` vanishes when `RⁿQ X₂` and `Rⁿ⁺¹Q X₁` do. -/
theorem isZero_rightDerived_X₃ (n : ℕ) (h₂ : IsZero ((Q.rightDerived n).obj S.X₂))
    (h₁ : IsZero ((Q.rightDerived (n + 1)).obj S.X₁)) :
    IsZero ((Q.rightDerived n).obj S.X₃) :=
  (horseshoe hS).isZero_rightDerived_X₃ Q n h₂ h₁

include hS in
/-- `Rⁿ⁺¹Q X₁` vanishes when `RⁿQ X₃` and `Rⁿ⁺¹Q X₂` do. -/
theorem isZero_rightDerived_succ_X₁ (n : ℕ) (h₃ : IsZero ((Q.rightDerived n).obj S.X₃))
    (h₂ : IsZero ((Q.rightDerived (n + 1)).obj S.X₂)) :
    IsZero ((Q.rightDerived (n + 1)).obj S.X₁) :=
  (horseshoe hS).isZero_rightDerived_succ_X₁ Q n h₃ h₂

include hS in
/-- `Rⁿ⁺¹Q X₁` vanishes when `RⁿQ X₂ ⟶ RⁿQ X₃` is an epimorphism and `Rⁿ⁺¹Q X₂` vanishes. -/
theorem isZero_rightDerived_succ_X₁_of_epi (n : ℕ) (hg : Epi ((Q.rightDerived n).map S.g))
    (h₂ : IsZero ((Q.rightDerived (n + 1)).obj S.X₂)) :
    IsZero ((Q.rightDerived (n + 1)).obj S.X₁) :=
  (horseshoe hS).isZero_rightDerived_succ_X₁_of_epi Q n hg h₂

include hS in
/-- `RⁿQ X₃ ≅ Rⁿ⁺¹Q X₁` when the two middle terms `RⁿQ X₂` and `Rⁿ⁺¹Q X₂` vanish. -/
theorem nonempty_iso_rightDerived (n : ℕ) (h : IsZero ((Q.rightDerived n).obj S.X₂))
    (h' : IsZero ((Q.rightDerived (n + 1)).obj S.X₂)) :
    Nonempty ((Q.rightDerived n).obj S.X₃ ≅ (Q.rightDerived (n + 1)).obj S.X₁) :=
  ⟨@asIso _ _ _ _ ((horseshoe hS).delta Q n) ((horseshoe hS).isIso_delta Q n h h')⟩

include hS in
/-- `RⁿQ X₂ ⟶ RⁿQ X₃` is an isomorphism when `RⁿQ X₁` and `Rⁿ⁺¹Q X₁` both vanish. -/
theorem isIso_rightDerived_map_g (n : ℕ) (h : IsZero ((Q.rightDerived n).obj S.X₁))
    (h' : IsZero ((Q.rightDerived (n + 1)).obj S.X₁)) :
    IsIso ((Q.rightDerived n).map S.g) :=
  (horseshoe hS).isIso_rightDerived_map_g Q n h h'

include hS in
/-- `Rⁿ⁺¹Q X₃ ≅ Rⁿ⁺²Q X₁` for a short exact sequence `S` with injective middle term. -/
theorem nonempty_iso_rightDerived_of_injective [Injective S.X₂] (n : ℕ) :
    Nonempty ((Q.rightDerived (n + 1)).obj S.X₃ ≅ (Q.rightDerived (n + 1 + 1)).obj S.X₁) :=
  ⟨(horseshoe hS).deltaIsoOfInjective Q n⟩

include hS in
/-- `Rⁿ⁺²Q X₁` vanishes when `Rⁿ⁺¹Q X₃` does, for `S` with injective middle term. -/
theorem isZero_rightDerived_succ_X₁_of_injective [Injective S.X₂] (n : ℕ)
    (h₃ : IsZero ((Q.rightDerived (n + 1)).obj S.X₃)) :
    IsZero ((Q.rightDerived (n + 1 + 1)).obj S.X₁) :=
  isZero_rightDerived_succ_X₁ hS Q (n + 1) h₃
    (Q.isZero_rightDerived_obj_injective_succ (n + 1) S.X₂)

include hS in
/-- `Rⁿ⁺¹Q X₃` vanishes when `Rⁿ⁺²Q X₁` does, for `S` with injective middle term. -/
theorem isZero_rightDerived_X₃_of_injective [Injective S.X₂] (n : ℕ)
    (h₁ : IsZero ((Q.rightDerived (n + 1 + 1)).obj S.X₁)) :
    IsZero ((Q.rightDerived (n + 1)).obj S.X₃) :=
  isZero_rightDerived_X₃ hS Q (n + 1) (Q.isZero_rightDerived_obj_injective_succ n S.X₂) h₁

end Existence

end Stacks.Cohomology.RightDerivedDelta

end
