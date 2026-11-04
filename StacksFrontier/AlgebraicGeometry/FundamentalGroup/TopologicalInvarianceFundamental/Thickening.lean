module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvarianceThickening
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleProper
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningMorphism.Extension

/-!
# Finite étale covers of a thickening

Let `X ⊆ X'` be a thickening of schemes, that is a closed immersion which is surjective on
points. Base change along it is an equivalence from the category `FÉt_{X'}` of schemes finite
étale over `X'` to the category `FÉt_X` of schemes finite étale over `X`.

## Main results

* `AlgebraicGeometry.isFinite_pullback_snd_iff_of_isThickening` — an étale morphism to the
  ambient scheme of a thickening is finite exactly when its base change is.
* `AlgebraicGeometry.finiteEtaleBaseChange_isEquivalence_of_isThickening` — base change along a
  thickening is an equivalence `FÉt_{X'} ⥤ FÉt_X`.

## Implementation notes

The statement records that the canonical base-change functor
`AlgebraicGeometry.finiteEtaleBaseChange` is itself an equivalence, rather than asserting that
the two categories are abstractly equivalent.

Finite étale covers are `AlgebraicGeometry.FiniteEtaleOver`, schemes étale over `X` are
`AlgebraicGeometry.Scheme.Etale`, and the inclusion of the former into the latter is
`CategoryTheory.MorphismProperty.Over.changeProp`.

## References

* [Stacks Project, Tag 0BQB](https://stacks.math.columbia.edu/tag/0BQB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

open Stacks.Thickenings

/-- **Finiteness of an étale morphism is detected on a thickening.** Let `i : X ⟶ X'` be a
thickening and let `g : Y ⟶ X'` be étale. Then `g` is finite if and only if its base change
along `i` is finite. -/
theorem isFinite_pullback_snd_iff_of_isThickening {X X' Y : Scheme.{u}} {i : X ⟶ X'}
    (hi : IsThickening i) (g : Y ⟶ X') [Etale g] :
    IsFinite (pullback.snd g i) ↔ IsFinite g := by
  have _ : IsClosedImmersion i := hi.1
  have _ : Surjective i := ⟨hi.2⟩
  have hsrc : IsThickening (pullback.fst g i) :=
    ⟨inferInstance, Surjective.surj (f := pullback.fst g i)⟩
  let φ : Arrow.mk (pullback.fst g i) ⟶ Arrow.mk i :=
    Arrow.homMk (pullback.snd g i) g pullback.condition.symm
  exact CartesianFiniteTypeMorphism.isFinite_iff
    { X := pullback g i, X' := Y, Y := X, Y' := X'
      i := pullback.fst g i, j := i, morphism := φ
      sourceThickening := hsrc, targetThickening := hi
      locallyOfFiniteType_left := inferInstanceAs (LocallyOfFiniteType (pullback.snd g i))
      locallyOfFiniteType_right := inferInstanceAs (LocallyOfFiniteType g)
      cartesian := (IsPullback.of_hasPullback g i).flip }

/-- The inclusion of the schemes finite étale over `X` into the schemes étale over `X`. -/
def finiteEtaleToEtale (X : Scheme.{u}) : FiniteEtaleOver X ⥤ X.Etale :=
  MorphismProperty.Over.changeProp X inf_le_right le_rfl

/-- The inclusion of the finite étale covers into the étale site is fully faithful. -/
def finiteEtaleToEtaleFullyFaithful (X : Scheme.{u}) :
    (finiteEtaleToEtale X).FullyFaithful :=
  MorphismProperty.Comma.fullyFaithfulChangeProp _ _ inf_le_right

/-- **Stacks Project, Tag 0BQB.** Let `X ⊆ X'` be a thickening of schemes. The functor
`FÉt_{X'} ⟶ FÉt_X`, `U' ↦ U' ×_{X'} X`, is an equivalence of categories. -/
@[stacks 0BQB, sga "1 IX 1.7" "special case", sga "1 IX 4.10" "special case"]
theorem finiteEtaleBaseChange_isEquivalence_of_isThickening {X X' : Scheme.{u}} (i : X ⟶ X')
    (hi : IsThickening i) : (finiteEtaleBaseChange i).IsEquivalence := by
  have _ : IsClosedImmersion i := hi.1
  let _ : MorphismProperty.HasPullbacksAlong (@Etale : MorphismProperty Scheme.{u}) i :=
    ⟨fun _ _ ↦ inferInstance⟩
  let _ : MorphismProperty.IsStableUnderBaseChangeAlong (@Etale : MorphismProperty Scheme.{u}) i :=
    ⟨fun pb hg ↦ MorphismProperty.IsStableUnderBaseChange.of_isPullback pb hg⟩
  let E : X'.Etale ⥤ X.Etale := MorphismProperty.Over.pullback (@Etale) ⊤ i
  have _ : E.IsEquivalence :=
    Stacks.Etale.etalePullback_isEquivalence_of_surjective_isClosedImmersion i hi.2
  let F := finiteEtaleBaseChange i
  let G := finiteEtaleToEtale X
  let G' := finiteEtaleToEtale X'
  have hobj : ∀ A : FiniteEtaleOver X', G.obj (F.obj A) = E.obj (G'.obj A) := fun _ ↦ rfl
  have hmap : ∀ {A B : FiniteEtaleOver X'} (f : A ⟶ B),
      G.map (F.map f) = E.map (G'.map f) := fun _ ↦ rfl
  have hGff := finiteEtaleToEtaleFullyFaithful X
  have hG'ff := finiteEtaleToEtaleFullyFaithful X'
  have _ : G.Faithful := hGff.faithful
  have _ : G'.Faithful := hG'ff.faithful
  have hfaithful : F.Faithful := ⟨fun {_ _ f g} h ↦ G'.map_injective (E.map_injective
    ((hmap f).symm.trans ((congrArg G.map h).trans (hmap g))))⟩
  have hfull : F.Full := ⟨fun f ↦ ⟨hG'ff.preimage (E.preimage (G.map f)),
    G.map_injective (by rw [hmap, hG'ff.map_preimage]; exact E.map_preimage _)⟩⟩
  have hess : F.EssSurj := by
    refine Functor.EssSurj.mk fun A ↦ ?_
    obtain ⟨B, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage (F := E) (G.obj A)
    have _ : IsIso e.hom.left :=
      ⟨e.inv.left, congrArg (·.left) e.hom_inv_id, congrArg (·.left) e.inv_hom_id⟩
    have _ : IsFinite (G.obj A).hom := A.prop.1
    have hfinE : IsFinite (E.obj B).hom := by
      rw [← MorphismProperty.Over.w e.hom]
      infer_instance
    have _ : Etale B.hom := B.prop
    have hfinB : IsFinite B.hom :=
      (isFinite_pullback_snd_iff_of_isThickening hi B.hom).mp hfinE
    let B' : FiniteEtaleOver X' := MorphismProperty.Over.mk ⊤ B.hom ⟨hfinB, B.prop⟩
    have eB : G'.obj B' ≅ B := MorphismProperty.Over.isoMk (Iso.refl B.left) (Category.id_comp _)
    exact ⟨B', ⟨hGff.preimageIso (eqToIso (hobj B') ≪≫ E.mapIso eB ≪≫ e)⟩⟩
  exact Functor.IsEquivalence.mk hfaithful hfull hess

end AlgebraicGeometry

end
