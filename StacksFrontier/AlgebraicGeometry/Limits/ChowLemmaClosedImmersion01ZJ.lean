module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import StacksFrontier.AlgebraicGeometry.Limits.ChowLemma
public import StacksFrontier.AlgebraicGeometry.Morphisms.PseudoCoherentFrom

/-!
# Finite type closed in finite presentation

A finitely presented closed model of a morphism `f : X ⟶ S` is a factorization of `f` as a closed
immersion `X ⟶ Y` followed by a separated morphism `Y ⟶ S` of finite presentation (Tag 01ZJ
asserts one exists for `f` separated of finite type over a quasi-compact, quasi-separated base).
This file proves its existence for a morphism of affine schemes, for an affine scheme over an
affine open of a quasi-separated base, and over a locally Noetherian base, together with its
stability properties, and deduces Chow's lemma for a morphism with such a model from Chow's lemma
for separated morphisms of finite presentation.

## Main definitions

* `AlgebraicGeometry.HasFinitePresentationClosedModel`: `f` factors as a closed immersion followed
  by a separated morphism of finite presentation.

## Main results

* `AlgebraicGeometry.hasFinitePresentationClosedModel_of_isAffine`: a morphism of affine schemes
  locally of finite type has a finitely presented closed model, given by an affine space over the
  target.
* `AlgebraicGeometry.hasFinitePresentationClosedModel_of_isLocallyNoetherian`: over a locally
  Noetherian base, a separated quasi-compact morphism locally of finite type has a finitely
  presented closed model.
* `AlgebraicGeometry.HasFinitePresentationClosedModel.of_isClosedImmersion`: a finitely presented
  closed model descends along a closed immersion.
* `AlgebraicGeometry.HasFinitePresentationClosedModel.comp`: a finitely presented closed model is
  stable under composition with a separated morphism of finite presentation.
* `AlgebraicGeometry.HasFinitePresentationClosedModel.of_isPullback`: a finitely presented closed
  model is stable under base change.
* `AlgebraicGeometry.hasFinitePresentationClosedModel_comp_ι_of_isAffine`: an affine scheme mapping
  by a morphism locally of finite type into an affine open of a quasi-separated base has a
  finitely presented closed model over the base.
* `AlgebraicGeometry.HasChowModification.of_hasFinitePresentationClosedModel`: a morphism with a
  finitely presented closed model satisfies Chow's lemma if Chow's lemma holds for every separated
  morphism of finite presentation to the base.

## Implementation notes

"Of finite presentation" is `LocallyOfFinitePresentation` together with `QuasiCompact`;
quasi-separatedness follows from `IsSeparated`.

## References

* [Stacks Project, Tag 01ZJ](https://stacks.math.columbia.edu/tag/01ZJ)
* [Stacks Project, Tag 0202](https://stacks.math.columbia.edu/tag/0202)
-/

@[expose] public section

open CategoryTheory Limits
open scoped AlgebraicGeometry

namespace AlgebraicGeometry

universe u

/-- A finitely presented closed model of `f : X ⟶ S`: a scheme `Y`, a separated morphism
`g : Y ⟶ S` locally of finite presentation and quasi-compact, and a closed immersion `j : X ⟶ Y`
with `j ≫ g = f`. -/
def HasFinitePresentationClosedModel {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  ∃ (Y : Scheme.{u}) (g : Y ⟶ S) (j : X ⟶ Y),
    LocallyOfFinitePresentation g ∧ QuasiCompact g ∧ IsSeparated g ∧ IsClosedImmersion j ∧
      j ≫ g = f

/-- If `j : X ⟶ Y` is a closed immersion of schemes over `S` and `Y ⟶ S` has a finitely
presented closed model, then so does `X ⟶ S`. -/
theorem HasFinitePresentationClosedModel.of_isClosedImmersion {X Y S : Scheme.{u}} {j : X ⟶ Y}
    {g : Y ⟶ S} {f : X ⟶ S} [IsClosedImmersion j] (hf : j ≫ g = f)
    (hg : HasFinitePresentationClosedModel g) : HasFinitePresentationClosedModel f := by
  obtain ⟨Z, h, k, hfp, hqc, hsep, hk, hcomm⟩ := hg
  exact ⟨Z, h, j ≫ k, hfp, hqc, hsep, inferInstance, by rw [Category.assoc, hcomm, hf]⟩

/-- If `f : X ⟶ Y` has a finitely presented closed model and `g : Y ⟶ S` is separated,
quasi-compact and locally of finite presentation, then `f ≫ g` has a finitely presented closed
model. -/
theorem HasFinitePresentationClosedModel.comp {X Y S : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ S}
    (hf : HasFinitePresentationClosedModel f) [LocallyOfFinitePresentation g] [QuasiCompact g]
    [IsSeparated g] : HasFinitePresentationClosedModel (f ≫ g) := by
  obtain ⟨Z, h, j, hfp, hqc, hsep, hj, hcomm⟩ := hf
  exact ⟨Z, h ≫ g, j, inferInstance, inferInstance, inferInstance, hj, by
    rw [← Category.assoc, hcomm]⟩

/-- Let `f' : X' ⟶ S'` be the base change of `f : X ⟶ S` along `g : S' ⟶ S`, exhibited by a
cartesian square. If `f` has a finitely presented closed model, then so does `f'`. -/
theorem HasFinitePresentationClosedModel.of_isPullback {X S X' S' : Scheme.{u}} {f : X ⟶ S}
    {g : S' ⟶ S} {f' : X' ⟶ S'} {p : X' ⟶ X} (hsq : IsPullback p f' f g)
    (hf : HasFinitePresentationClosedModel f) : HasFinitePresentationClosedModel f' := by
  obtain ⟨Y, h, j, hfp, hqc, hsep, hj, hcomm⟩ := hf
  have t : IsPullback (pullback.snd h g) (pullback.fst h g) g h :=
    (IsPullback.of_hasPullback h g).flip
  have s : IsPullback f' p g (j ≫ h) := by rw [hcomm]; exact hsq.flip
  refine ⟨pullback h g, pullback.snd h g, t.lift f' (p ≫ j) (by rw [s.w, Category.assoc]),
    inferInstance, inferInstance, inferInstance, ?_, t.lift_fst _ _ _⟩
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsClosedImmersion)
    (IsPullback.of_right' s t).flip hj

/-- A morphism of affine schemes locally of finite type has a finitely presented closed model:
it factors as a closed immersion into an affine space over the target followed by the structure
morphism of that affine space. -/
theorem hasFinitePresentationClosedModel_of_isAffine {X S : Scheme.{u}} [IsAffine X] [IsAffine S]
    (f : X ⟶ S) [LocallyOfFiniteType f] : HasFinitePresentationClosedModel f := by
  obtain ⟨n, i, hi, hcomm⟩ := exists_isClosedImmersion_affineSpace f
  exact ⟨AffineSpace (ULift.{u} (Fin n)) S, AffineSpace (ULift.{u} (Fin n)) S ↘ S, i,
    inferInstance, inferInstance, inferInstance, hi, hcomm⟩

/-- If `X` is affine and `f : X ⟶ V` is locally of finite type, where `V` is an affine open of a
quasi-separated scheme `S`, then `f ≫ V.ι` has a finitely presented closed model. -/
theorem hasFinitePresentationClosedModel_comp_ι_of_isAffine {X S : Scheme.{u}} [IsAffine X]
    [QuasiSeparatedSpace S] (V : S.affineOpens) (f : X ⟶ (V.1 : Scheme.{u}))
    [LocallyOfFiniteType f] : HasFinitePresentationClosedModel (f ≫ V.1.ι) :=
  have : IsAffine (V.1 : Scheme.{u}) := V.2
  (hasFinitePresentationClosedModel_of_isAffine f).comp

/-- Over a locally Noetherian base, a separated quasi-compact morphism locally of finite type is
its own finitely presented closed model, with the identity as closed immersion. -/
theorem hasFinitePresentationClosedModel_of_isLocallyNoetherian {X S : Scheme.{u}} (f : X ⟶ S)
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] :
    HasFinitePresentationClosedModel f :=
  ⟨X, f, 𝟙 X, inferInstance, inferInstance, inferInstance, inferInstance, Category.id_comp f⟩

/-- If `f : X ⟶ S` has a finitely presented closed model and every separated, quasi-compact
morphism `Y ⟶ S` locally of finite presentation has a Chow modification, then `f` has a Chow
modification. -/
theorem HasChowModification.of_hasFinitePresentationClosedModel {X S : Scheme.{u}} {f : X ⟶ S}
    (hf : HasFinitePresentationClosedModel f)
    (H : ∀ (Y : Scheme.{u}) (g : Y ⟶ S), LocallyOfFinitePresentation g → QuasiCompact g →
      IsSeparated g → HasChowModification g) :
    HasChowModification f := by
  obtain ⟨Y, g, j, hfp, hqc, hsep, hj, hcomm⟩ := hf
  exact HasChowModification.of_isClosedImmersion hcomm (H Y g hfp hqc hsep)

end AlgebraicGeometry

end
