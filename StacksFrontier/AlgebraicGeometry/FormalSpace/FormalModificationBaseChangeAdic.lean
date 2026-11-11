module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.FibreProductFormalBase
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FormalModificationBaseChange
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigEtaleBaseChangeCharts
public import StacksFrontier.AlgebraicGeometry.FormalSpace.WeakIdealPresentation
import StacksCore.Tactic.StacksAttribute

/-!
# Formal modifications are stable under adic base change

Let `S` be a scheme contained in a big fppf site `B`, let `f : X ⟶ Y` be a formal modification
of locally Noetherian formal algebraic spaces over `S` and let `g : Z ⟶ Y` be an adic morphism
(Definition 0AQ3) with `Z` locally Noetherian. **Stacks 0GDN** says that the base change
`X ×_Y Z ⟶ Z` is a formal modification.

## Main results

* `AlgebraicGeometry.FormalSpace.isNoetherian_formalSpectrum_of_isNoetherianAdic`: the formal
  spectrum of a Noetherian adic topological ring is a Noetherian affine formal algebraic space.
* `AlgebraicGeometry.FormalSpace.isLocallyNoetherian_pullback_of_isRigEtale`: the fibre product
  of a rig-étale morphism and an adic morphism of locally Noetherian formal algebraic spaces is
  locally Noetherian.
* `AlgebraicGeometry.FormalSpace.IsRigSurjective.of_isPullback_of_isAdicMorphism`: Stacks 0AQS
  for a base change along an adic morphism.
* `AlgebraicGeometry.FormalSpace.isFormalModification_pullback_snd_of_isAdicMorphism`:
  **Stacks 0GDN**.

## Implementation notes

The proof follows the source field by field: properness by Stacks 0GBT
(`AlgebraicGeometry.FormalSpace.IsProper.of_isPullback`), rig-étaleness by Stacks 0GD1
(`AlgebraicGeometry.FormalSpace.isRigEtale_pullback_snd_of_isLocallyNoetherian`), and the
rig-surjectivity of the base change and of its diagonal by Stacks 0AQS, the diagonal of the base
change being the base change of the diagonal of `f` along the adic morphism
`X' ×_{Z} X' ⟶ X ×_Y X`. The base-change argument of Stacks 0AQS uses only that the morphism one
bases along is representable by algebraic spaces, that is adic; it is stated here in that form.

That `X ×_Y Z` is locally Noetherian, part of the standing hypotheses of Definition 0GDK, is not
taken from Stacks 0AQ8: the fibre product is a formal algebraic space (Stacks 0AJ3), and the
covering of the proof of Stacks 0GD1 is by formal spectra of Noetherian adic rings.

## References

* [Stacks Project, Tag 0GDN](https://stacks.math.columbia.edu/tag/0GDN)
* [Stacks Project, Tag 0GD1](https://stacks.math.columbia.edu/tag/0GD1)
* [Stacks Project, Tag 0AQS](https://stacks.math.columbia.edu/tag/0AQS)
* [Stacks Project, Tag 0GBT](https://stacks.math.columbia.edu/tag/0GBT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalRing

universe u

namespace AlgebraicGeometry.FormalSpace

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The formal spectrum of a Noetherian adic topological ring over `S` is a Noetherian affine
formal algebraic space: it is presented by the spectra of the quotients of the ring by its
weak ideals of definition, whose section-ring projections are surjective (Stacks 0AIC). -/
theorem isNoetherian_formalSpectrum_of_isNoetherianAdic {A : Type u} [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A] (hA : IsNoetherianAdic A)
    (D : QuotientSystem B S hS A) : IsNoetherian B S hS (formalSpectrum D) := by
  have hAw := hA.1.isWeaklyAdmissible
  have haff : IsAffineFormalAlgebraicSpace B S hS (formalSpectrum D) :=
    isAffineFormalAlgebraicSpace_of_iso_formalSpectrum_of_isAdic B S hS hA.1 D (Iso.refl _)
  let P : WeakIdealColimitPresentation B S hS A (formalSpectrum D) :=
    { diagram := D.diagram
      quotientIso := fun _ => Iso.refl _
      quotientIso_natural := by intro first second arrow; rfl
      colimitIso := Iso.refl _ }
  obtain ⟨-, hall⟩ := hasAllSurjectivePresentations_of_weakIdealColimitPresentation B S hS A hAw
    haff.1 P
  obtain ⟨-, I, pre, hne, hdir, Dg, hDg, he⟩ := id haff
  let := pre
  exact ⟨⟨haff, I, pre, hne, hdir, Dg, hDg, he, hall I pre Dg hDg he⟩, A, inferInstance,
    inferInstance, inferInstance, inferInstance, ⟨hAw, ⟨P⟩⟩, hA.2, hA.1⟩

/-- **The fibre product is locally Noetherian.** Let `f : X ⟶ Y` be a rig-étale morphism and
`g : Z ⟶ Y` an adic morphism of locally Noetherian formal algebraic spaces over `S`. Then
`X ×_Y Z` is a locally Noetherian formal algebraic space: it is a formal algebraic space by
Stacks 0AJ3, and the covering of the proof of Stacks 0GD1 is an atlas of it by formal spectra of
Noetherian adic rings. -/
theorem isLocallyNoetherian_pullback_of_isRigEtale {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y)
    (g : Z ⟶ Y) (hX : IsLocallyNoetherian B S hS X) (hY : IsLocallyNoetherian B S hS Y)
    (hZ : IsLocallyNoetherian B S hS Z) (hf : IsRigEtale B S hS f)
    (hg : IsAdicMorphism B S hS g) : IsLocallyNoetherian B S hS (pullback f g) := by
  obtain ⟨I, U, u, ⟨haff, het, hsurj⟩, hfac⟩ :=
    correspondsToRigEtaleMapAfterSourceCover_pullback_snd B S hS f g hX hY hZ hf hg
  refine ⟨isFormalAlgebraicSpace_pullback_of_isFormalAlgebraicSpace B S hS f g hY.1 hX.1 hZ.1,
    I, U, u, haff, het, hsurj, fun i ↦ ?_⟩
  obtain ⟨V, v, t, -, -, -, ht⟩ := hfac i
  obtain ⟨A, R, _, _, _, _, _, _, _, _, -, hCR, -, -, E, eU, -⟩ := ht
  exact isNoetherian_of_iso B S hS eU.symm (isNoetherian_formalSpectrum_of_isNoetherianAdic B S hS
    hCR E)

/-- **Stacks 0AQS, along an adic morphism.** Let `p : W ⟶ Z` and `q : W ⟶ X` be the legs of a
cartesian square over `g : Z ⟶ Y` and `f : X ⟶ Y`. If `f` is rig-surjective and `g` is adic,
then `p` is rig-surjective: an adic point of `Z` composed with `g` is an adic point of `Y`, a
lift of it to `X` pairs with the point of `Z` to give a lift to `W`. -/
theorem IsRigSurjective.of_isPullback_of_isAdicMorphism {W X Y Z : FppfSheaf B S hS}
    {p : W ⟶ Z} {q : W ⟶ X} {g : Z ⟶ Y} {f : X ⟶ Y} (sq : IsPullback p q g f)
    (hg : IsAdicMorphism B S hS g) (hsf : IsRigSurjective B S hS f) :
    IsRigSurjective B S hS p := by
  intro R _ _ _ _ _ _ hRadic hRcomplete hRweak D pt hpt
  obtain ⟨R', hR'ring, hR'dom, hR'dvr, hR'alg, hR'ext, hR'top, hR'topring, hR'lin, hR'adic,
    hR'complete, D', e, x, he, hx⟩ :=
    hsf R hRadic hRcomplete hRweak D (pt ≫ g)
      (Space.isRepresentableByAlgebraicSpacesULift_comp B S hS pt.hom g.hom hpt hg)
  exact ⟨R', hR'ring, hR'dom, hR'dvr, hR'alg, hR'ext, hR'top, hR'topring, hR'lin, hR'adic,
    hR'complete, D', e,
    sq.lift (formalSpectrumMap hRweak e ≫ pt) x (by rw [Category.assoc]; exact hx.symm),
    he, sq.lift_fst _ _ _⟩

/-- **Stacks 0GDN.** Let `f : X ⟶ Y` be a morphism of locally Noetherian formal algebraic spaces
over `S` which is a formal modification. Then for any adic morphism `g : Z ⟶ Y` of locally
Noetherian formal algebraic spaces, the base change `X ×_Y Z ⟶ Z` is a formal modification.

The fibre product is locally Noetherian by
`AlgebraicGeometry.FormalSpace.isLocallyNoetherian_pullback_of_isRigEtale`; properness is
Stacks 0GBT, rig-étaleness Stacks 0GD1, and the rig-surjectivity of the base change and of its
diagonal Stacks 0AQS, the diagonal being the base change of `Δ_f` along the adic comparison
morphism `X' ×_Z X' ⟶ X ×_Y X` of `AlgebraicGeometry.FormalSpace.isPullback_selfPullbackMap`.
No hypothesis beyond those of the source is made: `g` is adic in the sense of Definition 0AQ3,
and neither `g` nor `Δ_f` is assumed locally of finite type. -/
@[stacks 0GDN]
theorem isFormalModification_pullback_snd_of_isAdicMorphism {X Y Z : FppfSheaf B S hS}
    (f : X ⟶ Y) (g : Z ⟶ Y) (hZ : IsLocallyNoetherian B S hS Z)
    (hg : IsAdicMorphism B S hS g) (hf : IsFormalModification B S hS f) :
    IsFormalModification B S hS (pullback.snd f g) := by
  have sq : IsPullback (pullback.snd f g) (pullback.fst f g) g f :=
    (IsPullback.of_hasPullback f g).flip
  have hm : IsAdicMorphism B S hS
      (pullback.map (pullback.snd f g) (pullback.snd f g) f f (pullback.fst f g)
        (pullback.fst f g) g sq.w sq.w) :=
    Space.isRepresentableByAlgebraicSpacesULift_of_isPullback B S hS _ _ _ _
      ((isPullback_selfPullbackMap sq).flip.map
        (sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1)))) hg
  exact
    { isLocallyNoetherian_source := isLocallyNoetherian_pullback_of_isRigEtale B S hS f g
        hf.isLocallyNoetherian_source hf.isLocallyNoetherian_target hZ hf.isRigEtale hg
      isLocallyNoetherian_target := hZ
      isProper := IsProper.of_isPullback B S hS sq hf.isProper
      isRigEtale := isRigEtale_pullback_snd_of_isLocallyNoetherian B S hS f g
        hf.isLocallyNoetherian_source hf.isLocallyNoetherian_target hZ hf.isRigEtale hg
      isRigSurjective := IsRigSurjective.of_isPullback_of_isAdicMorphism B S hS sq hg
        hf.isRigSurjective
      isRigSurjective_diagonal := IsRigSurjective.of_isPullback_of_isAdicMorphism B S hS
        (isPullback_diagonal_selfPullbackMap sq) hm hf.isRigSurjective_diagonal }

end AlgebraicGeometry.FormalSpace

end
