module

public import StacksFrontier.AlgebraicGeometry.Artin.ContractionClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionDiagonalRepresent
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionDiagonalTransport
import StacksFrontier.AlgebraicGeometry.ClosedPushforward.Coherent

/-!
# The diagonal of Artin's contraction functor

In the situation of Stacks 0GH8, recorded by `AlgebraicGeometry.Artin.ContractionSituation`, let
`F` be the functor of Stacks 0GHA on locally Noetherian schemes over `S`
(`AlgebraicGeometry.Artin.contractionFunctor`). If `X' → S` and `W → S` are separated, then the
diagonal `Δ : F → F × F` is representable by closed immersions.

## Main results

* `AlgebraicGeometry.Artin.ContractionEqualizer.exists_isClosedImmersion_factors_iff_of_isProper`:
  for the data of Stacks 0GHD over a locally Noetherian `V`, if `E' → V` is proper and
  `E_W → V_{/Z}` is a closed immersion, there is a closed subscheme of `V` through which a
  morphism from a locally Noetherian scheme factors exactly when the two elements of `F(V)`
  restrict to the same element.
* `AlgebraicGeometry.Artin.relative_isClosedImmersion_diag_contractionFunctor`: if `X' → S` and
  `W → S` are separated, the diagonal of `F` is representable by closed immersions.

## References

* [Stacks Project, Tag 001X](https://stacks.math.columbia.edu/tag/001X)
* [Stacks Project, Tag 0GHD](https://stacks.math.columbia.edu/tag/0GHD)
* [Stacks Project, Tag 0GHE](https://stacks.math.columbia.edu/tag/0GHE)
* [Stacks Project, Tag 0GHF](https://stacks.math.columbia.edu/tag/0GHF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Artin.ContractionEqualizer

open ContractionSituation

attribute [local instance] Space.pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {c : ContractionSituation B S hS} {V : BigFppfOver B S hS}

/-- **The equalizer of two elements of `F(V)`.** For the data of Stacks 0GHD over a locally
Noetherian scheme `V`, if `E' ⟶ V` is proper and `E_W ⟶ V_{/Z}` is a closed immersion, there is a
closed subscheme `e : b ⟶ V` such that a morphism `φ : A ⟶ V` from a locally Noetherian scheme
factors through `e` exactly when the two triples restrict to the same element of `F(A)`. -/
theorem exists_isClosedImmersion_factors_iff_of_isProper
    (d : ContractionEqualizer c V) (hVN : IsLocallyNoetherian V.left.obj)
    (hp : Space.IsProper B S hS d.toBase)
    (hEW : FormalSpace.IsClosedImmersion B S hS (equalizer.ι d.xhat₁ d.xhat₂)) :
    ∃ (b : BigFppfOver B S hS) (e : b ⟶ V),
      _root_.AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map e) ∧
      ∀ (A : BigFppfOver B S hS), IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj A) →
        ∀ φ : A ⟶ V, (∃ ψ : A ⟶ b, ψ ≫ e = φ) ↔ mapTriple c φ d.t₁ = mapTriple c φ d.t₂ := by
  have h0GHE : ∃ (X : (BigFppfOver B V.left.obj V.left.property)ᵒᵖ ⥤ Type u)
      (s : Solution (d.situation hVN) X),
      Set.range (Space.pointsMap B V.left.obj V.left.property s.U.toFunctor s.U.ι) = s.Tᶜ ∧
        Space.IsClosedImmersion B V.left.obj V.left.property (terminal.from X) := by
    exact exists_solution_of_isClosedImmersion (d.situation hVN) (d.isProper_terminal_from hp hVN)
      d.ZOverV d.isClosed_ZOverV
      (d.preimage_ZOverV hVN) (d.openPartMap hVN) (d.isClosedImmersion_openPartMap hp hVN)
      (d.formalPartMap hVN) (d.isClosedImmersion_formalPartMap hEW hVN)
  obtain ⟨X, s, hU, hX⟩ := h0GHE
  exact d.exists_isClosedImmersion_factors_iff (d.morIsoDiagonalFibre hVN s hU) hX

end AlgebraicGeometry.Artin.ContractionEqualizer

namespace AlgebraicGeometry.Artin

open ContractionSituation ContractionEqualizer

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- In the situation of Stacks 0GH8, if `X' ⟶ S` and `W ⟶ S` are separated, then the diagonal
`Δ : F ⟶ F × F` of the functor `F` of Stacks 0GHA is representable by closed immersions: for every
locally Noetherian scheme `V` over `S` and every morphism `h_V ⟶ F × F`, the fibre product with `Δ`
is represented by a locally Noetherian scheme over `S` whose morphism to `V` is a closed immersion.
-/
@[stacks 0GHF]
theorem relative_isClosedImmersion_diag_contractionFunctor (c : ContractionSituation B S hS)
    (hX' : Space.IsSeparated B S hS (terminal.from c.X'))
    (hW : FormalSpace.IsSeparatedMorphism B S hS (terminal.from c.W)) :
    (MorphismProperty.inverseImage (@IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
        (LocallyNoetherianOver.toScheme B S hS)).relative
      (uliftYoneda.{u + 1} (C := LocallyNoetherianOver B S hS)) (diag (contractionFunctor c)) := by
  have : MorphismProperty.RespectsIso (MorphismProperty.inverseImage
      (@IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      (LocallyNoetherianOver.toScheme B S hS)) :=
    MorphismProperty.RespectsIso.inverseImage _ _
  apply MorphismProperty.relative.of_exists
  intro a g
  let t₁ : Triple c a.obj := uliftYonedaEquiv.{u + 1} (g ≫ prod.fst)
  let t₂ : Triple c a.obj := uliftYonedaEquiv.{u + 1} (g ≫ prod.snd)
  have hg : g =
      prod.lift (uliftYonedaEquiv.{u + 1}.symm t₁) (uliftYonedaEquiv.{u + 1}.symm t₂) := by
    ext : 1 <;> simp [t₁, t₂]
  let d : ContractionEqualizer c a.obj :=
    ⟨t₁, t₂, t₁.compatible.some, t₂.compatible.some⟩
  have hVN : IsLocallyNoetherian a.obj.left.obj := a.property
  obtain ⟨b, e, he, hiff⟩ := d.exists_isClosedImmersion_factors_iff_of_isProper hVN
    (d.isProper_toBase hX') (d.isClosedImmersion_ι_EW hW)
  have : _root_.AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map e) := he
  have : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj a.obj) := a.property
  have hb : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj b) :=
    isLocallyNoetherian_of_isClosedImmersion ((BigFppfOver.toScheme B S hS).map e)
  let bN : LocallyNoetherianOver B S hS := ⟨b, hb⟩
  let eN : bN ⟶ a := ObjectProperty.homMk e
  have : Mono eN := by
    have : Mono ((LocallyNoetherianOver.toScheme B S hS).map eN) :=
      inferInstanceAs (Mono ((BigFppfOver.toScheme B S hS).map e))
    exact (LocallyNoetherianOver.toScheme B S hS).mono_of_mono_map this
  have key := isPullback_diag_of_factors_iff.{u + 1} (contractionFunctor c) eN t₁ t₂ (fun A φ => by
    refine Iff.trans ?_ (hiff A.obj A.property φ.hom)
    constructor
    · rintro ⟨ψ, hψ⟩
      exact ⟨ψ.hom, congrArg (fun k => k.hom) hψ⟩
    · rintro ⟨ψ, hψ⟩
      exact ⟨ObjectProperty.homMk ψ, by ext : 1; exact hψ⟩)
  rw [← hg] at key
  exact ⟨bN, _, eN, key, he⟩

end AlgebraicGeometry.Artin
