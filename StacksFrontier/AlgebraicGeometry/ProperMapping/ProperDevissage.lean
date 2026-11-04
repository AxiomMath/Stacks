module

public import StacksFrontier.AlgebraicGeometry.ProperMapping
public import StacksFrontier.AlgebraicGeometry.PushforwardCoherent
public import StacksFrontier.AlgebraicGeometry.CoherentOfFiniteType
public import StacksFrontier.AlgebraicGeometry.CoherentDevissage.DevissageFiltration
public import StacksFrontier.AlgebraicGeometry.Scheme.FunctorialityQuasiCoherent.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor

/-!
# Coherence of a direct image: the dévissage half of the proper mapping theorem

Let `f : X ⟶ S` be a quasi-compact quasi-separated morphism to a locally Noetherian scheme.
Coherence of `f_* ·` is stable under extensions of modules on `X` with quasi-coherent middle
term, which is hypothesis (2) of [Stacks, Tag 01YG]. Through the dévissage of
[Stacks, Tag 01YG], coherence of `f_* F` for every coherent `F` (the degree-zero assertion of
[Stacks, Tag 02O5], with no properness assumed) therefore follows from two inputs: the existence
of a dévissage filtration ([Stacks, Tag 01YF]) and coherence of `f_* i_* I` for a quasi-coherent
ideal `I` on an integral closed subscheme `i : Z ⟶ X`.

## Main results

* `Stacks.AlgebraicGeometry.ProperDevissage.isCoherent_pushforward_of_shortExact`: if `f` is
  quasi-compact and quasi-separated, `S` is locally Noetherian and `0 ⟶ F₁ ⟶ F₂ ⟶ F₃ ⟶ 0` is a
  short exact sequence of modules on `X` with `F₂` quasi-coherent, then coherence of `f_* F₁`
  and of `f_* F₃` gives coherence of `f_* F₂`.
* `Stacks.AlgebraicGeometry.ProperDevissage.isCoherent_pushforward_of_forall_hasIdealFiltration`:
  **the dévissage reduction.** With [Stacks, Tag 01YF] and the integral-ideal base case as
  explicit hypotheses, `f_* F` is coherent for every coherent `F`.
* `Stacks.AlgebraicGeometry.ProperDevissage.isCoherent_pushforward_iff_isFiniteType`: for a
  quasi-compact quasi-separated `f` and quasi-coherent `F`, coherence of `f_* F` **is** finite
  type of `f_* F`.
* `Stacks.AlgebraicGeometry.ProperDevissage.isCoherent_pushforward_comp_of_isFinite`: if
  `i : Z ⟶ X` and the composite `i ≫ f` is finite, then `f_* i_* G` is coherent for every
  coherent quasi-coherent `G` on `Z`, with no hypothesis on `f`.

## Implementation notes

**`_root_.SheafOfModules.IsCoherent` is written out throughout.** Coherence is declared twice,
and inside the `Stacks.` namespace both the bare name and the dot notation resolve to
`Stacks.SheafOfModules.IsCoherent`; the dévissage engine and the closure theory of
`ProperMapping.lean` are stated against the root constant, so leaving it unqualified would
silently state a different theorem.

## References

* [Stacks Project, Tag 02O5](https://stacks.math.columbia.edu/tag/02O5)
* [Stacks Project, Tag 01YG](https://stacks.math.columbia.edu/tag/01YG)
* [Stacks Project, Tag 01YF](https://stacks.math.columbia.edu/tag/01YF)
* [Stacks Project, Tag 01LC](https://stacks.math.columbia.edu/tag/01LC)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.ProperDevissage

variable {X S : Scheme.{u}} [IsLocallyNoetherian S]

/-- **Hypothesis (2) of [Stacks, Tag 01YG] for the property "the direct image is coherent".**
Let `f : X ⟶ S` be quasi-compact and quasi-separated with `S` locally Noetherian, and let
`T = (0 ⟶ T₁ ⟶ T₂ ⟶ T₃ ⟶ 0)` be a short exact sequence of modules on `X` whose middle term is
quasi-coherent. If `f_* T₁` and `f_* T₃` are coherent, so is `f_* T₂`. -/
theorem isCoherent_pushforward_of_shortExact (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    (T : ShortComplex X.Modules) (hT : T.ShortExact) [T.X₂.IsQuasicoherent]
    (h₁ : _root_.SheafOfModules.IsCoherent ((Scheme.Modules.pushforward f).obj T.X₁))
    (h₃ : _root_.SheafOfModules.IsCoherent ((Scheme.Modules.pushforward f).obj T.X₃)) :
    _root_.SheafOfModules.IsCoherent ((Scheme.Modules.pushforward f).obj T.X₂) := by
  have hqc₂ : ((Scheme.Modules.pushforward f).obj T.X₂).IsQuasicoherent := inferInstance
  have hqc₃ : ((Scheme.Modules.pushforward f).obj T.X₃).IsQuasicoherent :=
    @_root_.isQuasicoherent_of_isCoherent _ _ _ _ h₃
  obtain ⟨hexact, hmono⟩ :=
    (Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono
      (Scheme.Modules.pushforward f)).1 inferInstance T hT
  have hcomp : (Scheme.Modules.pushforward f).map T.f ≫
      Abelian.coimage.π ((Scheme.Modules.pushforward f).map T.g) = 0 :=
    Abelian.comp_coimage_π_eq_zero (T.map (Scheme.Modules.pushforward f)).zero
  have hU : (ShortComplex.mk _ _ hcomp).ShortExact :=
    { exact := ((T.map (Scheme.Modules.pushforward f)).exact_iff_exact_coimage_π).1 hexact
      mono_f := hmono
      epi_g := inferInstance }
  -- `Abelian.coimage` is a plain `def`, so instance search does not unfold it to the cokernel
  -- its instance is keyed on; the instance is therefore named rather than synthesized.
  have hQqc : (Abelian.coimage ((Scheme.Modules.pushforward f).map T.g)).IsQuasicoherent :=
    QuasicoherentColimits.isQuasicoherent_cokernel
      (kernel.ι ((Scheme.Modules.pushforward f).map T.g))
  have hQ : _root_.SheafOfModules.IsCoherent
      (Abelian.coimage ((Scheme.Modules.pushforward f).map T.g)) :=
    @CoherentOfFiniteType.isCoherent_of_mono_of_isQuasicoherent S ‹_› _ _ hQqc h₃
      (Abelian.factorThruCoimage ((Scheme.Modules.pushforward f).map T.g))
      (Abelian.instMonoFactorThruCoimage ((Scheme.Modules.pushforward f).map T.g))
  exact ProperMapping.isCoherent_X₂_of_shortExact_modules hU h₁ hQ

/-- **[Stacks, Tag 02O5] in degree zero, reduced to [Stacks, Tag 01YF] and one base case.**
Let `f : X ⟶ S` be quasi-compact and quasi-separated with `S` locally Noetherian. Suppose

* `hdev`: every coherent module on `X` carries a dévissage filtration — this is
  [Stacks, Tag 01YF]; and
* `hideal`: `f_* i_* I` is coherent for every quasi-coherent ideal `I ⊆ 𝒪_Z` on every integral
  closed subscheme `i : Z ⟶ X`.

Then `f_* F` is coherent for every coherent `F`. -/
theorem isCoherent_pushforward_of_forall_hasIdealFiltration
    (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    (hdev : ∀ G : X.Modules, _root_.SheafOfModules.IsCoherent G →
      CoherentDevissage.HasIdealFiltration G)
    (hideal : ∀ {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
      [AlgebraicGeometry.IsIntegral Z] (I : (SheafOfModules.unit Z.ringCatSheaf).Submodule),
      I.toSheafOfModules.IsQuasicoherent →
      _root_.SheafOfModules.IsCoherent ((Scheme.Modules.pushforward f).obj
        ((Scheme.Modules.pushforward i).obj I.toSheafOfModules)))
    (F : X.Modules) (hF : _root_.SheafOfModules.IsCoherent F) :
    _root_.SheafOfModules.IsCoherent ((Scheme.Modules.pushforward f).obj F) :=
  CoherentDevissage.property_of_forall_hasIdealFiltration
    (fun G => _root_.SheafOfModules.IsCoherent ((Scheme.Modules.pushforward f).obj G)) hdev
    (CoherentDevissage.isCoherent_of_isZero
      ((Scheme.Modules.pushforward f).map_isZero CoherentDevissage.isZero_terminal))
    (fun T hT _h₁ h₂ _h₃ hP₁ hP₃ =>
      have : T.X₂.IsQuasicoherent := @_root_.isQuasicoherent_of_isCoherent _ _ _ T.X₂ h₂
      isCoherent_pushforward_of_shortExact f T hT hP₁ hP₃)
    hideal F hF

/-- For a quasi-compact quasi-separated `f : X ⟶ S` with `S` locally Noetherian and `F`
quasi-coherent, the direct image `f_* F` is coherent exactly when it is of finite type. -/
theorem isCoherent_pushforward_iff_isFiniteType (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    (F : X.Modules) [F.IsQuasicoherent] :
    _root_.SheafOfModules.IsCoherent ((Scheme.Modules.pushforward f).obj F) ↔
      _root_.SheafOfModules.IsFiniteType ((Scheme.Modules.pushforward f).obj F) := by
  refine ⟨fun h => @_root_.SheafOfModules.IsCoherent.isFiniteType _ _ _ _ h, fun h => ?_⟩
  have := h
  exact CoherentOfFiniteType.isCoherent_of_isQuasicoherent_of_isFiniteType _

/-- If `i : Z ⟶ X` and `f : X ⟶ S` are such that the composite `i ≫ f` is finite and `S` is
locally Noetherian, then `f_* i_* G` is coherent for every coherent quasi-coherent `G` on `Z`,
with no hypothesis on `f`. -/
theorem isCoherent_pushforward_comp_of_isFinite {Z : Scheme.{u}} (i : Z ⟶ X) (f : X ⟶ S)
    [AlgebraicGeometry.IsFinite (i ≫ f)] (G : Z.Modules) [G.IsQuasicoherent]
    (hG : _root_.SheafOfModules.IsCoherent G) :
    _root_.SheafOfModules.IsCoherent ((Scheme.Modules.pushforward f).obj
      ((Scheme.Modules.pushforward i).obj G)) :=
  have : _root_.SheafOfModules.IsCoherent
      ((Scheme.Modules.pushforward (i ≫ f)).obj G) :=
    PushforwardCoherent.pushforward_isCoherent_of_isFinite (i ≫ f) G (hF := hG)
  CoherentDevissage.isCoherent_of_iso (N := (Scheme.Modules.pushforward (i ≫ f)).obj G)
    ((Scheme.Modules.pushforwardComp i f).app G)

end Stacks.AlgebraicGeometry.ProperDevissage

end

end
