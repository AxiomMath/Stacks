module

public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImageFTS.NormalizedExistenceNagata
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImageFTS.NormalizedProper

/-!
# Normalized dualizing complexes along a morphism, for Nagata compactifications

In Situation [Stacks, Tag 0AU4], for the upper shriek functors of Nagata compactifications
(`Stacks.Duality.UpperShriek.nagata`), let `f : X ⟶ Y` be a morphism of schemes of finite type
over `S` and `ω_X^•`, `ω_Y^•` the dualizing complexes normalized relative to `ω_S^•`. Then `ω_X^•`
is a dualizing complex normalized relative to `ω_Y^•` ([Stacks, Tag 0AUB]). If `f` is proper and
`a` is the right adjoint of `Rf_*`, then `a(ω_Y^•) ≅ ω_X^•` ([Stacks, Tag 0AUD]), whence the trace
map `Tr_f : Rf_* ω_X^• ⟶ ω_Y^•` and the duality `Hom_X(L, ω_X^•) = Hom_Y(Rf_* L, ω_Y^•)`
([Stacks, Tag 0B6X]).

## Main results

* `Stacks.Duality.NormalizedOnOpens.exists_relative_nagata`: [Stacks, Tag 0AUB].
* `Stacks.Duality.NormalizedOnOpens.twistedInverseImageObjIsoNagata`: [Stacks, Tag 0AUD].
* `Stacks.Duality.NormalizedOnOpens.traceNagata`,
  `Stacks.Duality.NormalizedOnOpens.homEquivNagata`,
  `Stacks.Duality.NormalizedOnOpens.homEquivNagata_apply`: [Stacks, Tag 0B6X], the trace map and
  the first isomorphism.

## References

* [Stacks Project, Tag 0AUB](https://stacks.math.columbia.edu/tag/0AUB)
* [Stacks Project, Tag 0AUD](https://stacks.math.columbia.edu/tag/0AUD)
* [Stacks Project, Tag 0B6X](https://stacks.math.columbia.edu/tag/0B6X)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Duality

namespace NormalizedOnOpens

variable {X Y S : Scheme.{u}} {f : X ⟶ Y} {q : Y ⟶ S} {p : X ⟶ S} (hpe : f ≫ q = p)
  {hp : IsFiniteTypeOverNoetherian p} {hq : IsFiniteTypeOverNoetherian q}
  {ωS : quasiCoherentDerivedCategoryPlusOfModel S}

include hpe in
/-- **[Stacks, Tag 0AUB]** In Situation 0AU4, let `f : X ⟶ Y` be a morphism of schemes of finite
type over `S` and `ω_X^•`, `ω_Y^•` dualizing complexes normalized relative to `ω_S^•`. Then
`ω_X^•` is a dualizing complex normalized relative to `ω_Y^•`: `ω_Y^•` and `ω_X^•` are dualizing,
so `(Y, ω_Y^•)` is again as in Situation 0AU4, and `ω_X^•` carries isomorphisms
`ω_X^•|_W ≅ (W → Y)^! ω_Y^•` for every open `W` separated over `Y`, compatible with restriction. -/
@[stacks 0AUB]
theorem exists_relative_nagata
    (hωS : haveI := hp.base_noetherian; IsDualizingComplex ωS.obj.obj)
    (𝒦X : NormalizedOnOpens UpperShriek.nagata hp ωS)
    (𝒦Y : NormalizedOnOpens UpperShriek.nagata hq ωS) :
    (haveI := hq.source_noetherian; IsDualizingComplex 𝒦Y.complex.obj.obj) ∧
    (haveI := hp.source_noetherian; IsDualizingComplex 𝒦X.complex.obj.obj) ∧
    ∃ 𝒦 : NormalizedOnOpens UpperShriek.nagata (hp.of_comp' hq hpe) 𝒦Y.complex,
      𝒦.complex = 𝒦X.complex := by
  have hωY := 𝒦Y.isDualizingComplex_ofCompactifications nagataCompactification hωS
  refine ⟨hωY, 𝒦X.isDualizingComplex_ofCompactifications nagataCompactification hωS, ?_⟩
  obtain ⟨ι, ⟨𝒰₀⟩⟩ := SeparatedCovering.exists_nonempty hp
  obtain ⟨J, ⟨𝒱⟩⟩ := SeparatedCovering.exists_nonempty hq
  let 𝒰 : SeparatedCovering p (J × ι) := 𝒰₀.interPreimage (f := f) hp 𝒱
  have hle : ∀ k, 𝒰.U k ≤ f ⁻¹ᵁ 𝒱.U k.1 := fun _ => inf_le_left
  let 𝒦' : NormalizedOnOpens UpperShriek.nagata (hp.of_comp' hq hpe) 𝒦Y.complex :=
    normalizedDualizingComplex (hp.of_comp' hq hpe) 𝒦Y.complex hωY
  obtain ⟨e, -, -⟩ := Normalized.existsUnique_iso_nagata hωY
    ((𝒦X.toNormalized 𝒰).overMid hpe hp hq Prod.fst hle (𝒦Y.toNormalized 𝒱))
    (𝒦'.toNormalized (𝒰.overMid 𝒱 hp hq hpe Prod.fst hle))
  exact ⟨{ complex := 𝒦X.complex
           localIso := fun W hW =>
             (UpperShriek.nagata.shriek W.ι ((hp.of_comp' hq hpe).isShriekable_ι W)).mapIso e ≪≫
               𝒦'.localIso W hW
           compat := fun h hW hW' =>
             (UpperShriek.restrictLocalIso_mapIso_trans UpperShriek.nagata (hp.of_comp' hq hpe)
               𝒦Y.complex e h hW (𝒦'.localIso _ hW)).trans
               (congrArg (_ ≪≫ ·) (𝒦'.compat h hW hW')) }, rfl⟩

/-- **[Stacks, Tag 0AUD]** In Situation 0AU4, let `f : X ⟶ Y` be a proper morphism of schemes of
finite type over `S`, `ω_X^•`, `ω_Y^•` the dualizing complexes normalized relative to `ω_S^•`,
and `a` the right adjoint of `Rf_*` ([Stacks, Tag 0A9E]). Then there is a canonical isomorphism
`a(ω_Y^•) ≅ ω_X^•`. -/
@[stacks 0AUD]
def twistedInverseImageObjIsoNagata
    (hωS : haveI := hp.base_noetherian; IsDualizingComplex ωS.obj.obj) [IsProper f]
    (𝒦X : NormalizedOnOpens UpperShriek.nagata hp ωS)
    (𝒦Y : NormalizedOnOpens UpperShriek.nagata hq ωS) :
    haveI := hq.source_noetherian
    haveI := hp.source_noetherian
    (twistedInverseImage f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).obj
        𝒦Y.complex.obj ≅ 𝒦X.complex.obj :=
  twistedInverseImageObjIso nagataCompactification hpe hωS 𝒦X 𝒦Y

/-- **[Stacks, Tag 0B6X], the trace map.** In Situation 0AU4, for a proper `f : X ⟶ Y` of schemes
of finite type over `S` and the dualizing complexes `ω_X^•`, `ω_Y^•` normalized relative to
`ω_S^•`, the canonical arrow `Tr_f : Rf_* ω_X^• ⟶ ω_Y^•`: the trace map of
[Stacks, Section 0AWG] read through `a(ω_Y^•) ≅ ω_X^•` ([Stacks, Tag 0AUD]). -/
@[stacks 0B6X]
def traceNagata
    (hωS : haveI := hp.base_noetherian; IsDualizingComplex ωS.obj.obj) [IsProper f]
    (𝒦X : NormalizedOnOpens UpperShriek.nagata hp ωS)
    (𝒦Y : NormalizedOnOpens UpperShriek.nagata hq ωS) :
    haveI := hq.source_noetherian
    haveI := hp.source_noetherian
    (quasiCoherentDerivedPushforward f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).obj
        𝒦X.complex.obj ⟶ 𝒦Y.complex.obj :=
  traceOfCompactifications nagataCompactification hpe hωS 𝒦X 𝒦Y

/-- **[Stacks, Tag 0B6X], the first isomorphism.** In Situation 0AU4, for a proper `f : X ⟶ Y` of
schemes of finite type over `S`, the dualizing complexes `ω_X^•`, `ω_Y^•` normalized relative to
`ω_S^•` and `L` in `D_QCoh(𝒪_X)`, `Hom_X(L, ω_X^•) = Hom_Y(Rf_* L, ω_Y^•)`; it sends `u` to
`Tr_f ∘ Rf_* u` (`homEquivNagata_apply`). -/
@[stacks 0B6X]
def homEquivNagata
    (hωS : haveI := hp.base_noetherian; IsDualizingComplex ωS.obj.obj) [IsProper f]
    (𝒦X : NormalizedOnOpens UpperShriek.nagata hp ωS)
    (𝒦Y : NormalizedOnOpens UpperShriek.nagata hq ωS)
    (L : quasiCoherentDerivedCategory X) :
    haveI := hq.source_noetherian
    haveI := hp.source_noetherian
    (L ⟶ 𝒦X.complex.obj) ≃
      ((quasiCoherentDerivedPushforward f
        (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).obj L ⟶ 𝒦Y.complex.obj) :=
  homEquivOfCompactifications nagataCompactification hpe hωS 𝒦X 𝒦Y L

/-- **[Stacks, Tag 0B6X], the first isomorphism is produced by the trace map**:
`homEquivNagata` sends `u : L ⟶ ω_X^•` to `Tr_f ∘ Rf_* u`. -/
@[stacks 0B6X]
theorem homEquivNagata_apply
    (hωS : haveI := hp.base_noetherian; IsDualizingComplex ωS.obj.obj) [IsProper f]
    (𝒦X : NormalizedOnOpens UpperShriek.nagata hp ωS)
    (𝒦Y : NormalizedOnOpens UpperShriek.nagata hq ωS)
    (L : quasiCoherentDerivedCategory X) (u : L ⟶ 𝒦X.complex.obj) :
    haveI := hq.source_noetherian
    haveI := hp.source_noetherian
    homEquivNagata hpe hωS 𝒦X 𝒦Y L u =
      (quasiCoherentDerivedPushforward f
        (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).map u ≫
        traceNagata hpe hωS 𝒦X 𝒦Y :=
  homEquivOfCompactifications_apply nagataCompactification hpe hωS 𝒦X 𝒦Y L u

end NormalizedOnOpens

end Stacks.Duality
