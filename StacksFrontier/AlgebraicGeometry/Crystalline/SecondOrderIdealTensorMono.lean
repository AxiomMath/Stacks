module

public import StacksFrontier.AlgebraicGeometry.Crystalline.FirstOrderAmbientCrystalComparison
public import StacksFrontier.AlgebraicGeometry.Crystalline.SecondOrderProjectionFormula

/-!
# The degree-two canonical map of [Stacks, Tag 07J6] is a monomorphism

Fix a global crystalline situation `(p, (S, I, γ), X)` of [Stacks, Tag 07MF], let `F` be a sheaf
of `𝒪_{X/S}`-modules on the big crystalline site and let `(U, T, δ)` be an object of `CRIS(X/S)`
with second-order universal thickening `(U, T'', δ'')` of [Stacks, Remark 60.14.5, Tag 07J3] and
first projection `q₀ : T'' ⟶ T`.

[Stacks, Lemma 60.15.1, Tag 07J6] reads the outcome of its integrability computation "as a
section of the subsheaf `F_T ⊗_{𝒪_T} Ω²_{T/S,δ}`".  This module is where that reading becomes a
theorem: for a locally quasi-coherent sheaf crystal `F` the canonical morphism

`F_T ⊗_{𝒪_T} Ω²_{T/S,δ} ⟶ q₀_* F_{T''}`

of `Crystalline.GlobalCrystallineSituation.secondOrderTensorComparison` is a **monomorphism**.
It is the degree-two analogue of the degree-one identification
`Crystalline.GlobalCrystallineSituation.isIso_firstOrderKernelComparison_of_isSheafCrystal`, and
it is the last input that makes the integrability half of the tag unconditional for a general
crystal.

## The chain

The morphism is the composite of three steps, and each is where the degree-one chain of
`StacksFrontier/AlgebraicGeometry/Crystalline/FirstOrderIdealKernelCrystal.lean` puts its
counterpart.

1. `Crystalline.secondOrderThickeningTensorTopInr` includes `F_T ⊗_{𝒪_T} Ω²_{T/S,δ}` into
   `F_T ⊗_{𝒪_T} q₀_* 𝒪_{T''}` as a **direct summand**.  Unconditional: `q₀` is the inclusion
   `g ↦ (g, 0, 0, 0)`, so the top summand `Ω²_{T/S,δ}` of
   `𝒪_{T''} = 𝒪_T ⊕ Ω_{T/S,δ} ⊕ Ω_{T/S,δ} ⊕ Ω²_{T/S,δ}` is an `𝒪_T`-submodule retracted by the
   top coordinate, which is `Crystalline.isSplitMono_secondOrderThickeningTopInrSheaf`.
2. The **projection formula at `q₀`**, [Stacks, Tag 0FZE], identifies `F_T ⊗_{𝒪_T} q₀_* 𝒪_{T''}`
   with `q₀_* (q₀^* F_T)`.  That is
   `Crystalline.isIso_secondOrderThickeningProjectionFormulaMap`, and it is unconditional: `q₀`
   is the identity on underlying topological spaces, hence a closed embedding, and the
   projection formula at a closed embedding holds for arbitrary modules.  No quasi-coherence of
   `F` is needed.
3. The **crystal property at `q₀`** identifies `q₀^* F_T` with `F_{T''}`.  That is
   `Crystalline.GlobalCrystallineSituation.Thickening.isIso_homEquiv_symm_ambientFMap`, which is
   [Stacks, Tag 07IQ] at an arbitrary morphism of `CRIS(X/S)`, here at `q₀`.

A split monomorphism followed by two isomorphisms is a split monomorphism, so the composite is
one, and in particular a monomorphism.

Unlike the degree-one chain the conclusion here is *not* an isomorphism onto a kernel, and no
splitting criterion and no normalisation of the projection-formula map on the unit section are
needed: injectivity is all [Stacks, Tag 07J6] uses of the degree-two map, and injectivity follows
from step 1 being split without any compatibility of the comparison with the projections.

## Main definitions

* `Crystalline.GlobalCrystallineSituation.secondOrderAmbientInclMap` — `q₀^* : F_T ⟶ q₀_* F_{T''}`,
  the `f`-map of [Stacks, Tag 07IQ] at `q₀` read on the ambient schemes.
* `Crystalline.GlobalCrystallineSituation.ambientSchemeCrystalComparisonQ₀` — the comparison map
  `q₀^* F_T ⟶ F_{T''}` of [Stacks, Tag 07IQ] at `q₀`, between sheaves of modules on the ambient
  schemes.  No hypothesis.
* `Crystalline.GlobalCrystallineSituation.secondOrderTensorToAmbient` — the comparison
  `F_T ⊗_{𝒪_T} q₀_* 𝒪_{T''} ⟶ q₀_* F_{T''}`: the projection-formula map at `q₀` followed by the
  direct image of the comparison map.  No hypothesis.
* `Crystalline.GlobalCrystallineSituation.secondOrderTensorComparison` — **the degree-two
  canonical map `F_T ⊗_{𝒪_T} Ω²_{T/S,δ} ⟶ q₀_* F_{T''}`.**  No hypothesis.

## Main results

* `Crystalline.GlobalCrystallineSituation.isIso_ambientSchemeCrystalComparisonQ₀` — the crystal
  property at `q₀`.
* `Crystalline.GlobalCrystallineSituation.isIso_secondOrderTensorToAmbient` — the comparison of
  the two middle terms is an isomorphism.
* `Crystalline.GlobalCrystallineSituation.isSplitMono_secondOrderTensorComparison` and
  `Crystalline.GlobalCrystallineSituation.mono_secondOrderTensorComparison` — **the degree-two
  canonical map is a split monomorphism, hence a monomorphism**, for a sheaf crystal.

## What is and is not proved

The conclusion holds for a sheaf crystal, with no further hypothesis: the crystal condition is
the only one, and it is the source's own.  Local quasi-coherence, which [Stacks, Tag 0FZE] asks
for, is **not needed**: since `q₀` is the identity on underlying topological spaces, the projection-formula
map at `q₀` is invertible for every sheaf of modules, by
`Crystalline.isIso_secondOrderThickeningProjectionFormulaMap`.  The same applies to
the degree-one identification.

The statement is at the level of **sheaves** of `𝒪_T`-modules, which is where
[Stacks, Tag 07J6] puts it.  The global-sections form — injectivity of
`Crystalline.GlobalCrystallineSituation.diffAction₂`, equivalently of
`Crystalline.GlobalCrystallineSituation.secondOrderSectionsMap` — does **not** follow from it,
and nothing here claims it does: the source of the sheaf-level map is the sheaf tensor product,
while the source of the global-sections map is the algebraic tensor product of global sections,
and `Γ` does not commute with `⊗` on a non-affine `T`.  The counterexample is recorded in the
module documentation of
`StacksFrontier/AlgebraicGeometry/Crystalline/FirstOrderIdealSheaf.lean` and it bites in degree two
exactly as in degree one.

Nothing in this module carries a `@[stacks]` attribute.  What is proved is a *component* of the
integrability clause of [Stacks, Tag 07J6] — the degree-two half of the identification the
clause's proof uses — and not that clause; the clause itself is
`Crystalline.GlobalCrystallineSituation.crystalConnectionTensor_comp_self_eq_zero`, and at
`F = 𝒪_{X/S}` it is registered on
`Crystalline.GlobalCrystallineSituation.structureSheafCrystalConnection_isIntegrable`.

## References

* [Stacks Project, Tag 07J6](https://stacks.math.columbia.edu/tag/07J6)
* [Stacks Project, Tag 07J3](https://stacks.math.columbia.edu/tag/07J3)
* [Stacks Project, Tag 07IQ](https://stacks.math.columbia.edu/tag/07IQ)
* [Stacks Project, Tag 0FZE](https://stacks.math.columbia.edu/tag/0FZE)
* [Stacks Project, Tag 07MF](https://stacks.math.columbia.edu/tag/07MF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory

universe u

noncomputable section

namespace Crystalline

attribute [local instance] monoidalCategorySchemeModules

namespace GlobalCrystallineSituation

variable {S : GlobalCrystallineSituation.{u}}
  (M : SheafOfModules.{u} (crystallineStructureSheaf S)) (A : Thickening S)

/-! ### The crystal comparison at `q₀` -/

/-- **`q₀^* : F_T ⟶ q₀_* F_{T''}`**, the restriction along the first projection
`q₀ : T'' ⟶ T` of [Stacks, Tag 07J3], as a morphism of sheaves of `𝒪_T`-modules.  It is the
`f`-map of [Stacks, Tag 07IQ] at `q₀`, read on the ambient schemes. -/
abbrev secondOrderAmbientInclMap :
    Thickening.ambientSchemeModule M A ⟶
      (Scheme.Modules.pushforward (secondOrderThickeningSiteQ₀ S A).targetHom.hom).obj
        (Thickening.ambientSchemeModule M (secondOrderThickeningObject S A)) :=
  Thickening.ambientFMap M (secondOrderThickeningSiteQ₀ S A)

/-- **The comparison map `q₀^* F_T ⟶ F_{T''}` of [Stacks, Tag 07IQ], between sheaves of modules
on the ambient schemes.**  It is the adjoint transpose of
`Crystalline.GlobalCrystallineSituation.secondOrderAmbientInclMap` along the adjunction between
`AlgebraicGeometry.Scheme.Modules.pullback` and `AlgebraicGeometry.Scheme.Modules.pushforward`
at the morphism of schemes `q₀ : T'' ⟶ T`.

This is the degree-two counterpart of
`Crystalline.GlobalCrystallineSituation.ambientSchemeCrystalComparison`; no hypothesis. -/
def ambientSchemeCrystalComparisonQ₀ :
    (Scheme.Modules.pullback (secondOrderThickeningSiteQ₀ S A).targetHom.hom).obj
        (Thickening.ambientSchemeModule M A) ⟶
      Thickening.ambientSchemeModule M (secondOrderThickeningObject S A) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction
    (secondOrderThickeningSiteQ₀ S A).targetHom.hom).homEquiv _ _).symm
      (secondOrderAmbientInclMap M A)

/-- **Stacks Project, Tag 07IQ.**  For a crystal in `𝒪_{X/S}`-modules the comparison map
`q₀^* F_T ⟶ F_{T''}` at the first projection of the second-order universal thickening of
[Stacks, Tag 07J3], read between sheaves of modules on the ambient schemes, is an isomorphism.

This is the crystal condition at the morphism `q₀` of `CRIS(X/S)`, transported to the ambient
schemes by
`Crystalline.GlobalCrystallineSituation.Thickening.isIso_homEquiv_symm_ambientFMap`, which is
stated at an arbitrary morphism of the site. -/
theorem isIso_ambientSchemeCrystalComparisonQ₀
    {M : SheafOfModules.{u} (crystallineStructureSheaf S)}
    (hM : IsSheafCrystal M) (A : Thickening S) :
    IsIso (ambientSchemeCrystalComparisonQ₀ M A) :=
  Thickening.isIso_homEquiv_symm_ambientFMap hM (secondOrderThickeningSiteQ₀ S A)

/-! ### The comparison of the two middle terms -/

/-- **The comparison `F_T ⊗_{𝒪_T} q₀_* 𝒪_{T''} ⟶ q₀_* F_{T''}`.**  It is the projection-formula
map `Crystalline.secondOrderThickeningProjectionFormulaMap` at `q₀` followed by the direct image
along `q₀` of the comparison map
`Crystalline.GlobalCrystallineSituation.ambientSchemeCrystalComparisonQ₀`.  No hypothesis. -/
def secondOrderTensorToAmbient :
    secondOrderThickeningTensorUnitRestriction A.thickening.target S.S.scheme A.toBase.hom
        (Thickening.ambientSchemeModule M A) ⟶
      (Scheme.Modules.pushforward (secondOrderThickeningSiteQ₀ S A).targetHom.hom).obj
        (Thickening.ambientSchemeModule M (secondOrderThickeningObject S A)) :=
  secondOrderThickeningProjectionFormulaMap A.thickening.target S.S.scheme A.toBase.hom
      (Thickening.ambientSchemeModule M A) ≫
    (Scheme.Modules.pushforward (secondOrderThickeningSiteQ₀ S A).targetHom.hom).map
      (ambientSchemeCrystalComparisonQ₀ M A)

/-- **The comparison of the middle terms is an isomorphism** as soon as the comparison map of
[Stacks, Tag 07IQ] at `q₀` is one.

The projection-formula half is [Stacks, Tag 0FZE] at `q₀`, in the form
`Crystalline.isIso_secondOrderThickeningProjectionFormulaMap`, applied to the restriction `F_T`.
Neither affineness of the ambient scheme nor quasi-coherence of `F` is used: `q₀` is the identity
on underlying topological spaces, and the projection formula at such a morphism holds for every
module. -/
theorem isIso_secondOrderTensorToAmbient
    (hc : IsIso (ambientSchemeCrystalComparisonQ₀ M A)) :
    IsIso (secondOrderTensorToAmbient M A) :=
  IsIso.comp_isIso' (isIso_secondOrderThickeningProjectionFormulaMap _ _ _ _)
    (((Scheme.Modules.pushforward (secondOrderThickeningSiteQ₀ S A).targetHom.hom).mapIso
      (@asIso _ _ _ _ _ hc)).isIso_hom)

/-! ### The degree-two canonical map -/

/-- **The degree-two canonical map `F_T ⊗_{𝒪_T} Ω²_{T/S,δ} ⟶ q₀_* F_{T''}`** by which
[Stacks, Lemma 60.15.1, Tag 07J6] reads the outcome of its integrability computation inside
`F_T ⊗_{𝒪_T} Ω²_{T/S,δ}`.

It is `F_T` tensored with the inclusion `η ↦ (0, 0, 0, η)` of the top summand of `𝒪_{T''}` —
the sheaf-level counterpart of the canonical map
`Crystalline.GlobalCrystallineSituation.diffAction₂` on sections — followed by the comparison
`Crystalline.GlobalCrystallineSituation.secondOrderTensorToAmbient` of the middle terms.  No
hypothesis.

This is the degree-two counterpart of
`Crystalline.GlobalCrystallineSituation.firstOrderKernelComparison`. -/
def secondOrderTensorComparison :
    secondOrderThickeningTensorSecondExterior A.thickening.target S.S.scheme A.toBase.hom
        (Thickening.ambientSchemeModule M A) ⟶
      (Scheme.Modules.pushforward (secondOrderThickeningSiteQ₀ S A).targetHom.hom).obj
        (Thickening.ambientSchemeModule M (secondOrderThickeningObject S A)) :=
  secondOrderThickeningTensorTopInr A.thickening.target S.S.scheme A.toBase.hom
      (Thickening.ambientSchemeModule M A) ≫
    secondOrderTensorToAmbient M A

/-- **On global sections the first step of the chain is the inclusion by which
`Crystalline.GlobalCrystallineSituation.diffAction₂` reads a two-form in `𝒪_{T''}`.**  The
sheaf-level inclusion of the top summand, read over the whole ambient scheme, is
`Crystalline.GlobalCrystallineSituation.secondOrderTopSection`; so
`Crystalline.GlobalCrystallineSituation.secondOrderTensorComparison` is built on the same
inclusion `η ↦ (0, 0, 0, η)` that the global-sections canonical map of [Stacks, Tag 07J6] uses,
and not on some other morphism. -/
theorem secondOrderThickeningTopInrSheaf_app_top (η : crysSecondFormSections A) :
    (secondOrderThickeningTopInrSheaf A.thickening.target S.S.scheme A.toBase.hom).val.app
        (Opposite.op ⊤) η = secondOrderTopSection A η := rfl

/-- **The degree-two canonical map is a split monomorphism**, under the two hypotheses of
`Crystalline.GlobalCrystallineSituation.isIso_secondOrderTensorToAmbient`: the inclusion of the
top summand is split by the top coordinate, and the comparison of the middle terms is an
isomorphism. -/
theorem isSplitMono_secondOrderTensorComparison_of_isIso
    (hc : IsIso (ambientSchemeCrystalComparisonQ₀ M A)) :
    IsSplitMono (secondOrderTensorComparison M A) := by
  have := isIso_secondOrderTensorToAmbient M A hc
  have := isSplitMono_secondOrderThickeningTensorTopInr A.thickening.target S.S.scheme
    A.toBase.hom (Thickening.ambientSchemeModule M A)
  show IsSplitMono (secondOrderThickeningTensorTopInr A.thickening.target S.S.scheme A.toBase.hom
    (Thickening.ambientSchemeModule M A) ≫ secondOrderTensorToAmbient M A)
  infer_instance

/-- **Stacks Project, Tag 07J6: the degree-two canonical map is a split monomorphism.**  For a
sheaf crystal `F` the canonical morphism

`F_T ⊗_{𝒪_T} Ω²_{T/S,δ} ⟶ q₀_* F_{T''}`

is a split monomorphism of sheaves of `𝒪_T`-modules.  The crystal condition is the only
hypothesis, and it enters through
`Crystalline.GlobalCrystallineSituation.isIso_ambientSchemeCrystalComparisonQ₀`. -/
theorem isSplitMono_secondOrderTensorComparison (hM : IsSheafCrystal M) :
    IsSplitMono (secondOrderTensorComparison M A) :=
  isSplitMono_secondOrderTensorComparison_of_isIso M A
    (isIso_ambientSchemeCrystalComparisonQ₀ hM A)

/-- **Stacks Project, Tag 07J6: the degree-two canonical map
`F_T ⊗_{𝒪_T} Ω²_{T/S,δ} ⟶ q₀_* F_{T''}` is a monomorphism**, for a sheaf crystal `F` on the big
crystalline site and every object `(U, T, δ)` of `CRIS(X/S)`.

This is the degree-two analogue of the identification
`Crystalline.GlobalCrystallineSituation.isIso_firstOrderKernelComparison_of_isSheafCrystal`, and
it is the sense in which [Stacks, Lemma 60.15.1, Tag 07J6] reads the outcome of its integrability
computation "as a section of the subsheaf `F_T ⊗ Ω²_{T/S,δ}` of `q₂^* F`": the image of
`∇(∇(s))` under the map is zero by
`Crystalline.GlobalCrystallineSituation`
`.diffAction₂_extendedConnectionTensor_crystalConnectionTensor`,
so injectivity of the map is what turns that into `∇ ∘ ∇ = 0`.

The three steps are the inclusion of the top summand of `𝒪_{T''}` as a direct summand, the
projection formula at `q₀` ([Stacks, Tag 0FZE], in the closed-embedding form that needs no
quasi-coherence) and the crystal property at `q₀` ([Stacks, Tag 07IQ]); see the module
documentation, which also records that the global-sections form of this statement does not follow
from it.

No `@[stacks]` attribute: this is a component of the integrability clause of the tag and not the
clause. -/
theorem mono_secondOrderTensorComparison (hM : IsSheafCrystal M) :
    Mono (secondOrderTensorComparison M A) :=
  have := isSplitMono_secondOrderTensorComparison M A hM
  inferInstance

end GlobalCrystallineSituation

end Crystalline

end

end
