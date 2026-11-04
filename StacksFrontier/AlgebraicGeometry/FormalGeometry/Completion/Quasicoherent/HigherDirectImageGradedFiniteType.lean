module

public import StacksFrontier.AlgebraicGeometry.CoherentTFAE.Basic
public import StacksFrontier.AlgebraicGeometry.FormalFunctions.ReesCohomologyFiniteReduction
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.Quasicoherent.HigherDirectImage
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.RestrictOpen
public import StacksCore.Tactic.StacksAttribute

/-!
# `⨁ₙ R ᵖ f_*(ℐⁿℱ)` is quasi-coherent and of finite type over `⨁ₙ ℐⁿ`

Let `f : X ⟶ Y` be a morphism of schemes, `ℱ` an `𝒪_X`-module and `ℐ ⊆ 𝒪_Y` a quasi-coherent
sheaf of ideals, with `Y` locally Noetherian, `f` proper and `ℱ` coherent. [Stacks, Tag 02O9]
asserts that
`ℳ = ⨁_{n ≥ 0} R ᵖ f_*(ℐⁿℱ)`
is a graded `𝒜 = ⨁_{n ≥ 0} ℐⁿ`-module which is quasi-coherent and of finite type.

Its proof in the source is two sentences: the statement is local on `Y`, so one may assume `Y`
affine, and over an affine base it is [Stacks, Tag 02O8]. This file carries out exactly that
reduction. Both clauses of the tag are proved, and both sit in the single theorem
`Stacks.Algebraization.isQuasicoherent_and_isCohomologyReesFinite_sigma_higherDirectImage`:

* **quasi-coherence** of `ℳ` and of each of its homogeneous pieces, and
* **finite type over `𝒜`**, read where the source reads it — after localizing on `Y`. Over an
  affine open `V ⊆ Y` the graded module of sections of `ℳ` is `⨁_{n ≥ 0} Hᵖ(f⁻¹(V), ℐⁿℱ)` and
  the graded ring of sections of `𝒜` is the Rees algebra `⨁_{n ≥ 0} ℐ(V)ⁿ`; the clause says
  that the former is a finite module over the latter, for every affine open `V` of `Y`. That is
  `Stacks.Cohomology.FormalFunctions.IsCohomologyReesFinite`, the conclusion of
  [Stacks, Tag 02O8], at the restricted situation `f⁻¹(V) ⟶ V ≅ Spec Γ(Y, V)`.

## Main definitions

* `Stacks.Algebraization.affineBaseChart`: the restriction `f⁻¹(V) ⟶ V` of `f` over an affine
  open `V` of `Y`, read through `V ≅ Spec Γ(Y, V)` as a scheme over `Spec Γ(Y, V)`. This is the
  shape [Stacks, Tag 02O8] is stated in: a scheme over the spectrum of a Noetherian ring.
* `Stacks.Algebraization.affineBaseChartModule`: the restriction of `ℱ` to `f⁻¹(V)`.

## Main results

* `Stacks.Algebraization.isCohomologyReesFinite_affineBaseChart`: [Stacks, Tag 02O8] applied on
  an affine chart of the base. All three of its inputs are local: `Γ(Y, V)` is Noetherian
  because `Y` is locally Noetherian, `f⁻¹(V) ⟶ Spec Γ(Y, V)` is proper because `f ∣_ V` is and
  `V ≅ Spec Γ(Y, V)`, and `ℱ|_{f⁻¹(V)}` is coherent because `X` is locally Noetherian — which
  it is, `f` being locally of finite type.
* `Stacks.Algebraization.isQuasicoherent_and_isCohomologyReesFinite_sigma_higherDirectImage`:
  both clauses of [Stacks, Tag 02O9], at the source's hypotheses and at no others. No Stacks
  attribute for Tag 02O9 is carried here: the finite-type clause is read after localizing on `Y`,
  as the source's proof reads it, and not as
  `SheafOfModules.GradedModule.IsFiniteType` of a graded `⨁ₙ ℐⁿ`-module on `Y`, which is the
  shape the tag's own words ask for. **That shape is now proved** — of the graded module
  `Stacks.Blowup.pushforwardReesGradedModulePlus`, in
  `Stacks.Algebraization.isQuasicoherent_and_isFiniteType_pushforwardReesGradedModulePlus`,
  which is where the tag is registered; see the implementation notes for how the two readings
  of the finiteness clause are related.

## Implementation notes

The hypotheses are exactly the source's: `IsLocallyNoetherian Y`, `IsProper f`, `ℱ` coherent.
Quasi-compactness and quasi-separatedness of `f`, local Noetherianness of `X` and
quasi-coherence of `ℱ` are all consequences and are derived, not assumed.

**Why the finite-type clause is stated here after localizing on `Y`, and where the sheaf-level
reading lives.** The graded `𝒜`-module structure on `⨁ₙ R ᵖ f_*(ℐⁿℱ)` as a sheaf on `Y` — the
maps `ℐⁱ ⊗ R ᵖ f_*(ℐⁿℱ) ⟶ R ᵖ f_*(ℐⁿ⁺ⁱℱ)` that the setup paragraph of [Stacks, Tag 02O7]
obtains by "localizing and then sheafifying" — is
`Stacks.Blowup.pushforwardReesGradedModulePlus`, and
`SheafOfModules.GradedModule.IsFiniteType` of it is
`Stacks.Algebraization.isQuasicoherent_and_isFiniteType_pushforwardReesGradedModulePlus`. The
statement proved here is the affine-local *input* to that one, not a weaker substitute for it:
the translation produces, over each affine open `V` of `Y`, finitely many *homogeneous* sections
whose `𝒜`-combinations exhaust every homogeneous section locally, out of
`Stacks.Cohomology.FormalFunctions.IsCohomologyReesFinite`, which unfolds to
`Module.Finite (⨁ₙ Stacks.Blowup.reesGrading ℐ(V) n) (⨁ₙ Hᵖ(f⁻¹(V), ℐ(V)ⁿ ℱ))` — so the
generation step is semilinear over `Stacks.Blowup.reesGrading`, the *ring* Rees algebra, and not
over `Stacks.Blowup.reesPiece`. The comparison between the two sides is
`Stacks.Algebraization.chartSections`, which is onto, additive and semilinear and deliberately
*not* `Γ(Y, V)`-linear; the spanning family the affine criterion wants is assembled from it in
the sibling module `HigherDirectImageFiniteTypeSpan`.

The nested-open compatibility of [Stacks, Tag 01E5] is **not** needed:
`pushforwardReesGradedModulePlus` reads the action through the extension
`𝒢 ↦ (j_{f⁻¹V})_*(𝒢|_{f⁻¹V})`, which turns a section of `ℐⁱ` over a proper open `V ⊆ Y` into a
morphism of sheaves on all of `X`, and compares two opens by
`Stacks.AlgebraicGeometry.SchemeHigherDirectImage.extendRestrictLE`, again a morphism of sheaves
on `X`.

The affine-local reading used here is the source's own: "the statement is local on `Y`, hence
this reduces to the case where `Y` is affine. In the affine case the result follows from
Lemma 30.20.1" — Lemma 30.20.1 being [Stacks, Tag 02O8].

`Stacks.Cohomology.FormalFunctions.IsCohomologyReesFinite ℐ(V) X' ℱ' p` unfolds to
`Module.Finite (⨁ₙ Stacks.Blowup.reesGrading ℐ(V) n) (⨁ₙ Hᵖ(f⁻¹(V), ℐ(V)ⁿ ℱ'))`, the acting
ring being the Rees algebra of `ℐ(V)` — Mathlib's `reesAlgebra`, graded, which is
`Γ(V, 𝒜)` — and the `ℐⁿℱ` in each summand being the ideal-power subsheaf
`Stacks.AlgebraicGeometry.IdealPower.idealPowerMultiple` for the ideal sheaf `ℐ(V) · 𝒪_{f⁻¹V}`
on the chart. That is the same construction as the `Stacks.Algebraization.idealPowerMultiple`
of the quasi-coherence clause — the two definitions are literally the same infimum, duplicated
in the tree.

`HasDerivedCategory.standard` is installed at a raised priority because the imports bring a
second `HasDerivedCategory` instance into scope, at a smaller universe, and the quasi-coherence
clause has to be stated at the same instance as
`Stacks.Algebraization.isQuasicoherent_sigma_higherDirectImage_idealPowerMultiple`.

## References

* [Stacks Project, Tag 02O9](https://stacks.math.columbia.edu/tag/02O9)
* [Stacks Project, Tag 02O8](https://stacks.math.columbia.edu/tag/02O8)
* [Stacks Project, Tag 02O7](https://stacks.math.columbia.edu/tag/02O7)
* [Stacks Project, Tag 01E5](https://stacks.math.columbia.edu/tag/01E5)
* [Stacks Project, Tag 01XJ](https://stacks.math.columbia.edu/tag/01XJ)
* [Stacks Project, Tag 01T6](https://stacks.math.columbia.edu/tag/01T6)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.FormalFunctions

universe u

attribute [local instance 100000] HasDerivedCategory.standard

namespace Stacks.Algebraization

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (F : X.Modules)

/-! ### The affine charts of the base -/

/-- The restriction `f⁻¹(V) ⟶ V` of `f` over an affine open `V` of `Y`, read through
`V ≅ Spec Γ(Y, V)` as a scheme over `Spec Γ(Y, V)`.

This is the shape in which [Stacks, Tag 02O8] is stated: a scheme over the spectrum of a ring,
the ring carrying the ideal. -/
public def affineBaseChart (V : Y.affineOpens) : Over (Spec (.of ↥Γ(Y, V.1))) :=
  Over.mk ((f ∣_ V.1) ≫ V.2.isoSpec.hom)

/-- The scheme underlying the chart over an affine open `V` of `Y` is `f⁻¹(V)`. -/
public theorem affineBaseChart_left (V : Y.affineOpens) :
    (affineBaseChart f V).left = (f ⁻¹ᵁ V.1).toScheme := rfl

/-- The restriction of `ℱ` to `f⁻¹(V)`, the coherent module on the chart. -/
public def affineBaseChartModule (V : Y.affineOpens) : (affineBaseChart f V).left.Modules :=
  (Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V.1).ι).obj F

/-- The structure morphism of the chart is proper when `f` is: it is `f ∣_ V` followed by the
isomorphism `V ≅ Spec Γ(Y, V)`, and properness is preserved by both. -/
public instance isProper_affineBaseChart_hom [IsProper f] (V : Y.affineOpens) :
    IsProper (affineBaseChart f V).hom :=
  MorphismProperty.RespectsIso.postcomp (P := @IsProper) V.2.isoSpec.hom (f ∣_ V.1) inferInstance

/-- The restriction of a coherent module to the chart is coherent. The ambient local
Noetherianness is the hypothesis of `isCoherent_restrict_of_isOpenImmersion`; for a proper `f`
it follows from that of `Y`. -/
public instance isCoherent_affineBaseChartModule [IsLocallyNoetherian X] [F.IsCoherent]
    (V : Y.affineOpens) : (affineBaseChartModule f F V).IsCoherent :=
  isCoherent_restrict_of_isOpenImmersion (f ⁻¹ᵁ V.1).ι F

/-- The ring of functions on an affine open of a locally Noetherian scheme is Noetherian; this
is the Noetherian hypothesis of [Stacks, Tag 02O8] on a chart. -/
public instance isNoetherianRing_sections_affineOpens [IsLocallyNoetherian Y]
    (V : Y.affineOpens) : IsNoetherianRing ↥Γ(Y, V.1) :=
  IsLocallyNoetherian.component_noetherian V

/-! ### [Stacks, Tag 02O8] on a chart -/

/-- **[Stacks, Tag 02O8] on an affine chart of the base.** For `Y` locally Noetherian, `f`
proper and `ℱ` coherent, and for every affine open `V` of `Y`, the graded module
`⨁_{n ≥ 0} Hᵖ(f⁻¹(V), ℐ(V)ⁿ ℱ)` is a finite module over the Rees algebra
`⨁_{n ≥ 0} ℐ(V)ⁿ = Γ(V, 𝒜)`.

Every hypothesis of the tag is local: `Γ(Y, V)` is Noetherian, `f⁻¹(V) ⟶ Spec Γ(Y, V)` is
proper, and the restriction of `ℱ` is coherent because `X` is locally Noetherian — which it is,
a proper morphism being locally of finite type ([Stacks, Tag 01T6]). -/
@[ega "III 2.4.2" "special case"]
public theorem isCohomologyReesFinite_affineBaseChart [IsLocallyNoetherian Y] [IsProper f]
    [F.IsCoherent] (I : Y.IdealSheafData) (p : ℕ) (V : Y.affineOpens) :
    IsCohomologyReesFinite (I.ideal V) (affineBaseChart f V)
      (affineBaseChartModule f F V) p :=
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  isCohomologyReesFinite (I.ideal V) (affineBaseChart f V) (affineBaseChartModule f F V) p
    inferInstance

/-! ### [Stacks, Tag 02O9] -/

/-- **[Stacks, Tag 02O9], in the affine-local reading of the source's own proof.** Let
`f : X ⟶ Y` be a morphism of schemes, `ℱ` an `𝒪_X`-module and
`ℐ ⊆ 𝒪_Y` a quasi-coherent sheaf of ideals. Assume `Y` locally Noetherian, `f` proper and `ℱ`
coherent. Then
`ℳ = ⨁_{n ≥ 0} R ᵖ f_*(ℐⁿℱ)`
is a graded `𝒜 = ⨁_{n ≥ 0} ℐⁿ`-module which is **quasi-coherent** — each homogeneous piece is,
and so is the direct sum — and **of finite type over `𝒜`**: over every affine open `V` of `Y`
the graded module of sections `⨁_{n ≥ 0} Hᵖ(f⁻¹(V), ℐⁿℱ)` of `ℳ` is a finite module over the
graded ring of sections `⨁_{n ≥ 0} ℐ(V)ⁿ` of `𝒜`.

This is the source's own argument: quasi-coherence is [Stacks, Tag 01XJ] applied to each
`ℐⁿℱ`, which is quasi-coherent, together with the stability of quasi-coherence under
colimits; and the finiteness clause is local on `Y`, hence is [Stacks, Tag 02O8] on each affine
chart of `Y`. See the implementation notes of this file for why the finite-type clause is read
here after localizing on `Y`, as the source reads it; the tag itself is registered on
`Stacks.Algebraization.isQuasicoherent_and_isFiniteType_pushforwardReesGradedModulePlus`, which
states the finiteness as `SheafOfModules.GradedModule.IsFiniteType` of the graded
`⨁ₙ ℐⁿ`-module on `Y` and takes this statement as its affine-local input. -/
@[ega "III 2.4.2" "special case",
  ega "III 3.3.1" "special case",
  ega "III 3.3.2" "more general",
  sga "2 XII 5.8" "(ii), special case"]
public theorem isQuasicoherent_and_isCohomologyReesFinite_sigma_higherDirectImage
    [IsLocallyNoetherian Y] [IsProper f] [F.IsCoherent] (I : Y.IdealSheafData) (p : ℕ) :
    ((∀ n : ℕ, (((Scheme.Modules.pushforward f).rightDerivedPlus (p : ℤ)).obj
        (idealPowerMultiple (I.comap f) n F).toSheafOfModules).IsQuasicoherent) ∧
      (∐ fun n : ℕ ↦ ((Scheme.Modules.pushforward f).rightDerivedPlus (p : ℤ)).obj
        (idealPowerMultiple (I.comap f) n F).toSheafOfModules).IsQuasicoherent) ∧
      ∀ V : Y.affineOpens,
        IsCohomologyReesFinite (I.ideal V) (affineBaseChart f V)
          (affineBaseChartModule f F V) p := by
  obtain ⟨hqc, -⟩ :=
    Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent F
  have := hqc
  exact ⟨⟨fun n ↦ isQuasicoherent_higherDirectImage_idealPowerMultiple f F I n (p : ℤ),
      isQuasicoherent_sigma_higherDirectImage_idealPowerMultiple f F I (p : ℤ)⟩,
    isCohomologyReesFinite_affineBaseChart f F I p⟩

end Stacks.Algebraization

end

end
