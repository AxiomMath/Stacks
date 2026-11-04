module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SiteCoherenceClosure
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentFiniteProduct
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteAffineProper
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealPowerModuleCoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealPowerSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SeparationAxioms
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ResolutionPropertyDescentIdealQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactEtaleLocalTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentIdealPowers
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedVariants
public import StacksFrontier.CategoryTheory.Sites.Modules.FiniteLocallyFreeBiproduct

/-!
# The source of the surjection of Stacks 0GUZ

In the situation of Stacks 0GUY — a quasi-compact and quasi-separated algebraic space `X` over a
scheme `S`, an affine surjective étale chart `φ : V → X` factored as an open immersion
`j : V → Y` followed by a finite morphism `π : Y → X`, and a finite type quasi-coherent sheaf of
ideals `ℐ ⊆ 𝒪_Y` cutting out the complement of `j(V)` — Stacks 0GUZ asserts, for `X` Noetherian,
that every coherent `𝒪_X`-module `ℱ` admits a surjection

`⨁_{i = 1}^{r} π_*(ℐ^{n_i}) ⟶ ℱ`

for some `r ≥ 0` and some integers `n_1, …, n_r ≥ 0`.

This file establishes what the **source** of that surjection is: the direct image `π_*(ℐⁿ)` of
every power of the sheaf of ideals is a coherent `𝒪_X`-module, hence so is any finite direct sum
of such direct images.  It also proves the step by which the surjection of Stacks 0GUZ is
consumed: a module surjected onto by a finite direct sum of quotients of finite locally free
modules is itself such a quotient.

The surjection itself is constructed in
`StacksFrontier/AlgebraicGeometry/Spaces/ResolutionPropertySurjection.lean`, as
`AlgebraicGeometry.Space.exists_epi_biproduct_idealSheafPowPushforward`.

## Main results

All the results about the situation live in the namespace `AlgebraicGeometry.Space` and take a
term of `AlgebraicGeometry.Space.ResolutionPropertyDescentSituation` as a parameter, that
structure having no inhabitation theorem.

* `AlgebraicGeometry.Space.hasEtaleLocalProperty_isLocallyNoetherian_of_resolutionSituation`:
  in the situation of Stacks 0GUY with `X` Noetherian, the algebraic space `Y` is locally
  Noetherian.
* `AlgebraicGeometry.Space.isFiniteType_idealSheafPow_of_resolutionSituation`: **every power
  `ℐⁿ` of the sheaf of ideals of the situation is of finite type.**
* `AlgebraicGeometry.Space.isCoherent_idealSheafPow_of_resolutionSituation`: **every power
  `ℐⁿ` is a coherent `𝒪_Y`-module**, for `X` Noetherian.
* `AlgebraicGeometry.Space.isCoherent_idealSheafPowPushforward`: **`π_*(ℐⁿ)` is a coherent
  `𝒪_X`-module.**
* `AlgebraicGeometry.Space.isCoherent_biproduct_idealSheafPowPushforward`: **the source
  `⨁_{i} π_*(ℐ^{n_i})` of the surjection of Stacks 0GUZ is a coherent `𝒪_X`-module.**
* `AlgebraicGeometry.Space.exists_isFiniteLocallyFreeOnSite_epi_of_epi_biproduct`: if each
  member of a finite family of `𝒪_X`-modules is the quotient of a finite locally free module,
  then so is every module that their direct sum surjects onto.

## Implementation notes

**Finite type of `ℐⁿ` avoids the quasi-coherence of `ℐⁿ`.**  The route to coherence does not go
through Stacks 07UB, as the one for `π_*ℐ` in
`StacksFrontier/AlgebraicGeometry/Spaces/Perfect/ResolutionPropertyDescentIdealQuotient.lean` does;
it goes through the subsheaf clause of Stacks 01BY,
`Stacks.SheafOfModules.isCoherentOnSite_of_mono`.  A power `ℐⁿ` is a subsheaf of `𝒪_Y`, which is
coherent on a locally Noetherian space by `AlgebraicGeometry.Space.isCoherent_structureSheaf`,
so only the *finite type* of `ℐⁿ` is needed — and quasi-coherence of `ℐⁿ` then *follows* from
coherence rather than being an input.  This matters: quasi-coherence of a power is exactly what
`StacksFrontier/AlgebraicGeometry/Spaces/QuasicoherentIdealPowers.lean` records as blocked, by a
mismatch between the `AlgebraicGeometry.Space.IdealSheaves` spelling of the small étale site and
the `AlgebraicGeometry.Space.structureRingSheaf` one.

**How the same mismatch is avoided for finite type.**  Finite type of a power is reached through
the site-level `Stacks.Sites.isFiniteType_idealPowSmul`, whose site and sheaf of rings are
implicit arguments inferred from the sheaf of ideals handed to it, and not through its algebraic
space specialization `AlgebraicGeometry.Space.isFiniteType_idealPowSubmodule`, which names the
site as `AlgebraicGeometry.Space.IdealSheaves` and so forces the blocked spelling.  The product
`ℐⁿ · 𝒪_Y` is then cancelled to `ℐⁿ` by `Stacks.Sites.idealSmul_top_eq`, the two powers being
identified by `AlgebraicGeometry.Space.idealSheafPow_eq_idealPow`.

**Relation to the existing `π_*ℐ`.**  At `n = 1` the module `π_*(ℐⁿ)` is `π_*ℐ`, by
`SheafOfModules.idealSheafPow_one`, and its coherence is already
`AlgebraicGeometry.Space.isCoherent_modulePushforwardIdeal`.  That lemma is *not* restated here
and is not what the results below generalize: it reaches coherence of `ℐ` from quasi-coherence
through Stacks 07UB, which no power other than the first is known to satisfy, whereas the route
below works uniformly in `n` and needs only finite type.

**The direct sum.**  Its existence is the hypothesis `[HasBiproduct …]` rather than an instance,
exactly as in `Stacks.SheafOfModules.isCoherentOnSite_biproduct` and
`AlgebraicGeometry.Space.isCoherent_biproduct`: the category of `𝒪_X`-modules is abelian with
all limits, so `CategoryTheory.Limits.HasBiproduct.of_hasProduct` produces it, but it is not
reliably synthesizable at these universes.  Coherence of the sum is
`AlgebraicGeometry.Space.isCoherent_biproduct`, and finite local freeness of a sum is
`Stacks.SheafOfModules.isFiniteLocallyFreeOnSite_biproduct`.

### Where the surjection is

The surjection of Stacks 0GUZ is
`AlgebraicGeometry.Space.exists_epi_biproduct_idealSheafPowPushforward` in
`StacksFrontier/AlgebraicGeometry/Spaces/ResolutionPropertySurjection.lean`.  The source's
`π^*ℱ ⊗ ω_{Y/X}` and trace are replaced there by the right adjoint `π^!` of `π_*`
(`AlgebraicGeometry.Space.affinePushforwardRightAdjoint`) and the counit `π_*π^!ℱ ⟶ ℱ`.

**Why the assembly step is the one Stacks 0GV0 needs.**  The converse direction of Stacks 0GV0
takes a finite locally free `ℰ` with `ℰ → π_*ℐ` surjective, propagates it to surjections
`ℰ^{⊗ n} → π_*(ℐ^n)`, and finishes with Stacks 0GUZ.  The last move is
`AlgebraicGeometry.Space.exists_isFiniteLocallyFreeOnSite_epi_of_epi_biproduct` below.  The
propagation runs through the surjections `π_*ℐ ⊗_{𝒪_X} π_*(ℐ^n) → π_*(ℐ^{n+1})`,
`AlgebraicGeometry.Space.epi_chartPowTensorHom`, and the converse of Stacks 0GV0 is
`AlgebraicGeometry.Space.hasResolutionProperty_of_exists_epi_modulePushforwardIdeal`.

## References

* [Stacks Project, Tag 0GUZ](https://stacks.math.columbia.edu/tag/0GUZ), Lemma 76.56.2 — the
  statement whose source module and assembly step are treated here.
* [Stacks Project, Tag 0GUY](https://stacks.math.columbia.edu/tag/0GUY), Situation 76.56.1.
* [Stacks Project, Tag 0GV0](https://stacks.math.columbia.edu/tag/0GV0), Lemma 76.56.3, the
  consumer of Stacks 0GUZ.
* [Stacks Project, Tag 01BY](https://stacks.math.columbia.edu/tag/01BY), the closure properties
  of coherence; clause (1) is the subsheaf clause used for `ℐⁿ`.
* [Stacks Project, Tag 07UB](https://stacks.math.columbia.edu/tag/07UB), coherence of the
  structure sheaf of a locally Noetherian algebraic space.
* [Stacks Project, Tag 07UH](https://stacks.math.columbia.edu/tag/07UH), coherence of the direct
  image along a finite morphism.
* [Stacks Project, Tag 03EA](https://stacks.math.columbia.edu/tag/03EA), Noetherian algebraic
  spaces.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hZ : B.Contains (⊤_ Scheme.{u}))

attribute [local instance] pointTopology

variable (X : AlgebraicSpaces B S hS) (hqc : IsQuasiCompactSpace B S hS X.1)
    (hqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
    (D : ResolutionPropertyDescentSituation B S hS hZ X hqc hqs)

/-! ### `Y` is locally Noetherian -/

/-- **In the situation of Stacks 0GUY with `X` Noetherian, the algebraic space `Y` is locally
Noetherian.**  The morphism `π : Y → X` is finite, hence locally of finite type, and local
Noetherianity passes to the source of a morphism locally of finite type by Stacks 04ZK. -/
theorem hasEtaleLocalProperty_isLocallyNoetherian_of_resolutionSituation
    (hX : IsNoetherian B S hS hZ X.1) :
    HasEtaleLocalProperty B S hS D.Y.1 (fun T : Scheme.{u} => IsLocallyNoetherian T) :=
  isLocallyNoetherian_of_isLocallyOfFiniteType B S hS D.Y.2 X.2 D.π
    (isLocallyOfFiniteType_of_isFinite B S hS D.Y.2 X.2 D.isFinite_π) hX.2.2

/-- **In the situation of Stacks 0GUY with `X` Noetherian, the algebraic space `Y` is
Noetherian**: the finite morphism `π` is proper (Stacks 04NZ), and Noetherianity passes to the
source of a proper morphism into a Noetherian algebraic space. -/
theorem isNoetherian_Y_of_resolutionSituation (hX : IsNoetherian B S hS hZ X.1) :
    IsNoetherian B S hS hZ D.Y.1 :=
  have hπ := ((isFinite_iff_isAffineHom_and_isProper B S hS D.Y.2 X.2 D.π).1 D.isFinite_π).2
  ⟨isQuasiCompactSpace_source_of_isQuasiCompact B S hS X.2 hX.1 hπ.2.1.2,
    isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS hZ D.Y.2 hX.2.1
      (isQuasiSeparated_of_isSeparated B S hS hπ.1),
    isLocallyNoetherian_of_isLocallyOfFiniteType B S hS D.Y.2 X.2 D.π hπ.2.1.1 hX.2.2⟩

/-! ### The powers of the sheaf of ideals are coherent -/

/-- **Every power `ℐⁿ` of the sheaf of ideals of the situation of Stacks 0GUY is of finite
type.**

The product `ℐⁿ · 𝒪_Y` of a power of a finite type sheaf of ideals with a module of finite type
is of finite type by `Stacks.Sites.isFiniteType_idealPowSmul`, and `ℐⁿ · 𝒪_Y` is `ℐⁿ` by
`Stacks.Sites.idealSmul_top_eq`.  The two constructions of the power are identified by
`AlgebraicGeometry.Space.idealSheafPow_eq_idealPow`. -/
theorem isFiniteType_idealSheafPow_of_resolutionSituation (n : ℕ) :
    PresheafOfModules.IsFiniteType (SmallEtale.topology B S hS D.Y.1)
      (SheafOfModules.idealSheafPow D.I n).toSheafOfModules.val := by
  have hI : PresheafOfModules.IsFiniteType (SmallEtale.topology B S hS D.Y.1)
      D.I.toSheafOfModules.val :=
    Stacks.SheafOfModules.presheaf_isFiniteType_of_isFiniteTypeOnSite _
      D.isFiniteTypeQuasicoherent_I.2
  have hunit : PresheafOfModules.IsFiniteType (SmallEtale.topology B S hS D.Y.1)
      (SheafOfModules.unit (structureRingSheaf B S hS D.Y)).val :=
    PresheafOfModules.isFiniteType_unit _
  have h := Stacks.Sites.isFiniteType_idealPowSmul
    (M := SheafOfModules.unit (structureRingSheaf B S hS D.Y)) D.I hI n ⊤
    (Stacks.Sites.isFiniteType_top
      (M := SheafOfModules.unit (structureRingSheaf B S hS D.Y)) hunit)
  have key : SheafOfModules.idealSheafPow D.I n =
      Stacks.Sites.idealPowSmul
        (M := SheafOfModules.unit (structureRingSheaf B S hS D.Y)) D.I n ⊤ :=
    Eq.trans (idealSheafPow_eq_idealPow B S hS D.Y D.I n)
      (Stacks.Sites.idealSmul_top_eq.{u, u + 1, u} _).symm
  rw [key]
  exact h

/-- **Every power `ℐⁿ` of the sheaf of ideals of the situation of Stacks 0GUY is a coherent
`𝒪_Y`-module**, for `X` Noetherian.

This is the subsheaf clause of Stacks 01BY: `ℐⁿ` is a subsheaf of `𝒪_Y`, which is coherent by
Stacks 07UB because `Y` is locally Noetherian, and `ℐⁿ` is of finite type by
`AlgebraicGeometry.Space.isFiniteType_idealSheafPow_of_resolutionSituation`.  Quasi-coherence of
`ℐⁿ` is a consequence, not an input. -/
theorem isCoherent_idealSheafPow_of_resolutionSituation (hX : IsNoetherian B S hS hZ X.1)
    (n : ℕ) :
    IsCoherent B S hS D.Y.1 D.Y.2 (SheafOfModules.idealSheafPow D.I n).toSheafOfModules := by
  have : Fact (HasEtaleLocalProperty B S hS D.Y.1
      (fun T : Scheme.{u} => IsLocallyNoetherian T)) :=
    ⟨hasEtaleLocalProperty_isLocallyNoetherian_of_resolutionSituation B S hS hZ X hqc hqs D hX⟩
  have hcoh : SheafOfModules.IsCoherentOnSite
      (SheafOfModules.idealSheafPow D.I n).toSheafOfModules :=
    Stacks.SheafOfModules.isCoherentOnSite_of_mono
      (SheafOfModules.idealSheafPow D.I n).ι
      (isCoherent_structureSheaf B S hS D.Y.1 D.Y.2).toIsCoherentOnSite
      (isFiniteType_idealSheafPow_of_resolutionSituation B S hS hZ X hqc hqs D n)
  exact (isCoherent_iff_isCoherentOnSite B S hS D.Y.1 D.Y.2
    (SheafOfModules.idealSheafPow D.I n).toSheafOfModules).2 hcoh

/-! ### The direct images of the powers, and their direct sums -/

/-- **`π_*(ℐⁿ)` is a coherent `𝒪_X`-module`**, in the situation of Stacks 0GUY with `X`
Noetherian.

This is the coherence clause of Stacks 07UH for the finite morphism `π`, whose input is the
coherence of `ℐⁿ` on `Y` from
`AlgebraicGeometry.Space.isCoherent_idealSheafPow_of_resolutionSituation`. -/
theorem isCoherent_idealSheafPowPushforward (hX : IsNoetherian B S hS hZ X.1) (n : ℕ) :
    IsCoherent B S hS X.1 X.2
      (idealSheafPowPushforward B S hS (D.piHom B S hS hZ X hqc hqs) D.I n) :=
  isCoherent_modulePushforward_of_isFinite' B S hS (D.piHom B S hS hZ X hqc hqs)
    D.isFinite_π hX.2.2 _
    (isCoherent_idealSheafPow_of_resolutionSituation B S hS hZ X hqc hqs D hX n)

/-- **The source `⨁_{i} π_*(ℐ^{n_i})` of the surjection of Stacks 0GUZ is a coherent
`𝒪_X`-module.**

Each summand is coherent by `AlgebraicGeometry.Space.isCoherent_idealSheafPowPushforward`, and
coherence is preserved by a finite direct sum,
`AlgebraicGeometry.Space.isCoherent_biproduct`. -/
theorem isCoherent_biproduct_idealSheafPowPushforward (hX : IsNoetherian B S hS hZ X.1)
    {r : ℕ} (n : Fin r → ℕ)
    [HasBiproduct fun i =>
      idealSheafPowPushforward B S hS (D.piHom B S hS hZ X hqc hqs) D.I (n i)] :
    IsCoherent B S hS X.1 X.2
      (⨁ fun i => idealSheafPowPushforward B S hS (D.piHom B S hS hZ X hqc hqs) D.I (n i)) :=
  isCoherent_biproduct B S hS X.1 X.2 _ fun i =>
    isCoherent_idealSheafPowPushforward B S hS hZ X hqc hqs D hX (n i)

/-! ### Consuming a surjection out of a finite direct sum -/

/-- **A module surjected onto by a finite direct sum of quotients of finite locally free modules
is itself the quotient of a finite locally free module.**

This is the step by which the surjection `⨁_i π_*(ℐ^{n_i}) → ℱ` of Stacks 0GUZ is consumed in
the proof of Stacks 0GV0.  The direct sum `⨁_i ℰ_i` of the given finite locally free modules is
finite locally free by `Stacks.SheafOfModules.isFiniteLocallyFreeOnSite_biproduct`, the induced
map `⨁_i ℰ_i → ⨁_i ℳ_i` is an epimorphism because a direct sum of epimorphisms is one
(`CategoryTheory.Limits.biproduct.map_epi`), and a composition of epimorphisms is an
epimorphism. -/
theorem exists_isFiniteLocallyFreeOnSite_epi_of_epi_biproduct {ι : Type} [Finite ι]
    (M : ι → Modules.{u, u} B S hS X.1 X.2) [HasBiproduct M]
    (hM : ∀ i, ∃ (E : Modules.{u, u} B S hS X.1 X.2)
      (_ : SheafOfModules.IsFiniteLocallyFreeOnSite E) (p : E ⟶ M i), Epi p)
    {F : Modules.{u, u} B S hS X.1 X.2} (σ : ⨁ M ⟶ F) (hσ : Epi σ) :
    ∃ (E : Modules.{u, u} B S hS X.1 X.2)
      (_ : SheafOfModules.IsFiniteLocallyFreeOnSite E) (p : E ⟶ F), Epi p := by
  choose E hE p hp using hM
  have : HasBiproduct E := HasBiproduct.of_hasProduct E
  have : ∀ i, Epi (p i) := hp
  have := hσ
  exact ⟨⨁ E, Stacks.SheafOfModules.isFiniteLocallyFreeOnSite_biproduct E hE,
    biproduct.map p ≫ σ, inferInstance⟩

/-! ### A module killed by a power of an ideal, section by section -/

/-- **A module killed by `ℐᵐ` in the sense of Stacks 07UK is killed section by section**: every
product of a section of `ℐᵐ` with a section of the module vanishes.  This is the form in which
the conclusion of Stacks 07UK
(`AlgebraicGeometry.Space.exists_idealPowSmul_eq_bot_iff_supportOfSheaf_subset_idealZeroLocus`)
is consumed by the surjectivity step of Stacks 0GUZ. -/
theorem smul_eq_zero_of_idealSmul_idealPow_top_eq_bot (Z : AlgebraicSpaces B S hS)
    (I : (SheafOfModules.unit (structureRingSheaf B S hS Z)).Submodule) (m : ℕ)
    (Q : Modules.{u, u} B S hS Z.1 Z.2)
    (h : Stacks.Sites.idealSmul (M := Q)
      (Stacks.Sites.idealPow (O := (smallEtaleRingedSite B S hS Z.1 Z.2).O) I m) ⊤ = ⊥)
    (W : (smallEtaleRingedSite B S hS Z.1 Z.2).Cᵒᵖ)
    (r : (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Z.1 Z.2).O).obj.obj W)
    (hr : r ∈ (SheafOfModules.idealSheafPow I m).obj W) (q : Q.val.obj W) : r • q = 0 := by
  rw [idealSheafPow_eq_idealPow B S hS Z I m] at hr
  have hmem := Stacks.Sites.smul_mem_idealSmul (M := Q)
    (Stacks.Sites.idealPow (O := (smallEtaleRingedSite B S hS Z.1 Z.2).O) I m)
    (N := ⊤) hr (Stacks.SheafOfModules.mem_top_obj q)
  have hz := SheafOfModules.Submodule.le_iff.1 h.le W hmem
  rw [SheafOfModules.Submodule.bot_obj] at hz
  exact (Submodule.mem_bot _).1 hz

end AlgebraicGeometry.Space

end
