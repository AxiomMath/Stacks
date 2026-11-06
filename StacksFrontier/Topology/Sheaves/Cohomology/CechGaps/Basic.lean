module

public import StacksFrontier.Topology.Sheaves.Cohomology.CechGaps.ShortExact
public import StacksFrontier.AlgebraicGeometry.SectionsExact.Discharge
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Vanishing of higher cohomology from Čech acyclicity of injectives

Let `Bas` be a set of opens of `X` and `Cov` a set of open coverings whose Čech intersections lie
in `Bas`. Suppose that injective `𝒪_X`-modules are Čech acyclic for `Cov`
(`CechAcyclicInjectives`), and that in every short exact sequence of `𝒪_X`-modules whose first
term is Čech acyclic for `Cov` the last map is surjective on sections over every open in `Bas`.
Then `Hⁿ(U, F) = 0` for every `U ∈ Bas`, every `n > 0` and every `𝒪_X`-module `F` that is Čech
acyclic for `Cov`.

## Main results

* `Stacks.CechGaps.shortExact_map_cechFunctor`: the Čech complexes of a short exact sequence of
  `𝒪_X`-modules form a short exact sequence of cochain complexes as soon as the last map is
  surjective on sections over the opens of the covering.
* `Stacks.CechGaps.hasVanishingHigherCech_X₃_of_basis`: Čech acyclicity passes to the quotient,
  given surjectivity on sections over `Bas`.
* `Stacks.CechGaps.cechDevissageStep_of'`: the dévissage step, under the two hypotheses above.
* `Stacks.CechGaps.higherCohomology_isZero_of_01EP_01EU`: the vanishing of `Hⁿ(U, F)` stated
  above.

## References

* [Stacks Project, Tag 01EW](https://stacks.math.columbia.edu/tag/01EW)
* [Stacks Project, Tag 01EV](https://stacks.math.columbia.edu/tag/01EV)
* [Stacks Project, Tag 01EU](https://stacks.math.columbia.edu/tag/01EU)
* [Stacks Project, Tag 01EP](https://stacks.math.columbia.edu/tag/01EP)
* [Stacks Project, Tag 01EM](https://stacks.math.columbia.edu/tag/01EM)
* [Stacks Project, Tag 01EL](https://stacks.math.columbia.edu/tag/01EL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.CohomologyVanishing

universe u u₂

namespace Stacks.CechGaps

variable {X : Type u} [TopologicalSpace X]
  (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u₂})

/-- The underlying presheaf of abelian groups of a sheaf of `𝒪_X`-modules. -/
noncomputable abbrev presheafOf : SheafOfModules.{u} R ⥤ ((Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) :=
  SheafOfModules.toSheaf R ⋙ sheafToPresheaf _ _

/-- The Čech complex of a sheaf of modules is the Čech complex of its underlying presheaf. -/
lemma cechFunctor_eq (V : OpenCover X) :
    cechFunctor.{u, u} R V = presheafOf R ⋙ cechComplexFunctor V.obj := rfl

/-- Sections over `W` are evaluation of the underlying presheaf at `W`. -/
lemma secF_eq (W : Opens X) :
    presheafOf R ⋙ (evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op W) = secF R W := rfl

/-- `cechFunctor R V` is an additive functor. -/
instance cechFunctorAdditive (V : OpenCover X) : (cechFunctor.{u, u} R V).Additive := by
  unfold cechFunctor
  infer_instance

/-- The Čech complexes of a short exact sequence of `𝒪_X`-modules form a short exact sequence of
cochain complexes, as soon as the last map is surjective on sections over every open occurring in
the Čech complexes of the covering. -/
@[ega "III 1.2.5" "partial"]
theorem shortExact_map_cechFunctor (V : OpenCover X) (S : ShortComplex (SheafOfModules.{u} R))
    (hS : S.ShortExact)
    (hepi : ∀ (p : ℕ) (x : Fin (p + 1) → V.ι), Epi ((secF R (∏ᶜ (V.obj ∘ x))).map S.g)) :
    (S.map (cechFunctor R V)).ShortExact :=
  shortExact_map_cechComplexFunctor V.obj (S.map (presheafOf R))
    (fun p x ↦ shortExact_map_secF R S hS _ (hepi p x))

/-- Every open occurring in the Čech complex of a covering whose Čech intersections lie in `Bas`
lies in `Bas`. -/
lemma prodOpens_mem {Bas : Set (Opens X)} (V : OpenCover X)
    (hCovBas : ∀ (p : ℕ) (x : Fin (p + 1) → V.ι), (⨅ k, V.obj (x k)) ∈ Bas)
    (p : ℕ) (x : Fin (p + 1) → V.ι) : (∏ᶜ (V.obj ∘ x) : Opens X) ∈ Bas := by
  rw [prodOpens_eq_iInf]
  exact hCovBas p x

/-- If the Čech complexes of a short exact sequence `S` of `𝒪_X`-modules form a short exact
sequence for every covering in `Cov`, and `S.X₁` and `S.X₂` are Čech acyclic for `Cov`, then so is
`S.X₃`. -/
theorem hasVanishingHigherCech_X₃' {Cov : Set (OpenCover X)}
    (S : ShortComplex (SheafOfModules.{u} R))
    (hSE : ∀ V ∈ Cov, (S.map (cechFunctor R V)).ShortExact)
    (h₁ : HasVanishingHigherCech R Cov S.X₁) (h₂ : HasVanishingHigherCech R Cov S.X₂) :
    HasVanishingHigherCech R Cov S.X₃ := fun V hV p hp ↦
  isZero_homology_X₃_of_shortExact (hSE V hV) (fun q hq ↦ h₁ V hV q hq)
    (fun q hq ↦ h₂ V hV q hq) p hp

/-- The Čech complexes of a short exact sequence form a short exact sequence of cochain complexes
for every covering in `Cov`, once the last map is surjective on sections over `Bas` and the Čech
intersections of the coverings in `Cov` lie in `Bas`. -/
@[ega "III 1.2.5" "partial"]
theorem shortExact_map_cechFunctor_of_basis {Bas : Set (Opens X)} {Cov : Set (OpenCover X)}
    (hCovBas : ∀ V ∈ Cov, ∀ (p : ℕ) (x : Fin (p + 1) → V.ι), (⨅ k, V.obj (x k)) ∈ Bas)
    (S : ShortComplex (SheafOfModules.{u} R)) (hS : S.ShortExact)
    (hepiBas : ∀ W ∈ Bas, Epi ((secF R W).map S.g)) :
    ∀ V ∈ Cov, (S.map (cechFunctor R V)).ShortExact :=
  fun V hV ↦ shortExact_map_cechFunctor R V S hS
      fun p x ↦ hepiBas _ (prodOpens_mem V (hCovBas V hV) p x)

/-- Let the Čech intersections of the coverings in `Cov` lie in `Bas`, and let `S` be a short
exact sequence of `𝒪_X`-modules whose last map is surjective on sections over `Bas`. If `S.X₁` and
`S.X₂` are Čech acyclic for `Cov`, then so is `S.X₃`. -/
theorem hasVanishingHigherCech_X₃_of_basis {Bas : Set (Opens X)} {Cov : Set (OpenCover X)}
    (hCovBas : ∀ V ∈ Cov, ∀ (p : ℕ) (x : Fin (p + 1) → V.ι), (⨅ k, V.obj (x k)) ∈ Bas)
    (S : ShortComplex (SheafOfModules.{u} R)) (hS : S.ShortExact)
    (hepiBas : ∀ W ∈ Bas, Epi ((secF R W).map S.g))
    (h₁ : HasVanishingHigherCech R Cov S.X₁) (h₂ : HasVanishingHigherCech R Cov S.X₂) :
    HasVanishingHigherCech R Cov S.X₃ :=
  hasVanishingHigherCech_X₃' R S (shortExact_map_cechFunctor_of_basis R hCovBas S hS hepiBas) h₁ h₂

/-- A short exact sequence `0 → G → I → Q → 0` of `𝒪_X`-modules with `I` injective, last map
surjective on sections over `Bas`, and `G` and `I` Čech acyclic for `Cov`, gives a short exact
sequence with first term `G`, injective middle term, last map surjective on sections over `Bas`,
and last term Čech acyclic for `Cov`. -/
theorem exists_cechDevissage {Bas : Set (Opens X)} {Cov : Set (OpenCover X)}
    (hCovBas : ∀ V ∈ Cov, ∀ (p : ℕ) (x : Fin (p + 1) → V.ι), (⨅ k, V.obj (x k)) ∈ Bas)
    (G : SheafOfModules.{u} R) (S : ShortComplex (SheafOfModules.{u} R)) (hS : S.ShortExact)
    (hX₁ : S.X₁ = G) (hI : Injective S.X₂)
    (hepi : ∀ W ∈ Bas, Epi ((secF R W).map S.g))
    (h₁ : HasVanishingHigherCech R Cov S.X₁) (h₂ : HasVanishingHigherCech R Cov S.X₂) :
    ∃ S' : ShortComplex (SheafOfModules.{u} R), S'.ShortExact ∧ S'.X₁ = G ∧ Injective S'.X₂ ∧
      (∀ V ∈ Bas, Epi ((secF R V).map S'.g)) ∧ HasVanishingHigherCech R Cov S'.X₃ :=
  ⟨S, hS, hX₁, hI, hepi, hasVanishingHigherCech_X₃_of_basis R hCovBas S hS hepi h₁ h₂⟩

variable [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [EnoughInjectives (SheafOfModules.{u} R)]

/-- The dévissage step `CechDevissageStep R Bas Cov G` holds, given that injective modules are
Čech acyclic for `Cov`, that in every short exact sequence with Čech acyclic first term the last
map is surjective on sections over `Bas`, and that the Čech intersections of the coverings in `Cov`
lie in `Bas`. -/
theorem cechDevissageStep_of' {Bas : Set (Opens X)} {Cov : Set (OpenCover X)}
    (hinj : CechAcyclicInjectives.{u, u, u₂} R Cov)
    (h01EU : ∀ S : ShortComplex (SheafOfModules.{u} R), S.ShortExact →
      HasVanishingHigherCech R Cov S.X₁ → ∀ W ∈ Bas, Epi ((secF R W).map S.g))
    (hCovBas : ∀ V ∈ Cov, ∀ (p : ℕ) (x : Fin (p + 1) → V.ι), (⨅ k, V.obj (x k)) ∈ Bas)
    (G : SheafOfModules.{u} R) : CechDevissageStep R Bas Cov G := by
  intro hG
  have hSX : (ShortComplex.mk (Injective.ι G) (cokernel.π (Injective.ι G))
      (cokernel.condition _)).ShortExact :=
    ShortComplex.ShortExact.mk'
      (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel (Injective.ι G)))
      (Injective.ι_mono G) inferInstance
  exact exists_cechDevissage R hCovBas G _ hSX rfl (Injective.injective_under G)
    (h01EU _ hSX hG) hG (hinj _ (Injective.injective_under G))

variable [HasDerivedCategory (SheafOfModules.{u} R)] [HasDerivedCategory AddCommGrpCat.{u}]

/-- Under the hypotheses of `cechDevissageStep_of'`, `Hⁿ(U, F) = 0` for every `U ∈ Bas`, every
`n > 0` and every `𝒪_X`-module `F` that is Čech acyclic for `Cov`. -/
theorem higherCohomology_isZero_of_01EP_01EU {Bas : Set (Opens X)} {Cov : Set (OpenCover X)}
    {U : Opens X} (hinj : CechAcyclicInjectives.{u, u, u₂} R Cov)
    (h01EU : ∀ S : ShortComplex (SheafOfModules.{u} R), S.ShortExact →
      HasVanishingHigherCech R Cov S.X₁ → ∀ W ∈ Bas, Epi ((secF R W).map S.g))
    (hCovBas : ∀ V ∈ Cov, ∀ (p : ℕ) (x : Fin (p + 1) → V.ι), (⨅ k, V.obj (x k)) ∈ Bas)
    (hU : U ∈ Bas) (F : SheafOfModules.{u} R) (hF : HasVanishingHigherCech R Cov F)
    (n : ℕ) (hn : 0 < n) : IsZero (Hgroup R U n F) :=
  higherCohomology_isZero_of_cechDevissage R (isCohomologyDeltaFunctor_rightDerived R U)
    (cechDevissageStep_of' R hinj h01EU hCovBas) hU F hF n hn

end Stacks.CechGaps
