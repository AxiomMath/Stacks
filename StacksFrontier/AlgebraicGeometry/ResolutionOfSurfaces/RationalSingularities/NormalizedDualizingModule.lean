module

public import StacksFrontier.Algebra.Homology.StrictlyPerfectRestriction
public import StacksFrontier.AlgebraicGeometry.Cohomology.LocallyNoetherian.Coherent
public import
  StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.DualizingPullback
public import
  StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.ExceptionalIdealPowers
import StacksCore.Tactic.StacksAttribute

/-!
# The dualizing module normalized relative to a dualizing module of the base

In Situation [Stacks, Tag 0B4W] — a two-dimensional local normal Nagata domain `A` defining a
rational singularity and a modification `f : X ⟶ Spec(A)` with `X` normal — a dualizing module
`ω_X` on `X` is only determined up to tensoring with an invertible module: being a dualizing
complex is a local condition, and an invertible twist of a dualizing complex is a dualizing
complex again ([Stacks, Tag 0A7F] read backwards). The source works with *the* dualizing module
of `X`, the one [Stacks, Remark 0B4R] fixes by asking that `ω_X[2]` be the dualizing complex
normalized relative to `ω_A[2]`, that is, `ω_X[2] = f^!(ω_A[2])`.

This file states that normalization as a condition on an `ω_X` already given, and proves that it
determines `ω_X` up to a unique isomorphism compatible with the traces.

## What the condition says

Writing `ω_X[2] = f^!(ω_A[2])` and shifting, Grothendieck duality for the proper morphism `f`
reads
`Hom_{𝒪_X}(ℱ, ω_X) = Hom_{D(A)}(Rf_*ℱ, ω_A)`
for `ℱ` quasi-coherent, and the isomorphism is "apply `Rf_*` and compose with the trace".
The fibres of `f` have dimension at most one, so `R^if_*ℱ = 0` for `i ≥ 2`; hence whenever
`H¹(X, ℱ) = 0` the complex `Rf_*ℱ` is the module `H⁰(X, ℱ)` in degree zero and the right-hand
side is `Hom_A(H⁰(X, ℱ), ω_A)`. That special case of the duality isomorphism mentions no derived
category, no shift and no `f^!`, and it is what
`AlgebraicGeometry.RationalSingularitySituation.NormalizedDualizingModule` records: a trace map
`t : H⁰(X, ω_X) ⟶ ω_A` for which

`Hom_{𝒪_X}(ℱ, ω_X) ⟶ Hom_A(H⁰(X, ℱ), ω_A)`, `φ ↦ t ∘ H⁰(φ)`

is bijective for every quasi-coherent `ℱ` with `H¹(X, ℱ) = 0`.

## Main definitions

* `AlgebraicGeometry.RationalSingularitySituation.tracePairing`: the map
  `φ ↦ t ∘ H⁰(φ)` above.
* `AlgebraicGeometry.RationalSingularitySituation.NormalizedDualizingModule`: the normalization
  condition, with its trace.
* `AlgebraicGeometry.RationalSingularitySituation.normalizedDualizingIso`: the canonical
  comparison isomorphism between two normalized dualizing modules.
* `AlgebraicGeometry.RationalSingularitySituation.structureRingEquiv`: `A ≅ Γ(X, 𝒪_X)`, the
  ring isomorphism of [Stacks, Tag 0B4Y].
* `AlgebraicGeometry.RationalSingularitySituation.unitSectionHom` and
  `.unitGlobalSectionsHomEquiv`: the two identifications `Hom_{𝒪_X}(𝒪_X, ℱ) = H⁰(X, ℱ)` and
  `Hom_A(H⁰(X, 𝒪_X), N) = N`.

## Main results

* `AlgebraicGeometry.RationalSingularitySituation.bijective_trace_of_normalized`:
  **[Stacks, Tag 0BBU]** for a normalized `ω_X`. The condition at `ℱ = 𝒪_X` is exactly the
  assertion that the trace is bijective, because `H¹(X, 𝒪_X) = 0` and `Γ(X, 𝒪_X) = A`.
* `AlgebraicGeometry.RationalSingularitySituation.dualizingTraceSequenceOfNormalized`: the datum
  `AlgebraicGeometry.RationalSingularitySituation.DualizingTraceSequence` of
  [Stacks, Tag 0BBU], built from the normalization.
* `AlgebraicGeometry.RationalSingularitySituation.existsUnique_hom_of_normalized` and
  `.normalizedDualizingIso`: a normalized dualizing module is unique up to a unique
  trace-compatible isomorphism.

## Implementation notes

**Why `H⁰(X, ω_X) ≅ ω_A` is not the normalization.** The isomorphism `H⁰(X, ω_X) ≅ ω_A` does not
pin `ω_X` down inside its orbit under the invertible modules. On the blowup `X` of `Spec(A)` in
the maximal ideal, with `E` the exceptional divisor and `ω_X` normalized, every `ω_X(nE)` has
`Γ(X, ω_X(nE)) ⊆ Γ(X ∖ E, ω_X) = ω_A`, with equality for all large `n` because `ω_A` is finitely
generated; so infinitely many members of the orbit have global sections `ω_A`. What the
condition below adds is the *universal property* of the trace, and that is what makes the
comparison isomorphism of `normalizedDualizingIso` canonical rather than merely existent.

**The universal property does not pin `ω_X` down either.** Take `A = ℚ[x, y, z]/(xz − y²)`
localized at `(x, y, z)`: a normal Nagata domain of dimension two, not regular, defining a
rational singularity, Gorenstein with `ω_A = A`. Let `X` be its blowup at the maximal ideal,
which is the minimal resolution: `X` is regular, `E ≅ ℙ¹_ℚ` with `𝒪_E(1) = 𝒪_{ℙ¹}(2)`, the
normal sheaf `𝒪_E(E)` is `𝒪_E(-1) = 𝒪_{ℙ¹}(-2)`, and `ω_X = 𝒪_X` is the normalized dualizing
module, the singularity being canonical. Then **`𝒪_X(E)` is normalized too**, with the same
trace, although `𝒪_X(E) ≇ 𝒪_X`.

Writing `ℐ_E = 𝒪_X(1)`, so that `𝒪_X(E)` is `𝒪_X(-1)`, here is why. The trace is unchanged:
`Γ(X, 𝒪_X(E)) ⊆ Γ(X ∖ E, 𝒪_X) = Γ(Spec(A) ∖ {𝔪}, 𝒪) = A` because `A` is normal of dimension
two, hence of depth two, and `A = Γ(X, 𝒪_X) ⊆ Γ(X, 𝒪_X(E))`, so both are `A = ω_A` and the
inclusion `𝒪_X ⊆ 𝒪_X(E)` is the identity on global sections. And the pairing is unchanged,
because `Hom(ℱ, 𝒪_X) ⟶ Hom(ℱ, 𝒪_X(E))` is bijective for every quasi-coherent `ℱ` with
`H¹(X, ℱ) = 0`: it is injective because `Hom(ℱ, -)` is left exact, and for surjectivity let
`φ : ℱ ⟶ 𝒪_X(E)` and let `ψ` be its composite with `𝒪_X(E) ↠ i_*𝒪_{ℙ¹}(-2)`. Were `ψ` nonzero,
its image would be `i_*𝒬` for a nonzero subsheaf `𝒬 ⊆ 𝒪_{ℙ¹}(-2)` — a submodule of `i_*` of
something is killed by `ℐ_E` — hence `𝒬 ≅ 𝒪_{ℙ¹}(-2 - d)` for some `d ≥ 0`, whose
`H¹(ℙ¹, -)` has dimension `d + 1`. But `ℱ ↠ i_*𝒬` and `H²(X, -)` vanishes on quasi-coherent
modules, the fibres of `f` having dimension at most one over the affine base
([Stacks, Tag 0E7D]), so `H¹(X, ℱ) ↠ H¹(X, i_*𝒬) = H¹(ℙ¹, 𝒬) ≠ 0` — contradicting
`H¹(X, ℱ) = 0`. So `ψ = 0`, `φ` factors through `𝒪_X`, and the two duality pairings agree under
the bijection.

The consequences are recorded where they bite.

* **Clause (2) of [Stacks, Tag 0B64] does not follow from the normalization**, and neither does
  the curve vanishing `H¹(E, (ω_X|_E)(n)) = 0` it rests on, nor the global generation of
  `ω_X|_E` of [Stacks, Tag 0B5H], nor `dim_κ H¹(E, ω_E) = 1`. For the normalized `𝒪_X(E)` above,
  `0 ⟶ 𝒪_X ⟶ 𝒪_X(E) ⟶ i_*𝒪_{ℙ¹}(-2) ⟶ 0` gives `H¹(X, 𝒪_X(E)) ≅ H¹(ℙ¹, 𝒪(-2)) = ℚ`, because
  `H⁰(ℙ¹, 𝒪(-2)) = 0` and `H¹(X, 𝒪_X) = H²(X, 𝒪_X) = 0`; so clause (2) at `n = 0` fails for it.
  Its restriction `𝒪_X(E)|_E = 𝒪_{ℙ¹}(-2)` is not generated by its global sections, and clause
  (1) attaches to it `ω_E = 𝒪_{ℙ¹}(-2) ⊗ 𝒪_E(-1) = 𝒪_{ℙ¹}(-4)` with
  `dim_ℚ H¹(E, ω_E) = 3`.
* **Clause (3) of [Stacks, Tag 0B64] does not follow from the normalization either.** For the
  normalized `𝒪_X(E)` above the trace is the identity on `Γ(X, 𝒪_X(E)) = A = ω_A`, so the
  canonical map of [Stacks, Tag 0BBU] is the inclusion `𝒪_X ⟶ 𝒪_X(E)`, whose cokernel is
  `i_*𝒪_{ℙ¹}(-2) ≠ 0`; it is not surjective. That is why
  `AlgebraicGeometry.BlowUpDualizing.epi_dualizingPullbackMap_of_normalized` carries the global
  generation of `ω_X|_E`, and `AlgebraicGeometry.BlowUpDualizing`
  `.nonempty_generatingSections_restriction_iff_epi` shows that hypothesis to be equivalent to
  the clause's own conclusion.
* **The uniqueness below is not affected**, because `existsUnique_hom_of_normalized` and
  `normalizedDualizingIso` ask for the vanishing of the first cohomology of the modules they
  compare, and that is exactly what excludes `𝒪_X(E)`. Within `{ω_X : H¹(X, ω_X) = 0}` the
  normalization does determine `ω_X` up to a unique trace-compatible isomorphism, and that is
  what those two results say.

**The condition is a condition, not a construction.** `f^!` at the level of schemes
([Stacks, Tag 0A9E]) is not needed to state it, nor to prove the uniqueness and the trace
isomorphism below: `ω_X` and the trace are parameters, and the only thing assumed about them is
the bijectivity above. Constructing an `ω_X` satisfying it is [Stacks, Tag 0B4R] and does use
`f^!`.

**The uniqueness statement names `H¹(X, ω_X) = 0`.** Producing a comparison map out of the
universal property at `ℱ = ω_X'` needs `H¹(X, ω_X') = 0`, which for a normalized dualizing
module is Grauert–Riemenschneider vanishing, [Stacks, Tag 0AXD]. It is therefore an argument of
`existsUnique_hom_of_normalized` and of `normalizedDualizingIso` rather than a field of the
structure, so that no part of clause (2) of [Stacks, Tag 0B64] — the vanishing
`H¹(X, ω_X(n)) = 0` for `n ≥ 0`, whose value at `n = 0` this is — enters the normalization
condition itself.

**`Γ(X, 𝒪_X)` as an `A`-module.** `AlgebraicGeometry.RationalSingularitySituation`
`.globalSectionsModule` restricts scalars along `A ⟶ Γ(X, 𝒪_X)`, so the `A`-module structure on
the underlying type of `Γ(X, 𝒪_X)` is not the one instance search finds there;
`globalFunctionsModule` is that structure, declared as a local instance for this file.

## References

* [Stacks Project, Tag 0B4R](https://stacks.math.columbia.edu/tag/0B4R)
* [Stacks Project, Tag 0B4W](https://stacks.math.columbia.edu/tag/0B4W)
* [Stacks Project, Tag 0B4Y](https://stacks.math.columbia.edu/tag/0B4Y)
* [Stacks Project, Tag 0BBU](https://stacks.math.columbia.edu/tag/0BBU)
* [Stacks Project, Tag 0A7F](https://stacks.math.columbia.edu/tag/0A7F)
* [Stacks Project, Tag 0A9E](https://stacks.math.columbia.edu/tag/0A9E)
* [Stacks Project, Tag 0AXD](https://stacks.math.columbia.edu/tag/0AXD)
* [Stacks Project, Tag 0B64](https://stacks.math.columbia.edu/tag/0B64)
* [Stacks Project, Tag 0B5H](https://stacks.math.columbia.edu/tag/0B5H)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.AffineBase

universe u

attribute [local instance 10000] HasDerivedCategory.standard

namespace AlgebraicGeometry

namespace RationalSingularitySituation

variable (S : RationalSingularitySituation.{u})

/-! ### Global sections as a functor to `A`-modules -/

/-- Global sections of a morphism of `𝒪_X`-modules, as a map of `A`-modules. -/
public def globalSectionsMap {F G : S.X.Modules} (φ : F ⟶ G) :
    S.globalSectionsModule F ⟶ S.globalSectionsModule G :=
  (ModuleCat.restrictScalars S.structureRingHom).map ((moduleGlobalSections S.X).map φ)

/-- `globalSectionsMap φ` acts on a global section through the component of `φ` over `X`. -/
@[simp]
public theorem globalSectionsMap_hom_apply {F G : S.X.Modules} (φ : F ⟶ G)
    (m : S.globalSectionsModule F) :
    (S.globalSectionsMap φ).hom m = (φ.val.app (op ⊤)).hom m := rfl

/-- Global sections of the identity morphism is the identity. -/
@[simp]
public theorem globalSectionsMap_id (F : S.X.Modules) :
    S.globalSectionsMap (𝟙 F) = 𝟙 (S.globalSectionsModule F) := by
  simp only [globalSectionsMap]
  rfl

/-- Global sections of a composite is the composite of the global sections. -/
@[simp]
public theorem globalSectionsMap_comp {F G H : S.X.Modules} (φ : F ⟶ G) (ψ : G ⟶ H) :
    S.globalSectionsMap (φ ≫ ψ) = S.globalSectionsMap φ ≫ S.globalSectionsMap ψ := by
  simp only [globalSectionsMap, Functor.map_comp]
  rfl

/-! ### `Γ(X, 𝒪_X) = A` -/

/-- **`Γ(X, 𝒪_X) = A`.** The ring homomorphism induced by `f`, as an isomorphism: this is
[Stacks, Tag 0B4Y]. -/
public def structureRingEquiv : S.A ≃+* Γ(S.X, ⊤) :=
  have : IsIso ((Scheme.ΓSpecIso (.of S.A)).inv ≫ S.f.appTop) := S.isIso_globalFunctions
  RingEquiv.ofBijective S.structureRingHom (ConcreteCategory.bijective_of_isIso
    ((Scheme.ΓSpecIso (.of S.A)).inv ≫ S.f.appTop))

/-- `structureRingEquiv` is the ring homomorphism induced by `f`. -/
@[simp]
public theorem structureRingEquiv_apply (a : S.A) :
    S.structureRingEquiv a = S.structureRingHom a := rfl

/-- The `A`-module structure on the global functions of `X`, at the underlying type: it is the
one `globalSectionsModule` puts there, through `f`, and instance search does not find it. -/
public abbrev globalFunctionsModule : Module S.A ↑Γ(S.X, ⊤) :=
  (S.globalSectionsModule (SheafOfModules.unit S.X.ringCatSheaf)).isModule

attribute [local instance] globalFunctionsModule

/-- **`Hom_A(H⁰(X, 𝒪_X), N) = N`**, by evaluation at the unit section: `Γ(X, 𝒪_X) = A` is free
of rank one on `1`. -/
public def unitGlobalSectionsHomEquiv (N : ModuleCat.{u} S.A) :
    (S.globalSectionsModule (SheafOfModules.unit S.X.ringCatSheaf) ⟶ N) ≃ N where
  toFun g := g.hom (1 : Γ(S.X, ⊤))
  invFun n := ModuleCat.ofHom (R := S.A) (X := ↑Γ(S.X, ⊤)) (Y := ↑N)
    { toFun := fun x => S.structureRingEquiv.symm x • n
      map_add' := fun x y => by simp [add_smul]
      map_smul' := fun a x => by
        change S.structureRingEquiv.symm (S.structureRingEquiv a * x) • n = a • _
        rw [S.structureRingEquiv.symm.map_mul, RingEquiv.symm_apply_apply, mul_smul] }
  left_inv g := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    have h : S.structureRingEquiv.symm x • (1 : Γ(S.X, ⊤)) = x := by
      change S.structureRingEquiv (S.structureRingEquiv.symm x) * (1 : Γ(S.X, ⊤)) = x
      rw [RingEquiv.apply_symm_apply, mul_one]
    exact (g.hom.map_smul (S.structureRingEquiv.symm x) (1 : Γ(S.X, ⊤))).symm.trans
      (congrArg g.hom.toFun h)
  right_inv n := by
    change S.structureRingEquiv.symm (1 : Γ(S.X, ⊤)) • n = n
    simp

/-! ### `Hom(𝒪_X, ℱ) = H⁰(X, ℱ)` -/

/-- The global section of `ℱ` determined by a morphism `𝒪_X ⟶ ℱ`: its value at the unit
section. -/
public def unitSectionHom (F : S.X.Modules)
    (φ : SheafOfModules.unit S.X.ringCatSheaf ⟶ F) : S.globalSectionsModule F :=
  (φ.val.app (op ⊤)).hom (1 : Γ(S.X, ⊤))

/-- **`Hom_{𝒪_X}(𝒪_X, ℱ) = H⁰(X, ℱ)`.** Morphisms out of the structure sheaf are sections, and a
section of a sheaf of modules on a space is determined by, and determined freely by, its value
over the whole space. -/
public theorem bijective_unitSectionHom (F : S.X.Modules) :
    Function.Bijective (S.unitSectionHom F) := by
  have h : S.unitSectionHom F =
      (fun s : SheafOfModules.sections F => s.val (op ⊤)) ∘ SheafOfModules.unitHomEquiv F := rfl
  rw [h]
  refine Function.Bijective.comp ⟨fun s s' hss => ?_, fun m => ?_⟩
    (SheafOfModules.unitHomEquiv F).bijective
  · exact Stacks.PresheafOfModules.sections_ext_top hss
  · exact ⟨Stacks.PresheafOfModules.sectionOfTop F.val m,
      Stacks.PresheafOfModules.sectionOfTop_val_top F.val m⟩

/-! ### The normalization condition -/

/-- The duality pairing of a trace map `t : H⁰(X, ω_X) ⟶ ω_A`: it sends a morphism
`φ : ℱ ⟶ ω_X` to `t ∘ H⁰(φ) : H⁰(X, ℱ) ⟶ ω_A`. -/
public def tracePairing {ωA : ModuleCat.{u} S.A} {ωX : S.X.Modules}
    (t : S.globalSectionsModule ωX ⟶ ωA) (F : S.X.Modules) :
    (F ⟶ ωX) → (S.globalSectionsModule F ⟶ ωA) :=
  fun φ => S.globalSectionsMap φ ≫ t

/-- **The dualizing module of `X` normalized relative to `ω_A`**, as a condition on a dualizing
module `ω_X` on `X` together with a trace map on global sections: the duality pairing of the
trace is bijective against every quasi-coherent module whose first cohomology vanishes.

This is the shape Grothendieck duality takes for `ω_X[2] = f^!(ω_A[2])` once the shift is
removed and `Rf_*ℱ` is concentrated in degree zero; see the module documentation. -/
public structure NormalizedDualizingModule [IsLocallyNoetherian S.X]
    (ωA : ModuleCat.{u} S.A) (ωX : S.X.Modules) where
  /-- `ω_X` is a dualizing module on `X`. -/
  isDualizing : Stacks.Duality.IsDualizingModule ωX
  /-- The trace map on global sections. -/
  trace : S.globalSectionsModule ωX ⟶ ωA
  /-- Relative duality in degree zero: against a quasi-coherent module with vanishing first
  cohomology, composing with the trace identifies morphisms into `ω_X` with `A`-linear maps of
  global sections into `ω_A`. -/
  bijective_tracePairing : ∀ F : S.X.Modules, F.IsQuasicoherent →
    IsZero (((moduleGlobalSections S.X).rightDerivedPlus 1).obj F) →
    Function.Bijective (S.tracePairing trace F)

variable [IsLocallyNoetherian S.X] {ωA : ModuleCat.{u} S.A} {ωX ωX' : S.X.Modules}

/-! ### The trace isomorphism -/

/-- **Stacks Project, Tag 0BBU** for a normalized dualizing module. The trace map
`H⁰(X, ω_X) ⟶ ω_A` of a dualizing module normalized relative to `ω_A` is bijective.

This is the normalization condition at `ℱ = 𝒪_X`: the structure sheaf is quasi-coherent and
`H¹(X, 𝒪_X) = 0` because `A` defines a rational singularity, so the pairing
`Hom_{𝒪_X}(𝒪_X, ω_X) ⟶ Hom_A(H⁰(X, 𝒪_X), ω_A)` is bijective; its source is `H⁰(X, ω_X)` and its
target is `ω_A`, the latter because `Γ(X, 𝒪_X) = A` by [Stacks, Tag 0B4Y], and under those two
identifications the pairing *is* the trace. -/
public theorem bijective_trace_of_normalized (N : S.NormalizedDualizingModule ωA ωX) :
    Function.Bijective N.trace.hom := by
  have hpair := N.bijective_tracePairing (SheafOfModules.unit S.X.ringCatSheaf)
    (_root_.isQuasicoherent_of_isCoherent _) S.isZero_firstCohomologyStructureSheaf
  have hcomp : (S.unitGlobalSectionsHomEquiv ωA) ∘
      S.tracePairing N.trace (SheafOfModules.unit S.X.ringCatSheaf) =
      N.trace.hom ∘ S.unitSectionHom ωX := rfl
  have h : Function.Bijective (N.trace.hom ∘ S.unitSectionHom ωX) :=
    hcomp ▸ ((S.unitGlobalSectionsHomEquiv ωA).bijective.comp hpair)
  exact (Function.Bijective.of_comp_iff _ (S.bijective_unitSectionHom ωX)).1 h

/-- The trace map of a normalized dualizing module, as an isomorphism. -/
public def traceIsoOfNormalized (N : S.NormalizedDualizingModule ωA ωX) :
    S.globalSectionsModule ωX ≅ ωA :=
  have : IsIso N.trace :=
    (ConcreteCategory.isIso_iff_bijective N.trace).2 (S.bijective_trace_of_normalized N)
  asIso N.trace

/-- **The datum of [Stacks, Tag 0BBU] follows from the normalization.** The trace of a
normalized dualizing module is injective, and exact against the zero obstruction map because it
is surjective; the obstruction group `Ext²_A(H¹(X, 𝒪_X), ω_A)` vanishes in every
`RationalSingularitySituation`. -/
public def dualizingTraceSequenceOfNormalized (N : S.NormalizedDualizingModule ωA ωX) :
    S.DualizingTraceSequence ωA ωX where
  trace := N.trace
  injective_trace := (S.bijective_trace_of_normalized N).1
  obstruction := 0
  exact b := iff_of_true (AddMonoidHom.zero_apply b)
    ((S.bijective_trace_of_normalized N).2 b)

/-! ### Uniqueness up to a canonical isomorphism -/

/-- **A normalized dualizing module receives a unique trace-compatible map from another one.**
The normalization condition for `ω_X` at `ℱ = ω_X'`, which is quasi-coherent because it is
coherent, turns the trace of `ω_X'` into a unique morphism `ω_X' ⟶ ω_X` over `ω_A`.

The vanishing `h'` of `H¹(X, ω_X')` is the content of [Stacks, Tag 0AXD] at `ω_X'`. -/
public theorem existsUnique_hom_of_normalized (N : S.NormalizedDualizingModule ωA ωX)
    (N' : S.NormalizedDualizingModule ωA ωX')
    (h' : IsZero (((moduleGlobalSections S.X).rightDerivedPlus 1).obj ωX')) :
    ∃! φ : ωX' ⟶ ωX, S.globalSectionsMap φ ≫ N.trace = N'.trace := by
  have hqc : ωX'.IsQuasicoherent :=
    let := N'.isDualizing.1
    _root_.isQuasicoherent_of_isCoherent ωX'
  obtain ⟨hinj, hsurj⟩ := N.bijective_tracePairing ωX' hqc h'
  obtain ⟨φ, hφ⟩ := hsurj N'.trace
  exact ⟨φ, hφ, fun ψ hψ => hinj (hψ.trans hφ.symm)⟩

/-- **The canonical comparison isomorphism of two normalized dualizing modules.** The
trace-compatible maps in the two directions compose to trace-compatible endomorphisms, which are
the identities by the uniqueness of `existsUnique_hom_of_normalized`.

The two vanishing hypotheses are the content of [Stacks, Tag 0AXD] at `ω_X` and at `ω_X'`. -/
public def normalizedDualizingIso (N : S.NormalizedDualizingModule ωA ωX)
    (N' : S.NormalizedDualizingModule ωA ωX')
    (h : IsZero (((moduleGlobalSections S.X).rightDerivedPlus 1).obj ωX))
    (h' : IsZero (((moduleGlobalSections S.X).rightDerivedPlus 1).obj ωX')) :
    ωX' ≅ ωX where
  hom := (S.existsUnique_hom_of_normalized N N' h').choose
  inv := (S.existsUnique_hom_of_normalized N' N h).choose
  hom_inv_id := by
    refine (S.existsUnique_hom_of_normalized N' N' h').unique ?_ ?_
    · rw [S.globalSectionsMap_comp, Category.assoc,
        (S.existsUnique_hom_of_normalized N' N h).choose_spec.1,
        (S.existsUnique_hom_of_normalized N N' h').choose_spec.1]
    · rw [S.globalSectionsMap_id, Category.id_comp]
  inv_hom_id := by
    refine (S.existsUnique_hom_of_normalized N N h).unique ?_ ?_
    · rw [S.globalSectionsMap_comp, Category.assoc,
        (S.existsUnique_hom_of_normalized N N' h').choose_spec.1,
        (S.existsUnique_hom_of_normalized N' N h).choose_spec.1]
    · rw [S.globalSectionsMap_id, Category.id_comp]

/-- The comparison isomorphism is compatible with the traces. -/
public theorem globalSectionsMap_normalizedDualizingIso_hom
    (N : S.NormalizedDualizingModule ωA ωX) (N' : S.NormalizedDualizingModule ωA ωX')
    (h : IsZero (((moduleGlobalSections S.X).rightDerivedPlus 1).obj ωX))
    (h' : IsZero (((moduleGlobalSections S.X).rightDerivedPlus 1).obj ωX')) :
    S.globalSectionsMap (S.normalizedDualizingIso N N' h h').hom ≫ N.trace = N'.trace :=
  (S.existsUnique_hom_of_normalized N N' h').choose_spec.1

/-- The comparison isomorphism is the only trace-compatible morphism. -/
public theorem eq_normalizedDualizingIso_hom (N : S.NormalizedDualizingModule ωA ωX)
    (N' : S.NormalizedDualizingModule ωA ωX')
    (h : IsZero (((moduleGlobalSections S.X).rightDerivedPlus 1).obj ωX))
    (h' : IsZero (((moduleGlobalSections S.X).rightDerivedPlus 1).obj ωX'))
    (φ : ωX' ⟶ ωX) (hφ : S.globalSectionsMap φ ≫ N.trace = N'.trace) :
    φ = (S.normalizedDualizingIso N N' h h').hom :=
  (S.existsUnique_hom_of_normalized N N' h').unique hφ
    (S.existsUnique_hom_of_normalized N N' h').choose_spec.1

end RationalSingularitySituation

end AlgebraicGeometry

end

end
