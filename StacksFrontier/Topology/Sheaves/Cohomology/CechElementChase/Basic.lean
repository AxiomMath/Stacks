module

public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
public import StacksFrontier.Topology.Sheaves.Cohomology.CechElementChase.Cocycle
public import StacksFrontier.Topology.Sheaves.Cohomology.CechGaps.Basic

/-!
# [Stacks, Tag 01EU]: vanishing first Čech cohomology makes sections surjective

`Stacks.CechGaps.higherCohomology_isZero_of_01EP_01EU` deduces [Stacks, Tag 01EW] from two
Stacks lemmas, [Stacks, Tag 01EP] (Čech acyclicity of injectives) and [Stacks, Tag 01EU], the
latter taken as the hypothesis

```
h01EU : ∀ S : ShortComplex (SheafOfModules R), S.ShortExact →
  HasVanishingHigherCech R Cov S.X₁ → ∀ W ∈ Bas, Epi ((secF R W).map S.g)
```

This file proves `h01EU` from a cofinality hypothesis on `Cov` alone, and restates
[Stacks, Tag 01EW] with [Stacks, Tag 01EP] as a hypothesis in place of `h01EU`.

## The statement, and why cofinality is needed

[Stacks, Tag 01EU] concludes surjectivity of `Γ(U, ℱ₂) → Γ(U, ℱ₃)` from vanishing of
`Ȟ¹(𝒰, ℱ₁)` for a system of coverings of `U` that is **cofinal**: the covering produced by local
surjectivity of `ℱ₂ → ℱ₃` is arbitrary, so it has to be refined by one of the coverings whose
first Čech cohomology is known to vanish. That hypothesis is part of the source statement (it is
the `Stacks.Cohomology.CofinalCoveringSystem` condition), and it is a condition on the pair
`(Bas, Cov)`, not a further theorem. It appears here as

```
hcof : ∀ W ∈ Bas, ∀ 𝒲 : OpenCover X, 𝒲.carrier = W → ∃ V ∈ Cov, V.Refines 𝒲
```

The conditioning of `h01EU` on `HasVanishingHigherCech R Cov S.X₁` is load-bearing and is kept:
without it the hypothesis would say that `Γ(W, -)` is right exact on all of `Mod(𝒪_X)` for every
`W ∈ Bas`, which is false on any space with nonvanishing `H¹`.

## Main results

* `Stacks.CechElementChase.exists_preimage_of_cech`: **the element chase**, at the level of
  abelian presheaves on the space. Given a cover `U` of `W`, local lifts of a section `s` of `P₃`
  over the members of the cover, exactness of `P₁ → P₂ → P₃` over every open, the sheaf condition
  on `P₂` and `P₃`, and vanishing of `Ȟ¹(U, P₁)`, the section `s` lifts over `W`.
* `Stacks.CechElementChase.exists_cover_lift`: the covering extracted from local surjectivity of
  a sheaf epimorphism — its index type is a subtype of `Opens X`, hence a `Type u`, which is what
  `OpenCover.ι` demands.
* `Stacks.CechElementChase.epi_secF_map_g`: **[Stacks, Tag 01EU]** for sheaves of `𝒪_X`-modules.
* `Stacks.CechElementChase.h01EU`: the hypothesis `h01EU` of
  `Stacks.CechGaps.higherCohomology_isZero_of_01EP_01EU`, proved from cofinality.
* `Stacks.CechElementChase.higherCohomology_isZero_of_01EP`: **[Stacks, Tag 01EW]**, with
  [Stacks, Tag 01EP] (`CechAcyclicInjectives`, Čech acyclicity of injective `𝒪_X`-modules) as a
  hypothesis.

## The route

Fix `W ∈ Bas` and `s ∈ Γ(W, ℱ₃)`.

1. `S.g` is an epimorphism of sheaves of modules, so `(SheafOfModules.toSheaf R).map S.g` is an
   epimorphism of sheaves of abelian groups — `SheafOfModules.toSheaf R` preserves colimits of the
   relevant shape, so `PreservesEpimorphisms` is an instance — hence locally surjective by
   `CategoryTheory.Sheaf.isLocallySurjective_iff_epi'`. `Presheaf.imageSieve_mem` turns that into
   a covering sieve of `W`, and `Opens.mem_grothendieckTopology` turns the sieve into a covering
   family: `exists_cover_lift`.
2. Refine that covering to one in `Cov` and restrict the lifts along the refinement.
3. Assemble the lifts into a Čech `0`-cochain `T` of `ℱ₂`. Its differential `d⁰T` is killed by
   `ℱ₂ → ℱ₃`, because the image `0`-cochain consists of restrictions of the single section `s`
   (`cechD_zero_eq_zero_of_restrict`), so `d⁰T` lifts componentwise to a `1`-cochain `C` of `ℱ₁`.
4. `C` is a cocycle: `d¹C` has vanishing image under the injective `ℱ₁ → ℱ₂`, since the image is
   `d¹d⁰T`.
5. `Ȟ¹(V, ℱ₁) = 0` makes `C` a coboundary `d⁰B`, and then the corrected cochain
   `T - (ℱ₁ → ℱ₂)(B)` is a `0`-cocycle.
6. A `0`-cocycle is a compatible family (`zeroCocycle_agree`), so it glues to `t ∈ Γ(W, ℱ₂)`;
   `t` maps to `s` because both restrict to the same sections on the cover and `ℱ₃` is a sheaf.

## Implementation notes

**The cover used for the gluing is indexed by `Fin 1 → V.ι`, not by `V.ι`.** The Čech `0`-cochain
lives over the opens `∏ᶜ (V.obj ∘ y)` for `y : Fin 1 → V.ι`, which are equal to `V.obj (y 0)` but
not definitionally so; rewriting the index of a dependent family would mean transporting sections
along an equality of opens. Taking the glueing cover to be `y ↦ ∏ᶜ (V.obj ∘ y)` avoids it
entirely: the two comparisons actually needed, `∏ᶜ (V.obj ∘ y) ≤ V.obj (y 0)` and
`V.obj i ≤ ∏ᶜ (V.obj ∘ (fun _ ↦ i))`, are inequalities, and the second is what makes the new
family still cover `W`.

**`TopCat.Sheaf` is a `def`, so the gluing lemma needs its arguments.**
`TopCat.Sheaf.existsUnique_gluing'` does not unify its first explicit argument with a term of type
`Sheaf (Opens.grothendieckTopology X) AddCommGrpCat` unless the space and the target category are
given explicitly; with `(X := TopCat.of X)` and `(C := AddCommGrpCat.{u})` supplied, the
definitional unfolding goes through.

**Compatibility is matched by proof irrelevance.** `TopCat.Presheaf.IsCompatible` is phrased with
`TopologicalSpace.Opens.infLELeft`/`infLERight`, while `zeroCocycle_agree` produces `homOfLE
inf_le_left`/`inf_le_right`; in `Opens X` these are the same morphism, so the terms are
interchangeable without a rewrite.

**No universe is left free.** As in `CechGaps`, the module universe is taken equal to the universe
of the space, and `CechAcyclicInjectives.{u, u, u₂}` is written with its three universes pinned —
`(space, module, ring)`. With the module universe left free, instance synthesis instead solves
`HasProducts.{u} AddCommGrpCat.{?w}` through `UnivLE`, and elaboration dies on a `whnf` heartbeat
timeout rather than on an error.

## References

* [Stacks Project, Tag 01EU](https://stacks.math.columbia.edu/tag/01EU)
* [Stacks Project, Tag 01EW](https://stacks.math.columbia.edu/tag/01EW)
* [Stacks Project, Tag 01EP](https://stacks.math.columbia.edu/tag/01EP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.CohomologyVanishing Stacks.CechGaps

universe u u₂

namespace Stacks.CechElementChase

section Chase

variable {X : Type u} [TopologicalSpace X] {ι : Type u} (U : ι → Opens X)
  {P₁ P₂ P₃ : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}} (φ : P₁ ⟶ P₂) (ψ : P₂ ⟶ P₃)

/-- **The element chase of [Stacks, Tag 01EU]**, for abelian presheaves on a space. A section `s`
of `P₃` over `W` that lifts to `P₂` over each member of a cover of `W` with vanishing first Čech
cohomology for `P₁` lifts over `W` itself. -/
theorem exists_preimage_of_cech (W : Opens X) (hUW : ∀ i, U i ≤ W) (hcov : W ≤ ⨆ i, U i)
    (hP₂ : Presheaf.IsSheaf (Opens.grothendieckTopology X) P₂)
    (hP₃ : Presheaf.IsSheaf (Opens.grothendieckTopology X) P₃)
    (hcomp : φ ≫ ψ = 0)
    (hinj : ∀ O : Opens X, Function.Injective (φ.app (op O)))
    (hex : ∀ (O : Opens X) (a : ToType (P₂.obj (op O))), ψ.app (op O) a = 0 →
      ∃ b, φ.app (op O) b = a)
    (hH1 : IsZero (((cechComplexFunctor U).obj P₁).homology 1))
    (s : ToType (P₃.obj (op W))) (τ : ∀ i, ToType (P₂.obj (op (U i))))
    (hτ : ∀ i, ψ.app (op (U i)) (τ i) = P₃.map (homOfLE (hUW i)).op s) :
    ∃ t, ψ.app (op W) t = s := by
  have hzero : ∀ (O : Opens X) (b : ToType (P₁.obj (op O))),
      ψ.app (op O) (φ.app (op O) b) = 0 := fun O b ↦ by
    simpa using ConcreteCategory.congr_hom
      (congrArg (fun α : P₁ ⟶ P₃ ↦ α.app (op O)) hcomp) b
  have hAW : ∀ y : Fin 1 → ι, (∏ᶜ (U ∘ y) : Opens X) ≤ W :=
    fun y ↦ (prodOpens_le_obj U y 0).trans (hUW (y 0))
  -- The Čech `0`-cochain of local lifts.
  obtain ⟨T, hT⟩ : ∃ T : ToType (((cechComplexFunctor U).obj P₂).X 0),
      ∀ y, Limits.Pi.π (cechDeg U P₂ 0) y T
        = P₂.map (homOfLE (prodOpens_le_obj U y 0)).op (τ (y 0)) :=
    ⟨(cechEquiv U P₂ 0).symm _, cechEquiv_symm_apply_π U P₂ 0 _⟩
  have hψT : ∀ y, Limits.Pi.π (cechDeg U P₃ 0) y (((cechComplexFunctor U).map ψ).f 0 T)
      = P₃.map (homOfLE (hAW y)).op s := by
    intro y
    rw [cechMap_π_apply, hT, NatTrans.naturality_apply, hτ, map_homOfLE_comp]
  -- Its differential dies under `ψ`, because the image cochain restricts the single section `s`.
  have hψD : ((cechComplexFunctor U).map ψ).f 1 (((cechComplexFunctor U).obj P₂).d 0 1 T) = 0 := by
    rw [cechMap_d_apply]
    exact cechD_zero_eq_zero_of_restrict U P₃ s hAW _ hψT
  -- So it lifts, componentwise, to a `1`-cochain of `P₁`.
  have hcex : ∀ x : Fin 2 → ι, ∃ c : ToType (P₁.obj (op (∏ᶜ (U ∘ x)))),
      φ.app (op (∏ᶜ (U ∘ x))) c
        = Limits.Pi.π (cechDeg U P₂ 1) x (((cechComplexFunctor U).obj P₂).d 0 1 T) := by
    intro x
    refine hex _ _ ?_
    rw [← cechMap_π_apply, hψD, cech_π_zero]
  choose c hc using hcex
  obtain ⟨C, hC⟩ : ∃ C : ToType (((cechComplexFunctor U).obj P₁).X 1),
      ∀ x, Limits.Pi.π (cechDeg U P₁ 1) x C = c x :=
    ⟨(cechEquiv U P₁ 1).symm c, cechEquiv_symm_apply_π U P₁ 1 c⟩
  have hΦC : ((cechComplexFunctor U).map φ).f 1 C = ((cechComplexFunctor U).obj P₂).d 0 1 T := by
    refine cech_ext U P₂ 1 _ _ fun x ↦ ?_
    rw [cechMap_π_apply, hC, hc]
  -- `C` is a cocycle: its image under the injective `φ` is `d¹d⁰T`.
  have hdC : ((cechComplexFunctor U).obj P₁).d 1 2 C = 0 := by
    refine cech_eq_zero U P₁ 2 _ fun y ↦ ?_
    refine hinj _ ?_
    rw [← cechMap_π_apply, cechMap_d_apply, hΦC, cech_d_d_apply, cech_π_zero, map_zero]
  -- Vanishing first Čech cohomology makes it a coboundary.
  obtain ⟨B, hB⟩ := exists_coboundary_of_cocycle _ hH1 C hdC
  -- The corrected `0`-cochain is a cocycle.
  have hu : ((cechComplexFunctor U).obj P₂).d 0 1
      (T - ((cechComplexFunctor U).map φ).f 0 B) = 0 := by
    rw [map_sub, ← cechMap_d_apply, hB, hΦC, sub_self]
  -- Glue it, over the cover indexed by the `0`-simplices.
  have hcovA : W ≤ ⨆ y : Fin 1 → ι, (∏ᶜ (U ∘ y) : Opens X) :=
    hcov.trans (iSup_le fun i ↦ (obj_le_prodOpens_const U i).trans
      (le_iSup (fun y : Fin 1 → ι ↦ (∏ᶜ (U ∘ y) : Opens X)) (fun _ ↦ i)))
  have hcompat : TopCat.Presheaf.IsCompatible (X := TopCat.of X) P₂
      (fun y : Fin 1 → ι ↦ (∏ᶜ (U ∘ y) : Opens X))
      (fun y ↦ Limits.Pi.π (cechDeg U P₂ 0) y (T - ((cechComplexFunctor U).map φ).f 0 B)) :=
    fun y z ↦ zeroCocycle_agree U P₂ hu y z _ inf_le_left inf_le_right
  obtain ⟨t, ht, -⟩ := TopCat.Sheaf.existsUnique_gluing' (X := TopCat.of X)
    (C := AddCommGrpCat.{u}) ⟨P₂, hP₂⟩ (fun y : Fin 1 → ι ↦ (∏ᶜ (U ∘ y) : Opens X)) W
    (fun y ↦ homOfLE (hAW y)) hcovA _ hcompat
  refine ⟨t, ?_⟩
  -- The components of the corrected cochain, read off at an ordinary type: a subtraction
  -- inside a Čech term is not available to `rw`, so it is resolved once, in term mode.
  have huc : ∀ y : Fin 1 → ι,
      Limits.Pi.π (cechDeg U P₂ 0) y (T - ((cechComplexFunctor U).map φ).f 0 B)
        = Limits.Pi.π (cechDeg U P₂ 0) y T
          - φ.app (op (∏ᶜ (U ∘ y))) (Limits.Pi.π (cechDeg U P₁ 0) y B) := fun y ↦
    (map_sub _ _ _).trans
      (congrArg (fun z ↦ Limits.Pi.π (cechDeg U P₂ 0) y T - z) (cechMap_π_apply U P₁ P₂ φ 0 B y))
  -- `ψ t` and `s` have the same restrictions to the cover, hence agree.
  have hψt : ∀ y : Fin 1 → ι, P₃.map (homOfLE (hAW y)).op (ψ.app (op W) t)
      = P₃.map (homOfLE (hAW y)).op s := by
    intro y
    rw [← NatTrans.naturality_apply, ht y, huc, map_sub, hzero, sub_zero, ← cechMap_π_apply]
    exact hψT y
  exact TopCat.Sheaf.eq_of_locally_eq' (X := TopCat.of X) (C := AddCommGrpCat.{u}) ⟨P₃, hP₃⟩
    (fun y : Fin 1 → ι ↦ (∏ᶜ (U ∘ y) : Opens X)) W (fun y ↦ homOfLE (hAW y)) hcovA _ _ hψt

end Chase

section Modules

variable {X : Type u} [TopologicalSpace X]
  (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u₂})

/-- Every member of a covering of `W` is contained in `W`. -/
lemma obj_le_of_carrier_eq {V : OpenCover X} {W : Opens X} (hVW : V.carrier = W) (i : V.ι) :
    V.obj i ≤ W :=
  (le_iSup V.obj i).trans (V.iSup_eq.trans hVW).le

variable (S : ShortComplex (SheafOfModules.{u} R))

/-- The composite of the two maps of underlying abelian presheaves is zero. -/
lemma presheafOf_map_f_comp_map_g :
    (presheafOf R).map S.f ≫ (presheafOf R).map S.g = 0 := by
  rw [← Functor.map_comp, S.zero, Functor.map_zero]

/-- `Γ(O, -)` sends a short exact sequence to an exact sequence with injective first map. -/
private lemma secF_map_exact_and_mono (hS : S.ShortExact) (O : Opens X) :
    (S.map (secF R O)).Exact ∧ Mono (S.map (secF R O)).f :=
  (Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono (secF R O)).1 inferInstance S hS

/-- **`Γ(O, -)` is left exact**, first consequence: the first map is injective on sections. -/
lemma injective_app_map_f (hS : S.ShortExact) (O : Opens X) :
    Function.Injective (((presheafOf R).map S.f).app (op O)) :=
  (AddCommGrpCat.mono_iff_injective _).1 (secF_map_exact_and_mono R S hS O).2

/-- **`Γ(O, -)` is left exact**, second consequence: a section killed by the second map comes
from the first. -/
lemma exists_app_map_f_eq (hS : S.ShortExact) (O : Opens X)
    (a : ToType (((presheafOf R).obj S.X₂).obj (op O)))
    (ha : ((presheafOf R).map S.g).app (op O) a = 0) :
    ∃ b, ((presheafOf R).map S.f).app (op O) b = a :=
  (ShortComplex.ab_exact_iff _).1 (secF_map_exact_and_mono R S hS O).1 a ha

variable [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **The covering of `W` by opens over which a given section lifts.** A sheaf epimorphism is
locally surjective, and the resulting covering sieve of `W` is turned into an `OpenCover` whose
index type is the subtype of `Opens X` of the opens appearing in it — a `Type u`, as
`OpenCover.ι` requires. -/
theorem exists_cover_lift (hS : S.ShortExact) (W : Opens X)
    (s : ToType (((presheafOf R).obj S.X₃).obj (op W))) :
    ∃ (𝒲 : OpenCover X) (h : 𝒲.carrier = W), ∀ j : 𝒲.ι,
      ∃ t, ((presheafOf R).map S.g).app (op (𝒲.obj j)) t
        = ((presheafOf R).obj S.X₃).map (homOfLE (obj_le_of_carrier_eq h j)).op s := by
  have := hS.epi_g
  have hls0 : Sheaf.IsLocallySurjective ((SheafOfModules.toSheaf R).map S.g) := by
    rw [Sheaf.isLocallySurjective_iff_epi']
    infer_instance
  have hls : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      ((presheafOf R).map S.g) := hls0
  have hsieve := Presheaf.imageSieve_mem (Opens.grothendieckTopology X)
    ((presheafOf R).map S.g) (U := op W) s
  refine ⟨⟨{V : Opens X // ∃ h : V ≤ W,
      (Presheaf.imageSieve ((presheafOf R).map S.g) s).arrows (homOfLE h)}, W, Subtype.val,
      le_antisymm (iSup_le fun p ↦ p.2.elim fun h _ ↦ h) ?_⟩, rfl, ?_⟩
  · intro x hx
    obtain ⟨Vx, f, hf, hxV⟩ := (Opens.mem_grothendieckTopology X).1 hsieve x hx
    exact Opens.mem_iSup.2 ⟨⟨Vx, f.le, hf⟩, hxV⟩
  · exact fun p ↦ p.2.snd

/-- **[Stacks, Tag 01EU].** If the first term of a short exact sequence of `𝒪_X`-modules has
vanishing higher Čech cohomology for `Cov`, and every covering of `W` is refined by one in `Cov`,
then sections over `W` are surjective on the last map. -/
theorem epi_secF_map_g (hS : S.ShortExact) {Cov : Set (OpenCover X)}
    (h₁ : HasVanishingHigherCech R Cov S.X₁) (W : Opens X)
    (hcof : ∀ 𝒲 : OpenCover X, 𝒲.carrier = W → ∃ V ∈ Cov, V.Refines 𝒲) :
    Epi ((secF R W).map S.g) := by
  rw [AddCommGrpCat.epi_iff_surjective]
  intro s
  obtain ⟨𝒲, h𝒲, hlift⟩ := exists_cover_lift R S hS W s
  obtain ⟨V, hVCov, hVcar, hVref⟩ := hcof 𝒲 h𝒲
  have hVW : ∀ i : V.ι, V.obj i ≤ W := obj_le_of_carrier_eq (hVcar.trans h𝒲)
  have hτ : ∀ i : V.ι, ∃ t : ToType (((presheafOf R).obj S.X₂).obj (op (V.obj i))),
      ((presheafOf R).map S.g).app (op (V.obj i)) t
        = ((presheafOf R).obj S.X₃).map (homOfLE (hVW i)).op s := by
    intro i
    obtain ⟨j, hj⟩ := hVref i
    obtain ⟨t, ht⟩ := hlift j
    refine ⟨((presheafOf R).obj S.X₂).map (homOfLE hj).op t, ?_⟩
    rw [NatTrans.naturality_apply, ht, map_homOfLE_comp]
  choose τ hτ' using hτ
  exact exists_preimage_of_cech V.obj ((presheafOf R).map S.f) ((presheafOf R).map S.g) W hVW
    (V.iSup_eq.trans (hVcar.trans h𝒲)).ge S.X₂.isSheaf S.X₃.isSheaf
    (presheafOf_map_f_comp_map_g R S) (injective_app_map_f R S hS) (exists_app_map_f_eq R S hS)
    (h₁ V hVCov 1 one_pos) s τ hτ'

variable (Bas : Set (Opens X)) (Cov : Set (OpenCover X))

/-- **The hypothesis `h01EU` of `Stacks.CechGaps.higherCohomology_isZero_of_01EP_01EU`**, proved
from cofinality of `Cov` among the coverings of the opens of `Bas`. -/
theorem h01EU
    (hcof : ∀ W ∈ Bas, ∀ 𝒲 : OpenCover X, 𝒲.carrier = W → ∃ V ∈ Cov, V.Refines 𝒲) :
    ∀ T : ShortComplex (SheafOfModules.{u} R), T.ShortExact →
      HasVanishingHigherCech R Cov T.X₁ → ∀ W ∈ Bas, Epi ((secF R W).map T.g) :=
  fun T hT h₁ W hW ↦ epi_secF_map_g R T hT h₁ W (hcof W hW)

variable [EnoughInjectives (SheafOfModules.{u} R)] [HasDerivedCategory (SheafOfModules.{u} R)]
  [HasDerivedCategory AddCommGrpCat.{u}]

/-- **[Stacks, Tag 01EW]**, with [Stacks, Tag 01EP] as a hypothesis:
`Stacks.CechGaps.higherCohomology_isZero_of_01EP_01EU` with `h01EU` supplied. -/
theorem higherCohomology_isZero_of_01EP {U : Opens X}
    (hinj : CechAcyclicInjectives.{u, u, u₂} R Cov)
    (hcof : ∀ W ∈ Bas, ∀ 𝒲 : OpenCover X, 𝒲.carrier = W → ∃ V ∈ Cov, V.Refines 𝒲)
    (hCovBas : ∀ V ∈ Cov, ∀ (p : ℕ) (x : Fin (p + 1) → V.ι), (⨅ k, V.obj (x k)) ∈ Bas)
    (hU : U ∈ Bas) (F : SheafOfModules.{u} R) (hF : HasVanishingHigherCech R Cov F)
    (n : ℕ) (hn : 0 < n) : IsZero (Hgroup R U n F) :=
  higherCohomology_isZero_of_01EP_01EU R hinj (h01EU R Bas Cov hcof) hCovBas hU F hF n hn

end Modules

end Stacks.CechElementChase
