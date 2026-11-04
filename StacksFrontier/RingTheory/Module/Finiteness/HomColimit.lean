module

public import StacksCore.Tactic.StacksAttribute
public import Mathlib.Algebra.Category.ModuleCat.EpiMono
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
public import Mathlib.CategoryTheory.Linear.Yoneda
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.RingTheory.PicardGroup

/-!
# Finiteness of a module characterized by injectivity of the Hom comparison map

Let `R` be a commutative ring and `N` an `R`-module. The following are equivalent (Stacks
Tag 0G8N):

1. `N` is a finite, i.e. finitely generated, `R`-module.
2. For every filtered colimit `M = colim_i Mᵢ` of `R`-modules, indexed by an arbitrary
   filtered category `I`, the canonical comparison map
   `Θ_N : colim_i Hom_R(N, Mᵢ) → Hom_R(N, M)` is injective.

For `N` finitely *presented*, `Θ_N` is an isomorphism for all filtered colimits; for `N`
finitely *generated* it is merely injective, and this lemma says that injectivity for *all*
filtered colimits characterizes finiteness exactly.

## Conventions

`R` is a commutative ring with unit, all modules are unital `R`-modules, and `Hom_R(-,-)` is
the `R`-module of `R`-linear maps.

## Implementation notes

We work in the category `ModuleCat R`. The covariant Hom functor `homFunctor R N`
sends `M` to `ModuleCat.of R (N ⟶ M)`, with maps given by `Linear.rightComp`
(`homFunctor_map_apply`).

For a diagram `F : I ⥤ ModuleCat R` over a filtered category `I`, the colimit `M = colimit F`
is the filtered colimit with canonical structure maps `colimit.ι F i : F.obj i ⟶ colimit F`;
these are the `ψᵢ` of the informal statement.

The comparison map `Θ_N` is the canonical morphism
`colimit.post F G : colimit (F ⋙ G) ⟶ G.obj (colimit F)` for `G = Hom_R(N, -)`. By the
universal property of the colimit it is the unique morphism whose composite with
`colimit.ι (F ⋙ G) i` equals `G.map (colimit.ι F i)`, i.e. post-composition with `ψᵢ`.

Injectivity of the `R`-module homomorphism `Θ_N` is expressed categorically as `Mono Θ_N`,
which by `ModuleCat.mono_iff_injective` is equivalent to injectivity of the underlying
function.

Here `R : Type w`, modules are objects of `ModuleCat.{w} R`, and index categories are
`w`-small; this is the setting of
`ModuleCat.FilteredColimits.forget_preservesFilteredColimits`.
-/

@[expose] public section

open CategoryTheory Limits

namespace Stacks.Module.FinitenessViaHomColimit

universe w

variable (R : Type w) [CommRing R]
/-- The covariant Hom functor `Hom_R(N, -) : ModuleCat R ⥤ ModuleCat R`,
sending an `R`-module `M` to the `R`-module of `R`-linear maps `N → M`. -/
noncomputable abbrev homFunctor (N : ModuleCat.{w} R) : ModuleCat.{w} R ⥤ ModuleCat R where
  obj M := ModuleCat.of R (N ⟶ M)
  map f := ModuleCat.ofHom (Linear.rightComp R _ f)

/-- The Hom functor acts on morphisms by post-composition. -/
lemma homFunctor_map_apply (N : ModuleCat.{w} R) {M M' : ModuleCat.{w} R} (g : M ⟶ M')
    (f : N ⟶ M) : (homFunctor R N).map g f = f ≫ g :=
  Linear.rightComp_apply R N g f

/-- The canonical comparison map
`Θ_N : colim_i Hom_R(N, M_i) → Hom_R(N, colim_i M_i)`
for a filtered diagram `F : I ⥤ ModuleCat R` with colimit `M = colimit F`.

It is the comparison morphism `colimit.post F (Hom_R(N, -))`, the unique morphism
sending the class of `f : N → M_i` to `ψ_i ∘ f : N → M`. -/
noncomputable def comparisonMap (N : ModuleCat.{w} R) {I : Type w} [SmallCategory I]
    (F : I ⥤ ModuleCat.{w} R) :
    colimit (F ⋙ homFunctor R N) ⟶ (homFunctor R N).obj (colimit F) :=
  colimit.post F (homFunctor R N)

/-- The "injectivity for all filtered colimits" condition: for every small filtered
diagram of `R`-modules, the comparison map `Θ_N` is injective (a monomorphism). -/
abbrev InjectiveForAllFilteredColimits (N : ModuleCat.{w} R) : Prop :=
  ∀ (I : Type w) [SmallCategory I] [IsFiltered I] (F : I ⥤ ModuleCat.{w} R),
    Mono (comparisonMap R N F)

/-- Correctness of `comparisonMap`: it is characterized by sending the class of a
morphism `f : N → M_i` (the image under the colimit structure map) to the composite
`ψ_i ∘ f : N → M`, where `ψ_i = colimit.ι F i` and `ψ'_i` is the structure map of
the colimit of the Hom-diagram. Concretely, the composite of `comparisonMap` with
the structure map of `colimit (F ⋙ Hom_R(N,-))` at index `i` equals the map
`Hom_R(N, ψ_i)`, i.e. post-composition with `colimit.ι F i`. -/
theorem comparisonMap_fac (N : ModuleCat.{w} R) {I : Type w} [SmallCategory I]
    (F : I ⥤ ModuleCat.{w} R) (i : I) :
    colimit.ι (F ⋙ homFunctor R N) i ≫ comparisonMap R N F
      = (homFunctor R N).map (colimit.ι F i) := by
  -- `comparisonMap R N F` is by definition `colimit.post F (homFunctor R N)`, and
  -- this factorization is exactly the universal-property lemma `colimit.ι_post`.
  unfold comparisonMap
  exact colimit.ι_post F (homFunctor R N) i

/-- An element of `G.obj i` dies in a filtered colimit iff it dies at some later stage. -/
private theorem colimit_ι_apply_eq_zero_iff {I : Type w} [SmallCategory I] [IsFiltered I]
    (G : I ⥤ ModuleCat.{w} R) (i : I) (x : ToType (G.obj i)) :
    (ConcreteCategory.hom (colimit.ι G i)) x = 0 ↔
      ∃ (k : I) (g : i ⟶ k), (ConcreteCategory.hom (G.map g)) x = 0 := by
  have := ModuleCat.FilteredColimits.forget_preservesFilteredColimits (R := R)
  rw [← map_zero (ConcreteCategory.hom (colimit.ι G i)), Concrete.colimit_rep_eq_iff_exists]
  refine ⟨fun ⟨k, g, _, h⟩ => ⟨k, g, by rwa [map_zero] at h⟩, fun ⟨k, g, h⟩ => ⟨k, g, g, ?_⟩⟩
  rw [h, map_zero]

/-- Given finitely many elements of `F.obj i` that all become
zero in the filtered colimit, there is a single index `k` and morphism `g : i ⟶ k`
killing all of them. -/
theorem dominate_finset {I : Type w} [SmallCategory I] [IsFiltered I]
    (F : I ⥤ ModuleCat.{w} R) (i : I) (T : Type*) (y : T → ToType (F.obj i)) (s : Finset T)
    (h : ∀ x ∈ s, (ConcreteCategory.hom (colimit.ι F i)) (y x) = 0) :
    ∃ (k : I) (g : i ⟶ k), ∀ x ∈ s, (ConcreteCategory.hom (F.map g)) (y x) = 0 := by
  classical
  induction s using Finset.induction with
  | empty => exact ⟨i, 𝟙 i, by simp⟩
  | insert a s ha ih =>
      obtain ⟨k, g, hk⟩ := ih (fun x hx => h x (Finset.mem_insert_of_mem hx))
      obtain ⟨ka, ga, hga⟩ := (colimit_ι_apply_eq_zero_iff R F i (y a)).mp
        (h a (Finset.mem_insert_self a s))
      let m := IsFiltered.max k ka
      let lk : k ⟶ m := IsFiltered.leftToMax k ka
      let la : ka ⟶ m := IsFiltered.rightToMax k ka
      let e := IsFiltered.coeqHom (g ≫ lk) (ga ≫ la)
      have hcond : g ≫ lk ≫ e = ga ≫ la ≫ e := by
        simpa using IsFiltered.coeq_condition (g ≫ lk) (ga ≫ la)
      refine ⟨_, g ≫ lk ≫ e, fun x hx => ?_⟩
      rcases Finset.mem_insert.mp hx with rfl | hxs
      · simp [hcond, hga]
      · simp [hk x hxs]

/-- **(1) ⇒ (2).** If `N` is a finite `R`-module then the comparison map `Θ_N` is
injective (a monomorphism) for every small filtered colimit.

## Rigorous informal proof (Stacks 0G8N, forward direction)

Let `x₁, …, xₘ` be a finite generating set for `N` (exists since `N` is finite).
Fix a small filtered diagram `F : I ⥤ ModuleCat R` with colimit `M = colimit F`
and structure maps `ψᵢ = colimit.ι F i : Mᵢ → M`.

By `ModuleCat.mono_iff_injective` it suffices to prove the underlying `R`-linear
map of `Θ_N = comparisonMap R N F` is injective. As it is a module homomorphism,
injectivity is equivalent to: every `z : colim_i Hom_R(N, Mᵢ)` with `Θ_N z = 0`
satisfies `z = 0`.

* **Represent `z`.** Since `forget (ModuleCat R)` preserves filtered colimits
  (`ModuleCat.FilteredColimits.forget_preservesFilteredColimits`), the colimit is
  a filtered concrete colimit, so by `Concrete.colimit_exists_rep` there is an
  index `i` and `f : (F ⋙ homFunctor R N).obj i = Hom_R(N, Mᵢ)`, i.e. an
  `R`-linear map `f : N → Mᵢ`, with `z = colimit.ι (F ⋙ homFunctor R N) i f`.

* **Read off the hypothesis.** By `comparisonMap_fac`,
  `Θ_N z = (homFunctor R N).map (ψᵢ) f`. The functor `homFunctor R N` acts on
  morphisms by post-composition (`homFunctor_map_apply` / `Linear.rightComp`),
  so this equals `f ≫ ψᵢ : N → M`, i.e. `ψᵢ ∘ f`. Thus the hypothesis `Θ_N z = 0`
  says `ψᵢ ∘ f = 0` as a map `N → M`; evaluating at each generator,
  `ψᵢ (f xⱼ) = 0` in `M` for all `j`.

* **Filtered zero criterion, generator by generator.** For each `j`, applying
  `Concrete.colimit_rep_eq_iff_exists` to the colimit `M = colimit F` (with the
  elements `f xⱼ : Mᵢ` and `0 : Mᵢ`, and using `(F.map g) 0 = 0`), the equality
  `ψᵢ (f xⱼ) = ψᵢ 0 = 0` yields some `kⱼ` and a morphism `gⱼ : i ⟶ kⱼ` with
  `(F.map gⱼ) (f xⱼ) = 0` in `M_{kⱼ}`.

* **Dominate by one index.** `I` is filtered, so there is a single `k` together
  with morphisms `i ⟶ k` factoring through each `kⱼ` (use `IsFiltered.sup` /
  `IsFiltered.toSup` over the finitely many `kⱼ`, or iterate `IsFiltered.max`).
  Let `g : i ⟶ k` be the resulting morphism. By functoriality and the previous
  step, `(F.map g) (f xⱼ) = 0` in `M_k` for every generator `xⱼ`.

* **Vanishing on a spanning set.** The composite `f ≫ F.map g : N → M_k` is an
  `R`-linear map vanishing on the generating set `{x₁,…,xₘ}`, hence vanishes on
  `span R {x₁,…,xₘ} = N` (use `LinearMap.ext` after reducing to the spanning set,
  e.g. via `Submodule.span_le`/`LinearMap.eqOn_span` and `Module.Finite` giving a
  spanning finite set). Therefore `f ≫ F.map g = 0` as a morphism `N → M_k`, i.e.
  `(homFunctor R N).map (F.map g) f = 0`.

* **Conclude `z = 0`.** Now `(F ⋙ homFunctor R N).map g f = 0`. Applying
  `Concrete.colimit_rep_eq_iff_exists` *in the colimit of the Hom-diagram* (the
  elements `f : Hom_R(N,Mᵢ)` and `0`, using the morphism `g : i ⟶ k`), this gives
  `colimit.ι (F ⋙ homFunctor R N) i f = colimit.ι (F ⋙ homFunctor R N) i 0 = 0`,
  i.e. `z = 0`.

This proves injectivity, hence `Mono (comparisonMap R N F)`, for every `F`.
-/
@[ega "IV 8.5.2.1" "Finite-type clause"]
theorem finite_imp_injective (N : ModuleCat.{w} R) [Module.Finite R N] :
    InjectiveForAllFilteredColimits R N := by
  intro I _ _ F
  rw [ModuleCat.mono_iff_injective]
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨i, f, rfl⟩ := Concrete.colimit_exists_rep (F ⋙ homFunctor R N) z
  -- read hypothesis through comparisonMap_fac
  have hzf : f ≫ colimit.ι F i = 0 := by
    rwa [← CategoryTheory.comp_apply, comparisonMap_fac, homFunctor_map_apply] at hz
  -- hzf : f ≫ colimit.ι F i = 0  (a ModuleCat morphism N ⟶ colimit F)
  -- so for every x : N, (colimit.ι F i) (f x) = 0 in colimit F.
  have hgen : ∀ x : N, (colimit.ι F i) ((ConcreteCategory.hom (f : N ⟶ F.obj i)) x) = 0 := by
    intro x
    have := congrArg (fun (m : N ⟶ colimit F) => (ConcreteCategory.hom m) x) hzf
    simpa [ModuleCat.hom_comp] using this
  -- finite spanning set of N
  obtain ⟨s, hs⟩ := Module.finite_def.mp (inferInstance : Module.Finite R (N : Type w))
  -- dominate the finitely many generators
  obtain ⟨k, g, hg⟩ := dominate_finset R F i N (ConcreteCategory.hom (f : N ⟶ F.obj i)) s
    (fun x _ => hgen x)
  -- The composite f ≫ F.map g : N ⟶ F.obj k vanishes on the spanning set, hence is 0.
  have hfg0 : (f : N ⟶ F.obj i) ≫ F.map g = 0 := by
    refine ModuleCat.hom_ext (LinearMap.ext_on hs fun x hx => ?_)
    rw [ModuleCat.hom_comp, ModuleCat.hom_zero]
    rw [LinearMap.comp_apply, LinearMap.zero_apply]
    exact hg x (Finset.mem_coe.mp hx)
  -- Conclude z = colimit.ι ... i f = 0.
  rw [(colimit_ι_apply_eq_zero_iff R _ i f).mpr ⟨k, g, ?_⟩]
  rw [Functor.comp_map, homFunctor_map_apply]
  exact hfg0

-- Auxiliary constructions for the converse direction (2) ⇒ (1).

/-- For a finite subset `E ⊆ N`, the submodule `N_E := span R E ⊆ N`. -/
abbrev witnessSub (N : ModuleCat.{w} R) (E : Finset N) : Submodule R N :=
  Submodule.span R (E : Set N)

/-- `E ⊆ E'` implies `N_E ⊆ N_{E'}` (monotonicity of `span`). -/
theorem witnessSub_mono (N : ModuleCat.{w} R) {E E' : Finset N} (h : E ≤ E') :
    witnessSub R N E ≤ witnessSub R N E' :=
  Submodule.span_mono (by exact_mod_cast h)

/-- The witness filtered diagram `F : Finset N ⥤ ModuleCat R`, sending a finite
subset `E ⊆ N` to the quotient `N / N_E`, with transition maps the canonical
surjections `N/N_E ↠ N/N_{E'}` for `E ⊆ E'`. -/
noncomputable abbrev witnessFunctor (N : ModuleCat.{w} R) : Finset N ⥤ ModuleCat.{w} R where
  obj E := ModuleCat.of R (N ⧸ witnessSub R N E)
  map {E E'} f := ModuleCat.ofHom (Submodule.factor (witnessSub_mono R N (leOfHom f)))

/-- The projection `π_E : N ⟶ N/N_E`, an element of `Hom_R(N, F.obj E)`. -/
noncomputable def witnessProj (N : ModuleCat.{w} R) (E : Finset N) :
    N ⟶ (witnessFunctor R N).obj E :=
  ModuleCat.ofHom ((witnessSub R N E).mkQ)

/-- The composite `π_E ∘ (transition map)` equals `π_{E'}` (`factor ∘ mkQ = mkQ`). -/
theorem witnessProj_comp (N : ModuleCat.{w} R) {E E' : Finset N} (f : E ⟶ E') :
    witnessProj R N E ≫ (witnessFunctor R N).map f = witnessProj R N E' := by
  ext x
  simp [witnessProj]

/-- The structure map of the colimit kills the class of any `x : N` coming from
`N/N_∅`: passing to `N/N_{x}` makes `x` vanish (since `x ∈ span {x}`). -/
theorem witnessProj_emptyset_zero (N : ModuleCat.{w} R) (x : N) :
    (colimit.ι (witnessFunctor R N) (∅ : Finset N))
      ((witnessSub R N (∅ : Finset N)).mkQ x) = 0 := by
  have hle : (∅ : Finset N) ≤ ({x} : Finset N) := by simp
  have hw := colimit.w (witnessFunctor R N) (homOfLE hle)
  have key : (colimit.ι (witnessFunctor R N) (∅ : Finset N))
      ((witnessSub R N (∅ : Finset N)).mkQ x)
      = (colimit.ι (witnessFunctor R N) ({x} : Finset N))
          ((witnessSub R N ({x} : Finset N)).mkQ x) := by
    rw [← hw, CategoryTheory.comp_apply]
    exact congrArg _ (Submodule.factor_mk (witnessSub_mono R N hle) x)
  rw [key]
  have hx : x ∈ witnessSub R N ({x} : Finset N) := Submodule.subset_span (by simp)
  rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero _).mpr hx, map_zero]

/-- **(2) ⇒ (1).** If the comparison map `Θ_N` is injective for every small filtered
colimit then `N` is a finite `R`-module.

## Rigorous informal proof (Stacks 0G8N, converse direction)

We construct one specific filtered colimit on which injectivity of `Θ_N` forces
`N` to be finite.

* **Index category.** Let `I` be the set of finite subsets `E ⊆ N`, ordered by
  inclusion (a directed/filtered preorder: it is nonempty — `∅ ∈ I` — and any two
  `E, E'` are dominated by `E ∪ E'`). For `E ∈ I` let `N_E := span R E ⊆ N`, the
  submodule generated by `E`.

* **Diagram.** Define `F : I ⥤ ModuleCat R` by `F.obj E = N / N_E` (the quotient
  module) and, for `E ⊆ E'` (so `N_E ⊆ N_{E'}`), the canonical surjection
  `N/N_E ↠ N/N_{E'}` (`Submodule.mapQ`/`Submodule.factor` of the identity). These
  are functorial.

* **The colimit is `0`.** `M := colimit F = colim_E N/N_E = 0`. Indeed, by the
  filtered colimit zero criterion every class is killed: a class represented by
  `[x] ∈ N/N_E` maps to `0` in `N/N_{E'}` for `E' = E ∪ {x}`, since then
  `x ∈ N_{E'}`. Hence the structure maps `ψ_E` all factor through `0`, so the
  colimit `M` is the zero module (formally: it is generated by the images of the
  `ψ_E`, all of which are `0`; or `Hom_R(N, M) = 0`).

* **A class mapping to 0.** For each `E`, the projection `π_E : N → N/N_E` is an
  element of `Hom_R(N, N/N_E) = (F ⋙ homFunctor R N).obj E`. Let
  `z := colimit.ι (F ⋙ homFunctor R N) E₀ π_{E₀}` for `E₀ = ∅` be the corresponding
  class in `colim_E Hom_R(N, N/N_E)`. Then `Θ_N z = ψ_{E₀} ∘ π_{E₀} : N → M`, a map
  into the zero module `M`, hence `Θ_N z = 0`.

* **Injectivity bites.** Apply hypothesis `h` to this `F`:
  `Mono (comparisonMap R N F)`, equivalently injective. From `Θ_N z = 0` we get
  `z = 0`, i.e. `colimit.ι (F ⋙ homFunctor R N) E₀ π_{E₀} = 0` in
  `colim_E Hom_R(N, N/N_E)`. By the filtered colimit zero criterion
  (`Concrete.colimit_rep_eq_iff_exists` with `0`), there is `E ⊇ E₀` and the
  transition map `i_E : E₀ ⟶ E` with `(F ⋙ homFunctor R N).map i_E π_{E₀} = 0`,
  i.e. the composite `N → N/N_{E₀} → N/N_E` is the zero map. But that composite is
  exactly `π_E : N → N/N_E`. So `π_E = 0`, i.e. `N/N_E = 0`, i.e. `N_E = N`.

* **Conclusion.** `N = N_E = span R E` with `E` finite, so `N` is finitely
  generated, i.e. `Module.Finite R N`.
-/
theorem injective_imp_finite (N : ModuleCat.{w} R)
    (h : InjectiveForAllFilteredColimits R N) : Module.Finite R N := by
  set F := witnessFunctor R N with hF
  -- The distinguished class `z := [π_∅] ∈ colim_E Hom_R(N, N/N_E)`.
  set z := colimit.ι (F ⋙ homFunctor R N) (∅ : Finset N) (witnessProj R N (∅ : Finset N)) with hz
  -- Step A: `Θ_N z = 0`, because it equals `π_∅ ≫ ψ_∅ : N → colimit F`, which is
  -- the zero map (each class `[x]` already dies in `N/N_{x}`).
  have hStepA : (comparisonMap R N F) z = 0 := by
    rw [hz, ← CategoryTheory.comp_apply, comparisonMap_fac, homFunctor_map_apply]
    ext x
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, witnessProj, ModuleCat.hom_ofHom,
      ModuleCat.hom_zero, LinearMap.zero_apply]
    exact witnessProj_emptyset_zero R N x
  -- Step B: injectivity of `Θ_N` (from the hypothesis) forces `z = 0`.
  have hmono := h (Finset N) F
  rw [ModuleCat.mono_iff_injective] at hmono
  have hz0 : z = 0 := hmono (by rw [hStepA, map_zero])
  -- Step C: filtered colimit zero criterion gives a finite `E ⊇ ∅` with `π_E = 0`.
  obtain ⟨k, f, hfg⟩ := (colimit_ι_apply_eq_zero_iff R _ _ _).mp hz0
  -- The left-hand side `(F ⋙ Hom)(f) π_∅` is exactly `π_k`.
  have hLHS : (ConcreteCategory.hom ((F ⋙ homFunctor R N).map f)) (witnessProj R N (∅ : Finset N))
      = witnessProj R N k := by
    rw [Functor.comp_map, homFunctor_map_apply]
    exact witnessProj_comp R N f
  rw [hLHS] at hfg
  -- So `π_k = 0`, i.e. `N/N_k = 0`, i.e. `N_k = ⊤`.
  have hmkQ : (witnessSub R N k).mkQ = 0 := by
    have := congrArg ModuleCat.Hom.hom hfg
    simpa [witnessProj] using this
  have htop : witnessSub R N k = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx : (witnessSub R N k).mkQ x = 0 := by rw [hmkQ]; rfl
    rwa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hx
  -- Step D: `N = span R k` with `k` finite, hence `N` is finitely generated.
  rw [Module.finite_def, Submodule.fg_def]
  exact ⟨k, k.finite_toSet, htop⟩

/-- **Stacks Tag 0G8N.** An `R`-module `N` is finite (finitely generated) if and
only if for every filtered colimit `M = colim_i M_i` of `R`-modules the canonical
comparison map `Θ_N : colim_i Hom_R(N, M_i) → Hom_R(N, M)` is injective. -/
@[stacks 0G8N, ega "IV 8.5.2.1" "Forward implication"]
theorem finite_iff_comparisonMap_injective (N : ModuleCat.{w} R) :
    Module.Finite R N ↔ InjectiveForAllFilteredColimits R N :=
  ⟨fun _ => finite_imp_injective R N, injective_imp_finite R N⟩

end Stacks.Module.FinitenessViaHomColimit

/-!
# Finite presentation of a module characterized by bijectivity of the Hom comparison map

Let `R` be a commutative unital ring and `N` an `R`-module. The following are equivalent
(Stacks Tag 0G8P):

1. `N` is a finitely presented `R`-module.
2. For every directed (filtered) system `(Mᵢ, f_{ij})_{i ∈ I}` of `R`-modules with colimit
   `M = colim_i Mᵢ`, the canonical comparison map
   `Φ : colim_i Hom_R(N, Mᵢ) → Hom_R(N, M)` is bijective.

## Conventions

* Finite presentation is `Module.FinitePresentation R N`: there is a finite generating set
  `S ⊆ N` whose associated map `R^S → N` has finitely generated kernel, equivalently an exact
  sequence `R^m → R^n → N → 0`.
* The colimit of a directed system of modules is `Module.DirectLimit G f`, with canonical
  `R`-linear maps `Module.DirectLimit.of R ι G f i : G i →ₗ[R] Module.DirectLimit G f`. Here
  `ι` is a directed preorder and the `f i j hij : G i →ₗ[R] G j` form a `DirectedSystem`.
* A directed system `(Mᵢ, f_{ij})` is encoded by an index `Preorder ι` that is
  `IsDirectedOrder`, `Nonempty` and has `DecidableEq` (required by the `Module.DirectLimit`
  API), a family `G : ι → Type u` of `R`-modules, and maps
  `f : (i j : ι) → i ≤ j → G i →ₗ[R] G j` with a `DirectedSystem` instance, i.e.
  `f i i = id` and `f j k ∘ f i j = f i k`.

## The Hom system and the comparison map

The `R`-modules `Hom_R(N, Mᵢ)` form a directed system via post-composition with `f_{ij}`,
i.e. `LinearMap.compRight R (f i j hij)`, with colimit
`Module.DirectLimit (fun i => N →ₗ[R] G i)` for that system. Post-composition with the
canonical maps `gᵢ = of R ι G f i` induces, by the universal property
(`Module.DirectLimit.lift`), the comparison map
`Φ : colim_i Hom_R(N, Mᵢ) → Hom_R(N, colim_i Mᵢ)`, characterized on representatives by
`Φ [φ] = gᵢ ∘ φ`. Since all transition maps and canonical maps are `R`-linear, `Φ` is
`R`-linear; the content of the theorem is its bijectivity.
-/

universe u

open Module
/-- The canonical comparison map
`Φ : colim_i Hom_R(N, M_i) → Hom_R(N, colim_i M_i)`,
induced by the universal property of the colimit of the `Hom`-system together with
the canonical maps `g_i = Module.DirectLimit.of`. On a representative `φ : N →ₗ[R] M_i`
it is given by `Φ [φ] = g_i ∘ φ` (see `comparisonMap_of` below). -/
@[sga "3 VIIB 0.3.5"]
noncomputable def homColimComparison
    {R : Type*} [CommSemiring R] {N : Type*} [AddCommMonoid N] [Module R N]
    {ι : Type*} [Preorder ι] [DecidableEq ι] (G : ι → Type*)
    [(i : ι) → AddCommMonoid (G i)] [(i : ι) → Module R (G i)]
    (f : (i j : ι) → i ≤ j → G i →ₗ[R] G j) :
    Module.DirectLimit (fun i => N →ₗ[R] G i)
        (fun i j hij => LinearMap.compRight R (f i j hij)) →ₗ[R]
      (N →ₗ[R] Module.DirectLimit G f) :=
  Module.DirectLimit.lift R ι (fun i => N →ₗ[R] G i)
    (fun i j hij => LinearMap.compRight R (f i j hij))
    (fun i => LinearMap.compRight R (Module.DirectLimit.of R ι G f i))
    (by
      intro i j hij φ
      ext n
      simp [Module.DirectLimit.of_f])

/-- Correctness of the comparison map: on a representative `φ : N →ₗ[R] M_i`, the value
`Φ [φ]` is the post-composition `g_i ∘ φ` with the canonical map into the colimit.
This characterizes `homColimComparison` as the canonical comparison map `Φ`. -/
theorem comparisonMap_of
    {R : Type*} [CommSemiring R] {N : Type*} [AddCommMonoid N] [Module R N]
    {ι : Type*} [Preorder ι] [DecidableEq ι]
    (G : ι → Type*) [(i : ι) → AddCommMonoid (G i)] [(i : ι) → Module R (G i)]
    (f : (i j : ι) → i ≤ j → G i →ₗ[R] G j)
    (i : ι) (φ : N →ₗ[R] G i) :
    homColimComparison G f
        (Module.DirectLimit.of R ι (fun i => N →ₗ[R] G i)
          (fun i j hij => LinearMap.compRight R (f i j hij)) i φ) =
      (Module.DirectLimit.of R ι G f i).comp φ := by
  rw [homColimComparison, Module.DirectLimit.lift_of, LinearMap.compRight_apply]

/-- A finite module has a finite spanning family whose linear combination map is surjective. -/
private theorem exists_fin_span_eq_top_and_surjective (R : Type*) [Semiring R] (N : Type*)
    [AddCommMonoid N] [Module R N] [Module.Finite R N] :
    ∃ (n : ℕ) (s : Fin n → N), Submodule.span R (Set.range s) = ⊤ ∧
      Function.Surjective (Finsupp.linearCombination R s) := by
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := R) (M := N)
  exact ⟨n, s, hs, by rw [← LinearMap.range_eq_top, Finsupp.range_linearCombination, hs]⟩

/-- Finitely many elements of `G i` that vanish in the direct limit all vanish at a common
stage `j ≥ i`. -/
theorem Module.DirectLimit.exists_forall_map_eq_zero {R : Type*} [Semiring R] {ι : Type*}
    [Preorder ι] [DecidableEq ι] [IsDirectedOrder ι] {G : ι → Type*}
    [(i : ι) → AddCommMonoid (G i)] [(i : ι) → Module R (G i)]
    {f : (i j : ι) → i ≤ j → G i →ₗ[R] G j} [DirectedSystem G (fun i j h => f i j h)]
    {α : Type*} [Finite α] (i : ι) (x : α → G i) (hx : ∀ a, of R ι G f i (x a) = 0) :
    ∃ j, ∃ hij : i ≤ j, ∀ a, f i j hij (x a) = 0 := by
  have := Nonempty.intro i
  have := Fintype.ofFinite α
  choose j hij hj using fun a => of.zero_exact (hx a)
  obtain ⟨k, hk⟩ := Finset.exists_le (Finset.univ.image j)
  obtain ⟨l, hil, hkl⟩ := directed_of (· ≤ ·) i k
  refine ⟨l, hil, fun a => ?_⟩
  rw [← DirectedSystem.map_map' f (hij a)
    ((hk _ (Finset.mem_image_of_mem _ (Finset.mem_univ a))).trans hkl), hj a, map_zero]

/-- Injectivity of the comparison map, given that `N` is finitely generated.
If `φ : N →ₗ[R] G i` becomes zero after post-composing with the canonical map into
the colimit, then its class in the colimit of the `Hom`-system is already zero. -/
@[ega "IV 8.5.2" "(i), special case", ega "IV 8.5.2.1" "more general"]
theorem comparison_injective
    {R : Type*} [CommRing R] {N : Type*} [AddCommGroup N] [Module R N]
    [Module.Finite R N]
    {ι : Type*} [Preorder ι] [DecidableEq ι] [IsDirectedOrder ι]
    (G : ι → Type*) [(i : ι) → AddCommGroup (G i)] [(i : ι) → Module R (G i)]
    (f : (i j : ι) → i ≤ j → G i →ₗ[R] G j)
    [DirectedSystem G (fun i j h => f i j h)]
    (i : ι) (φ : N →ₗ[R] G i)
    (hφ : (Module.DirectLimit.of R ι G f i).comp φ = 0) :
    Module.DirectLimit.of R ι (fun i => N →ₗ[R] G i)
      (fun i j hij => LinearMap.compRight R (f i j hij)) i φ = 0 := by
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := R) (M := N)
  obtain ⟨j, hij, hj⟩ := Module.DirectLimit.exists_forall_map_eq_zero i (φ ∘ s) fun k => by
    simpa using LinearMap.congr_fun hφ (s k)
  rw [← Module.DirectLimit.of_f (hij := hij),
    show LinearMap.compRight R (f i j hij) φ = 0 from
      LinearMap.ext_on hs (by rintro _ ⟨k, rfl⟩; simpa using hj k), map_zero]

/-- Surjectivity of the comparison map, given that `N` is finitely presented.
Every linear map `ψ : N →ₗ[R] colim G` factors, up to the canonical maps, through
some `G j`. -/
@[ega "IV 8.5.2.1" "surjectivity", sga "3 VIIB 0.3.5" "(3)"]
theorem homColimComparison_surjective
    {R : Type*} [Ring R] {N : Type*} [AddCommGroup N] [Module R N]
    [Module.FinitePresentation R N]
    {ι : Type*} [Preorder ι] [DecidableEq ι] [IsDirectedOrder ι] [Nonempty ι]
    (G : ι → Type*) [(i : ι) → AddCommGroup (G i)] [(i : ι) → Module R (G i)]
    (f : (i j : ι) → i ≤ j → G i →ₗ[R] G j)
    [DirectedSystem G (fun i j h => f i j h)]
    (ψ : N →ₗ[R] Module.DirectLimit G f) :
    ∃ (j : ι) (φ : N →ₗ[R] G j), (Module.DirectLimit.of R ι G f j).comp φ = ψ := by
  obtain ⟨n, s, -, hpsurj⟩ := exists_fin_span_eq_top_and_surjective R N
  set p : (Fin n →₀ R) →ₗ[R] N := Finsupp.linearCombination R s with hp
  obtain ⟨t, ht⟩ := Module.FinitePresentation.fg_ker p hpsurj
  choose ii xx hxx using fun k => Module.DirectLimit.exists_of (ψ (s k))
  obtain ⟨i, hi⟩ := Finset.exists_le (Finset.univ.image ii)
  let q : (Fin n →₀ R) →ₗ[R] G i := Finsupp.linearCombination R fun k =>
    f (ii k) i (hi _ (Finset.mem_image_of_mem _ (Finset.mem_univ k))) (xx k)
  have hcomp : (Module.DirectLimit.of R ι G f i).comp q = ψ.comp p := by
    ext k
    simp [q, p, hxx]
  have hqp (w) : Module.DirectLimit.of R ι G f i (q w) = ψ (p w) := LinearMap.congr_fun hcomp w
  obtain ⟨j, hij, hj⟩ := Module.DirectLimit.exists_forall_map_eq_zero i (fun v : t => q v)
    fun v => by
      rw [hqp, (LinearMap.mem_ker.1 (ht ▸ Submodule.subset_span v.2 : v.1 ∈ p.ker)), map_zero]
  have hker : p.ker ≤ ((f i j hij).comp q).ker := by
    rw [← ht, Submodule.span_le]
    exact fun v hv => LinearMap.mem_ker.2 (hj ⟨v, hv⟩)
  refine ⟨j, p.ker.liftQ _ hker ∘ₗ (p.quotKerEquivOfSurjective hpsurj).symm.toLinearMap,
    LinearMap.ext fun a => ?_⟩
  obtain ⟨w, rfl⟩ := hpsurj a
  simpa [p.quotKerEquivOfSurjective_symm_apply hpsurj] using hqp w

/-- Abbreviation for the bijectivity hypothesis driving the reverse direction:
the comparison map is bijective for *every* directed system over a directed index
type living in the universe of `N`. -/
abbrev ComparisonBijective (R : Type u) [CommRing R] (N : Type u) [AddCommGroup N]
    [Module R N] : Prop :=
  ∀ {ι : Type u} [Preorder ι] [DecidableEq ι] [IsDirectedOrder ι] [Nonempty ι]
    (G : ι → Type u) [(i : ι) → AddCommGroup (G i)] [(i : ι) → Module R (G i)]
    (f : (i j : ι) → i ≤ j → G i →ₗ[R] G j)
    [DirectedSystem G (fun i j h => f i j h)],
    Function.Bijective (homColimComparison (R := R) (N := N) (ι := ι) G f)

/-- **Reverse direction, Step 1 (finite generation).**

Assume the comparison map is bijective for every directed system (`hbij`).
Then `N` is finitely generated, i.e. `Module.Finite R N`.

The argument (Stacks 0G8P, first half of (2) ⇒ (1)).
Write `N` as the filtered colimit of its finitely generated submodules. Concretely,
index by `ι := {P : Submodule R N // P.FG}` (a directed order: `Module.fgSystem`'s
`IsDirectedOrder` instance; nonempty since `⊥` is FG), with module family
`G P := ↥(P : Submodule R N)` and transition maps the inclusions `fgSystem R N`.
Mathlib's `Module.fgSystem.equiv R N : DirectLimit G f ≃ₗ[R] N` realizes `N` as this
colimit, and `Module.fgSystem.equiv_comp_of` says `equiv ∘ (of P) = P.subtype`.

Apply `hbij` to this system to get *surjectivity* of `homColimComparison`. Feed it the
map `ψ := (equiv).symm.toLinearMap : N →ₗ[R] DirectLimit G f` (well-defined because
`equiv` is an iso). Surjectivity of `homColimComparison`, together with
`Module.DirectLimit.exists_of` and `comparisonMap_of`, factors `ψ` through a finite
stage: there is `P : ι` and `φ : N →ₗ[R] ↥P` with `(of P).comp φ = ψ`.
Post-compose with `equiv`: `equiv ∘ of P ∘ φ = equiv ∘ ψ = id_N`, and by
`equiv_comp_of` the left side is `P.subtype ∘ φ`. Hence `P.subtype ∘ φ = id_N`, so
`P.subtype : ↥P → N` is surjective, i.e. its range `P` equals `⊤`. Since `P` is FG,
`⊤` is FG, i.e. `N` is finitely generated. -/
theorem reverse_finite
    {R : Type u} [CommRing R] {N : Type u} [AddCommGroup N] [Module R N]
    (hbij : ComparisonBijective R N) :
    Module.Finite R N := by
  classical
  let e := Module.fgSystem.equiv R N
  obtain ⟨z, hz⟩ := (hbij _ (Module.fgSystem R N)).surjective e.symm.toLinearMap
  obtain ⟨P, φ, rfl⟩ := Module.DirectLimit.exists_of z
  rw [comparisonMap_of] at hz
  have hP : (P : Submodule R N) = ⊤ := by
    refine eq_top_iff.2 fun x _ => ?_
    have := congr(e ($hz x))
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at this
    have h := LinearMap.congr_fun (Module.fgSystem.equiv_comp_of P) (φ x)
    rw [LinearMap.comp_apply, LinearEquiv.coe_coe, this] at h
    exact h ▸ (φ x).2
  exact Module.finite_def.mpr (hP ▸ P.property)

/-- The quotients `F ⧸ S i` by a monotone family of submodules form a directed system under
the maps `Submodule.factor`. -/
theorem Submodule.directedSystem_factor {R : Type*} [Ring R] {F : Type*} [AddCommGroup F]
    [Module R F] {ι : Type*} [Preorder ι] {S : ι → Submodule R F} (hS : Monotone S) :
    DirectedSystem (fun i => F ⧸ S i) (fun _ _ h => Submodule.factor (hS.imp h)) where
  map_self _ x := Submodule.Quotient.induction_on _ x fun _ => by simp
  map_map _ _ _ _ _ x := Submodule.factor_comp_apply _ _ x

/-- If a monotone family `S` of submodules of `F` lies in `K` and exhausts `K` above `i₀`, then
the projection `colim_i F ⧸ S i → F ⧸ K` has a linear right inverse. -/
theorem Submodule.exists_rightInverse_lift_factor {R : Type*} [Ring R] {F : Type*}
    [AddCommGroup F] [Module R F] {ι : Type*} [Preorder ι] [DecidableEq ι]
    {S : ι → Submodule R F} (hS : Monotone S) {K : Submodule R F} (hSK : ∀ i, S i ≤ K)
    (i₀ : ι) (hK : ∀ x ∈ K, ∃ i, i₀ ≤ i ∧ x ∈ S i) :
    ∃ s : F ⧸ K →ₗ[R] Module.DirectLimit (fun i => F ⧸ S i) (fun _ _ h => factor (hS.imp h)),
      ∀ y, Module.DirectLimit.lift R ι _ _ (fun i => factor (hSK i))
        (fun _ _ _ x => factor_comp_apply _ _ x) (s y) = y := by
  refine ⟨K.liftQ ((Module.DirectLimit.of R ι _ _ i₀).comp (S i₀).mkQ) fun x hx => ?_,
    fun y => Submodule.Quotient.induction_on _ y fun x => ?_⟩
  · obtain ⟨i, hi, hxi⟩ := hK x hx
    rw [LinearMap.mem_ker, LinearMap.comp_apply, ← Module.DirectLimit.of_f (hij := hi),
      factor_mk, mkQ_apply, (Quotient.mk_eq_zero _).2 hxi, map_zero]
  · rw [liftQ_apply, LinearMap.comp_apply, Module.DirectLimit.lift_of, factor_mk, mkQ_apply]

/-- A retract of a finitely presented module is finitely presented. -/
theorem Module.FinitePresentation.of_retract {R : Type*} [Ring R] {M N : Type*}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [FinitePresentation R M]
    (i : N →ₗ[R] M) (r : M →ₗ[R] N) (h : r ∘ₗ i = LinearMap.id) : FinitePresentation R N := by
  have hri (x : N) : r (i x) = x := LinearMap.congr_fun h x
  let g : M →ₗ[R] LinearMap.ker r :=
    (LinearMap.id - i ∘ₗ r).codRestrict _ fun y => by simp [hri]
  refine finitePresentation_of_split_exact i g (LinearMap.ker r).subtype ?_
    (Function.LeftInverse.injective hri) fun y => ⟨fun hy => ⟨r y, ?_⟩, ?_⟩
  · ext z
    simp [g]
  · exact (sub_eq_zero.1 (by simpa [g] using congr_arg Subtype.val hy)).symm
  · rintro ⟨a, rfl⟩
    exact Subtype.ext <| by simp [g, hri]


/-- **Reverse direction, Step 2 (finitely generated kernel).**

Assume the comparison map is bijective for every directed system (`hbij`) and let
`p : (Fin n →₀ R) →ₗ[R] N` be surjective with kernel `K`. For a finitely generated submodule `Q`
of `K` let `S Q ⊆ Fin n →₀ R` be its image. The quotients `(Fin n →₀ R) ⧸ S Q` form a directed
system of finitely presented modules (`Submodule.directedSystem_factor`), and the projection from
its colimit onto `(Fin n →₀ R) ⧸ K ≃ N` has a linear right inverse
(`Submodule.exists_rightInverse_lift_factor`). Surjectivity of the comparison map factors the
resulting map `N → colim` through one stage `(Fin n →₀ R) ⧸ S Q`; composing with the projection
to `(Fin n →₀ R) ⧸ K ≃ N` shows that `N` is a retract of that finitely presented module. Hence `N`
is finitely presented (`Module.FinitePresentation.of_retract`) and `K` is finitely generated
(`Module.FinitePresentation.fg_ker`). -/
theorem reverse_fg_ker
    {R : Type u} [CommRing R] {N : Type u} [AddCommGroup N] [Module R N]
    (hbij : ComparisonBijective R N)
    {n : ℕ} (p : (Fin n →₀ R) →ₗ[R] N) (hp : Function.Surjective p) :
    (LinearMap.ker p).FG := by
  classical
  let S : {Q : Submodule R (LinearMap.ker p) // Q.FG} → Submodule R (Fin n →₀ R) :=
    fun Q => Q.1.map (LinearMap.ker p).subtype
  have hS : Monotone S := fun _ _ h => Submodule.map_mono h
  have hSK Q : S Q ≤ LinearMap.ker p := Submodule.map_subtype_le _ _
  have := Submodule.directedSystem_factor hS
  obtain ⟨s, hs⟩ := Submodule.exists_rightInverse_lift_factor hS hSK ⟨⊥, Submodule.fg_bot⟩
    fun x hx => ⟨⟨_, Submodule.fg_span_singleton ⟨x, hx⟩⟩, Subtype.mk_le_mk.2 bot_le, ⟨x, hx⟩,
      Submodule.mem_span_singleton_self _, rfl⟩
  let e := p.quotKerEquivOfSurjective hp
  obtain ⟨z, hz⟩ := (hbij _ fun _ _ h => Submodule.factor (hS.imp h)).surjective
    (s ∘ₗ e.symm.toLinearMap)
  obtain ⟨Q, φ, rfl⟩ := Module.DirectLimit.exists_of z
  rw [comparisonMap_of] at hz
  have : Module.FinitePresentation R (_ ⧸ S Q) :=
    Module.finitePresentation_of_free_of_surjective (S Q).mkQ (S Q).mkQ_surjective
      (by rw [Submodule.ker_mkQ]; exact Q.2.map _)
  have := Module.FinitePresentation.of_retract φ
    (e.toLinearMap ∘ₗ Submodule.factor (hSK Q)) <| by
      ext a
      have h := congr(Module.DirectLimit.lift R _ _ _ (fun i => Submodule.factor (hSK i))
        (fun _ _ _ x => Submodule.factor_comp_apply _ _ x) ($hz a))
      simp only [LinearMap.comp_apply, Module.DirectLimit.lift_of, hs] at h
      simp [h]
  exact Module.FinitePresentation.fg_ker p hp

/-- The Hom comparison map is bijective for a finitely presented module, with no
universe restrictions on the directed system. -/
theorem homColimComparison_bijective
    {R : Type*} [CommRing R] {N : Type*} [AddCommGroup N] [Module R N]
    [Module.FinitePresentation R N]
    {ι : Type*} [Preorder ι] [DecidableEq ι] [IsDirectedOrder ι] [Nonempty ι]
    (G : ι → Type*) [(i : ι) → AddCommGroup (G i)] [(i : ι) → Module R (G i)]
    (f : (i j : ι) → i ≤ j → G i →ₗ[R] G j) [DirectedSystem G (fun i j h => f i j h)] :
    Function.Bijective (homColimComparison (N := N) G f) := by
  refine ⟨?_, fun ψ => ?_⟩
  · rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro z hz
    obtain ⟨i, φ, rfl⟩ := Module.DirectLimit.exists_of z
    rw [LinearMap.mem_ker, comparisonMap_of] at hz
    exact comparison_injective G f i φ hz
  · obtain ⟨j, φ, hφ⟩ := homColimComparison_surjective (R := R) (N := N) G f ψ
    exact ⟨Module.DirectLimit.of R ι (fun i => N →ₗ[R] G i)
      (fun i j hij => LinearMap.compRight R (f i j hij)) j φ, by rwa [comparisonMap_of]⟩

/-- **Stacks Tag 0G8P.** An `R`-module `N` is finitely presented if and only if for
every directed (filtered) system of `R`-modules the canonical comparison map
`Φ : colim_i Hom_R(N, M_i) → Hom_R(N, colim_i M_i)` is bijective.

We quantify over index types `ι` and module families `G` in the universe `u` of `R` and `N`.
The forward direction holds for directed systems in any universe. The converse uses the system
of finitely generated submodules of `N`, which lives in the universe of `N`, and the system of
quotients `(Fin n →₀ R) ⧸ S Q`, which lives in the universe of `R`. -/
@[stacks 0G8P,
  ega "IV 8.5.2" "(i), special case",
  ega "IV 8.5.2.1" "more general",
  sga "3 VIIB 0.3.5" "(3), special case"]
theorem finitePresentation_iff_comparisonMap_bijective
    (R : Type u) [CommRing R] (N : Type u) [AddCommGroup N] [Module R N] :
    Module.FinitePresentation R N ↔
      ∀ {ι : Type u} [Preorder ι] [DecidableEq ι] [IsDirectedOrder ι] [Nonempty ι]
        (G : ι → Type u) [(i : ι) → AddCommGroup (G i)] [(i : ι) → Module R (G i)]
        (f : (i j : ι) → i ≤ j → G i →ₗ[R] G j)
        [DirectedSystem G (fun i j h => f i j h)],
        Function.Bijective (homColimComparison (R := R) (N := N) (ι := ι) G f) := by
  refine ⟨fun _ _ _ _ _ _ G _ _ f _ => homColimComparison_bijective G f, fun hbij => ?_⟩
  have := reverse_finite hbij
  obtain ⟨n, s, -, hp⟩ := exists_fin_span_eq_top_and_surjective R N
  exact Module.finitePresentation_of_free_of_surjective _ hp (reverse_fg_ker hbij _ hp)
