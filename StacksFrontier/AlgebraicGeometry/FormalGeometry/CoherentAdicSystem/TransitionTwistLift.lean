module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.TransitionTwistSurjectivity
public import StacksFrontier.AlgebraicGeometry.SectionRingGeometric.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.MonoidalInduced

/-!
# Lifting a family of twisted sections up the tower of a coherent adic system

The generation step of [Stacks, Tag 0885] that follows the cohomological one. Let `𝓕` be a
coherent adic system along an ideal sheaf on a scheme `X`, let `N` be an `𝒪_X`-module and let `U`
be an open of `X`. Suppose that each twisted transition map is surjective on sections over `U`:

  `Γ(U, 𝓕_{n+1} ⊗ N) ⟶ Γ(U, 𝓕_n ⊗ N)`  surjective, for every `n`.

Then any family `s : ι → Γ(U, 𝓕_0 ⊗ N)` of sections at the bottom of the tower extends to a
family at *every* level, compatible with the transition maps and equal to `s` at level `0`. This
is the step the twisted mapping-out property of [Stacks, Tag 0885] consumes: a morphism from a
finite direct sum of negative twists into the system is exactly such a compatible family, and
`Stacks.Coherent.epi_iff_epi_app_zero` ([Stacks, Tag 087Y]) then reduces its surjectivity to the
single level `0`, where `σ 0 = s` puts the given generating family back.

## Main results

* `Stacks.Coherent.exists_compatible_sections_tensorRight_transition_of_surjective` — the
  lifting itself: the compatible family `σ` with `σ 0 = s`.
* `Stacks.Coherent.app_tensorRight_transition_eq_of_le` — a family compatible with the
  successive transitions is compatible with *every* transition `𝓕_n ⟶ 𝓕_m`, `m ≤ n`.
* `Stacks.Coherent.exists_compatible_sections_tensorRight_transition_tensorPowModule` — the
  uniform form for `f : X ⟶ Spec A` proper over a Noetherian base and `L` an `f`-ample
  invertible module: one `d₀` such that for every `d ≥ d₀` every family of global sections of
  `𝓕_0 ⊗ L ^⊗ d` lifts to a compatible family along the whole tower.
* `Stacks.Coherent.exists_compatible_sections_whiskerRight_tensorPowModule` — **the same in the
  monoidal spelling**, which is the one the mapping-out property of [Stacks, Tag 0885] consumes:
  the sections are elements of `Γ(𝓕_n ⊗ L ^⊗ d, ⊤)` and the transition map is the right
  whiskering `𝓕_{n+1} ⟶ 𝓕_n ▷ L ^⊗ d` read on sections by
  `AlgebraicGeometry.Scheme.Modules.Hom.app`.
* `Stacks.Coherent.tensorRightModulesIso` and
  `Stacks.Coherent.whiskerRight_comp_tensorRightModulesIso` — the comparison of the two
  spellings of the twist and its naturality, and
  `Stacks.Coherent.surjective_app_whiskerRight_of_surjective_app_tensorRightModules` — the
  transport of surjectivity across it.

## Implementation notes

**No generation hypothesis, and none is needed.** The family `s` is taken bare: nothing is
assumed about it, in particular not that it generates `𝓕_0 ⊗ N`. Generation is a property of
`s` alone, and the clause `σ 0 = s` of the conclusion transports it — or any other property of
`s` — to level `0` of the lifted family, which by [Stacks, Tag 087Y] is the only level at which
it has to be checked. Assuming generation here would be an unused hypothesis.

**Nor invertibility of the twist, nor coherence.** The only input is the surjectivity, supplied
as a hypothesis; `Stacks.Coherent.surjective_app_tensorRight_transition_of_isZero_Hgroup` and
`Stacks.Coherent.exists_surjective_app_tensorRight_transition_tensorPowModule` are where
invertibility, properness and ampleness are used, and the last result here is the composite with
the second of those. The index type `ι` is arbitrary — the induction is indifferent to it, so
finiteness of the generating family is not assumed either; `Fin t` is the instance [Stacks, Tag
0885] uses.

**The induction is a `Nat.rec` on the dependent family.** The sections at level `n` live in a
type that varies with `n`, so the lifted family is not built by `induction` on a goal but as a
term `Nat.rec` over the motive `fun n => ι → Γ(U, 𝓕_n ⊗ N)`, each successor stage applying
`Function.surjInv` of the surjectivity at that level pointwise in `ι`. Compatibility is then
`Function.surjInv_eq`, and `σ 0 = s` is `rfl`. The arbitrary-index core is
`exists_tower_of_surjective`, which knows nothing about schemes.

**`rw` is avoided in `app_tensorRight_transition_eq_of_le`.**
`AlgebraicGeometry.Scheme.Modules` is a plain `def` for `SheafOfModules _`, agreeing with it only
at default transparency, so rewriting under `(tensorRightModules X N).map _` fails keyed matching
on goals that display the pattern character for character. Every step of that proof is therefore
a `congrArg` at an explicitly ascribed function, in term mode; the two steps that pass a
composite or an identity through `.val.app` are `rfl`
(`Stacks.SheafOfModules.comp_val_app_apply` is itself `rfl`). Composites of transitions of `ℕᵒᵖ`
are compared with `Subsingleton.elim`, as elsewhere in this directory, `ℕᵒᵖ` being a preorder
category.

**The two spellings of the twist are genuinely different objects, and the transport is proved,
not assumed.** The surjectivity this file consumes is stated at the tensor product sheaf of
[Stacks, Tag 01CA], through `Stacks.Coherent.tensorRightModules`; the mapping-out property that
consumes this file is stated at the monoidal product of `X.Modules`, through `▷`. These are *not*
definitionally equal — `M ⊗ N = (tensorRightModules X N).obj M` fails `rfl` at default
transparency, the monoidal product being the localized one and the other the sheafification of
the objectwise tensor product — so `tensorRightModulesIso` is the named comparison
(`Stacks.SheafOfModules.tensorObjIso`, ascribed at the scheme spelling) and
`whiskerRight_comp_tensorRightModulesIso` its naturality in the left factor, obtained from
`Stacks.SheafOfModules.tensorObjIso_naturality` at `g` and `𝟙 N` together with
`CategoryTheory.MonoidalCategory.tensorHom_id`. `g ▷ N` and `g ⊗ₘ 𝟙 N` are themselves not
definitionally equal here, so that last step is the named lemma rather than `rfl`, and it is
applied through `congrArg` because `rw` does not find the pattern `?f ⊗ₘ 𝟙 ?Y` in a goal that
displays `g ⊗ₘ 𝟙 N`. What *is* `rfl` is
`Stacks.SheafOfModules.sheafifyTensorHom _ _ g (𝟙 N) = (tensorRightModules X N).map g`, which is
why the naturality lands on the twist functor with no further comparison.

**Surjectivity transports; the lifting does not have to.** Only
`surjective_app_whiskerRight_of_surjective_app_tensorRightModules` crosses the comparison — one
statement about one map — after which the induction is run again on the other side. Transporting
the whole lifted family instead would require the comparison to be natural in `𝓕` as well and
would carry an isomorphism through every level.

## References

* [Stacks Project, Tag 0885](https://stacks.math.columbia.edu/tag/0885)
* [Stacks Project, Tag 087Y](https://stacks.math.columbia.edu/tag/087Y)
* [Stacks Project, Tag 087W](https://stacks.math.columbia.edu/tag/087W)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.Cohomology.FormalFunctions (baseIdealSheaf)

universe v u

namespace Stacks.Coherent

/-! ### The arbitrary-index core -/

/-- **A tower of surjections admits compatible lifts of any family at its base.** Given types
`α n`, maps `f n : α (n + 1) → α n` all surjective and a family `a : ι → α 0`, there is a family
`s n : ι → α n` at every level with `s 0 = a` and `f n (s (n + 1) i) = s n i`.

Each stage is `Function.surjInv` of the surjectivity below it, applied pointwise in `ι`; the
recursion is a `Nat.rec` over the motive `fun n => ι → α n`, the types `α n` being different at
different `n`. -/
private theorem exists_tower_of_surjective {ι : Type v} {α : ℕ → Type*}
    (f : ∀ n : ℕ, α (n + 1) → α n) (hf : ∀ n : ℕ, Function.Surjective (f n)) (a : ι → α 0) :
    ∃ s : ∀ n : ℕ, ι → α n, s 0 = a ∧ ∀ (n : ℕ) (i : ι), f n (s (n + 1) i) = s n i :=
  ⟨Nat.rec (motive := fun n => ι → α n) a fun n y i => Function.surjInv (hf n) (y i),
    rfl, fun n _ => Function.surjInv_eq (hf n) _⟩

/-! ### Lifting twisted sections up the tower -/

variable {X : Scheme.{u}} {I : X.IdealSheafData}

/-- **A family of twisted sections at the bottom of a coherent adic system extends up the whole
tower.** Let `𝓕` be a coherent adic system along `I`, let `N` be an `𝒪_X`-module, let `U` be an
open of `X` and suppose each twisted transition `𝓕_{n+1} ⊗ N ⟶ 𝓕_n ⊗ N` is surjective on
sections over `U`. Then every family `s : ι → Γ(U, 𝓕_0 ⊗ N)` is the level-`0` part of a family
`σ n : ι → Γ(U, 𝓕_n ⊗ N)` compatible with the transition maps.

Nothing is assumed about `s`: any property of it — generation of `𝓕_0 ⊗ N`, in the use this is
made for — is carried to level `0` of `σ` by the clause `σ 0 = s`. Nothing is assumed about `N`
either, invertibility entering only through the surjectivity hypothesis. -/
public theorem exists_compatible_sections_tensorRight_transition_of_surjective
    (𝓕 : CoherentAdicSystems I) (U : X.Opens) (N : X.Modules)
    (hsurj : ∀ n : ℕ, Function.Surjective
      (((tensorRightModules X N).map
        (𝓕.obj.map (homOfLE (Nat.le_succ n)).op)).val.app (op U)))
    {ι : Type v}
    (s : ι → ToType (((tensorRightModules X N).obj (𝓕.obj.obj (op 0))).val.obj (op U))) :
    ∃ σ : ∀ n : ℕ,
        ι → ToType (((tensorRightModules X N).obj (𝓕.obj.obj (op n))).val.obj (op U)),
      σ 0 = s ∧
      ∀ (n : ℕ) (i : ι),
        ((tensorRightModules X N).map
            (𝓕.obj.map (homOfLE (Nat.le_succ n)).op)).val.app (op U) (σ (n + 1) i) = σ n i :=
  exists_tower_of_surjective
    (fun n x => ((tensorRightModules X N).map
      (𝓕.obj.map (homOfLE (Nat.le_succ n)).op)).val.app (op U) x) hsurj s

/-- **Compatibility with the successive transitions gives compatibility with all of them.** If
`σ` is a family of twisted sections with
`(𝓕_{n+1} ⊗ N ⟶ 𝓕_n ⊗ N) (σ (n + 1) i) = σ n i` for every `n`, then
`(𝓕_n ⊗ N ⟶ 𝓕_m ⊗ N) (σ n i) = σ m i` for every `m ≤ n`.

The transition `𝓕_n ⟶ 𝓕_m` is the composite of the successive ones, two morphisms of `ℕᵒᵖ` with
the same source and target being equal; twisting and taking sections are functorial, and a
composite acts on sections by composition. -/
public theorem app_tensorRight_transition_eq_of_le
    (𝓕 : CoherentAdicSystems I) (U : X.Opens) (N : X.Modules) {ι : Type v}
    {σ : ∀ n : ℕ,
      ι → ToType (((tensorRightModules X N).obj (𝓕.obj.obj (op n))).val.obj (op U))}
    (hσ : ∀ (n : ℕ) (i : ι),
      ((tensorRightModules X N).map
        (𝓕.obj.map (homOfLE (Nat.le_succ n)).op)).val.app (op U) (σ (n + 1) i) = σ n i)
    {m n : ℕ} (hmn : m ≤ n) (i : ι) :
    ((tensorRightModules X N).map (𝓕.obj.map (homOfLE hmn).op)).val.app (op U) (σ n i)
      = σ m i := by
  induction hmn with
  | refl =>
      exact (congrArg (fun φ : op m ⟶ op m =>
            ((tensorRightModules X N).map (𝓕.obj.map φ)).val.app (op U) (σ m i))
          (Subsingleton.elim _ (𝟙 (op m)))).trans
        ((congrArg (fun ψ : 𝓕.obj.obj (op m) ⟶ 𝓕.obj.obj (op m) =>
              ((tensorRightModules X N).map ψ).val.app (op U) (σ m i))
            (𝓕.obj.map_id (op m))).trans
          (congrArg (fun ψ : (tensorRightModules X N).obj (𝓕.obj.obj (op m)) ⟶
                (tensorRightModules X N).obj (𝓕.obj.obj (op m)) =>
              ψ.val.app (op U) (σ m i))
            ((tensorRightModules X N).map_id (𝓕.obj.obj (op m)))))
  | @step n hmn ih =>
      refine (congrArg (fun φ : op (n + 1) ⟶ op m =>
            ((tensorRightModules X N).map (𝓕.obj.map φ)).val.app (op U) (σ (n + 1) i))
          (Subsingleton.elim _
            ((homOfLE (Nat.le_succ n)).op ≫ (homOfLE hmn).op))).trans ?_
      refine (congrArg (fun ψ : 𝓕.obj.obj (op (n + 1)) ⟶ 𝓕.obj.obj (op m) =>
            ((tensorRightModules X N).map ψ).val.app (op U) (σ (n + 1) i))
          (𝓕.obj.map_comp (homOfLE (Nat.le_succ n)).op (homOfLE hmn).op)).trans ?_
      refine (congrArg (fun ψ : (tensorRightModules X N).obj (𝓕.obj.obj (op (n + 1))) ⟶
            (tensorRightModules X N).obj (𝓕.obj.obj (op m)) =>
            ψ.val.app (op U) (σ (n + 1) i))
          ((tensorRightModules X N).map_comp (𝓕.obj.map (homOfLE (Nat.le_succ n)).op)
            (𝓕.obj.map (homOfLE hmn).op))).trans ?_
      exact (congrArg (fun x => ((tensorRightModules X N).map
          (𝓕.obj.map (homOfLE hmn).op)).val.app (op U) x) (hσ n i)).trans ih

/-! ### The uniform statement, with the cohomological step supplied -/

/-- **The generation step of [Stacks, Tag 0885], uniformly in the level.** Let `A` be a
Noetherian ring, `I ⊆ A` an ideal, `f : X ⟶ Spec A` proper, `L` an invertible `𝒪_X`-module ample
relative to `f`, and `𝓕` an object of `Coh(X, 𝓘)` for `𝓘 = I · 𝒪_X`. Then there is an integer
`d₀` such that for every `d ≥ d₀` and every family

  `s : ι → H⁰(X, 𝓕_0 ⊗ L ^⊗ d)`

there is a family `σ n : ι → H⁰(X, 𝓕_n ⊗ L ^⊗ d)` at every level with `σ 0 = s`, compatible with
the twisted transition maps — one `d₀` for the whole system and every family at once.

The `d₀` is that of
`Stacks.Coherent.exists_surjective_app_tensorRight_transition_tensorPowModule`, hence that of
[Stacks, Tag 0884]; the lifting is
`Stacks.Coherent.exists_compatible_sections_tensorRight_transition_of_surjective`. -/
public theorem exists_compatible_sections_tensorRight_transition_tensorPowModule
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [IsProper f]
    (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]
    (hL : Stacks.RelativeAmple.IsRelativelyAmple f L)
    (𝓕 : CoherentAdicSystems (baseIdealSheaf A I f)) :
    ∃ d₀ : ℤ, ∀ (d : ℤ), d₀ ≤ d → ∀ (ι : Type v)
      (s : ι → ToType (((tensorRightModules X (Stacks.Ample.tensorPowModule X L d)).obj
        (𝓕.obj.obj (op 0))).val.obj (op ⊤))),
      ∃ σ : ∀ n : ℕ, ι → ToType
          (((tensorRightModules X (Stacks.Ample.tensorPowModule X L d)).obj
            (𝓕.obj.obj (op n))).val.obj (op ⊤)),
        σ 0 = s ∧
        ∀ (n : ℕ) (i : ι),
          ((tensorRightModules X (Stacks.Ample.tensorPowModule X L d)).map
              (𝓕.obj.map (homOfLE (Nat.le_succ n)).op)).val.app (op ⊤) (σ (n + 1) i) = σ n i := by
  obtain ⟨d₀, hd₀⟩ :=
    exists_surjective_app_tensorRight_transition_tensorPowModule A I f L hL 𝓕
  exact ⟨d₀, fun d hd ι s =>
    exists_compatible_sections_tensorRight_transition_of_surjective 𝓕 ⊤ _
      (fun n => hd₀ n d hd) s⟩

/-! ### The monoidal spelling, which the mapping-out property of 0885 consumes -/

section Monoidal

open CategoryTheory.MonoidalCategory
open Stacks.SheafInternalHom (isSheaf_structureRingPresheaf)

attribute [local instance] Stacks.SheafInternalHom.sheafifyMonoidal
  Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemePreadditive
  Stacks.SectionRingGeometric.schemeTensorRightAdditive

/-- **The monoidal product and the twist functor compared**: `M ⊗ N` is the tensor product sheaf
of [Stacks, Tag 01CA], which is `(tensorRightModules X N).obj M`.

This is `Stacks.SheafOfModules.tensorObjIso` with its type ascribed at the scheme spelling of the
category of modules, for the reason recorded for `Stacks.Coherent.tensorRightModules` itself: the
underlying statement is about `SheafOfModules (TensorSheafification.structureSheaf X.presheaf _)`
and instance search, being syntactic, does not bridge that to `X.Modules`. The two sides are not
definitionally equal, so this iso is not a `refl`. -/
public def tensorRightModulesIso {X : Scheme.{u}} (M N : X.Modules) :
    (M ⊗ N : X.Modules) ≅ (tensorRightModules X N).obj M :=
  Stacks.SheafOfModules.tensorObjIso X.presheaf (isSheaf_structureRingPresheaf X) M N

/-- **`tensorRightModulesIso` is natural in the left factor**: right whiskering by `N` becomes the
action of `Stacks.Coherent.tensorRightModules X N` on morphisms.

`Stacks.SheafOfModules.tensorObjIso_naturality` at `g` and `𝟙 N` gives the square for `g ⊗ₘ 𝟙 N`,
whose right-hand side is `(tensorRightModules X N).map g` by definition;
`CategoryTheory.MonoidalCategory.tensorHom_id` turns `g ⊗ₘ 𝟙 N` into `g ▷ N`, and is applied
through `congrArg` rather than `rw`, which does not find its pattern here. -/
public theorem whiskerRight_comp_tensorRightModulesIso {X : Scheme.{u}} (N : X.Modules)
    {M P : X.Modules} (g : M ⟶ P) :
    (g ▷ N) ≫ (tensorRightModulesIso P N).hom =
      (tensorRightModulesIso M N).hom ≫ (tensorRightModules X N).map g :=
  (congrArg (fun φ : (M ⊗ N : X.Modules) ⟶ (P ⊗ N : X.Modules) =>
        φ ≫ (tensorRightModulesIso P N).hom)
      (MonoidalCategory.tensorHom_id g N)).symm.trans
    (Stacks.SheafOfModules.tensorObjIso_naturality X.presheaf
      (isSheaf_structureRingPresheaf X) g (𝟙 N))

/-- An isomorphism of `𝒪_X`-modules is left-cancelled by its inverse on sections over `U`. -/
private theorem inv_app_hom_app {X : Scheme.{u}} {Q R : X.Modules} (U : X.Opens) (iso : Q ≅ R)
    (z : Γ(Q, U)) : iso.inv.app U (iso.hom.app U z) = z := by
  simpa only [Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.id_app,
    ConcreteCategory.comp_apply, ConcreteCategory.id_apply] using
    congrArg (fun φ : Q ⟶ Q => φ.app U z) iso.hom_inv_id

/-- **Surjectivity on sections crosses the comparison of the two spellings of the twist.** If
tensoring `g` with `N` through `Stacks.Coherent.tensorRightModules` is surjective on sections over
`U`, then so is right whiskering `g` by `N` in the monoidal structure of `X.Modules`.

The two maps are conjugate by `tensorRightModulesIso`
(`whiskerRight_comp_tensorRightModulesIso`), whose components are isomorphisms and hence
bijective on sections; the preimage of a section `y` is the one of
`(tensorRightModulesIso P N).hom.app U y` carried back by the inverse at the source. -/
public theorem surjective_app_whiskerRight_of_surjective_app_tensorRightModules
    {X : Scheme.{u}} (N : X.Modules) {M P : X.Modules} (U : X.Opens) (g : M ⟶ P)
    (h : Function.Surjective (((tensorRightModules X N).map g).app U)) :
    Function.Surjective ((g ▷ N).app U) := by
  intro y
  obtain ⟨x, hx⟩ := h ((tensorRightModulesIso P N).hom.app U y)
  refine ⟨(tensorRightModulesIso M N).inv.app U x, ?_⟩
  have hsq := congrArg
    (fun φ : (M ⊗ N : X.Modules) ⟶ (tensorRightModules X N).obj P =>
      φ.app U ((tensorRightModulesIso M N).inv.app U x))
    (whiskerRight_comp_tensorRightModulesIso N g)
  simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply] at hsq
  have key := (hsq.trans (congrArg
    (fun z => ((tensorRightModules X N).map g).app U z)
    (inv_app_hom_app U (tensorRightModulesIso M N).symm x))).trans hx
  exact ((inv_app_hom_app U (tensorRightModulesIso P N) _).symm.trans
      (congrArg (fun w => (tensorRightModulesIso P N).inv.app U w) key)).trans
    (inv_app_hom_app U (tensorRightModulesIso P N) y)

/-- **The generation step of [Stacks, Tag 0885] in the spelling its mapping-out property
consumes.** Hypotheses as for
`Stacks.Coherent.exists_compatible_sections_tensorRight_transition_tensorPowModule`. There is a
`d₀` such that for every `d ≥ d₀`, every `t` and every family `s₀ : Fin t → Γ(𝓕_0 ⊗ L ^⊗ d, ⊤)`
of global sections, there are families `s j : ∀ n, Γ(𝓕_n ⊗ L ^⊗ d, ⊤)` with `s j 0 = s₀ j` and

  `(𝓕_{n+1} ⟶ 𝓕_n ▷ L ^⊗ d).app ⊤ (s j (n + 1)) = s j n`.

Nothing is assumed about `s₀`, in particular not that it generates: as for the other spelling,
`s j 0 = s₀ j` is what carries generation — or any other property of `s₀` — to level `0`, the
only level at which [Stacks, Tag 087Y] requires it.

The surjectivity comes from
`Stacks.Coherent.exists_surjective_app_tensorRight_transition_tensorPowModule` across
`Stacks.Coherent.surjective_app_whiskerRight_of_surjective_app_tensorRightModules`, and the
induction is then the same `exists_tower_of_surjective` run in the monoidal spelling. The index
and level arguments are ordered `Fin t` first, matching the mapping-out property's binder. -/
public theorem exists_compatible_sections_whiskerRight_tensorPowModule
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [IsProper f]
    (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]
    (hL : Stacks.RelativeAmple.IsRelativelyAmple f L)
    (𝓕 : CoherentAdicSystems (baseIdealSheaf A I f)) :
    ∃ d₀ : ℤ, ∀ d : ℤ, d₀ ≤ d → ∀ (t : ℕ)
      (s₀ : Fin t → Γ(𝓕.obj.obj (op 0) ⊗ Stacks.Ample.tensorPowModule X L d, ⊤)),
      ∃ s : Fin t → (n : ℕ) → Γ(𝓕.obj.obj (op n) ⊗ Stacks.Ample.tensorPowModule X L d, ⊤),
        (∀ j, s j 0 = s₀ j) ∧
        ∀ (j : Fin t) (n : ℕ),
          ((𝓕.obj.map (homOfLE (Nat.le_succ n)).op ▷
            Stacks.Ample.tensorPowModule X L d).app ⊤) (s j (n + 1)) = s j n := by
  obtain ⟨d₀, hd₀⟩ :=
    exists_surjective_app_tensorRight_transition_tensorPowModule A I f L hL 𝓕
  refine ⟨d₀, fun d hd t s₀ => ?_⟩
  obtain ⟨σ, hσ0, hσ⟩ := exists_tower_of_surjective
    (α := fun n => Γ(𝓕.obj.obj (op n) ⊗ Stacks.Ample.tensorPowModule X L d, ⊤))
    (fun n x => (𝓕.obj.map (homOfLE (Nat.le_succ n)).op ▷
      Stacks.Ample.tensorPowModule X L d).app ⊤ x)
    (fun n => surjective_app_whiskerRight_of_surjective_app_tensorRightModules
      _ ⊤ _ (hd₀ n d hd)) s₀
  exact ⟨fun j n => σ n j, fun j => congrFun hσ0 j, fun j n => hσ n j⟩

end Monoidal

end Stacks.Coherent

end
