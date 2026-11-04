module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyConstantSerreClass

/-!
# A quotient of a constant sheaf of modules with a constant kernel

Let `(C, J)` be a site, `Λ` a ring, `M` a `Λ`-module and `p : M̲ ⟶ B` an epimorphism from the
constant sheaf on `M` to a sheaf of `Λ`-modules. Suppose there is a submodule `N ≤ M` such that,
over every object `W` which is not covered by the empty sieve, a constant `a ∈ M` is sent to zero
by `p` exactly when `a ∈ N`. Then `B` is the constant sheaf on `M ⧸ N`.

We also show that a family of submodules of a Noetherian module, indexed by the objects over a
fixed object and growing along morphisms, takes a maximal value at some object not covered by the
empty sieve, and keeps that value over every object above it which is not covered by the empty
sieve either.

## Main results

* `Stacks.ConstantSheaf.nonempty_constantSheaf_quotient_iso`: `B ≅ (M ⧸ N)̲`.
* `Stacks.ConstantSheaf.exists_eq_of_isNoetherian`: the maximal value of a growing family of
  submodules of a Noetherian module.

## References

* [Stacks Project, Tag 09BH](https://stacks.math.columbia.edu/tag/09BH)
* [Stacks Project, Tag 09BU](https://stacks.math.columbia.edu/tag/09BU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u w r

namespace Stacks.ConstantSheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) {Λ : Type r} [Ring Λ]

/-- Two sections of a sheaf of modules agreeing on a covering sieve are equal. -/
private theorem sheaf_section_ext (F : Sheaf J (ModuleCat.{max u v w} Λ)) {W : C} {S : Sieve W}
    (hS : S ∈ J W) {x y : F.obj.obj (op W)}
    (h : ∀ ⦃W' : C⦄ (g : W' ⟶ W), S g → (F.obj.map g.op).hom x = (F.obj.map g.op).hom y) :
    x = y :=
  (((isSheaf_iff_isSheaf_of_type _ _).mp
    ((sheafCompose J (forget (ModuleCat.{max u v w} Λ))).obj F).property) _ hS).isSeparatedFor.ext
      fun _ g hg ↦ h g hg

/-- Over an object covered by the empty sieve, a sheaf of modules has at most one section. -/
theorem subsingleton_of_bot_mem (F : Sheaf J (ModuleCat.{max u v w} Λ)) {W : C}
    (hW : (⊥ : Sieve W) ∈ J W) : Subsingleton (F.obj.obj (op W)) :=
  ⟨fun _ _ ↦ sheaf_section_ext J F hW fun _ _ h ↦ h.elim⟩

variable (M : ModuleCat.{max u v w} Λ)

/-- The canonical map from a module to the sections of the constant sheaf on it. -/
abbrev constSection (W : C) :
    M ⟶ ((constantSheaf J (ModuleCat.{max u v w} Λ)).obj M).obj.obj (op W) :=
  (toSheafify J ((Functor.const Cᵒᵖ).obj M)).app (op W)

/-- **A quotient of a constant sheaf with a constant kernel is constant.** Let
`p : M̲ ⟶ B` be an epimorphism of sheaves of `Λ`-modules and `N ≤ M` a submodule such that `p`
kills the constants in `N` over every object, and over every object not covered by the empty
sieve kills only those. Then `B` is isomorphic to the constant sheaf on `M ⧸ N`. -/
theorem nonempty_constantSheaf_quotient_iso (N : Submodule Λ M)
    (B : Sheaf J (ModuleCat.{max u v w} Λ)) (p : (constantSheaf J _).obj M ⟶ B) [Epi p]
    (h1 : ∀ (W : C) (a : M), a ∈ N → (p.hom.app (op W)).hom ((constSection J M W).hom a) = 0)
    (h2 : ∀ (W : C), (⊥ : Sieve W) ∉ J W → ∀ a : M,
      (p.hom.app (op W)).hom ((constSection J M W).hom a) = 0 → a ∈ N) :
    Nonempty ((constantSheaf J (ModuleCat.{max u v w} Λ)).obj (ModuleCat.of Λ (M ⧸ N)) ≅ B) := by
  let A := ModuleCat.{max u v w} Λ
  let P := (Functor.const Cᵒᵖ).obj M
  let P' := (Functor.const Cᵒᵖ).obj (ModuleCat.of Λ (M ⧸ N))
  let σ : P ⟶ B.obj := toSheafify J P ≫ p.hom
  have hσ (W : C) (a : M) (ha : a ∈ N) : (σ.app (op W)).hom a = 0 := h1 W a ha
  let φ : P' ⟶ B.obj :=
    { app W := ModuleCat.ofHom (N.liftQ (σ.app W).hom fun a ha ↦ hσ W.unop a ha)
      naturality W W' f := by
        ext x
        obtain ⟨a, rfl⟩ := N.mkQ_surjective x
        exact congrArg (fun g ↦ g.hom a) (σ.naturality f) }
  let adj := sheafificationAdjunction J A
  let p' : (constantSheaf J A).obj (ModuleCat.of Λ (M ⧸ N)) ⟶ B := (adj.homEquiv _ _).symm φ
  let q : M ⟶ ModuleCat.of Λ (M ⧸ N) := ModuleCat.ofHom N.mkQ
  have hfac : (constantSheaf J A).map q ≫ p' = p := by
    apply (adj.homEquiv _ _).injective
    refine (adj.homEquiv_naturality_left ((Functor.const Cᵒᵖ).map q) p').trans ?_
    refine (congrArg (fun g ↦ (Functor.const Cᵒᵖ).map q ≫ g)
      ((adj.homEquiv _ _).apply_symm_apply φ)).trans ?_
    refine Eq.trans ?_ (adj.homEquiv_unit _ _ p).symm
    ext W a
    rfl
  have : Epi p' := epi_of_epi_fac hfac
  have key : toSheafify J P' ≫ p'.hom = φ := by
    have := (adj.homEquiv _ _).apply_symm_apply φ
    rwa [Adjunction.homEquiv_unit] at this
  have hinj (W : C) : Function.Injective (p'.hom.app (op W)).hom := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    let F' := (constantSheaf J A).obj (ModuleCat.of Λ (M ⧸ N))
    have := Stacks.ConstantSheaf.isLocallySurjective_toSheafify_moduleCat.{v, u, w} J Λ P'
    have hS := Presheaf.imageSieve_mem J (toSheafify J P') (U := op W) x
    refine sheaf_section_ext J F' hS fun W' g hg ↦ ?_
    obtain ⟨y, hy⟩ := hg
    obtain ⟨a, rfl⟩ := N.mkQ_surjective y
    rw [map_zero]
    by_cases hW' : (⊥ : Sieve W') ∈ J W'
    · have := subsingleton_of_bot_mem.{v, u, w} J F' hW'
      exact Subsingleton.elim _ _
    · have h0 : (p'.hom.app (op W')).hom ((F'.obj.map g.op).hom x) = 0 := by
        have := congrArg (fun f ↦ f.hom x) (p'.hom.naturality g.op)
        change (p'.hom.app (op W')).hom ((F'.obj.map g.op).hom x) =
          (B.obj.map g.op).hom ((p'.hom.app (op W)).hom x) at this
        rw [this, hx, map_zero]
      have hσa : (σ.app (op W')).hom a = 0 := by
        have := congrArg (fun f ↦ (f.app (op W')).hom (N.mkQ a)) key
        change (p'.hom.app (op W')).hom (((toSheafify J P').app (op W')).hom (N.mkQ a)) =
          (σ.app (op W')).hom a at this
        rw [← this]
        change (p'.hom.app (op W')).hom (ConcreteCategory.hom ((toSheafify J P').app (op W'))
          (N.mkQ a)) = 0
        rwa [hy]
      have h3 : (ConcreteCategory.hom ((toSheafify J P').app (op W'))) (N.mkQ a) = 0 := by
        rw [show N.mkQ a = 0 from (Submodule.Quotient.mk_eq_zero N).mpr (h2 W' hW' a hσa),
          map_zero]
      exact hy.symm.trans h3
  have : ∀ W, Mono (p'.hom.app W) := fun W ↦
    (ModuleCat.mono_iff_injective _).mpr (hinj W.unop)
  have : Mono p' := (sheafToPresheaf J A).mono_of_mono_map (NatTrans.mono_of_mono_app p'.hom)
  have : IsIso p' := isIso_of_mono_of_epi p'
  exact ⟨asIso p'⟩

omit [Ring Λ] in
/-- **A maximal value of a growing family of submodules.** Let `M` be a Noetherian `S`-module
and let `c f` be a submodule of `M` for each morphism `f : W ⟶ U`, growing under precomposition.
If `U` is not covered by the empty sieve, there is `f₀ : U₀ ⟶ U` with `U₀` not covered by the
empty sieve at which `c` is maximal: `c (g ≫ f₀) = c f₀` for every `g : W ⟶ U₀` with `W` not
covered by the empty sieve. -/
theorem exists_eq_of_isNoetherian {S : Type*} [Ring S] {M : Type*} [AddCommGroup M] [Module S M]
    [IsNoetherian S M] (U : C) (hU : (⊥ : Sieve U) ∉ J U)
    (c : ∀ {W : C}, (W ⟶ U) → Submodule S M)
    (hc : ∀ {W W' : C} (f : W ⟶ U) (g : W' ⟶ W), c f ≤ c (g ≫ f)) :
    ∃ (U₀ : C) (f₀ : U₀ ⟶ U), (⊥ : Sieve U₀) ∉ J U₀ ∧
      ∀ {W : C} (g : W ⟶ U₀), (⊥ : Sieve W) ∉ J W → c (g ≫ f₀) = c f₀ := by
  let 𝒮 : Set (Submodule S M) := {N | ∃ (W : C) (f : W ⟶ U), (⊥ : Sieve W) ∉ J W ∧ c f = N}
  obtain ⟨N₀, ⟨U₀, f₀, hU₀, rfl⟩, hmax⟩ :=
    set_has_maximal_iff_noetherian.mpr inferInstance 𝒮 ⟨c (𝟙 U), U, 𝟙 U, hU, rfl⟩
  exact ⟨U₀, f₀, hU₀, fun g hW ↦
    ((hc f₀ g).lt_or_eq.resolve_left (hmax _ ⟨_, _, hW, rfl⟩)).symm⟩

end Stacks.ConstantSheaf

end
