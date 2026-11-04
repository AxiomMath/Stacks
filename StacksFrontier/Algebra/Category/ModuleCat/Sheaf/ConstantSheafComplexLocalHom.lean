module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Sites.Adjunction
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.RingTheory.Finiteness.Projective
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FiniteTypeKernel
import StacksCore.Tactic.StacksAttribute

/-!
# Maps between complexes of constant sheaves of modules

Let `J` be a Grothendieck topology on `C` and let `Λ` be a ring. For a complex `P` of
`Λ`-modules write `P̲` for the complex of constant sheaves of `Λ`-modules it generates. A map of
complexes `β : P̲ ⟶ T̲` is *not* in general of the form `g̲` for a map of complexes `g : P ⟶ T`.
This file proves that it is so locally, provided `P` is a complex of finite projective
`Λ`-modules which vanishes in all but finitely many degrees: every object `U` of the site carries
a covering sieve along each of whose arrows the restriction of `β` is `g̲` for some map of
complexes `g : P ⟶ T`.

This is the step that Stacks 09BE adds to Stacks 09BD — the appeal to Modules on Sites, Tag 093S
(3) made in the source's two-line proof — carried out at the level of complexes rather than of a
single sheaf.

## Main results

* `Stacks.ConstantSheaf.exists_cover_lift_of_finite_projective`: a linear map out of a finite
  projective module lifts, on a covering sieve, through a locally surjective map of presheaves of
  modules.
* `Stacks.ConstantSheaf.injective_toSheafify_const_app`: over an object whose empty sieve is not
  covering, the canonical map from a module to the sections of its constant sheaf is injective.
* `Stacks.ConstantSheaf.overPullback_constantSheaf_hom_ext`: two maps out of the restriction of a
  constant sheaf of modules to a slice site agree as soon as they agree on the canonical image of
  the module over the terminal object of the slice.
* `Stacks.ConstantSheaf.exists_cover_chainMap_of_constantSections`: a family of maps
  `P^n ⟶ Γ(U, T̲^n)` compatible with the differentials lifts, on a covering sieve of `U`, to a
  map of complexes `P ⟶ T`.
* `Stacks.ConstantSheaf.exists_cover_overPullback_eq_constantSheaf_mapHomologicalComplex`:
  **the main result**, the local constancy of a map of complexes of constant sheaves of modules.

## Implementation notes

The finiteness hypothesis is `Module.Finite` together with `Module.Projective` in every degree,
which is the form in which `StacksDraft.Perfect.IsPerfect` (Stacks 0657 (1)) and
`CategoryTheory.FilteredDerived.finiteProjectiveComplex` (Stacks 03TH) record the terms of a
representative of a perfect object; projectivity is what makes the degreewise lifting work, since
it presents each `P^n` as a retract of a finite free module.

Boundedness enters only as the finiteness of the set of degrees in which `P` is nonzero, rather
than as `IsStrictlyGE` and `IsStrictlyLE`, because all the proof needs is that one covering sieve
can serve all the degrees at once; `Stacks.SheafOfModules.finite_notIsZero_of_strictlyBounded`
supplies this hypothesis from the two-sided bounds.

**Why the differentials commute.** The degreewise lifts are produced one degree at a time and
nothing forces them to form a map of complexes. The commutation is checked in `T` itself, which
is possible because the canonical map from a module to the sections of its constant sheaf is
injective over an object whose empty sieve is not covering
(`Stacks.ConstantSheaf.injective_toSheafify_const_app`). Over an object whose empty sieve *is*
covering every sheaf is terminal, and there the zero map already witnesses the conclusion; so no
hypothesis excluding the empty topos is needed, which is why none appears.

**What this file does not prove.** Stacks 09BE concerns a morphism `φ : K̲ ⟶ L̲` of the derived
category `D(C, Λ)` with `K` perfect, and asserts that `φ` is locally the image of a morphism
`K ⟶ L` of `D(Λ)`. Reaching that statement from the result proved here additionally requires
Stacks 09BD — that `φ` is, on a covering, represented by an actual map of complexes — in the
derived category of `ModuleCat.{w} Λ`-valued sheaves and with the module universe independent of
the universes of the site. The library's Stacks 09BD and Stacks 08FR
(`AlgebraicGeometry.RingedSite.exists_coveringSieve_complexMap_of_finite_projective` and
`AlgebraicGeometry.RingedSite.exists_coveringSieve_complexMap`) are stated for
`SheafOfModules.{0}` over a `RingedSite.{u, u, 0}`, so neither the ambient category nor the
universe level matches, and bridging them would need the equivalence between sheaves of modules
over the constant sheaf of rings and `ModuleCat`-valued sheaves, which is Stacks 093T and is not
in the library. The `@[stacks 09BE]` attribute below therefore carries a part string naming what
is proved, and no unqualified 09BE claim is made.

## References

* [Stacks Project, Tag 09BE](https://stacks.math.columbia.edu/tag/09BE)
* [Stacks Project, Tag 09BD](https://stacks.math.columbia.edu/tag/09BD)
* [Stacks Project, Tag 093S](https://stacks.math.columbia.edu/tag/093S)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u

namespace Stacks.ConstantSheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

variable {Λ : Type*} [Ring Λ]

/-- A linear map out of a finite projective module into the sections of a presheaf of modules
lifts, on a covering sieve, through a locally surjective map of presheaves of modules. -/
lemma exists_cover_lift_of_finite_projective {M : Type*} [AddCommGroup M] [Module Λ M]
    [Module.Finite Λ M] [Module.Projective Λ M]
    {F G : Cᵒᵖ ⥤ ModuleCat.{w} Λ} (η : F ⟶ G) [Presheaf.IsLocallySurjective J η] (U : C)
    (φ : M →ₗ[Λ] G.obj (op U)) :
    ∃ S : Sieve U, S ∈ J U ∧ ∀ {V : C} (f : V ⟶ U), S f →
      ∃ g : M →ₗ[Λ] F.obj (op V),
        (η.app (op V)).hom ∘ₗ g = (G.map f.op).hom ∘ₗ φ := by
  classical
  obtain ⟨n, p, q, _, _, hpq⟩ := Module.Finite.exists_comp_eq_id_of_projective Λ M
  let b := Pi.basisFun Λ (Fin n)
  let S (i : Fin n) := Presheaf.imageSieve η (φ (p (b i)))
  refine ⟨Finset.univ.inf S, Stacks.SheafOfModules.FiniteTypeKernel.finsetInf_mem J _ S
    (fun i _ => Presheaf.imageSieve_mem J η _), ?_⟩
  intro V f hf
  have hi (i : Fin n) : S i f := (Finset.inf_le (f := S) (Finset.mem_univ i)) _ hf
  choose z hz using hi
  let t := b.constr ℕ z
  have ht : (η.app (op V)).hom ∘ₗ t = (G.map f.op).hom ∘ₗ φ ∘ₗ p := by
    refine b.ext fun i => ?_
    simpa only [LinearMap.comp_apply, t, Module.Basis.constr_basis] using hz i
  refine ⟨t ∘ₗ q, ?_⟩
  rw [← LinearMap.comp_assoc, ht, LinearMap.comp_assoc, LinearMap.comp_assoc, hpq,
    LinearMap.comp_id]

variable [HasWeakSheafify J (ModuleCat.{w} Λ)]

/-- Over an object whose empty sieve is not covering, the canonical map from a module to the
sections of the constant sheaf it generates is injective. -/
lemma injective_toSheafify_const_app [J.WEqualsLocallyBijective (ModuleCat.{w} Λ)]
    (M : ModuleCat.{w} Λ) (U : C) (hU : (⊥ : Sieve U) ∉ J U) :
    Function.Injective ((toSheafify J ((Functor.const Cᵒᵖ).obj M)).app (op U)) := by
  intro x y hxy
  have hcover := (J.W_toSheafify ((Functor.const Cᵒᵖ).obj M)).isLocallyInjective.equalizerSieve_mem
    x y hxy
  by_contra h
  refine hU ?_
  convert hcover using 1
  ext V f
  simp [Presheaf.equalizerSieve_apply, h]

/-- Two maps out of a sheafification agree as soon as they agree after composition with a map
which the topology inverts. -/
lemma hom_ext_of_W {D : Type*} [Category* D] [HasWeakSheafify J D] {P Q T : Cᵒᵖ ⥤ D}
    (η : P ⟶ Q) (hη : J.W η) (_hQ : Presheaf.IsSheaf J Q) (hT : Presheaf.IsSheaf J T)
    (f g : Q ⟶ T) (h : η ≫ f = η ≫ g) : f = g := by
  have : IsIso (sheafifyMap J η) := by
    have := (J.W_iff η).mp hη
    exact inferInstanceAs (IsIso ((sheafToPresheaf J D).map ((presheafToSheaf J D).map η)))
  have he : sheafifyLift J f hT = sheafifyLift J g hT := by
    refine (cancel_epi (sheafifyMap J η)).mp ?_
    rw [sheafifyMap_sheafifyLift, sheafifyMap_sheafifyLift, h]
  simpa only [toSheafify_sheafifyLift] using congrArg (fun t => toSheafify J Q ≫ t) he

/-- Two maps out of the restriction to `C/U` of a constant sheaf of modules agree as soon as they
agree on the canonical image of the module over the terminal object of the slice. -/
lemma overPullback_constantSheaf_hom_ext [J.WEqualsLocallyBijective (ModuleCat.{w} Λ)] (U : C)
    [HasWeakSheafify (J.over U) (ModuleCat.{w} Λ)]
    [(J.over U).WEqualsLocallyBijective (ModuleCat.{w} Λ)] (M : ModuleCat.{w} Λ)
    (F : Sheaf (J.over U) (ModuleCat.{w} Λ))
    (f g : (J.overPullback (ModuleCat.{w} Λ) U).obj
      ((constantSheaf J (ModuleCat.{w} Λ)).obj M) ⟶ F)
    (h : (toSheafify J ((Functor.const Cᵒᵖ).obj M)).app (op U) ≫ f.hom.app (op (Over.mk (𝟙 U))) =
      (toSheafify J ((Functor.const Cᵒᵖ).obj M)).app (op U) ≫ g.hom.app (op (Over.mk (𝟙 U)))) :
    f = g := by
  let η := toSheafify J ((Functor.const Cᵒᵖ).obj M)
  have := (J.W_toSheafify ((Functor.const Cᵒᵖ).obj M)).isLocallyInjective
  have := (J.W_toSheafify ((Functor.const Cᵒᵖ).obj M)).isLocallySurjective
  have := Presheaf.isLocallyInjective_whisker (J.over U) J (Over.forget U) η
  have := Presheaf.isLocallySurjective_whisker (J.over U) J (Over.forget U) η
  refine Sheaf.hom_ext ?_
  refine hom_ext_of_W (J.over U) (Functor.whiskerLeft (Over.forget U).op η)
    (((J.over U).W_iff_isLocallyBijective _).mpr ⟨inferInstance, inferInstance⟩)
    ((J.overPullback (ModuleCat.{w} Λ) U).obj
      ((constantSheaf J (ModuleCat.{w} Λ)).obj M)).property F.property _ _ ?_
  refine ((constantPresheafAdj (ModuleCat.{w} Λ)
    (Over.mkIdTerminal (X := U))).homEquiv M F.obj).injective ?_
  show (𝟙 M) ≫ ((η.app (op U)) ≫ f.hom.app (op (Over.mk (𝟙 U)))) =
    (𝟙 M) ≫ ((η.app (op U)) ≫ g.hom.app (op (Over.mk (𝟙 U))))
  simpa only [Category.id_comp] using h

/-- The constant sheaf functor on modules is additive. -/
instance constantSheaf_moduleCat_additive :
    (constantSheaf J (ModuleCat.{w} Λ)).Additive := by
  unfold constantSheaf
  have h1 : (presheafToSheaf J (ModuleCat.{w} Λ)).Additive :=
    (sheafificationAdjunction J (ModuleCat.{w} Λ)).left_adjoint_additive
  have h2 : (Functor.const Cᵒᵖ (C := ModuleCat.{w} Λ)).Additive := ⟨by intros; rfl⟩
  infer_instance

/-- Restriction of sheaves of modules to a slice site is additive. -/
instance overPullback_additive_moduleCat (U : C) :
    (J.overPullback (ModuleCat.{w} Λ) U).Additive where
  map_add := by intros; rfl

/-- Restriction along a morphism of the site is additive on sheaves of modules. -/
instance overMapPullback_additive_moduleCat {U V : C} (f : U ⟶ V) :
    (J.overMapPullback (ModuleCat.{w} Λ) f).Additive where
  map_add := by intros; rfl

/-- The canonical maps to the constant sheaves are natural in the module. -/
private theorem comp_toSheafify_const_app {M N : ModuleCat.{w} Λ} (f : M ⟶ N) (U : Cᵒᵖ) :
    f ≫ (toSheafify J ((Functor.const Cᵒᵖ).obj N)).app U =
      (toSheafify J ((Functor.const Cᵒᵖ).obj M)).app U ≫
        ((constantSheaf J (ModuleCat.{w} Λ)).map f).hom.app U :=
  congrArg (fun t => t.app U) (toSheafify_naturality J ((Functor.const Cᵒᵖ).map f))

/-- **The chain-map lifting step.** Let `P` be a complex of finite projective `Λ`-modules which is
nonzero in only finitely many degrees and let `T` be any complex of `Λ`-modules. A family of maps
`P^n ⟶ Γ(U, T̲^n)` compatible with the differentials lifts, on a covering sieve of `U`, to an
honest map of complexes `P ⟶ T` inducing it. -/
lemma exists_cover_chainMap_of_constantSections
    [J.WEqualsLocallyBijective (ModuleCat.{w} Λ)]
    (P T : CochainComplex (ModuleCat.{w} Λ) ℤ)
    (hs : {n : ℤ | ¬ IsZero (P.X n)}.Finite)
    (hfin : ∀ n : ℤ, Module.Finite Λ (P.X n))
    (hproj : ∀ n : ℤ, Module.Projective Λ (P.X n)) (U : C)
    (φ : ∀ n, P.X n ⟶ ((constantSheaf J (ModuleCat.{w} Λ)).obj (T.X n)).obj.obj (op U))
    (hφ : ∀ n m, φ n ≫ ((constantSheaf J (ModuleCat.{w} Λ)).map (T.d n m)).hom.app (op U) =
      P.d n m ≫ φ m) :
    ∃ S : Sieve U, S ∈ J U ∧ ∀ {V : C} (f : V ⟶ U), S f →
      ∃ g : P ⟶ T, ∀ n,
        g.f n ≫ (toSheafify J ((Functor.const Cᵒᵖ).obj (T.X n))).app (op V) =
          φ n ≫ ((constantSheaf J (ModuleCat.{w} Λ)).obj (T.X n)).obj.map f.op := by
  classical
  let c := constantSheaf J (ModuleCat.{w} Λ)
  let η (n : ℤ) := toSheafify J ((Functor.const Cᵒᵖ).obj (T.X n))
  have hlift (n : ℤ) := by
    let := hfin n
    let := hproj n
    have := (J.W_toSheafify ((Functor.const Cᵒᵖ).obj (T.X n))).isLocallySurjective
    exact exists_cover_lift_of_finite_projective J (η n) U (φ n).hom
  choose S hS hg using hlift
  refine ⟨hs.toFinset.inf S, Stacks.SheafOfModules.FiniteTypeKernel.finsetInf_mem J _ S
    (fun n _ => hS n), ?_⟩
  intro V f hf
  by_cases hV : (⊥ : Sieve V) ∈ J V
  · exact ⟨0, fun n => ((c.obj (T.X n)).isTerminalOfBotCover V hV).hom_ext _ _⟩
  have hex (n : ℤ) : ∃ g : P.X n ⟶ T.X n,
      g ≫ (η n).app (op V) = φ n ≫ (c.obj (T.X n)).obj.map f.op := by
    by_cases hn : n ∈ hs.toFinset
    · obtain ⟨g, hg⟩ := hg n f ((Finset.inf_le (f := S) hn) _ hf)
      exact ⟨ModuleCat.ofHom g, ModuleCat.hom_ext hg⟩
    · have hz : IsZero (P.X n) := by
        by_contra h
        exact hn (hs.mem_toFinset.mpr h)
      exact ⟨0, hz.eq_of_src _ _⟩
  choose g hg using hex
  have hcomm (n m : ℤ) : g n ≫ T.d n m = P.d n m ≫ g m := by
    have hnat : T.d n m ≫ (η m).app (op V) =
        (η n).app (op V) ≫ (c.map (T.d n m)).hom.app (op V) :=
      comp_toSheafify_const_app J (T.d n m) (op V)
    have he : (g n ≫ T.d n m) ≫ (η m).app (op V) =
        (P.d n m ≫ g m) ≫ (η m).app (op V) :=
      Eq.trans (Category.assoc _ _ _) <|
      Eq.trans (congrArg (fun t => g n ≫ t) hnat) <|
      Eq.trans (Category.assoc _ _ _).symm <|
      Eq.trans (congrArg (fun t => t ≫ (c.map (T.d n m)).hom.app (op V)) (hg n)) <|
      Eq.trans (Category.assoc _ _ _) <|
      Eq.trans (congrArg (fun t => φ n ≫ t) ((c.map (T.d n m)).hom.naturality f.op)) <|
      Eq.trans (Category.assoc _ _ _).symm <|
      Eq.trans (congrArg (fun t => t ≫ (c.obj (T.X m)).obj.map f.op) (hφ n m)) <|
      Eq.trans (Category.assoc _ _ _) <|
      Eq.trans (congrArg (fun t => P.d n m ≫ t) (hg m).symm) (Category.assoc _ _ _).symm
    refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    exact injective_toSheafify_const_app J (T.X m) V hV (ConcreteCategory.congr_hom he x)
  exact ⟨{ f := g, comm' := fun n m _ => hcomm n m }, hg⟩

/-- **The local constancy of a map of complexes of constant sheaves of modules.** Let `P` be a
complex of finite projective `Λ`-modules which is nonzero in only finitely many degrees, let `T`
be any complex of `Λ`-modules, and write `P̲`, `T̲` for the associated complexes of constant
sheaves of `Λ`-modules. A map of complexes `β : P̲|_U ⟶ T̲|_U` on a slice site is, after
restriction along the arrows of a covering sieve of `U`, the image of an honest map of complexes
`P ⟶ T` of `Λ`-modules.

This is the content Stacks 09BE adds to Stacks 09BD at the level of complexes, i.e. the
application of Stacks 093S (3) made in the source's proof. -/
@[stacks 09BE "local_constancy_of_a_map_of_constant_complexes"]
theorem exists_cover_overPullback_eq_constantSheaf_mapHomologicalComplex
    [J.WEqualsLocallyBijective (ModuleCat.{w} Λ)]
    [∀ V : C, HasWeakSheafify (J.over V) (ModuleCat.{w} Λ)]
    [∀ V : C, (J.over V).WEqualsLocallyBijective (ModuleCat.{w} Λ)]
    (P T : CochainComplex (ModuleCat.{w} Λ) ℤ)
    (hs : {n : ℤ | ¬ IsZero (P.X n)}.Finite)
    (hfin : ∀ n : ℤ, Module.Finite Λ (P.X n))
    (hproj : ∀ n : ℤ, Module.Projective Λ (P.X n)) (U : C)
    (β : ((J.overPullback (ModuleCat.{w} Λ) U).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((constantSheaf J (ModuleCat.{w} Λ)).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ⟶
      ((J.overPullback (ModuleCat.{w} Λ) U).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((constantSheaf J (ModuleCat.{w} Λ)).mapHomologicalComplex (ComplexShape.up ℤ)).obj T)) :
    ∃ S : Sieve U, S ∈ J U ∧ ∀ {V : C} (f : V ⟶ U), S f →
      ∃ g : P ⟶ T, ∀ n,
        (J.overMapPullback (ModuleCat.{w} Λ) f).map (β.f n) =
          (J.overPullback (ModuleCat.{w} Λ) V).map
            ((constantSheaf J (ModuleCat.{w} Λ)).map (g.f n)) := by
  let c := constantSheaf J (ModuleCat.{w} Λ)
  let η (n : ℤ) := toSheafify J ((Functor.const Cᵒᵖ).obj (P.X n))
  let φ (n : ℤ) := (η n).app (op U) ≫ (β.f n).hom.app (op (Over.mk (𝟙 U)))
  have hφ (n m : ℤ) : φ n ≫ (c.map (T.d n m)).hom.app (op U) = P.d n m ≫ φ m := by
    have hb : (β.f n).hom.app (op (Over.mk (𝟙 U))) ≫ (c.map (T.d n m)).hom.app (op U) =
        (c.map (P.d n m)).hom.app (op U) ≫ (β.f m).hom.app (op (Over.mk (𝟙 U))) :=
      congrArg (fun k => k.hom.app (op (Over.mk (𝟙 U)))) (β.comm n m)
    have hη : P.d n m ≫ (η m).app (op U) =
        (η n).app (op U) ≫ (c.map (P.d n m)).hom.app (op U) :=
      comp_toSheafify_const_app J (P.d n m) (op U)
    exact Eq.trans (Category.assoc _ _ _) <|
      Eq.trans (congrArg (fun t => (η n).app (op U) ≫ t) hb) <|
      Eq.trans (Category.assoc _ _ _).symm <|
      Eq.trans (congrArg (fun t => t ≫ (β.f m).hom.app (op (Over.mk (𝟙 U)))) hη.symm) <|
      Category.assoc _ _ _
  obtain ⟨S, hS, h⟩ :=
    exists_cover_chainMap_of_constantSections J P T hs hfin hproj U φ hφ
  refine ⟨S, hS, fun {V} f hf => ?_⟩
  obtain ⟨g, hg⟩ := h f hf
  refine ⟨g, fun n => ?_⟩
  refine overPullback_constantSheaf_hom_ext J V (P.X n) _ _ _ ?_
  have hηg : g.f n ≫ (toSheafify J ((Functor.const Cᵒᵖ).obj (T.X n))).app (op V) =
      (η n).app (op V) ≫ (c.map (g.f n)).hom.app (op V) :=
    comp_toSheafify_const_app J (g.f n) (op V)
  have hb : (c.obj (P.X n)).obj.map f.op ≫ (β.f n).hom.app (op (Over.mk (𝟙 V ≫ f))) =
      (β.f n).hom.app (op (Over.mk (𝟙 U))) ≫ (c.obj (T.X n)).obj.map f.op :=
    (β.f n).hom.naturality (Over.homMk f (by simp) :
      Over.mk (𝟙 V ≫ f) ⟶ Over.mk (𝟙 U)).op
  have hu : (η n).app (op V) = (η n).app (op U) ≫ (c.obj (P.X n)).obj.map f.op :=
    (η n).naturality f.op
  show (η n).app (op V) ≫ (β.f n).hom.app (op (Over.mk (𝟙 V ≫ f))) =
    (η n).app (op V) ≫ (c.map (g.f n)).hom.app (op V)
  refine Eq.trans ?_ hηg
  refine Eq.trans ?_ (hg n).symm
  exact Eq.trans (congrArg (fun t => t ≫ (β.f n).hom.app (op (Over.mk (𝟙 V ≫ f)))) hu) <|
    Eq.trans (Category.assoc _ _ _) <|
    Eq.trans (congrArg (fun t => (η n).app (op U) ≫ t) hb) (Category.assoc _ _ _).symm

end Stacks.ConstantSheaf

end
