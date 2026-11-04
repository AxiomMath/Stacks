module

public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.EpiMono
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-!
# Natural transformations out of a functor on modules are determined on the free module

Let `F : Mod_A ⥤ D` be a functor which preserves coproducts indexed by `Type u` and
epimorphisms, for instance a right exact functor commuting with direct sums. Every `A`-module
`M` is a quotient of the free module `⨁_{m ∈ M} A`, so `F(M)` is a quotient of
`∐_{m ∈ M} F(A)`, and a natural transformation `F ⟶ G` to any functor `G` is determined by its
component at the free module `A` of rank one. This is the uniqueness half of the
Eilenberg–Watts description of right exact functors between module categories.

## Main definitions

* `ModuleCat.sigmaRegularDesc`: the canonical epimorphism `⨁_{m ∈ M} A ⟶ M`.

## Main results

* `ModuleCat.natTrans_ext_of_app_self`: two natural transformations `F ⟶ G` agreeing at
  `ModuleCat.of A A` are equal.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace ModuleCat

variable {A : Type u} [Ring A] {D : Type v} [Category.{w} D]

/-- The canonical epimorphism `⨁_{m ∈ M} A ⟶ M`, `1` in the summand of `m` going to `m`. -/
noncomputable def sigmaRegularDesc (M : ModuleCat.{u} A) :
    ∐ (fun _ : M => ModuleCat.of A A) ⟶ M :=
  Sigma.desc fun m => ModuleCat.ofHom (LinearMap.toSpanSingleton A M m)

/-- The canonical map `⨁_{m ∈ M} A ⟶ M` is an epimorphism. -/
instance (M : ModuleCat.{u} A) : Epi (sigmaRegularDesc M) := by
  refine ⟨fun {X} h₁ h₂ e => ModuleCat.hom_ext (LinearMap.ext fun m => ?_)⟩
  have h := congrArg (fun k => (Sigma.ι (fun _ : M => ModuleCat.of A A) m ≫ k).hom (1 : A)) e
  simpa [sigmaRegularDesc] using h

/-- **Natural transformations out of a functor on modules are determined on the free module of
rank one.** If `F : Mod_A ⥤ D` preserves coproducts indexed by `Type u` and epimorphisms, two
natural transformations `F ⟶ G` which agree at `A` are equal. -/
theorem natTrans_ext_of_app_self {F G : ModuleCat.{u} A ⥤ D}
    [∀ J : Type u, PreservesColimitsOfShape (Discrete J) F] [F.PreservesEpimorphisms]
    {α β : F ⟶ G} (h : α.app (ModuleCat.of A A) = β.app (ModuleCat.of A A)) : α = β := by
  ext M
  rw [← cancel_epi (F.map (sigmaRegularDesc M)), α.naturality, β.naturality]
  congr 1
  refine (isColimitOfPreserves F
    (colimit.isColimit (Discrete.functor fun _ : M => ModuleCat.of A A))).hom_ext fun j => ?_
  simp only [Functor.mapCocone_ι_app, colimit.cocone_ι]
  exact (α.naturality _).trans ((congrArg (· ≫ G.map _) h).trans (β.naturality _).symm)

end ModuleCat
