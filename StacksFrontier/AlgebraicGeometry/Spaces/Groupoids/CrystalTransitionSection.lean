module

public import StacksFrontier.AlgebraicGeometry.Descent.SectionsPullbackComparison.GeneratingFamily
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.CrystalsInQuasicoherentModules

/-!
# The transition maps on sections of a crystal

Let `X = ({X i}, {f φ})` be a system of schemes and let `(F, α)` be a crystal in quasi-coherent
modules on it.  For `φ ∈ Φ` with `j φ = (i, i')`, an open `U ⊆ X i` and an open `V ⊆ X i'` with
`V ⊆ (f φ)⁻¹ U`, pulling a section of `F i` over `U` back along `f φ` and pushing it into `F i'`
along `α φ` gives a map on sections `Γ(F i, U) → Γ(F i', V)`.  This file sets up that map and
proves the fact about it that the exhaustion half of Stacks 077Z rests on: over a pair of affine
opens it is *surjective up to spans*, that is, the sections of `F i'` over `V` are generated over
`Γ(X i', V)` by the transitions of the sections of `F i` over `U`.

That statement is the crystal-theoretic form of
`AlgebraicGeometry.span_pullbackSection_eq_top`, which is the same assertion for the pullback
`(f φ)^* (F i)` itself; the comparison isomorphism `α φ` transports it, because an isomorphism of
`𝒪_X`-modules is bijective and semilinear on sections over every open.

## Main definitions

* `Stacks.AlgebraicGeometry.Crystals.Crystal.transitionSection`: the map on sections.
* `Stacks.AlgebraicGeometry.Crystals.appₗ`: the action of a morphism of `𝒪_X`-modules on the
  sections over an open, as a `Γ(X, U)`-linear map.

## Main results

* `Stacks.AlgebraicGeometry.Crystals.Crystal.span_transitionSection_eq_top`: over affine opens
  `U ⊆ X i` and `V ⊆ X i'` with `V ⊆ (f φ)⁻¹ U`, the sections of `F i'` over `V` are generated
  over `Γ(X i', V)` by the transitions of the sections of `F i` over `U`.
* `Stacks.AlgebraicGeometry.Crystals.Crystal.exists_finite_subset_span_transition`: for affine
  opens `U ⊆ X i` and `V ⊆ X i'`, every section of `F i'` over `V` is, whenever
  `V ⊆ (f φ)⁻¹ U`, a finite combination of transitions of finitely many sections of `F i` over
  `U`.

## References

* [Stacks Project, Tag 077Z](https://stacks.math.columbia.edu/tag/077Z)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.Crystals

/-- **The action of a morphism of `𝒪_X`-modules on sections, as a linear map.**  The sections of
an `𝒪_X`-module over an open `U` form a `Γ(X, U)`-module and a morphism of modules acts on them
`Γ(X, U)`-linearly. -/
def appₗ {X : Scheme.{u}} {A B : X.Modules} (g : A ⟶ B) (V : X.Opens) :
    Γ(A, V) →ₗ[Γ(X, V)] Γ(B, V) where
  toFun := g.app V
  map_add' x y := by simp
  map_smul' r x := by simp

/-- The linear map `appₗ g V` sends a section `x` to `g.app V x`. -/
@[simp]
theorem appₗ_apply {X : Scheme.{u}} {A B : X.Modules} (g : A ⟶ B) (V : X.Opens)
    (x : Γ(A, V)) : appₗ g V x = g.app V x := rfl

/-- The action on sections of an isomorphism of `𝒪_X`-modules is surjective. -/
theorem surjective_appₗ {X : Scheme.{u}} {A B : X.Modules} (g : A ⟶ B) [IsIso g]
    (V : X.Opens) : Function.Surjective (appₗ g V) := fun x =>
  ⟨(inv g).app V x, by
    rw [appₗ_apply, Scheme.Modules.inv_app, ← ConcreteCategory.comp_apply, IsIso.inv_hom_id,
      ConcreteCategory.id_apply]⟩

namespace Crystal

variable {D : SchemeSystem.{u}} (M : Crystal D)

/-- **The transition map on sections of a crystal.**  For `φ` with `j φ = (i, i')`, an open
`U ⊆ X i` and an open `V ⊆ X i'` inside `(f φ)⁻¹ U`, a section of `F i` over `U` is pulled back
along `f φ` and pushed into `F i'` by the comparison isomorphism `α φ`. -/
def transitionSection (φ : D.Φ) (U : (D.X (D.j φ).1).Opens) (V : (D.X (D.j φ).2).Opens)
    (h : V ≤ (D.f φ) ⁻¹ᵁ U) (a : Γ(M.F (D.j φ).1, U)) : Γ(M.F (D.j φ).2, V) :=
  (M.α φ).hom.app V (pullbackSectionHom (D.f φ) (M.F (D.j φ).1) U V h a)

/-- The transition map on sections is semilinear in the same way as pulling a section back: a
function on `V` pulled up from `U` can be moved across it. -/
theorem transitionSection_smul (φ : D.Φ) (U : (D.X (D.j φ).1).Opens)
    (V : (D.X (D.j φ).2).Opens) (h : V ≤ (D.f φ) ⁻¹ᵁ U) (r : Γ(D.X (D.j φ).1, U))
    (a : Γ(M.F (D.j φ).1, U)) :
    M.transitionSection φ U V h (r • a)
      = (D.f φ).appLE U V h r • M.transitionSection φ U V h a := by
  rw [transitionSection, pullbackSectionHom_smul, transitionSection,
    Scheme.Modules.Hom.app_smul]

/-- **The transitions of the sections over an affine open generate the sections over an affine
open above it.**  This is `AlgebraicGeometry.span_pullbackSection_eq_top` transported along the
comparison isomorphism `α φ`, which is bijective and linear on sections. -/
theorem span_transitionSection_eq_top (φ : D.Φ) {U : (D.X (D.j φ).1).Opens} (hU : IsAffineOpen U)
    {V : (D.X (D.j φ).2).Opens} (hV : IsAffineOpen V) (h : V ≤ (D.f φ) ⁻¹ᵁ U) :
    Submodule.span Γ(D.X (D.j φ).2, V)
      (Set.range fun a : Γ(M.F (D.j φ).1, U) => M.transitionSection φ U V h a) = ⊤ := by
  have : (M.F (D.j φ).1).IsQuasicoherent := M.isQuasicoherent _
  have hrange : (Set.range fun a : Γ(M.F (D.j φ).1, U) => M.transitionSection φ U V h a)
      = appₗ (M.α φ).hom V ''
        Set.range fun a : Γ(M.F (D.j φ).1, U) =>
          pullbackSectionHom (D.f φ) (M.F (D.j φ).1) U V h a := by
    rw [← Set.range_comp]
    rfl
  rw [hrange, Submodule.span_image, span_pullbackSection_eq_top (D.f φ) (M.F (D.j φ).1) hU hV h,
    Submodule.map_top]
  exact LinearMap.range_eq_top.mpr (surjective_appₗ (M.α φ).hom V)

/-- **Every section over an affine open is a finite combination of transitions of finitely many
sections over an affine open below it.**  For affine opens `U` and `V`, there is a finite set
`s` of sections of `F i` over `U` such that, whenever `V ⊆ (f φ)⁻¹ U`, the section `m` lies in
the span of the transitions of the elements of `s`. -/
theorem exists_finite_subset_span_transition (φ : D.Φ) (U : (D.X (D.j φ).1).affineOpens)
    (V : (D.X (D.j φ).2).affineOpens) (m : Γ(M.F (D.j φ).2, V.1)) :
    ∃ s : Set Γ(M.F (D.j φ).1, U.1), s.Finite ∧ ∀ h : V.1 ≤ (D.f φ) ⁻¹ᵁ U.1,
      m ∈ Submodule.span Γ(D.X (D.j φ).2, V.1)
        ((fun a => M.transitionSection φ U.1 V.1 h a) '' s) := by
  classical
  by_cases h : V.1 ≤ (D.f φ) ⁻¹ᵁ U.1
  · have hm : m ∈ Submodule.span Γ(D.X (D.j φ).2, V.1)
        (Set.range fun a : Γ(M.F (D.j φ).1, U.1) => M.transitionSection φ U.1 V.1 h a) := by
      rw [M.span_transitionSection_eq_top φ U.2 V.2 h]
      trivial
    obtain ⟨n, c, y, hy⟩ := Submodule.mem_span_set'.mp hm
    refine ⟨Set.range fun k : Fin n => (y k).2.choose, Set.finite_range _, fun h' => ?_⟩
    rw [← hy]
    refine Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    exact ⟨(y k).2.choose, Set.mem_range_self k, (y k).2.choose_spec⟩
  · exact ⟨∅, Set.finite_empty, fun h' => absurd h' h⟩

end Crystal

end Stacks.AlgebraicGeometry.Crystals

end
