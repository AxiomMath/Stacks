module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.ComplementFormalFunctionsHigher
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.ComplementSheafCohomologyComparison
public import StacksCore.Tactic.StacksAttribute

/-!
# Formal functions in higher degrees, for sheaf cohomology on the complement

Let `A` be a Noetherian ring which is `f`-adically complete, let `f ∈ 𝔞` for a finitely generated
ideal `𝔞`, let `M` be a finite `A`-module, let `s ≥ 0`, and assume `H^k_𝔞(M)` is annihilated by
a power of `f` for every `k ≤ s + 1`. Then with `U = Spec(A) ∖ V(𝔞)` the canonical map

`H^i(U, M̃) ⟶ lim_n H^i(U, (M/fⁿM)̃)`

of sheaf cohomology groups on the open subscheme `U` is a bijection for every `i < s`. This is
[Stacks, Tag 0EKM].

`StacksFrontier/AlgebraicGeometry/FormalGeometry/ComplementFormalFunctionsHigher.lean` proves the
statement for the Čech cone model `Stacks.Algebraization.complementCohomologyFunctor` of
`H^i(U, -)`. Here it is transported to the sheaf cohomology `Hfunctor` of [Stacks, Tag 01E3] of
`M̃|U` on the open subscheme `U`, along the natural isomorphism
`Stacks.Algebraization.ComplementSheafComparison.hfunctorComplementTildeIso` between the two
models: a natural isomorphism of functors carries the compatible sequences of one tower to those
of the other, and the canonical map of one model to the canonical map of the other.

## Main definitions

* `Stacks.Algebraization.towerSectionsMapOf`: for a functor `F` to abelian groups and a tower
  `X₀ ⟵ X₁ ⟵ ⋯` under an object `M`, the canonical map from `F(M)` to the compatible sequences of
  the tower `F(Xₙ)`.
* `Stacks.Algebraization.HigherComplementTower.sheafCohomologyToTowerSections`: the canonical map
  `H^i(U, M̃) ⟶ lim_n H^i(U, (M/fⁿM)̃)` of sheaf cohomology on `U`.

## Main results

* `Stacks.Algebraization.bijective_towerSectionsMapOf_of_iso`: bijectivity of the canonical map is
  invariant under a natural isomorphism of functors.
* `Stacks.Algebraization.HigherComplementTower.bijective_sheafCohomologyToTowerSections` —
  **Stacks 0EKM**.

## References

* [Stacks Project, Tag 0EKM](https://stacks.math.columbia.edu/tag/0EKM)
* [Stacks Project, Tag 01E3](https://stacks.math.columbia.edu/tag/01E3)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open Stacks.LocalCohomology

universe u

namespace Stacks.Algebraization

/-! ### Compatible sequences of a tower, transported along a natural isomorphism -/

section Transport

variable {C : Type*} [Category C] (F : C ⥤ AddCommGrpCat.{u}) {M : C} (X : ℕ → C)
  (π : ∀ n, M ⟶ X n) (τ : ∀ n, X (n + 1) ⟶ X n) (hπ : ∀ n, π (n + 1) ≫ τ n = π n)

/-- **The canonical map into the inverse limit of a tower.** For a functor `F` to abelian groups
and maps `π n : M ⟶ X n` compatible with the transition maps `τ n : X (n + 1) ⟶ X n`, the map
sending `m ∈ F(M)` to the compatible sequence `(F(π n) m)ₙ` of the tower `F(Xₙ)`. -/
def towerSectionsMapOf (m : F.obj M) :
    {x : ∀ n, F.obj (X n) // ∀ n, ConcreteCategory.hom (F.map (τ n)) (x (n + 1)) = x n} :=
  ⟨fun n ↦ ConcreteCategory.hom (F.map (π n)) m, fun n ↦ by
    rw [← ConcreteCategory.comp_apply, ← F.map_comp, hπ]⟩

/-- **Bijectivity of the canonical map is invariant under a natural isomorphism.** -/
theorem bijective_towerSectionsMapOf_of_iso {G : C ⥤ AddCommGrpCat.{u}} (e : F ≅ G)
    (h : Function.Bijective (towerSectionsMapOf G X π τ hπ)) :
    Function.Bijective (towerSectionsMapOf F X π τ hπ) := by
  have hinj : ∀ Y : C, Function.Injective (ConcreteCategory.hom (e.hom.app Y)) := fun Y ↦
    (ConcreteCategory.bijective_of_isIso (e.hom.app Y)).1
  have hinv : ∀ (Y : C) (y : G.obj Y),
      ConcreteCategory.hom (e.hom.app Y) (ConcreteCategory.hom (e.inv.app Y) y) = y := fun Y y ↦
    by rw [← ConcreteCategory.comp_apply, Iso.inv_hom_id_app, ConcreteCategory.id_apply]
  let ψ : {x : ∀ n, F.obj (X n) // ∀ n, ConcreteCategory.hom (F.map (τ n)) (x (n + 1)) = x n} →
      {x : ∀ n, G.obj (X n) // ∀ n, ConcreteCategory.hom (G.map (τ n)) (x (n + 1)) = x n} :=
    fun x ↦ ⟨fun n ↦ ConcreteCategory.hom (e.hom.app (X n)) (x.1 n), fun n ↦ by
      rw [← ConcreteCategory.comp_apply, ← e.hom.naturality, ConcreteCategory.comp_apply, x.2 n]⟩
  have hψ : Function.Injective ψ := fun x y hxy ↦ Subtype.ext (funext fun n ↦
    hinj (X n) (congrFun (congrArg Subtype.val hxy) n))
  have key : ∀ m : F.obj M, ψ (towerSectionsMapOf F X π τ hπ m) =
      towerSectionsMapOf G X π τ hπ (ConcreteCategory.hom (e.hom.app M) m) := fun m ↦
    Subtype.ext (funext fun n ↦ by
      change ConcreteCategory.hom (e.hom.app (X n)) (ConcreteCategory.hom (F.map (π n)) m) =
        ConcreteCategory.hom (G.map (π n)) (ConcreteCategory.hom (e.hom.app M) m)
      rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, e.hom.naturality])
  refine ⟨fun a b hab ↦ hinj M (h.1 ?_), fun y ↦ ?_⟩
  · rw [← key, ← key, hab]
  · obtain ⟨m, hm⟩ := h.2 (ψ y)
    refine ⟨ConcreteCategory.hom (e.inv.app M) m, hψ ?_⟩
    rw [key, hinv, hm]

end Transport

end Stacks.Algebraization

namespace Stacks.Algebraization.HigherComplementTower

open Stacks.Algebraization Stacks.Algebraization.ComplementSheafComparison

variable {A : Type u} [CommRing A] (I : Ideal A) (f : A) (M : ModuleCat.{u} A)

/-- The cohomology `H^i(U, (-)~|U)` of [Stacks, Tag 01E3] on the open subscheme
`U = Spec A ∖ V(I)`, as a functor of the module. -/
abbrev sheafCohomologyComplement (i : ℕ) : ModuleCat.{u} A ⥤ AddCommGrpCat.{u} :=
  complementTildeFunctor A I ⋙ Hfunctor (complementZeroLocus A I : Scheme).ringCatSheaf ⊤ i

/-- **The canonical map `H^i(U, M̃) ⟶ lim_n H^i(U, (M/fⁿM)̃)`** of sheaf cohomology on the open
subscheme `U = Spec A ∖ V(I)`, whose `n`-th component is the map induced by the reduction
`M ⟶ M / fⁿM`; the inverse limit is the group of compatible sequences of the tower. -/
def sheafCohomologyToTowerSections (i : ℕ) :=
  towerSectionsMapOf (sheafCohomologyComplement I i) (fun n ↦ (powerQuotientShortComplex f M n).X₃)
    (fun n ↦ (powerQuotientShortComplex f M n).g)
    (fun n ↦ (powerQuotientSESMap f M (Nat.le_succ n)).τ₃)
    (fun n ↦ powerQuotient_g_comp_τ₃ f M (Nat.le_succ n))

/-- Let `A` be a Noetherian ring. Let `f ∈ 𝔞 ⊆ A` be an element of an ideal of `A`. Let `M` be a
finite `A`-module and let `s ≥ 0`. Assume `A` is `f`-adically complete and `H^k_𝔞(M)` is
annihilated by a power of `f` for `k ≤ s + 1`. Then with `U = Spec(A) ∖ V(𝔞)` the canonical map
`H^i(U, M̃) ⟶ lim_n H^i(U, (M/fⁿM)̃)` of sheaf cohomology on `U` is a bijection for every `i < s`.

The ideal is finitely generated because `A` is Noetherian; the statement for the Čech cone model
of `H^i(U, -)` attached to a finite family of generators is
`Stacks.Algebraization.HigherComplementTower.bijective_toTowerSections`, and the natural
isomorphism `Stacks.Algebraization.ComplementSheafComparison.hfunctorComplementTildeIso` between
the two models transports it. -/
@[stacks 0EKM "H^i(U, -) is the sheaf cohomology of Stacks 01E3 on the open subscheme \
U = Spec(A) ∖ V(𝔞), and the inverse limit is the group of compatible sequences of the tower of \
the H^i(U, (M/fⁿM)~)"]
theorem bijective_sheafCohomologyToTowerSections [IsNoetherianRing A] (hf : f ∈ I)
    [Module.Finite A M] [IsAdicComplete (Ideal.span {f}) A] (s : ℕ)
    (hann : ∀ k : ℕ, k ≤ s + 1 → ∃ c : ℕ,
      ∀ x : localCohomologyModule A I (Ideal.fg_of_isNoetherianRing I) M (k : ℤ), f ^ c • x = 0)
    (i : ℕ) (hi : i < s) :
    Function.Bijective (sheafCohomologyToTowerSections I f M i) := by
  obtain ⟨r, fam, hfam⟩ :=
    Submodule.fg_iff_exists_fin_generating_family.1 (Ideal.fg_of_isNoetherianRing I)
  exact bijective_towerSectionsMapOf_of_iso _ _ _ _ _
    (hfunctorComplementTildeIso fam I hfam (Ideal.fg_of_isNoetherianRing I) i)
    (bijective_toTowerSections (Ideal.fg_of_isNoetherianRing I) fam hfam f hf M s hann i hi)

end Stacks.Algebraization.HigherComplementTower

end
