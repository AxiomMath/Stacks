module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoherentFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Duality.ProperOverField.Duality
public import StacksFrontier.AlgebraicGeometry.Duality.ProperOverField.DualizingComplex
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.CoherentDerivedSubcategory
import StacksCore.Tactic.StacksAttribute

/-!
# The dualizing complex of a proper scheme over a field is characterized by duality

Let `X` be a proper scheme over a field `k` and `ω_X^• = a(𝒪_{Spec k})` the dualizing complex of
[Stacks, Tag 0FVV]. The footnote to part (5) of that lemma says that the functorial isomorphisms
`Ext^i_X(K, ω_X^•) = Hom_k(H^{-i}(X, K), k)` characterize `ω_X^•` in `D_QCoh(𝒪_X)` up to unique
isomorphism by the Yoneda lemma, and that since `ω_X^•` lies in `D^b_Coh(𝒪_X)` it suffices to let
`K` range over `D^b_Coh(𝒪_X)`.

Both characterizations need only degree zero: an object `ω` together with bijections
`Hom(K, ω) ≃ Hom_k(H⁰(X, K), k)`, natural in `K`, is isomorphic to `ω_X^•` by exactly one
isomorphism carrying them to the duality isomorphisms `α ↦ t ∘ H⁰(X, α)` of `ω_X^•`
(`t` the trace, `Stacks.Duality.traceOverField`).

## Main results

* `Stacks.Duality.boundedCoherent_relativeDualizingComplex_of_isProper`: `ω_X^• ∈ D^b_Coh(𝒪_X)`.
* `Stacks.Duality.existsUnique_iso_relativeDualizingComplex_of_homEquiv`: the characterization
  among the objects of any subcategory of `D_QCoh(𝒪_X)` containing `ω_X^•`.
* `Stacks.Duality.existsUnique_iso_relativeDualizingComplex_of_quasiCoherent`: in `D_QCoh(𝒪_X)`.
* `Stacks.Duality.existsUnique_iso_relativeDualizingComplex_of_boundedCoherent`: in
  `D^b_Coh(𝒪_X)`.

## References

* [Stacks Project, Tag 0FVV](https://stacks.math.columbia.edu/tag/0FVV)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Duality

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]

/-- **[Stacks, Tag 0FVV], footnote to part (5): `ω_X^•` lies in `D^b_Coh(𝒪_X)`.** Its cohomology
sheaves are coherent ([Stacks, Tag 0A89]) and vanish outside `[-dim X, 0]` (part (1)). -/
@[stacks 0FVV "footnote to part (5): ω_X^• is in D^b_Coh(O_X)"]
theorem boundedCoherent_relativeDualizingComplex_of_isProper :
    DerivedCategoryB.derivedCategoryBBounded (A := X.Modules) (isCoherentSheaf X)
      (relativeDualizingComplex f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
        (DerivedPushforward.derivedStructureSheaf (Spec (.of k)))).obj := by
  have := LocallyOfFiniteType.isLocallyNoetherian f
  refine ⟨⟨⟨_, isZero_homology_of_lt_of_isProper f⟩, ⟨0, fun n hn => ?_⟩⟩,
    mem_coherentDerivedCategory_of_isDualizingComplex X
      (isDualizingComplex_relativeDualizingComplex_of_isProper f)⟩
  by_contra h
  have := (le_zero_and_le_dim_of_not_isZero_homology_of_isProper f n h).1
  omega

/-- **The duality isomorphisms characterize `ω_X^•`.** Let `P` be a property of objects of
`D(𝒪_X)` satisfied by `ω_X^•` and only by objects of `D_QCoh(𝒪_X)`. If `ω` satisfies `P` and
`φ_K : Hom(K, ω) ≃ Hom_k(H⁰(X, K), k)` are bijections for the `K` satisfying `P`, natural in `K`,
then exactly one isomorphism `e : ω ≅ ω_X^•` carries `φ` to the duality isomorphisms
`α ↦ t ∘ H⁰(X, α)` of `ω_X^•`. -/
theorem existsUnique_iso_relativeDualizingComplex_of_homEquiv
    (P : ObjectProperty (DerivedCategory X.Modules))
    (hP : ∀ K, P K →
      DerivedCategoryB.derivedCategoryB (A := X.Modules)
        (SheafOfModules.isQuasicoherent X.ringCatSheaf) K)
    (hPω : P (relativeDualizingComplex f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
      (DerivedPushforward.derivedStructureSheaf (Spec (.of k)))).obj)
    (ω : DerivedCategory X.Modules) (hω : P ω)
    (φ : ∀ K, P K → ((K ⟶ ω) ≃ ((DerivedCategory.homologyFunctor (ModuleCat k) 0).obj
      ((derivedGlobalSectionsOver f).obj K) ⟶ ModuleCat.of k k)))
    (hφ : ∀ {K L : DerivedCategory X.Modules} (hK : P K) (hL : P L) (g : K ⟶ L) (α : L ⟶ ω),
      φ K hK (g ≫ α) =
        (DerivedCategory.homologyFunctor (ModuleCat k) 0).map
          ((derivedGlobalSectionsOver f).map g) ≫ φ L hL α) :
    ∃! e : ω ≅ (relativeDualizingComplex f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
        (DerivedPushforward.derivedStructureSheaf (Spec (.of k)))).obj,
      ∀ (K : DerivedCategory X.Modules) (hK : P K) (α : K ⟶ ω),
        (DerivedCategory.homologyFunctor (ModuleCat k) 0).map
          ((derivedGlobalSectionsOver f).map (α ≫ e.hom)) ≫ traceOverField f = φ K hK α := by
  set W := (relativeDualizingComplex f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
    (DerivedPushforward.derivedStructureSheaf (Spec (.of k)))).obj
  let ψ : ∀ K : DerivedCategory X.Modules, (K ⟶ W) → _ := fun K g =>
    (DerivedCategory.homologyFunctor (ModuleCat k) 0).map
      ((derivedGlobalSectionsOver f).map g) ≫ traceOverField f
  have hψ : ∀ K, P K → Function.Bijective (ψ K) := fun K hK =>
    bijective_homologyFunctor_map_comp_traceOverField f ⟨K, hP K hK⟩
  have nat : ∀ {K L : DerivedCategory X.Modules} (g : K ⟶ L) (β : L ⟶ W),
      ψ K (g ≫ β) = (DerivedCategory.homologyFunctor (ModuleCat k) 0).map
        ((derivedGlobalSectionsOver f).map g) ≫ ψ L β := by
    intro K L g β
    simp only [ψ, Functor.map_comp, Category.assoc]
  let hom : ω ⟶ W := (Equiv.ofBijective _ (hψ ω hω)).symm (φ ω hω (𝟙 ω))
  have hhom : ψ ω hom = φ ω hω (𝟙 ω) := (Equiv.ofBijective _ (hψ ω hω)).apply_symm_apply _
  let inv : W ⟶ ω := (φ W hPω).symm (ψ W (𝟙 W))
  have hinv : φ W hPω inv = ψ W (𝟙 W) := (φ W hPω).apply_symm_apply _
  have h₁ : ∀ K (hK : P K) (α : K ⟶ ω), ψ K (α ≫ hom) = φ K hK α := by
    intro K hK α
    rw [nat, hhom, ← hφ hK hω, Category.comp_id]
  have h₂ : ∀ K (hK : P K) (β : K ⟶ W), φ K hK (β ≫ inv) = ψ K β := by
    intro K hK β
    rw [hφ hK hPω, hinv, ← nat, Category.comp_id]
  refine ⟨⟨hom, inv, ?_, ?_⟩, h₁, fun e he => ?_⟩
  · exact (φ ω hω).injective (by rw [h₂ ω hω hom, hhom])
  · exact (hψ W hPω).1 (by rw [h₁ W hPω inv, hinv])
  · refine Iso.ext ((hψ ω hω).1 ?_)
    rw [hhom, ← he ω hω (𝟙 ω), Category.id_comp]

/-- **[Stacks, Tag 0FVV], footnote to part (5): the duality isomorphisms characterize `ω_X^•` in
`D_QCoh(𝒪_X)` up to unique isomorphism.** If `ω ∈ D_QCoh(𝒪_X)` has bijections
`Hom(K, ω) ≃ Hom_k(H⁰(X, K), k)` natural in `K ∈ D_QCoh(𝒪_X)`, then exactly one isomorphism
`ω ≅ ω_X^•` carries them to the duality isomorphisms of `ω_X^•` (degree zero of part (5)). -/
@[stacks 0FVV "footnote to part (5): the isomorphisms characterize ω_X^• in D_QCoh(O_X) up to \
unique isomorphism"]
theorem existsUnique_iso_relativeDualizingComplex_of_quasiCoherent
    (ω : quasiCoherentDerivedCategory X)
    (φ : ∀ K : quasiCoherentDerivedCategory X, (K.obj ⟶ ω.obj) ≃
      ((DerivedCategory.homologyFunctor (ModuleCat k) 0).obj
        ((derivedGlobalSectionsOver f).obj K.obj) ⟶ ModuleCat.of k k))
    (hφ : ∀ {K L : quasiCoherentDerivedCategory X} (g : K.obj ⟶ L.obj) (α : L.obj ⟶ ω.obj),
      φ K (g ≫ α) =
        (DerivedCategory.homologyFunctor (ModuleCat k) 0).map
          ((derivedGlobalSectionsOver f).map g) ≫ φ L α) :
    ∃! e : ω.obj ≅ (relativeDualizingComplex f
        (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
        (DerivedPushforward.derivedStructureSheaf (Spec (.of k)))).obj,
      ∀ (K : quasiCoherentDerivedCategory X) (α : K.obj ⟶ ω.obj),
        (DerivedCategory.homologyFunctor (ModuleCat k) 0).map
          ((derivedGlobalSectionsOver f).map (α ≫ e.hom)) ≫ traceOverField f = φ K α :=
  (existsUnique_iso_relativeDualizingComplex_of_homEquiv f
    (DerivedCategoryB.derivedCategoryB (A := X.Modules)
      (SheafOfModules.isQuasicoherent X.ringCatSheaf))
    (fun _ h => h) (relativeDualizingComplex f _ _).property ω.obj ω.property
    (fun K hK => φ ⟨K, hK⟩) (fun hK hL g α => hφ (K := ⟨_, hK⟩) (L := ⟨_, hL⟩) g α)).imp fun _ h =>
      ⟨fun K α => h.1 K.obj K.property α, fun e he => h.2 e fun K hK α => he ⟨K, hK⟩ α⟩

/-- **[Stacks, Tag 0FVV], footnote to part (5): it suffices to consider `K ∈ D^b_Coh(𝒪_X)`.** If
`ω ∈ D^b_Coh(𝒪_X)` has bijections `Hom(K, ω) ≃ Hom_k(H⁰(X, K), k)` natural in
`K ∈ D^b_Coh(𝒪_X)`, then exactly one isomorphism `ω ≅ ω_X^•` carries them to the duality
isomorphisms of `ω_X^•`; this uses that `ω_X^•` lies in `D^b_Coh(𝒪_X)`
(`Stacks.Duality.boundedCoherent_relativeDualizingComplex_of_isProper`). -/
@[stacks 0FVV "footnote to part (5): ω_X^• is characterized by the isomorphisms for K in \
D^b_Coh(O_X)"]
theorem existsUnique_iso_relativeDualizingComplex_of_boundedCoherent
    (ω : DerivedCategory X.Modules)
    (hω : DerivedCategoryB.derivedCategoryBBounded (A := X.Modules) (isCoherentSheaf X) ω)
    (φ : ∀ K : DerivedCategory X.Modules,
      DerivedCategoryB.derivedCategoryBBounded (A := X.Modules) (isCoherentSheaf X) K →
      ((K ⟶ ω) ≃ ((DerivedCategory.homologyFunctor (ModuleCat k) 0).obj
        ((derivedGlobalSectionsOver f).obj K) ⟶ ModuleCat.of k k)))
    (hφ : ∀ {K L : DerivedCategory X.Modules}
      (hK : DerivedCategoryB.derivedCategoryBBounded (A := X.Modules) (isCoherentSheaf X) K)
      (hL : DerivedCategoryB.derivedCategoryBBounded (A := X.Modules) (isCoherentSheaf X) L)
      (g : K ⟶ L) (α : L ⟶ ω),
      φ K hK (g ≫ α) =
        (DerivedCategory.homologyFunctor (ModuleCat k) 0).map
          ((derivedGlobalSectionsOver f).map g) ≫ φ L hL α) :
    ∃! e : ω ≅ (relativeDualizingComplex f
        (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
        (DerivedPushforward.derivedStructureSheaf (Spec (.of k)))).obj,
      ∀ (K : DerivedCategory X.Modules)
        (hK : DerivedCategoryB.derivedCategoryBBounded (A := X.Modules) (isCoherentSheaf X) K)
        (α : K ⟶ ω),
        (DerivedCategory.homologyFunctor (ModuleCat k) 0).map
          ((derivedGlobalSectionsOver f).map (α ≫ e.hom)) ≫ traceOverField f = φ K hK α :=
  existsUnique_iso_relativeDualizingComplex_of_homEquiv f _
    (fun _ hK n => have : _root_.SheafOfModules.IsCoherent _ := hK.2 n
      _root_.isQuasicoherent_of_isCoherent _)
    (boundedCoherent_relativeDualizingComplex_of_isProper f) ω hω φ hφ

end Stacks.Duality

end
