module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Kunneth.EtaleKunnethMap
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.SepClosedFieldConstantSheaf
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantRingEquivalence
public import StacksFrontier.RingTheory.Dualizing.MapDerivedCategory
public import Mathlib.CategoryTheory.Sites.DenseSubsite.InducedTopology

/-!
# `D((Spec k)_étale, Λ) ≃ D(Λ)` for a separably closed field `k`

Let `k` be a separably closed field and `Λ` a commutative ring. Every scheme étale over `Spec k`
is covered by sections of its structure morphism, so the terminal object of `(Spec k)_étale` is
a cover-dense subsite all by itself (`Stacks.EtaleCohomology.SepClosedField`). The topology it
induces on the one-object category is the trivial one, so by the comparison lemma sheaves on
`(Spec k)_étale` with values in any complete category `A` are the objects of `A`. Reading sheaves
of `Λ̲`-modules as sheaves of `Λ`-modules, this gives an equivalence

`Mod((Spec k)_étale, Λ̲) ≌ Mod(Λ)`,

and, an equivalence of abelian categories being exact, an equivalence of derived categories

`D((Spec k)_étale, Λ) ≌ D(Λ)`.

This is how [Stacks, Tag 0F1P] reads `RΓ(X, E)` as an object of `D(Λ)` when `X` lives over a
separably closed field.

## Main definitions

All in the namespace `Stacks.EtaleCohomology.EtaleCoefficients`.

* `sheafEquivOfSepClosed` — `Sheaf ((Spec k)_étale) A ≌ A`.
* `modulesEquivOfSepClosed` — `Mod((Spec k)_étale, Λ̲) ≌ ModuleCat Λ`, on the small model of
  `Stacks.EtaleCohomology.EtaleCoefficients`.
* `derivedModulesEquivOfSepClosed` — `D((Spec k)_étale, Λ) ≌ D(Λ)`.

## Main results

* `inducedTopology_pointFunctor_eq_bot` — the topology induced on the one-object category at the
  terminal object of `(Spec k)_étale` is the trivial one.

## Implementation notes

The compatibility of the equivalence with `⊗^L` is
`Stacks.EtaleCohomology.EtaleCoefficients.derivedModulesEquivOfSepClosedTensorIso`, in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.Kunneth.SeparablyClosedFieldTensor`. It is what
turns the Künneth map of `Stacks.EtaleCohomology.EtaleCoefficients.kunnethOverFieldMap` into a
map `RΓ(X, E) ⊗^L_Λ RΓ(Y, K) ⟶ RΓ(X ×_k Y, pr₁⁻¹E ⊗^L pr₂⁻¹K)` in `D(Λ)`.

## References

* [Stacks Project, Tag 0F1P](https://stacks.math.columbia.edu/tag/0F1P)
* [Stacks Project, Tag 04JQ](https://stacks.math.columbia.edu/tag/04JQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.EtaleCohomology.SepClosedField

universe t₂ t₁ u

namespace Stacks.EtaleCohomology.EtaleCoefficients

variable (k : Type u) [Field k] [IsSepClosed k]

/-- **The topology induced at the terminal object of `(Spec k)_étale` is trivial**: a sieve on
the one object covers only if it is the maximal sieve. Otherwise it is empty, and the empty
sieve does not cover the nonempty scheme `Spec k`. -/
theorem inducedTopology_pointFunctor_eq_bot :
    (pointFunctor k).inducedTopology (smallEtaleTopology (Spec (.of k))) = ⊥ := by
  ext X S
  rw [Functor.mem_inducedTopology_iff_of_isCoverDense, GrothendieckTopology.bot_covering]
  refine ⟨fun hS => ?_, fun h => h ▸ (Sieve.functorPushforward_top (pointFunctor k) X).symm ▸
    (smallEtaleTopology _).top_mem _⟩
  by_contra hne
  have hempty : ∀ {Y : Discrete PUnit.{1}} (f : Y ⟶ X), ¬ S f := by
    intro Y f hf
    obtain rfl : Y = X := Subsingleton.elim _ _
    obtain rfl : f = 𝟙 Y := Subsingleton.elim _ _
    exact hne (Sieve.id_mem_iff_eq_top.1 hf)
  have hcov : Sieve.ofArrows (fun i : PEmpty.{1} => i.elim) (fun i => i.elim) ∈
      smallEtaleTopology (Spec (.of k)) ((pointFunctor k).obj X) := by
    refine (smallEtaleTopology _).superset_covering ?_ hS
    rintro Z g ⟨Y, f, h, hf, rfl⟩
    exact (hempty f hf).elim
  have hu := (ofArrows_mem_smallEtaleTopology_iff _).1 hcov
  rw [Set.iUnion_of_empty] at hu
  have : Nonempty ↥((pointFunctor k).obj X).left :=
    inferInstanceAs (Nonempty ↥(Spec (.of k)))
  exact Set.empty_ne_univ hu

/-- On the one-object category with the topology induced from `(Spec k)_étale`, every presheaf is
a sheaf. -/
theorem isSheaf_inducedTopology_pointFunctor {A : Type t₁} [Category.{t₂} A]
    (P : (Discrete PUnit.{1})ᵒᵖ ⥤ A) :
    Presheaf.IsSheaf ((pointFunctor k).inducedTopology (smallEtaleTopology (Spec (.of k)))) P := by
  rw [inducedTopology_pointFunctor_eq_bot]
  exact Presheaf.isSheaf_bot P

/-- On the one-object category with the topology induced from `(Spec k)_étale`, the forgetful
functor from sheaves to presheaves is essentially surjective. -/
instance {A : Type t₁} [Category.{t₂} A] :
    (sheafToPresheaf ((pointFunctor k).inducedTopology (smallEtaleTopology (Spec (.of k))))
      A).EssSurj where
  mem_essImage P := ⟨⟨P, isSheaf_inducedTopology_pointFunctor k P⟩, ⟨Iso.refl _⟩⟩

/-- On the one-object category with the topology induced from `(Spec k)_étale`, the forgetful
functor from sheaves to presheaves is an equivalence. -/
instance {A : Type t₁} [Category.{t₂} A] :
    (sheafToPresheaf ((pointFunctor k).inducedTopology (smallEtaleTopology (Spec (.of k))))
      A).IsEquivalence where

/-- **Sheaves on `(Spec k)_étale` are the objects of `A`**, for `k` separably closed: the
comparison lemma along the terminal object, which is a cover-dense subsite, then the
identification of sheaves for the trivial topology on one object with the objects of `A`. -/
def sheafEquivOfSepClosed (A : Type t₁) [Category.{t₂} A]
    [∀ X : (Spec (.of k)).Etaleᵒᵖ, HasLimitsOfShape (StructuredArrow X (pointFunctor k).op) A] :
    Sheaf (smallEtaleTopology (Spec (.of k))) A ≌ A :=
  (Functor.sheafInducedTopologyEquivOfIsCoverDense (pointFunctor k)
      (smallEtaleTopology (Spec (.of k))) A).symm.trans
    ((sheafToPresheaf _ A).asEquivalence.trans
      ((Discrete.opposite PUnit.{1}).congrLeft.trans Functor.equiv))

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- **Sheaves of `Λ̲`-modules on `(Spec k)_étale` are `Λ`-modules**, for `k` separably closed:
sheaves of `Λ̲`-modules on the small model are sheaves of `Λ`-modules
(`Stacks.ConstantSheaf.constantSheafModuleEquivalence`), sheaves on the small model are sheaves
on `(Spec k)_étale` (`sheafEquiv`), and those are `Λ`-modules (`sheafEquivOfSepClosed`). -/
def modulesEquivOfSepClosed :
    SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
      (ringedTopos Λ (Spec (.of k))).O) ≌ ModuleCat.{u + 1} Λ :=
  letI : ∀ X : (Spec (.of k)).Etaleᵒᵖ,
      HasLimitsOfShape (StructuredArrow X (pointFunctor k).op) (ModuleCat.{u + 1} Λ) :=
    fun _ => ModuleCat.hasLimitsOfShape
  (Stacks.ConstantSheaf.constantSheafModuleEquivalence (topology (Spec (.of k)))
      (R := Λ)).symm.trans
    ((sheafEquiv (Spec (.of k)) (ModuleCat.{u + 1} Λ)).symm.trans
      (sheafEquivOfSepClosed k (ModuleCat.{u + 1} Λ)))

-- `DerivedModules`, the derived category of the étale site, is read at the standard model, as in
-- `StacksFrontier.AlgebraicGeometry.EtaleCohomology.Kunneth.EtaleKunnethMap`.
attribute [local instance] HasDerivedCategory.standard

/-- **`D((Spec k)_étale, Λ) ≃ D(Λ)`** for `k` separably closed: the equivalence of derived
categories induced by the exact equivalence `modulesEquivOfSepClosed`. -/
def derivedModulesEquivOfSepClosed [HasDerivedCategory (ModuleCat.{u + 1} Λ)] :
    DerivedModules Λ (Spec (.of k)) ≌ DerivedCategory (ModuleCat.{u + 1} Λ) :=
  letI : (modulesEquivOfSepClosed k Λ).functor.Additive :=
    Functor.additive_of_preserves_binary_products _
  Dualizing.mapDerivedCategoryEquivalenceOfEquivalence (modulesEquivOfSepClosed k Λ)

end Stacks.EtaleCohomology.EtaleCoefficients

end
