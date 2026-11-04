module

public import StacksFrontier.AlgebraicGeometry.Stacks.GerbeRelativeDiagonalDescent
public import StacksFrontier.AlgebraicGeometry.Stacks.ProperCancellation
public import StacksFrontier.AlgebraicGeometry.Stacks.ProperImageAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactMorphismPermanence
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationEquivalenceInvariance
public import StacksFrontier.AlgebraicGeometry.Stacks.SurjectiveBaseChange

/-!
# Properness is unchanged by precomposition with an equivalence

Let `k : 𝒵 ⟶ 𝒳` be a 1-morphism of algebraic stacks over `S` whose underlying functor is an
equivalence of categories. This file proves that separatedness, local finite type,
quasi-compactness, universal closedness, finite type and properness of `f : 𝒳 ⟶ 𝒴` pass to
`k ≫ f`.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.exists_quasiInverse_of_isEquivalence`: Stacks 003Z,
  part (2), in the 2-category of algebraic stacks.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isProper_comp_of_isEquivalence` and its components.

## Implementation notes

With a quasi-inverse `e`, `f ≅ e ≫ (k ≫ f)` with `e` surjective, so quasi-compactness is
Stacks 050X and universal closedness is Stacks 0CQK; local finite type moves along the
equivalence by `AlgebraicGeometry.Stack.hasPropertyOnSomeSmoothDiagram_of_isEquivalence`, as
local finite presentation does in
`AlgebraicGeometry.Stack.AlgebraicStacks.isLocallyOfFinitePresentation_comp_of_isEquivalence`.
-/

@[expose] public section

open CategoryTheory

universe u w

namespace AlgebraicGeometry.Stack.AlgebraicStacks

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒵 𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS}

/-- **Stacks 003Z, part (2), in the 2-category of algebraic stacks.** A 1-morphism whose
underlying functor is an equivalence has a quasi-inverse 1-morphism, whose underlying functor is
again an equivalence, with a 2-isomorphism `e ≫ k ≅ 𝟙`. -/
theorem exists_quasiInverse_of_isEquivalence (k : 𝒵 ⟶ 𝒳)
    (hk : Functor.IsEquivalence (CatFiberedInGroupoids.homFunctor k.hom)) :
    ∃ e : 𝒳 ⟶ 𝒵, Functor.IsEquivalence (CatFiberedInGroupoids.homFunctor e.hom) ∧
      Nonempty (e ≫ k ≅ 𝟙 𝒳) := by
  obtain ⟨F, hF, η, ε, -, hε⟩ :=
    Functor.IsFiberedInGroupoids.isEquivalence_over 𝒵.val.val.p 𝒳.val.val.p
      𝒵.val.isFiberedInGroupoids 𝒳.val.isFiberedInGroupoids
      (CatFiberedInGroupoids.homFunctor k.hom)
      (CatFiberedInGroupoids.homFunctor_comp_p k.hom) hk
  have he : Functor.IsEquivalence F :=
    (CategoryTheory.Equivalence.mk F (CatFiberedInGroupoids.homFunctor k.hom) ε.symm
      η).isEquivalence_functor
  refine ⟨Bicategory.InducedBicategory.mkHom (Bicategory.InducedBicategory.mkHom ⟨F, hF⟩),
    he, ⟨Bicategory.InducedBicategory.isoMk (Bicategory.InducedBicategory.isoMk
      (BasedNatIso.mkNatIso (F := BasedFunctor.comp ⟨F, hF⟩ k.hom.hom)
        (G := BasedFunctor.id 𝒳.val.val) ε hε))⟩⟩

variable (k : 𝒵 ⟶ 𝒳) (f : 𝒳 ⟶ 𝒴)
  (hk : Functor.IsEquivalence (CatFiberedInGroupoids.homFunctor k.hom))
include hk

/-- If `e ≫ k ≅ 𝟙`, then `e ≫ (k ≫ f) ≅ f`. -/
private def quasiInverse_comp_comp_iso {C : Type*} [Bicategory C] {a b d : C}
    (e : a ⟶ b) (k : b ⟶ a) (f : a ⟶ d) (h : e ≫ k ≅ 𝟙 a) : e ≫ (k ≫ f) ≅ f :=
  (Bicategory.associator e k f).symm ≪≫ Bicategory.whiskerRightIso h f ≪≫ Bicategory.leftUnitor f

/-- Separatedness is unchanged by precomposition with an equivalence. -/
theorem isSeparated_comp_of_isEquivalence (hf : IsSeparated B S hS f) :
    IsSeparated B S hS (k ≫ f) :=
  isSeparated_of_equivalence B S hS f (k ≫ f) k.hom.hom (Iso.refl _) hk hf

/-- Local finite type is unchanged by precomposition with an equivalence. -/
theorem isLocallyOfFiniteType_comp_of_isEquivalence (hf : IsLocallyOfFiniteType B S hS f) :
    IsLocallyOfFiniteType B S hS (k ≫ f) := by
  obtain ⟨e, he, ⟨hiso⟩⟩ := exists_quasiInverse_of_isEquivalence B S hS k hk
  refine (Stack.hasPropertyOnEverySmoothDiagram_iff_some.{u, w} B S hS
      (fun _ _ h => Space.IsLocallyOfFiniteType B S hS h)
      (Space.isSmoothLocalOnSourceAndTarget_locallyOfFiniteType B S hS)
      𝒵.property 𝒴.property (k ≫ f).hom).2
    (Stack.hasPropertyOnSomeSmoothDiagram_of_isEquivalence B S hS
      (fun _ _ h => Space.IsLocallyOfFiniteType B S hS h) (k ≫ f).hom f.hom
      e.hom he ?_
      ((Stack.hasPropertyOnEverySmoothDiagram_iff_some.{u, w} B S hS
        (fun _ _ h => Space.IsLocallyOfFiniteType B S hS h)
        (Space.isSmoothLocalOnSourceAndTarget_locallyOfFiniteType B S hS)
        𝒳.property 𝒴.property f.hom).1 hf))
  exact (quasiInverse_comp_comp_iso e.hom k.hom f.hom
    (Bicategory.InducedBicategory.isoHom hiso)).symm


/-- Quasi-compactness (Stacks 050U) is unchanged by precomposition with an equivalence: with a
quasi-inverse `e`, `f ≅ e ≫ (k ≫ f)` and `e` is surjective, so Stacks 050X applies. -/
theorem isQuasiCompactMorphism_comp_of_isEquivalence (hf : IsQuasiCompactMorphism B S hS f) :
    IsQuasiCompactMorphism B S hS (k ≫ f) := by
  obtain ⟨e, he, ⟨hiso⟩⟩ := exists_quasiInverse_of_isEquivalence B S hS k hk
  exact isQuasiCompactMorphism_of_comp_of_isSurjective B S hS e f (k ≫ f)
    (quasiInverse_comp_comp_iso e k f hiso)
    (surjective_pointsMap_of_isEquivalence B S hS e he) hf

/-- Universal closedness (Stacks 0513) is unchanged by precomposition with an equivalence: with a
quasi-inverse `e`, `e ≫ (k ≫ f) ≅ f` and `e` is surjective, so Stacks 0CQK applies. -/
theorem universallyClosed_comp_of_isEquivalence (hf : UniversallyClosed B S hS f) :
    UniversallyClosed B S hS (k ≫ f) := by
  obtain ⟨e, he, ⟨hiso⟩⟩ := exists_quasiInverse_of_isEquivalence B S hS k hk
  refine universallyClosed_of_surjective_comp B S hS e (k ≫ f) ?_
    (surjective_pointsMap_of_isEquivalence B S hS e he)
  exact universallyClosed_of_iso B S hS (quasiInverse_comp_comp_iso e k f hiso).symm hf

/-- Finite type (Stacks 06FS) is unchanged by precomposition with an equivalence. -/
theorem isFiniteType_comp_of_isEquivalence (hf : IsFiniteType B S hS f) :
    IsFiniteType B S hS (k ≫ f) :=
  ⟨isLocallyOfFiniteType_comp_of_isEquivalence B S hS k f hk hf.1,
    isQuasiCompactMorphism_comp_of_isEquivalence B S hS k f hk hf.2⟩

/-- Properness (Stacks 0CL5) is unchanged by precomposition with an equivalence. -/
theorem isProper_comp_of_isEquivalence (hf : IsProper B S hS f) :
    IsProper B S hS (k ≫ f) :=
  ⟨isSeparated_comp_of_isEquivalence B S hS k f hk hf.1,
    isFiniteType_comp_of_isEquivalence B S hS k f hk hf.2.1,
    universallyClosed_comp_of_isEquivalence B S hS k f hk hf.2.2⟩

end AlgebraicGeometry.Stack.AlgebraicStacks
