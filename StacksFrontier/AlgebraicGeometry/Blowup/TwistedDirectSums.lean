module

public import StacksFrontier.AlgebraicGeometry.Blowup.TwistDegreeOne
public import StacksFrontier.AlgebraicGeometry.DerivedAcyclic.GlobalSections
public import StacksFrontier.AlgebraicGeometry.DerivedGlobalSections
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.EilenbergWattsHypotheses
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.QuasiCompactCoproductSections
public import StacksCore.Tactic.StacksAttribute

/-!
# Direct sums of a sheaf with no higher cohomology

Let `X` be a quasi-compact quasi-separated scheme and let `ℱ` be an `𝒪_X`-module whose
cohomology vanishes in positive degrees. Cohomology of such an `X` commutes with arbitrary
direct sums, so the same vanishing holds for `⨁_{j ∈ J} ℱ`, and therefore every such direct sum
is right acyclic for `Γ(X, -)`, with global sections `⨁_{j ∈ J} Γ(X, ℱ)`.

On the blowup `X = Proj(⨁_{n ≥ 0} Iⁿ)` of an affine scheme `Spec A` in an ideal `I` this applies
to the twists `𝒪_X(q)`: for `q` above the threshold of [Stacks, Tag 0AG7] the twist has no
higher cohomology, so every direct sum of copies of `𝒪_X(q)` is right acyclic for `Γ(X, -)`, and
the identification of [Stacks, Tag 0AG6] turns the resulting module of sections into a direct
sum of copies of `Iⁿ`.

## Main results

* `AlgebraicGeometry.isZero_rightDerived_sectionsFunctor_coproduct`: positive-degree cohomology
  of a direct sum of modules without higher cohomology vanishes.
* `AlgebraicGeometry.rightAcyclic_sectionsFunctor_coproduct` and
  `AlgebraicGeometry.rightAcyclic_sectionsFunctor_of_iso_coproduct`: such a direct sum, and
  anything isomorphic to one, is right acyclic for `Γ(X, -)`.
* `AlgebraicGeometry.isIso_to_derivedGlobalSections_of_termwise_coproduct`: a complex with such
  terms computes derived global sections.
* `AlgebraicGeometry.coproductSectionsIso` and
  `AlgebraicGeometry.coproductGlobalSectionsOverIso`: its global sections are the direct sum of
  the global sections of the summands, over the ring of global functions and over a base ring
  respectively.
* `Stacks.Blowup.rightAcyclic_sectionsFunctor_coproduct_blowUpTwist` and
  `Stacks.Blowup.coproductSectionsIsoIdealPow`: the two statements for a direct sum of copies of
  `𝒪_X(q)` on an affine blowup, the first granted the vanishing of [Stacks, Tag 0AG7] and the
  second granted in addition the identification of sections of [Stacks, Tag 0AG6].

## Implementation notes

The vanishing hypothesis is stated for the `ℤ`-indexed `CategoryTheory.Functor.rightDerivedPlus`,
which is the indexing `CategoryTheory.Functor.rightAcyclic` is defined against, while the
preservation of direct sums is available for the `ℕ`-indexed
`CategoryTheory.Functor.rightDerived`; `Stacks.DerivedIndexing.rightDerivedIso` carries the
statement between the two.

The two topological hypotheses of the direct-sum theorem are already discharged for a scheme, so
quasi-compactness and quasi-separatedness of the space are the only hypotheses here. For the
affine blowup both are available: quasi-compactness because the blowup of a Noetherian affine
scheme is proper over its base, and quasi-separatedness because it is separated over an affine
base.

## References

* [Stacks Project, Tag 01AI](https://stacks.math.columbia.edu/tag/01AI)
* [Stacks Project, Tag 01FF](https://stacks.math.columbia.edu/tag/01FF)
* [Stacks Project, Tag 0AG6](https://stacks.math.columbia.edu/tag/0AG6)
* [Stacks Project, Tag 0AG7](https://stacks.math.columbia.edu/tag/0AG7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry Stacks.AlgebraicGeometry.TopDegreeBaseChange

universe u

namespace AlgebraicGeometry

attribute [local instance 10000] HasDerivedCategory.standard

variable (X : Scheme.{u}) [CompactSpace (X : Type u)]

section QuasiSeparated

variable [QuasiSeparatedSpace (X : Type u)]

/-- **Cohomology of a direct sum of modules without higher cohomology vanishes.** On a
quasi-compact quasi-separated scheme cohomology commutes with arbitrary direct sums, so a direct
sum of modules whose degree-`q` cohomology vanishes again has vanishing degree-`q`
cohomology. -/
theorem isZero_rightDerived_sectionsFunctor_coproduct {J : Type u} (F : J → X.Modules) (q : ℕ)
    (hF : ∀ j, IsZero (((Stacks.Cohomology.sectionsFunctor X ⊤).rightDerived q).obj (F j))) :
    IsZero (((Stacks.Cohomology.sectionsFunctor X ⊤).rightDerived q).obj (∐ F)) := by
  have hpres : PreservesColimitsOfShape (Discrete J)
      ((Stacks.Cohomology.sectionsFunctor X ⊤).rightDerived q) :=
    preservesColimitsOfShape_discrete_rightDerived_moduleGlobalSections X q J
  have hcolim : IsColimit (((Stacks.Cohomology.sectionsFunctor X ⊤).rightDerived q).mapCocone
      (colimit.cocone (Discrete.functor F))) :=
    isColimitOfPreserves _ (colimit.isColimit _)
  rw [IsZero.iff_id_eq_zero]
  exact hcolim.hom_ext fun j => (hF j.as).eq_of_src _ _

/-- **Cohomology of a direct sum of modules without higher cohomology vanishes**, in the
`ℤ`-indexing of `CategoryTheory.Functor.rightDerivedPlus`. -/
theorem isZero_rightDerivedPlus_sectionsFunctor_coproduct {J : Type u} (F : J → X.Modules)
    (i : ℤ) (hi : 0 < i)
    (hF : ∀ j, IsZero (((Stacks.Cohomology.sectionsFunctor X ⊤).rightDerivedPlus i).obj (F j))) :
    IsZero (((Stacks.Cohomology.sectionsFunctor X ⊤).rightDerivedPlus i).obj (∐ F)) := by
  obtain ⟨q, rfl⟩ : ∃ q : ℕ, (q : ℤ) = i := ⟨i.toNat, by omega⟩
  let e := Stacks.DerivedIndexing.rightDerivedIso (Stacks.Cohomology.sectionsFunctor X ⊤) q
  exact (isZero_rightDerived_sectionsFunctor_coproduct X F q fun j =>
    (hF j).of_iso (e.app (F j))).of_iso (e.app (∐ F)).symm

/-- **A direct sum of modules with no higher cohomology is right acyclic for `Γ(X, -)`.**
Sections are left exact, so right acyclicity is the vanishing of all higher cohomology, and that
vanishing passes to direct sums on a quasi-compact quasi-separated scheme. -/
theorem rightAcyclic_sectionsFunctor_coproduct {J : Type u} (F : J → X.Modules)
    (hF : ∀ i : ℤ, 0 < i → ∀ j,
      IsZero (((Stacks.Cohomology.sectionsFunctor X ⊤).rightDerivedPlus i).obj (F j))) :
    (Stacks.Cohomology.sectionsFunctor X ⊤).rightAcyclic (∐ F) :=
  (((Stacks.Cohomology.sectionsFunctor X ⊤).rightAcyclic_iff_isIso_and_isZero_rightDerivedPlus
      (∐ F)).2 inferInstance).mpr fun i hi =>
    isZero_rightDerivedPlus_sectionsFunctor_coproduct X F i hi (hF i hi)

/-- **A module isomorphic to a direct sum of modules with no higher cohomology is right acyclic
for `Γ(X, -)`.** Right acyclicity is invariant under isomorphism, which is the form the
termwise-acyclicity hypothesis of [Stacks, Tag 0G9P] is checked in. -/
theorem rightAcyclic_sectionsFunctor_of_iso_coproduct {J : Type u} (F : J → X.Modules)
    (G : X.Modules) (e : G ≅ ∐ F)
    (hF : ∀ i : ℤ, 0 < i → ∀ j,
      IsZero (((Stacks.Cohomology.sectionsFunctor X ⊤).rightDerivedPlus i).obj (F j))) :
    (Stacks.Cohomology.sectionsFunctor X ⊤).rightAcyclic G :=
  (Stacks.Cohomology.sectionsFunctor X ⊤).rightAcyclic.prop_of_iso e.symm
    (rightAcyclic_sectionsFunctor_coproduct X F hF)

/-- **A complex whose terms are direct sums of modules without higher cohomology computes
derived global sections.** Each term is right acyclic for `Γ(X, -)`, so [Stacks, Tag 0G9P]
applies: the canonical comparison from termwise global sections to any right derived
global-sections functor is an isomorphism at the complex. -/
theorem isIso_to_derivedGlobalSections_of_termwise_coproduct
    (K : CochainComplex X.Modules ℤ) (hqc : ∀ n, (K.X n).IsQuasicoherent)
    {J : ℤ → Type u} (F : (n : ℤ) → J n → X.Modules) (e : ∀ n, K.X n ≅ ∐ F n)
    (hF : ∀ n : ℤ, ∀ i : ℤ, 0 < i → ∀ j,
      IsZero (((Stacks.Cohomology.sectionsFunctor X ⊤).rightDerivedPlus i).obj (F n j)))
    (RΓ : DerivedCategory X.Modules ⥤ DerivedCategory (ModuleCat.{u} Γ(X, ⊤)))
    (α : (Stacks.Cohomology.sectionsFunctor X ⊤).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RΓ)
    [RΓ.IsRightDerivedFunctor α
      (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ))] :
    IsIso (α.app ((HomotopyCategory.quotient _ _).obj K)) :=
  isIso_to_derivedGlobalSections_of_termwise_acyclic X K hqc
    (fun n => rightAcyclic_sectionsFunctor_of_iso_coproduct X (F n) (K.X n) (e n) (hF n)) RΓ α

end QuasiSeparated

/-- Global sections over a quasi-compact space commute with direct sums of sheaves of modules.
This is [Stacks, Tag 01AI] at the whole space. -/
theorem preservesColimitsOfShape_discrete_sectionsFunctor_top (J : Type u) :
    PreservesColimitsOfShape (Discrete J) (Stacks.Cohomology.sectionsFunctor X ⊤) :=
  Stacks.SheafOfModules.preservesCoproducts_evaluation_of_isCompact (I := J) X.ringCatSheaf ⊤
    (by simpa using CompactSpace.isCompact_univ)

/-- **Global sections of a direct sum of `𝒪_X`-modules on a quasi-compact scheme are the direct
sum of their global sections.** -/
def coproductSectionsIso {J : Type u} (F : J → X.Modules) :
    (Stacks.Cohomology.sectionsFunctor X ⊤).obj (∐ F) ≅
      ∐ fun j => (Stacks.Cohomology.sectionsFunctor X ⊤).obj (F j) :=
  have : PreservesColimitsOfShape (Discrete J) (Stacks.Cohomology.sectionsFunctor X ⊤) :=
    preservesColimitsOfShape_discrete_sectionsFunctor_top X J
  preservesColimitIso (Stacks.Cohomology.sectionsFunctor X ⊤) (Discrete.functor F) ≪≫
    HasColimit.isoOfNatIso (Discrete.compNatIsoDiscrete F (Stacks.Cohomology.sectionsFunctor X ⊤))

/-- **Global sections over a base ring commute with direct sums of sheaves of modules on a
quasi-compact scheme.** Restriction of scalars along `A ⟶ Γ(X, 𝒪_X)` is a left adjoint, so it
preserves the direct sum. -/
theorem preservesColimitsOfShape_discrete_globalSectionsOver {A : Type u} [CommRing A]
    (f : X ⟶ Spec (.of A)) (J : Type u) :
    PreservesColimitsOfShape (Discrete J) (globalSectionsOver f) := by
  have h₁ : PreservesColimitsOfShape (Discrete J)
      (Stacks.Cohomology.sectionsFunctor X ⊤) :=
    preservesColimitsOfShape_discrete_sectionsFunctor_top X J
  have h₂ : PreservesColimitsOfShape (Discrete J)
      (ModuleCat.restrictScalars.{u} (((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom)) :=
    ⟨fun {_} => inferInstance⟩
  exact ⟨fun {K} =>
    (inferInstance : PreservesColimit K (Stacks.Cohomology.sectionsFunctor X ⊤ ⋙
      ModuleCat.restrictScalars.{u} (((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom)))⟩

/-- **Global sections of a direct sum of `𝒪_X`-modules, as a module over a base ring**, are the
direct sum of the global sections of the summands. -/
def coproductGlobalSectionsOverIso {A : Type u} [CommRing A] (f : X ⟶ Spec (.of A))
    {J : Type u} (F : J → X.Modules) :
    (globalSectionsOver f).obj (∐ F) ≅ ∐ fun j => (globalSectionsOver f).obj (F j) :=
  have : PreservesColimitsOfShape (Discrete J) (globalSectionsOver f) :=
    preservesColimitsOfShape_discrete_globalSectionsOver X f J
  preservesColimitIso (globalSectionsOver f) (Discrete.functor F) ≪≫
    HasColimit.isoOfNatIso (Discrete.compNatIsoDiscrete F (globalSectionsOver f))

end AlgebraicGeometry

namespace Stacks.Blowup

attribute [local instance 10000] HasDerivedCategory.standard

variable {A : Type u} [CommRing A] (I : Ideal A)

/-- **The affine blowup is quasi-separated**: it is separated over an affine, hence
quasi-separated, base. -/
instance quasiSeparatedSpace_blowUpSpec : QuasiSeparatedSpace (blowUpSpec I) :=
  quasiSeparatedSpace_of_quasiSeparated (toSpec I)

/-- The twist `𝒪_X(q)` on the affine blowup `X = Proj(⨁_{n ≥ 0} Iⁿ)`, with its type declared at
`X.Modules`. -/
abbrev blowUpTwist (q : ℤ) : (blowUpSpec I).Modules :=
  AlgebraicGeometry.ProjectiveSpectrum.Proj.twistingSheaf (reesGrading I) q

variable [IsNoetherianRing A]

/-- **A direct sum of copies of a twist without higher cohomology is right acyclic for
`Γ(X, -)`** on the affine blowup of a Noetherian affine scheme. The hypothesis is the vanishing
of [Stacks, Tag 0AG7], which holds for every `q` above a threshold depending only on `A` and
`I`. -/
theorem rightAcyclic_sectionsFunctor_coproduct_blowUpTwist (q : ℤ) (J : Type u)
    (hvanish : ∀ i : ℤ, 0 < i →
      IsZero (((Stacks.Cohomology.sectionsFunctor (blowUpSpec I) ⊤).rightDerivedPlus i).obj
        (blowUpTwist I q))) :
    (Stacks.Cohomology.sectionsFunctor (blowUpSpec I) ⊤).rightAcyclic
      (∐ fun _ : J => blowUpTwist I q) :=
  rightAcyclic_sectionsFunctor_coproduct (blowUpSpec I) _ fun i hi _ => hvanish i hi

/-- **Global sections of a direct sum of copies of a large twist on an affine blowup form a
direct sum of copies of `Iⁿ`.** The hypothesis `hsections` is the identification of
[Stacks, Tag 0AG6] clause (3), `H⁰(X, 𝒪_X(n)) = Iⁿ`, which holds for every `n` above a threshold
depending only on `A` and `I`. -/
def coproductSectionsIsoIdealPow (n : ℕ) (J : Type u)
    (hsections : (globalSectionsOver (toSpec I)).obj (blowUpTwist I (n : ℤ)) ≅
      ModuleCat.of A (I ^ n : Ideal A)) :
    (globalSectionsOver (toSpec I)).obj (∐ fun _ : J => blowUpTwist I (n : ℤ)) ≅
      ∐ fun _ : J => ModuleCat.of A (I ^ n : Ideal A) :=
  coproductGlobalSectionsOverIso (blowUpSpec I) (toSpec I) _ ≪≫
    HasColimit.isoOfNatIso (Discrete.natIso fun _ => hsections)

end Stacks.Blowup

end
