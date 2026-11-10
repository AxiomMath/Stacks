module

public import Mathlib.CategoryTheory.Functor.OfSequence
public import StacksFrontier.Algebra.Homology.DerivedCategory.TruncGEComparison
public import StacksFrontier.AlgebraicGeometry.Cohomology.TruncationTowerBridge
public import StacksFrontier.AlgebraicGeometry.DerivedTildeEquivalence.Quasicoherent
public import StacksFrontier.Homology.DerivedCategory.KInjectiveProducts

/-!
# Unbounded affine vanishing, and the unit of the derived Spec–Γ adjunction

Let `R` be a commutative ring and `M^\bullet` a cochain complex of `R`-modules. This file supplies
the last input of unbounded affine vanishing and so proves it outright: the comparison
$$ Q(\Gamma(\operatorname{Spec} R, \widetilde{M}^\bullet)) \longrightarrow
   R\Gamma(\operatorname{Spec} R, Q(\widetilde{M}^\bullet)) $$
is invertible for *every* `M^\bullet`, which is the affine case of [Stacks, Tag 08D4]; and
therefore the unit of the derived sheafification–sections adjunction is invertible, which is the
**unit half of [Stacks, Tag 06Z0]** — derived sheafification `D(R) ⥤ D(𝒪_{Spec R})` is fully
faithful.

`StacksFrontier/AlgebraicGeometry/Cohomology/TruncationTowerBridge.lean` had already reduced that
comparison, through the `E = R\lim \tau_{\geq -n}E` argument of
`StacksFrontier/AlgebraicGeometry/AffineVanishingUnbounded/Tower.lean` and [Stacks, Tag 08D3] at the
locally small model, to one purely local input: a tower `𝓘 : ℕᵒᵖ ⥤ CochainComplex Mod(𝒪_{Spec R})`
of `Γ`-acyclic resolutions of the sheafified truncations, together with isomorphisms identifying
`Q(𝓘_n)` with `\tau_{\geq -n}Q(\widetilde{M}^\bullet)` under the canonical maps. Its *What is not
done* section named the obstruction to the cheapest candidate for `𝓘` — the sheafified
truncations themselves, whose terms are quasi-coherent hence `Γ`-acyclic over an affine base — as
the absence of the comparison `K.truncGE a ⟶ K.truncGE b` for `a ≤ b`, Mathlib having only the
functoriality of `\tau_{\geq n}` in the complex and not in the degree.

That comparison is `CochainComplex.truncGEMapOfLE`, of
`StacksFrontier/Algebra/Homology/DerivedCategory/TruncGEComparison.lean`, and the identification it
asked for is `DerivedCategory.isIso_descTruncGE_Q_map` of the same file. With both in hand the
tower is `AlgebraicGeometry.tildeTruncGETower` below, the resolutions `g_n` are identities, and
nothing conditional remains.

## Main definitions

* `AlgebraicGeometry.tildeTruncGETower` — the tower `n ↦ (\tau_{\geq -n}M)^\sim` of sheafified
  truncations, as a functor `ℕᵒᵖ ⥤ CochainComplex Mod(𝒪_{Spec R}) ℤ`.

## Main results

* `AlgebraicGeometry.isIso_globalSectionsComplexComparison_tilde` — **unbounded affine vanishing,
  the affine case of [Stacks, Tag 08D4]**, unconditionally.
* `AlgebraicGeometry.isIso_unit_app_derivedTildeGlobalSectionsAdjunction` — the unit of the derived
  sheafification–sections adjunction is invertible at every object of `D(R)`.
* `AlgebraicGeometry.derivedTildeFullyFaithful` — **the unit half of [Stacks, Tag 06Z0]**: derived
  sheafification is fully faithful.

## What is not done

No Stacks-tag attribute appears below. Tag 08D4 is the statement for an arbitrary scheme and what
is proved here is the affine case; Tag 06Z0 is the equivalence, whose remaining half is essential
surjectivity of derived sheafification — the counit — and is untouched here. The three formulations
of that half are recorded in the *What is not done* section of
`StacksFrontier/AlgebraicGeometry/DerivedTildeEquivalence/Quasicoherent.lean`; the first of the
three listed there, through the unit, is discharged by this file.

## Implementation notes

*The derived category in force is the locally small one*,
`AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`, as everywhere in this cluster. Nothing here
pins `CategoryTheory.HasDerivedCategory.standard`: the free `HasDerivedCategory` binder is what
makes the cited Tag 08D3 applicable, and it is what the compact-generation consumers downstream
require. See the implementation notes of
`StacksFrontier/AlgebraicGeometry/Cohomology/TruncationTowerAnyModel.lean`.

*Countable products.* The two `HasProduct` hypotheses of the cited reduction are discharged from
`Stacks.KInjectiveProducts.hasProductsOfShape_derivedCategory_sheafOfModules`, which gives
`HasProductsOfShape ℕ` for the derived category of modules on any ringed site from a chosen
derived category alone. It is introduced with its type written out, so that the
`HasDerivedCategory` instance it is applied at is forced by unification to be the locally small
one keyed on `X.Modules` rather than the one keyed on `SheafOfModules R`; those two are distinct
terms and instance search crosses neither.

*Why the instance arguments are supplied by name.* `(tildeTruncGETower R M).obj ⟨n⟩` is only
semireducibly the sheafified truncation — `CategoryTheory.Functor.ofOpSequence` is a plain `def` —
so instance search does not see the strict bound, the acyclicity of the terms or the
quasi-coherence through it. Each is therefore passed as `inferInstanceAs` at the unfolded
spelling, whose result has a definitionally equal type.

## References

* [Stacks Project, Tag 08D3](https://stacks.math.columbia.edu/tag/08D3)
* [Stacks Project, Tag 08D4](https://stacks.math.columbia.edu/tag/08D4)
* [Stacks Project, Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0)
* [Stacks Project, Tag 070F](https://stacks.math.columbia.edu/tag/070F)
* [Stacks Project, Tag 070M](https://stacks.math.columbia.edu/tag/070M)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated DerivedCategory

universe u

namespace AlgebraicGeometry

variable (R : CommRingCat.{u}) (M : CochainComplex (ModuleCat.{u} R) ℤ)

/-! ### The tower of sheafified truncations -/

/-- **The tower of sheafified truncations of a complex of `R`-modules.** The inverse system
`n ↦ (\tau_{\geq -n}M^\bullet)^\sim` indexed by `ℕᵒᵖ`, whose transition map is the sheafification
of `CochainComplex.truncGEMapOfLE`.

This is the tower that
`AlgebraicGeometry.isIso_globalSectionsComplexComparison_tilde_of_resolutionTower` asks for, with
the resolutions taken to be identities: the terms of `(\tau_{\geq -n}M)^\sim` are quasi-coherent,
hence already right acyclic for global sections over an affine base. -/
def tildeTruncGETower : ℕᵒᵖ ⥤ CochainComplex (Spec R).Modules ℤ :=
  Functor.ofOpSequence
    (X := fun n : ℕ ↦ ((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (M.truncGE (-(n : ℤ))))
    fun n ↦ ((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).map
      (M.truncGEMapOfLE (show -((n + 1 : ℕ) : ℤ) ≤ -(n : ℤ) by omega))

/-- The `n`-th term of the tower of sheafified truncations is `(\tau_{\geq -n}M^\bullet)^\sim`. -/
@[simp]
theorem tildeTruncGETower_obj (n : ℕ) :
    (tildeTruncGETower R M).obj ⟨n⟩ =
      ((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (M.truncGE (-(n : ℤ))) :=
  rfl

/-- The successor transition map of the tower of sheafified truncations is the sheafification of
the comparison of truncations. -/
@[simp]
theorem tildeTruncGETower_map_succ (n : ℕ) :
    (tildeTruncGETower R M).map (homOfLE (Nat.le_succ n)).op =
      ((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (M.truncGEMapOfLE (show -((n + 1 : ℕ) : ℤ) ≤ -(n : ℤ) by omega)) :=
  Functor.ofOpSequence_map_homOfLE_succ _ n

/-- **The canonical maps into the tower are compatible with its transitions.** Sheafified, the
canonical map `M^\bullet ⟶ (\tau_{\geq -(n+1)}M)^\sim` followed by the transition of the tower is
the canonical map `M^\bullet ⟶ (\tau_{\geq -n}M)^\sim`.

This is `CochainComplex.πTruncGE_comp_truncGEMapOfLE` under `{}^\sim`. It is assembled in term
mode: `rw` builds its motive at `implicit` transparency, where `(tildeTruncGETower R M).obj ⟨n⟩`
is not interchangeable with the sheafified truncation it unfolds to, so the rewrite of the
transition map fails on a goal that visibly contains it. -/
theorem tildeTruncGETower_πTruncGE_comp_map_succ (n : ℕ) :
    ((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (M.πTruncGE (-((n + 1 : ℕ) : ℤ))) ≫
        (tildeTruncGETower R M).map (homOfLE (Nat.le_succ n)).op =
      ((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (M.πTruncGE (-(n : ℤ))) :=
  (congrArg (fun z ↦ ((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).map
      (M.πTruncGE (-((n + 1 : ℕ) : ℤ))) ≫ z) (tildeTruncGETower_map_succ R M n)).trans
    ((CategoryTheory.Functor.map_comp _ _ _).symm.trans
      (congrArg ((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (CochainComplex.πTruncGE_comp_truncGEMapOfLE M _)))

/-! ### Unbounded affine vanishing -/

/-- **Unbounded affine vanishing, the affine case of [Stacks, Tag 08D4].** For every cochain
complex `M^\bullet` of `R`-modules the comparison
`Q(\Gamma(\operatorname{Spec} R, \widetilde{M}^\bullet)) ⟶ R\Gamma(Q(\widetilde{M}^\bullet))` is
an isomorphism.

`AlgebraicGeometry.isIso_globalSectionsComplexComparison_tilde_of_resolutionTower` reduces this to
a tower of `Γ`-acyclic resolutions of the sheafified truncations computing the truncations of
`Q(\widetilde{M}^\bullet)`. The tower of the sheafified truncations themselves serves: its terms
are quasi-coherent, hence `Γ`-acyclic over an affine base, so the resolutions are identities; and
`DerivedCategory.isIso_descTruncGE_Q_map` identifies `Q((\tau_{\geq -n}M)^\sim)` with
`\tau_{\geq -n}Q(\widetilde{M}^\bullet)` under `Q` of the sheafified canonical map, because
`{}^\sim` preserves homology and that map is a quasi-isomorphism in every degree `≥ -n`. The
compatibility with the transitions is `CochainComplex.πTruncGE_comp_truncGEMapOfLE` under
`{}^\sim`. -/
theorem isIso_globalSectionsComplexComparison_tilde :
    IsIso (globalSectionsComplexComparison (𝟙 (Spec R))
      (((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj M)) := by
  have hprod : HasProductsOfShape ℕ (DerivedCategory (Spec R).Modules) :=
    Stacks.KInjectiveProducts.hasProductsOfShape_derivedCategory_sheafOfModules
      (Spec R).ringCatSheaf
  have hGEtower : ∀ n : ℕ, DerivedCategory.TStructure.t.IsGE
      ((tildeTruncGETower R M ⋙ DerivedCategory.Q).obj ⟨n⟩) (-(n : ℤ)) := fun n ↦
    inferInstanceAs (DerivedCategory.TStructure.t.IsGE (DerivedCategory.Q.obj
      (((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (M.truncGE (-(n : ℤ))))) (-(n : ℤ)))
  have hdesc : ∀ n : ℕ, IsIso (DerivedCategory.TStructure.t.descTruncGE
      (DerivedCategory.Q.map (((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (M.πTruncGE (-(n : ℤ))))) (-(n : ℤ))) := by
    intro n
    refine DerivedCategory.isIso_descTruncGE_Q_map _ _ fun r hr ↦ ?_
    have : QuasiIsoAt (M.πTruncGE (-(n : ℤ))) r := M.quasiIsoAt_πTruncGE _ r hr
    infer_instance
  refine isIso_globalSectionsComplexComparison_tilde_of_resolutionTower R M
    (tildeTruncGETower R M)
    (fun n ↦ inferInstanceAs (CochainComplex.IsStrictlyGE
      (((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (M.truncGE (-(n : ℤ)))) (-(n : ℤ))))
    (fun n i ↦ rightAcyclic_globalSectionsOver_of_isQuasicoherent (𝟙 (Spec R))
      ((tilde.functor R).obj ((M.truncGE (-(n : ℤ))).X i)))
    (fun n ↦ 𝟙 _) (fun n ↦ inferInstanceAs (QuasiIso (𝟙
      (((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (M.truncGE (-(n : ℤ)))))))
    (fun n ↦ @asIso _ _ _ _ _ (hdesc n)) (fun n ↦ ?_) (fun n ↦ ?_)
  · exact (DerivedCategory.TStructure.t.π_descTruncGE _ _).trans
      (congrArg DerivedCategory.Q.map (Category.comp_id _).symm)
  · exact congrArg DerivedCategory.Q.map
      (((congrArg (fun z ↦ ((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).map
            (M.πTruncGE (-((n + 1 : ℕ) : ℤ))) ≫ z)
          (Category.id_comp ((tildeTruncGETower R M).map
            (homOfLE (Nat.le_succ n)).op))).trans
        (tildeTruncGETower_πTruncGE_comp_map_succ R M n)).trans (Category.comp_id _).symm)

/-! ### The unit half of Tag 06Z0 -/

/-- **The unit of the derived sheafification–sections adjunction is invertible.** For every object
`N` of `D(R)` the unit of `AlgebraicGeometry.derivedTildeGlobalSectionsAdjunction` is an
isomorphism at `N`.

This is `AlgebraicGeometry.isIso_derivedTildeGlobalSectionsAdjunction_unit_app` fed with
unbounded affine vanishing. -/
theorem isIso_unit_app_derivedTildeGlobalSectionsAdjunction
    (N : DerivedCategory (ModuleCat.{u} R)) :
    IsIso ((derivedTildeGlobalSectionsAdjunction R).val.unit.app N) :=
  isIso_derivedTildeGlobalSectionsAdjunction_unit_app R
    (fun K ↦ isIso_globalSectionsComplexComparison_tilde R K) N

/-- **The unit half of [Stacks, Tag 06Z0]: derived sheafification is fully faithful.** The functor
`AlgebraicGeometry.derivedTilde R : D(R) ⥤ D_QCoh(𝒪_{Spec R})` is fully faithful.

`AlgebraicGeometry.derivedTildeFullyFaithfulOfIsIsoUnit` with the unit invertibility just
established. The remaining half of the tag, essential surjectivity, is
`AlgebraicGeometry.essSurj_derivedTilde_of_isIso_counit` and is not proved. -/
def derivedTildeFullyFaithful : (derivedTilde R).FullyFaithful :=
  derivedTildeFullyFaithfulOfIsIsoUnit R
    (isIso_unit_app_derivedTildeGlobalSectionsAdjunction R)

end AlgebraicGeometry

end
