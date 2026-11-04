module

public import StacksFrontier.Algebra.Module.FlatCoefficientDescent
public import StacksFrontier.AlgebraicGeometry.FlatModuleCohomologyBaseChange.Cohomology

/-!
# The degreewise comparison over a quasi-compact open

In the situation of
`StacksFrontier/AlgebraicGeometry/FlatModuleCohomologyBaseChange/Degreewise.lean` — a cartesian
square

```
X' --g'--> X
|          |
f'         f
v          v
S' --g---> S
```

with `S` and `S'` affine, `F` a quasi-coherent `𝒪_X`-module and `G` a quasi-coherent
`𝒪_{S'}`-module flat over `S` — the comparison

`Γ(G, ⊤) ⊗_{Γ(S, ⊤)} Γ(F, U) ⟶ Γ((f')^* G ⊗ (g')^* F, (g')⁻¹U)`

is injective for every quasi-compact open `U` of `X`, and bijective for every quasi-compact and
quasi-separated one. In particular it is bijective over the whole of `X` when `f` is
quasi-compact and quasi-separated, which is [Stacks, Tag 0GN5] in degree zero at the level of
modules, for the canonical map.

`Stacks.AlgebraicGeometry.ModuleBaseChange.bijective_comparisonMap_of_isAffineOpen` has the
affine case, where no flatness is needed. Flatness is what makes the passage to a cover
possible: it is used to tensor the two sheaf axioms with `Γ(G, ⊤)`.

## Main definitions

* `Stacks.AlgebraicGeometry.ModuleBaseChange.comparisonDescent`: the comparison of
  `Degreewise.lean`, read as a datum for the local-to-global induction of
  `Stacks.FlatCoefficientDescent`.

## Main results

* `Stacks.AlgebraicGeometry.ModuleBaseChange.injective_comparisonMap_of_isCompact`: **the
  comparison is injective over a quasi-compact open.**
* `Stacks.AlgebraicGeometry.ModuleBaseChange.bijective_comparisonMap_of_isCompact`: **the
  comparison is bijective over a quasi-compact quasi-separated open.**
* `Stacks.AlgebraicGeometry.ModuleBaseChange.bijective_comparisonMap_top`: **the comparison is
  bijective over the whole of `X`**, for `f` quasi-compact and quasi-separated.

## Implementation notes

The induction is `Stacks.FlatCoefficientDescent.Comparison.bijective_of_iSup`, the
coefficient-module analogue of the engine that
`StacksFrontier/AlgebraicGeometry/PullbackSections/Qcqs.lean` runs for degree-zero flat base change
of the sections of a quasi-coherent module; the assembly below is the one of that file, with the
flat algebra `Γ(S', ⊤)` replaced by the flat module `Γ(G, ⊤)` and the comparison supplied
directly rather than as the base change of a linear map.

The two sheaf axioms are those of `F` on `X` and of `(f')^* G ⊗ (g')^* F` on `X'`; the target is
indexed by the opens of `X` through `U ↦ (g')⁻¹U`, which is legitimate because taking preimages
preserves suprema and infima. Only separation is used for the target, and gluing only for `F`
and only over a pair of opens.

Quasi-separatedness enters exactly once, to make the pairwise intersections of the members of an
affine cover quasi-compact, where injectivity is already known.

## References

* [Stacks Project, Tag 0GN5](https://stacks.math.columbia.edu/tag/0GN5)
* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
* [Stacks Project, Tag 01U4](https://stacks.math.columbia.edu/tag/01U4)
-/

@[expose] public noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
open TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.SectionsBaseChange
open scoped TensorProduct

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso Stacks.SheafInternalHom.isLocalization_sheafify
  Stacks.SheafInternalHom.monoidalCategory Stacks.SheafInternalHom.sheafifyMonoidal
  Stacks.SheafInternalHom.braidedCategory Stacks.SheafInternalHom.schemeMonoidalCategory

namespace Stacks.AlgebraicGeometry.ModuleBaseChange

variable {S S' X X' : Scheme.{u}} {g : S' ⟶ S} {f : X ⟶ S} {g' : X' ⟶ X} {f' : X' ⟶ S'}

/-- **The comparison as a datum for the local-to-global induction.** The source is the sections
of `F` over the opens of `X`, the target the sections of `(f')^* G ⊗ (g')^* F` over their
preimages, and the comparison map is the one of `Degreewise.lean`. -/
def comparisonDescent (H : IsPullback g' f' f g) (F : X.Modules) (G : S'.Modules) :
    letI := baseModule g G ⊤
    letI := baseAlgebra g
    letI := coeffTower g G
    letI : ∀ U : X.Opens, Module Γ(S, ⊤) Γ(F, U) := fun U => baseModule f F U
    Stacks.FlatCoefficientDescent.Comparison Γ(S, ⊤) Γ(G, ⊤) X.Opens (fun U => Γ(F, U))
      (fun U => Γ(tensorPullback g' f' F G, g' ⁻¹ᵁ U)) :=
  let := baseModule g G ⊤
  let := baseAlgebra g
  let := coeffTower g G
  let : ∀ U : X.Opens, Module Γ(S, ⊤) Γ(F, U) := fun U => baseModule f F U
  let : ∀ U : X.Opens,
      Module Γ(S', ⊤) Γ(tensorPullback g' f' F G, g' ⁻¹ᵁ U) := fun U =>
    baseModule f' (tensorPullback g' f' F G) (g' ⁻¹ᵁ U)
  { resM := fun {_ _} h => baseResHom f F h
    resN := fun {_ _} h =>
      { toFun := ((tensorPullback g' f' F G).presheaf.map
          (homOfLE (Scheme.Hom.preimage_mono g' h)).op).hom
        map_zero' := map_zero _
        map_add' := map_add _ }
    cmp := fun U => (comparisonMap g' f' F G H U).toAddMonoidHom
    resM_resM := by
      intro U V W h₁ h₂ x
      change (F.presheaf.map (homOfLE h₂).op).hom ((F.presheaf.map (homOfLE h₁).op).hom x) =
        (F.presheaf.map (homOfLE (h₂.trans h₁)).op).hom x
      rw [← ConcreteCategory.comp_apply, ← F.presheaf.map_comp]
      rfl
    resN_resN := by
      intro U V W h₁ h₂ y
      change ((tensorPullback g' f' F G).presheaf.map
          (homOfLE (Scheme.Hom.preimage_mono g' h₂)).op).hom
        (((tensorPullback g' f' F G).presheaf.map
          (homOfLE (Scheme.Hom.preimage_mono g' h₁)).op).hom y) = _
      rw [← ConcreteCategory.comp_apply, ← (tensorPullback g' f' F G).presheaf.map_comp]
      rfl
    cmp_res := fun {_ _} h x => comparisonMap_comm_res g' f' F G H h x
    sepM := by
      intro U cov hcov hU x hx
      refine TopCat.Sheaf.eq_of_locally_eq' (⟨F.presheaf, F.isSheaf⟩ : TopCat.Sheaf Ab.{u} _)
        (fun V : {V : X.Opens // V ∈ cov} => (V : X.Opens)) U
        (fun V => homOfLE (hcov V.1 V.2)) (by rw [← sSup_eq_iSup']; exact hU) x 0 (fun V => ?_)
      rw [map_zero]
      exact hx V.1 V.2
    sepN := by
      intro U cov hcov hU y hy
      refine TopCat.Sheaf.eq_of_locally_eq'
        (⟨(tensorPullback g' f' F G).presheaf, (tensorPullback g' f' F G).isSheaf⟩ :
          TopCat.Sheaf Ab.{u} _)
        (fun V : {V : X.Opens // V ∈ cov} => g' ⁻¹ᵁ (V : X.Opens)) (g' ⁻¹ᵁ U)
        (fun V => homOfLE (Scheme.Hom.preimage_mono g' (hcov V.1 V.2))) ?_ y 0 (fun V => ?_)
      · rw [← Scheme.Hom.preimage_iSup]
        exact Scheme.Hom.preimage_mono g' (by rw [← sSup_eq_iSup']; exact hU)
      · rw [map_zero]
        exact hy V.1 V.2
    glueM := by
      intro U₁ U₂ x₁ x₂ hx
      exact sheaf_glue_pair (⟨F.presheaf, F.isSheaf⟩ : TopCat.Sheaf Ab.{u} _) U₁ U₂ x₁ x₂ hx }

/-- The comparison map of `Degreewise.lean` is the comparison of `comparisonDescent`. -/
theorem comparisonDescent_cmp (H : IsPullback g' f' f g) (F : X.Modules) (G : S'.Modules)
    (U : X.Opens) :
    letI := baseModule g G ⊤
    letI := baseAlgebra g
    letI := coeffTower g G
    letI : ∀ V : X.Opens, Module Γ(S, ⊤) Γ(F, V) := fun V => baseModule f F V
    letI := baseModule f' (tensorPullback g' f' F G) (g' ⁻¹ᵁ U)
    ⇑((comparisonDescent H F G).cmp U) = ⇑(comparisonMap g' f' F G H U) :=
  rfl

/-- A quasi-compact open is the union of finitely many affine opens contained in it. -/
private theorem exists_finite_affineOpens_cover {U : X.Opens} (hU : IsCompact (X := X) U) :
    ∃ (I : Set X.affineOpens) (_ : Finite I), (∀ i : I, (i.1 : X.Opens) ≤ U) ∧
      U ≤ ⨆ i : I, (i.1 : X.Opens) := by
  obtain ⟨I, hI, e⟩ := isCompact_iff_finite_and_eq_biUnion_affineOpens.mp hU
  exact ⟨I, hI.to_subtype, fun i => by rw [e]; exact le_iSup_of_le i.1 (le_iSup_of_le i.2 le_rfl),
    le_of_eq (by rw [e, iSup_subtype'])⟩

/-- **The comparison is injective over a quasi-compact open.** A quasi-compact open is covered by
finitely many affine opens, over which the comparison is bijective, and tensoring the separation
axiom of `F` with the flat module `Γ(G, ⊤)` keeps it exact. -/
theorem injective_comparisonMap_of_isCompact [IsAffine S] [IsAffine S']
    (H : IsPullback g' f' f g) (F : X.Modules) [F.IsQuasicoherent] (G : S'.Modules)
    [G.IsQuasicoherent] (hflat : letI := baseModule g G ⊤; Module.Flat Γ(S, ⊤) Γ(G, ⊤))
    {U : X.Opens} (hU : IsCompact (X := X) U) :
    letI := baseModule g G ⊤
    letI := baseModule f F U
    letI := baseAlgebra g
    letI := coeffTower g G
    letI := baseModule f' (tensorPullback g' f' F G) (g' ⁻¹ᵁ U)
    Function.Injective (comparisonMap g' f' F G H U) := by
  let := baseModule g G ⊤
  let := baseAlgebra g
  let := coeffTower g G
  let : ∀ V : X.Opens, Module Γ(S, ⊤) Γ(F, V) := fun V => baseModule f F V
  let : ∀ V : X.Opens,
      Module Γ(S', ⊤) Γ(tensorPullback g' f' F G, g' ⁻¹ᵁ V) := fun V =>
    baseModule f' (tensorPullback g' f' F G) (g' ⁻¹ᵁ V)
  let := hflat
  obtain ⟨I, hIfin, hle, hcov⟩ := exists_finite_affineOpens_cover hU
  exact (comparisonDescent H F G).injective_of_iSup U (fun i : I => (i.1 : X.Opens)) hle hcov
    (fun i => (bijective_comparisonMap_of_isAffineOpen H F G i.1.2).injective)

/-- **The comparison is bijective over a quasi-compact quasi-separated open.** The two pieces of
a Mayer–Vietoris step are handled by the induction on a finite affine cover; the comparison is
injective over the pairwise intersections of the cover because those are quasi-compact. -/
theorem bijective_comparisonMap_of_isCompact [IsAffine S] [IsAffine S']
    (H : IsPullback g' f' f g) (F : X.Modules) [F.IsQuasicoherent] (G : S'.Modules)
    [G.IsQuasicoherent] (hflat : letI := baseModule g G ⊤; Module.Flat Γ(S, ⊤) Γ(G, ⊤))
    {U : X.Opens} (hU : IsCompact (X := X) U) (hUqs : IsQuasiSeparated (U : Set X)) :
    letI := baseModule g G ⊤
    letI := baseModule f F U
    letI := baseAlgebra g
    letI := coeffTower g G
    letI := baseModule f' (tensorPullback g' f' F G) (g' ⁻¹ᵁ U)
    Function.Bijective (comparisonMap g' f' F G H U) := by
  let := baseModule g G ⊤
  let := baseAlgebra g
  let := coeffTower g G
  let : ∀ V : X.Opens, Module Γ(S, ⊤) Γ(F, V) := fun V => baseModule f F V
  let : ∀ V : X.Opens,
      Module Γ(S', ⊤) Γ(tensorPullback g' f' F G, g' ⁻¹ᵁ V) := fun V =>
    baseModule f' (tensorPullback g' f' F G) (g' ⁻¹ᵁ V)
  let := hflat
  obtain ⟨I, hIfin, hle, hcov⟩ := exists_finite_affineOpens_cover hU
  refine (comparisonDescent H F G).bijective_of_iSup U (fun i : I => (i.1 : X.Opens)) hle hcov
    (fun i => bijective_comparisonMap_of_isAffineOpen H F G i.1.2) (fun i j => ?_)
  refine injective_comparisonMap_of_isCompact H F G hflat ?_
  have h := hUqs (i.1 : X.Opens) (j.1 : X.Opens) (hle i) (i.1 : X.Opens).isOpen
    i.1.2.isCompact (hle j) (j.1 : X.Opens).isOpen j.1.2.isCompact
  simpa using h

/-- **The comparison is bijective over the whole of `X`.** For a cartesian square with `S` and
`S'` affine, `f` quasi-compact and quasi-separated, `F` a quasi-coherent `𝒪_X`-module and `G` a
quasi-coherent `𝒪_{S'}`-module flat over `S`, the canonical map

`Γ(G, ⊤) ⊗_{Γ(S, ⊤)} Γ(X, F) ⟶ Γ(X', (f')^* G ⊗ (g')^* F)`

is bijective. This is [Stacks, Tag 0GN5] in degree zero at the level of modules, for the
canonical map rather than for an unconstrained isomorphism. -/
theorem bijective_comparisonMap_top [IsAffine S] [IsAffine S'] (H : IsPullback g' f' f g)
    [QuasiCompact f] [QuasiSeparated f] (F : X.Modules) [F.IsQuasicoherent] (G : S'.Modules)
    [G.IsQuasicoherent] (hG : IsFlatOver g.toLRSHom.toShHom G) :
    letI := baseModule g G ⊤
    letI := baseModule f F ⊤
    letI := baseAlgebra g
    letI := coeffTower g G
    letI := baseModule f' (tensorPullback g' f' F G) (g' ⁻¹ᵁ ⊤)
    Function.Bijective (comparisonMap g' f' F G H ⊤) := by
  have : CompactSpace ↥X := QuasiCompact.compactSpace_of_compactSpace f
  have : QuasiSeparatedSpace ↥X := quasiSeparatedSpace_of_quasiSeparated f
  refine bijective_comparisonMap_of_isCompact H F G (flat_sections_of_isFlatOver g G hG)
    (by simpa using isCompact_univ (X := X)) ?_
  simpa using isQuasiSeparated_univ (α := X)

end Stacks.AlgebraicGeometry.ModuleBaseChange

end
