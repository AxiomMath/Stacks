module

public import StacksFrontier.AlgebraicGeometry.Cohomology.Coherent.ArtinRees
public import
  StacksFrontier.AlgebraicGeometry.LocalCohomology.CodimensionOneObstruction.SectionsFunctionField
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Non-coherence of the direct image from an open subscheme avoiding a codimension-one point

Let `X` be an integral locally Noetherian scheme, `S` a nonempty open subscheme, and `z` a point
outside `S` whose local ring has dimension at most one. This file proves that the direct image
`(S → X)_* 𝒪_S` is not a coherent `𝒪_X`-module.

This is the first paragraph of [Stacks, Tag 0AWC] in the case `𝓕 = 𝒪_{X' ∩ U}` with `X' = X`,
that is, the case in which the associated point of `𝓕` is the generic point of `X` itself. The
mathematical content is
`Stacks.AlgebraicGeometry.CodimensionOneObstruction.not_moduleFinite_sections`; what is added
here is the observation that coherence of the direct image would make its module of sections over
an affine open `V₀` containing `z` a finite module over `Γ(X, V₀)`.

## Main results

* `not_isCoherent_pushforward_structureSheaf_of_dim_le_one`, in the namespace
  `Stacks.AlgebraicGeometry.CodimensionOneObstruction`: the direct image of the structure sheaf
  of `S` along the open immersion into `X` is not coherent.

## Implementation notes

The sections of `(S → X)_* 𝒪_S` over `W` are by definition the sections of `𝒪_S` over
`S.ι ⁻¹ᵁ W`, which in turn are the sections of `𝒪_X` over `S.ι ''ᵁ (S.ι ⁻¹ᵁ W) = S ⊓ W`, with
`Γ(X, W)` acting through `S.ι.app W`. That this action is restriction is
`Stacks.AlgebraicGeometry.CodimensionOneObstruction.ι_app_comp_mapInfLE`; both maps are
`X.presheaf.map` of an arrow `W ⟶ S ⊓ W` in the poset of opens, and there is only one such
arrow.

## References

* [Stacks Project, Tag 0AWC](https://stacks.math.columbia.edu/tag/0AWC)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u

namespace Stacks.AlgebraicGeometry.CodimensionOneObstruction

/-- The image of the preimage of `W` under the inclusion of an open `U` is `U ⊓ W`. -/
theorem ι_image_preimage_eq_inf {X : Scheme.{u}} (U W : X.Opens) :
    U.ι ''ᵁ (U.ι ⁻¹ᵁ W) = U ⊓ W := by
  refine TopologicalSpace.Opens.ext ?_
  show U.ι.base.hom '' (U.ι.base.hom ⁻¹' (W : Set X)) = _
  rw [Set.image_preimage_eq_inter_range]
  simp [Scheme.Opens.range_ι, Set.inter_comm]

/-- Restriction maps of the structure sheaf along parallel arrows of opens agree. -/
private theorem presheaf_map_eq_of_parallel {X : Scheme.{u}} {U V : X.Opens}
    (f g : op U ⟶ op V) : X.presheaf.map f = X.presheaf.map g :=
  congrArg _ (Subsingleton.elim f g)

/-- Reading the sections of an open subscheme over the preimage of `W` as sections over `U ⊓ W`
turns the structure map of the open immersion into restriction. -/
theorem ι_app_comp_mapInfLE {X : Scheme.{u}} (U W : X.Opens) :
    U.ι.app W ≫ X.presheaf.map (homOfLE (le_of_eq (ι_image_preimage_eq_inf U W).symm)).op
      = X.presheaf.map (homOfLE (inf_le_right : U ⊓ W ≤ W)).op := by
  simp only [Scheme.Opens.ι_app]
  exact Eq.trans (X.presheaf.map_comp _ _).symm (presheaf_map_eq_of_parallel _ _)

/-- The `Γ(X, W)`-linear map from the sections over `W` of the direct image of the structure sheaf
of an open `U` to `Γ(X, U ⊓ W)`, on which `Γ(X, W)` acts through restriction. -/
noncomputable def pushforwardSectionsHom {X : Scheme.{u}} (U W : X.Opens) :
    letI := resAlgebra (inf_le_right : U ⊓ W ≤ W)
    Γ((Scheme.Modules.pushforward U.ι).obj (SheafOfModules.unit _), W) →ₗ[Γ(X, W)] Γ(X, U ⊓ W) :=
  letI := resAlgebra (inf_le_right : U ⊓ W ≤ W)
  { toFun := fun m =>
      X.presheaf.map (homOfLE (le_of_eq (ι_image_preimage_eq_inf U W).symm)).op m
    map_add' := fun m n => by
      change X.presheaf.map _ (m + n) = _
      exact map_add _ _ _
    map_smul' := fun a m => by
      have hmul : ∀ c d : Γ(X, U.ι ''ᵁ (U.ι ⁻¹ᵁ W)),
          X.presheaf.map (homOfLE (le_of_eq (ι_image_preimage_eq_inf U W).symm)).op (c * d)
            = X.presheaf.map (homOfLE (le_of_eq (ι_image_preimage_eq_inf U W).symm)).op c *
              X.presheaf.map (homOfLE (le_of_eq (ι_image_preimage_eq_inf U W).symm)).op d :=
        fun c d => map_mul _ c d
      have hone : ∀ c : Γ(X, W),
          X.presheaf.map (homOfLE (le_of_eq (ι_image_preimage_eq_inf U W).symm)).op
              ((U.ι.app W).hom c)
            = (X.presheaf.map (homOfLE (inf_le_right : U ⊓ W ≤ W)).op) c := fun c => by
        have h2 : (ConcreteCategory.hom (U.ι.app W ≫
            X.presheaf.map (homOfLE (le_of_eq (ι_image_preimage_eq_inf U W).symm)).op)) c
              = (X.presheaf.map (homOfLE (inf_le_right : U ⊓ W ≤ W)).op) c := by
          rw [ι_app_comp_mapInfLE]
        exact h2
      exact (hmul ((U.ι.app W).hom a) m).trans
        (congrArg (fun t => t *
          X.presheaf.map (homOfLE (le_of_eq (ι_image_preimage_eq_inf U W).symm)).op m) (hone a)) }

/-- The map `pushforwardSectionsHom U W` is surjective. -/
theorem pushforwardSectionsHom_surjective {X : Scheme.{u}} (U W : X.Opens) :
    Function.Surjective (pushforwardSectionsHom U W) := by
  have key : ∀ y : Γ(X, U ⊓ W),
      X.presheaf.map (homOfLE (le_of_eq (ι_image_preimage_eq_inf U W).symm)).op
        (X.presheaf.map (homOfLE (le_of_eq (ι_image_preimage_eq_inf U W))).op y) = y := by
    intro y
    rw [← ConcreteCategory.comp_apply, ← X.presheaf.map_comp, ← op_comp,
      presheaf_map_eq_of_parallel _ (𝟙 _), X.presheaf.map_id]
    rfl
  exact fun y => ⟨X.presheaf.map (homOfLE (le_of_eq (ι_image_preimage_eq_inf U W))).op y, key y⟩

/-- Let `X` be an integral locally Noetherian scheme, `z` a point of `X` whose local ring has
dimension at most one, and `S` a nonempty open subscheme not containing `z`. Then the direct image
`(S → X)_* 𝒪_S` of the structure sheaf of `S` is not a coherent `𝒪_X`-module. -/
@[ega "IV 5.10.10" "(ii), special case",
  ega "IV 5.11.1" "b) ⇒ c), for Z closed",
  ega "IV 7.8.3" "(ix), partial"]
theorem not_isCoherent_pushforward_structureSheaf_of_dim_le_one {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] {z : X} (hdim : ringKrullDim (X.presheaf.stalk z) ≤ 1)
    {S : X.Opens} [Nonempty S.toScheme] (hzS : z ∉ S) :
    ¬ ((Scheme.Modules.pushforward S.ι).obj (SheafOfModules.unit _)).IsCoherent := by
  intro hcoh
  obtain ⟨V₀, hV₀, hz, -⟩ :=
    AlgebraicGeometry.exists_isAffineOpen_mem_and_subset (U := (⊤ : X.Opens)) (x := z) trivial
  have hneV₀ : Nonempty V₀.toScheme := ⟨⟨z, hz⟩⟩
  have hgenS : genericPoint X ∈ S :=
    ((genericPoint_spec X).mem_open_set_iff S.isOpen).mpr (by simpa using ‹Nonempty S.toScheme›)
  have hgenV₀ : genericPoint X ∈ V₀ :=
    ((genericPoint_spec X).mem_open_set_iff V₀.isOpen).mpr (by simpa using hneV₀)
  have : Nonempty (S ⊓ V₀ : X.Opens).toScheme := ⟨⟨genericPoint X, ⟨hgenS, hgenV₀⟩⟩⟩
  let := resAlgebra (inf_le_right : S ⊓ V₀ ≤ V₀)
  have hfin : Module.Finite Γ(X, V₀)
      Γ((Scheme.Modules.pushforward S.ι).obj (SheafOfModules.unit _), V₀) :=
    AlgebraicGeometry.moduleFinite_sections _ ⟨V₀, hV₀⟩
  exact not_moduleFinite_sections hV₀ hz hdim (inf_le_right : S ⊓ V₀ ≤ V₀)
    (fun h => hzS h.1)
    (Module.Finite.of_surjective (pushforwardSectionsHom S V₀)
      (pushforwardSectionsHom_surjective S V₀))

end Stacks.AlgebraicGeometry.CodimensionOneObstruction

end
