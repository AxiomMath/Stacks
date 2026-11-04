module

public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparisonTopologies
public import StacksFrontier.AlgebraicGeometry.Spaces.SimplicialSpaces.FppfSite
public import StacksFrontier.CategoryTheory.Sites.Topos.AbelianInverseImageULift
import StacksFrontier.AlgebraicGeometry.Spaces.StructureSheaf

/-!
# The comparison of the fppf site of an algebraic space with its spaces-étale site

Let `S` be a scheme and `Y` an algebraic space over `S`. The functor
`Y_{spaces, étale} → (Spaces/Y)_fppf`, `V ↦ V/Y`, is a morphism of sites, and defines the
morphism of topoi

`a_Y : Sh((Spaces/Y)_fppf) → Sh(Y_étale)`

of Section 0DGE (written `a_Y = ε_Y ∘ π_Y` there). These are the horizontal arrows of the
diagram of Stacks 0DH5 used in the proof of Stacks 0DH7, for `Y = X` and `Y = U_n`, and the
morphisms whose cohomological behaviour Stacks 0DGG describes.

## Main definitions

* `AlgebraicGeometry.Space.fppfSpacesEtaleMorphism`: the morphism of topoi `a_Y`.
* `AlgebraicGeometry.Space.fppfSpacesEtaleAbelianDirectImage` and
  `AlgebraicGeometry.Space.fppfSpacesEtaleAbelianAdjunction`: its direct image on abelian
  sheaves, restriction along `V ↦ V/Y`, and the adjunction `a_Y^{-1} ⊣ a_{Y,*}`.
* `AlgebraicGeometry.Space.FppfSpacesEtaleAcyclic`: the property of `Y` that
  `F → a_{Y,*} a_Y^{-1} F` is an isomorphism and `R^q a_{Y,*} a_Y^{-1} F = 0` for `q > 0`, for
  every abelian sheaf `F` on `Y_étale`; this is the content of Stacks 0DGG read on a single
  abelian sheaf.

## Main results

* `AlgebraicGeometry.Space.spacesEtale_precoverage_le_comap_fppf`: an étale covering of the
  spaces-étale site of `Y` is an fppf covering (Stacks 0DFC).
* `AlgebraicGeometry.Space.spacesEtaleInclusion_isMorphismOfSites_fppf`: `V ↦ V/Y` is a
  morphism of sites `(Spaces/Y)_fppf → Y_{spaces, étale}`.

## Implementation notes

The fppf site of `Y` is the localization at `Y` of the fppf site of
`StacksFrontier.AlgebraicGeometry.Spaces.SimplicialSpaces.FppfSite`, and the étale topos of `Y` is
the topos of its spaces-étale site, as in Section 0DE7. The functor `V ↦ V/Y` is the full
inclusion of the spaces-étale site into the slice.

## References

* [Stacks Project, Tag 0DGE](https://stacks.math.columbia.edu/tag/0DGE)
* [Stacks Project, Tag 0DGG](https://stacks.math.columbia.edu/tag/0DGG)
* [Stacks Project, Tag 0DH5](https://stacks.math.columbia.edu/tag/0DH5)
* [Stacks Project, Tag 0DFC](https://stacks.math.columbia.edu/tag/0DFC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.Topos.AbelianPushforward

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} (Y : AlgebraicSpaces B S hS)

/-- **An étale covering is an fppf covering.** A jointly point-surjective family of the
spaces-étale site of `Y` generates a covering sieve of the fppf site of `Y`, by Stacks 0DFC. -/
theorem spacesEtale_precoverage_le_comap_fppf :
    SpacesEtale.precoverage B S hS Y ≤
      ((fppfTopology B S hS).over Y).toPrecoverage.comap (SpacesEtale.inclusion B S hS Y) := by
  intro A R hR
  rw [Precoverage.mem_comap_iff, GrothendieckTopology.mem_toPrecoverage_iff]
  obtain ⟨F, rfl, hF⟩ := (SpacesEtale.mem_precoverage_iff B S hS Y).1 hR
  rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_generate]
  let G := SpacesEtale.toSpaces B S hS Y
  have hEq : Sieve.generate (Presieve.functorPushforward (Over.forget Y)
      ((F.map (SpacesEtale.inclusion B S hS Y)).presieve₀)) =
      Sieve.generate ((F.map G).presieve₀) := by
    rw [PreZeroHypercover.presieve₀_map, ← Sieve.arrows_generate_map_eq_functorPushforward,
      Sieve.generate_sieve, PreZeroHypercover.presieve₀_map]
    simp [G, SpacesEtale.toSpaces, SpacesEtale.inclusion]
  rw [← PreZeroHypercover.presieve₀_map, hEq]
  refine Precoverage.generate_mem_toGrothendieck ⟨F.I₀, fun i ↦ G.obj (F.X i),
    fun i ↦ G.map (F.f i), rfl, isFppfCovering_of_isEtaleCovering B S hS ?_⟩
  refine ⟨(G.obj A).property, fun i ↦ (G.obj (F.X i)).property, fun i ↦ ?_, ?_⟩
  · exact isEtale_of_isEtale_over B S hS (G.obj (F.X i)).property (G.obj A).property Y.property
      (G.map (F.f i)).hom ((F.X i).1.hom).hom A.1.hom.hom (F.X i).property A.property
      (congrArg (fun k ↦ k.hom) (Over.w (F.f i).hom))
  · refine Set.eq_univ_of_forall fun x ↦ ?_
    obtain ⟨i, y, hy⟩ := hF x
    exact Set.mem_iUnion.2 ⟨i, y, hy⟩

/-- The functor `V ↦ V/Y` is continuous from the spaces-étale site of `Y` to the fppf site of
`Y`. -/
instance spacesEtaleInclusion_isContinuous_fppf :
    (SpacesEtale.inclusion B S hS Y).IsContinuous (SpacesEtale.topology B S hS Y)
      ((fppfTopology B S hS).over Y) :=
  Stacks.Sites.isContinuous_toGrothendieck_of_le_comap _ _ _
    (spacesEtale_precoverage_le_comap_fppf Y)

/-- **Section 0DGE.** The functor `V ↦ V/Y` from the spaces-étale site of `Y` to the fppf site
of `Y` is a morphism of sites `(Spaces/Y)_fppf → Y_{spaces, étale}`: it is continuous and
preserves the final object and fibre products. -/
theorem spacesEtaleInclusion_isMorphismOfSites_fppf :
    (SpacesEtale.inclusion B S hS Y).IsMorphismOfSites (SpacesEtale.topology B S hS Y)
      ((fppfTopology B S hS).over Y) :=
  Functor.isMorphismOfSites_of_isTerminal _ _ _ (SpacesEtale.final_isTerminal B S hS Y)
    Over.mkIdTerminal

/-- **Section 0DGE.** The morphism of topoi `a_Y : Sh((Spaces/Y)_fppf) → Sh(Y_étale)`. -/
abbrev fppfSpacesEtaleMorphism :
    MorphismOfTopoi (Sheaf ((fppfTopology B S hS).over Y) (Type (u + 1)))
      (Sheaf (SpacesEtale.topology B S hS Y) (Type (u + 1))) :=
  (spacesEtaleInclusion_isMorphismOfSites_fppf Y).morphismOfTopoi

/-- The direct image `a_{Y,*}` on sheaves of sets, restriction along `V ↦ V/Y`, is a right
adjoint. -/
instance isRightAdjoint_spacesEtaleInclusion_sheafPushforwardContinuous_fppf :
    ((SpacesEtale.inclusion B S hS Y).sheafPushforwardContinuous (Type (u + 1))
      (SpacesEtale.topology B S hS Y) ((fppfTopology B S hS).over Y)).IsRightAdjoint :=
  ⟨_, ⟨(fppfSpacesEtaleMorphism Y).adj⟩⟩

/-- The direct image `a_{Y,*}` on abelian sheaves: restriction along `V ↦ V/Y`. -/
abbrev fppfSpacesEtaleAbelianDirectImage :
    Sheaf ((fppfTopology B S hS).over Y) AddCommGrpCat.{u + 1} ⥤
      Sheaf (SpacesEtale.topology B S hS Y) AddCommGrpCat.{u + 1} :=
  (SpacesEtale.inclusion B S hS Y).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
    (SpacesEtale.topology B S hS Y) ((fppfTopology B S hS).over Y)

/-- The inverse image `a_Y^{-1}` on abelian sheaves. -/
abbrev fppfSpacesEtaleAbelianInverseImage :
    Sheaf (SpacesEtale.topology B S hS Y) AddCommGrpCat.{u + 1} ⥤
      Sheaf ((fppfTopology B S hS).over Y) AddCommGrpCat.{u + 1} :=
  Sites.abelianInverseImage (fppfSpacesEtaleMorphism Y)

/-- The adjunction `a_Y^{-1} ⊣ a_{Y,*}` on abelian sheaves. -/
abbrev fppfSpacesEtaleAbelianAdjunction :
    fppfSpacesEtaleAbelianInverseImage Y ⊣ fppfSpacesEtaleAbelianDirectImage Y :=
  abelianInverseImageAdjRestriction (SpacesEtale.inclusion B S hS Y)
    (SpacesEtale.topology B S hS Y) ((fppfTopology B S hS).over Y) (fppfSpacesEtaleMorphism Y)
    (Iso.refl _)

/-- The direct image `a_{Y,*}` on abelian sheaves is an additive functor. -/
instance fppfSpacesEtaleAbelianDirectImage_additive :
    (fppfSpacesEtaleAbelianDirectImage Y).Additive where

/-- The property of `Y` that, for every abelian sheaf `F` on `Y_étale`, the unit
`F → a_{Y,*} a_Y^{-1} F` is an isomorphism and `R^q a_{Y,*} a_Y^{-1} F = 0` for `q > 0`. This is
what Stacks 0DGG asserts for `K = F[0]`, and by Leray's acyclicity lemma it is equivalent to
Stacks 0DGG on `D^+(Y_étale)`. -/
def FppfSpacesEtaleAcyclic : Prop :=
  ∀ F : Sheaf (SpacesEtale.topology B S hS Y) AddCommGrpCat.{u + 1},
    IsIso ((fppfSpacesEtaleAbelianAdjunction Y).unit.app F) ∧
      ∀ q : ℕ, 0 < q → IsZero (((fppfSpacesEtaleAbelianDirectImage Y).rightDerived q).obj
        ((fppfSpacesEtaleAbelianInverseImage Y).obj F))

end AlgebraicGeometry.Space

end
