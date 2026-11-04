module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalTypesSitePresentedPullback
public import StacksFrontier.Algebra.Homology.DerivedCategory.LeftDerivedOfExactFunctor
public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackCechDescentSpacesEtale
public import StacksFrontier.AlgebraicGeometry.Spaces.SimplicialAugmentationPullbackExact
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleModulePullbackFlatExact

/-!
# Pullback along a vertex of an fppf hypercovering preserves quasi-coherence

For an fppf hypercovering `U` and a complex `K₀` on the spaces-étale site of `U_0` with
quasi-coherent cohomology, the derived pullback of `K₀` along the last vertex `U_k ⟶ U_0` has
quasi-coherent cohomology; this is the statement `SpacesEtaleVertexQuasicoherent`.

The vertex is a composite of the faces `δ₀`, which are flat. Along a flat morphism the pullback
of modules on the spaces-étale sites is exact, so the derived pullback is the degreewise pullback
and commutes with cohomology; and the pullback of a quasi-coherent module along a morphism of
spaces-étale sites is quasi-coherent.

## Main results

* `isQuasicoherentOnSite_spacesEtaleRingedToposHom_pullbackModules_obj`: pullback of modules
  along `spacesEtaleRingedToposHom f` preserves quasi-coherence.
* `isSpacesEtaleQuasicoherentComplex_spacesEtaleDerivedPull_of_isFlat`: for flat `f`, `Lf^*`
  preserves complexes with quasi-coherent cohomology.
* `isFlat_δ_of_isHypercoveringAugmentation` and
  `isFlat_left_map_const_last_of_isHypercoveringAugmentation`: the faces and the last vertex
  `U_k ⟶ U_0` of an fppf hypercovering are flat.
* `spacesEtaleVertexQuasicoherent`: pullback along a vertex of an fppf hypercovering preserves
  complexes with quasi-coherent cohomology.

## References

* [Stacks Project, Tag 0DER](https://stacks.math.columbia.edu/tag/0DER)
* [Stacks Project, Tag 03DO](https://stacks.math.columbia.edu/tag/03DO)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Space.SimplicialSpacesEtaleSite

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

open Stacks.Cohomology.DerivedPullbackOfToposHom Stacks.CategoryTheory.Hypercovering

attribute [local instance] HasDerivedCategory.standard

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Pullback of modules along a morphism of algebraic spaces preserves quasi-coherence on the
spaces-étale sites** (Stacks 03DO): the morphism of ringed topoi `spacesEtaleRingedToposHom f`
comes from the morphism of sites of base change. -/
theorem isQuasicoherentOnSite_spacesEtaleRingedToposHom_pullbackModules_obj
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (F : SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf (spacesEtaleRingedTopos B S hS Y).O))
    (hF : F.IsQuasicoherentOnSite) :
    ((spacesEtaleRingedToposHom f).toModulesHom.pullbackModules.obj F).IsQuasicoherentOnSite := by
  have : PreservesLimitsOfShape (Discrete PEmpty.{1}) (spacesBaseChange B S hS f).functor :=
    Functor.preservesLimitsOfShape_pempty_of_isTerminal _
      (SpacesEtale.isTerminal_idObj B S hS Y)
      (isTerminal_spacesBaseChange_idObj B S hS f)
  have : HasFiniteLimits (SpacesEtale B S hS Y) := hasFiniteLimits_of_hasTerminal_and_pullbacks
  have : PreservesFiniteLimits (spacesBaseChange B S hS f).functor :=
    preservesFiniteLimits_of_preservesTerminal_and_pullbacks _
  exact RingedToposHom.isQuasicoherentOnSite_pullbackModules_of_isMorphismOfSites
    (spacesEtaleRingedToposHom f) (spacesBaseChange_isMorphismOfSites B S hS f) rfl F hF

/-- **Derived pullback along a flat morphism preserves quasi-coherent cohomology on the
spaces-étale sites.** Along a flat `f` the pullback of modules is exact, so `Lf^*` is the functor
it induces on derived categories, `H^q(Lf^*K) ≅ f^*H^q(K)`, and `f^*` preserves quasi-coherence. -/
theorem isSpacesEtaleQuasicoherentComplex_spacesEtaleDerivedPull_of_isFlat
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hf : IsFlat B S hS f.hom)
    (K : spacesEtaleDerivedModules B S hS Y) (hK : IsSpacesEtaleQuasicoherentComplex B S hS Y K) :
    IsSpacesEtaleQuasicoherentComplex B S hS X ((spacesEtaleDerivedPull B S hS f).obj K) := by
  have := preservesFiniteLimits_spacesEtaleRingedToposHom_pullbackModules_spacesEtaleModulePullbackFlatExact
    f hf
  have := RingedToposHom.pullbackModules_preservesFiniteColimits (spacesEtaleRingedToposHom f)
  have := RingedToposHom.pullbackModules_additive (spacesEtaleRingedToposHom f)
  intro n
  refine SheafOfModules.IsQuasicoherentOnSite.of_iso
    ((DerivedCategory.homologyFunctor _ n).mapIso
      ((Stacks.Homology.leftDerivedIsoMapDerivedCategory
        (spacesEtaleRingedToposHom f).toModulesHom.pullbackModules
        (spacesEtaleDerivedPull B S hS f)
        (derivedPullbackComparison (X := spacesEtaleRingedTopos B S hS X)
          (Y := spacesEtaleRingedTopos B S hS Y) (spacesEtaleRingedToposHom f))).app K).symm) ?_
  refine SheafOfModules.IsQuasicoherentOnSite.of_iso
    ((StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso
      (spacesEtaleRingedToposHom f).toModulesHom.pullbackModules n).app K).symm ?_
  exact isQuasicoherentOnSite_spacesEtaleRingedToposHom_pullbackModules_obj f _ (hK n)

/-- The last vertex `[0] ⟶ [k + 1]` is the last vertex `[0] ⟶ [k]` followed by `δ₀`. -/
theorem const_last_succ_eq_comp_δ_zero (k : ℕ) :
    SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk (k + 1)) (Fin.last (k + 1)) =
      SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk k) (Fin.last k) ≫
        SimplexCategory.δ (0 : Fin (k + 2)) := by
  ext i
  fin_cases i
  simp [SimplexCategory.δ, Fin.succAbove]

/-- The last vertex `[0] ⟶ [0]` is the identity. -/
theorem const_last_zero_eq_id :
    SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk 0) (Fin.last 0) =
      𝟙 (SimplexCategory.mk 0) := by
  ext i
  fin_cases i
  rfl

/-- The flat morphisms of algebraic spaces, as a morphism property. -/
abbrev isFlatMorphismProperty : MorphismProperty (AlgebraicSpaces B S hS) :=
  fun _ _ f => IsFlat B S hS f.hom

/-- Flat morphisms of algebraic spaces are stable under base change. -/
instance isFlatMorphismProperty_isStableUnderBaseChange :
    (isFlatMorphismProperty (B := B) (S := S) (hS := hS)).IsStableUnderBaseChange :=
  isFlat_isStableUnderBaseChange _ _ _

/-- Flat morphisms of algebraic spaces contain the identities and are closed under composition. -/
instance isFlatMorphismProperty_isMultiplicative :
    (isFlatMorphismProperty (B := B) (S := S) (hS := hS)).IsMultiplicative where
  id_mem Z := isFlat_id _ _ _ Z.2
  comp_mem {Z₁ Z₂ Z₃} f g hf hg := isFlat_comp _ _ _ Z₁.2 Z₂.2 Z₃.2 f.hom g.hom hf hg

/-- An fppf hypercovering of algebraic spaces is a hypercovering for the flat morphisms. -/
theorem isHypercovering_isFlatMorphismProperty_of_isHypercoveringAugmentation
    (U : SimplicialObject.Augmented (AlgebraicSpaces B S hS))
    (hU : IsHypercoveringAugmentation
      (bigFppfSpaceSiteOfSchemeSite B S hS).pretopologyBigFppfPretopology U.left U.hom) :
    (isFlatMorphismProperty (B := B) (S := S) (hS := hS)).IsHypercovering U :=
  { map_zero := isFlat_of_singleton_mem_pretopology _ hU.1
    map_one := isFlat_of_singleton_mem_pretopology _ hU.2.1
    matching := fun n hn => isFlat_of_singleton_mem_pretopology _ (hU.2.2 n hn) }

/-- **The faces of an fppf hypercovering are flat** (Stacks 0DER). -/
theorem isFlat_δ_of_isHypercoveringAugmentation
    (U : SimplicialObject.Augmented (AlgebraicSpaces B S hS))
    (hU : IsHypercoveringAugmentation
      (bigFppfSpaceSiteOfSchemeSite B S hS).pretopologyBigFppfPretopology U.left U.hom)
    (k : ℕ) (i : Fin (k + 2)) :
    IsFlat B S hS (U.left.δ i).hom :=
  MorphismProperty.IsHypercovering.face_mem _
    (isHypercovering_isFlatMorphismProperty_of_isHypercoveringAugmentation U hU) k i

/-- **The last vertex of an fppf hypercovering is flat** (Stacks 0DER): `U_k ⟶ U_0` is a
composite of faces `δ₀`, each flat. -/
theorem isFlat_left_map_const_last_of_isHypercoveringAugmentation
    (U : SimplicialObject.Augmented (AlgebraicSpaces B S hS))
    (hU : IsHypercoveringAugmentation
      (bigFppfSpaceSiteOfSchemeSite B S hS).pretopologyBigFppfPretopology U.left U.hom) (k : ℕ) :
    IsFlat B S hS (U.left.map (SimplexCategory.const (SimplexCategory.mk 0)
      (SimplexCategory.mk k) (Fin.last k)).op).hom := by
  show isFlatMorphismProperty _
  induction k with
  | zero =>
    rw [const_last_zero_eq_id, op_id, U.left.map_id]
    exact MorphismProperty.id_mem _ _
  | succ k ih =>
    rw [const_last_succ_eq_comp_δ_zero, op_comp, U.left.map_comp]
    exact MorphismProperty.comp_mem _ _ _ (isFlat_δ_of_isHypercoveringAugmentation U hU k 0) ih

variable (B S hS) in
/-- **Pullback along a vertex of an fppf hypercovering preserves quasi-coherence**: the derived
pullback along `U_k ⟶ U_0` of a complex with quasi-coherent cohomology has quasi-coherent
cohomology. -/
theorem spacesEtaleVertexQuasicoherent : SpacesEtaleVertexQuasicoherent B S hS :=
  fun U hU K₀ hK₀ k =>
    isSpacesEtaleQuasicoherentComplex_spacesEtaleDerivedPull_of_isFlat _
      (isFlat_left_map_const_last_of_isHypercoveringAugmentation U hU k) K₀ hK₀

end AlgebraicGeometry.Space.SimplicialSpacesEtaleSite
