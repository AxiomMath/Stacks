module

public import StacksFrontier.Algebra.Homology.DerivedCategory.LeftDerivedOfExactFunctor
public import StacksFrontier.AlgebraicGeometry.Quot.SmallEtaleSpacesEtaleDerivedFullyFaithful
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleModulePullbackFaithfullyFlat

/-!
# The essential image of `Φ` descends along fppf coverings

Let `Φ_X = AlgebraicGeometry.Space.smallEtaleSpacesEtaleDerivedFunctor` be the comparison of the
derived category of modules on the small étale site of an algebraic space `X` (sections in
`Type u`) with that on its spaces-étale site (sections in `Type (u + 1)`). This file proves the
fourth clause of `AlgebraicGeometry.Space.SmallEtaleSpacesEtaleDescentComparison`. Let
`f : Y ⟶ X` be an fppf covering, `L` a complex on the spaces-étale site of `X` with
quasi-coherent cohomology, and `K'` a complex on the small étale site of `Y` with quasi-coherent
cohomology such that `Φ_Y(K') ≅ Lf^*L`. Then `L ≅ Φ_X(K)` for some `K` with quasi-coherent
cohomology.

Since `f` is flat, `Lf^*` is computed degreewise, so `f^*Hⁿ(L) ≅ Hⁿ(Lf^*L) ≅ ι(Hⁿ(K'))` has
`u`-small sections. Since `f` is moreover surjective, the unit `Hⁿ(L) ⟶ f_*f^*Hⁿ(L)` is a
monomorphism (`AlgebraicGeometry.Space.mono_spacesEtalePullbackAdjunction_unit_app`), and the
sections of `f_*f^*Hⁿ(L)` over `V` are those of `f^*Hⁿ(L)` over `V ×_X Y`. So `Hⁿ(L)` has
`u`-small sections, and the essential image of `Φ_X` contains `L`
(`AlgebraicGeometry.Space.exists_smallEtaleSpacesEtaleDerivedFunctor_obj_iso_of_quasicoherent`).

## Main results

* `AlgebraicGeometry.Space.small_of_small_spacesEtalePullbackModules_obj`: along a flat
  surjective morphism, a module on the spaces-étale site whose pullback has `u`-small sections
  has `u`-small sections.
* `AlgebraicGeometry.Space.exists_smallEtaleSpacesEtaleDerivedFunctor_obj_iso_of_fppfCovering`:
  the fourth clause of `AlgebraicGeometry.Space.SmallEtaleSpacesEtaleDescentComparison`.

## References

* [Stacks Project, Tag 03G1](https://stacks.math.columbia.edu/tag/03G1)
* [Stacks Project, Tag 05V5](https://stacks.math.columbia.edu/tag/05V5)
* [Stacks Project, Tag 0GYY](https://stacks.math.columbia.edu/tag/0GYY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry.Space

universe u

open SimplicialSpacesEtaleSite Stacks.Cohomology.DerivedPullbackOfToposHom

section Descent

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)

/-- The direct image along the spaces-étale morphism of `f` of a module with `u`-small sections
has `u`-small sections: its sections over `V` are those of the module over `V ×_Y X`. -/
theorem small_spacesEtalePushforwardModules_obj
    (H : SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf (spacesEtaleRingedTopos B S hS X).O))
    (hH : ∀ W : (SpacesEtale B S hS X)ᵒᵖ, Small.{u} (H.val.obj W))
    (V : (SpacesEtale B S hS Y)ᵒᵖ) :
    Small.{u} (((Stacks.Sheaves.RingedToposModules.pushforwardModules
      (spacesEtaleRingedToposHom f).toModulesHom).obj H).val.obj V) :=
  hH (op ((spacesBaseChange B S hS f).functor.obj V.unop))

/-- **Along a flat surjective morphism `f : X ⟶ Y`, `u`-smallness of sections descends**: an
`𝒪_Y`-module on the spaces-étale site whose pullback `f^*G` has `u`-small sections has `u`-small
sections. The unit `G ⟶ f_*f^*G` is a monomorphism, hence injective on sections. -/
theorem small_of_small_spacesEtalePullbackModules_obj (hf : IsFlat B S hS f.hom)
    (hs : IsSurjective B S hS f.hom)
    (G : SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf (spacesEtaleRingedTopos B S hS Y).O))
    (hG : ∀ W : (SpacesEtale B S hS X)ᵒᵖ,
      Small.{u} (((spacesEtaleRingedToposHom f).toModulesHom.pullbackModules.obj G).val.obj W))
    (V : (SpacesEtale B S hS Y)ᵒᵖ) :
    Small.{u} (G.val.obj V) := by
  let η : G ⟶ (Stacks.Sheaves.RingedToposModules.pushforwardModules
      (spacesEtaleRingedToposHom f).toModulesHom).obj
        ((spacesEtaleRingedToposHom f).toModulesHom.pullbackModules.obj G) :=
    (Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules
      (spacesEtaleRingedToposHom f).toModulesHom).unit.app G
  have : Mono η := mono_spacesEtalePullbackAdjunction_unit_app f hf hs G
  have := small_spacesEtalePushforwardModules_obj f _ hG V
  exact small_of_injective (f := fun x : G.val.obj V ↦ (η.val.app V).hom x)
    (PresheafOfModules.injective_of_mono ((SheafOfModules.forget _).map η) V)

end Descent

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] HasDerivedCategory.standard

/-- **The essential image of `Φ` descends along fppf coverings**: the fourth clause of
`AlgebraicGeometry.Space.SmallEtaleSpacesEtaleDescentComparison`. If `L` is a complex on the
spaces-étale site of `X` with quasi-coherent cohomology, `f : Y ⟶ X` is an fppf covering and
`Φ_Y(K') ≅ Lf^*L` for a complex `K'` on the small étale site of `Y` with quasi-coherent
cohomology, then `L ≅ Φ_X(K)` for a complex `K` on the small étale site of `X` with
quasi-coherent cohomology. -/
theorem exists_smallEtaleSpacesEtaleDerivedFunctor_obj_iso_of_fppfCovering
    {X Y : AlgebraicSpaces B S hS} (f : Y ⟶ X) (hf : fppfCoveringMorphisms B S hS f)
    (L : spacesEtaleDerivedModules B S hS X) (hL : IsSpacesEtaleQuasicoherentComplex B S hS X L)
    (K' : derivedModules B S hS Y) (_ : IsSmallEtaleQuasicoherentComplex B S hS Y K')
    (e : Nonempty ((smallEtaleSpacesEtaleDerivedFunctor B S hS Y).obj K' ≅
      (spacesEtaleDerivedPull B S hS f).obj L)) :
    ∃ K : derivedModules B S hS X, IsSmallEtaleQuasicoherentComplex B S hS X K ∧
      Nonempty ((smallEtaleSpacesEtaleDerivedFunctor B S hS X).obj K ≅ L) := by
  obtain ⟨e⟩ := e
  have hflat : IsFlat B S hS f.hom := hf.flat ()
  have hsurj : IsSurjective B S hS f.hom :=
    (isJointlySurjective_const_iff B S hS (I := Unit) f.hom).1 hf.jointly_surjective
  have := preservesFiniteLimits_spacesEtaleRingedToposHom_pullbackModules_spacesEtaleModulePullbackFlatExact
    f hflat
  have := RingedToposHom.pullbackModules_preservesFiniteColimits (spacesEtaleRingedToposHom f)
  have := RingedToposHom.pullbackModules_additive (spacesEtaleRingedToposHom f)
  have := preservesFiniteLimits_toSpacesEtaleModules B S hS Y
  have := preservesFiniteColimits_toSpacesEtaleModules B S hS Y
  refine exists_smallEtaleSpacesEtaleDerivedFunctor_obj_iso_of_quasicoherent B S hS X L hL
    (fun n V ↦ small_of_small_spacesEtalePullbackModules_obj f hflat hsurj _ (fun W ↦ ?_) V)
  let e₁ := ((spacesEtaleRingedToposHom f).toModulesHom.pullbackModules
    |>.mapDerivedCategoryHomologyIso n).app L
  let e₂ := (DerivedCategory.homologyFunctor _ n).mapIso
    ((Stacks.Homology.leftDerivedIsoMapDerivedCategory
      (spacesEtaleRingedToposHom f).toModulesHom.pullbackModules
      (spacesEtaleDerivedPull B S hS f)
      (derivedPullbackComparison (X := spacesEtaleRingedTopos B S hS Y)
        (Y := spacesEtaleRingedTopos B S hS X) (spacesEtaleRingedToposHom f))).app L)
  let e₃ := (DerivedCategory.homologyFunctor _ n).mapIso e
  let e₄ := ((toSpacesEtaleRingedToposModules B S hS Y).mapDerivedCategoryHomologyIso n).app K'
  let E := e₁.symm ≪≫ e₂.symm ≪≫ e₃.symm ≪≫ e₄
  exact @small_map _ _ (small_toSpacesEtaleModules_obj B S hS Y _ W)
    ((PresheafOfModules.evaluation _ W).mapIso
      ((SheafOfModules.forget _).mapIso E)).toLinearEquiv.toEquiv

end AlgebraicGeometry.Space

end
