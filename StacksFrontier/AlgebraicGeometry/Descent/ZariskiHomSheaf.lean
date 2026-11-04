module

public import StacksFrontier.AlgebraicGeometry.Descent.FpqcHomSheaf
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.EventualMapEq

/-!
# The Zariski sheaf condition for the presheaf of morphisms of modules

For a scheme `X` and sheaves of modules `A` and `B` on `X`, Mathlib's
`CategoryTheory.Pseudofunctor.presheafHom` for the pullback pseudofunctor of sheaves of modules
is the presheaf on the schemes over `X` sending `T ⟶ X` to the morphisms `T^* A ⟶ T^* B`. This
file shows that this presheaf is separated for Zariski coverings, for arbitrary sheaves of
modules, and that it is a Zariski sheaf whenever morphisms of sheaves of modules glue along open
coverings, `AlgebraicGeometry.ZariskiModuleHomAmalgamation`.

## Main definitions

* `AlgebraicGeometry.overPresieve`: the presieve on the terminal object of the schemes over `X`
  attached to a family of morphisms `u i : U i ⟶ X`.
* `AlgebraicGeometry.ZariskiModuleHomAmalgamation`: for every jointly surjective family of open
  immersions `u i : U i ⟶ X` and all sheaves of modules `A` and `B` on `X`, every compatible
  family of morphisms `(u i)^* A ⟶ (u i)^* B` has an amalgamation.

## Main results

* `AlgebraicGeometry.isSeparatedFor_presheafHom_zariski`: a morphism `A ⟶ B` of sheaves of
  modules on a scheme is determined by its restrictions to a jointly surjective family of open
  immersions.
* `AlgebraicGeometry.pullback_map_eq_of_pullHom_eq`: the pullback map on morphisms is determined
  by the restriction map of the presheaf of morphisms.
* `AlgebraicGeometry.isSheafFor_presheafHom_zariski`,
  `AlgebraicGeometry.isPrestackFor_zariski_of_amalgamation`,
  `AlgebraicGeometry.isPrestack_zariski_of_amalgamation` and
  `AlgebraicGeometry.isSheaf_presheafHom_zariski_of_amalgamation`: assuming
  `AlgebraicGeometry.ZariskiModuleHomAmalgamation`, the sheaf condition for the presheaf of
  morphisms for a Zariski covering family, the descent of morphisms along a Zariski covering
  family, the prestack property of the pullback pseudofunctor for the Zariski topology, and the
  Zariski sheaf property of the presheaf of morphisms.

## Implementation notes

The comparison isomorphisms of `AlgebraicGeometry.modulePullbackPseudofunctor_pullHom` are
cancelled with `cancel_epi` and `cancel_mono` as terms rather than as rewrites: the equation
lives in a hom type spelled with the pseudofunctor's `map`, while its two sides are spelled with
`AlgebraicGeometry.Scheme.Modules.pullback`, and a rewrite whose motive mentions both is
rejected at `implicit` transparency.

## References

* [Stacks Project, Tag 023T](https://stacks.math.columbia.edu/tag/023T)
* [Stacks Project, Tag 03DT](https://stacks.math.columbia.edu/tag/03DT)
-/

@[expose] public section

open CategoryTheory Opposite
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- The presieve on the terminal object `X ⟶ X` of the schemes over `X` attached to a family of
morphisms `u i : U i ⟶ X`. -/
abbrev overPresieve {X : Scheme.{u}} {ι : Type*} {U : ι → Scheme.{u}} (u : ∀ i, U i ⟶ X) :
    Presieve (Over.mk (𝟙 X)) :=
  Presieve.ofArrows (fun i ↦ Over.mk (u i))
    (fun i ↦ (Over.homMk (u i) : Over.mk (u i) ⟶ Over.mk (𝟙 X)))

/-- Morphisms of sheaves of modules glue along open coverings: for every jointly surjective
family of open immersions `u i : U i ⟶ X` and all sheaves of modules `A` and `B` on `X`, every
compatible family of morphisms `(u i)^* A ⟶ (u i)^* B` is the restriction of a morphism
`A ⟶ B`. -/
def ZariskiModuleHomAmalgamation : Prop :=
  ∀ ⦃X : Scheme.{u}⦄ ⦃ι : Type (u + 1)⦄ ⦃U : ι → Scheme.{u}⦄ (u : ∀ i, U i ⟶ X),
    Presieve.ofArrows U u ∈ Scheme.zariskiPrecoverage.{u} X →
    ∀ (A B : X.Modules)
      (x : Presieve.FamilyOfElements (modulePullbackPseudofunctor.presheafHom A B)
        (overPresieve u)),
      x.Compatible → ∃ t, x.IsAmalgamation t

/-- The restriction map of the presheaf of morphisms determines the pullback map on morphisms:
two morphisms with the same restriction along `f` have the same pullback along `f`. -/
lemma pullback_map_eq_of_pullHom_eq {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z)
    (w : f ≫ g = h) {M N : Z.Modules}
    {t₁ t₂ : (Scheme.Modules.pullback g).obj M ⟶ (Scheme.Modules.pullback g).obj N}
    (heq : Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (F := modulePullbackPseudofunctor) t₁ f h h w w =
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (F := modulePullbackPseudofunctor) t₂ f h h w w) :
    (Scheme.Modules.pullback f).map t₁ = (Scheme.Modules.pullback f).map t₂ :=
  have heq' := ((modulePullbackPseudofunctor_pullHom f g h w M N t₁).symm.trans heq).trans
    (modulePullbackPseudofunctor_pullHom f g h w M N t₂)
  (cancel_mono _).mp ((cancel_epi _).mp ((cancel_epi _).mp heq'))

/-- The presheaf of morphisms is separated for Zariski covering families: a morphism
`X^* A ⟶ X^* B` of sheaves of modules on a scheme is determined by its restrictions to the
members of a jointly surjective family of open immersions. -/
theorem isSeparatedFor_presheafHom_zariski {X : Scheme.{u}} {ι : Type*} {U : ι → Scheme.{u}}
    (u : ∀ i, U i ⟶ X) (hu : ∀ i, IsOpenImmersion (u i))
    (hcov : ∀ x : X, ∃ i, x ∈ Set.range (u i)) (A B : X.Modules) :
    Presieve.IsSeparatedFor (modulePullbackPseudofunctor.presheafHom A B) (overPresieve u) := by
  intro x t₁ t₂ h₁ h₂
  have key (i : ι) : (Scheme.Modules.pullback (u i)).map t₁ =
      (Scheme.Modules.pullback (u i)).map t₂ := by
    have := hu i
    exact pullback_map_eq_of_pullHom_eq (u i) (𝟙 X) (u i) (Category.comp_id _)
      ((h₁ _ (Presieve.ofArrows.mk i)).trans (h₂ _ (Presieve.ofArrows.mk i)).symm)
  refine Stacks.AlgebraicGeometry.ModuleLimits.hom_ext_of_restrict_cover
    (fun i ↦ (u i).opensRange) hcov fun i ↦ ?_
  have := hu i
  refine Stacks.AlgebraicGeometry.ModuleLimits.map_eq_of_natIso
    (Scheme.Modules.restrictFunctorIsoPullback ((u i).opensRange).ι).symm ?_
  rw [← Scheme.Hom.isoOpensRange_inv_comp (u i)]
  exact Stacks.AlgebraicGeometry.ModuleLimits.pullback_map_eq_of_precomp _ _ (key i)

/-- If `AlgebraicGeometry.ZariskiModuleHomAmalgamation` holds, the presheaf of morphisms of two
sheaves of modules on `X` satisfies the sheaf condition for every Zariski covering family of `X`,
read as a presieve of the terminal object of the schemes over `X`. -/
theorem isSheafFor_presheafHom_zariski (hz : ZariskiModuleHomAmalgamation.{u})
    {X : Scheme.{u}} {ι : Type (u + 1)} {U : ι → Scheme.{u}} (u : ∀ i, U i ⟶ X)
    (hu : Presieve.ofArrows U u ∈ Scheme.zariskiPrecoverage.{u} X) (A B : X.Modules) :
    Presieve.IsSheafFor (modulePullbackPseudofunctor.presheafHom A B) (overPresieve u) := by
  have hu' : (∀ x : X, ∃ i, x ∈ Set.range (u i)) ∧ ∀ i, IsOpenImmersion (u i) := by
    simpa using hu
  exact (isSeparatedFor_presheafHom_zariski u hu'.2 hu'.1 A B).isSheafFor (hz u hu A B)

/-- If `AlgebraicGeometry.ZariskiModuleHomAmalgamation` holds, the pullback pseudofunctor of
sheaves of modules satisfies the descent of morphisms for every Zariski covering family. -/
theorem isPrestackFor_zariski_of_amalgamation (hz : ZariskiModuleHomAmalgamation.{u})
    (X : Scheme.{u}) (R : Presieve X) (hR : R ∈ Scheme.zariskiPrecoverage.{u} X) :
    modulePullbackPseudofunctor.IsPrestackFor R := by
  obtain ⟨ι, U, u, rfl⟩ := R.exists_eq_ofArrows
  rw [Pseudofunctor.isPrestackFor_ofArrows_iff,
    Functor.FullyFaithful.nonempty_iff_map_bijective]
  intro A B
  rw [Pseudofunctor.bijective_toDescentData_map_iff]
  exact isSheafFor_presheafHom_zariski hz u hR A B

/-- If `AlgebraicGeometry.ZariskiModuleHomAmalgamation` holds, the pullback pseudofunctor of
sheaves of modules is a prestack for the Zariski topology. -/
theorem isPrestack_zariski_of_amalgamation (hz : ZariskiModuleHomAmalgamation.{u}) :
    modulePullbackPseudofunctor.IsPrestack Scheme.zariskiTopology.{u} :=
  Pseudofunctor.IsPrestack.of_precoverage (isPrestackFor_zariski_of_amalgamation hz)

/-- If `AlgebraicGeometry.ZariskiModuleHomAmalgamation` holds, then for every scheme `S` and all
sheaves of modules `M` and `N` on `S`, the presheaf on the schemes over `S` sending `T ⟶ S` to
the morphisms `T^* M ⟶ T^* N` is a sheaf for the Zariski topology. -/
theorem isSheaf_presheafHom_zariski_of_amalgamation (hz : ZariskiModuleHomAmalgamation.{u})
    {S : Scheme.{u}} (M N : S.Modules) :
    Presheaf.IsSheaf (Scheme.zariskiTopology.{u}.over S)
      (modulePullbackPseudofunctor.presheafHom M N) :=
  have := isPrestack_zariski_of_amalgamation hz
  Pseudofunctor.IsPrestack.isSheaf (F := modulePullbackPseudofunctor)
    Scheme.zariskiTopology.{u} M N

end AlgebraicGeometry

end
