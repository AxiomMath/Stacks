module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EtaleModuleCohomologyForget
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.AcyclicResolutionBaseChange

/-!
# Higher direct images of the underlying abelian sheaf of an injective sheaf of modules

Let `f : X ⟶ Y` be a morphism of schemes, `Λ` a ring and `I` an injective sheaf of `Λ`-modules on
`X_étale`. The underlying abelian sheaf of `I` is in general not an injective abelian sheaf, but
its higher direct images vanish: `R^q f_*(I_ab) = 0` for `q > 0`. This is [Stacks, Tag 03FD] for
direct images,
`Stacks.Cohomology.InjectiveModuleSheafAcyclicity.isZero_higherDirectImage_toSheaf_succ`, read
through the equivalence of sheaves of `Λ`-modules on the small étale site with sheaves of modules
over the constant sheaf of rings `Λ̲`.

## Main results

* `Stacks.EtaleCohomology.rightAcyclic_etaleAbelianDirectImage_etaleModuleForgetUniv_obj`: the
  underlying abelian sheaf of an injective sheaf of `Λ`-modules is acyclic for `f_*`.

## References

* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
* [Stacks Project, Tag 072W](https://stacks.math.columbia.edu/tag/072W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

attribute [local instance] HasDerivedCategory.standard

universe u r

namespace Stacks.EtaleCohomology

variable (Λ : Type r) [Ring Λ]

attribute [local instance] Stacks.Cohomology.SiteModules.site_wEqualsLocallyBijective_addCommGrp
  Stacks.Cohomology.SiteModules.site_hasExt_addCommGrp

/-- **The underlying abelian sheaf of an injective sheaf of `Λ`-modules is acyclic for direct
image** ([Stacks, Tag 03FD]): through the equivalence with sheaves of modules over the constant
sheaf of rings `Λ̲`, its higher direct images vanish. -/
theorem rightAcyclic_etaleAbelianDirectImage_etaleModuleForgetUniv_obj {X Y : Scheme.{u}}
    (f : X ⟶ Y) (I : EtaleModules.{u, r} Λ X) [Injective I] :
    (etaleAbelianDirectImage.{u, r} f).rightAcyclic ((etaleModuleForgetAb.{u, r} Λ X).obj I) := by
  refine (Stacks.Cohomology.rightAcyclic_iff_isZero_rightDerived _ _).2 fun p hp => ?_
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  let E := etaleModuleSheafEquivalence.{u, r} Λ X
  have : Injective (E.functor.obj I) := E.symm.toAdjunction.map_injective I inferInstance
  have h :=
    Stacks.Cohomology.InjectiveModuleSheafAcyclicity.isZero_higherDirectImage_toSheaf_succ.{r}
      Y.smallEtaleTopology X.smallEtaleTopology (smallEtaleBaseChange f)
      (etaleConstantRingSheaf.{u, r} Λ X) (E.functor.obj I) q
  exact h.of_iso (((etaleAbelianDirectImage.{u, r} f).rightDerived (q + 1)).mapIso
    ((etaleModuleSheafEquivalenceFunctorCompToSheaf.{u, r} Λ X).app I).symm)

end Stacks.EtaleCohomology
