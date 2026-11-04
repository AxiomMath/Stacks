module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LowerShriekForgetFullyFaithful
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackContinuousUnivLE
public import StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.ModuleLowerShriekAcyclic
public import StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.ProjectionLowerShriekAcyclic
public import StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.RingedProjection
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LowerShriek.DerivedAdjunction
import StacksCore.Tactic.StacksAttribute

/-!
# Lower shriek of modules for the projection of a fibred category

Let `(D, O_D)` be a ringed site and `p : C ⥤ D` a fibred category over its underlying site, the
standing data of Stacks 08P8, with `C` carrying the inherited topology, `π : Sh(C) ⟶ Sh(D)` the
induced morphism of topoi and `O_C = π⁻¹O_D`. Since `π⁻¹` is restriction along `p`, `O_C` is the
restriction of `O_D` along `p` and `π^* = π⁻¹` on modules is restriction along `p`. It has a left
adjoint `π_! : Mod(O_C) ⥤ Mod(O_D)`, and on abelian sheaves `π⁻¹` has a left adjoint `π_!^{Ab}`.

Stacks 09CY asserts that `forget ∘ π_! = π_!^{Ab} ∘ forget`. This file proves it: the canonical
comparison `π_!^{Ab} ∘ forget ⟶ forget ∘ π_!` of Stacks 0798 is an isomorphism.

By the criterion of Stacks 0798,
`Stacks.SheafOfModules.isIso_lowerShriekForgetComparison_of_localizedStructureSheafComparison`, it
suffices that, for every object `U` of `C`, the comparison for the localized projection
`π_U : C/U ⥤ D/p(U)` is invertible at the structure sheaf `O_U`. By Stacks 08P9 the functor `π_U`
has a continuous right adjoint, the cartesian section `V ↦ V ×_{p(U)} U`, with invertible counit.
So restriction along `π_U` is fully faithful on abelian sheaves and on modules, both counits of
the lower-shriek adjunctions of `π_U` are invertible, and the comparison — compatible with the
counits like every adjoint mate — is invertible at every restricted module, in particular at
`O_U = π_U⁻¹ O_{p(U)}`, by
`Stacks.SheafOfModules.isIso_lowerShriekForgetComparison_app_unit_of_adjunction`.
This is where the fibred structure enters: for a general morphism of ringed sites the comparison
is not invertible (`Stacks.SheafOfModules.lowerShriekForget_not_isomorphic`).

## Main definitions

* `Stacks.Sites.FibredCategory.FibredCategorySituation.totalModuleRing`: `O_C = π⁻¹O_D`.
* `Stacks.Sites.FibredCategory.FibredCategorySituation.sheafModuleRestriction` and
  `.moduleLowerShriek`: `π^*` and `π_!` on sheaves of modules, with the adjunction
  `.moduleLowerShriekAdjunction`.
* `Stacks.Sites.FibredCategory.FibredCategorySituation.moduleLowerShriekForgetComparison`: the
  comparison `π_!^{Ab} ∘ forget ⟶ forget ∘ π_!` of Stacks 0798.
* `Stacks.Sites.FibredCategory.FibredCategorySituation.moduleLowerShriekForgetIso`: the resulting
  isomorphism `forget ∘ π_! ≅ π_!^{Ab} ∘ forget`.

## Main results

* `FibredCategorySituation.isIso_localizedStructureSheafComparison_baseModuleRing`: the
  canonical map `(π_U)_!^{Ab} O_U ⟶ O_{p(U)}` of Stacks 0798 is an isomorphism.
* `Stacks.Sites.FibredCategory.FibredCategorySituation.isIso_moduleLowerShriekForgetComparison`:
  **`forget ∘ π_! = π_!^{Ab} ∘ forget`**.
* `Stacks.Sites.FibredCategory.FibredCategorySituation.totalModuleRingIso`: `O_C` here is the
  structure sheaf of the ringed topos of Stacks 08P8, `totalRingedTopos`.

## Implementation notes

`O_C` is taken to be the restriction of `O_D` along `p`, as a sheaf of rings. The structure sheaf
`totalRingedTopos.O` of Stacks 08P8 is built instead by transporting ring operations along the
inverse image of sheaves of sets; the two are identified, with identity underlying sheaves of
sets, by `totalModuleRingIso`.

## References

* [Stacks Project, Tag 09CY](https://stacks.math.columbia.edu/tag/09CY)
* [Stacks Project, Tag 08PC](https://stacks.math.columbia.edu/tag/08PC)
* [Stacks Project, Tag 0798](https://stacks.math.columbia.edu/tag/0798)
* [Stacks Project, Tag 08P9](https://stacks.math.columbia.edu/tag/08P9)
* [Stacks Project, Tag 08P8](https://stacks.math.columbia.edu/tag/08P8)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace Stacks.Sites.FibredCategory.FibredCategorySituation

universe uD vD uC vC w

variable (s : FibredCategorySituation.{uD, vD, uC, vC, w})

/-- `O_D`, the structure sheaf of the base as a sheaf of rings, with its sections lifted to the
universe in which `π` is formed. -/
abbrev baseModuleRing : Sheaf s.base.J RingCat.{max w uD vD uC vC} :=
  Stacks.SheafOfModules.Tensor.ringSheaf s.baseRingedTopos.O

/-- `O_C = π⁻¹O_D`, the structure sheaf of the total category: the restriction along `p` of the
structure sheaf of the base, `π⁻¹` being restriction along `p`. -/
abbrev totalModuleRing : Sheaf s.topology RingCat.{max w uD vD uC vC} :=
  Stacks.SheafOfModules.inverseImageRing s.topology s.base.J s.p s.baseModuleRing

/-- `O_C` is the structure sheaf of the total ringed topos of Stacks 08P8: the inverse image of
`O_D` along `π`, formed by transporting the ring operations along the inverse image of sheaves of
sets, is the restriction of `O_D` along `p`, the comparison being the identity on underlying
sheaves of sets. -/
def totalModuleRingIso :
    Stacks.SheafOfModules.Tensor.ringSheaf s.totalRingedTopos.O ≅ s.totalModuleRing :=
  (sheafCompose s.topology
    (forget₂ CommRingCat.{max w uD vD uC vC} RingCat.{max w uD vD uC vC})).mapIso
    (Stacks.Sheaves.ToposPullback.restrictionCommRingIso s.topology s.base.J s.p
      s.liftedBaseSheaf)


/-- The localized projection `C/U ⥤ D/p(U)` is continuous (Stacks 08P9), for a fibred
category whose base, total category and coefficients have independent universes. -/
instance isContinuous_overPost_of_fibredCategorySituation
    (t : FibredCategorySituation.{uD, vD, uC, vC, w}) (U : t.C) :
    (Over.post (X := U) t.p).IsContinuous (t.topology.over U) (t.base.J.over (t.p.obj U)) :=
  (localizedProjectionSection t U).isContinuous

/-- Abelian sheaves on the total category can be weakly sheafified. Recorded so that instance
search does not try the generic instances, whose universes it cannot solve. -/
instance hasWeakSheafifyTopology :
    HasWeakSheafify s.topology AddCommGrpCat.{max w uD vD uC vC} :=
  @HasSheafify.isRightAdjoint _ _ _ _ _ s.hasSheafifyTopology

/-- Abelian sheaves on the base can be weakly sheafified. -/
instance hasWeakSheafifyBase :
    HasWeakSheafify s.base.J AddCommGrpCat.{max w uD vD uC vC} :=
  @HasSheafify.isRightAdjoint _ _ _ _ _ s.hasSheafifyBaseTopology

/-- Abelian sheaves on a slice of the total category can be sheafified. -/
instance hasSheafifyOver (U : s.C) :
    HasSheafify (s.topology.over U) AddCommGrpCat.{max w uD vD uC vC} :=
  hasSheafify_addCommGrpCat.{max uC vC, vC, max w uD vD uC vC} (s.topology.over U)

/-- Abelian sheaves on a slice of the base can be sheafified. -/
instance hasSheafifyBaseOver (V : s.base.C) :
    HasSheafify (s.base.J.over V) AddCommGrpCat.{max w uD vD uC vC} :=
  hasSheafify_addCommGrpCat.{max uD vD, vD, max w uD vD uC vC} (s.base.J.over V)

/-- On a slice of the total category the weak equivalences of abelian sheaves are the locally
bijective morphisms. -/
instance wEqualsLocallyBijectiveOver (U : s.C) :
    (s.topology.over U).WEqualsLocallyBijective AddCommGrpCat.{max w uD vD uC vC} :=
  Stacks.Cohomology.SiteModules.site_wEqualsLocallyBijective_addCommGrp.{max uC vC, vC,
    max w uD vD uC vC} (J := s.topology.over U)

/-- On a slice of the base the weak equivalences of abelian sheaves are the locally bijective
morphisms. -/
instance wEqualsLocallyBijectiveBaseOver (V : s.base.C) :
    (s.base.J.over V).WEqualsLocallyBijective AddCommGrpCat.{max w uD vD uC vC} :=
  Stacks.Cohomology.SiteModules.site_wEqualsLocallyBijective_addCommGrp.{max uD vD, vD,
    max w uD vD uC vC} (J := s.base.J.over V)

/-- `π^* : Mod(O_D) ⥤ Mod(O_C)`, restriction of sheaves of modules along `p`. -/
abbrev sheafModuleRestriction :
    SheafOfModules.{max w uD vD uC vC} s.baseModuleRing ⥤
      SheafOfModules.{max w uD vD uC vC} s.totalModuleRing :=
  Stacks.Cohomology.DerivedLowerShriek.restrictionModules s.topology s.base.J s.p
    s.baseModuleRing

/-- `π_! : Mod(O_C) ⥤ Mod(O_D)`, the lower-shriek functor on sheaves of modules: the left adjoint
of `π^*`. -/
abbrev moduleLowerShriek :
    SheafOfModules.{max w uD vD uC vC} s.totalModuleRing ⥤
      SheafOfModules.{max w uD vD uC vC} s.baseModuleRing :=
  Stacks.Cohomology.DerivedLowerShriek.lowerShriekModules s.topology s.base.J s.p
    s.baseModuleRing

/-- **Stacks 09CY, the module-level `π_!`.** The lower-shriek functor `π_!` on sheaves of modules
is left adjoint to `π^* = π⁻¹`, restriction of sheaves of modules along `p`. -/
@[stacks 09CY "the module-level `π_!` of Situation 08P8 and its adjunction `π_! ⊣ π^*`"]
def moduleLowerShriekAdjunction : s.moduleLowerShriek ⊣ s.sheafModuleRestriction :=
  Stacks.Cohomology.DerivedLowerShriek.adjunctionModules s.topology s.base.J s.p s.baseModuleRing

/-- The canonical comparison `π_!^{Ab} ∘ forget ⟶ forget ∘ π_!` of Stacks 0798: the adjoint
mate of the identity `forget ∘ π^* = π⁻¹ ∘ forget`. -/
abbrev moduleLowerShriekForgetComparison :
    SheafOfModules.toSheaf s.totalModuleRing ⋙ s.abelianLowerShriek ⟶
      s.moduleLowerShriek ⋙ SheafOfModules.toSheaf s.baseModuleRing :=
  Stacks.SheafOfModules.lowerShriekForgetComparison s.p
    (Stacks.SheafOfModules.structureMap s.topology s.base.J s.p s.baseModuleRing)

/-- **The canonical map `(π_U)_!^{Ab} O_U ⟶ O_{p(U)}` of Stacks 0798 is an isomorphism**, for
every object `U` of the total category. The localized projection `π_U : C/U ⥤ D/p(U)` has the
cartesian section of Stacks 08P9 as a continuous right adjoint with invertible counit, so
`Stacks.SheafOfModules.isIso_lowerShriekForgetComparison_app_unit_of_adjunction` applies, and
`π_U` carries the terminal object of `C/U` to that of `D/p(U)`, which makes
`(π_U)_! O_U ⟶ O_{p(U)}` invertible on modules. -/
theorem isIso_localizedStructureSheafComparison_baseModuleRing (U : s.C) :
    IsIso (Stacks.SheafOfModules.localizedStructureSheafComparison
      s.topology s.base.J s.p s.baseModuleRing U) := by
  have := (localizedProjectionSection s U).cartesianSection_isContinuous
  have : IsIso (localizedProjectionSection s U).cartesianSection_adjunction.counit := by
    rw [(localizedProjectionSection s U).cartesianSection_counit]
    infer_instance
  have := Stacks.SheafOfModules.isIso_lowerShriekForgetComparison_app_unit_of_adjunction
    (s.topology.over U) (s.base.J.over (s.p.obj U)) (Over.post (X := U) s.p)
    (s.baseModuleRing.over (s.p.obj U))
    (localizedProjectionSection s U).cartesianSection_adjunction
  exact IsIso.comp_isIso' this inferInstance

/-- **Stacks 09CY, `forget ∘ π_! = π_!^{Ab} ∘ forget`.** The canonical comparison
`π_!^{Ab} ∘ forget ⟶ forget ∘ π_!` of Stacks 0798 between lower shriek of abelian sheaves and
lower shriek of sheaves of modules, for the projection of a fibred category, is an isomorphism.

By the criterion of Stacks 0798 this reduces to the canonical maps
`(π_U)_!^{Ab} O_U ⟶ O_{p(U)}`, which are isomorphisms by
`isIso_localizedStructureSheafComparison_baseModuleRing`. This is Stacks 08PC part (2) in the
situation of the remark. -/
@[stacks 09CY "`forget ∘ π_! = π_!^{Ab} ∘ forget`: the canonical comparison of Stacks 0798 is \
an isomorphism"]
instance isIso_moduleLowerShriekForgetComparison :
    IsIso s.moduleLowerShriekForgetComparison :=
  Stacks.SheafOfModules.isIso_lowerShriekForgetComparison_of_localizedStructureSheafComparison.{w,
    uC, uD, vC, vD} s.topology s.base.J s.p s.baseModuleRing
    s.isIso_localizedStructureSheafComparison_baseModuleRing

/-- The isomorphism `forget ∘ π_! ≅ π_!^{Ab} ∘ forget`, inverse of the canonical comparison. -/
def moduleLowerShriekForgetIso :
    s.moduleLowerShriek ⋙ SheafOfModules.toSheaf s.baseModuleRing ≅
      SheafOfModules.toSheaf s.totalModuleRing ⋙ s.abelianLowerShriek :=
  (asIso s.moduleLowerShriekForgetComparison).symm

end Stacks.Sites.FibredCategory.FibredCategorySituation

end
