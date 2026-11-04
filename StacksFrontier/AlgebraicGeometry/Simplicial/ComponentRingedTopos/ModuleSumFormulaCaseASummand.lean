module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackModulesOfIsoStructureMap
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposModulePushforwardRestriction
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ModuleSumFormulaCaseA
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.TransitionRingFsharp
public import StacksFrontier.CategoryTheory.Adjunction.LeftAdjointUniqTranspose
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ModuleLowerShriekExactUnconditional

/-!
# The summand of the componentwise direct sum for modules, case (A)

Let `C` be a simplicial site — case (A) of the simplicial-site situation of Stacks 09WE — and
let `P` be a sheaf of commutative rings on its total site. Stacks 0D72 presents the restriction
to degree `m` of module lower shriek from degree `n` as the direct sum, over the simplex maps
`φ : [n] ⟶ [m]`, of the module pullbacks along the transitions `f_φ`, and this development
carries two readings of that summand. The formula is proved for the first,
`CategoryTheory.SimplicialSite.transitionModulePullbackA`, which is Mathlib's pullback of
sheaves of modules along the ring map `O(φ)` for the morphism of sites `u_φ`; it is consumed in
the second, `CategoryTheory.SimplicialSiteSituation.transitionPullbackModules`, which is the
pullback of sheaves of modules along the transition morphism of *ringed topoi*. This file
identifies them.

Both summands are left adjoints, so the comparison is made on the right adjoints, where it is
the generic statement of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/ToposModulePushforwardRestriction.lean` — the
direct image of modules along a morphism of ringed topoi whose direct image of sheaves of sets
is restriction along a continuous functor of sites is Mathlib's pushforward — together with the
identification of the two scalar maps, which is the whole arithmetic content and is carried out
below.

## Main definitions

* `CategoryTheory.SimplicialSite.transitionPushforwardModulesIsoA`: the comparison of the two
  right adjoints, `f_{φ*} ≅ SheafOfModules.pushforward O(φ)`.

## Main results

* `CategoryTheory.SimplicialSite.transitionPullbackModulesIsoA`: **the summand comparison.**
  The pullback of sheaves of modules along the transition morphism of ringed topoi of a simplex
  map is the pullback along the ring map `O(φ)`.
* `CategoryTheory.SimplicialSite.ringFsharp_comp_restrictionRingIso`: the direct-image form of
  the structure map of the transition morphism of ringed topoi is the ring map `O(φ)` of
  Stacks 0D72, the transported ring structure on the direct image being identified with the
  original one by `Stacks.Sheaves.ToposPullback.restrictionRingIso`.

The reading of the two forms of that structure map as the transitions of Stacks 09WF holds in
either case of the simplicial-site situation and is
`CategoryTheory.SimplicialSiteSituation.ringSheafMap_ringFsharp_transition`, in
`StacksFrontier/AlgebraicGeometry/Simplicial/ComponentRingedTopos/TransitionRingFsharp.lean`.

## Implementation notes

The ring-level identity is proved on underlying sheaves of sets, where
`CategoryTheory.sheafCompose _ (CategoryTheory.forget RingCat)` is faithful. There the
direct-image form of the transition's structure map is the direct-image transition of Stacks 09WF
by `CategoryTheory.SimplicialSiteSituation.ringSheafMap_ringFsharp_transition`, and in case (A)
that transition is, on sections, restriction along the cross-fibre arrow `(φ, 𝟙)`
(`restrictTransition_inl_app`), which is exactly the ring map `O(φ)` on sections. The second step
is `rfl` on sections and the rest is `Eq.trans` and `congrArg`.

Nothing here is rewritten with `rw`. The two spellings of the degree-`n` component topology —
`(componentRingedTopos P n).J`, which the morphism of ringed topoi uses, and
`componentTopology n`, which the morphism of sites uses — are equal by `Eq.refl`, but a rewrite
across them cannot place its motive, exactly as recorded in the implementation notes of
`StacksFrontier/AlgebraicGeometry/Simplicial/ComponentRingedTopos/ComponentPullbackRestriction.lean`.
For the same reason the implicit site arguments of `CategoryTheory.SheafOfModules.pushforward`
and `…pushforwardCongr` are given by name: without that they are still metavariables when the
continuity instance is sought, and instance search cannot assign a metavariable it did not
create.

The two scalar maps are compared through the unit form of the structure map (`ringFsharp_eq`,
which is `CategoryTheory.Adjunction.homEquiv_unit` for the ring-level adjunction) and the
naturality of `restrictionRingIso` in the sheaf of rings; that is what turns the composite scalar
map of the generic comparison into the direct-image form of the structure map followed by a
single ring-level identification.

## References

* [Stacks Project, Tag 09WE](https://stacks.math.columbia.edu/tag/09WE)
* [Stacks Project, Tag 09WF](https://stacks.math.columbia.edu/tag/09WF)
* [Stacks Project, Tag 0D72](https://stacks.math.columbia.edu/tag/0D72)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward
open Stacks.Sheaves.RingedToposModules
open Stacks.SheafOfModules.RestrictRan

universe u

namespace CategoryTheory.SimplicialSite

variable (C : SimplicialSite.{u}) {n m : SimplexCategory}
  (P : Sheaf (situation C).totalTopology CommRingCat.{u})

/-- **In case (A) the ring map `O(φ)` is the direct-image transition of Stacks 09WF.** On
underlying sheaves of sets both are restriction along the cross-fibre arrow `(φ, 𝟙)`, so the
identification holds on sections by definition. -/
theorem ringSheafMap_ringTransitionA (φ : n ⟶ m) :
    (sheafCompose ((situation C).componentTopology n) (forget RingCat.{u})).map
        (ringTransitionA C
          ((Stacks.SheafOfModules.Tensor.ringSheaf (J := (situation C).totalTopology) P)) φ) =
      ((situation C).restrictTransition φ).app
        ((sheafCompose (situation C).totalTopology (forget CommRingCat.{u})).obj P) :=
  Sheaf.hom_ext_sections fun _ _ ↦ rfl

/-- **The direct-image form of the structure map of the transition is the ring map `O(φ)` of
Stacks 0D72.** The direct image of the structure sheaf carries a transported ring structure; read
through the identification of that structure with the original one, the structure map is the ring
map along which the case-(A) summand is taken. -/
theorem ringFsharp_comp_restrictionRingIso (φ : n ⟶ m) :
    ((situation C).transitionRingedToposHom P φ).ringFsharp ≫
        (restrictionRingIso ((situation C).componentTopology n)
          ((situation C).componentTopology m) (transitionFunctorA C φ)
          (Stacks.SheafOfModules.Tensor.ringSheaf ((situation C).componentRingedTopos P m).O)).hom =
      ringTransitionA C
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := (situation C).totalTopology) P)) φ :=
  (sheafCompose ((situation C).componentTopology n) (forget RingCat.{u})).map_injective
    (((sheafCompose ((situation C).componentTopology n)
          (forget RingCat.{u})).map_comp _ _).trans
      ((congrArg
            (fun g ↦ (sheafCompose ((situation C).componentTopology n)
                (forget RingCat.{u})).map
                ((situation C).transitionRingedToposHom P φ).ringFsharp ≫ g)
            (restrictionRingIso_hom_ringSheafMap ((situation C).componentTopology n)
              ((situation C).componentTopology m) (transitionFunctorA C φ)
              (Stacks.SheafOfModules.Tensor.ringSheaf
                ((situation C).componentRingedTopos P m).O))).trans
        ((Category.comp_id _).trans
          (((situation C).ringSheafMap_ringFsharp_transition P φ).trans
            (ringSheafMap_ringTransitionA C P φ).symm))))

/-- The direct-image form of the structure map, written through the unit of the ring-level
adjunction: this is the shape in which it meets the composite scalar map of the generic
comparison. -/
theorem ringFsharp_eq (φ : n ⟶ m) :
    ((situation C).transitionRingedToposHom P φ).ringFsharp =
      ringUnit ((situation C).transitionRingedToposHom P φ).toToposHom
          (Stacks.SheafOfModules.Tensor.ringSheaf ((situation C).componentRingedTopos P n).O) ≫
        pullbackRingSheafMap ((situation C).componentTopology n)
          ((transitionFunctorA C φ).sheafPushforwardContinuous (Type u)
            ((situation C).componentTopology n) ((situation C).componentTopology m))
          ((situation C).transitionRingedToposHom P φ).ringFsharpInverseImage :=
  Adjunction.homEquiv_unit _ _ _ _

/-- **The scalar map of the generic comparison is the case-(A) ring map `O(φ)`.** The unit at the
level of sheaves of rings, the identification of the transported ring structure with the original
one, and the direct image of the inverse-image form of the structure map compose to the
direct-image form of the structure map followed by that identification, which is `O(φ)`. -/
theorem restrictionPushforwardRingMap_eq (φ : n ⟶ m) :
    restrictionPushforwardRingMap ((situation C).componentTopology n)
        ((situation C).componentTopology m) (transitionFunctorA C φ) _ _
        ((situation C).transitionRingedToposHom P φ).toModulesHom.fSharpInverseImage
        _
        (ringUnit ((situation C).transitionRingedToposHom P φ).toToposHom
          (Stacks.SheafOfModules.Tensor.ringSheaf ((situation C).componentRingedTopos P n).O)) =
      ringTransitionA C
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := (situation C).totalTopology) P)) φ := by
  have hnat := restrictionRingIso_naturality ((situation C).componentTopology n)
      ((situation C).componentTopology m) (transitionFunctorA C φ)
      ((situation C).transitionRingedToposHom P φ).ringFsharpInverseImage
  refine Eq.trans (congrArg
    (fun d ↦ restrictionPushforwardRingMap ((situation C).componentTopology n)
      ((situation C).componentTopology m) (transitionFunctorA C φ) _ _ d _
      (ringUnit ((situation C).transitionRingedToposHom P φ).toToposHom
        (Stacks.SheafOfModules.Tensor.ringSheaf ((situation C).componentRingedTopos P n).O)))
    (AlgebraicGeometry.RingedToposHom.forgetCommRingSheaf_map_fSharpInverseImage
      ((situation C).transitionRingedToposHom P φ)).symm) ?_
  exact (congrArg
        (fun g ↦ ringUnit ((situation C).transitionRingedToposHom P φ).toToposHom
          (Stacks.SheafOfModules.Tensor.ringSheaf
            ((situation C).componentRingedTopos P n).O) ≫ g) hnat.symm).trans
    ((Category.assoc _ _ _).symm.trans
      ((congrArg (fun g ↦ g ≫ _) (ringFsharp_eq C P φ).symm).trans
        (ringFsharp_comp_restrictionRingIso C P φ)))

/-- **The direct image of sheaves of modules along the transition morphism of ringed topoi is
Mathlib's pushforward along the ring map `O(φ)`.** In case (A) the direct image of sheaves of
sets of the transition is restriction along the morphism of sites `u_φ` — it is the defining
field of `CategoryTheory.Functor.IsMorphismOfSites.morphismOfTopoi` — so the generic comparison
applies, and its scalar map is `O(φ)`.

The direct image is taken at the reading `AlgebraicGeometry.RingedToposHom.toModulesHom` of the
morphism of ringed topoi, not at
`AlgebraicGeometry.RingedToposHom.toRingedToposModulesHom`. That is deliberate and is the whole
reason the leg equation of Stacks 0D72 (6) can be assembled: it is the reading that
`AlgebraicGeometry.RingedToposHom.pullbackAdjPushforwardModules` is defined at, so no transport
across the two readings has to be crossed downstream. See the docstring of
`CategoryTheory.SimplicialSite.transitionRingedToposPushforwardModulesIsoA`. -/
def transitionPushforwardModulesIsoA (φ : n ⟶ m) :
    SheafOfModules.pushforward.{u}
        (J := (situation C).componentTopology n) (K := (situation C).componentTopology m)
        (ringTransitionA C
          ((Stacks.SheafOfModules.Tensor.ringSheaf (J := (situation C).totalTopology) P)) φ) ≅
      pushforwardModules (X := (situation C).componentRingedTopos P m)
        (Y := (situation C).componentRingedTopos P n)
        ((situation C).transitionRingedToposHom P φ).toModulesHom :=
  (SheafOfModules.pushforwardCongr (J := (situation C).componentTopology n)
        (K := (situation C).componentTopology m)
        (restrictionPushforwardRingMap_eq C P φ)).symm ≪≫
    (pushforwardRestrictionModulesIso ((situation C).componentTopology n)
      ((situation C).componentTopology m) (transitionFunctorA C φ) _ _
      ((situation C).transitionRingedToposHom P φ).toModulesHom.fSharpInverseImage
      _
      (ringUnit ((situation C).transitionRingedToposHom P φ).toToposHom
        (Stacks.SheafOfModules.Tensor.ringSheaf ((situation C).componentRingedTopos P n).O))).symm

/-- **The comparison of the two direct images along a transition of Stacks 09WF in case (A).**
The direct image of sheaves of modules along the ring map `O(φ)`, which is the right adjoint of
the summand of the case-(A) direct-sum formula, is the direct image along the transition morphism
of ringed topoi, which is the right adjoint of the summand
`CategoryTheory.SimplicialSiteSituation.transitionPullbackModules` that Stacks 0D74 consumes.

Two comparisons separate them and this assembles both: the comparison
`CategoryTheory.SimplicialSite.transitionPushforwardModulesIsoA` of the right adjoints, and the
comparison `AlgebraicGeometry.RingedToposHom.toModulesPushforwardIso` of the modules
development's direct image with `AlgebraicGeometry.RingedToposHom.pushforwardModules`. Each is
the identity on a module of sections, *by `Eq.refl`*, and that is what makes the comparison factor
of the leg equation reachable; the leg equation of Stacks 0D72 (6) in case (A),
`CategoryTheory.SimplicialSite.moduleSumFormulaLegEqA`, rests on it.

There used to be a third factor between them: the transport `eqToIso` of
`AlgebraicGeometry.RingedToposHom.pushforwardModules_toRingedToposModulesHom` across the two
readings `AlgebraicGeometry.RingedToposHom.toRingedToposModulesHom` and
`AlgebraicGeometry.RingedToposHom.toModulesHom` of a morphism of ringed topoi as the four-field
datum of the modules development, because
`CategoryTheory.SimplicialSite.transitionPushforwardModulesIsoA` was built at the first reading.
That factor is *not* the identity on underlying sheaves of sets in any usable sense: comparing its
source and target there is a kernel deterministic timeout, so `CategoryTheory.eqToHom_refl` does
not apply to it, and with it present the comparison factor of the leg equation cannot be read on a
section at all. It is gone because the comparison is now built at the *second* reading, which is
the one `AlgebraicGeometry.RingedToposHom.pullbackAdjPushforwardModules` is defined at; the cost
of moving it is one `congrArg` over
`AlgebraicGeometry.RingedToposHom.forgetCommRingSheaf_map_fSharpInverseImage`, an equality of
morphisms of sheaves of rings, inside
`CategoryTheory.SimplicialSite.restrictionPushforwardRingMap_eq`. -/
def transitionRingedToposPushforwardModulesIsoA (φ : n ⟶ m) :
    SheafOfModules.pushforward.{u}
        (J := (situation C).componentTopology n) (K := (situation C).componentTopology m)
        (ringTransitionA C
          ((Stacks.SheafOfModules.Tensor.ringSheaf (J := (situation C).totalTopology) P)) φ) ≅
      ((situation C).transitionRingedToposHom P φ).pushforwardModules :=
  transitionPushforwardModulesIsoA C P φ ≪≫
    ((situation C).transitionRingedToposHom P φ).toModulesPushforwardIso

/-- **The summand comparison of Stacks 0D72 in case (A).** The pullback of sheaves of modules
along the transition morphism of ringed topoi of a simplex map `φ : [n] ⟶ [m]` is the pullback
of sheaves of modules along the ring map `O(φ)` for the morphism of sites `u_φ`.

Both are left adjoints — the first by Stacks 03D7 for the two-field morphism of ringed topoi,
the second by construction — and their right adjoints are identified by
`CategoryTheory.SimplicialSite.transitionRingedToposPushforwardModulesIsoA`, so uniqueness of
left adjoints gives the comparison. This is what turns the direct-sum formula
`CategoryTheory.SimplicialSite.componentModuleSumFormulaA` into the formula that Stacks 0D74 and
Stacks 0D75 consume.

The Stacks 03D7 adjunction taken here is the one of the *two-field* morphism of ringed topoi,
`AlgebraicGeometry.RingedToposHom.pullbackAdjPushforwardModules`, whose left adjoint already *is*
the summand `CategoryTheory.SimplicialSiteSituation.transitionPullbackModules`. Taking instead
the adjunction of the modules development at
`AlgebraicGeometry.RingedToposHom.toRingedToposModulesHom` — the other reading of the morphism —
leaves a `CategoryTheory.eqToIso` in front of the comparison, and that transport cannot be
cancelled downstream at any price: the two readings agree only propositionally, so a definitional
comparison which reaches them does not terminate. The implementation notes of
`StacksFrontier/AlgebraicGeometry/Simplicial/ComponentRingedTopos/ModuleSumFormulaLegCaseB.lean`
record the measurements. -/
def transitionPullbackModulesIsoA (φ : n ⟶ m) :
    (situation C).transitionPullbackModules' P φ ≅
      transitionModulePullbackA C
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := (situation C).totalTopology) P)) φ :=
  Adjunction.leftAdjointUniq
    (((situation C).transitionRingedToposHom P φ).pullbackAdjPushforwardModules.ofNatIsoRight
      (transitionRingedToposPushforwardModulesIsoA C P φ).symm)
    (SheafOfModules.pullbackPushforwardAdjunction.{u}
      (ringTransitionA C
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := (situation C).totalTopology) P)) φ))

/-- `CategoryTheory.SimplicialSite.transitionPullbackModulesIsoA` is, by definition, the
comparison of the two left adjoints of the two Stacks 03D7 adjunctions it is built from.

This records the definition as a *propositional* equality so that a consumer never has to unfold
it inside a larger type. Proving it costs one `δ`-step against the definition's own expected
type, which is where that step is affordable; forcing the same step while elaborating the
transposition identity below is not, and that is what
`CategoryTheory.SimplicialSite.homEquiv_transitionPullbackModulesIsoA_hom_app_comp` uses this
for. -/
theorem transitionPullbackModulesIsoA_eq (φ : n ⟶ m) :
    transitionPullbackModulesIsoA C P φ =
      Adjunction.leftAdjointUniq
        (((situation C).transitionRingedToposHom P φ).pullbackAdjPushforwardModules.ofNatIsoRight
          (transitionRingedToposPushforwardModulesIsoA C P φ).symm)
        (SheafOfModules.pullbackPushforwardAdjunction.{u}
          (ringTransitionA C
            ((Stacks.SheafOfModules.Tensor.ringSheaf (J := (situation C).totalTopology) P)) φ)) :=
  rfl

/-- **The summand comparison of case (A) transposes away: Stacks 0D72 (6), the step that moves a
transposition between the two readings of the summand.** Transposing the summand comparison
`CategoryTheory.SimplicialSite.transitionPullbackModulesIsoA`, followed by a morphism out of the
case-(A) summand, along the Stacks 03D7 adjunction of the transition morphism of ringed topoi is
transposing that morphism along the case-(A) summand's own adjunction and applying the comparison
`CategoryTheory.SimplicialSite.transitionRingedToposPushforwardModulesIsoA` of the two right
adjoints afterwards.

The content is
`CategoryTheory.Adjunction.homEquiv_leftAdjointUniq_ofNatIsoRight_symm_hom_app_comp` at the two
adjunctions the summand comparison is built from. What takes arranging is the *shape*, and the
two steps below are not interchangeable with writing the identity out directly.

Elaborating this statement with the comparison replaced by its definition — a
`CategoryTheory.Adjunction.leftAdjointUniq` standing under the hom-set bijection of the
Stacks 03D7 adjunction — exhausts the heartbeat budget, and it does so whether the
`CategoryTheory.Adjunction.ofNatIsoRight` is named or the comparison is left as the definition to
be unfolded. The same identity *built upwards*, by instantiating the general lemma and letting
its type be inferred, costs under a second. So the obstruction is not the identity and not the
two adjunctions: it is that the elaborator cannot drive this type top-down, because projecting
`CategoryTheory.Iso.hom` out of a `…leftAdjointUniq` under an expected type asks it to reduce
that comparison to a structure, and reducing it reaches the two adjunctions' data.

So the comparison is kept opaque. The general lemma is applied in the form that takes it as a
variable together with
`CategoryTheory.SimplicialSite.transitionPullbackModulesIsoA_eq`, the equation identifying it;
the type of the application is then this statement already, syntactically, and nothing is
unfolded inside a type at any point. -/
theorem homEquiv_transitionPullbackModulesIsoA_hom_app_comp (φ : n ⟶ m)
    (X : _root_.SheafOfModules.{u} ((situation C).componentRingSheaf
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := (situation C).totalTopology) P)) n))
    (T : _root_.SheafOfModules.{u} ((situation C).componentRingSheaf
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := (situation C).totalTopology) P)) m))
    (k : (transitionModulePullbackA C
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (J := (situation C).totalTopology) P)) φ).obj X ⟶ T) :
    ((situation C).transitionRingedToposHom P φ).pullbackAdjPushforwardModules.homEquiv X T
        ((transitionPullbackModulesIsoA C P φ).hom.app X ≫ k) =
      (SheafOfModules.pullbackPushforwardAdjunction.{u}
            (ringTransitionA C
              ((Stacks.SheafOfModules.Tensor.ringSheaf
                (J := (situation C).totalTopology) P)) φ)).homEquiv X T
          k ≫
        (transitionRingedToposPushforwardModulesIsoA C P φ).hom.app T :=
  Adjunction.homEquiv_eq_of_eq_leftAdjointUniq_ofNatIsoRight_symm
    ((situation C).transitionRingedToposHom P φ).pullbackAdjPushforwardModules
    (SheafOfModules.pullbackPushforwardAdjunction.{u}
      (ringTransitionA C
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := (situation C).totalTopology) P)) φ))
    (transitionRingedToposPushforwardModulesIsoA C P φ)
    (transitionPullbackModulesIsoA C P φ) (transitionPullbackModulesIsoA_eq C P φ) k

end CategoryTheory.SimplicialSite

end
