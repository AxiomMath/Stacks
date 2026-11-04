module

public import StacksFrontier.AlgebraicGeometry.RelativeDifferentialStalk.Stalk
import StacksCore.Tactic.StacksAttribute

/-!
# From the sectionwise presheaf to the sheaf of relative differentials, on stalks

The sheaf of relative differentials of a morphism `φ` of sheaves of commutative rings is, by
`AlgebraicGeometry.SheafOfModules.moduleOfDifferentialsIsoSectionwise`, the sheafification of the
presheaf of sectionwise Kähler differentials.  **This file shows that passing from that presheaf
to its sheafification does not change the stalk**, which transports the computation of
`StacksFrontier.AlgebraicGeometry.RelativeDifferentialStalk.Stalk` from the presheaf to the sheaf.

## Main results

* `Stacks.RelativeDifferentialStalk.toPresheaf_map_toSectionwiseDifferentialsSheaf`: the morphism
  of presheaves of abelian groups underlying the unit of sheafification
  `AlgebraicGeometry.SheafOfModules.toSectionwiseDifferentialsSheaf` *is* the unit of
  sheafification of presheaves of abelian groups.  This holds by `rfl`.
* `Stacks.RelativeDifferentialStalk.isIso_stalkFunctor_map_toSectionwiseDifferentialsSheaf`: that
  morphism therefore induces an isomorphism on every stalk.

## Implementation notes

The first result is Mathlib's
`PresheafOfModules.toPresheaf_map_sheafificationHomEquiv_def`, which is itself stated as `rfl`:
the unit of `PresheafOfModules.sheafificationAdjunction` at `P` is, on underlying presheaves of
abelian groups, `CategoryTheory.toSheafify` at `P.presheaf` composed with the identity.  The
second is then Mathlib's `TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso`, which says the
stalk functor inverts the unit of sheafification because both it and its composite with
sheafification are left adjoint to the skyscraper functor.

The `HasSheafify` instance has to be named, and named identically to the way
`AlgebraicGeometry.SheafOfModules.sectionwiseDifferentialsSheaf` names it, or the statement is
about a different sheafification functor and does not typecheck against it.  That is why
`hasSheafifyEssentiallySmallSite` appears in every statement below rather than being left to
instance search.

## References

* [Stacks Project, Tag 08TE](https://stacks.math.columbia.edu/tag/08TE)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry AlgebraicGeometry.SheafOfModules PresheafOfModules

universe u

namespace Stacks.RelativeDifferentialStalk

variable {X : TopCat.{u}} {O₁ O₂ : TopCat.Sheaf CommRingCat.{u} X} (φ : O₁ ⟶ O₂)

/-- **The unit of sheafification of the presheaf of sectionwise differentials is, on underlying
presheaves of abelian groups, the unit of sheafification of presheaves of abelian groups.** -/
public theorem toPresheaf_map_toSectionwiseDifferentialsSheaf :
    letI : HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
      hasSheafifyEssentiallySmallSite.{_, _, _, _, u} _ _
    (PresheafOfModules.toPresheaf _).map (toSectionwiseDifferentialsSheaf.{u, u} φ) =
      CategoryTheory.toSheafify (Opens.grothendieckTopology X)
        (DifferentialsConstruction.relativeDifferentials' φ.hom).presheaf :=
  rfl

/-- **Sheafifying the presheaf of sectionwise differentials does not change its stalks.** -/
public theorem isIso_stalkFunctor_map_toSectionwiseDifferentialsSheaf (x : X) :
    letI : HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
      hasSheafifyEssentiallySmallSite.{_, _, _, _, u} _ _
    IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      ((PresheafOfModules.toPresheaf _).map (toSectionwiseDifferentialsSheaf.{u, u} φ))) := by
  let : HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
    hasSheafifyEssentiallySmallSite.{_, _, _, _, u} _ _
  rw [toPresheaf_map_toSectionwiseDifferentialsSheaf φ]
  exact TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat.{u}
    (DifferentialsConstruction.relativeDifferentials' φ.hom).presheaf

/-- A morphism of presheaves of modules whose induced map of stalks at `x` is an isomorphism
gives a linear equivalence of those stalks over the stalk of the ring presheaf. -/
public noncomputable def stalkLinearEquivOfIsIso {R : X.Presheaf CommRingCat.{u}}
    (M N : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)) (f : M ⟶ N) (x : X)
    (h : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      ((PresheafOfModules.toPresheaf _).map f))) :
    ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) M.presheaf x)
      ≃ₗ[ToType (R.stalk x)]
      ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) N.presheaf x) :=
  letI := h
  LinearEquiv.ofBijective (presheafModuleStalkLinearMapCommRing M N f x)
    (ConcreteCategory.bijective_of_isIso
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        ((PresheafOfModules.toPresheaf _).map f)))

/-- The stalk of the sheafification of the presheaf of sectionwise differentials is a module over
the stalk of `O₂`.  This is the module structure of `Mathlib.Algebra.Category.ModuleCat.Stalk`,
recorded at the spelling of the ring sheaf that `sectionwiseDifferentialsSheaf` carries: instance
search does not identify `AlgebraicGeometry.SheafOfModules.underlyingRingSheaf O₂` with the
composition of `O₂` with the forgetful functor to rings on its own. -/
public noncomputable instance moduleStalkSectionwiseDifferentialsSheaf (x : X) :
    Module (ToType (O₂.presheaf.stalk x))
      (ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        (sectionwiseDifferentialsSheaf.{u, u} φ).val.presheaf x)) :=
  inferInstanceAs (Module (ToType (O₂.presheaf.stalk x))
    (ToType (TopCat.Presheaf.stalk
      (show PresheafOfModules.{u} (O₂.presheaf ⋙ forget₂ CommRingCat RingCat) from
        (sectionwiseDifferentialsSheaf.{u, u} φ).val).presheaf x)))

/-- The stalk of the presheaf of sectionwise differentials, identified with the stalk of its
sheafification. -/
public noncomputable def stalkSectionwiseLinearEquiv (x : X) :
    letI : HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
      hasSheafifyEssentiallySmallSite.{_, _, _, _, u} _ _
    ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        (DifferentialsConstruction.relativeDifferentials' φ.hom).presheaf x)
      ≃ₗ[ToType (O₂.presheaf.stalk x)]
      ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        (sectionwiseDifferentialsSheaf.{u, u} φ).val.presheaf x) := by
  letI : HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
    hasSheafifyEssentiallySmallSite.{_, _, _, _, u} _ _
  exact stalkLinearEquivOfIsIso (R := O₂.presheaf) _ _ (toSectionwiseDifferentialsSheaf.{u, u} φ) x
    (isIso_stalkFunctor_map_toSectionwiseDifferentialsSheaf φ x)

/-- The canonical comparison of the sheaf of relative differentials with the sheafification of
the sectionwise differentials induces an isomorphism on stalks, being an isomorphism. -/
public theorem isIso_stalkFunctor_map_moduleOfDifferentialsIsoSectionwise (x : X) :
    IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      ((PresheafOfModules.toPresheaf (underlyingRingSheaf O₂).presheaf).map
        ((_root_.SheafOfModules.forget (underlyingRingSheaf O₂)).map
          (moduleOfDifferentialsIsoSectionwise.{u, u} φ).hom))) :=
  inferInstance

/-- The stalk of the sheaf of relative differentials, identified with the stalk of the
sheafification of the presheaf of sectionwise differentials. -/
public noncomputable def stalkModuleOfDifferentialsLinearEquiv (x : X) :
    ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        (moduleOfDifferentials.{u, u, u} φ).val.presheaf x)
      ≃ₗ[ToType (O₂.presheaf.stalk x)]
      ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        (sectionwiseDifferentialsSheaf.{u, u} φ).val.presheaf x) :=
  stalkLinearEquivOfIsIso (R := O₂.presheaf) _ _
    ((_root_.SheafOfModules.forget (underlyingRingSheaf O₂)).map
      (moduleOfDifferentialsIsoSectionwise.{u, u} φ).hom) x
    (isIso_stalkFunctor_map_moduleOfDifferentialsIsoSectionwise φ x)

/-- **Stacks Project, Tag 08TE.** The stalk of the sheaf of relative differentials of a
morphism of sheaves of commutative rings is the module of Kähler differentials of its stalk
map: `Ω_{O₂/O₁, x} = Ω_{O₂,x / O₁,x}`.

It is also Stacks Tag 01V0 at a point: the sheaf of relative differentials commutes with taking
stalks. -/
@[stacks 08TE "the identification"]
public noncomputable def stalkModuleOfDifferentialsKaehlerLinearEquiv (x : X)
    [DecidableEq (OrderDual (TopologicalSpace.OpenNhds x))] :
    letI := algebraStalk φ.hom x
    ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        (moduleOfDifferentials.{u, u, u} φ).val.presheaf x)
      ≃ₗ[ToType (O₂.presheaf.stalk x)]
      KaehlerDifferential (ToType (O₁.presheaf.stalk x)) (ToType (O₂.presheaf.stalk x)) := by
  letI := algebraStalk φ.hom x
  exact
    ((stalkModuleOfDifferentialsLinearEquiv φ x).trans
      (stalkSectionwiseLinearEquiv φ x).symm).trans (stalkLinearEquiv φ.hom x)

/-- The linear equivalence of stalks attached to a stalkwise isomorphism of presheaves of modules
carries the germ of a section to the germ of its image. -/
public theorem stalkLinearEquivOfIsIso_germ {R : X.Presheaf CommRingCat.{u}}
    (M N : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)) (f : M ⟶ N) (x : X)
    (h : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      ((PresheafOfModules.toPresheaf _).map f)))
    (U : Opens X) (hx : x ∈ U) (m : M.obj (op U)) :
    stalkLinearEquivOfIsIso M N f x h
        (TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) M.presheaf U x hx m) =
      TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) N.presheaf U x hx ((f.app (op U)).hom m) :=
  presheafModuleStalkLinearMapCommRing_germ M N f x U hx m

/-- The identification of the stalk of the presheaf of sectionwise differentials with the stalk of
its sheafification carries the germ of a section to the germ of its image under the unit of
sheafification. -/
public theorem stalkSectionwiseLinearEquiv_germ (x : X) (U : Opens X) (hx : x ∈ U)
    (m : (DifferentialsConstruction.relativeDifferentials' φ.hom).obj (op U)) :
    stalkSectionwiseLinearEquiv φ x
        (TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
          (DifferentialsConstruction.relativeDifferentials' φ.hom).presheaf U x hx m) =
      TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
        (sectionwiseDifferentialsSheaf.{u, u} φ).val.presheaf U x hx
        (((toSectionwiseDifferentialsSheaf.{u, u} φ).app (op U)).hom m) :=
  stalkLinearEquivOfIsIso_germ (R := O₂.presheaf) _ _ _ x
    (isIso_stalkFunctor_map_toSectionwiseDifferentialsSheaf φ x) U hx m

/-- The identification of the stalk of the sheaf of relative differentials with the stalk of the
sheafified sectionwise differentials carries the germ of a section to the germ of its image under
`AlgebraicGeometry.SheafOfModules.moduleOfDifferentialsIsoSectionwise`. -/
public theorem stalkModuleOfDifferentialsLinearEquiv_germ (x : X) (U : Opens X) (hx : x ∈ U)
    (m : (moduleOfDifferentials.{u, u, u} φ).val.obj (op U)) :
    stalkModuleOfDifferentialsLinearEquiv φ x
        (TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
          (moduleOfDifferentials.{u, u, u} φ).val.presheaf U x hx m) =
      TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
        (sectionwiseDifferentialsSheaf.{u, u} φ).val.presheaf U x hx
        (((moduleOfDifferentialsIsoSectionwise.{u, u} φ).hom.val.app (op U)).hom m) :=
  stalkLinearEquivOfIsIso_germ (R := O₂.presheaf) _ _ _ x
    (isIso_stalkFunctor_map_moduleOfDifferentialsIsoSectionwise φ x) U hx m

/-- `Stacks.RelativeDifferentialStalk.stalkModuleOfDifferentialsKaehlerLinearEquiv` is the
composite of its three constituents. -/
public theorem stalkModuleOfDifferentialsKaehlerLinearEquiv_apply (x : X)
    [DecidableEq (OrderDual (TopologicalSpace.OpenNhds x))]
    (m : ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
      (moduleOfDifferentials.{u, u, u} φ).val.presheaf x)) :
    letI := algebraStalk φ.hom x
    stalkModuleOfDifferentialsKaehlerLinearEquiv φ x m =
      stalkLinearEquiv φ.hom x
        ((stalkSectionwiseLinearEquiv φ x).symm
          (stalkModuleOfDifferentialsLinearEquiv φ x m)) :=
  rfl

/-- **Stacks Project, Tag 08TE.** The identification of the stalk of the sheaf of relative
differentials with the Kähler differentials of the stalk map carries universal differentials to
universal differentials.

The germ at `x` of the universal relative differential of a section of `O₂` over a neighbourhood
of `x` goes to the universal differential of the germ of that section. This is what makes the
identification canonical. -/
@[stacks 08TE "compatibility with the universal derivations"]
public theorem stalkModuleOfDifferentialsKaehlerLinearEquiv_germ_d (x : X)
    [DecidableEq (OrderDual (TopologicalSpace.OpenNhds x))]
    (i : OrderDual (TopologicalSpace.OpenNhds x)) (a : nhdRing O₂.presheaf i) :
    letI := algebraStalk φ.hom x
    stalkModuleOfDifferentialsKaehlerLinearEquiv φ x
        (TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
          (moduleOfDifferentials.{u, u, u} φ).val.presheaf (nhdOpen i) x (mem_nhdOpen i)
          ((universalDerivation.{u, u, u} φ).d a)) =
      KaehlerDifferential.D (ToType (O₁.presheaf.stalk x)) (ToType (O₂.presheaf.stalk x))
        (O₂.presheaf.germ (nhdOpen i) x (mem_nhdOpen i) a) := by
  let := algebraStalk φ.hom x
  have hfwd : stalkSectionwiseLinearEquiv φ x
        (TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
          (DifferentialsConstruction.relativeDifferentials' φ.hom).presheaf (nhdOpen i) x
          (mem_nhdOpen i) ((DifferentialsConstruction.derivation' φ.hom).d a)) =
      stalkModuleOfDifferentialsLinearEquiv φ x
        (TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
          (moduleOfDifferentials.{u, u, u} φ).val.presheaf (nhdOpen i) x (mem_nhdOpen i)
          ((universalDerivation.{u, u, u} φ).d a)) := by
    rw [stalkSectionwiseLinearEquiv_germ, stalkModuleOfDifferentialsLinearEquiv_germ]
    exact congrArg
      (fun z => TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
        (sectionwiseDifferentialsSheaf.{u, u} φ).val.presheaf (nhdOpen i) x (mem_nhdOpen i) z)
      (moduleOfDifferentialsIsoSectionwise_hom_app_d.{u, u} φ (op (nhdOpen i)) a).symm
  rw [stalkModuleOfDifferentialsKaehlerLinearEquiv_apply, ← hfwd, LinearEquiv.symm_apply_apply]
  exact stalkLinearEquiv_germ_D φ.hom x i a

end Stacks.RelativeDifferentialStalk

end
