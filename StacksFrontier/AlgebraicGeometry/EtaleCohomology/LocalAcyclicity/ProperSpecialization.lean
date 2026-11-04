module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocalAcyclicity.LocallyConstantCoefficients
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocalAcyclicity.ProperCospecialization
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleDerivedSectionsRestrictionComp
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SpecializationMapAndFibres

/-!
# The specialization map of a proper morphism

Let `f : X ⟶ S` be a proper morphism of schemes, `s` a geometric point of `S`, `t` a geometric
point of `Spec 𝒪^{sh}_{S,s}` and `t'` its image in `S`. For a bounded below object `K` of
`D(X_étale)` with torsion cohomology sheaves, relative to which `f` is locally acyclic, the
specialization map

`sp : (Rf_*K)_s ⟶ (Rf_*K)_{t'}`

is an isomorphism, and so is the cospecialization map. The results take the proper base change
theorem and the stalk formula `DerivedPushforwardStalkFormula` as hypotheses.

Here `Y = X ×_S Spec 𝒪^{sh}_{S,s}`, `X_t` is the fibre of `Y` over `t`, `h : X_t ⟶ Y` is its
inclusion and `β_{K,s,t}` is the cospecialization unit `cospecializationUnit`.

## Main results

* `AlgebraicGeometry.geometricFibreIsoCospecializationFibre` — the geometric fibre of `f` at
  `t'` is the fibre of `Y ⟶ Spec 𝒪^{sh}_{S,s}` over `t`, compatibly with the morphisms to `Y`.
* `AlgebraicGeometry.isIso_restriction_cospecializationFibre_iff` — pullback of derived sections
  along `h : X_t ⟶ Y` is invertible on `K|_Y` exactly when derived sections of `β_{K,s,t}` are.
* `AlgebraicGeometry.isIso_specializationMap_of_isProper` — the specialization map of a proper
  morphism is an isomorphism.
* `AlgebraicGeometry.isIso_specializationMap_and_cospecializationMap_of_isProper` — the
  specialization and cospecialization maps of a proper morphism are isomorphisms.

## References

* [Stacks Project, Tag 0GJW](https://stacks.math.columbia.edu/tag/0GJW)
* [Stacks Project, Tag 0GJ9](https://stacks.math.columbia.edu/tag/0GJ9)
* [Stacks Project, Tag 03Q9](https://stacks.math.columbia.edu/tag/03Q9)
* [Stacks Project, Tag 095T](https://stacks.math.columbia.edu/tag/095T)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry

open Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] isGrothendieckAbelian_sheaf_smallEtale_objectUniverse

variable (B : BigEtaleSite.{u}) {X S : Scheme.{u}} (hS : B.Contains S) (f : X ⟶ S)
  (s : GeometricPoint S) (t : GeometricPoint (strictHenselization B S hS s))

/-! ### The two fibres over `t` -/

/-- The fibre `X_t` of the base change `Y = X ×_S Spec 𝒪^{sh}_{S,s}` over `t` is a fibre product
of `f` with the image `t'` of `t` in `S`. -/
theorem isPullback_cospecializationFibre :
    IsPullback (cospecializationFibreToSource B hS f s t) (cospecializationFibreToPoint B hS f s t)
      f (specializedGeometricPoint B S hS s t).hom :=
  (IsPullback.of_hasPullback (strictHenselizationBaseChangeToStrictHenselization B hS f s)
      t.hom).paste_horiz (IsPullback.of_hasPullback f (strictHenselizationToBase B S hS s))
    |>.flip |> fun h => by
      simpa [cospecializationFibreToSource, specializedGeometricPoint, GeometricPoint.map] using
        h.flip

/-- For the image `t'` of a
geometric point `t` of `Spec 𝒪^{sh}_{S,s}` in `S`, the geometric fibre `X_{t'} = X ×_S t'` is
the fibre `X_t = Y ×_{Spec 𝒪^{sh}_{S,s}} t` of the base change `Y = X ×_S Spec 𝒪^{sh}_{S,s}`. -/
def geometricFibreIsoCospecializationFibre :
    geometricFibre f (specializedGeometricPoint B S hS s t) ≅ cospecializationFibre B hS f s t :=
  (isPullback_cospecializationFibre B hS f s t).isoPullback.symm

/-- The identification `X_{t'} ≅ X_t` lies over `Y`: followed by `h : X_t ⟶ Y` it is the
canonical morphism from the geometric fibre `X_{t'}` into `Y' = X ×_S Spec 𝒪^{sh}_{S,t'}`
followed by the base change `Y' ⟶ Y` of the specialization morphism. -/
theorem geometricFibreIsoCospecializationFibre_hom_comp :
    (geometricFibreIsoCospecializationFibre B hS f s t).hom ≫
        cospecializationFibreToBaseChange B hS f s t =
      geometricFibreToStrictHenselizationBaseChange B hS f
          (specializedGeometricPoint B S hS s t) ≫
        strictHenselizationBaseChangeSpecializationMapAt B hS f s t := by
  have hA : strictHenselizationBaseChangeSpecializationMapAt B hS f s t ≫
      pullback.fst f (strictHenselizationToBase B S hS s) =
      strictHenselizationBaseChangeToSource B hS f (specializedGeometricPoint B S hS s t) :=
    strictHenselizationBaseChangeSpecializationMap_comp_toSource B hS f s t
  have hB : strictHenselizationBaseChangeSpecializationMapAt B hS f s t ≫
      pullback.snd f (strictHenselizationToBase B S hS s) =
      strictHenselizationBaseChangeToStrictHenselization B hS f
          (specializedGeometricPoint B S hS s t) ≫
        specializationMorphism B S hS s t :=
    strictHenselizationBaseChangeSpecializationMap_comp_toStrictHenselization B hS f s t
  have hP : geometricPointToStrictHenselization B S hS (specializedGeometricPoint B S hS s t) ≫
      specializationMorphism B S hS s t = t.hom :=
    geometricPointToStrictHenselization_comp_specializationMorphism B S hS s t
  have hI : (geometricFibreIsoCospecializationFibre B hS f s t).hom ≫
      cospecializationFibreToPoint B hS f s t =
      geometricFibreToPoint f (specializedGeometricPoint B S hS s t) :=
    (isPullback_cospecializationFibre B hS f s t).isoPullback_inv_snd
  have hJ : (geometricFibreIsoCospecializationFibre B hS f s t).hom ≫
      cospecializationFibreToSource B hS f s t =
      geometricFibreToSource f (specializedGeometricPoint B S hS s t) :=
    (isPullback_cospecializationFibre B hS f s t).isoPullback_inv_fst
  apply pullback.hom_ext
  · simp only [Category.assoc]
    rw [hA]
    exact hJ.trans (geometricFibreToStrictHenselizationBaseChange_comp_toSource B hS f _).symm
  · simp only [Category.assoc]
    rw [hB, pullback.condition, ← Category.assoc, hI]
    have hL : geometricFibreToStrictHenselizationBaseChange B hS f
          (specializedGeometricPoint B S hS s t) ≫
        strictHenselizationBaseChangeToStrictHenselization B hS f
          (specializedGeometricPoint B S hS s t) =
        geometricFibreToPoint f (specializedGeometricPoint B S hS s t) ≫
          geometricPointToStrictHenselization B S hS (specializedGeometricPoint B S hS s t) :=
      pullback.lift_snd _ _ _
    refine Eq.trans ?_ (Category.assoc _ _ _)
    refine Eq.trans ?_ (congrArg (· ≫ specializationMorphism B S hS s t) hL.symm)
    exact ((Category.assoc _ _ _).trans
      (congrArg (geometricFibreToPoint f (specializedGeometricPoint B S hS s t) ≫ ·) hP)).symm

/-! ### Pullback along `h : X_t ⟶ Y` -/

/-- For `h : X_t ⟶ Y`, the restriction `RΓ(Y, K|_Y) ⟶ RΓ(X_t, h⁻¹(K|_Y))` is invertible exactly
when `RΓ(Y, β_{K,s,t})` is. -/
theorem isIso_restriction_cospecializationFibre_iff (K : smallEtaleDerivedCategory X) :
    IsIso ((smallEtaleDerivedGlobalSectionsRestriction
        (cospecializationFibreToBaseChange B hS f s t)).app
          ((smallEtaleDerivedPullbackAb (strictHenselizationBaseChangeToSource B hS f s)).obj K)) ↔
      IsIso ((smallEtaleDerivedGlobalSections (strictHenselizationBaseChange B hS f s)).map
        (cospecializationUnit B hS f s t K)) := by
  rw [smallEtaleDerivedGlobalSectionsRestriction_app, cospecializationUnit_eq,
    (smallEtaleDerivedGlobalSections (strictHenselizationBaseChange B hS f s)).map_comp,
    isIso_comp_right_iff, isIso_comp_right_iff]

/-- Restriction of derived sections along `a ≫ b` on `M` is restriction along `b`, then along `a`,
then the map induced by the composition isomorphism of derived inverse images. -/
private theorem smallEtaleDerivedGlobalSectionsRestriction_comp_app_eq {Y Z : Scheme.{u}}
    (a : X ⟶ Y) (b : Y ⟶ Z) (M : smallEtaleDerivedCategory Z) :
    (smallEtaleDerivedGlobalSectionsRestriction (a ≫ b)).app M =
      (smallEtaleDerivedGlobalSectionsRestriction b).app M ≫
        (smallEtaleDerivedGlobalSectionsRestriction a).app
          ((smallEtaleDerivedPullbackAb b).obj M) ≫
        (smallEtaleDerivedGlobalSections X).map
          ((smallEtaleDerivedPullbackAbCompIsoQhLift (smallEtalePullbackAbCompIso a b)).hom.app
            M) := by
  rw [smallEtaleDerivedGlobalSectionsRestriction_comp]
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.associator_inv_app,
    Functor.whiskerRight_app, Category.id_comp]

/-! ### The specialization map -/

/-- The specialization map of a proper morphism `f` is an isomorphism for a bounded below object
`K` of `D(X_étale)` with torsion cohomology sheaves relative to which `f` is locally acyclic. It
takes the proper base change theorem as `h095T` and the stalk formula
`DerivedPushforwardStalkFormula` as `h03Q9`. -/
theorem isIso_specializationMap_of_isProper (hX : B.Contains X)
    (h095T : ∀ ⦃X S : Scheme.{u}⦄ (f : X ⟶ S) [IsProper f],
      CohomologyCommutesWithBaseChange.{u, 0} f)
    (h03Q9 : DerivedPushforwardStalkFormula B) [IsProper f]
    (K : smallEtaleDerivedCategory X) (m : ℤ) (hK : K.IsGE m)
    (hKt : Stacks.Torsion.torsionCohomologyProperty.{u + 1} (smallEtaleTopology X) K)
    (hla : IsLocallyAcyclicRelative B hX hS f K) :
    IsIso ((smallEtaleDerivedSpecializationStalkAbAt B S hS s t).app
      ((smallEtaleDerivedPushforwardAb f).obj K)) := by
  set t' := specializedGeometricPoint B S hS s t
  set M := (smallEtaleDerivedPullbackAb (strictHenselizationBaseChangeToSource B hS f s)).obj K
  set φ := strictHenselizationBaseChangeSpecializationMapAt B hS f s t
  set i' := geometricFibreToStrictHenselizationBaseChange B hS f t'
  set h := cospecializationFibreToBaseChange B hS f s t
  set e := geometricFibreIsoCospecializationFibre B hS f s t
  have hh : IsIso ((smallEtaleDerivedGlobalSectionsRestriction h).app M) :=
    (isIso_restriction_cospecializationFibre_iff B hS f s t K).2
      (isIso_globalSections_map_cospecializationUnit B hS f s t K hX h095T h03Q9 m hK hKt
        hla)
  have he : IsIso (smallEtaleDerivedGlobalSectionsRestriction e.hom) :=
    isIso_smallEtaleDerivedGlobalSectionsRestriction e.hom
  have heh : IsIso ((smallEtaleDerivedGlobalSectionsRestriction (e.hom ≫ h)).app M) := by
    rw [smallEtaleDerivedGlobalSectionsRestriction_comp_app_eq]
    infer_instance
  have hi' : IsIso ((smallEtaleDerivedGlobalSectionsRestriction i').app
      ((smallEtaleDerivedPullbackAb φ).obj M)) :=
    hasClosedGeometricFibreRestrictionIso_of_cohomologyCommutesWithBaseChange B h095T hS f t' _ m
      ((smallEtalePullbackAb φ).isGE_obj_mapDerivedCategory _ m
        ((smallEtalePullbackAb _).isGE_obj_mapDerivedCategory K m hK))
      (torsionCohomologyProperty_smallEtaleDerivedPullbackAb _ _
        (torsionCohomologyProperty_smallEtaleDerivedPullbackAb _ K hKt))
  have hφ : IsIso ((smallEtaleDerivedGlobalSectionsRestriction φ).app M) := by
    have hcomp : IsIso ((smallEtaleDerivedGlobalSectionsRestriction (i' ≫ φ)).app M) := by
      rwa [← geometricFibreIsoCospecializationFibre_hom_comp]
    rwa [smallEtaleDerivedGlobalSectionsRestriction_comp_app_eq, ← Category.assoc,
      isIso_comp_right_iff, isIso_comp_right_iff] at hcomp
  have hsec : IsIso ((strictHenselizationSectionsSpecializationAt B hS f s t).app K) := by
    rw [strictHenselizationSectionsSpecializationAt_eq]
    simp only [strictHenselizationSectionsSpecialization, NatTrans.comp_app,
      Functor.whiskerLeft_app, Functor.associator_inv_app, Functor.whiskerRight_app,
      Category.id_comp]
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ hφ (Iso.isIso_hom (Functor.mapIso _
      ((smallEtaleDerivedPullbackAbCompIsoQhLift
        (strictHenselizationBaseChangeSpecializationPullbackAbCompIso B hS f s t)).app K)))
  have key := NatTrans.congr_app
    (derivedPushforwardStalkToStrictHenselizationSections_comp_sectionsSpecialization
      B hS f s t) K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at key
  have h0 := h03Q9 hS f s K m hK
  have h1 := h03Q9 hS f t' K m hK
  have : IsIso ((smallEtaleDerivedSpecializationStalkAbAt B S hS s t).app
      ((smallEtaleDerivedPushforwardAb f).obj K) ≫
        (derivedPushforwardStalkToStrictHenselizationSections B hS f t').app K) := by
    rw [← key]
    infer_instance
  exact IsIso.of_isIso_comp_right _
    ((derivedPushforwardStalkToStrictHenselizationSections B hS f t').app K)

/-! ### Tag 0GJW -/

/-- Let `f : X ⟶ S` be a morphism of
schemes of a big étale site and `K` an object of `D(X_étale)` such that

1. `K` is bounded below,
2. `f` is locally acyclic relative to `K`,
3. `f` is proper, and
4. `K` has torsion cohomology sheaves.

Then for every geometric point `s` of `S` and every geometric point `t` of `Spec 𝒪^{sh}_{S,s}`
the specialization map `sp : (Rf_*K)_s ⟶ (Rf_*K)_t` is an isomorphism, and the cospecialization
map `cosp : RΓ(X_t, K) ⟶ RΓ(X_s, K)`, which exists because `i⁻¹β_{K,s,t}` is an isomorphism, is
an isomorphism.

The stalk at `t` is taken at the image of `t` in `S`. The theorem takes the proper base change
theorem as `h095T` and the stalk formula `DerivedPushforwardStalkFormula` as `h03Q9`. -/
theorem isIso_specializationMap_and_cospecializationMap_of_isProper
    (h095T : ∀ ⦃X S : Scheme.{u}⦄ (f : X ⟶ S) [IsProper f],
      CohomologyCommutesWithBaseChange.{u, 0} f)
    (h03Q9 : DerivedPushforwardStalkFormula B) (hX : B.Contains X) [IsProper f]
    (K : smallEtaleDerivedCategory X) (m : ℤ) (hK : K.IsGE m)
    (hla : IsLocallyAcyclicRelative B hX hS f K)
    (hKt : Stacks.Torsion.torsionCohomologyProperty.{u + 1} (smallEtaleTopology X) K) :
    IsIso ((smallEtaleDerivedSpecializationStalkAbAt B S hS s t).app
        ((smallEtaleDerivedPushforwardAb f).obj K)) ∧
      ∃ _ : IsIso ((smallEtaleDerivedPullbackAb
          (geometricFibreToStrictHenselizationBaseChange B hS f s)).map
            (cospecializationUnit B hS f s t K)),
        IsIso (cospecializationMap B hS f s t K) :=
  have := isIso_pullback_cospecializationUnit_of_derivedPushforwardStalkFormula B hX hS f s t h03Q9
    K m hK hla
  ⟨isIso_specializationMap_of_isProper B hS f s t hX h095T h03Q9 K m hK hKt hla, this,
    isIso_cospecializationMap_of_cohomologyCommutesWithBaseChange B hS f s t K h095T m hK hKt⟩

end AlgebraicGeometry

end
