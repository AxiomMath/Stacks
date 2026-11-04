module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.StrictlyHenselianFibreSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ProperBaseChangeTheoremUnconditional
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionUnboundedDirectImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleDerivedSectionsRestrictionComp
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocalAcyclicity.CospecializationMap
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SpecializationMapAndFibres
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.DerivedPushforwardStalkStrictHenselization
public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowCoreflection
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocalAcyclicity.ProperSpecialization

/-!
# The specialization map of a proper morphism, from restriction to the geometric fibres

Let `f : X ⟶ S` be a proper morphism of schemes, `s` a geometric point of `S`, `t` a geometric
point of `Spec 𝒪^{sh}_{S,s}` and `t'` its image in `S`. Write `Y = X ×_S Spec 𝒪^{sh}_{S,s}` and
`h : X_t ⟶ Y` for the fibre of `Y` over `t`. For a bounded below object `K` of `D(X_étale)` with
torsion cohomology sheaves, the specialization map

`sp : (Rf_*K)_s ⟶ (Rf_*K)_{t'}`

is an isomorphism as soon as pullback of derived sections `RΓ(Y, K|_Y) ⟶ RΓ(X_t, h⁻¹(K|_Y))` is.
This is the argument of [Stacks, Tag 0GJW] for `sp` with its last step, the invertibility of
that pullback (which the source deduces from local acyclicity), left as the hypothesis `hh`; the
proper base change theorem (Tag 095T,
`Stacks.EtaleCohomology.cohomologyCommutesWithBaseChange_of_isProper`) and the stalk computation
(Tag 03Q9, `AlgebraicGeometry.isIso_derivedPushforwardStalkToStrictHenselizationSections_of_isGE`)
are theorems. For smooth proper families of curves and `K = ℤ/ℓ`, `ℓ` invertible, `hh` is
supplied by
`Stacks.EtaleCohomology.CurveFamily.bijective_constantExtRestriction_of_strictlyHenselian`.

## Main results

* `AlgebraicGeometry.hasClosedGeometricFibreRestrictionIso_of_cohomologyCommutesWithBaseChange`.
* `AlgebraicGeometry.geometricFibreIsoCospecializationFibre`.
* `AlgebraicGeometry.isIso_specializationMap_of_isProper_of_isIso_restriction`.

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

/-- Restriction of derived sections along `a ≫ b` at `N` is restriction along `b`, then along `a`,
then the map induced by the composition isomorphism of derived inverse images. -/
private theorem smallEtaleDerivedGlobalSectionsRestriction_comp_app {X₀ X₁ X₂ : Scheme.{u}}
    (a : X₀ ⟶ X₁) (b : X₁ ⟶ X₂) (N : smallEtaleDerivedCategory X₂) :
    (smallEtaleDerivedGlobalSectionsRestriction (a ≫ b)).app N =
      (smallEtaleDerivedGlobalSectionsRestriction b).app N ≫
        (smallEtaleDerivedGlobalSectionsRestriction a).app
            ((smallEtaleDerivedPullbackAb b).obj N) ≫
          (smallEtaleDerivedGlobalSections X₀).map
            ((smallEtaleDerivedPullbackAbCompIsoQhLift (smallEtalePullbackAbCompIso a b)).hom.app
              N) := by
  rw [smallEtaleDerivedGlobalSectionsRestriction_comp]
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.associator_inv_app,
    Functor.whiskerRight_app, Category.id_comp]

/-! ### The specialization map -/

/-- **The specialization map of a proper morphism is an isomorphism once restriction to the fibre
over `t` is.** For a bounded below object `K` of `D(X_étale)` with torsion cohomology sheaves,
if pullback of derived sections along `h : X_t ⟶ Y` is invertible on `K|_Y` (`hh`), then the
specialization map `(Rf_*K)_s ⟶ (Rf_*K)_{t'}` is an isomorphism.

Followed by pullback to the closed geometric fibre `X_{t'}` of `Y' = X ×_S Spec 𝒪^{sh}_{S,t'}`,
invertible by proper base change, pullback along the base change `φ : Y' ⟶ Y` of the
specialization morphism is pullback along `X_{t'} ≅ X_t ⟶ Y`, hence invertible; and by Tag 0GJ9
and Tag 03Q9 the specialization map is pullback along `φ` up to isomorphisms. -/
theorem isIso_specializationMap_of_isProper_of_isIso_restriction [IsProper f]
    (K : smallEtaleDerivedCategory X) (m : ℤ) (hK : K.IsGE m)
    (hKt : Stacks.Torsion.torsionCohomologyProperty.{u + 1} (smallEtaleTopology X) K)
    (hh : IsIso ((smallEtaleDerivedGlobalSectionsRestriction
        (cospecializationFibreToBaseChange B hS f s t)).app
          ((smallEtaleDerivedPullbackAb (strictHenselizationBaseChangeToSource B hS f s)).obj K))) :
    IsIso ((smallEtaleDerivedSpecializationStalkAbAt B S hS s t).app
      ((smallEtaleDerivedPushforwardAb f).obj K)) := by
  set t' := specializedGeometricPoint B S hS s t
  set M := (smallEtaleDerivedPullbackAb (strictHenselizationBaseChangeToSource B hS f s)).obj K
  set φ := strictHenselizationBaseChangeSpecializationMapAt B hS f s t
  set i' := geometricFibreToStrictHenselizationBaseChange B hS f t'
  set h := cospecializationFibreToBaseChange B hS f s t
  set e := geometricFibreIsoCospecializationFibre B hS f s t
  -- hence pullback along `X_{t'} ≅ X_t ⟶ Y` is invertible
  have he : IsIso (smallEtaleDerivedGlobalSectionsRestriction e.hom) :=
    isIso_smallEtaleDerivedGlobalSectionsRestriction e.hom
  have heh : IsIso ((smallEtaleDerivedGlobalSectionsRestriction (e.hom ≫ h)).app M) := by
    rw [smallEtaleDerivedGlobalSectionsRestriction_comp_app]
    infer_instance
  -- pullback to the closed geometric fibre of `Y'` is invertible by proper base change
  have hi' : IsIso ((smallEtaleDerivedGlobalSectionsRestriction i').app
      ((smallEtaleDerivedPullbackAb φ).obj M)) :=
    hasClosedGeometricFibreRestrictionIso_of_cohomologyCommutesWithBaseChange B
      (fun _ _ g _ => cohomologyCommutesWithBaseChange_of_isProper g) hS f t' _ m
      ((smallEtalePullbackAb φ).isGE_obj_mapDerivedCategory _ m
        ((smallEtalePullbackAb _).isGE_obj_mapDerivedCategory K m hK))
      (torsionCohomologyProperty_smallEtaleDerivedPullbackAb _ _
        (torsionCohomologyProperty_smallEtaleDerivedPullbackAb _ K hKt))
  -- so pullback along `φ` is invertible on `K|_Y`
  have hφ : IsIso ((smallEtaleDerivedGlobalSectionsRestriction φ).app M) := by
    have hcomp : IsIso ((smallEtaleDerivedGlobalSectionsRestriction (i' ≫ φ)).app M) := by
      rw [← geometricFibreIsoCospecializationFibre_hom_comp]
      exact heh
    rwa [smallEtaleDerivedGlobalSectionsRestriction_comp_app, isIso_comp_right_iff] at hcomp
  have hsec : IsIso ((strictHenselizationSectionsSpecializationAt B hS f s t).app K) := by
    rw [strictHenselizationSectionsSpecializationAt_eq]
    simp only [strictHenselizationSectionsSpecialization, NatTrans.comp_app,
      Functor.whiskerLeft_app, Functor.associator_inv_app, Functor.whiskerRight_app,
      Category.id_comp]
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ hφ (Iso.isIso_hom (Functor.mapIso _
      ((smallEtaleDerivedPullbackAbCompIsoQhLift
        (strictHenselizationBaseChangeSpecializationPullbackAbCompIso B hS f s t)).app K)))
  -- the square of Tag 0GJ9, whose horizontal arrows are invertible by Tag 03Q9
  have key := NatTrans.congr_app
    (derivedPushforwardStalkToStrictHenselizationSections_comp_sectionsSpecialization
      B hS f s t) K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at key
  -- (instance search for these two from `IsProper f` is slow in this import closure)
  have : QuasiCompact f :=
    @AlgebraicGeometry.instQuasiCompactOfUniversallyClosed _ _ f IsProper.toUniversallyClosed
  have : QuasiSeparated f :=
    @AlgebraicGeometry.IsSeparated.instQuasiSeparated _ _ f IsProper.toIsSeparated
  have h0 : ∀ u, IsIso ((derivedPushforwardStalkToStrictHenselizationSections B hS f u).app K) :=
    fun u => @isIso_derivedPushforwardStalkToStrictHenselizationSections_of_isGE B X S hS f _ _ u
      K m hK
  have := h0 s
  have := h0 t'
  have : IsIso ((smallEtaleDerivedSpecializationStalkAbAt B S hS s t).app
      ((smallEtaleDerivedPushforwardAb f).obj K) ≫
        (derivedPushforwardStalkToStrictHenselizationSections B hS f t').app K) := by
    rw [← key]
    infer_instance
  exact IsIso.of_isIso_comp_right _
    ((derivedPushforwardStalkToStrictHenselizationSections B hS f t').app K)

end AlgebraicGeometry

end
