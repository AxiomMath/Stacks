module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ClosedImmersionsPushforward.AbelianSheafEssentialImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.StalkIsomorphismCriterion
import all StacksFrontier.AlgebraicGeometry.EtaleCohomology.FinitePushforwardStalk.Injectivity

/-!
# The augmentation of the Čech resolution of a finite surjection is injective

Let `f : X ⟶ Y` be a finite surjective morphism of schemes. The unit `ℱ ⟶ f_* f^{-1}ℱ` of the
inverse-image/direct-image adjunction on abelian sheaves on the small étale sites is a
monomorphism.

A geometric point of `Y` lifts through a finite surjective morphism, and the stalk of the unit
at a geometric point which lifts is a split monomorphism: the stalk of `f^{-1}ℱ` at a lift is
the stalk of `ℱ` at the point ([Stacks, Tag 03Q1](https://stacks.math.columbia.edu/tag/03Q1)),
and the stalk of the unit followed by that identification and by the stalk of the counit is that
identification again, by the triangle identity. Injectivity on all stalks at geometric points
gives local injectivity, hence a monomorphism.

Since the zeroth level of the Čech nerve of `f` is `X` itself, this is exactness at `ℱ` of the
complex `0 → ℱ → ℱ₀ → ℱ₁ → ⋯` of [Stacks, Tag 09Z2](https://stacks.math.columbia.edu/tag/09Z2).

## Main results

* `AlgebraicGeometry.exists_geometricPoint_map_eq_of_isFinite` — a geometric point of the target
  of a finite surjective morphism is the image of a geometric point of the source.
* `AlgebraicGeometry.injective_etaleStalk_map_smallEtaleUnitAb` — the stalk of the unit at a
  geometric point of `Y` which lifts to `X` is injective.
* `AlgebraicGeometry.mono_smallEtaleUnitAb_of_isFinite_of_surjective` — for a finite surjective
  morphism the unit is a monomorphism.

## References

* [Stacks Project, Tag 09Z2](https://stacks.math.columbia.edu/tag/09Z2)
* [Stacks Project, Tag 03Q1](https://stacks.math.columbia.edu/tag/03Q1)
* [Stacks Project, Tag 03PU](https://stacks.math.columbia.edu/tag/03PU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)

/-- A geometric point of the target of a finite surjective morphism is the image of a geometric
point of the source with the same residue field: a point of the source over the image point
exists by surjectivity, and the residue field extension there is finite, so the chosen
algebraically closed field receives it. -/
public theorem exists_geometricPoint_map_eq_of_isFinite
    [IsFinite (B.inclusion.map f)] [Surjective (B.inclusion.map f)] (y : GeometricPoint Y.1) :
    ∃ x : GeometricPoint X.1, x.map (B.inclusion.map f) = y := by
  obtain ⟨x₀, hx₀⟩ := (B.inclusion.map f).surjective (y.hom default)
  obtain ⟨g, -⟩ := exists_geometricLift_of_mem_fiber (B.inclusion.map f) y x₀ hx₀
  exact ⟨geometricPointLift (B.inclusion.map f) y g, geometricPointLift_map _ y g⟩

/-- **The stalk of the unit at a geometric point of `Y` which lifts to `X` is injective.** The
stalk of `f^{-1}ℱ` at a lift `x` is the stalk of `ℱ` at `f ∘ x`, and composing the stalk of the
unit with that identification and with the stalk of the counit returns the identification, by
the triangle identity of the adjunction. -/
public theorem injective_etaleStalk_map_smallEtaleUnitAb (x : GeometricPoint X.1)
    (G : Sheaf (SmallEtale.topology B Y.1 Y.property) AddCommGrpCat.{u + 1}) :
    Function.Injective
      ((etaleStalkFunctorAbelian B Y.1 Y.property (x.map (B.inclusion.map f))).map
        (((smallEtaleBaseChange B f).sheafAdjunctionContinuous AddCommGrpCat.{u + 1}
          (SmallEtale.topology B Y.1 Y.property)
          (SmallEtale.topology B X.1 X.property)).unit.app G)) := by
  set PB := (smallEtaleBaseChange B f).sheafPullback AddCommGrpCat.{u + 1}
    (SmallEtale.topology B Y.1 Y.property) (SmallEtale.topology B X.1 X.property) with hPB
  set PF := (smallEtaleBaseChange B f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
    (SmallEtale.topology B Y.1 Y.property) (SmallEtale.topology B X.1 X.property) with hPF
  set SX := etaleStalkFunctorAbelian B X.1 X.property x with hSX
  set adj := (smallEtaleBaseChange B f).sheafAdjunctionContinuous AddCommGrpCat.{u + 1}
    (SmallEtale.topology B Y.1 Y.property) (SmallEtale.topology B X.1 X.property) with hadj
  set e := smallEtalePullbackStalkIsoAbelian B f x with he
  have htri : (PB ⋙ SX).map (adj.unit.app G) ≫ SX.map (adj.counit.app (PB.obj G)) =
      𝟙 ((PB ⋙ SX).obj G) := by
    rw [Functor.comp_map, ← Functor.map_comp, adj.left_triangle_components G]
    exact CategoryTheory.Functor.map_id _ _
  have hfac : (etaleStalkFunctorAbelian B Y.1 Y.property
        (x.map (B.inclusion.map f))).map (adj.unit.app G) ≫
      (e.inv.app ((PB ⋙ PF).obj G) ≫ SX.map (adj.counit.app (PB.obj G))) = e.inv.app G := by
    rw [← Category.assoc, e.inv.naturality (adj.unit.app G), Category.assoc, htri]
    exact Category.comp_id _
  have hmono : Mono ((etaleStalkFunctorAbelian B Y.1 Y.property
      (x.map (B.inclusion.map f))).map (adj.unit.app G)) := mono_of_mono_fac hfac
  exact (AddCommGrpCat.mono_iff_injective _).1 hmono

/-- **Stacks 09Z2, exactness at `ℱ`.** For a finite surjective morphism of schemes the unit
`ℱ ⟶ f_* f^{-1}ℱ` of the inverse-image/direct-image adjunction on abelian sheaves on the small
étale sites is a monomorphism. The zeroth level of the Čech nerve of `f` being `X` itself, this
is injectivity of the augmentation `ℱ ⟶ ℱ₀`. -/
@[stacks 09Z2 "exactness at `ℱ` of `0 → ℱ → ℱ₀ → ℱ₁ → ⋯`, i.e. injectivity of the augmentation
`ℱ ⟶ ℱ₀ = f_*f^{-1}ℱ`; exactness in the higher degrees and the spectral sequence are not proved
here"]
public theorem mono_smallEtaleUnitAb_of_isFinite_of_surjective
    [IsFinite (B.inclusion.map f)] [Surjective (B.inclusion.map f)]
    (G : Sheaf (SmallEtale.topology B Y.1 Y.property) AddCommGrpCat.{u + 1}) :
    Mono (((smallEtaleBaseChange B f).sheafAdjunctionContinuous AddCommGrpCat.{u + 1}
      (SmallEtale.topology B Y.1 Y.property)
      (SmallEtale.topology B X.1 X.property)).unit.app G) := by
  have : Sheaf.IsLocallyInjective
      (((smallEtaleBaseChange B f).sheafAdjunctionContinuous AddCommGrpCat.{u + 1}
        (SmallEtale.topology B Y.1 Y.property)
        (SmallEtale.topology B X.1 X.property)).unit.app G) :=
    isLocallyInjective_of_injective_etaleStalkMap.{u, u + 1} B Y.1 Y.property _ fun s => by
      obtain ⟨x, hx⟩ := exists_geometricPoint_map_eq_of_isFinite B f s
      subst hx
      exact injective_etaleStalk_map_smallEtaleUnitAb B f x G
  exact Sheaf.mono_of_isLocallyInjective _

end AlgebraicGeometry

end
