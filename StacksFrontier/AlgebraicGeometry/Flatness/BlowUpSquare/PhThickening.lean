module

public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.Sieves.Functoriality
public import StacksFrontier.AlgebraicGeometry.Thickenings
public import StacksFrontier.AlgebraicGeometry.Topologies.Ph.BigSite
public import StacksFrontier.AlgebraicGeometry.Topologies.Ph.Coverings
public import StacksFrontier.CategoryTheory.Sites.Pretopology.CombinatorialEquivalence
public import StacksCore.Tactic.StacksAttribute

/-!
# Invariance of ph sheaves under thickenings

A sheaf on the big ph site over a scheme has the same sections on an object of the site and on
any thickening of that object inside the site: restriction along a thickening is a bijection
on sections.

## Main results

* `AlgebraicGeometry.BigPHOver.bijective_map_of_isThickening`: restriction of a ph sheaf
  along a thickening is bijective.

## Implementation notes

The thickening is a morphism in the slice category defining the big ph site over `S`; the
hypothesis is that its underlying morphism of schemes is a thickening in the sense of
`Stacks.Thickenings.IsThickening`.

A thickening is a surjective closed immersion, hence proper and surjective, so it is a ph
covering of schemes by `AlgebraicGeometry.surjective_proper_isPHCovering`. Transporting that
covering into the size-bounded category and then into the slice over `S` turns the singleton
sieve on the thickening into a covering sieve for the localized topology, and the sheaf
condition for a singleton covering by a monomorphism is exactly bijectivity of the
restriction map.

## References

* [Stacks Project, Tag 0EW2](https://stacks.math.columbia.edu/tag/0EW2)
-/

@[expose] public section

open CategoryTheory

universe u v

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 0EW2.** Restriction of a ph sheaf along a thickening is a bijection
of sections. -/
@[stacks 0EW2]
theorem BigPHOver.bijective_map_of_isThickening
    (B : BigPHSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : Sheaf (BigPHOver.topology B S hS) (Type v))
    {X X' : BigPHOver B S hS} (i : X ⟶ X')
    (hi : Stacks.Thickenings.IsThickening ((BigPHOver.toScheme B S hS).map i)) :
    Function.Bijective (F.obj.map i.op) := by
  change Stacks.Thickenings.IsThickening (B.inclusion.map i.left) at hi
  let f := B.inclusion.map i.left
  have : Surjective f := ⟨hi.2⟩
  have : IsClosedImmersion f := hi.1
  have : IsProper f := by infer_instance
  have : Mono (B.inclusion.map i.left) := by infer_instance
  have hphSmall := surjective_proper_isPHCovering f
  let EBig : PreZeroHypercover.{u + 1} (B.inclusion.obj X'.left) := {
      I₀ := ULift.{u + 1} Unit
      X := fun _j => B.inclusion.obj X.left
      f := fun _j => f
    }
  let E : Covering B.Schemes := ⟨X'.left, {
    I₀ := ULift.{u + 1} Unit
    X := fun _j => X.left
    f := fun _j => i.left
  }⟩
  have hphBig : IsPHCovering EBig.X EBig.f := by
    rw [isPHCovering_iff] at hphSmall ⊢
    refine ⟨fun _ => hphSmall.1 (), ?_⟩
    intro U hU
    obtain ⟨𝒰, hstd, ⟨φ⟩⟩ := hphSmall.2 U hU
    let k : ((PreZeroHypercover.singleton f).pullback₂ U.ι).Hom
        (EBig.pullback₂ U.ι) := {
      s₀ := fun _ => ULift.up ()
      h₀ := fun _ => 𝟙 _
      w₀ := fun _ => by simp [EBig, PreZeroHypercover.pullback₂,
        PreZeroHypercover.singleton]
    }
    exact ⟨𝒰, hstd, ⟨φ.comp k⟩⟩
  have hphE : IsPHCoveringInCutoff E := by
    change IsPHCovering (E.2.map B.inclusion).X (E.2.map B.inclusion).f
    simpa [E, EBig, f, PreZeroHypercover.map] using hphBig
  obtain ⟨⟨Vtarget, Vfamily⟩, hV, hTarget, hComb⟩ :=
    B.covering_representative E hphE
  change E.1 = Vtarget at hTarget
  subst Vtarget
  have hbaseE : Sieve.generate E.2.presieve₀ ∈ B.topology E.1 :=
    Precoverage.generate_mem_toGrothendieck
      (PreZeroHypercover.presieve₀_eq_of_combinatoriallyEquivalent hComb ▸
        (BigPHSite.mem_precoverage_iff B).2 ⟨Vfamily, rfl, hV⟩)
  have hbase : Sieve.generate (Presieve.singleton i.left) ∈ B.topology X'.left := by
    simpa [E, PreZeroHypercover.presieve₀, Presieve.ofArrows_of_unique] using hbaseE
  have hsieve : Sieve.overEquiv X' (Sieve.generate (Presieve.singleton i)) =
      Sieve.generate (Presieve.singleton i.left) := by
    rw [Sieve.overEquiv_generate]
    rw [← Sieve.arrows_generate_map_eq_functorPushforward]
    simp
  have hcover : Sieve.generate (Presieve.singleton i) ∈
      BigPHOver.topology B S hS X' := by
    rw [BigPHOver.topology, GrothendieckTopology.mem_over_iff, hsieve]
    exact hbase
  have hsheaf : Presieve.IsSheafFor F.obj (Presieve.singleton i) :=
    (Presieve.isSheafFor_iff_generate (Presieve.singleton i)).2
      (Presheaf.IsSheaf.isSheafFor F.property _ hcover)
  have hunique := (Presieve.isSheafFor_singleton).mp hsheaf
  have hpreimage (x : F.obj.obj (Opposite.op X)) :
      ∃! y, F.obj.map (Opposite.op i) y = x := by
    apply hunique x
    intro Z p₁ p₂ hp
    have : p₁ = p₂ := by
      ext
      have h : p₁.left ≫ i.left = p₂.left ≫ i.left := congrArg Over.Hom.left hp
      exact congrArg (fun q => q.hom) (B.inclusion.map_injective ((cancel_mono f).1
        (by simpa only [Functor.map_comp] using
          congrArg (fun g => B.inclusion.map g) h)))
    subst p₂
    rfl
  constructor
  · intro a b hab
    exact (hpreimage (F.obj.map (Opposite.op i) a)).unique rfl hab.symm
  · intro x
    obtain ⟨y, hy, _⟩ := hpreimage x
    exact ⟨y, hy⟩

end AlgebraicGeometry
