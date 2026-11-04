module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.ComplexSystemGlueing

/-!
# Tag 0D6B from a system of complexes

`Stacks.DerivedGlueing.ProducesComplexSystem` asks, for each datum of [Stacks, Tag 0D6B] — a
well ordered increasing family of opens `W`, prescribed objects `K α` without negative self-Ext,
and prescribed transitions `ρ^α_β` satisfying the cocycle condition — for a system of complexes

```
F : E ⥤ CochainComplex (Mod 𝒪_X) ℤ,   I α,   hsupp : F α ≅ (j_α)_! (I α),   hqi,
hK : Q (I α) ≅ K α
```

whose own transitions, `Stacks.DerivedGlueing.glueingTransitionIso` read through `hK`, are the
prescribed `ρ^α_β`.  The assembly `Stacks.DerivedGlueing.glueing_compatibility_of_iso` produces
the identifications `σ_α` of the restrictions of the colimit and proves them compatible with
the transitions the system determines, hence with the prescribed ones.

`Stacks.DerivedGlueing.gluesAlongWellOrderedCover_of_producesComplexSystem` is that
implication.  Its cofinal family is `Set.univ`, and the empty index order is handled by the zero
object.  `Stacks.DerivedGlueing.producesComplexSystem` proves the hypothesis, by the transfinite
recursion of the source.

## References

* [Stacks Project, Tag 0D6B](https://stacks.math.columbia.edu/tag/0D6B)
* [Stacks Project, Tag 0D68](https://stacks.math.columbia.edu/tag/0D68)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open ExtensionByZeroModules
open scoped ZeroObject

namespace Stacks.DerivedGlueing

universe u

attribute [local instance] HasDerivedCategory.standard

variable {X : RingedSpace.{u, u}}

/-- **A system of complexes realising the datum of [Stacks, Tag 0D6B]**: representatives `I α`
of the prescribed objects and a functor `F` whose values are their extensions by zero, whose
transitions restrict to quasi-isomorphisms and induce the prescribed transitions. -/
def ProducesComplexSystem (S : LocallyGiven X) : Prop :=
  ∀ (E : Type u) [LinearOrder E] [WellFoundedLT E] (W : E → Opens X.carrier)
    (hmono : ∀ β α : E, β ≤ α → W β ≤ W α),
      ∀ (K : ∀ α : E, OpenDerivedCategory X (W α)),
        (∀ (α : E) (i : ℤ), i < 0 → Subsingleton (ShiftedHom (K α) (K α) i)) →
        ∀ (rho : ∀ (β α : E) (h : β < α),
            (S.restriction (W β) (W α) (hmono β α h.le)).obj (K α) ≅ K β),
          (∀ (γ β α : E) (hγβ : γ < β) (hβα : β < α),
              (rho γ α (hγβ.trans hβα)).hom =
                (S.restrictionComp (W γ) (W β) (W α) (hmono γ β hγβ.le)
                    (hmono β α hβα.le)).hom.app (K α) ≫
                  (S.restriction (W γ) (W β) (hmono γ β hγβ.le)).map (rho β α hβα).hom ≫
                    (rho γ β hγβ).hom) →
            ∃ (F : E ⥤ CochainComplex (SheafOfModules.{u} (underlyingRingSheaf X)) ℤ)
              (I : ∀ α : E, CochainComplex (SheafOfModules.{u} (restrictedRingSheaf X (W α))) ℤ)
              (hsupp : ∀ α : E, F.obj α ≅
                ((jShriek (W α) (underlyingRingSheaf X)).mapHomologicalComplex
                  (ComplexShape.up ℤ)).obj (I α))
              (hqi : ∀ (β α : E) (h : β ≤ α),
                QuasiIso (((jStar (W β) (underlyingRingSheaf X)).mapHomologicalComplex
                  (ComplexShape.up ℤ)).map (F.map h.hom)))
              (hK : ∀ α : E, DerivedCategory.Q.obj (I α) ≅ K α),
              ∀ (β α : E) (h : β < α),
                ((S.restriction (W β) (W α) (hmono β α h.le)).mapIso (hK α).symm ≪≫
                  glueingTransitionIso S W F I hsupp hqi (hmono β α h.le) h.le ≪≫ hK β) =
                  rho β α h

/-- **A system of complexes realising the datum gives the glueing property over a well ordered
increasing cover.** -/
theorem gluesAlongWellOrderedCover_of_producesComplexSystem (S : LocallyGiven X)
    (hprod : ProducesComplexSystem S) : GluesAlongWellOrderedCover.{u} S := by
  intro E _ _ W hmono _ _ K hExt rho hcocycle
  rcases isEmpty_or_nonempty E with hE | hE
  · exact ⟨0, fun α => isEmptyElim α, ∅, fun α => isEmptyElim α,
      fun _ γ _ h => absurd h (Set.notMem_empty γ)⟩
  · have := hE
    have hmono' : ∀ β α : E, β ≤ α → W β ≤ W α := fun β α h =>
      (eq_or_lt_of_le h).elim (fun e => e ▸ le_rfl) (hmono β α)
    obtain ⟨F, I, hsupp, hqi, hK, hrho⟩ :=
      hprod E W hmono' K hExt rho hcocycle
    refine ⟨glueingObject F, fun α => glueingRestrictionIso S W F I hsupp hqi α ≪≫ hK α,
      Set.univ, fun α => ⟨α, Set.mem_univ α, le_rfl⟩, fun β γ h _ => ?_⟩
    rw [← hrho β γ h]
    exact glueing_compatibility_of_iso W F I hsupp S hqi K hK (hmono' β γ h.le) h.le

/-- **The conclusion of [Stacks, Tag 0D6B] from a system of complexes realising its datum.** -/
theorem exists_glueing_of_wellOrderedCover_of_producesComplexSystem (S : LocallyGiven X)
    (hprod : ProducesComplexSystem S)
    (E : Type u) [LinearOrder E] [WellFoundedLT E] (W : E → Opens X.carrier)
    (hsucc : ∀ β α : E, β < α → (∀ γ : E, γ < α → γ ≤ β) → W β ≤ W α)
    (hlimit : ∀ α : E, (¬ ∃ β : E, β < α ∧ ∀ γ : E, γ < α → γ ≤ β) →
      W α = ⨆ (β : E) (_ : β < α), W β)
    (hcover : (⨆ α : E, W α) = ⊤) (K : ∀ α : E, OpenDerivedCategory X (W α))
    (hExt : ∀ (α : E) (i : ℤ), i < 0 → Subsingleton (ShiftedHom (K α) (K α) i))
    (rho : ∀ (β α : E) (h : β < α),
      (S.restriction (W β) (W α) (le_of_succ_of_limit W hsucc hlimit β α h)).obj (K α) ≅ K β)
    (hcocycle : ∀ (γ β α : E) (hγβ : γ < β) (hβα : β < α),
      (rho γ α (hγβ.trans hβα)).hom =
        (S.restrictionComp (W γ) (W β) (W α) (le_of_succ_of_limit W hsucc hlimit γ β hγβ)
            (le_of_succ_of_limit W hsucc hlimit β α hβα)).hom.app (K α) ≫
          (S.restriction (W γ) (W β)
            (le_of_succ_of_limit W hsucc hlimit γ β hγβ)).map (rho β α hβα).hom ≫
            (rho γ β hγβ).hom) :
    ∃ (G : OpenDerivedCategory X ⊤)
      (sigma : ∀ α : E, (S.restriction (W α) ⊤ le_top).obj G ≅ K α),
      ∀ (β α : E) (h : β < α),
        (S.restrictionComp (W β) (W α) ⊤
              (le_of_succ_of_limit W hsucc hlimit β α h) le_top).hom.app G ≫
            (S.restriction (W β) (W α)
              (le_of_succ_of_limit W hsucc hlimit β α h)).map (sigma α).hom ≫ (rho β α h).hom =
          (sigma β).hom :=
  exists_glueing_of_wellOrderedCover_of_gluesAlong S
    (gluesAlongWellOrderedCover_of_producesComplexSystem S hprod) E W hsucc hlimit hcover K hExt
    rho hcocycle

end Stacks.DerivedGlueing

end
