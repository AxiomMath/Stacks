module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.LimitPerfectDescendSquareStep
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DerivedPullbackPerfect
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedPullbackAlongIso

/-!
# Descending finitely many perfect objects to a common stage

In Situation 09RH, with limit `X = lim X_i`, suppose that perfect objects descend along the
projections `X ⟶ X_i`: every perfect object of `D(𝒪_X)` is the derived pullback of a perfect
object on some stage.  Then finitely many perfect objects descend to one common stage.  The
statement is read through an isomorphism `X' ≅ X` from a given algebraic space.

## Main results

* `DescentSituation.exists_stage_derivedPullback_iso_of_perfectObjectsDescend`:
  finitely many perfect objects on an algebraic space isomorphic to the limit are the derived
  pullbacks of perfect objects on one stage.

## References

* [Stacks Project, Tag 09RJ](https://stacks.math.columbia.edu/tag/09RJ)
* [Stacks Project, Tag 09RH](https://stacks.math.columbia.edu/tag/09RH)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace DescentSituation

variable {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
  (D : DescentSituation B S hS hZ I)

/-- **Finitely many perfect objects descend to a common stage.**  If perfect objects descend along
the projections of Situation 09RH, then for an algebraic space `X'` with `e : X' ≅ X` and finitely
many perfect objects `E_l` of `D(𝒪_{X'})` there are a stage `i ≥ 0` and perfect objects `F_l` of
`D(𝒪_{X_i})` with `L(f_i ∘ e)^* F_l ≅ E_l`. -/
theorem exists_stage_derivedPullback_iso_of_perfectObjectsDescend
    (hD : PerfectObjectsDescend (fun i : D.Stages => D.projection i.1))
    {X' : AlgebraicSpaces B S hS} (e : X' ≅ D.limitSpace) {ι : Type*} [Finite ι]
    (E : ι → @DerivedCategory (Modules.{u, u} B S hS X'.1 X'.2) _ _
      (HasDerivedCategory.standard _))
    (hE : ∀ l, letI := HasDerivedCategory.standard (Modules.{u, u} B S hS X'.1 X'.2)
      (smallEtaleRingedSite B S hS X'.1 X'.2).IsPerfect (E l)) :
    ∃ (i : D.Stages) (F : ι → @DerivedCategory (Modules.{u, u} B S hS (D.stage i.1).1
        (D.stage i.1).2) _ _ (HasDerivedCategory.standard _)),
      (∀ l, letI := HasDerivedCategory.standard (Modules.{u, u} B S hS (D.stage i.1).1
          (D.stage i.1).2)
        (smallEtaleRingedSite B S hS (D.stage i.1).1 (D.stage i.1).2).IsPerfect (F l)) ∧
      ∀ l, letI := HasDerivedCategory.standard (Modules.{u, u} B S hS X'.1 X'.2)
        letI := HasDerivedCategory.standard (Modules.{u, u} B S hS (D.stage i.1).1
          (D.stage i.1).2)
        Nonempty ((smallEtaleDerivedModulePullback B S hS (e.hom ≫ D.projection i.1)).obj (F l) ≅
          E l) := by
  classical
  let := HasDerivedCategory.standard (Modules.{u, u} B S hS X'.1 X'.2)
  let := HasDerivedCategory.standard (Modules.{u, u} B S hS D.limitSpace.1 D.limitSpace.2)
  choose i₀ F₀ hF₀ hiso using
    fun l => hD _ (isPerfect_smallEtaleDerivedModulePullback e.inv _ (hE l))
  have : Fintype ι := Fintype.ofFinite ι
  have : Nonempty D.Stages := ⟨⟨D.base, le_rfl⟩⟩
  obtain ⟨i, hi⟩ := (Finset.univ.image i₀).exists_le
  have hle : ∀ l, (i₀ l).1 ≤ i.1 := fun l => hi _ (Finset.mem_image_of_mem _ (Finset.mem_univ l))
  refine ⟨i, fun l => (smallEtaleDerivedModulePullback B S hS (D.transition (hle l))).obj (F₀ l),
    fun l => isPerfect_smallEtaleDerivedModulePullback _ _ (hF₀ l), fun l => ⟨?_⟩⟩
  have hcomp : (e.hom ≫ D.projection i.1) ≫ D.transition (hle l) =
      e.hom ≫ D.projection (i₀ l).1 := by
    rw [Category.assoc, projection_comp_transition]
  exact (smallEtaleDerivedModulePullbackCompIso B S hS _ _).app _ ≪≫
    (smallEtaleDerivedModulePullbackCongr B S hS hcomp).app _ ≪≫
    ((smallEtaleDerivedModulePullbackCompIso B S hS _ _).app _).symm ≪≫
    (smallEtaleDerivedModulePullback B S hS e.hom).mapIso (hiso l).some ≪≫
    (smallEtaleDerivedModulePullbackHomInvIso B S hS e).app (E l)

end DescentSituation

end AlgebraicGeometry.Space

end
