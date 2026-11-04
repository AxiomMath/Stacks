module

public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.StageTensorSectionsIso
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedSheafHomTensorDualNatural
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.AffinePerfectSections
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedTensorClosed
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedPullback
public import StacksFrontier.CategoryTheory.Adjunction.LiftLeftAdjoint
public import StacksFrontier.Homology.Injectives.DerivedCategory.DerivedLimit
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.PerfectSectionsTransition
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.CohomologyBaseChangeSheafHom

/-!
# `RΓ(X, E ⊗^𝐋 -)` for a perfect `E`, and derived limits

Let `X` be the algebraic space of Situation [Stacks, Tag 0CX4] over `Spec A`, and `E` a perfect
object of `D(𝒪_X)`. The functor `RΓ(X, E ⊗^𝐋 -) : D(𝒪_X) ⥤ D(A)` is a right adjoint: tensoring
with a perfect `E` is right adjoint to tensoring with its dual (Stacks 08J8, 08JJ), and
`RΓ(X, -) = RΓ(Spec A, Rf_* -)` is right adjoint to `Lf^* ∘ Φ_A`. Its left adjoint lands in
`D_QCoh(𝒪_X)`, so

* it inverts the counit `DQ_X(L) ⟶ L` of a coherator ([Stacks, Tag 08H0]), and
* it carries the derived-limit triangle of `L = R lim (iₙ,* Fₙ)` to a distinguished triangle.

## Main definitions

* `AlgebraicGeometry.Space.FlatSheafExistenceSituation.tensorSectionsFunctor`: `RΓ(X, E ⊗^𝐋 -)`.
* `AlgebraicGeometry.Space.FlatSheafExistenceSituation.tensorSectionsAdjunction`: its left
  adjoint.

## Main results

* `AlgebraicGeometry.Space.FlatSheafExistenceSituation.isIso_tensorSectionsFunctor_map_counit`:
  `RΓ(X, E ⊗^𝐋 DQ_X(L)) ≅ RΓ(X, E ⊗^𝐋 L)`.
* `AlgebraicGeometry.Space.FlatSheafExistenceSituation.tensorSections_derivedLimit_triangle`:
  the image of a derived-limit triangle is distinguished.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

universe u

namespace AlgebraicGeometry.Space

namespace FlatSheafExistenceSituation

variable (D : FlatSheafExistenceSituation.{u})
  (E : spaceDerivedCategory D.B D.S D.containsLimitBase D.X.left)

/-- **`RΓ(X, E ⊗^𝐋 -) : D(𝒪_X) ⥤ D(A)`**, with `RΓ(X, -) = RΓ(Spec A, Rf_* -)`. -/
abbrev tensorSectionsFunctor :
    spaceDerivedCategory D.B D.S D.containsLimitBase D.X.left ⥤
      StacksDraft.ringDerivedCategory Γ((BigFppfOver.toScheme D.B D.S D.containsLimitBase).obj
        (limitBaseObject D.system D.B D.containsLimitBase), ⊤) :=
  (smallEtaleDerivedTensor D.B D.S D.containsLimitBase D.X.left).obj E ⋙
    (derivedModulePushforward D.B D.S D.containsLimitBase D.X.hom ⋙
      representedAffineDerivedSections D.B D.S D.containsLimitBase
        (limitBaseObject D.system D.B D.containsLimitBase))

/-- **`RΓ(X, E ⊗^𝐋 -)` is a right adjoint** for perfect `E`, with left adjoint
`Lf^*Φ_A(-) ⊗^𝐋 E^∨`. -/
def tensorSectionsAdjunction (hE : spaceIsPerfect D.B D.S D.containsLimitBase D.X.left E) :
    (representedAffineDerivedAssociated D.B D.S D.containsLimitBase
          (limitBaseObject D.system D.B D.containsLimitBase) ⋙
        smallEtaleDerivedModulePullback D.B D.S D.containsLimitBase D.X.hom) ⋙
      (smallEtaleDerivedTensor D.B D.S D.containsLimitBase D.X.left).flip.obj
        (smallEtaleDerivedDual D.B D.S D.containsLimitBase D.X.left E) ⊣
      D.tensorSectionsFunctor E :=
  (affineBaseDerivedSectionsAdjunction D.B D.S D.containsLimitBase D.X.hom).comp
    (smallEtaleDerivedTensorDualAdjunction D.B D.S D.containsLimitBase D.X.left E hE)

/-- **`RΓ(X, E ⊗^𝐋 -)` inverts the counit of a coherator**, for perfect `E`: its left adjoint
`Lf^*Φ_A(-) ⊗^𝐋 E^∨` lands in `D_QCoh(𝒪_X)` (Stacks 08DW, 08F5). -/
theorem isIso_tensorSectionsFunctor_map_counit
    (hE : spaceIsPerfect D.B D.S D.containsLimitBase D.X.left E)
    {DQ : spaceDerivedCategory D.B D.S D.containsLimitBase D.X.left ⥤
      (spaceQuasicoherentProp D.B D.S D.containsLimitBase D.X.left).FullSubcategory}
    (adj : (spaceQuasicoherentProp D.B D.S D.containsLimitBase D.X.left).ι ⊣ DQ)
    (L : spaceDerivedCategory D.B D.S D.containsLimitBase D.X.left) :
    IsIso ((D.tensorSectionsFunctor E).map (adj.counit.app L)) :=
  Adjunction.isIso_map_counit_app_of_forall adj (D.tensorSectionsAdjunction E hE)
    (fun Y => qcohDerived_smallEtaleDerivedTensor D.X.left _ _
      (derivedQuasicoherent_smallEtaleDerivedModulePullback D.B D.S D.containsLimitBase D.X.hom _
        (qcohDerived_representedAffineDerivedAssociated_obj D.B D.S D.containsLimitBase
          (limitBaseObject D.system D.B D.containsLimitBase) Y))
      (qcohDerived_of_isPerfect D.B D.S D.containsLimitBase D.X.left _
        (isPerfect_smallEtaleDerivedDual D.B D.S D.containsLimitBase D.X.left E hE))) L

/-! The shift structures of the small étale functors are elaborated under the standard model, so the
triangle argument is run with that model installed. -/
section StandardModel

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
attribute [local instance] HasDerivedCategory.standard SheafOfModules.instAbelian

/-- **`RΓ(X, E ⊗^𝐋 -)` carries a derived-limit triangle of `(iₙ,* Fₙ)` to a distinguished
triangle**, for perfect `E`: it is exact and, being a right adjoint, preserves the product. The
new structural map is the image of the old one followed by the product comparison. -/
theorem tensorSections_derivedLimit_triangle
    (hE : spaceIsPerfect D.B D.S D.containsLimitBase D.X.left E)
    (L : spaceDerivedCategory D.B D.S D.containsLimitBase D.X.left)
    (p : L ⟶ ∏ᶜ fun n : ℕ => D.derivedSystem.obj ⟨n⟩)
    (hp : ∃ δ : (∏ᶜ fun n : ℕ => D.derivedSystem.obj ⟨n⟩) ⟶ L⟦(1 : ℤ)⟧,
      Triangle.mk p (Pi.lift fun n : ℕ => Pi.π (fun n : ℕ => D.derivedSystem.obj ⟨n⟩) n -
        Pi.π (fun n : ℕ => D.derivedSystem.obj ⟨n⟩) (n + 1) ≫
          D.derivedSystem.map (homOfLE (Nat.le_succ n)).op) δ ∈
        distTriang (spaceDerivedCategory D.B D.S D.containsLimitBase D.X.left)) :
    ∃ _ : HasProduct fun n : ℕ => (D.tensorSectionsFunctor E).obj (D.derivedSystem.obj ⟨n⟩),
      ∃ δ : (∏ᶜ fun n : ℕ => (D.tensorSectionsFunctor E).obj (D.derivedSystem.obj ⟨n⟩)) ⟶
          ((D.tensorSectionsFunctor E).obj L)⟦(1 : ℤ)⟧,
        Triangle.mk ((D.tensorSectionsFunctor E).map p ≫
            piComparison (D.tensorSectionsFunctor E) (fun n : ℕ => D.derivedSystem.obj ⟨n⟩))
          (Pi.lift fun n : ℕ =>
            Pi.π (fun n : ℕ => (D.tensorSectionsFunctor E).obj (D.derivedSystem.obj ⟨n⟩)) n -
              Pi.π (fun n : ℕ => (D.tensorSectionsFunctor E).obj (D.derivedSystem.obj ⟨n⟩))
                  (n + 1) ≫
                (D.tensorSectionsFunctor E).map
                  (D.derivedSystem.map (homOfLE (Nat.le_succ n)).op)) δ ∈
          distTriang (StacksDraft.ringDerivedCategory
            Γ((BigFppfOver.toScheme D.B D.S D.containsLimitBase).obj
              (limitBaseObject D.system D.B D.containsLimitBase), ⊤)) := by
  have _ : PreservesLimitsOfSize.{0, 0} (D.tensorSectionsFunctor E) :=
    (D.tensorSectionsAdjunction E hE).rightAdjoint_preservesLimits
  let G := D.tensorSectionsFunctor E
  let P : ℕ → spaceDerivedCategory D.B D.S D.containsLimitBase D.X.left :=
    fun n => D.derivedSystem.obj ⟨n⟩
  refine ⟨⟨⟨_, isLimitOfHasProductOfPreservesLimit G P⟩⟩, ?_⟩
  obtain ⟨δ, hT⟩ := hp
  have : G.Additive := Functor.additive_of_preserves_binary_products G
  let : ((smallEtaleDerivedTensor D.B D.S D.containsLimitBase D.X.left).obj E).CommShift ℤ :=
    (smallEtaleDerivedTensorProduct D.B D.S D.containsLimitBase D.X.left).commShift_right E
  have : ((smallEtaleDerivedTensor D.B D.S D.containsLimitBase D.X.left).obj E).IsTriangulated :=
    (smallEtaleDerivedTensorProduct D.B D.S D.containsLimitBase D.X.left).exact_right E
  let T₀ : Triangle (DerivedCategory (SheafOfModules.{u}
      (ringedToposStructureRingSheaf D.B D.S D.containsLimitBase D.X.left))) :=
    Triangle.mk p (Pi.lift fun n : ℕ => Pi.π (fun n : ℕ => D.derivedSystem.obj ⟨n⟩) n -
      Pi.π (fun n : ℕ => D.derivedSystem.obj ⟨n⟩) (n + 1) ≫
        D.derivedSystem.map (homOfLE (Nat.le_succ n)).op) δ
  have hT' : T₀ ∈ distTriang _ := hT
  let T₁ :=
    ((smallEtaleDerivedTensor D.B D.S D.containsLimitBase D.X.left).obj E).mapTriangle.obj T₀
  have h₁ : T₁ ∈ distTriang _ :=
    ((smallEtaleDerivedTensor D.B D.S D.containsLimitBase D.X.left).obj E).map_distinguished _ hT'
  let T₂ := (derivedModulePushforward D.B D.S D.containsLimitBase D.X.hom).mapTriangle.obj T₁
  have h₂ : T₂ ∈ distTriang _ :=
    (derivedModulePushforward D.B D.S D.containsLimitBase D.X.hom).map_distinguished _ h₁
  let T₃ := (representedAffineDerivedSections D.B D.S D.containsLimitBase
    (limitBaseObject D.system D.B D.containsLimitBase)).mapTriangle.obj T₂
  have h₃ : T₃ ∈ distTriang _ := (representedAffineDerivedSections D.B D.S D.containsLimitBase
    (limitBaseObject D.system D.B D.containsLimitBase)).map_distinguished _ h₂
  let d : (∏ᶜ P) ⟶ ∏ᶜ P := Pi.lift (fun n ↦ Pi.π P n -
    Pi.π P (n + 1) ≫ D.derivedSystem.map (homOfLE (Nat.le_succ n)).op)
  let d' : (∏ᶜ fun n ↦ G.obj (P n)) ⟶ ∏ᶜ fun n ↦ G.obj (P n) := Pi.lift (fun n ↦
    Pi.π (fun n ↦ G.obj (P n)) n - Pi.π (fun n ↦ G.obj (P n)) (n + 1) ≫
      G.map (D.derivedSystem.map (homOfLE (Nat.le_succ n)).op))
  let e := asIso (piComparison G P)
  have hd : G.map d ≫ e.hom = e.hom ≫ d' :=
    Stacks.InverseSystem.map_piLift_sub_comp_piComparison G P
      fun n => D.derivedSystem.map (homOfLE (Nat.le_succ n)).op
  refine ⟨e.inv ≫ T₃.mor₃, isomorphic_distinguished _ h₃ _
    (Triangle.isoMk _ _ (Iso.refl _) e.symm e.symm ?_ ?_ ?_)⟩
  · show (G.map p ≫ e.hom) ≫ e.inv = 𝟙 _ ≫ G.map p
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Category.id_comp]
  · show d' ≫ e.inv = e.inv ≫ G.map d
    rw [← cancel_epi e.hom, e.hom_inv_id_assoc, ← Category.assoc, ← hd, Category.assoc,
      e.hom_inv_id, Category.comp_id]
  · exact (congrArg (fun z => (e.inv ≫ T₃.mor₃) ≫ z)
      (CategoryTheory.Functor.map_id _ _)).trans (Category.comp_id _)

end StandardModel

end FlatSheafExistenceSituation

end AlgebraicGeometry.Space
