module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveRepresentationCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricGlobalSectionsGaloisEquiv
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RepresentationNormalInvariants
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GeometricQuotientGaloisEquiv

/-!
# `H⁰(X_k̄, ℱ_ρ) = M^{π₁(X_k̄, η̄)}`, canonically and Galois-equivariantly

Let `X` be a geometrically connected smooth curve over `k`, `η̄` a geometric point of `X_k̄`, and
`N ⊆ π₁(X, η̄)` the image of `π₁(X_k̄, η̄)`. For a finite `Λ`-module `M` with a continuous action
`ρ` of `π₁(X, η̄)`, evaluation at `η̄` identifies `H⁰(X_k̄, ℱ_ρ)` with `M^{π₁(X_k̄, η̄)}`,
naturally in `ρ` and compatibly with the actions of `Gal(k̄/k) = π₁(X, η̄)/N`. This is the
degree-zero assertion of Remark 03VL.

The inclusion `M^N ⟶ M` induces a bijection `Γ(X_k̄, ℱ_{ρ^N}|) ⟶ Γ(X_k̄, ℱ_ρ|)`; since `N` acts
trivially on `M^N`, this reduces the statement to the case of a trivial geometric action, which is
`AlgebraicGeometry.geometricGlobalSectionsTrivialEquiv`.

## Main results

* `AlgebraicGeometry.geometricGlobalSectionsInvariantsEquiv`, with
  `AlgebraicGeometry.geometricGlobalSectionsInvariantsEquiv_naturality` and
  `AlgebraicGeometry.geometricGlobalSectionsInvariantsEquiv_galois`.
* `AlgebraicGeometry.bijective_globalSections_normalInvariantsι`.

## Implementation notes

The identification is evaluation at `η̄` and involves no choice. Only the proof that the map
`Γ(X_k̄, ℱ_{ρ^N}|) ⟶ Γ(X_k̄, ℱ_ρ|)` is bijective uses the existence-only identification
`AlgebraicGeometry.curveGlobalSectionsIsoInvariants`, through its naturality, which holds for any
of the choices made in it.

## References

* [Stacks Project, Tag 03VL](https://stacks.math.columbia.edu/tag/03VL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.GroupCohomology Stacks.Frobenius Stacks.EtaleCohomology

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (X : B.Scheme) {k : Type u} [Field k] (f : X.1 ⟶ Spec (.of k))
  [IsCurve k f] [Smooth f] [GeometricallyConnected f] (kbar : Type u) [Field kbar]
  [Algebra k kbar] [IsAlgClosed kbar] [Algebra.IsAlgebraic k kbar]
  (Λ : Type) [Ring Λ] [Fintype Λ]
  (y : GeometricPoint (fieldBaseChange (Over.mk f) kbar))

omit [Fintype Λ] in
/-- A morphism whose image under one of two isomorphic functors to modules is bijective has
bijective image under the other. -/
theorem bijective_map_of_natIso {C : Type*} [Category C] {F G : C ⥤ ModuleCat.{u + 1} Λ}
    (e : F ≅ G) {a b : C} (φ : a ⟶ b) (h : Function.Bijective (G.map φ)) :
    Function.Bijective (F.map φ) := by
  have hnat : F.map φ = e.hom.app a ≫ G.map φ ≫ e.inv.app b := by
    rw [← Category.assoc, ← e.hom.naturality φ, Category.assoc, Iso.hom_inv_id_app,
      Category.comp_id]
  have hcomp : ⇑(F.map φ) = e.inv.app b ∘ G.map φ ∘ e.hom.app a := by
    funext x
    rw [hnat]
    rfl
  rw [hcomp]
  exact (ConcreteCategory.bijective_of_isIso (e.inv.app b)).comp
    (h.comp (ConcreteCategory.bijective_of_isIso (e.hom.app a)))

omit [Fintype Λ] in
/-- Lifting the universe of modules preserves bijectivity of a linear map. -/
theorem bijective_uliftFunctor_map {A A' : ModuleCat.{u + 1} Λ} (g : A ⟶ A')
    (h : Function.Bijective g) :
    Function.Bijective ((ModuleCat.uliftFunctor.{0, u + 1} Λ).map g) :=
  ⟨fun _ _ hab ↦ ULift.ext (h.1 (congrArg ULift.down hab)),
    fun z ↦ ⟨⟨(h.2 z.down).choose⟩, ULift.ext (h.2 z.down).choose_spec⟩⟩

/-- The image `N` of `π₁(X_k̄, η̄) ⟶ π₁(X, η̄)`. -/
abbrev geometricFundamentalGroupRange :
    letI := connectedSpace_of_isCurve B X f
    letI := connectedSpace_fieldBaseChange f kbar
    Subgroup (EtaleFundamentalGroup X.1 (y.map (fieldBaseChangeObjProj B X f kbar
      (contains_fieldBaseChange_of_isCurve B X f kbar)).hom)) :=
  letI := connectedSpace_of_isCurve B X f
  letI := connectedSpace_fieldBaseChange f kbar
  (etaleFundamentalGroupMap (fieldBaseChangeObjProj B X f kbar
    (contains_fieldBaseChange_of_isCurve B X f kbar)).hom y).toMonoidHom.range

omit [Fintype Λ] in
/-- **Restricted to `π₁(X_k̄)`, the inclusion `M^N ⟶ M` is a bijection on invariants**: the
`π₁(X_k̄)`-invariants of `M` are `M^N`, all of which are `N`-invariant. -/
theorem bijective_invariants_res_normalInvariantsι [Finite Λ]
    (ρ : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom))) :
    letI := connectedSpace_of_isCurve B X f
    letI := connectedSpace_fieldBaseChange f kbar
    Function.Bijective ((finiteTypeContinuousModuleInvariants Λ
      (EtaleFundamentalGroup (fieldBaseChange (Over.mk f) kbar) y)).map
        ((finiteTypeContinuousModuleRes Λ (etaleFundamentalGroupMap
          (fieldBaseChangeObjProj B X f kbar (contains_fieldBaseChange_of_isCurve B X f kbar)).hom
            y)).map ((finiteTypeContinuousModuleNormalInvariantsι Λ
              (geometricFundamentalGroupRange B X f kbar y)).app ρ))) := by
  let := connectedSpace_of_isCurve B X f
  let := connectedSpace_fieldBaseChange f kbar
  refine ⟨fun a b h ↦ ?_, fun z ↦ ?_⟩
  · exact Subtype.ext (Subtype.ext (congrArg (fun w ↦ (w.1 : _)) h))
  · refine ⟨⟨⟨z.1, ?_⟩, fun g ↦ Subtype.ext (z.2 g)⟩, rfl⟩
    rintro n ⟨g, rfl⟩
    exact z.2 g

omit [Fintype Λ] in
/-- **The inclusion `M^N ⟶ M` induces a bijection `Γ(X_k̄, ℱ_{ρ^N}|) ⟶ Γ(X_k̄, ℱ_ρ|)`.** Through
the identification of both sides with `π₁(X_k̄)`-invariants (natural in the representation, for
whichever choices it is built with), this is `bijective_invariants_res_normalInvariantsι`. -/
theorem bijective_globalSections_normalInvariantsι [Finite Λ]
    (ρ : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom))) :
    letI := connectedSpace_of_isCurve B X f
    letI := connectedSpace_fieldBaseChange f kbar
    Function.Bijective ((geometricRepresentationSheaf B X (y.map (fieldBaseChangeObjProj B X f kbar
        (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) Λ f kbar ⋙
      etaleModuleGlobalSections.{u, 0} Λ (fieldBaseChange (Over.mk f) kbar)).map
        ((finiteTypeContinuousModuleNormalInvariantsι Λ
          (geometricFundamentalGroupRange B X f kbar y)).app ρ)) := by
  let := connectedSpace_of_isCurve B X f
  let := connectedSpace_fieldBaseChange f kbar
  exact bijective_map_of_natIso Λ (curveGlobalSectionsIsoInvariants B X f kbar Λ y) _
    (bijective_uliftFunctor_map Λ _ (bijective_invariants_res_normalInvariantsι B X f kbar Λ y ρ))

section Canonical

omit [Fintype Λ] [Smooth f] in
/-- The `π₁(X_k̄)`-action on `M^N` is trivial. -/
theorem normalInvariants_geometric_trivial [Finite Λ]
    (ρ : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom))) :
    letI := connectedSpace_of_isCurve B X f
    letI := connectedSpace_fieldBaseChange f kbar
    ∀ g, (finiteTypeContinuousModuleRepresentation Λ _
        ((finiteTypeContinuousModuleNormalInvariants Λ
          (geometricFundamentalGroupRange B X f kbar y)).obj ρ))
      (etaleFundamentalGroupMap (fieldBaseChangeObjProj B X f kbar
        (contains_fieldBaseChange_of_isCurve B X f kbar)).hom y g) = 1 := by
  let := connectedSpace_of_isCurve B X f
  let := connectedSpace_fieldBaseChange f kbar
  intro g
  exact finiteTypeContinuousModuleNormalInvariants_rho_eq_one Λ _ ρ _ ⟨g, rfl⟩

/-- **The evaluation at `η̄` of a global section of `ℱ_ρ|_{X_k̄}` factors through `M^N`**: it is
the evaluation for `ρ^N` followed by the inclusion, along the bijection
`Γ(X_k̄, ℱ_{ρ^N}|) ⟶ Γ(X_k̄, ℱ_ρ|)`. -/
theorem geometricGlobalSectionsEval_normalInvariantsι
    (ρ : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom)))
    (w : letI := connectedSpace_of_isCurve B X f
      ↑((etaleModuleGlobalSections.{u, 0} Λ (fieldBaseChange (Over.mk f) kbar)).obj
        (geometricRepresentationRestriction B X f kbar Λ y
          ((finiteTypeContinuousModuleNormalInvariants Λ
            (geometricFundamentalGroupRange B X f kbar y)).obj ρ)))) :
    letI := connectedSpace_of_isCurve B X f
    geometricGlobalSectionsEval B X f kbar Λ y ρ
        ((etaleModuleGlobalSections.{u, 0} Λ (fieldBaseChange (Over.mk f) kbar)).map
          ((etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj (Over.mk f) kbar)).map
            ((representationSheaf B X (y.map (fieldBaseChangeObjProj B X f kbar
              (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) Λ).map
                ((finiteTypeContinuousModuleNormalInvariantsι Λ
                  (geometricFundamentalGroupRange B X f kbar y)).app ρ))) w) =
      (show ↥(normalInvariantsSubmodule Λ (geometricFundamentalGroupRange B X f kbar y)
          (finiteTypeContinuousModuleRepresentation Λ _ ρ)) from
        geometricGlobalSectionsEval B X f kbar Λ y _ w).1 :=
  geometricGlobalSectionsEval_naturality B X f kbar Λ y _ w

/-- **Every global section of `ℱ_ρ|_{X_k̄}` comes from `ℱ_{ρ^N}|_{X_k̄}`.** -/
theorem exists_globalSections_normalInvariantsι (ρ : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom)))
    (z : (letI := connectedSpace_of_isCurve B X f
      ↑((etaleModuleGlobalSections.{u, 0} Λ (fieldBaseChange (Over.mk f) kbar)).obj
        (geometricRepresentationRestriction B X f kbar Λ y ρ)))) :
    letI := connectedSpace_of_isCurve B X f
    ∃ w : ↑((etaleModuleGlobalSections.{u, 0} Λ (fieldBaseChange (Over.mk f) kbar)).obj
        (geometricRepresentationRestriction B X f kbar Λ y
          ((finiteTypeContinuousModuleNormalInvariants Λ
            (geometricFundamentalGroupRange B X f kbar y)).obj ρ))),
      (etaleModuleGlobalSections.{u, 0} Λ (fieldBaseChange (Over.mk f) kbar)).map
          ((etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj (Over.mk f) kbar)).map
            ((representationSheaf B X (y.map (fieldBaseChangeObjProj B X f kbar
              (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) Λ).map
                ((finiteTypeContinuousModuleNormalInvariantsι Λ
                  (geometricFundamentalGroupRange B X f kbar y)).app ρ))) w = z :=
  (bijective_globalSections_normalInvariantsι B X f kbar Λ y ρ).2 z

/-- The evaluation at `η̄` of a global section of `ℱ_ρ|_{X_k̄}` is `π₁(X_k̄)`-invariant. -/
theorem geometricGlobalSectionsEval_mem_invariants (ρ : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom)))
    (z : (letI := connectedSpace_of_isCurve B X f
      ↑((etaleModuleGlobalSections.{u, 0} Λ (fieldBaseChange (Over.mk f) kbar)).obj
        (geometricRepresentationRestriction B X f kbar Λ y ρ)))) :
    letI := connectedSpace_of_isCurve B X f
    letI := connectedSpace_fieldBaseChange f kbar
    geometricGlobalSectionsEval B X f kbar Λ y ρ z ∈
      finiteTypeContinuousModuleInvariantsSubmodule Λ
        (EtaleFundamentalGroup (fieldBaseChange (Over.mk f) kbar) y)
        ((finiteTypeContinuousModuleRes Λ (etaleFundamentalGroupMap
          (fieldBaseChangeObjProj B X f kbar (contains_fieldBaseChange_of_isCurve B X f kbar)).hom
            y)).obj ρ) := by
  let := connectedSpace_of_isCurve B X f
  let := connectedSpace_fieldBaseChange f kbar
  obtain ⟨w, rfl⟩ := exists_globalSections_normalInvariantsι B X f kbar Λ y ρ z
  rw [geometricGlobalSectionsEval_normalInvariantsι]
  intro g
  exact (show ↥(normalInvariantsSubmodule Λ (geometricFundamentalGroupRange B X f kbar y)
      (finiteTypeContinuousModuleRepresentation Λ _ ρ)) from
    geometricGlobalSectionsEval B X f kbar Λ y _ w).2 _ ⟨g, rfl⟩

/-- The evaluation at `η̄` as a `Λ`-linear map into the `π₁(X_k̄)`-invariants. -/
def geometricGlobalSectionsInvariantsMap
    (ρ : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom))) :
    letI := connectedSpace_of_isCurve B X f
    letI := connectedSpace_fieldBaseChange f kbar
    ↑((etaleModuleGlobalSections.{u, 0} Λ (fieldBaseChange (Over.mk f) kbar)).obj
        (geometricRepresentationRestriction B X f kbar Λ y ρ)) →ₗ[Λ]
      ↑((finiteTypeContinuousModuleInvariants Λ
        (EtaleFundamentalGroup (fieldBaseChange (Over.mk f) kbar) y)).obj
          ((finiteTypeContinuousModuleRes Λ (etaleFundamentalGroupMap
            (fieldBaseChangeObjProj B X f kbar (contains_fieldBaseChange_of_isCurve B X f kbar)).hom
              y)).obj ρ)) :=
  letI := connectedSpace_of_isCurve B X f
  letI := connectedSpace_fieldBaseChange f kbar
  LinearMap.codRestrict _
    { toFun := geometricGlobalSectionsEval B X f kbar Λ y ρ
      map_add' := geometricGlobalSectionsEval_add B X f kbar Λ y ρ
      map_smul' := geometricGlobalSectionsEval_smul B X f kbar Λ y ρ }
    (geometricGlobalSectionsEval_mem_invariants B X f kbar Λ y ρ)

/-- **The evaluation at `η̄` identifies `Γ(X_k̄, ℱ_ρ|)` with the `π₁(X_k̄)`-invariants.** Through
the bijection `Γ(X_k̄, ℱ_{ρ^N}|) ⟶ Γ(X_k̄, ℱ_ρ|)` it is the evaluation for the representation
`ρ^N`, trivial on `π₁(X_k̄)`, which is bijective onto `M^N`. -/
theorem bijective_geometricGlobalSectionsInvariantsMap (ρ : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom))) :
    Function.Bijective (geometricGlobalSectionsInvariantsMap B X f kbar Λ y ρ) := by
  let := connectedSpace_of_isCurve B X f
  let := connectedSpace_fieldBaseChange f kbar
  have hN := bijective_geometricGlobalSectionsEval B X f kbar Λ y _
    (normalInvariants_geometric_trivial B X f kbar Λ y ρ)
  refine ⟨fun z₁ z₂ h ↦ ?_, fun m ↦ ?_⟩
  · obtain ⟨w₁, rfl⟩ := exists_globalSections_normalInvariantsι B X f kbar Λ y ρ z₁
    obtain ⟨w₂, rfl⟩ := exists_globalSections_normalInvariantsι B X f kbar Λ y ρ z₂
    have h' := congrArg Subtype.val h
    change geometricGlobalSectionsEval B X f kbar Λ y ρ _ =
      geometricGlobalSectionsEval B X f kbar Λ y ρ _ at h'
    rw [geometricGlobalSectionsEval_normalInvariantsι,
      geometricGlobalSectionsEval_normalInvariantsι] at h'
    rw [hN.1 (Subtype.ext h')]
  · obtain ⟨w, hw⟩ := hN.2 ⟨m.1, by
      rintro n ⟨g, rfl⟩
      exact m.2 g⟩
    refine ⟨(etaleModuleGlobalSections.{u, 0} Λ (fieldBaseChange (Over.mk f) kbar)).map
      ((etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj (Over.mk f) kbar)).map
        ((representationSheaf B X (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) Λ).map
            ((finiteTypeContinuousModuleNormalInvariantsι Λ
              (geometricFundamentalGroupRange B X f kbar y)).app ρ))) w, Subtype.ext ?_⟩
    show geometricGlobalSectionsEval B X f kbar Λ y ρ _ = _
    rw [geometricGlobalSectionsEval_normalInvariantsι]
    exact congrArg Subtype.val hw

/-- **Stacks Project, Tag 03VL, degree zero, canonically: `H⁰(X_k̄, ℱ_ρ) = M^{π₁(X_k̄, η̄)}`.** The
evaluation at the geometric point `η̄` of `X_k̄` identifies the global sections of the restriction
of `ℱ_ρ` to `X_k̄` with the `π₁(X_k̄, η̄)`-invariants of `M`. It involves no choice: it is built
from the explicit sheaf `ℱ_ρ` of Tag 0DV5 and evaluation, not from the existence-only comparison
of Tag 0DV6. Its naturality in `ρ` is `geometricGlobalSectionsInvariantsEquiv_naturality` and its
Galois equivariance `geometricGlobalSectionsInvariantsEquiv_galois`. The source states this for `X`
projective and `#Λ ∈ k^*`; neither is used. -/
@[stacks 03VL "H⁰(X_k̄, ℱ_ρ) = M^{π₁(X_k̄,η̄)}: the canonical identification, by evaluation at η̄"]
def geometricGlobalSectionsInvariantsEquiv (ρ : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom))) :
    letI := connectedSpace_of_isCurve B X f
    letI := connectedSpace_fieldBaseChange f kbar
    ↑((etaleModuleGlobalSections.{u, 0} Λ (fieldBaseChange (Over.mk f) kbar)).obj
        (geometricRepresentationRestriction B X f kbar Λ y ρ)) ≃ₗ[Λ]
      ↑((finiteTypeContinuousModuleInvariants Λ
        (EtaleFundamentalGroup (fieldBaseChange (Over.mk f) kbar) y)).obj
          ((finiteTypeContinuousModuleRes Λ (etaleFundamentalGroupMap
            (fieldBaseChangeObjProj B X f kbar (contains_fieldBaseChange_of_isCurve B X f kbar)).hom
              y)).obj ρ)) :=
  LinearEquiv.ofBijective _ (bijective_geometricGlobalSectionsInvariantsMap B X f kbar Λ y ρ)

/-- The identification is the evaluation at `η̄`. -/
theorem geometricGlobalSectionsInvariantsEquiv_apply (ρ : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom)))
    (z : letI := connectedSpace_of_isCurve B X f
      ↑((etaleModuleGlobalSections.{u, 0} Λ (fieldBaseChange (Over.mk f) kbar)).obj
        (geometricRepresentationRestriction B X f kbar Λ y ρ))) :
    letI := connectedSpace_of_isCurve B X f
    letI := connectedSpace_fieldBaseChange f kbar
    (geometricGlobalSectionsInvariantsEquiv B X f kbar Λ y ρ z).1 =
      geometricGlobalSectionsEval B X f kbar Λ y ρ z :=
  rfl

/-- **Stacks Project, Tag 03VL, degree zero: the identification is natural in `ρ`.** For
`φ : ρ ⟶ ρ'`, it carries the map induced by `φ` on global sections to `φ` on invariants. -/
@[stacks 03VL "H⁰(X_k̄, ℱ_ρ) = M^{π₁(X_k̄,η̄)} functorially in ρ"]
theorem geometricGlobalSectionsInvariantsEquiv_naturality
    {ρ ρ' : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom))} (φ : ρ ⟶ ρ')
    (z : letI := connectedSpace_of_isCurve B X f
      ↑((etaleModuleGlobalSections.{u, 0} Λ (fieldBaseChange (Over.mk f) kbar)).obj
        (geometricRepresentationRestriction B X f kbar Λ y ρ))) :
    letI := connectedSpace_of_isCurve B X f
    letI := connectedSpace_fieldBaseChange f kbar
    (geometricGlobalSectionsInvariantsEquiv B X f kbar Λ y ρ'
        ((etaleModuleGlobalSections.{u, 0} Λ (fieldBaseChange (Over.mk f) kbar)).map
          ((etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj (Over.mk f) kbar)).map
            ((representationSheaf B X (y.map (fieldBaseChangeObjProj B X f kbar
              (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) Λ).map φ)) z)).1 =
      φ.hom.hom.hom.hom.hom (geometricGlobalSectionsInvariantsEquiv B X f kbar Λ y ρ z).1 := by
  rw [geometricGlobalSectionsInvariantsEquiv_apply, geometricGlobalSectionsInvariantsEquiv_apply]
  exact geometricGlobalSectionsEval_naturality B X f kbar Λ y φ z

/-- **Stacks Project, Tag 03VL, degree zero: the identification is Galois-equivariant.** For
`γ ∈ π₁(X, η̄)` with image `σ ∈ Aut(k̄/k) = π₁(X, η̄)/π₁(X_k̄, η̄)`, it carries the action of `σ`
on `H⁰(X_k̄, ℱ_ρ)` (through `id × Spec σ` on `X_k̄`) to the action of `ρ(γ)` on
`M^{π₁(X_k̄, η̄)}`. -/
@[stacks 03VL "H⁰(X_k̄, ℱ_ρ) = M^{π₁(X_k̄,η̄)} as Gal(k̄/k) = π₁(X,η̄)/π₁(X_k̄,η̄)-modules"]
theorem geometricGlobalSectionsInvariantsEquiv_galois (ρ : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom)))
    (γ : letI := connectedSpace_of_isCurve B X f
      EtaleFundamentalGroup X.1 (y.map (fieldBaseChangeObjProj B X f kbar
        (contains_fieldBaseChange_of_isCurve B X f kbar)).hom))
    (z : letI := connectedSpace_of_isCurve B X f
      ↑((etaleModuleGlobalSections.{u, 0} Λ (fieldBaseChange (Over.mk f) kbar)).obj
        (geometricRepresentationRestriction B X f kbar Λ y ρ))) :
    letI := connectedSpace_of_isCurve B X f
    letI := connectedSpace_fieldBaseChange f kbar
    (geometricGlobalSectionsInvariantsEquiv B X f kbar Λ y ρ
        ((fieldBaseChangeGlobalSectionsGaloisAction Λ (Over.mk f) kbar
          (geometricQuotientGaloisEquiv B X f kbar y (QuotientGroup.mk γ)) _).hom z)).1 =
      (finiteTypeContinuousModuleRepresentation Λ _ ρ) γ
        (geometricGlobalSectionsInvariantsEquiv B X f kbar Λ y ρ z).1 := by
  let := connectedSpace_of_isCurve B X f
  let := connectedSpace_fieldBaseChange f kbar
  obtain ⟨w, rfl⟩ := exists_globalSections_normalInvariantsι B X f kbar Λ y ρ z
  have hnat := ConcreteCategory.congr_hom
    (fieldBaseChangeGlobalSectionsGaloisAction_naturality Λ (Over.mk f) kbar
      (geometricQuotientGaloisEquiv B X f kbar y (QuotientGroup.mk γ))
      ((representationSheaf B X (y.map (fieldBaseChangeObjProj B X f kbar
        (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) Λ).map
          ((finiteTypeContinuousModuleNormalInvariantsι Λ
            (geometricFundamentalGroupRange B X f kbar y)).app ρ))) w
  simp only [ConcreteCategory.comp_apply] at hnat
  set ι := (etaleModuleGlobalSections.{u, 0} Λ (fieldBaseChange (Over.mk f) kbar)).map
    ((etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj (Over.mk f) kbar)).map
      ((representationSheaf B X (y.map (fieldBaseChangeObjProj B X f kbar
        (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) Λ).map
          ((finiteTypeContinuousModuleNormalInvariantsι Λ
            (geometricFundamentalGroupRange B X f kbar y)).app ρ))) with hι
  have hact : (fieldBaseChangeGlobalSectionsGaloisAction Λ (Over.mk f) kbar
      (geometricQuotientGaloisEquiv B X f kbar y (QuotientGroup.mk γ))
        ((representationSheaf B X (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) Λ).obj ρ)).hom (ι w) =
      ι ((fieldBaseChangeGlobalSectionsGaloisAction Λ (Over.mk f) kbar
        (geometricQuotientGaloisEquiv B X f kbar y (QuotientGroup.mk γ)) _).hom w) :=
    hnat.symm
  rw [geometricGlobalSectionsInvariantsEquiv_apply, geometricGlobalSectionsInvariantsEquiv_apply,
    hact, hι, geometricGlobalSectionsEval_normalInvariantsι,
    geometricGlobalSectionsEval_normalInvariantsι,
    geometricGlobalSectionsEval_galois B X f kbar Λ y _
      (normalInvariants_geometric_trivial B X f kbar Λ y ρ) γ w]
  rfl

end Canonical

end AlgebraicGeometry
