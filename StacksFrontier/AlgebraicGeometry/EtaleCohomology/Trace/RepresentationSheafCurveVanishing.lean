module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RepresentationSheafEffacementCriterion
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.CurveCohomologyTheorem
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.ProjectiveCurveBaseChange

/-!
# Vanishing of the étale cohomology of `X_{k̄}` with coefficients in a finite ring

Let `X` be a curve over a field `k` and `k̄` an algebraically closed extension. Every sheaf of
modules over a finite ring `Λ` is torsion (its sections are killed by `#Λ`), so by Tag 0A53 its
étale cohomology on `X_{k̄}` vanishes above degree two, and by Tag 0A54 above degree one when
`X_{k̄}` is affine. In the Tag 03VM argument this disposes of the degrees `i ≥ 3` (and `i = 2` in
the affine case) of the effacement of `(M, ρ) ↦ H^i(X_{k̄}, ℱ_ρ)`.

## Main results

* `Stacks.EtaleCohomology.torsionSheafProperty_etaleModuleUnderlyingAbelian` — a sheaf of modules
  over a finite ring is torsion.
* `Stacks.EtaleCohomology.isZero_rightDerived_fieldBaseChange_of_two_lt` and
  `Stacks.EtaleCohomology.isZero_rightDerived_fieldBaseChange_of_isAffine` — the vanishing.
* `AlgebraicGeometry.geometricRepresentationCohomology_unit_eq_zero_of_two_lt` — the effacement
  hypothesis of `elementwiseEffaceable_geometricRepresentationCohomology_of_forall_exists_unit` in
  degrees above two.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

/-- `Ext` of abelian sheaves on the small étale site at its object universe, pinned. -/
local instance (priority := 3000) hasExt_smallEtale_objectUniverse''
    (Y : Scheme.{u}) : HasExt.{u + 1} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
  haveI : IsGrothendieckAbelian.{u + 1} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
    Stacks.EtaleCohomology.isGrothendieckAbelian_sheaf_smallEtale_objectUniverse Y
  CategoryTheory.IsGrothendieckAbelian.hasExt _

/-- Sheafification of presheaves of `Λ`-modules on Mathlib's small étale site, pinned at
`u + 1`. -/
local instance (priority := 3000) etaleModules_hasSheafify_objectUniverse'' (Λ : Type) [Ring Λ]
    (Y : Scheme.{u}) : HasSheafify Y.smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
  etaleModules_hasSheafify.{u, 0} Λ Y

/-- Enough injectives for sheaves of `Λ`-modules on Mathlib's small étale site, pinned at
`u + 1`. -/
local instance (priority := 3000) etaleModules_enoughInjectives_objectUniverse'' (Λ : Type)
    [Ring Λ] (Y : Scheme.{u}) : EnoughInjectives (EtaleModules.{u, 0} Λ Y) :=
  etaleModules_enoughInjectives.{u, 0} Λ Y

variable (Λ : Type) [Ring Λ] [Finite Λ]

/-- **A sheaf of modules over a finite ring is torsion**: each of its sections is killed by `#Λ`,
which kills `Λ`. -/
theorem torsionSheafProperty_etaleModuleUnderlyingAbelian {Z : Scheme.{u}}
    (G : EtaleModules.{u, 0} Λ Z) :
    Stacks.Torsion.torsionSheafProperty Z.smallEtaleTopology
      ((etaleModuleUnderlyingAbelian Z Λ).obj G) := by
  intro U s
  refine ⟨⊤, Z.smallEtaleTopology.top_mem U, fun V g _ => ⟨Nat.card Λ, Nat.card_pos, ?_⟩⟩
  let t : G.obj.obj (Opposite.op V) := ((etaleModuleUnderlyingAbelian Z Λ).obj G).obj.map g.op s
  change Nat.card Λ • t = 0
  rw [← one_smul Λ t, ← smul_assoc, card_nsmul_eq_zero', zero_smul]

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (K : Type u) [Field K]
  [Algebra k K] [IsAlgClosed K]

omit [Finite Λ] in
/-- `H^q_Λ(Z, G) = 0` as soon as `H^q` of the underlying abelian sheaf vanishes. -/
theorem isZero_rightDerived_of_subsingleton_sheafH {Z : Scheme.{u}} (G : EtaleModules.{u, 0} Λ Z)
    (q : ℕ) (h : Subsingleton (Sheaf.H.{u + 1} ((etaleModuleUnderlyingAbelian Z Λ).obj G) q)) :
    IsZero (((etaleModuleGlobalSections.{u, 0} Λ Z).rightDerived q).obj G) := by
  rw [ModuleCat.isZero_iff_subsingleton]
  have : Subsingleton ↑((etaleModuleUnderlyingAbelian Z Λ ⋙
      Sheaf.functorH.{u + 1, u + 1, u, u + 1} Z.smallEtaleTopology q).obj G) := h
  exact ((ConcreteCategory.bijective_of_isIso
    ((etaleModuleCohomologyIsoFunctorH Λ q).hom.app G)).1).subsingleton

/-- **Tag 0A53 with coefficients in a finite ring**: on the base change `X_{k̄}` of a curve the
étale cohomology of a sheaf of `Λ`-modules vanishes above degree two. -/
theorem isZero_rightDerived_fieldBaseChange_of_two_lt (hcurve : IsCurve k f)
    (G : EtaleModules.{u, 0} Λ (Stacks.Frobenius.fieldBaseChange (Over.mk f) K)) {q : ℕ}
    (hq : 2 < q) :
    IsZero (((etaleModuleGlobalSections.{u, 0} Λ
      (Stacks.Frobenius.fieldBaseChange (Over.mk f) K)).rightDerived q).obj G) :=
  isZero_rightDerived_of_subsingleton_sheafH Λ G q
    ((ProjectiveCurveBaseChange.torsionSheafSituation.{0, u} f K hcurve _
      (torsionSheafProperty_etaleModuleUnderlyingAbelian Λ G)).isVanishingAboveDegreeTwo q hq)

/-- **Tag 0A54 with coefficients in a finite ring**: if `X_{k̄}` is affine, the étale cohomology of
a sheaf of `Λ`-modules on it vanishes above degree one. -/
theorem isZero_rightDerived_fieldBaseChange_of_isAffine (hcurve : IsCurve k f)
    [IsAffine (Stacks.Frobenius.fieldBaseChange (Over.mk f) K)]
    (G : EtaleModules.{u, 0} Λ (Stacks.Frobenius.fieldBaseChange (Over.mk f) K)) {q : ℕ}
    (hq : 1 < q) :
    IsZero (((etaleModuleGlobalSections.{u, 0} Λ
      (Stacks.Frobenius.fieldBaseChange (Over.mk f) K)).rightDerived q).obj G) :=
  isZero_rightDerived_of_subsingleton_sheafH Λ G q
    ((ProjectiveCurveBaseChange.torsionSheafSituation.{0, u} f K hcurve _
      (torsionSheafProperty_etaleModuleUnderlyingAbelian Λ G)).isAffineVanishingAboveDegreeOne
        (inferInstanceAs (IsAffine (Stacks.Frobenius.fieldBaseChange (Over.mk f) K))) q hq)

end Stacks.EtaleCohomology


namespace AlgebraicGeometry

open Stacks.EtaleCohomology Stacks.GroupCohomology

/-- Sheafification of presheaves of `Λ`-modules on Mathlib's small étale site, pinned at
`u + 1`. -/
local instance (priority := 3000) etaleModules_hasSheafify_objectUniverse_geometric (Λ : Type)
    [Ring Λ] (Y : Scheme.{u}) : HasSheafify Y.smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
  etaleModules_hasSheafify.{u, 0} Λ Y

/-- Enough injectives for sheaves of `Λ`-modules on Mathlib's small étale site, pinned at
`u + 1`. -/
local instance (priority := 3000) etaleModules_enoughInjectives_objectUniverse_geometric
    (Λ : Type) [Ring Λ] (Y : Scheme.{u}) : EnoughInjectives (EtaleModules.{u, 0} Λ Y) :=
  etaleModules_enoughInjectives.{u, 0} Λ Y

variable (B : BigEtaleSite.{u}) (X : B.Scheme) [ConnectedSpace X.1] (x : GeometricPoint X.1)
  (Λ : Type) [Ring Λ] [Finite Λ] {k : Type u} [Field k] (f : X.1 ⟶ Spec (.of k)) (K : Type u)
  [Field K] [Algebra k K] [IsAlgClosed K]

/-- **The effacement hypothesis above degree two.** For a curve `X` over `k` and `K`
algebraically closed, `H^{n+1}(X_K, ℱ_ρ) = 0` for `n + 1 > 2`, so every class there dies under
the unit of the identity cover. This is the hypothesis of
`AlgebraicGeometry.elementwiseEffaceable_geometricRepresentationCohomology_of_forall_exists_unit`
in those degrees. -/
theorem exists_unit_map_eq_zero_of_two_lt (hcurve : IsCurve k f)
    (M : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 x)) {n : ℕ}
    (hn : 2 < n + 1) (ξ : ((etaleModuleGlobalSections.{u, 0} Λ
        (Stacks.Frobenius.fieldBaseChange (Over.mk f) K)).rightDerived (n + 1)).obj
          ((geometricRepresentationSheaf B X x Λ f K).obj M)) :
    ∃ (Y : Scheme.{u}) (π : Y ⟶ X.1) (_ : IsFinite π) (_ : Etale π) (_ : Surjective π),
      ((etaleModuleGlobalSections.{u, 0} Λ
        (Stacks.Frobenius.fieldBaseChange (Over.mk f) K)).rightDerived (n + 1)).map
        ((etaleModuleInverseImage.{u, 0} Λ
          (pullback.fst (Over.mk f).hom (Stacks.Frobenius.specAlgebraMap k K))).map
          ((etaleModuleInverseImageAdj.{u, 0} Λ π).unit.app
            ((representationSheaf B X x Λ).obj M))) ξ = 0 := by
  have hz := isZero_rightDerived_fieldBaseChange_of_two_lt Λ f K hcurve
    ((geometricRepresentationSheaf B X x Λ f K).obj M) hn
  rw [ModuleCat.isZero_iff_subsingleton] at hz
  refine ⟨X.1, 𝟙 _, inferInstance, inferInstance, inferInstance, ?_⟩
  rw [Subsingleton.elim ξ 0]
  exact map_zero _

end AlgebraicGeometry

end
