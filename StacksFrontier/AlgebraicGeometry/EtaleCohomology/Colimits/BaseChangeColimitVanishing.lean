module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.LevelVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.BaseChangeColimitCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.BaseChangeAlgebraSystemInverseImages
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.QcqsBaseChangeEtaleCohomology
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Existence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Sheafification.SmallEtaleAbelian

/-!
# Vanishing on the limit of the base changes of a quasi-compact quasi-separated scheme

Let `T` be an affine scheme, `X ⟶ T` quasi-compact and quasi-separated, `(Z_i)` a directed
system of affine schemes over `T`, `Y_i = Z_i ×_T X` with limit `Y`, `p : Y ⟶ X` the projection
and `F` an abelian sheaf on `X_étale`. If `H^n(Y_i, π_i⁻¹ F) = 0` for every `i`, then
`H^n(Y, p⁻¹ F) = 0`
(`Stacks.EtaleCohomology.ColimitBaseChange.isZero_rightDerivedΓ_limit_of_levels`, in the right
derived functors of `CategoryTheory.Sheaf.Γ`, and
`Stacks.EtaleCohomology.ColimitBaseChange.subsingleton_sheafH_limit_of_levels'`, in
`CategoryTheory.Sheaf.H`).

This is `Stacks.EtaleCohomology.AffineLimitCohomology.subsingleton_sheafH_limit_of_levels` at the
system of base changes, a big étale site containing all the schemes involved being chosen once
and for all (`AlgebraicGeometry.BigEtaleSite.exists_contains_of_small`). No hypothesis is carried:
the levels are quasi-compact and quasi-separated because `X ⟶ T` is, and that is all the
Mayer–Vietoris induction behind the statement uses.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology.ColimitBaseChange

open Stacks.EtaleCohomology.BaseChangeAlgebraSystem Stacks.EtaleCohomology.AffineLimitCohomology
  Stacks.EtaleCohomology.TransitionBaseChange Stacks.EtaleCohomology.QcqsBaseChange

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
  (T : Scheme.{u}) [IsAffine T] (X : Over T) (Z : Iᵒᵖ ⥤ Over T) [∀ i, IsAffine (Z.obj i).left]
  (F : Sheaf X.left.smallEtaleTopology Ab.{u + 1})
  (cY : Cone (baseChange T X Z)) (hcY : IsLimit cY)
  (p : cY.pt ⟶ X.left) (hp : ∀ i, p = cY.π.app i ≫ levelProj T X Z i)

attribute [local instance] isContinuous_levelEtale

/-- Sheafification of abelian groups at the object universe of the small étale site. -/
local instance hasSheafify_smallEtale_objectUniverse' (Y : Scheme.{u}) :
    HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  Scheme.hasSheafify_smallEtaleTopology.{u, u + 1} Y

omit [Nonempty I] [IsDirected I (· ≤ ·)] [IsAffine T] [∀ i, IsAffine (Z.obj i).left] in
/-- A big étale site containing every level of the system of base changes and its limit. -/
theorem exists_bigEtaleSite_contains :
    ∃ B : BigEtaleSite.{u}, (∀ i, B.Contains ((baseChange T X Z).obj i)) ∧ B.Contains cY.pt := by
  let S₀ : Set Scheme.{u} := Set.range (baseChange T X Z).obj ∪ {cY.pt}
  have : Small.{u} S₀ := small_union _ _
  obtain ⟨B, hB⟩ := AlgebraicGeometry.BigEtaleSite.exists_contains_of_small S₀
  exact ⟨B, fun i ↦ hB _ (Or.inl ⟨i, rfl⟩), hB _ (Or.inr rfl)⟩

omit [Nonempty I] [IsDirected I (· ≤ ·)] [IsAffine T] in
/-- Every level of the system of base changes is quasi-separated when `X ⟶ T` is. -/
theorem quasiSeparatedSpace_baseChange_obj [QuasiSeparated X.hom] (i : Iᵒᵖ) :
    QuasiSeparatedSpace ((baseChange T X Z).obj i) :=
  @quasiSeparatedSpace_of_quasiSeparated _ _ (Limits.pullback.fst (Z.obj i).hom X.hom) inferInstance
    (quasiSeparated_baseChange_fst T X Z i)

include hcY hp in
/-- **Stacks 03Q6, vanishing form, in `Sheaf.H`.** If `H^n(Y_i, π_i⁻¹ F) = 0` for every `i`, then
`H^n(Y, p⁻¹ F) = 0`. -/
theorem subsingleton_sheafH_limit_of_levels' [QuasiCompact X.hom] [QuasiSeparated X.hom]
    (n : ℕ) (h : ∀ i, Subsingleton (Sheaf.H.{u + 1, u + 1} (levelSheaf T X Z F i) n)) :
    Subsingleton (Sheaf.H.{u + 1, u + 1} ((smallEtalePullbackAb p).obj F) n) := by
  obtain ⟨B, hD, hY⟩ := exists_bigEtaleSite_contains T X Z cY
  let E := affineEtaleSiteColimit.{u, u} (baseChange T X Z) cY B hD hY hcY
  let i₀ : (sys.{u, u} (baseChange T X Z) cY B hD hY hcY).I :=
    E.indexEquiv.inverse.obj (Opposite.op (Classical.arbitrary I))
  have : CompactSpace (levelScheme.{u, u} (baseChange T X Z) cY B hD hY hcY i₀) :=
    compactSpace_baseChange_obj T X Z _
  have : QuasiSeparatedSpace (levelScheme.{u, u} (baseChange T X Z) cY B hD hY hcY i₀) :=
    quasiSeparatedSpace_baseChange_obj T X Z _
  exact subsingleton_sheafH_limit_of_levels.{u, u} (baseChange T X Z) cY B hD hY hcY
    (baseChangeCoconeToX T X Z) p (fun _ ↦ hp _) F i₀ n (fun _ ↦ h _)

include hcY hp in
/-- **Stacks 03Q6, vanishing form.** If the right derived functors of global sections vanish in
degree `n` on every level `π_i⁻¹ F`, they vanish in degree `n` on `p⁻¹ F` over the limit. -/
theorem isZero_rightDerivedΓ_limit_of_levels [QuasiCompact X.hom] [QuasiSeparated X.hom] (n : ℕ)
    (h : ∀ i, IsZero
      (((Sheaf.Γ ((baseChange T X Z).obj i).smallEtaleTopology Ab.{u + 1}).rightDerived n).obj
        (levelSheaf T X Z F i))) :
    IsZero (((Sheaf.Γ cY.pt.smallEtaleTopology Ab.{u + 1}).rightDerived n).obj
      ((smallEtalePullbackAb p).obj F)) :=
  (Stacks.Cohomology.GlobalSections.subsingleton_sheafH_iff_isZero_rightDerivedΓ.{u + 1, u, u + 1}
      _ _ _).1
    (subsingleton_sheafH_limit_of_levels' T X Z F cY hcY p hp n fun i ↦
      (Stacks.Cohomology.GlobalSections.subsingleton_sheafH_iff_isZero_rightDerivedΓ.{u + 1, u,
        u + 1} _ _ _).2 (h i))

end Stacks.EtaleCohomology.ColimitBaseChange

end
