module

public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationModuleFullness
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ConditionComparisons
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingFiniteTypeLimitImage
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompact

/-!
# The fullness clause of Stacks 07V7 for a system of base changes

Let `D` be a cofiltered inverse system of quasi-compact quasi-separated algebraic spaces with
affine transition morphisms, and let `r : R ⟶ X_i` be a morphism from a quasi-compact
quasi-separated algebraic space to a stage.  The base changes `X_j ×_{X_i} R` form again such a
system, with limit `X ×_{X_i} R`, and the fullness clause applied to it reads: a morphism between
the inverse images to `X ×_{X_i} R` of two finitely presented `𝒪_R`-modules is, at a later stage,
the restriction of a morphism between their inverse images to `X_j ×_{X_i} R`.

## Main results

* `AlgebraicGeometry.Space.exists_homRestrict_eq_of_baseChange`: that statement.

## References

* [Stacks Project, Tag 07V7](https://stacks.math.columbia.edu/tag/07V7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Cardinal

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (hZ : B.Contains (⊤_ Scheme.{u}))
variable {I : Type u} [Category.{u} I] [IsCofiltered I]
  (D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
  (hL : HasSiteLimit B S hS D)
  (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
variable {i : I} (R : AlgebraicSpaces B S hS) (r : R ⟶ stageAlgebraicSpace B S hS D hD i)

omit [IsCofiltered I] in
include hL in
/-- The members of a system of base changes along a morphism from a quasi-compact space are
quasi-compact. -/
theorem isQuasiCompactSpace_stageBaseChangeSystem (hRqc : IsQuasiCompactSpace B S hS R.1)
    (j : Over i) : IsQuasiCompactSpace B S hS ((stageBaseChangeSystem B S hS D i r.hom).obj j) :=
  isQuasiCompactSpace_source_of_isQuasiCompact B S hS R.2 hRqc
    (isQuasiCompact_of_isAffineHom' B S hS _
      (isAlgebraicSpace_stageBaseChangeSystem B S hS D hD R r j) R.2
      (IsAffineHom.of_isPullback (isPullback_stageBaseChangeSystem B S hS D i r.hom j)
        (hL.1 j.hom)))

omit [IsCofiltered I] in
/-- The members of a system of base changes of quasi-separated spaces are quasi-separated. -/
theorem isAbsolutelyQuasiSeparated_stageBaseChangeSystem
    (hQs : ∀ i, IsAbsolutelyQuasiSeparated B S hS hZ (D.obj i))
    (hRqs : IsAbsolutelyQuasiSeparated B S hS hZ R.1) (j : Over i) :
    IsAbsolutelyQuasiSeparated B S hS hZ ((stageBaseChangeSystem B S hS D i r.hom).obj j) :=
  isAbsolutelyQuasiSeparated_pullback B S hS hZ _ _ (hD j.left) R.2 (hD i) (hQs j.left) hRqs

/-- **The fullness clause of Stacks 07V7 for a system of base changes.**  For a morphism
`r : R ⟶ X_i` from a quasi-compact quasi-separated algebraic space and two finitely presented
`𝒪_R`-modules `M`, `N`, every morphism between their inverse images to `X ×_{X_i} R` is, at a
later stage `j`, the restriction of a morphism between their inverse images to `X_j ×_{X_i} R`;
both are compared on the chosen limit of the system of base changes, through
`AlgebraicGeometry.Space.limitBaseChangeSystemIso`. -/
theorem exists_homRestrict_eq_of_baseChange
    (_hQc : ∀ i, IsQuasiCompactSpace B S hS (D.obj i))
    (hQs : ∀ i, IsAbsolutelyQuasiSeparated B S hS hZ (D.obj i))
    (hRqc : IsQuasiCompactSpace B S hS R.1) (hRqs : IsAbsolutelyQuasiSeparated B S hS hZ R.1)
    {M N : Modules.{u, u} B S hS R.1 R.2}
    (hM : M.IsFinitePresentationOnSite) (hN : N.IsFinitePresentationOnSite)
    (φ : (modulePullback B S hS (limitBaseChangeSnd B S hS D hL hD R r)).obj M ⟶
      (modulePullback B S hS (limitBaseChangeSnd B S hS D hL hD R r)).obj N) :
    ∃ (j : Over i) (ψ : (modulePullback B S hS (stageBaseChangeSpaceSnd B S hS D hD R r j)).obj M ⟶
        (modulePullback B S hS (stageBaseChangeSpaceSnd B S hS D hD R r j)).obj N),
      moduleHomRestrict M N (limitSpaceProjection B S hS (stageBaseChangeSystem B S hS D i r.hom)
          (hasSiteLimit_stageBaseChangeSystem B S hS D hL hD R r)
          (isAlgebraicSpace_stageBaseChangeSystem B S hS D hD R r) j)
        (stageBaseChangeSpaceSnd B S hS D hD R r j)
        (limitBaseChangeSystemIso B S hS D hL hD R r ≫
          limitBaseChangeSnd B S hS D hL hD R r)
        (limitBaseChangeSystemIso_comp_snd B S hS D hL hD R r j).symm ψ =
      moduleHomRestrict M N (limitBaseChangeSystemIso B S hS D hL hD R r)
        (limitBaseChangeSnd B S hS D hL hD R r) _ rfl φ := by
  let b : Over i := Over.mk (𝟙 i)
  let sb := stageBaseChangeSpaceSnd B S hS D hD R r b
  let θ := limitBaseChangeSystemIso B S hS D hL hD R r
  let lbs := limitBaseChangeSnd B S hS D hL hD R r
  let lamb := limitSpaceProjection B S hS (stageBaseChangeSystem B S hS D i r.hom)
    (hasSiteLimit_stageBaseChangeSystem B S hS D hL hD R r)
    (isAlgebraicSpace_stageBaseChangeSystem B S hS D hD R r) b
  have hθ : θ ≫ lbs = lamb ≫ sb :=
    limitBaseChangeSystemIso_comp_snd B S hS D hL hD R r b
  obtain ⟨j, e, ψ', hψ'⟩ := exists_homRestrict_eq_limitProjection B S hS hZ
    (stageBaseChangeSystem B S hS D i r.hom) (hasSiteLimit_stageBaseChangeSystem B S hS D hL hD R r)
    (isAlgebraicSpace_stageBaseChangeSystem B S hS D hD R r)
    (isQuasiCompactSpace_stageBaseChangeSystem B S hS D hL hD R r hRqc)
    (isAbsolutelyQuasiSeparated_stageBaseChangeSystem B S hS hZ D hD R r hQs hRqs) b
    (isFinitePresentationOnSite_modulePullback B S hS sb M hM)
    (isFinitePresentationOnSite_modulePullback B S hS sb N hN)
    (homConjInv sb lamb (moduleHomRestrict M N θ lbs (lamb ≫ sb) hθ φ))
  have he :
      stageTransition B S hS _ (isAlgebraicSpace_stageBaseChangeSystem B S hS D hD R r) e ≫ sb =
      stageBaseChangeSpaceSnd B S hS D hD R r j :=
    ObjectProperty.hom_ext _ (stageBaseChangeSystem_map_comp_snd B S hS D i r.hom e)
  obtain ⟨ψ, hψ⟩ := exists_homRestrict_eq_of_homRestrict_eq_homConjInv sb _ _ lamb
    (limitSpaceProjection_comp B S hS _ _ _ e) _ he ψ' _ hψ'
  refine ⟨j, ψ, ?_⟩
  have key : ∀ (q : _ ⟶ R) (hq₁ : _) (hq₂ : _), lamb ≫ sb = q →
      moduleHomRestrict M N (limitSpaceProjection B S hS (stageBaseChangeSystem B S hS D i r.hom)
          (hasSiteLimit_stageBaseChangeSystem B S hS D hL hD R r)
          (isAlgebraicSpace_stageBaseChangeSystem B S hS D hD R r) j)
        (stageBaseChangeSpaceSnd B S hS D hD R r j) q hq₁ ψ =
        moduleHomRestrict M N θ lbs q hq₂ φ := by
    rintro _ _ _ rfl
    exact hψ
  exact key _ _ _ hθ.symm

omit [IsCofiltered I] in
/-- The leg at `j` of the cone obtained by base changing the limit cone of `D` along `r'`,
followed by the first projection of the `j`-th base change, is the first projection of
`limit D ×_{D i} R'` followed by the limit projection to `D.obj j.left`. -/
theorem baseChangeCone_π_comp_fst {R' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (r' : R' ⟶ D.obj i)
    (j : Over i) :
    ((Over.forget R').mapCone ((Over.pullback r').mapCone ((limit.cone D).overPost i))).π.app j ≫
        stageBaseChangeSystemFst B S hS D i r' j =
      pullback.fst (limit.π D i) r' ≫ limit.π D j.left := by
  dsimp [stageBaseChangeSystemFst, Over.pullback, Over.post, Cone.overPost]
  simp only [Over.homMk_left, pullback.lift_fst]
  rfl

/-- The projection of a member of the system of base changes to its stage, as a morphism of
algebraic spaces. -/
noncomputable def stageBaseChangeSpaceFst (j : Over i) :
    stageAlgebraicSpace B S hS (stageBaseChangeSystem B S hS D i r.hom)
      (isAlgebraicSpace_stageBaseChangeSystem B S hS D hD R r) j ⟶
        stageAlgebraicSpace B S hS D hD j.left :=
  ObjectProperty.homMk (stageBaseChangeSystemFst B S hS D i r.hom j)

/-- Under `limitBaseChangeSystemIso`, the first projection of the base change of the limit
followed by the projection to the stage `j.left` agrees with the projection of the limit of the
system of base changes to its `j`-th member followed by `stageBaseChangeSpaceFst`. -/
theorem limitBaseChangeSystemIso_comp_fst (j : Over i) :
    limitBaseChangeSystemIso B S hS D hL hD R r ≫
        limitBaseChangeFst B S hS D hL hD R r ≫
          limitSpaceProjection B S hS D hL hD j.left =
      limitSpaceProjection B S hS (stageBaseChangeSystem B S hS D i r.hom)
          (hasSiteLimit_stageBaseChangeSystem B S hS D hL hD R r)
          (isAlgebraicSpace_stageBaseChangeSystem B S hS D hD R r) j ≫
        stageBaseChangeSpaceFst B S hS D hD R r j := by
  apply ObjectProperty.hom_ext
  have e := baseChangeCone_π_comp_fst B S hS D r.hom j
  have e2 := IsLimit.conePointUniqueUpToIso_hom_comp (limit.isLimit _)
    (isLimitPullbackLimitOverPost B S hS D i r.hom) j
  exact (congrArg (fun z => _ ≫ z) e.symm).trans
    ((Category.assoc _ _ _).symm.trans ((congrArg (fun z => z ≫ _) e2).trans rfl))

/-- The inverse of `limitBaseChangeSystemIso`. -/
noncomputable def limitBaseChangeSystemIsoInv :
    limitBaseChangeSpace B S hS D hL hD R r ⟶
      limitSpace B S hS (stageBaseChangeSystem B S hS D i r.hom)
        (hasSiteLimit_stageBaseChangeSystem B S hS D hL hD R r) :=
  ObjectProperty.homMk ((limit.isLimit _).conePointUniqueUpToIso
    (isLimitPullbackLimitOverPost B S hS D i r.hom)).inv

/-- The composite of `limitBaseChangeSystemIsoInv` and `limitBaseChangeSystemIso` is the identity
of the limit of the system of base changes. -/
theorem limitBaseChangeSystemIsoInv_comp :
    limitBaseChangeSystemIsoInv B S hS D hL hD R r ≫
        limitBaseChangeSystemIso B S hS D hL hD R r = 𝟙 _ :=
  ObjectProperty.hom_ext _ (Iso.inv_hom_id _)

/-- **The faithfulness clause of Stacks 07V7 for a system of base changes, for modules on the
base.**  Two morphisms between finitely presented `𝒪_R`-modules whose inverse images to the base
change `X ×_{X_i} R` of the limit agree have equal inverse images to the base change
`X_j ×_{X_i} R` of some later stage. -/
theorem eventually_map_eq_of_baseChange' (hRqc : IsQuasiCompactSpace B S hS R.1)
    {M N : Modules.{u, u} B S hS R.1 R.2}
    (hM : M.IsFinitePresentationOnSite) (hN : N.IsFinitePresentationOnSite) (x y : M ⟶ N)
    (h : (modulePullback B S hS (limitBaseChangeSnd B S hS D hL hD R r)).map x =
      (modulePullback B S hS (limitBaseChangeSnd B S hS D hL hD R r)).map y) :
    ∃ j : Over i,
      (modulePullback B S hS (stageBaseChangeSpaceSnd B S hS D hD R r j)).map x =
        (modulePullback B S hS (stageBaseChangeSpaceSnd B S hS D hD R r j)).map y := by
  have hqc : IsQuasiCompactSpace B S hS
      ((stageBaseChangeSystem B S hS D i r.hom).obj (Over.mk (𝟙 i))) := by
    have hP : IsPullback (pullback.fst (D.map (𝟙 i)) r.hom) (pullback.snd (D.map (𝟙 i)) r.hom)
        (𝟙 _) r.hom := by
      simpa only [D.map_id] using IsPullback.of_hasPullback (D.map (𝟙 i)) r.hom
    exact isQuasiCompactSpace_of_iso B S hS
      (hP.isoIsPullback _ _ (IsPullback.id_vert r.hom)).symm hRqc
  have h1 := map_comp_eq_of_map_map_eq B S hS
    (limitBaseChangeSystemIso B S hS D hL hD R r)
    (limitBaseChangeSnd B S hS D hL hD R r) (x := x) (y := y) (by rw [h])
  rw [limitBaseChangeSystemIso_comp_snd B S hS D hL hD R r (Over.mk (𝟙 i))]
    at h1
  have h2 := map_map_eq_of_map_comp_eq B S hS _ _ h1
  obtain ⟨k, e, hk⟩ := eventually_eq_of_modulePullback_limitSpaceProjection_eq B S hS _
    (hasSiteLimit_stageBaseChangeSystem B S hS D hL hD R r)
    (isAlgebraicSpace_stageBaseChangeSystem B S hS D hD R r) (Over.mk (𝟙 i)) hqc
    _ _ (isFinitePresentationOnSite_modulePullback B S hS _ _ hM)
    (isFinitePresentationOnSite_modulePullback B S hS _ _ hN) _ _ h2
  refine ⟨k, ?_⟩
  have he : stageTransition B S hS _ (isAlgebraicSpace_stageBaseChangeSystem B S hS D hD R r) e ≫
      stageBaseChangeSpaceSnd B S hS D hD R r (Over.mk (𝟙 i)) =
      stageBaseChangeSpaceSnd B S hS D hD R r k :=
    ObjectProperty.hom_ext _ (stageBaseChangeSystem_map_comp_snd B S hS D i r.hom e)
  have h3 := map_comp_eq_of_map_map_eq B S hS _ _ hk
  rw [he] at h3
  exact h3

end AlgebraicGeometry.Space

end
