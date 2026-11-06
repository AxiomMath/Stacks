module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EtaleNeighborhoodBaseChangeOverOpen
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.EtaleBaseChange
public import StacksFrontier.Algebra.Homology.DerivedCategory.InverseLimitHelpers

/-!
# Acyclicity of injective sheaves pulled back to the strict henselization base change

Let `f : X ⟶ S` be a morphism of schemes, `s` a geometric point of `S`, `U` an open subscheme
containing the image of `s`, and `p : X ×_S Spec(𝒪^{sh}_{S,s}) ⟶ X` the projection. This file
presents `X ×_S Spec(𝒪^{sh}_{S,s})` itself, with no change of vertex, as the limit of the base
changes `Z_a ×_U X_U` of `AlgebraicGeometry.etaleNeighborhoodDirectedBaseChange`, and shows that
the levels of that system are étale over `X_U`. Consequently, whenever étale cohomology of the
limit vanishes as soon as it vanishes on every level (which is [Stacks, Tag 03Q6]), the inverse
image `p⁻¹I` of an injective abelian sheaf `I` on `X_étale` is acyclic for global sections: on
every level the inverse image of `I` is again injective, its restriction to the étale scheme
`Z_a ×_U X_U` over `X` being injective.

## Main definitions

* `AlgebraicGeometry.strictHenselizationDirectedLimitCone`: the cone on the base changes with
  vertex `X ×_S Spec(𝒪^{sh}_{S,s})`.
* `AlgebraicGeometry.strictHenselizationToSourceOverOpen`: the projection from that vertex to
  `X_U`.

## Main results

* `AlgebraicGeometry.isLimitStrictHenselizationDirectedLimitCone`: it is a limit cone.
* `AlgebraicGeometry.rightAcyclic_strictHenselizationPullback_of_isZero`: the acyclicity of
  `p⁻¹I`, from the vanishing statement of [Stacks, Tag 03Q6] for this system.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing
open AlgebraicGeometry.Scheme Stacks.EtaleCohomology

universe u

namespace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

-- Prefer the direct existence theorem to searching for an injective replacement.
attribute [local instance 2000]
  HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (s : GeometricPoint S)
  (U : S.Opens) (hU : s.hom (closedPoint s.residueField) ∈ U) {X : Scheme.{u}} (f : X ⟶ S)

/-- The cone on the base changes `Z_a ×_U X_U` whose vertex is `X ×_S Spec(𝒪^{sh}_{S,s})`. -/
abbrev strictHenselizationDirectedLimitCone :
    Cone (etaleNeighborhoodDirectedBaseChange B S hS s U hU f) :=
  (etaleNeighborhoodDirectedBaseChangeCone B S hS s U hU f).extend
    (etaleNeighborhoodDirectedBaseChangeConePtIso B S hS s U hU f).inv

/-- **`X ×_S Spec(𝒪^{sh}_{S,s})` is the limit of the base changes `Z_a ×_U X_U`.** -/
def isLimitStrictHenselizationDirectedLimitCone :
    IsLimit (strictHenselizationDirectedLimitCone B S hS s U hU f) :=
  IsLimit.ofIsoLimit (isLimitEtaleNeighborhoodDirectedBaseChangeCone B S hS s U hU f)
    (Cone.ext (etaleNeighborhoodDirectedBaseChangeConePtIso B S hS s U hU f) (fun _ => by simp))

/-- The projection from `X ×_S Spec(𝒪^{sh}_{S,s})` to `X_U`. -/
abbrev strictHenselizationToSourceOverOpen :
    strictHenselizationBaseChange B hS f s ⟶ (sourceOverOpen S U f).left :=
  (etaleNeighborhoodDirectedBaseChangeConePtIso B S hS s U hU f).inv ≫
    pullback.snd (strictHenselizationDirectedCone B S hS s U hU).pt.hom (sourceOverOpen S U f).hom

/-- The projection to `X_U` followed by `X_U ⟶ X` is the projection `p`. -/
@[reassoc (attr := simp)]
theorem strictHenselizationToSourceOverOpen_fst :
    strictHenselizationToSourceOverOpen B S hS s U hU f ≫ pullback.fst f U.ι =
      strictHenselizationBaseChangeToSource B hS f s := by
  rw [Category.assoc, ← etaleNeighborhoodDirectedBaseChangeConePtIso_hom_toSource,
    Iso.inv_hom_id_assoc]

/-- Every leg of the limit cone, followed by the projection of the level to `X_U`, is the
projection of the vertex to `X_U`. -/
@[reassoc]
theorem strictHenselizationDirectedLimitCone_π_snd
    (a : (etaleNeighborhoodDirectedIndex B S hS s U hU)ᵒᵖ) :
    (strictHenselizationDirectedLimitCone B S hS s U hU f).π.app a ≫
        pullback.snd ((etaleNeighborhoodDirectedSystem B S hS s U hU).obj a).hom
          (sourceOverOpen S U f).hom =
      strictHenselizationToSourceOverOpen B S hS s U hU f := by
  simp only [Over.pullback, Cone.extend_π, Functor.const_obj_obj, Functor.mapCone_π_app,
    Over.forget_map, NatTrans.comp_app, Category.assoc, Functor.const_map_app, Over.homMk_left]
  exact congrArg (_ ≫ ·) (pullback.lift_snd _ _ _)

/-- The structure morphism to `U` of a member of the directed system is étale. -/
instance etale_etaleNeighborhoodDirectedSystem_hom
    (a : (etaleNeighborhoodDirectedIndex B S hS s U hU)ᵒᵖ) :
    Etale ((etaleNeighborhoodDirectedSystem B S hS s U hU).obj a).hom := by
  have : Etale (((etaleNeighborhoodDirectedSystem B S hS s U hU).obj a).hom ≫ U.ι) := by
    change Etale (etaleNeighborhoodToOpen B S hS s U _ ≫ U.ι)
    rw [etaleNeighborhoodToOpen_ι]
    exact ((etaleNeighborhoodOpenInclusion B S hS s U).obj
      ((etaleNeighborhoodDirectedFunctor B S hS s U hU).obj a)).1.property
  exact Etale.of_comp _ U.ι

/-- The projection of a level `Z_a ×_U X_U` to `X_U` is étale, a base change of the étale
structure morphism of `Z_a`. -/
instance etale_etaleNeighborhoodDirectedBaseChange_snd
    (a : (etaleNeighborhoodDirectedIndex B S hS s U hU)ᵒᵖ) :
    Etale (pullback.snd ((etaleNeighborhoodDirectedSystem B S hS s U hU).obj a).hom
      (sourceOverOpen S U f).hom) :=
  inferInstance

/-- **The inverse image of an injective sheaf to `X ×_S Spec(𝒪^{sh}_{S,s})` is acyclic, given
[Stacks, Tag 03Q6] for the system `Z_a ×_U X_U`** in its vanishing form: if, for an abelian sheaf
`F` on `X_U`, the cohomology of its inverse images vanishes in degree `p` on every level, then so
does that of its inverse image on the limit. -/
theorem rightAcyclic_strictHenselizationPullback_of_isZero
    (hvan : ∀ (F : Sheaf (smallEtaleTopology (sourceOverOpen S U f).left) Ab.{u + 1}) (p : ℕ),
      (∀ a, IsZero (((Sheaf.Γ (smallEtaleTopology
          ((etaleNeighborhoodDirectedBaseChange B S hS s U hU f).obj a)) Ab.{u + 1}).rightDerived
            p).obj ((smallEtalePullbackAb (pullback.snd
              ((etaleNeighborhoodDirectedSystem B S hS s U hU).obj a).hom
              (sourceOverOpen S U f).hom)).obj F))) →
        IsZero (((Sheaf.Γ (smallEtaleTopology (strictHenselizationBaseChange B hS f s))
          Ab.{u + 1}).rightDerived p).obj
            ((smallEtalePullbackAb (strictHenselizationToSourceOverOpen B S hS s U hU f)).obj F)))
    (I : Sheaf (smallEtaleTopology X) Ab.{u + 1}) (hI : Injective I) :
    (Sheaf.Γ (smallEtaleTopology (strictHenselizationBaseChange B hS f s))
      Ab.{u + 1}).rightAcyclic
        ((smallEtalePullbackAb (strictHenselizationBaseChangeToSource B hS f s)).obj I) := by
  rw [rightAcyclic_iff_isZero_rightDerived]
  rintro p hp
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hp.ne'
  have hF := (smallEtalePullbackAb (pullback.fst f U.ι)).injective_obj_of_injective hI
  refine (hvan _ (n + 1) fun a => ?_).of_iso (((Sheaf.Γ (smallEtaleTopology
    (strictHenselizationBaseChange B hS f s)) Ab.{u + 1}).rightDerived (n + 1)).mapIso
      (eqToIso (by rw [strictHenselizationToSourceOverOpen_fst]) ≪≫
        (smallEtalePullbackAbCompIso (strictHenselizationToSourceOverOpen B S hS s U hU f)
          (pullback.fst f U.ι)).symm.app I))
  have := (smallEtalePullbackAb (pullback.snd
    ((etaleNeighborhoodDirectedSystem B S hS s U hU).obj a).hom
    (sourceOverOpen S U f).hom)).injective_obj_of_injective hF
  exact Functor.isZero_rightDerived_obj_injective_succ _ n _

end AlgebraicGeometry

end
