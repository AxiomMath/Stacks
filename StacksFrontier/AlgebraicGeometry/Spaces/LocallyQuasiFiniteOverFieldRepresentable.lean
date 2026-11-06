module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ConditionComparisons
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.LocallyQuasiFiniteOverField
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.NoetherianQuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.DimensionLocalRings
public import StacksFrontier.AlgebraicGeometry.Spaces.DimensionZeroOverField
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenImmersionSurjectiveOnPointsIso
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiLocallyQuasiSeparatedCodimensionZero

/-!
# An algebraic space locally quasi-finite over a field is a scheme

Let `X` be an algebraic space over a scheme `S` which is the spectrum of a field `k`, and assume
that the structure morphism `X ⟶ S` is locally quasi-finite (more generally, that `X` has a
locally quasi-finite morphism to an object of the site which is the spectrum of a field) — by
Stacks 0ACA, conditions (4) and (5), equivalently `X` is locally of finite type over `k` and of
dimension at most zero. Then `X` is representable.

This is the scheme clause of case (2) of Stacks 06LZ, and it is what the hard direction of
Stacks 06N3 uses: the self-intersection `Spec k ×_𝒳 Spec k` of a finite type point of a DM stack
is such a space.

## Main results

* `AlgebraicGeometry.Space.isDecentSpace_of_isLocallyQuasiFinite_to_field`: an algebraic space
  locally quasi-finite over an object of the site which is the spectrum of a field is decent.
* `AlgebraicGeometry.Space.isRepresentable_of_isLocallyQuasiFinite_to_field`: such a space is
  representable.
* `AlgebraicGeometry.Space.isRepresentable_of_dimension_le_zero_to_field`: the same for an
  algebraic space locally of finite type over the field and of dimension at most zero.

## Implementation notes

The source's own proof of case (2) runs through a finite étale equivalence relation on an affine
chart and the quotient of Stacks 03BM. Here case (2) is reduced to case (1) instead, as the
source remarks: the space is decent (condition (γ) of Stacks 03JX, by the argument of
`AlgebraicGeometry.Space.isDecentSpace_of_isLocallyQuasiFinite`, run over a field object of the
site instead of over the base), locally Noetherian since its étale charts are of finite type over
a field, hence quasi-separated by Stacks 0BB6, hence Zariski locally quasi-separated by
Stacks 03JX; Stacks 06NH then puts every point of codimension zero — here every point — into a
representable open subspace, which is therefore everything.

No `@[stacks 06LZ]` attribute is placed: the tag also asserts separatedness and the affineness of
quasi-compact opens, and treats two further cases.

## References

* [Stacks Project, Tag 06LZ](https://stacks.math.columbia.edu/tag/06LZ)
* [Stacks Project, Tag 0ACA](https://stacks.math.columbia.edu/tag/0ACA)
* [Stacks Project, Tag 0BB6](https://stacks.math.columbia.edu/tag/0BB6)
* [Stacks Project, Tag 03JX](https://stacks.math.columbia.edu/tag/03JX)
* [Stacks Project, Tag 06NH](https://stacks.math.columbia.edu/tag/06NH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] pointTopology

/-- Pullbacks of presheaves on `BigFppfOver B S hS`, given directly: instance search for them
times out under Lean v4.35.0. -/
local instance (priority := high) hasPullbacks_presheaf_LocallyQuasiFiniteOverFieldRepresentable :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  Limits.functorCategoryHasLimitsOfShape

local instance (priority := high) hasPullback_presheaf_LocallyQuasiFiniteOverFieldRepresentable
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  (hasPullbacks_presheaf_LocallyQuasiFiniteOverFieldRepresentable B S hS).has_limit _

/-- Small discrete limits of presheaves on `BigFppfOver B S hS`, given directly. -/
local instance (priority := high)
    hasLimitsOfShape_discrete_presheaf_LocallyQuasiFiniteOverFieldRepresentable (J : Type) :
    HasLimitsOfShape (Discrete J) ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  Limits.functorCategoryHasLimitsOfShape

/-- **An algebraic space locally quasi-finite over a field is decent**, for a field which is an
object `K` of the site over `S` rather than the base itself. An affine étale chart `U` of `X` is
locally quasi-finite and quasi-compact over the one-point scheme `K`, so it has finitely many
points; so does `U ×_K U`, into which the self-intersection `U ×_X U` embeds. -/
theorem isDecentSpace_of_isLocallyQuasiFinite_to_field {k : Type u} [Field k]
    {K : BigFppfOver B S hS} (e : (BigFppfOver.toScheme B S hS).obj K ≅ Spec (.of k))
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (g : X ⟶ yoneda.obj K) (hlqf : IsLocallyQuasiFinite B S hS g) :
    IsDecentSpace B S hS X := by
  classical
  rw [isDecentSpace_iff_hasFiniteChartAndRelationFibersAtEveryPoint B S hS X hX]
  intro x U hU φ hφ
  obtain ⟨h, hh⟩ : ∃ h : U ⟶ K, yoneda.map h = φ ≫ g :=
    ⟨_, Yoneda.fullyFaithful.map_preimage _⟩
  have hUlqf : LocallyQuasiFinite ((BigFppfOver.toScheme B S hS).map h) :=
    (hlqf U K φ (𝟙 _) h hφ (presheaf_yoneda_map_id_etale B S hS _)
      (by rw [hh, Category.comp_id])).2
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj U) := hU
  have hfinite : ∀ (T : Scheme.{u}) (q : T ⟶ (BigFppfOver.toScheme B S hS).obj K),
      LocallyQuasiFinite q → QuasiCompact q → Finite T := by
    intro T q _ _
    let q' := q ≫ e.hom
    have hq := q'.finite_preimage_singleton (Classical.arbitrary (Spec (.of k)))
    rw [show q' ⁻¹' {Classical.arbitrary (Spec (.of k))} = Set.univ from
      Set.eq_univ_of_forall fun _ => Subsingleton.elim _ _] at hq
    exact Set.finite_univ_iff.mp hq
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj K) := IsAffine.of_isIso e.hom
  have hUfin : Finite ((BigFppfOver.toScheme B S hS).obj U) :=
    hfinite _ _ hUlqf inferInstance
  have hptsU : Finite (points B S hS (yoneda.obj U)) :=
    Finite.of_equiv _ (schemePointsHomeomorph B S hS U).toEquiv.symm
  refine ⟨Set.toFinite _, ?_⟩
  -- the fibre product `U ×_K U` in the site has finitely many points
  have : PreservesLimitsOfShape WalkingCospan (BigFppfOver.toScheme B S hS) :=
    preservesLimitsOfShape_walkingCospan_toScheme B S hS
  set W := pullback h h with hWdef
  have hsq : IsPullback ((BigFppfOver.toScheme B S hS).map (pullback.fst h h))
      ((BigFppfOver.toScheme B S hS).map (pullback.snd h h))
      ((BigFppfOver.toScheme B S hS).map h) ((BigFppfOver.toScheme B S hS).map h) :=
    (IsPullback.of_hasPullback h h).map (BigFppfOver.toScheme B S hS)
  have : LocallyQuasiFinite ((BigFppfOver.toScheme B S hS).map (pullback.snd h h)) :=
    MorphismProperty.of_isPullback hsq hUlqf
  have : QuasiCompact ((BigFppfOver.toScheme B S hS).map (pullback.snd h h)) :=
    MorphismProperty.of_isPullback hsq
      (inferInstanceAs (QuasiCompact ((BigFppfOver.toScheme B S hS).map h)))
  have hWfin : Finite ((BigFppfOver.toScheme B S hS).obj W) :=
    hfinite _ ((BigFppfOver.toScheme B S hS).map (pullback.snd h h ≫ h)) (by
      rw [Functor.map_comp]; infer_instance) (by rw [Functor.map_comp]; infer_instance)
  have hptsW : Finite (points B S hS (yoneda.obj W)) :=
    Finite.of_equiv _ (schemePointsHomeomorph B S hS W).toEquiv.symm
  -- the self-intersection embeds into `h_W`
  have hWpb : IsPullback (yoneda.map (pullback.fst h h)) (yoneda.map (pullback.snd h h))
      (φ ≫ g) (φ ≫ g) := by
    rw [← hh]
    exact (IsPullback.of_hasPullback h h).map yoneda
  let m : pullback φ φ ⟶ yoneda.obj W :=
    hWpb.lift (pullback.fst φ φ) (pullback.snd φ φ) (by rw [← Category.assoc, pullback.condition,
      Category.assoc])
  have : Mono m := ⟨fun a b hab => pullback.hom_ext
    (by simpa [m] using congrArg (· ≫ yoneda.map (pullback.fst h h)) hab)
    (by simpa [m] using congrArg (· ≫ yoneda.map (pullback.snd h h)) hab)⟩
  have : Finite (points B S hS (pullback φ φ)) :=
    Finite.of_injective _ (pointsMap_injective_of_mono B S hS m)
  exact Set.toFinite _

/-- **An algebraic space locally quasi-finite over a field is representable.** The field is
an object `K` of the site over `S` whose underlying scheme is the spectrum of a field; for
`K = S` this is the scheme clause of case (2) of Stacks 06LZ in the form of Stacks 0ACA (5). -/
theorem isRepresentable_of_isLocallyQuasiFinite_to_field {k : Type u} [Field k]
    {K : BigFppfOver B S hS} (e : (BigFppfOver.toScheme B S hS).obj K ≅ Spec (.of k))
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (g : X ⟶ yoneda.obj K) (hlqf : IsLocallyQuasiFinite B S hS g) :
    X.IsRepresentable := by
  have hZ := B.contains_terminal
  have hdec := isDecentSpace_of_isLocallyQuasiFinite_to_field B S hS e hX g hlqf
  have hNoeth : HasEtaleLocalProperty B S hS X (fun Y : Scheme.{u} => IsLocallyNoetherian Y) := by
    obtain ⟨U, a, hsurj, ha⟩ := hX.exists_atlas
    refine ⟨U, a, hsurj, ha, ?_⟩
    obtain ⟨h, hh⟩ : ∃ h : U ⟶ K, yoneda.map h = a ≫ g :=
      ⟨_, Yoneda.fullyFaithful.map_preimage _⟩
    have hU : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map h) :=
      (hlqf U K a (𝟙 _) h ha (presheaf_yoneda_map_id_etale B S hS _)
        (by rw [hh, Category.comp_id])).1
    have : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj K) :=
      isLocallyNoetherian_of_isOpenImmersion e.hom
    exact LocallyOfFiniteType.isLocallyNoetherian ((BigFppfOver.toScheme B S hS).map h)
  have hqs := isAbsolutelyQuasiSeparated_of_isLocallyNoetherian_of_isDecentSpace B S hS hZ X hX
    hNoeth hdec
  have hzqs := isAbsolutelyZariskiLocallyQuasiSeparated_of_isAbsolutelyQuasiSeparated B S hS
    (X := X) hZ hX hqs
  obtain ⟨G, hG, hGrep, -, hcodim⟩ :=
    exists_denseRange_isRepresentable_isOpenSubspace_codimensionZero B S hS hZ X hX hzqs
  have hsub : Subsingleton ((BigFppfOver.toScheme B S hS).obj K) :=
    ⟨fun a b => e.hom.homeomorph.injective (Subsingleton.elim _ _)⟩
  have hdim : dimension B S hS X hX ≤ 0 :=
    (isLocallyQuasiFinite_iff_dimension_le_zero B S hS hX hsub g
      (holdsOnEveryEtaleChart_mono B S hS (fun _ h => h.1) hlqf)).1 hlqf
  have hsurj : Function.Surjective (pointsMap B S hS G.toFunctor G.ι) := by
    intro x
    refine hcodim x (le_antisymm ?_ bot_le)
    have hle : (localRingDimension B S hS x : WithBot ℕ∞) ≤ 0 := by
      refine le_trans ?_ hdim
      rw [dimension_eq_iSup_localRingDimension B S hS X hX]
      exact le_iSup (fun y : points B S hS X => (localRingDimension B S hS y : WithBot ℕ∞)) x
    exact_mod_cast hle
  have : IsIso G.ι := isIso_of_isOpenImmersion_of_surjective_pointsMap B S hS G.ι hG.2 hsurj
  obtain ⟨U, ⟨r⟩⟩ := hGrep.has_representation
  exact Functor.IsRepresentable.mk' (r.toIso ≪≫ asIso G.ι)

/-- **An algebraic space locally of finite type over a field and of dimension at most zero is
representable.** By Stacks 0ACA, conditions (4) and (5), such a space is locally quasi-finite
over the field. -/
theorem isRepresentable_of_dimension_le_zero_to_field {k : Type u} [Field k]
    {K : BigFppfOver B S hS} (e : (BigFppfOver.toScheme B S hS).obj K ≅ Spec (.of k))
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (g : X ⟶ yoneda.obj K) (hlft : IsLocallyOfFiniteType B S hS g)
    (hdim : dimension B S hS X hX ≤ 0) :
    X.IsRepresentable :=
  isRepresentable_of_isLocallyQuasiFinite_to_field B S hS e hX g
    ((isLocallyQuasiFinite_iff_dimension_le_zero B S hS hX
      ⟨fun _ _ => e.hom.homeomorph.injective (Subsingleton.elim _ _)⟩ g hlft).2 hdim)

end AlgebraicGeometry.Space

end
