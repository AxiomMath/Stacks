module

public import StacksFrontier.AlgebraicGeometry.PicardScheme.Jacobian.HilbertChart

/-!
# The chart of Stacks 0B9X in the whole rigidified Picard functor

The analogue of `Stacks.RigidifiedPicard.exists_representableBy_cohomologySubfunctorZero` for
the whole rigidified Picard functor `Pic_{X/S,σ}` rather than its degree-zero part: the open
`W ⊆ Hilb^g_{X/S}` of [Stacks, Tag 0B9X] represents the subfunctor of [Stacks, Tag 0B9V]
(translated by `θ`; the source's chart is `θ = 0`). This is the chart the proof of
[Stacks, Tag 0B9Z] feeds to the group-scheme criterion [Stacks, Tag 0B9Q].
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.ProperFlatFibreEulerCharacteristic

universe u

namespace Stacks.RigidifiedPicard

variable {X S : Scheme.{u}} (f : X ⟶ S) [Flat f] [LocallyOfFinitePresentation f] [IsProper f]

section Chart

variable [SmoothOfRelativeDimension 1 f] (σ : S ⟶ X) (hσ : σ ≫ f = 𝟙 S)
  (h0B91 : PerfectDerivedPushforward.{u}) (hbc : BaseChangeDerivedPushforward.{u})
  (θ : Stacks.Picard.ofScheme X) {g : ℕ} {H : Over S}
  (hH : Stacks.Hilbert.RepresentsHilbertFunctorOfRank (Over.mk f) H g)

omit [Flat f] [LocallyOfFinitePresentation f] [IsProper f] [SmoothOfRelativeDimension 1 f] in
/-- Two elements of `Pic_{X/S,σ}(T)` are equal when their classes in `Pic(X_T)` are. -/
theorem ext_functor {T : Over S} {z z' : (functor f σ hσ ⋙ forget GrpCat).obj (op T)}
    (h : smallEquiv _ ((Multiplicative.toAdd z : group f σ hσ T) :
        Stacks.Picard.smallOfScheme (bc f T)) =
      smallEquiv _ ((Multiplicative.toAdd z' : group f σ hσ T) :
        Stacks.Picard.smallOfScheme (bc f T))) : z = z' := by
  show Multiplicative.ofAdd (Multiplicative.toAdd z : group f σ hσ T) =
    Multiplicative.ofAdd (Multiplicative.toAdd z' : group f σ hσ T)
  exact congrArg _ (Subtype.ext ((smallEquiv (bc f T)).injective h))

include h0B91 hbc hH in
/-- **[Stacks, Tag 0B9X] for the whole rigidified Picard functor, with the representing
isomorphism.** For `H` representing `Hilb^g_{X/S}`, the translate by `θ` of the subfunctor of
[Stacks, Tag 0B9V] of `Pic_{X/S,σ}` is represented by an open subscheme `W` of `H`, through the
isomorphism sending `a : T ⟶ W` to the normalised Abel class of the family classified by `a`,
translated by `θ`. The claim of the source's proof — every class `ℒ` with `Rf_{T,*}ℒ` invertible
in degree `0` is the class of a unique degree-`g` divisor up to a class from the base — is the
pair of hypotheses `hexists`, `huniq`. -/
theorem exists_representableBy_cohomologySubfunctor_spec
    (hexists : ∀ (T : Over S) (c : Stacks.Picard.ofScheme (bc f T)),
      HasInvertibleDirectImage f T c →
        ∃ (Z : Stacks.Hilbert.HilbertFamily (Over.mk f) T g) (n : Stacks.Picard.ofScheme T.left),
          abelClass f Z = c + Stacks.Picard.schemePullbackClass (bcProj f T) n)
    (huniq : ∀ (T : Over S) (Z Z' : Stacks.Hilbert.HilbertFamily (Over.mk f) T g),
      HasInvertibleDirectImage f T (abelClass f Z) →
        (∃ n : Stacks.Picard.ofScheme T.left,
          abelClass f Z' = abelClass f Z + Stacks.Picard.schemePullbackClass (bcProj f T) n) →
          Z = Z') :
    ∃ (W : H.left.Opens) (R : (cohomologySubfunctor f σ hσ h0B91 hbc θ).toFunctor.RepresentableBy
      (Over.mk (W.ι ≫ H.hom))), ∀ {T : Over S} (a : T ⟶ Over.mk (W.ι ≫ H.hom)),
        smallEquiv _ ((Multiplicative.toAdd (R.homEquiv a).1 : group f σ hσ T) :
          Stacks.Picard.smallOfScheme (bc f T)) = chartClass f σ hσ θ hH (a ≫ chartι W) := by
  obtain ⟨W, hW⟩ := exists_chartOpen f h0B91 hbc hH
  let F := cohomologySubfunctor f σ hσ h0B91 hbc θ
  have hmemW : ∀ {T : Over S} (a : T ⟶ Over.mk (W.ι ≫ H.hom)),
      Set.range (a ≫ chartι W).left ⊆ (W : Set H.left) := by
    intro T a
    rintro _ ⟨x, rfl⟩
    rw [← Scheme.Opens.range_ι]
    exact ⟨a.left x, rfl⟩
  let cls : ∀ {T : Over S}, (T ⟶ Over.mk (W.ι ≫ H.hom)) →
      (functor f σ hσ ⋙ forget GrpCat).obj (op T) := fun {T} a =>
    Multiplicative.ofAdd (mkGroup f σ hσ (chartClass f σ hσ θ hH (a ≫ chartι W))
      (schemePullbackClass_bcSection_chartClass f σ hσ θ hH _))
  have hcls : ∀ {T : Over S} (a : T ⟶ Over.mk (W.ι ≫ H.hom)),
      smallEquiv _ ((Multiplicative.toAdd (cls a) : group f σ hσ T) :
        Stacks.Picard.smallOfScheme (bc f T)) =
        chartClass f σ hσ θ hH (a ≫ chartι W) := fun a =>
      smallEquiv_mkGroup f σ hσ _ (schemePullbackClass_bcSection_chartClass f σ hσ θ hH _)
  have hclsF : ∀ {T : Over S} (a : T ⟶ Over.mk (W.ι ≫ H.hom)), cls a ∈ F.obj (op T) := by
    intro T a
    show IsCohomologyClass f θ T _
    rw [hcls, isCohomologyClass_chartClass_iff f σ hσ h0B91 hbc θ hH, hW]
    exact hmemW a
  let toF : ∀ {T : Over S}, (T ⟶ Over.mk (W.ι ≫ H.hom)) → F.toFunctor.obj (op T) := fun {T} a =>
    ⟨cls a, hclsF a⟩
  have hinj : ∀ {T : Over S}, Function.Injective (toF (T := T)) := by
    intro T a a' h
    have hc : chartClass f σ hσ θ hH (a ≫ chartι W) = chartClass f σ hσ θ hH (a' ≫ chartι W) := by
      rw [← hcls a, ← hcls a']
      exact congrArg (fun z : (functor f σ hσ ⋙ forget GrpCat).obj (op T) =>
        smallEquiv _ ((Multiplicative.toAdd z : group f σ hσ T) :
          Stacks.Picard.smallOfScheme (bc f T))) (congrArg Subtype.val h)
    obtain ⟨n, hn⟩ := abelNormalized_add_eq f σ hσ θ (hH.family (a ≫ chartι W))
    obtain ⟨n', hn'⟩ := abelNormalized_add_eq f σ hσ θ (hH.family (a' ≫ chartι W))
    have hZ : hH.family (a ≫ chartι W) = hH.family (a' ≫ chartι W) := by
      refine huniq T _ _ ((hW T _).2 (hmemW a)) ⟨n - n', ?_⟩
      have h1 : abelClass f (hH.family (a' ≫ chartι W)) =
          abelClass f (hH.family (a ≫ chartι W)) +
            Stacks.Picard.schemePullbackClass (bcProj f T) n -
              Stacks.Picard.schemePullbackClass (bcProj f T) n' := by
        rw [← hn, ← chartClass, hc, chartClass, hn']
        exact (add_sub_cancel_right _ _).symm
      rw [h1, show Stacks.Picard.schemePullbackClass (bcProj f T) (n - n') =
        Stacks.Picard.schemePullbackClass (bcProj f T) n -
          Stacks.Picard.schemePullbackClass (bcProj f T) n' from
        map_sub (Stacks.Picard.schemePullbackClassHom _) n n']
      exact add_sub_assoc _ _ _
    exact Over.OverMorphism.ext ((cancel_mono W.ι).1
      (congrArg CommaMorphism.left (hH.family.injective hZ)))
  have hsurj : ∀ {T : Over S}, Function.Surjective (toF (T := T)) := by
    intro T x
    set c : Stacks.Picard.ofScheme (bc f T) := smallEquiv _ ((Multiplicative.toAdd x.1 :
      group f σ hσ T) : Stacks.Picard.smallOfScheme (bc f T))
    obtain ⟨Z, n, hZ⟩ := hexists T _ x.2
    let m : T ⟶ H := hH.family.symm Z
    have hmZ : hH.family m = Z := hH.family.apply_symm_apply Z
    have hmW : Set.range m.left ⊆ (W : Set H.left) := by
      rw [← hW, hmZ, hZ, hasInvertibleDirectImage_add_bcProj_iff f h0B91 hbc]
      exact x.2
    obtain ⟨a, ham⟩ : ∃ a : T ⟶ Over.mk (W.ι ≫ H.hom), a ≫ chartι W = m :=
      ⟨Over.homMk (IsOpenImmersion.lift W.ι m.left (by simpa using hmW)) (by
          show IsOpenImmersion.lift W.ι m.left _ ≫ W.ι ≫ H.hom = T.hom
          rw [IsOpenImmersion.lift_fac_assoc, Over.w m]),
        Over.OverMorphism.ext (IsOpenImmersion.lift_fac _ _ _)⟩
    refine ⟨a, Subtype.ext ?_⟩
    show cls a = x.1
    refine ext_functor f σ hσ ?_
    rw [hcls a, ham, chartClass, hmZ, abelNormalized, hZ, add_sub_right_comm, add_sub_cancel_right,
      normalize_add_bcProj, normalize_eq_self f σ hσ T c
        ((mem_group_iff f σ hσ T _).1 (Multiplicative.toAdd x.1 : group f σ hσ T).2)]
  refine ⟨W, { homEquiv := Equiv.ofBijective toF ⟨hinj, hsurj⟩, homEquiv_comp := ?_ }, hcls⟩
  intro T T' b a
  apply Subtype.ext
  show cls (b ≫ a) = (functor f σ hσ ⋙ forget GrpCat).map b.op (cls a)
  refine ext_functor f σ hσ ?_
  rw [functor_map_val, hcls, hcls, Category.assoc, chartClass_comp]

include h0B91 hbc hH in
/-- **[Stacks, Tag 0B9X] for the whole rigidified Picard functor, given its claim and
[Stacks, Tag 0B91].** For `H` representing `Hilb^g_{X/S}`, the translate by `θ` of the
subfunctor of [Stacks, Tag 0B9V] of `Pic_{X/S,σ}` is represented by an open subscheme `W` of
`H`; with `θ = 0` this is the source's statement. The claim of the source's proof is the pair of
hypotheses `hexists`, `huniq`. -/
theorem exists_representableBy_cohomologySubfunctor
    (hexists : ∀ (T : Over S) (c : Stacks.Picard.ofScheme (bc f T)),
      HasInvertibleDirectImage f T c →
        ∃ (Z : Stacks.Hilbert.HilbertFamily (Over.mk f) T g) (n : Stacks.Picard.ofScheme T.left),
          abelClass f Z = c + Stacks.Picard.schemePullbackClass (bcProj f T) n)
    (huniq : ∀ (T : Over S) (Z Z' : Stacks.Hilbert.HilbertFamily (Over.mk f) T g),
      HasInvertibleDirectImage f T (abelClass f Z) →
        (∃ n : Stacks.Picard.ofScheme T.left,
          abelClass f Z' = abelClass f Z + Stacks.Picard.schemePullbackClass (bcProj f T) n) →
          Z = Z') :
    ∃ W : H.left.Opens,
      Nonempty ((cohomologySubfunctor f σ hσ h0B91 hbc θ).toFunctor.RepresentableBy
        (Over.mk (W.ι ≫ H.hom))) := by
  obtain ⟨W, R, -⟩ := exists_representableBy_cohomologySubfunctor_spec f σ hσ h0B91 hbc θ hH
    hexists huniq
  exact ⟨W, ⟨R⟩⟩

end Chart

end Stacks.RigidifiedPicard

end
