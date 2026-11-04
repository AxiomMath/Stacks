module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.BertiniFieldBaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.BertiniGenericMember

/-!
# The divisor `H_v` of the base-changed situation is a base change of `H_v`

Work in the standing situation of the Bertini theorems ([Stacks, Tag 0G47]) and let `K/k` and
`F/k` be field extensions, both contained in a field `M` over `k`. The base-changed situation
`Stacks.Bertini.FamilyDivisors.baseChangeFamily` over `K` has its own divisors `H_w` attached to
vectors of `(K ⊗_k V) ⊗_K M = V ⊗_k M`, and this file identifies the one attached to the
coordinate tuple `a` read in `M` with the base change along `M/F` of the divisor `H_v` of the
original situation attached to `a` read in `F`.

Both `X_M` (formed in two steps, `X → X_K → X_M`) and `X_F` present a fibre product of `X` with a
field over `Spec k`, so there is a comparison morphism `X_M ⟶ X_F` making `X_M` the base change
of `X_F` along `Spec M ⟶ Spec F`
(`Stacks.Bertini.FamilyDivisors.isPullback_baseChangeComparison`). The two sections cutting out
the two divisors are, up to the comparison isomorphism `p^* q^* L ≅ (p ≫ q)^* L` of pullbacks,
the same linear combination of the same pulled-back sections of `L`, the coefficients
corresponding under `Γ(X_F) ⟶ Γ(X_M)`; so the identification of the divisors is an instance of
`Stacks.Bertini.zeroScheme_sum_smul_comap`.

## Main results

* `Stacks.Bertini.FamilyDivisors.baseChangeComparison`,
  `Stacks.Bertini.FamilyDivisors.isPullback_baseChangeComparison`: `X_M = X_F ×_{Spec F} Spec M`.
* `Stacks.Bertini.FamilyDivisors.specializedDivisor_baseChangeFamily_eq_comap`: the divisor of the
  base-changed situation is the inverse image of the divisor of the original one.
* `Stacks.Bertini.FamilyDivisors.exists_isPullback_specializedDivisor_baseChangeFamily`: the
  resulting cartesian square of the two divisors over `Spec M ⟶ Spec F`, which is the form in
  which `AlgebraicGeometry.smooth_of_smooth_pullback_snd_spec_algebraMap` consumes it.

## Implementation notes

The coordinate tuple of the base-changed situation is indexed by
`Fin (dim_K (K ⊗_k V))` and that of the original one by `Fin (dim_k V)`; the two agree under
`Stacks.Bertini.FamilyDivisors.finrank_baseChangeFamily`, and the hypothesis `ha'` of the main
results is that the tuples correspond under that reindexing and the inclusion `F ⟶ M`.

## References

* [Stacks Project, Tag 0G47](https://stacks.math.columbia.edu/tag/0G47)
* [Stacks Project, Tag 02FY](https://stacks.math.columbia.edu/tag/02FY)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.Bertini.FamilyDivisors

/-- **A scalar of a field read on the spectrum of an extension field.** -/
theorem appTop_specMap_algebraMap (k' K' : Type u) [Field k'] [Field K'] [Algebra k' K']
    (t : k') :
    (Spec.map (CommRingCat.ofHom (algebraMap k' K'))).appTop
        ((Scheme.ΓSpecIso (.of k')).inv t) =
      (Scheme.ΓSpecIso (.of K')).inv (algebraMap k' K' t) := by
  rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.comp_apply]
  rfl

/-- The base field of the situation base changed along `K/k` is `K`, so an algebra over `K` is an
algebra over it. The instance is needed because the base field of the base-changed situation is
`K` only up to unfolding, which instance resolution does not do. -/
instance algebra_baseChangeFamily_k (D : FamilyDivisors.{u, u}) (K : Type u) [Field K]
    [Algebra D.k K] (M : Type u) [CommRing M] [Algebra K M] :
    Algebra (D.baseChangeFamily K).k M :=
  inferInstanceAs (Algebra K M)

variable (D : FamilyDivisors.{u, u}) (K : Type u) [Field K] [Algebra D.k K]
  (F : Type u) [Field F] [Algebra D.k F] (M : Type u) [Field M] [Algebra D.k M]
  [Algebra K M] [Algebra F M] [IsScalarTower D.k K M] [IsScalarTower D.k F M]

/-- `Spec M ⟶ Spec k` factors through `Spec K` and through `Spec F` in the same way. -/
theorem specMap_algebraMap_comp_eq :
    Spec.map (CommRingCat.ofHom (algebraMap K M)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap D.k K)) =
      Spec.map (CommRingCat.ofHom (algebraMap F M)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap D.k F)) := by
  have h : (algebraMap K M).comp (algebraMap D.k K) =
      (algebraMap F M).comp (algebraMap D.k F) := by
    ext t
    rw [RingHom.comp_apply, RingHom.comp_apply, ← IsScalarTower.algebraMap_apply,
      ← IsScalarTower.algebraMap_apply]
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, h]

/-- **The projection `X_M ⟶ X`** of the scheme base changed in two steps, first to `K` and then
to `M`. It is named because the composite of the two projections is well typed only after the
base-changed situation's scheme is unfolded to `X_K`, which makes the composite itself unusable
as a rewriting target. -/
def baseChangeToXTwice : (D.baseChangeFamily K).baseChange M ⟶ D.X :=
  (D.baseChangeFamily K).baseChangeToX M ≫ D.baseChangeToX K

/-- **`X_M` is the fibre product of `X` and `Spec M` over `Spec k`**, read through the
intermediate field `K`: the two cartesian squares `X_M = X_K ×_{Spec K} Spec M` and
`X_K = X ×_{Spec k} Spec K` paste. -/
theorem isPullback_baseChangeToXTwice :
    IsPullback (D.baseChangeToXTwice K M) ((D.baseChangeFamily K).baseChangeToSpec M) D.toBase
      (Spec.map (CommRingCat.ofHom (algebraMap F M)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap D.k F))) := by
  rw [← D.specMap_algebraMap_comp_eq K F M]
  exact ((D.baseChangeFamily K).isPullback_baseChange M).paste_horiz
    (D.isPullback_baseChange K)

/-- **The comparison morphism `X_M ⟶ X_F`**, where `X_M` is formed from the situation base
changed to `K`: it is the morphism to `X_F = X ×_{Spec k} Spec F` classifying the two projections
of `X_M`. -/
def baseChangeComparison : (D.baseChangeFamily K).baseChange M ⟶ D.baseChange F :=
  (D.isPullback_baseChange F).lift (D.baseChangeToXTwice K M)
    ((D.baseChangeFamily K).baseChangeToSpec M ≫
      Spec.map (CommRingCat.ofHom (algebraMap F M)))
    (by rw [(D.isPullback_baseChangeToXTwice K F M).w, Category.assoc])

/-- **`X_M = X_F ×_{Spec F} Spec M`.** The comparison morphism makes `X_M` the base change of
`X_F` along `M/F`; this is the cancellation of the cartesian square presenting
`X_F = X ×_{Spec k} Spec F` out of the one presenting `X_M = X ×_{Spec k} Spec M`. -/
theorem isPullback_baseChangeComparison :
    IsPullback (D.baseChangeComparison K F M) ((D.baseChangeFamily K).baseChangeToSpec M)
      (D.baseChangeToSpec F) (Spec.map (CommRingCat.ofHom (algebraMap F M))) :=
  IsPullback.of_right' (D.isPullback_baseChangeToXTwice K F M) (D.isPullback_baseChange F)

/-- The comparison morphism carries the projection to `X` of `X_F` to that of `X_M`. -/
theorem baseChangeComparison_comp_baseChangeToX :
    D.baseChangeComparison K F M ≫ D.baseChangeToX F = D.baseChangeToXTwice K M :=
  (D.isPullback_baseChange F).lift_fst _ _ _

/-- **A scalar of `F`, read as a function on `X_M` through `X_F` or directly.** -/
theorem appTop_baseChangeComparison_baseChangeScalar (x : F) :
    (D.baseChangeComparison K F M).appTop (D.baseChangeScalar F x) =
      (D.baseChangeFamily K).baseChangeScalar M (algebraMap F M x) := by
  show (D.baseChangeComparison K F M).appTop
    ((D.baseChangeToSpec F).appTop ((Scheme.ΓSpecIso (.of F)).inv x)) = _
  rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
    (D.isPullback_baseChangeComparison K F M).w, Scheme.Hom.comp_appTop,
    CommRingCat.comp_apply, appTop_specMap_algebraMap F M x]
  rfl

/-- **The two-step pullback of `L` to `X_M` agrees with the one-step pullback.** -/
def pullbackCompModuleIso :
    (Scheme.Modules.pullback ((D.baseChangeFamily K).baseChangeToX M)).obj
        (D.baseChangeFamily K).L ≅
      (Scheme.Modules.pullback (D.baseChangeToXTwice K M)).obj D.L :=
  (Scheme.Modules.pullbackComp ((D.baseChangeFamily K).baseChangeToX M)
    (D.baseChangeToX K)).app D.L

omit [Algebra D.k M] [IsScalarTower D.k K M] in
/-- The comparison isomorphism of the two pullbacks of `L` carries the two-step pullback of a
global section of `L` to its one-step pullback. -/
theorem pullbackCompModuleIso_hom_app (s : Γ(D.L, ⊤)) :
    Scheme.Modules.Hom.app (D.pullbackCompModuleIso K M).hom ⊤
        (pullbackGlobalSections ((D.baseChangeFamily K).baseChangeToX M)
          (D.baseChangeFamily K).L (pullbackGlobalSections (D.baseChangeToX K) D.L s)) =
      pullbackGlobalSections (D.baseChangeToXTwice K M) D.L s :=
  AlgebraicGeometry.SectionsEqualizer.pullbackGlobalSections_comp
    ((D.baseChangeFamily K).baseChangeToX M) (D.baseChangeToX K) D.L s

omit [Algebra D.k M] [IsScalarTower D.k K M] in
/-- The comparison isomorphism carries the two-step pullback of the section of the `j`-th
base-changed basis vector to the one-step pullback of the section of the `j`-th basis vector,
the indices corresponding under `dim_K (K ⊗_k V) = dim_k V`. -/
theorem pullbackCompModuleIso_hom_app_sectionOf_basis
    (j : Fin (Module.finrank (D.baseChangeFamily K).k (D.baseChangeFamily K).V)) :
    Scheme.Modules.Hom.app (D.pullbackCompModuleIso K M).hom ⊤
        (pullbackGlobalSections ((D.baseChangeFamily K).baseChangeToX M)
          (D.baseChangeFamily K).L
          ((D.baseChangeFamily K).sectionOf ((D.baseChangeFamily K).basis j))) =
      pullbackGlobalSections (D.baseChangeToXTwice K M) D.L
        (D.sectionOf (D.basis (finCongr (D.finrank_baseChangeFamily K) j))) := by
  rw [show ((D.baseChangeFamily K).sectionOf ((D.baseChangeFamily K).basis j) :
        Γ((D.baseChangeFamily K).L, ⊤)) =
      pullbackGlobalSections (D.baseChangeToX K) D.L
        (D.sectionOf (D.basis (finCongr (D.finrank_baseChangeFamily K) j))) from
    D.sectionOf_baseChangeFamily_basis K j]
  exact D.pullbackCompModuleIso_hom_app K M _

/-- **The divisor of the base-changed situation is the inverse image of the divisor of the
original one.** For a coordinate tuple `a` with entries in `F` and its image `a'` in `M`,
reindexed along `dim_K (K ⊗_k V) = dim_k V`, the divisor `H_{a'}` on `X_M` of the situation base
changed to `K` is the scheme-theoretic inverse image of the divisor `H_a` on `X_F` of the
original situation.

Both are the zero scheme of the same combination `Σᵢ aᵢ ψ(vᵢ)` of the same pulled-back sections
of `L`, read on `X_M` and on `X_F`; the identity is
`Stacks.Bertini.zeroScheme_sum_smul_comap` once the two-step pullback of `L` is matched with the
one-step pullback. -/
theorem specializedDivisor_baseChangeFamily_eq_comap
    (a : Fin (Module.finrank D.k D.V) → F)
    (a' : Fin (Module.finrank (D.baseChangeFamily K).k (D.baseChangeFamily K).V) → M)
    (ha' : ∀ j, a' j = algebraMap F M (a (finCongr (D.finrank_baseChangeFamily K) j))) :
    (D.baseChangeFamily K).specializedDivisor M a' =
      (D.specializedDivisor F a).comap (D.baseChangeComparison K F M) := by
  have hcomap : (D.specializedDivisor F a).comap (D.baseChangeComparison K F M) =
      zeroScheme ((D.baseChangeFamily K).baseChange M)
        ((Scheme.Modules.pullback (D.baseChangeToXTwice K M)).obj D.L)
        (∑ i, (D.baseChangeFamily K).baseChangeScalar M (algebraMap F M (a i)) •
          pullbackGlobalSections (D.baseChangeToXTwice K M) D.L (D.sectionOf (D.basis i))) :=
    (zeroScheme_sum_smul_comap D.L (D.baseChangeToX F) (D.baseChangeComparison K F M)
      (D.baseChangeToXTwice K M) (D.baseChangeComparison_comp_baseChangeToX K F M)
      (fun i => D.baseChangeScalar F (a i))
      (fun i => (D.baseChangeFamily K).baseChangeScalar M (algebraMap F M (a i)))
      (fun i => D.appTop_baseChangeComparison_baseChangeScalar K F M (a i))
      (fun i => D.sectionOf (D.basis i))).symm
  rw [hcomap]
  refine zeroScheme_eq_of_iso (D.pullbackCompModuleIso K M) ?_
  show Scheme.Modules.Hom.app (D.pullbackCompModuleIso K M).hom ⊤
      ((D.baseChangeFamily K).specializedSection M a') = _
  rw [specializedSection]
  refine (map_sum _ _ Finset.univ).trans ?_
  refine Eq.trans (Finset.sum_congr rfl fun j _ => ?_)
    (Equiv.sum_comp (finCongr (D.finrank_baseChangeFamily K))
      (fun i => (D.baseChangeFamily K).baseChangeScalar M (algebraMap F M (a i)) •
        pullbackGlobalSections (D.baseChangeToXTwice K M) D.L (D.sectionOf (D.basis i))))
  rw [ha' j, Scheme.Modules.Hom.app_smul]
  exact congrArg
    (fun z => (D.baseChangeFamily K).baseChangeScalar M
        (algebraMap F M (a (finCongr (D.finrank_baseChangeFamily K) j))) • z)
    (D.pullbackCompModuleIso_hom_app_sectionOf_basis K M j)

/-- **The divisor of the base-changed situation, with its structure morphism, is the base change
of the divisor of the original one.** This is the cartesian square that
`AlgebraicGeometry.smooth_of_smooth_pullback_snd_spec_algebraMap` consumes: smoothness of
`H_{a'} ⟶ Spec M` gives smoothness of `H_a ⟶ Spec F`.

The comparison morphism is left existentially quantified because the identification of the two
ideal sheaves (`Stacks.Bertini.FamilyDivisors.specializedDivisor_baseChangeFamily_eq_comap`) is
what identifies the two subschemes, and rewriting along it changes the type of the morphism. -/
theorem exists_isPullback_specializedDivisor_baseChangeFamily
    (a : Fin (Module.finrank D.k D.V) → F)
    (a' : Fin (Module.finrank (D.baseChangeFamily K).k (D.baseChangeFamily K).V) → M)
    (ha' : ∀ j, a' j = algebraMap F M (a (finCongr (D.finrank_baseChangeFamily K) j))) :
    ∃ p : ((D.baseChangeFamily K).specializedDivisor M a').subscheme ⟶
        (D.specializedDivisor F a).subscheme,
      IsPullback p (((D.baseChangeFamily K).specializedDivisor M a').subschemeι ≫
          (D.baseChangeFamily K).baseChangeToSpec M)
        ((D.specializedDivisor F a).subschemeι ≫ D.baseChangeToSpec F)
        (Spec.map (CommRingCat.ofHom (algebraMap F M))) := by
  rw [D.specializedDivisor_baseChangeFamily_eq_comap K F M a a' ha']
  exact ⟨_, (isPullback_subschemeι_comap (D.specializedDivisor F a)
    (D.baseChangeComparison K F M)).flip.paste_vert
    (D.isPullback_baseChangeComparison K F M)⟩

end Stacks.Bertini.FamilyDivisors

end
