module

public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.MemberPerMemberIso
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.MemberPairNaturality
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.MemberSiteComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.MemberEffectivity

/-!
# Descent of quasi-coherent modules along a Zariski covering of an algebraic space

Let `X` be an algebraic space over a scheme `S` and let `(f i : Y i ⟶ X)` be a Zariski covering of
`X`. The canonical descent functor of the covering, from quasi-coherent `𝒪_X`-modules to descent
data for quasi-coherent modules relative to the covering, is an equivalence: every descent datum is
effective and the functor is fully faithful.

All names below are in the namespace `AlgebraicGeometry.Space.QuasiCoherentDescent`.

## Main results

* `memberReading_app_apply`: a family of isomorphisms `τ i : (f i)^*M ≅ D.F i` and an isomorphism
  `β` of the restriction of `M` to the site of the charts of the members, whose components agree,
  agree on every section over a chart of a member.
* `memberReading_compat`: the readings of such a family `τ` agree over the charts of the pairwise
  fibre products.
* `exists_memberReading`: every descent datum relative to a family of algebraic spaces étale over
  `X` whose charts are cover dense admits a quasi-coherent `𝒪_X`-module `M` and isomorphisms
  `τ i : (f i)^*M ≅ D.F i` whose readings agree over the charts of the pairwise fibre products.
* `isEquivalence_etaleCanonicalDescentFunctor_of_isZariskiCovering`: the canonical descent functor
  of a Zariski covering of an algebraic space is an equivalence.
* `isEtaleEffective_and_fullyFaithful_of_isZariskiCovering`: for a Zariski covering of an algebraic
  space, every descent datum for quasi-coherent modules is effective and the canonical descent
  functor is fully faithful.

## References

* [Stacks Project, Tag 04W6](https://stacks.math.columbia.edu/tag/04W6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Space.QuasiCoherentDescent

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {I : Type v} {X : AlgebraicSpaces B S hS} (Yi : I → AlgebraicSpaces B S hS)
  (f : ∀ i, Yi i ⟶ X) (hf : ∀ i, IsEtale B S hS (f i).hom)

section CoverDense

variable [hcd : (memberFunctor B S hS Yi f hf).IsCoverDense (SmallEtale.topology B S hS X.1)]

section Reading

variable (D : DescentDatum B S hS Yi f)
  (hL : MemberAbLaws B S hS Yi f hf (fun p => ↥(memberDatumObj B S hS Yi f hf D p))
    (fun _ => inferInstance)
    (fun p q g m => (memberDatumAbTransHom B S hS Yi f hf D p q g).val.app
      (Opposite.op (chartSpaceIdChart B S hS (Yi q.unop.1) q.unop.2))
      (memberDatumAbRestrFn B S hS Yi f hf D p q g m)))
  (hM : MemberModLaws B S hS Yi f hf (memberDatumObj B S hS Yi f hf D)
    (fun p q g m => (memberDatumAbTransHom B S hS Yi f hf D p q g).val.app
      (Opposite.op (chartSpaceIdChart B S hS (Yi q.unop.1) q.unop.2))
      (memberDatumAbRestrFn B S hS Yi f hf D p q g m)))
  (hsh : Presheaf.IsSheaf (memberTopology B S hS Yi f hf)
    (memberFunctorOfLawsV B S hS Yi f hf hL))
  (M : Modules.{u, u} B S hS X.1 X.2)
  (β : (memberRestriction B S hS Yi f hf).obj M ≅
    memberSheafOfLaws B S hS Yi f hf hL hM hsh)
  (τ : ∀ i, (etaleModulePullback.{u, u} B S hS (f i) (hf i)).obj M ≅ D.F i)
  (hτ : ∀ (i : I) (V : SmallEtale B S hS (Yi i).1),
    (τ i).hom.val.app (Opposite.op V) =
      β.hom.val.app (Opposite.op (memberPair B S hS Yi f hf i V)))

include hτ in
/-- If the components of `τ i` are the components of `β` at the objects `(i, V)`, then `τ i` and
`β` agree on every section over a chart `V` of the member `Y i`. -/
theorem memberReading_app_apply (i : I) (V : SmallEtale B S hS (Yi i).1)
    (t : ((etaleModulePullback.{u, u} B S hS (f i) (hf i)).obj M).val.obj (Opposite.op V)) :
    (τ i).hom.val.app (Opposite.op V) t =
      β.hom.val.app (Opposite.op (memberPair B S hS Yi f hf i V)) t :=
  apply_congr (hτ i V) fun φ => ModuleCat.Hom.hom φ t

include β hτ in
/-- The readings of the per-member isomorphisms `τ i` agree over the charts of the pairwise fibre
products `Y i ×_X Y j`. -/
theorem memberReading_compat (i j : I)
    (Z : SmallEtale B S hS (pair B S hS Yi f i j).1)
    (σ : M.val.obj (Opposite.op ((smallEtalePostcomp B S hS (f i) (hf i)).obj
      ((smallEtalePostcomp B S hS (pairFst B S hS Yi f i j)
        (isEtale_pairFst B S hS Yi f hf i j)).obj Z)))) :
    (τ j).hom.val.app
        (Opposite.op ((smallEtalePostcomp B S hS (pairSnd B S hS Yi f i j)
          (isEtale_pairSnd B S hS Yi f hf i j)).obj Z))
        (M.val.map (pairChartConnect B S hS Yi f hf Z).op σ) =
      etaleSect B S hS (pairSnd B S hS Yi f i j)
          (isEtale_pairSnd B S hS Yi f hf i j) (D.F j) Z
        ((D.transition i j).hom.val.app (Opposite.op Z)
          (etaleSectInv B S hS (pairFst B S hS Yi f i j)
            (isEtale_pairFst B S hS Yi f hf i j) (D.F i) Z
            ((τ i).hom.val.app
              (Opposite.op ((smallEtalePostcomp B S hS (pairFst B S hS Yi f i j)
                (isEtale_pairFst B S hS Yi f hf i j)).obj Z)) σ))) :=
  ((memberReading_app_apply B S hS Yi f hf D hL hM hsh M β τ hτ j _
          (M.val.map (pairChartConnect B S hS Yi f hf Z).op σ)).trans
      (memberNaturality_on_pairChart B S hS Yi f hf D hL hM hsh M β i j Z σ)).trans
    (apply_congr (memberReading_app_apply B S hS Yi f hf D hL hM hsh M β τ hτ i _ σ)
        (fun t => etaleSect B S hS (pairSnd B S hS Yi f i j)
            (isEtale_pairSnd B S hS Yi f hf i j) (D.F j) Z
          ((D.transition i j).hom.val.app (Opposite.op Z)
            (etaleSectInv B S hS (pairFst B S hS Yi f i j)
              (isEtale_pairFst B S hS Yi f hf i j) (D.F i) Z t)))).symm

end Reading

include hcd in
/-- Every descent datum `D` relative to a family of algebraic spaces étale over `X` whose charts
are cover dense admits a quasi-coherent `𝒪_X`-module `M` and a family of isomorphisms
`τ i : (f i)^*M ≅ D.F i` whose readings agree over the charts of the pairwise fibre products. -/
theorem exists_memberReading (D : DescentDatum B S hS Yi f) :
    ∃ (M : Modules.{u, u} B S hS X.1 X.2) (_ : M.IsQuasicoherentOnSite)
      (τ : ∀ i, (etaleModulePullback.{u, u} B S hS (f i) (hf i)).obj M ≅ D.F i),
      ∀ (i j : I) (Z : SmallEtale B S hS (pair B S hS Yi f i j).1)
        (σ : M.val.obj (Opposite.op ((smallEtalePostcomp B S hS (f i) (hf i)).obj
          ((smallEtalePostcomp B S hS (pairFst B S hS Yi f i j)
            (isEtale_pairFst B S hS Yi f hf i j)).obj Z)))),
        (τ j).hom.val.app
            (Opposite.op ((smallEtalePostcomp B S hS (pairSnd B S hS Yi f i j)
              (isEtale_pairSnd B S hS Yi f hf i j)).obj Z))
            (M.val.map (pairChartConnect B S hS Yi f hf Z).op σ) =
          etaleSect B S hS (pairSnd B S hS Yi f i j)
              (isEtale_pairSnd B S hS Yi f hf i j) (D.F j) Z
            ((D.transition i j).hom.val.app (Opposite.op Z)
              (etaleSectInv B S hS (pairFst B S hS Yi f i j)
                (isEtale_pairFst B S hS Yi f hf i j) (D.F i) Z
                ((τ i).hom.val.app
                  (Opposite.op ((smallEtalePostcomp B S hS (pairFst B S hS Yi f i j)
                    (isEtale_pairFst B S hS Yi f hf i j)).obj Z)) σ))) := by
  obtain ⟨M, ⟨β⟩⟩ := (essSurj_memberRestriction_anyIndex B S hS Yi f hf).mem_essImage
    (memberSheafOfLaws B S hS Yi f hf (memberDatumAb_laws B S hS Yi f hf D)
      (memberDatumAb_mod_laws B S hS Yi f hf D)
      (isSheaf_memberDatumAbFunctor B S hS Yi f hf D (memberDatumAb_laws B S hS Yi f hf D)))
  obtain ⟨τ, hτ⟩ := exists_memberPerMemberIso B S hS Yi f hf D _ _ _ M β
  exact ⟨M, isQuasicoherentOnSite_of_memberDatumSheaf_iso B S hS Yi f hf D _ _ _ M β, τ,
    memberReading_compat B S hS Yi f hf D _ _ _ M β τ hτ⟩

end CoverDense

/-! ### The equivalence for a Zariski covering -/

/-- The canonical descent functor of a Zariski covering of an algebraic space is an
equivalence. -/
theorem isEquivalence_etaleCanonicalDescentFunctor_of_isZariskiCovering
    (hcov : IsZariskiCovering B S hS I (fun i => (Yi i).1) (fun i => (f i).hom)) :
    (etaleCanonicalDescentFunctor B S hS Yi f hf).IsEquivalence :=
  have := isCoverDense_memberFunctor_of_isZariskiCovering B S hS Yi f hf hcov
  isEquivalence_etaleCanonicalDescentFunctorOfIsZariskiCovering B S hS Yi f hf hcov
    (exists_memberReading B S hS Yi f hf)

/-! ### The two clauses of the tag -/

/-- For a Zariski covering of an algebraic space, every descent datum for quasi-coherent modules is
effective, and the canonical descent functor is fully faithful. -/
@[stacks 04W6]
theorem isEtaleEffective_and_fullyFaithful_of_isZariskiCovering
    (hcov : IsZariskiCovering B S hS I (fun i => (Yi i).1) (fun i => (f i).hom)) :
    (∀ D : DescentDatum B S hS Yi f, IsEtaleEffective B S hS Yi f hf D) ∧
      (etaleCanonicalDescentFunctor B S hS Yi f hf).Full ∧
        (etaleCanonicalDescentFunctor B S hS Yi f hf).Faithful :=
  have := isEquivalence_etaleCanonicalDescentFunctor_of_isZariskiCovering B S hS Yi f hf hcov
  ⟨isEtaleEffective_of_essSurj B S hS Yi f hf (Functor.EssSurj.mk fun D =>
      Functor.IsEquivalence.essSurj.mem_essImage D),
    inferInstance, inferInstance⟩

end AlgebraicGeometry.Space.QuasiCoherentDescent

end
