module

public import StacksFrontier.AlgebraicGeometry.ClosedImmersionCohomology.OverField
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.HyperplaneRestrictionConstruction
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.RegularitySectionMultiplication

/-!
# Cohomology on a hyperplane of `ℙⁿ_k` is cohomology of its direct image

The `compare` clause of `AlgebraicGeometry.HyperplaneRestrictionPackage` asks for the
`k`-linear isomorphism

`Hⁱ(ℙᵐ_k, 𝒢) ≅ Hⁱ(ℙ^{m+1}_k, j_*𝒢)`

for the hyperplane inclusion `j : ℙᵐ_k ⟶ ℙ^{m+1}_k`. `AlgebraicGeometry.cohomologyOverField` is
the right derived global sections with scalars restricted along a **given** morphism to
`Spec k`, and
`AlgebraicGeometry.cohomologyOverFieldPushforwardIsoOfIsClosedImmersion` produces the comparison
for the structure morphism `j ≫ (ℙ^{m+1}_k ↘ Spec k)` of `ℙᵐ_k` that `j` induces — not for the
canonical one. The two agree exactly when `j` is a morphism over `Spec k`, and that is the
hypothesis here: two morphisms `ℙᵐ_k ⟶ Spec k` differ by a ring endomorphism of `k`, of which a
field has many, so the clause cannot be dropped.

`AlgebraicGeometry.exists_restrictionSequences` supplies it: the hyperplane it builds is a
closed immersion over `Spec k`.

## Main results

* `AlgebraicGeometry.projectiveHPushforwardIso`: **the `compare` isomorphism**, for a closed
  immersion `ℙᵐ_k ⟶ ℙ^{m+1}_k` over `Spec k`.
* `AlgebraicGeometry.cohomologyOverFieldMap_comp_pushforwardIso_hom` and
  `AlgebraicGeometry.cohomologyOverFieldMap_pushforward_eq_conj`: **the comparison is natural in
  the module.** The map induced on `Hⁱ(ℙⁿ_k, -)` by a direct image `j_*φ` is the map induced by
  `φ`, conjugated by the comparison at its two ends. The second form carries the `eqToIso`
  rewrite of the structure morphism that `projectiveHPushforwardIso` has in it, through
  `AlgebraicGeometry.cohomologyOverFieldMap_congr`.
* `AlgebraicGeometry.exists_restrictionSequences_compare`: the same for the hyperplane of
  `AlgebraicGeometry.exists_restrictionSequences`, with the sequences — both in the shape whose
  first arrow is multiplication by the section on the nose
  (`AlgebraicGeometry.HasMulRestrictionSequences`) and in the shape [Stacks, Tag 0EGK] leaves
  them in — so that a single invocation produces the restriction data together with its
  cohomology comparison.

## Naturality, and what it is for

The `liftSection` clause of `AlgebraicGeometry.HyperplaneRestrictionPackage` separates its two
sides by exactly a conjugation `(compare d).inv ≫ … ≫ (compare (d+1)).hom`, so naturality of the
comparison in the module turns that clause into a statement about the direct image of
multiplication by a section — a statement about *sheaves*. That is what
`AlgebraicGeometry.liftsSectionAlong_of_pushforward_square` does with it.

Both factors of the comparison are components of natural transformations, the second
(`Stacks.Cohomology.ClosedImmersion.closedImmersionCohomologyIso`) being an isomorphism of
functors outright, so the naturality is read off `CategoryTheory.NatTrans.naturality` once
`AlgebraicGeometry.cohomologyOverFieldMap` can be unfolded — which is what the `@[expose]` on it
is for. The proof is given on elements because the two `Scheme.Hom.appLE` proof obligations that
the comparison and `AlgebraicGeometry.cohomologyOverField` each discharge by `simp` are distinct
proof terms of the same `Prop`: definitionally equal, so `exact` crosses the gap, but not
syntactically equal, so `rw` does not.

## References

* [Stacks Project, Tag 089W](https://stacks.math.columbia.edu/tag/089W)
* [Stacks Project, Tag 089Z](https://stacks.math.columbia.edu/tag/089Z)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.AlgebraicGeometry.ProjTwistTensorPow (twistOver)

universe u

namespace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

/-! ### Naturality of the comparison in the module -/

/-- **The comparison of cohomologies along a closed immersion is natural in the module.** For
`φ : ℳ ⟶ 𝒩` on `Z`, the square with sides `Hⁿ(Z, φ)`, `Hⁿ(X, i_*φ)` and the two comparisons
commutes.

Both factors of the comparison are components of natural transformations —
`ModuleCat.restrictScalarsComp'App` for the factorisation `k ⟶ Γ(X, ⊤) ⟶ Γ(Z, ⊤)` of the
structure map, and `Stacks.Cohomology.ClosedImmersion.closedImmersionCohomologyIso`, which is an
isomorphism of *functors* — so what has to be supplied here is only that
`AlgebraicGeometry.cohomologyOverFieldMap` is the derived global sections of `φ` with scalars
restricted, which is what `@[expose]` on that definition makes visible. -/
theorem cohomologyOverFieldMap_comp_pushforwardIso_hom (k : Type u) [Field k]
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (f : X ⟶ Spec (.of k))
    {M N : Z.Modules} (φ : M ⟶ N) (n : ℕ) :
    cohomologyOverFieldMap k (i ≫ f) φ n ≫
        (cohomologyOverFieldPushforwardIsoOfIsClosedImmersion k i f N n).hom =
      (cohomologyOverFieldPushforwardIsoOfIsClosedImmersion k i f M n).hom ≫
        cohomologyOverFieldMap k f ((Scheme.Modules.pushforward i).map φ) n := by
  have hB := (Stacks.Cohomology.ClosedImmersion.closedImmersionCohomologyIso i n).hom.naturality φ
  refine ModuleCat.hom_ext (LinearMap.ext fun a => ?_)
  with_unfolding_all exact congrFun (congrArg (fun g => (ConcreteCategory.hom g : _ → _)) hB) a

/-- **Cohomology on a hyperplane is cohomology of its direct image, as `k`-vector spaces.**
For a closed immersion `j : ℙᵐ_k ⟶ ℙⁿ_k` **over `Spec k`**,
`Hⁱ(ℙᵐ_k, 𝒢) ≅ Hⁱ(ℙⁿ_k, j_*𝒢)`.

This is `AlgebraicGeometry.cohomologyOverFieldPushforwardIsoOfIsClosedImmersion`, whose source
is the cohomology of `𝒢` taken over the structure morphism `j ≫ (ℙⁿ_k ↘ Spec k)` induced by `j`;
the hypothesis `hj` says that morphism **is** the canonical structure morphism of `ℙᵐ_k`, which
is what makes the source `AlgebraicGeometry.projectiveH`. -/
def projectiveHPushforwardIso (k : Type u) [Field k] {m n : ℕ}
    (j : projectiveSpaceOverRing m (.of k) ⟶ projectiveSpaceOverRing n (.of k))
    [IsClosedImmersion j]
    (hj : j ≫ projectiveSpaceToBase k n = projectiveSpaceToBase k m)
    (G : (projectiveSpaceOverRing m (.of k)).Modules) (i : ℕ) :
    projectiveH k m G i ≅
      projectiveH k n ((Scheme.Modules.pushforward j).obj G) i :=
  eqToIso (congrArg (fun φ => cohomologyOverField k φ G i) hj).symm ≪≫
    cohomologyOverFieldPushforwardIsoOfIsClosedImmersion k j (projectiveSpaceToBase k n) G i

/-- `AlgebraicGeometry.cohomologyOverFieldMap` taken along two **equal** morphisms to `Spec k`,
transported by the induced equality of the two cohomologies. This is needed because
`AlgebraicGeometry.projectiveHPushforwardIso` carries the rewrite of the structure morphism of
its source as an `eqToIso`, so its naturality statement has those transports in it. -/
theorem cohomologyOverFieldMap_congr (k : Type u) [Field k] {X : Scheme.{u}}
    {f f' : X ⟶ Spec (.of k)} (h : f = f') {A B : X.Modules} (φ : A ⟶ B) (i : ℕ) :
    cohomologyOverFieldMap k f φ i =
      eqToHom (congrArg (fun g => cohomologyOverField k g A i) h) ≫
        cohomologyOverFieldMap k f' φ i ≫
          eqToHom (congrArg (fun g => cohomologyOverField k g B i) h).symm := by
  subst h
  simp

/-- **The comparison `AlgebraicGeometry.projectiveHPushforwardIso` is natural in the module**: the
map induced on `Hⁱ(ℙⁿ_k, -)` by the direct image `j_*φ` of a morphism `φ` on `ℙᵐ_k` is the map
induced by `φ` on `Hⁱ(ℙᵐ_k, -)`, conjugated by the comparison at the two ends.

This is what makes the `liftSection` clause of `AlgebraicGeometry.HyperplaneRestrictionPackage` —
whose two sides are separated by exactly such a conjugation — equivalent to a statement about the
direct image, hence to a statement about sheaves rather than about cohomology. -/
theorem cohomologyOverFieldMap_pushforward_eq_conj (k : Type u) [Field k] {m n : ℕ}
    (j : projectiveSpaceOverRing m (.of k) ⟶ projectiveSpaceOverRing n (.of k))
    [IsClosedImmersion j]
    (hj : j ≫ projectiveSpaceToBase k n = projectiveSpaceToBase k m)
    {A B : (projectiveSpaceOverRing m (.of k)).Modules} (φ : A ⟶ B) (i : ℕ) :
    cohomologyOverFieldMap k (projectiveSpaceToBase k n)
        ((Scheme.Modules.pushforward j).map φ) i =
      (projectiveHPushforwardIso k j hj A i).inv ≫
        cohomologyOverFieldMap k (projectiveSpaceToBase k m) φ i ≫
          (projectiveHPushforwardIso k j hj B i).hom := by
  have hnat := cohomologyOverFieldMap_comp_pushforwardIso_hom k j
    (projectiveSpaceToBase k n) φ i
  have key : cohomologyOverFieldMap k (projectiveSpaceToBase k n)
        ((Scheme.Modules.pushforward j).map φ) i =
      (cohomologyOverFieldPushforwardIsoOfIsClosedImmersion k j
          (projectiveSpaceToBase k n) A i).inv ≫
        cohomologyOverFieldMap k (j ≫ projectiveSpaceToBase k n) φ i ≫
          (cohomologyOverFieldPushforwardIsoOfIsClosedImmersion k j
            (projectiveSpaceToBase k n) B i).hom := by
    rw [hnat, Iso.inv_hom_id_assoc]
  rw [key, cohomologyOverFieldMap_congr k hj φ i]
  simp [projectiveHPushforwardIso]

/-- **The twisted hyperplane restriction sequences of [Stacks, Tag 08A0] and [Stacks, Tag 0EGK]
over an infinite field, with the degree-zero cohomology comparison of [Stacks, Tag 089W].**

This is `AlgebraicGeometry.exists_restrictionSequences` with the `compare` clause of
`AlgebraicGeometry.HyperplaneRestrictionPackage` adjoined: the hyperplane it produces is a
closed immersion over `Spec k`, so `AlgebraicGeometry.projectiveHPushforwardIso` applies to it
in every cohomological degree and at every twist. -/
theorem exists_restrictionSequences_compare (k : Type u) [Field k] [Infinite k] (m : ℕ)
    (F : (projectiveSpaceOverRing (m + 1) (.of k)).Modules) (hFc : F.IsCoherent) :
    ∃ (G : (projectiveSpaceOverRing m (.of k)).Modules) (_ : G.IsCoherent)
      (j : projectiveSpaceOverRing m (.of k) ⟶ projectiveSpaceOverRing (m + 1) (.of k))
      (_ : IsAffineHom j) (_ : IsClosedImmersion j)
      (_ : ∀ (A : (projectiveSpaceOverRing m (.of k)).Modules) (i : ℕ),
          projectiveH k m A i ≅
            projectiveH k (m + 1) ((Scheme.Modules.pushforward j).obj A) i)
      (s : (twistOver (m + 1) (Spec (.of k)) 1).sections),
      HasMulRestrictionSequences k m F G j s ∧
      ∀ d : ℤ, ∃ (a : projectiveTwist (m + 1) F (d - 1) ⟶ projectiveTwist (m + 1) F d)
        (b : projectiveTwist (m + 1) F d ⟶
          (Scheme.Modules.pushforward j).obj (projectiveTwist m G d))
        (w : a ≫ b = 0), (ShortComplex.mk a b w).ShortExact := by
  obtain ⟨G, hGc, j, hjaff, hjover, hjci, s, hmul, hseq⟩ :=
    exists_restrictionSequences k m F hFc
  exact ⟨G, hGc, j, hjaff, hjci,
    fun A i => projectiveHPushforwardIso k j hjover A i, s, hmul, hseq⟩

end AlgebraicGeometry

end
