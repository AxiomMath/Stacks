module

public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
public import StacksFrontier.AlgebraicGeometry.ProEtale.BoundedLocallyConstantInduction
public import StacksFrontier.AlgebraicGeometry.ProEtale.CoefficientRestrictionInverseImage
public import StacksFrontier.AlgebraicGeometry.ProEtale.CompletedConstantClopenModel
public import StacksFrontier.AlgebraicGeometry.ProEtale.LocallyConstantAdicModel
public import StacksCore.Tactic.StacksAttribute

/-!
# The finite disjoint covering carrying adic models of a constructible complex

Let `X` be a weakly contractible affine scheme, `Λ` a Noetherian ring and `I ⊆ Λ` an ideal, and
let `K` be an object of `D_cons(X, Λ)` whose derived reduction `K ⊗_Λ^L \underline{Λ/I}` has
locally constant cohomology sheaves. Stacks 09C3 asserts that `X` decomposes into a finite
disjoint union of opens `U_i` such that on each `U_i` the complex `K` is represented by a complex
`(\underline{M^a})^∧ → ⋯ → (\underline{M^b})^∧` of completed constant sheaves attached to finite
projective `Λ^∧`-modules, for some maps of sheaves between them. This file proves it.

## Main results

* `AlgebraicGeometry.ProEtale.hasFiniteDisjointCompletedConstantModel_of_isLocallyConstant`:
  Stacks 09C3.

## The proof

The source argues by induction on the length of the range `[a, b]` given by Stacks 09C2: the
top cohomology sheaf `H^b(K)` is derived complete, its reduction is locally constant of finite
type, Stacks 09BZ gives a surjection `(\underline{Λ}^∧)^{⊕t} → H^b(K)`, which lifts to
`(\underline{Λ}^∧)^{⊕t}[-b] → K`; its cone has the same properties on `[a, b - 1]`, and a model
of the cone extends by one term to a model of `K`. The case `a = b` is treated on a finite
disjoint open covering on which the reduction is constant.

Here the induction is run on `X` itself, without restricting to opens, in
`AlgebraicGeometry.ProEtale.exists_complex_of_hasBoundedLocallyConstantReduction`: it produces
one complex representing `K` on all of `X` whose terms in degrees above `a` are finite direct
sums of copies of `\underline{Λ}^∧`, and whose term `F` in degree `a` satisfies the hypotheses of
the base case. Only then is `X` decomposed: `F ⊗ \underline{Λ/I}` is constant on the members of a
clopen decomposition of `X`, and on each member `F` is the completed constant sheaf of a finite
projective `Λ^∧`-module (`AlgebraicGeometry.ProEtale.exists_clopenDecomposition_inverseImage_iso`).
Restricting the global complex to the members gives the conclusion, the restriction of
`\underline{Λ}^∧` being `\underline{Λ}^∧`.

The induction works in the derived category of sheaves of `Λ`-modules, where the reduction is a
derived tensor product; it is transported to `D(X_proét, Λ)` along
`AlgebraicGeometry.ProEtale.derivedModuleEquiv`, and the restriction to an open along
`AlgebraicGeometry.ProEtale.CoefficientRestriction.ofWeaklyEtale` is identified with the inverse
image of sheaves of `Λ`-modules by
`AlgebraicGeometry.ProEtale.coefficientRestrictionIsoInverseImage`.

## References

* [Stacks Project, Tag 09C3](https://stacks.math.columbia.edu/tag/09C3)
* [Stacks Project, Tag 09C2](https://stacks.math.columbia.edu/tag/09C2)
* [Stacks Project, Tag 09BZ](https://stacks.math.columbia.edu/tag/09BZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u w

namespace AlgebraicGeometry.ProEtale

attribute [local instance] HasDerivedCategory.standard
  SheafOfModules.hasSheafify_commRingCat
  Stacks.hasSheafCompose_forget₂_commRingCat

variable (X : Scheme.{u}) (Λ : Type (max (u + 1) w)) [CommRing Λ] (I : Ideal Λ)
  [IsNoetherianRing Λ]

/-- **Stacks 09C3.** Let `X` be a weakly contractible affine scheme, `Λ` a Noetherian ring,
`I ⊆ Λ` an ideal and `K` an object of `D_cons(X, Λ)` such that the cohomology sheaves of
`K ⊗_Λ^L \underline{Λ/I}` are locally constant. Then there are a finite disjoint open covering
`X = ∐ U_i` and, for each `i`, finite projective `Λ^∧`-modules `M^a, …, M^b` such that `K|_{U_i}`
is represented in `D(U_{i, proét}, Λ)` by a complex
`(\underline{M^a})^∧ → ⋯ → (\underline{M^b})^∧` for some maps of sheaves of `Λ`-modules between
consecutive terms.

The covering, the restrictions and the models are those of
`AlgebraicGeometry.ProEtale.HasFiniteDisjointCompletedConstantModel`; weak contractibility of `X`
is that of Stacks 090L. -/
@[stacks 09C3]
theorem hasFiniteDisjointCompletedConstantModel_of_isLocallyConstant [IsAffine X]
    (hX : ProetaleWContractible.IsWeaklyContractibleObj X)
    (K : DerivedSheaves.{u, max (u + 1) w, w} X Λ)
    (hK : IsConstructibleViaDerivedReduction.{u, w} X Λ I K)
    (hloc : ∀ i : ℤ, Stacks.ConstantSheaf.IsLocallyConstant (Scheme.ProEt.topology X)
      ((DerivedCategory.homologyFunctor _ i).obj ((derivedReduction.{u, w} X Λ I).obj K))) :
    HasFiniteDisjointCompletedConstantModel.{u, max (u + 1) w, w} X Λ I K := by
  let E := constantCoefficientModuleEquiv.{u, max (u + 1) w, w} X Λ
  let e := derivedModuleEquiv.{u, max (u + 1) w, w} X Λ
  let : E.functor.Additive := Functor.additive_of_preserves_binary_products _
  obtain ⟨a, b, hd⟩ := exists_hasBoundedLocallyConstantReduction X Λ I K hK hloc
  obtain ⟨C, hGE, hLE, ⟨eK⟩, hfree, hbase⟩ :=
    exists_complex_of_hasBoundedLocallyConstantReduction X Λ I hX (max a b - a).toNat
      (e.inverse.obj K) a (max a b) (by omega) (hd.mono le_rfl (le_max_right a b))
  obtain ⟨n, U, hdisj, hcov, hU⟩ := exists_clopenDecomposition_inverseImage_iso X Λ I hX hbase
  refine ⟨n, U, hdisj, hcov, fun i => ?_⟩
  let ρ := CoefficientRestriction.ofWeaklyEtale.{u, max (u + 1) w, w} (U i).ι Λ
  let := ρ.additive
  let := ρ.preservesFiniteLimits
  let := ρ.preservesFiniteColimits
  let EU := constantCoefficientModuleEquiv.{u, max (u + 1) w, w} (U i).toScheme Λ
  let jΛ := proetaleModuleInverseImage.{u, max (u + 1) w, w} (U i).ι Λ
  let C' := (E.functor.mapHomologicalComplex _).obj C
  have hterm : ∀ (k : ℤ) {N}, (jΛ.obj (C.X k) ≅ N) → (ρ.functor.obj (C'.X k) ≅ _) :=
    fun k _ f => (coefficientRestrictionIsoInverseImage (U i).ι Λ).app _ ≪≫
      EU.functor.mapIso (jΛ.mapIso (E.unitIso.app (C.X k)).symm ≪≫ f) ≪≫
      (constantCoefficientModuleEquivFunctorIso.{u, max (u + 1) w, w} (U i).toScheme Λ).app _
  refine ⟨ρ, a, max a b, (ρ.functor.mapHomologicalComplex _).obj C', ?_, ?_, fun k => ?_, ?_⟩
  · rw [CochainComplex.isStrictlyGE_iff]
    intro k hk
    exact ρ.functor.map_isZero (E.functor.map_isZero (C.isZero_of_isStrictlyGE a k hk))
  · rw [CochainComplex.isStrictlyLE_iff]
    intro k hk
    exact ρ.functor.map_isZero (E.functor.map_isZero (C.isZero_of_isStrictlyLE _ k hk))
  · by_cases hk : k = a
    · subst hk
      obtain ⟨M, hM1, hM2, ⟨e'⟩⟩ := hU i
      exact ⟨M, hM1, hM2, ⟨hterm k e'⟩⟩
    · obtain ⟨t, ⟨e₁⟩⟩ := hfree k hk
      obtain ⟨M, hM1, hM2, ⟨e₂⟩⟩ := exists_completedConstantSheaf_iso_biproduct (U i).toScheme Λ I t
      exact ⟨M, hM1, hM2, ⟨hterm k (jΛ.mapIso e₁ ≪≫ jΛ.mapBiproduct _ ≪≫
        biproduct.mapIso (fun _ => proetaleModuleInverseImageCompletedConstantSheafIso
          (U i).ι Λ I _) ≪≫ e₂.symm)⟩⟩
  · exact ⟨ρ.functor.mapDerivedCategory.mapIso ((e.counitIso.app K).symm ≪≫ e.functor.mapIso eK ≪≫
      E.functor.mapDerivedCategoryFactors.app C) ≪≫ ρ.functor.mapDerivedCategoryFactors.app C'⟩

end AlgebraicGeometry.ProEtale

end
