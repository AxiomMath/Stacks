module

public import StacksFrontier.AlgebraicGeometry.DeRham.WeilCohomology.DeRhamChernSetup
public import StacksFrontier.AlgebraicGeometry.DeRham.WeilCohomology.DeRhamSubbundleDivisor
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ChernClasses.KZeroRule
public import StacksFrontier.AlgebraicGeometry.Chow.VectorBundleKZeroPullback

/-!
# The de Rham situation of Section 45.12 on quasi-compact quasi-separated schemes

The proof of Lemma 0FW9 in the Stacks project applies Weil Cohomology Theories, Proposition 0FI5
to the category `𝒞` of quasi-compact and quasi-separated schemes with
`A(X) = ⨁_{i ≥ 0} H^{2i}_{dR}(X/𝐙)`, after checking the axioms of Section 0FI4. This file does that
over an arbitrary base scheme `B`, with the projective bundle formula (axiom (4), Proposition 0FMT)
as the one input:

* clause (1) and clause (2) and the clauses (3)(a)-(c), from
  `Stacks.WeilCohomology.QCQSScheme`;
* axioms (1) and (3) (Tags 0FM3, 0FMD) and the functor `A`, from `Stacks.DeRhamChern.chernSetup`;
* axiom (2), the decomposition along open and closed pieces, from
  `Stacks.DeRhamClopen.bijective_evenDeRhamPullback`;
* axiom (5) (Lemmas 0FMX, 0FMY), from
  `Stacks.WeilCohomology.QCQSScheme.exists_isBundleEmbedding_deRhamDivisor`.

So, given the bundle formula, there is a unique de Rham total Chern class
(`Stacks.DeRhamChern.existsUnique_isDeRhamTotalChernClass_of_bundleFormula`).

## Main definitions

* `Stacks.DeRhamChern.sourceChernSetup`: the standing situation of Section 45.12.
* `Stacks.DeRhamChern.IsDeRhamTotalChernClass`: the three properties of Tag 0FW9.

## References

* [Stacks Project, Tag 0FW9](https://stacks.math.columbia.edu/tag/0FW9)
* [Stacks Project, Section 0FI4](https://stacks.math.columbia.edu/tag/0FI4)
* [Stacks Project, Tag 0FI5](https://stacks.math.columbia.edu/tag/0FI5)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.WeilCohomology Stacks.DeRhamBaseChange

universe u v₁ w

attribute [local instance] Stacks.Cohomology.Generators.picardGroupAddCommGroup

namespace Stacks.DeRhamChern

/-! ### The three properties of the de Rham total Chern class -/

section Properties

variable {S : Scheme.{u}} {C : Type w} [Category.{v₁} C] (T : C ⥤ Over S)

/-- **The three properties of the de Rham total Chern class of Tag 0FW9.** A rule `c` assigns to
every object `X` of `𝒞` and every class `α ∈ K₀(Vect(X))` the components
`c X α n ∈ H^{2n}_{dR}(X/S)` of an element of `∏_{n ≥ 0} H^{2n}_{dR}(X/S)`, read in the
even-degree ring; and

1. `c(α + β) = c(α) c(β)`, the product of `∏_n H^{2n}_{dR}(X/S)` being the convolution of cup
   products, and `c(0) = 1`;
2. `c(f^*α) = f^*c(α)` for every morphism `f : X ⟶ Y` of `𝒞`, on all of `K₀(Vect(Y))`;
3. `c([ℒ]) = 1 + c₁^{dR}(ℒ)` for every invertible module `ℒ`. -/
structure IsDeRhamTotalChernClass
    (c : ∀ X : C, VectorBundleKZero (T.obj X).left → ℕ → evenDeRhamRing (T.obj X).hom) :
    Prop where
  /-- The `n`-th component lies in `H^{2n}_{dR}(X/S)`. -/
  mem_grade : ∀ (X : C) (α : VectorBundleKZero (T.obj X).left) (n : ℕ),
    c X α n ∈ AlgebraicGeometry.SheafOfModules.evenDeRhamGrade _ _ n
  /-- **Property (1)**: `c(α + β) = c(α) c(β)`. -/
  map_add : ∀ (X : C) (α β : VectorBundleKZero (T.obj X).left) (n : ℕ),
    c X (α + β) n = ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, c X α p.1 * c X β p.2
  /-- **Property (1)**: `c(0) = 1`. -/
  map_zero : ∀ (X : C) (n : ℕ), c X 0 n = if n = 0 then 1 else 0
  /-- **Property (2)**: `c(f^*α) = f^*c(α)` on `K₀(Vect(Y))`, for the pullback homomorphism
  `AlgebraicGeometry.VectorBundleKZero.pullbackRingHom` of `K₀(Vect(-))`. -/
  map_pull : ∀ {X Y : C} (f : X ⟶ Y) (α : VectorBundleKZero (T.obj Y).left) (n : ℕ),
    pull T f (c Y α n) = c X (VectorBundleKZero.pullbackRingHom (T.map f).left α) n
  /-- **Property (3)**: `c([ℒ]) = 1 + c₁^{dR}(ℒ)`. -/
  invertible : ∀ (X : C) (L : (T.obj X).left.Modules)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible (T.obj X).left.presheaf
      (T.obj X).left.ringCatSheaf.2 L) (n : ℕ),
    c X (VectorBundleKZero.classOf (T.obj X).left L) n =
      if n = 0 then 1 else if n = 1 then c₁ T X (picardClassOf (T.obj X).left L hL) else 0

/-- **On the standing situation of even-degree de Rham cohomology, a total Chern class in the
sense of Tag 0FI5 is a de Rham total Chern class in the sense of Tag 0FW9.** Property (2) is read
on the classes of finite locally free modules (and on additive maps with the generator property) on
the left and on all of `K₀(Vect(-))` on the right; the two agree because those classes
generate. -/
theorem isTotalChernClassOnLocallyFree_chernSetup_iff
    (bundleDatum : ∀ (X : C) (E : ((T ⋙ Over.forget S).obj X).Modules) (r : ℕ),
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (r + 1) →
        BundleDatum (T ⋙ Over.forget S) X E r)
    (bijective_bundleFormula : ∀ (X : C) (E : ((T ⋙ Over.forget S).obj X).Modules) (r : ℕ)
      (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (r + 1)),
      Function.Bijective fun a : Fin (r + 1) → evenDeRhamRing (T.obj X).hom =>
        ∑ i : Fin (r + 1),
          c₁ T (bundleDatum X E r hE).bundle (bundleDatum X E r hE).twistClass ^ (i : ℕ) *
            pull T (bundleDatum X E r hE).proj (a i))
    (c : ∀ X : C, VectorBundleKZero (T.obj X).left → ℕ → evenDeRhamRing (T.obj X).hom) :
    IsTotalChernClassOnLocallyFree (chernSetup T bundleDatum bijective_bundleFormula) c ↔
      IsDeRhamTotalChernClass T c :=
  ⟨fun h =>
    { mem_grade := h.mem_grade
      map_add := h.map_add
      map_zero := h.map_zero
      map_pull := fun f α n => h.map_pull_kZero f
        (VectorBundleKZero.pullbackRingHom (T.map f).left).toAddMonoidHom
        (fun E => VectorBundleKZero.pullbackRingHom_classOf _ E) α n
      invertible := h.invertible },
   fun h =>
    { mem_grade := h.mem_grade
      map_add := h.map_add
      map_zero := h.map_zero
      map_pull := fun {X Y} f E hE n =>
        (h.map_pull f (VectorBundleKZero.classOf _ E) n).trans
          (congrArg (fun α => c X α n)
            (VectorBundleKZero.pullbackRingHom_classOf (T.map f).left E hE))
      map_pull_kZero := fun f κ hκ α n => by
        have hκ' : κ = (VectorBundleKZero.pullbackRingHom (T.map f).left).toAddMonoidHom :=
          VectorBundleKZero.addHom_ext fun E hE =>
            (hκ E hE).trans
              (VectorBundleKZero.pullbackRingHom_classOf _ E hE).symm
        rw [hκ']
        exact h.map_pull f α n
      invertible := h.invertible }⟩

end Properties

/-! ### The standing situation on quasi-compact and quasi-separated schemes over `B` -/

section Source

variable (B : Scheme.{u})
  (hbundle : ∀ (X : (QCQSScheme B).FullSubcategory)
    (E : (((QCQSScheme B).ι ⋙ Over.forget B).obj X).Modules) (r : ℕ)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (r + 1)),
    Function.Bijective fun a : Fin (r + 1) → evenDeRhamRing ((QCQSScheme B).ι.obj X).hom =>
      ∑ i : Fin (r + 1),
        c₁ (QCQSScheme B).ι (QCQSScheme.bundleObject X E r hE).toBundleDatum.bundle
            (QCQSScheme.bundleObject X E r hE).toBundleDatum.twistClass ^ (i : ℕ) *
          pull (QCQSScheme B).ι (QCQSScheme.bundleObject X E r hE).toBundleDatum.proj (a i))

/-- **The standing situation of Section 45.12 for even-degree de Rham cohomology on
quasi-compact and quasi-separated schemes over `B`**, given the projective bundle formula
`hbundle` (axiom (4)): `A(X) = ⨁_i H^{2i}_{dR}(X/B)`, graded by `A^i = H^{2i}_{dR}`, with the
projective bundles, the open and closed subschemes and the decomposition of `A` along them. -/
def sourceChernSetup :
    SourceChernSetup.{u, u, u, u + 1} (QCQSScheme B).FullSubcategory (QCQSScheme.toScheme B) :=
  { chernSetup (QCQSScheme B).ι (fun X E r hE => (QCQSScheme.bundleObject X E r hE).toBundleDatum)
      hbundle with
    compactSpace := fun X => QCQSScheme.compactSpace X
    isInternal_grade := fun _ => AlgebraicGeometry.SheafOfModules.isInternal_evenDeRhamGrade _ _
    bundleObject := QCQSScheme.bundleObject
    bundleDatum_eq := fun _ _ _ _ => rfl
    clopenSubobject := QCQSScheme.clopenSubobject
    bijective_pull_clopenSubobject := fun X _ _ U hU hdisj hcov =>
      Stacks.DeRhamClopen.bijective_evenDeRhamPullback X.obj.hom U hU hdisj hcov
    mem_grade_of_pull_clopenSubobject := fun X _ _ U hU hdisj hcov a n h =>
      Stacks.DeRhamClopen.mem_evenDeRhamGrade_of_evenDeRhamPullback X.obj.hom U hU hdisj hcov a n
        h }

/-- **Axiom (3) of Section 45.12** for the de Rham situation (Tag 0FMD). -/
theorem pullbackFirstChernCondition_sourceChernSetup :
    PullbackFirstChernCondition (sourceChernSetup B hbundle) :=
  fun f L hL => pull_c₁ (QCQSScheme B).ι f L hL

/-- **Clause (3)(b) of Section 45.12** for the de Rham situation. -/
theorem bundleCompareClause_sourceChernSetup : BundleCompareClause (sourceChernSetup B hbundle) :=
  fun X X' f E r hE hE' => QCQSScheme.exists_isBundleCompare X X' f E r hE hE'

/-- **Clause (3)(c) and axiom (5) of Section 45.12** for the de Rham situation (Lemmas 0FMX and
0FMY). -/
theorem divisorDatumClause_sourceChernSetup : DivisorDatumClause (sourceChernSetup B hbundle) :=
  fun X T hT _ r hF hE => QCQSScheme.exists_isBundleEmbedding_deRhamDivisor X T hT r hF hE

include hbundle in
/-- **The de Rham total Chern class on quasi-compact and quasi-separated schemes over `B`, given
the projective bundle formula** (the proof of Tag 0FW9, Proposition 0FI5 applied to the de Rham
situation): there is a unique rule with the three properties of
`Stacks.DeRhamChern.IsDeRhamTotalChernClass`. -/
theorem existsUnique_isDeRhamTotalChernClass_of_bundleFormula :
    ∃! c : ∀ X : (QCQSScheme B).FullSubcategory,
        VectorBundleKZero ((QCQSScheme B).ι.obj X).left → ℕ →
          evenDeRhamRing ((QCQSScheme B).ι.obj X).hom,
      IsDeRhamTotalChernClass (QCQSScheme B).ι c :=
  (existsUnique_congr fun c => isTotalChernClassOnLocallyFree_chernSetup_iff (QCQSScheme B).ι
    (fun X E r hE => (QCQSScheme.bundleObject X E r hE).toBundleDatum) hbundle c).mp
    (existsUnique_isTotalChernClass_of_source (sourceChernSetup B hbundle)
      (pullbackFirstChernCondition_sourceChernSetup B hbundle)
      (bundleCompareClause_sourceChernSetup B hbundle)
      (divisorDatumClause_sourceChernSetup B hbundle))

end Source

end Stacks.DeRhamChern

end
