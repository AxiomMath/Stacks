module

public import StacksFrontier.AlgebraicGeometry.Flatness.FlatteningFunctor.FlatDimensionEtaleComparison

/-!
# Transporting the flat-dimension condition between étale charts

In Situation 05MT the functor `F_n` depends on the triple `(f : X ⟶ S, F, n)`. This file records
the ways in which two such triples presenting "the same" family give the same functor, which is
what an algebraic space presented by different étale charts needs.

## Main results

* `AlgebraicGeometry.FlatDimensionSituation.isFlat_mk_iff_of_eq_of_iso`: the condition is
  unchanged when the morphism is replaced by an equal one and the module by an isomorphic one.
* `AlgebraicGeometry.FlatDimensionSituation.etaleChart_isFlat_iff_of_surjective`: for a
  surjective étale chart `h : X' ⟶ X` the functor of `(h ≫ f, h^* F)` is `F_n`, by the two
  assertions of Stacks 05UD.
* `AlgebraicGeometry.FlatDimensionSituation.isFlat_iff_of_surjective_etale`: the same for a
  triple `(f', F')` on `X'` with `f' = h ≫ f` and `F' ≅ h^* F`.
* `AlgebraicGeometry.FlatDimensionSituation.isFlat_iff_forall_etaleChart_of_relation`: if
  `p₁, p₂ : R ⟶ X` are étale with `p₁ ≫ f = p₂ ≫ f` and `p₁^* F ≅ p₂^* F`, and finitely many
  étale charts `hⱼ : Wⱼ ⟶ X` have the property that every point of `Ass_{X/S}(F)` over the image
  of `T` is related through `R` to a point of the image of some `hⱼ`, then `F_T` is flat in
  dimensions `≥ n` exactly when every chart is. This is the second assertion of Stacks 05UD for
  the charts `Wⱼ ×_{X, p₁} R ⟶ X` through `p₂`, whose images are the `R`-saturations of the images
  of the `hⱼ`.

## Implementation notes

The relation `R` is the one an étale chart `U ⟶ X` of an algebraic space carries,
`R = U ×_X U`: two points of `U` lie over the same point of the space exactly when they are
related through `R`, and the restriction of a module on the space to `U` pulls back to
isomorphic modules along the two projections. That is the only use made of it.

## References

* [Stacks Project, Tag 05UD](https://stacks.math.columbia.edu/tag/05UD)
* [Stacks Project, Tag 05MT](https://stacks.math.columbia.edu/tag/05MT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

namespace FlatDimensionSituation

attribute [local instance] isQuasicoherent_pullback_obj' isFiniteType_pullback_obj'

/-- The condition after base change is unchanged when the morphism of the situation is replaced
by an equal one and its module by an isomorphic one. -/
theorem isFlat_mk_iff_of_eq_of_iso {S X : Scheme.{u}} {f g : X ⟶ S} (hfg : f = g)
    [LocallyOfFiniteType f] [LocallyOfFiniteType g] {F G : X.Modules} [F.IsQuasicoherent]
    [F.IsFiniteType] [G.IsQuasicoherent] [G.IsFiniteType] (e : F ≅ G) (n : ℕ) (T : Over S) :
    ({ S := S, X := X, f := f, F := F, n := n } :
        FlatDimensionSituation.{u}).IsFlatInDimensionsGEAfterBaseChange T ↔
      ({ S := S, X := X, f := g, F := G, n := n } :
        FlatDimensionSituation.{u}).IsFlatInDimensionsGEAfterBaseChange T := by
  subst hfg
  exact isFlatOverInDimensionsGE_iff_of_moduleIso _
    ((Scheme.Modules.pullback (pullback.fst f T.hom)).mapIso e) n

variable (D : FlatDimensionSituation.{u})

/-- **Stacks 05UD for a surjective chart.** For a surjective étale morphism `h : X' ⟶ X`, the
functor of `(h ≫ f, h^* F)` is `F_n`: one inclusion is the first assertion of Stacks 05UD, and
the other its second assertion, the image of `h` containing the whole relative assassin. -/
theorem etaleChart_isFlat_iff_of_surjective {X' : Scheme.{u}} (h : X' ⟶ D.X) [Etale h]
    (hs : Function.Surjective h) (T : Over D.S) :
    (D.etaleChart h).IsFlatInDimensionsGEAfterBaseChange T ↔
      D.IsFlatInDimensionsGEAfterBaseChange T :=
  ((D.isFlat_etaleChart_and_iff_of_relativeAssassin_subset h).2
    (fun x _ ↦ hs x) T).symm

/-- **A triple presented on a surjective étale chart.** Let `h : X' ⟶ X` be surjective and
étale, and let `(f', F')` be a triple on `X'` with `f' = h ≫ f` and `F' ≅ h^* F`. Then the
functor of `(f', F')` is `F_n`. -/
theorem isFlat_iff_of_surjective_etale {X' : Scheme.{u}} (h : X' ⟶ D.X) [Etale h]
    (hs : Function.Surjective h) {f' : X' ⟶ D.S} [LocallyOfFiniteType f'] (hf' : f' = h ≫ D.f)
    {F' : X'.Modules} [F'.IsQuasicoherent] [F'.IsFiniteType]
    (e : F' ≅ (Scheme.Modules.pullback h).obj D.F) (T : Over D.S) :
    ({ S := D.S, X := X', f := f', F := F', n := D.n } :
        FlatDimensionSituation.{u}).IsFlatInDimensionsGEAfterBaseChange T ↔
      D.IsFlatInDimensionsGEAfterBaseChange T :=
  (isFlat_mk_iff_of_eq_of_iso hf' e D.n T).trans (D.etaleChart_isFlat_iff_of_surjective h hs T)

/-- **The second assertion of Stacks 05UD through an étale relation.** Let `p₁, p₂ : R ⟶ X` be
étale with `p₁ ≫ f = p₂ ≫ f` and `p₁^* F ≅ p₂^* F`, and let `hⱼ : Wⱼ ⟶ X` be étale. Let `T` be a
scheme over `S` such that every point of `Ass_{X/S}(F)` lying over the image of `T` is the image
under `p₂` of a point of `R` whose image under `p₁` lies in the image of some `hⱼ`. Then `F_T` is
flat over `T` in dimensions `≥ n` as soon as the module of every chart `hⱼ` is.

The charts to which Stacks 05UD is applied are `kⱼ = Wⱼ ×_{X, p₁} R ⟶ R ⟶ X` through `p₂`: their
images contain the relative assassin over the image of `T`, and the module of `kⱼ` is, through the
isomorphism `p₁^* F ≅ p₂^* F`, the module of the étale chart `Wⱼ ×_{X, p₁} R ⟶ Wⱼ` of `hⱼ`, so its
condition is implied by that of `hⱼ` by the first assertion of Stacks 05UD. -/
theorem isFlat_of_forall_etaleChart_of_relation {R : Scheme.{u}} (p₁ p₂ : R ⟶ D.X) [Etale p₁]
    [Etale p₂] (hp : p₁ ≫ D.f = p₂ ≫ D.f)
    (e : (Scheme.Modules.pullback p₁).obj D.F ≅ (Scheme.Modules.pullback p₂).obj D.F)
    {ι : Type*} {W : ι → Scheme.{u}} (h : ∀ j, W j ⟶ D.X) [∀ j, Etale (h j)] (T : Over D.S)
    (hcov : ∀ x ∈ Stacks.Divisors.relativeAssassin D.f D.F, D.f x ∈ Set.range T.hom →
      ∃ j, ∃ w : W j, ∃ r : R, h j w = p₁ r ∧ p₂ r = x)
    (hT : ∀ j, (D.etaleChart (h j)).IsFlatInDimensionsGEAfterBaseChange T) :
    D.IsFlatInDimensionsGEAfterBaseChange T := by
  let k : ∀ j, pullback (h j) p₁ ⟶ D.X := fun j ↦ pullback.snd (h j) p₁ ≫ p₂
  have hk : ∀ j, Etale (k j) := fun j ↦ inferInstance
  refine D.isFlat_of_forall_etaleChart k T ?_ fun j ↦ ?_
  · intro x hx hxT
    obtain ⟨j, w, r, hwr, rfl⟩ := hcov x hx hxT
    obtain ⟨z, -, hz⟩ := Scheme.Pullback.exists_preimage_pullback w r hwr
    refine ⟨j, z, ?_⟩
    change p₂ (pullback.snd (h j) p₁ z) = p₂ r
    rw [hz]
  · -- the chart `kⱼ` is the étale chart `Wⱼ ×_X R ⟶ Wⱼ` of the chart `hⱼ`
    let C := D.etaleChart (h j)
    have hf : pullback.fst (h j) p₁ ≫ C.f = k j ≫ D.f := by
      change pullback.fst (h j) p₁ ≫ h j ≫ D.f = (pullback.snd (h j) p₁ ≫ p₂) ≫ D.f
      rw [pullback.condition_assoc, hp, Category.assoc]
    let eF : (Scheme.Modules.pullback (pullback.fst (h j) p₁)).obj C.F ≅
        (Scheme.Modules.pullback (k j)).obj D.F :=
      (Scheme.Modules.pullbackComp (pullback.fst (h j) p₁) (h j)).app D.F ≪≫
        (Scheme.Modules.pullbackCongr pullback.condition).app D.F ≪≫
        ((Scheme.Modules.pullbackComp (pullback.snd (h j) p₁) p₁).app D.F).symm ≪≫
        (Scheme.Modules.pullback (pullback.snd (h j) p₁)).mapIso e ≪≫
        (Scheme.Modules.pullbackComp (pullback.snd (h j) p₁) p₂).app D.F
    exact (isFlat_mk_iff_of_eq_of_iso hf eF D.n T).1
      (C.isFlat_etaleChart_of_isFlat (pullback.fst (h j) p₁) T (hT j))

/-- **Stacks 05UD through an étale relation, as an equivalence.** Under the hypotheses of
`AlgebraicGeometry.FlatDimensionSituation.isFlat_of_forall_etaleChart_of_relation`, `F_T` is flat
over `T` in dimensions `≥ n` exactly when the module of every chart `hⱼ` is. -/
theorem isFlat_iff_forall_etaleChart_of_relation {R : Scheme.{u}} (p₁ p₂ : R ⟶ D.X) [Etale p₁]
    [Etale p₂] (hp : p₁ ≫ D.f = p₂ ≫ D.f)
    (e : (Scheme.Modules.pullback p₁).obj D.F ≅ (Scheme.Modules.pullback p₂).obj D.F)
    {ι : Type*} {W : ι → Scheme.{u}} (h : ∀ j, W j ⟶ D.X) [∀ j, Etale (h j)] (T : Over D.S)
    (hcov : ∀ x ∈ Stacks.Divisors.relativeAssassin D.f D.F, D.f x ∈ Set.range T.hom →
      ∃ j, ∃ w : W j, ∃ r : R, h j w = p₁ r ∧ p₂ r = x) :
    D.IsFlatInDimensionsGEAfterBaseChange T ↔
      ∀ j, (D.etaleChart (h j)).IsFlatInDimensionsGEAfterBaseChange T :=
  ⟨fun hT j ↦ D.isFlat_etaleChart_of_isFlat (h j) T hT,
    D.isFlat_of_forall_etaleChart_of_relation p₁ p₂ hp e h T hcov⟩

end FlatDimensionSituation

end AlgebraicGeometry

end
