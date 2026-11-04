module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatFppfSiteFunctor
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.AffineFlatBaseChangeSections
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.CoheratorFlatFppf
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FlatBaseChangeCoherator
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LqcohSheafFbcPullback

/-!
# The coherator commutes with flat pullback (Stacks 0GQJ)

Let `f : 𝒳 ⟶ 𝒴` be a flat morphism of algebraic stacks and let `Q_𝒳`, `Q_𝒴` be the coherators of
**Stacks 0778**, the right adjoints `Q : LQCoh^fbc(𝒪) ⥤ QCoh(𝒪)` of the inclusions
`i : QCoh(𝒪) ⥤ LQCoh^fbc(𝒪)` (`AlgebraicGeometry.Stack.AlgebraicStacks.lqcohFbcCoherator`).
**Stacks 0GQJ** says `Q_𝒳 ∘ f^* = f^* ∘ Q_𝒴`.  The identification is the canonical one: `f^*`
preserves `QCoh` (**Stacks 06WH**) and `LQCoh^fbc` (**Stacks 0771** part (3)) compatibly with the
inclusions, and the mate of `i ∘ f^* = f^* ∘ i` under the two adjunctions is a natural map
`f^* ∘ Q_𝒴 ⟶ Q_𝒳 ∘ f^*`; at `𝓕` it corresponds to `f^*` of the adjunction map `Q_𝒴(𝓕) ⟶ 𝓕`.  The
statement is that this map is an isomorphism.

## The proof

The source shows that `f^*Q_𝒴(𝓕) ⟶ Q_𝒳(f^*𝓕)` has parasitic kernel and cokernel, using that the
adjunction map `Q_𝒴(𝓕) ⟶ 𝓕` has (**Stacks 0779**), that `f^*` keeps this for flat `f`
(**Stacks 0774**), and **Stacks 0776**.  Here the same argument is run on the flat-fppf site, where
"parasitic kernel and cokernel" reads "invertible after restriction to the flat objects":

* the restriction `g^{-1}` of `𝒪_𝒳`-modules to the flat-fppf site inverts the adjunction map
  `Q_𝒳(𝓖) ⟶ 𝓖` at every `𝓖` in `LQCoh^fbc(𝒪_𝒳)`
  (`isIso_modulePullback_map_ι_map_lqcohFbcCoheratorAdjunction_counit_app`);
* `f^*` of the adjunction map of `𝒴` is bijective on sections over every flat object `x` of `𝒳`,
  because those are its sections over `f x`, a flat object of `𝒴` as `f` is flat
  (`AlgebraicGeometry.Stack.FlatFppf.flatObject_map`);
* the counit square of the mate then shows that `g^{-1}` inverts the comparison map, and
  `g^{-1}` is fully faithful on `QCoh(𝒪_𝒳)`, so the comparison map is invertible.

## Main definitions

* `AlgebraicGeometry.Stack.AlgebraicStacks.lqcohFbcCoheratorPullbackComparison`: the canonical
  comparison `f^* ∘ Q_𝒴 ⟶ Q_𝒳 ∘ f^*`.
* `AlgebraicGeometry.Stack.AlgebraicStacks.lqcohFbcCoheratorPullbackIso`: the natural isomorphism
  it is, for flat `f`.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.isIso_lqcohFbcCoheratorPullbackComparison`:
  **Stacks 0GQJ**.

## References

* [Stacks Project, Tag 0GQJ](https://stacks.math.columbia.edu/tag/0GQJ)
* [Stacks Project, Tag 0771](https://stacks.math.columbia.edu/tag/0771)
* [Stacks Project, Tag 0774](https://stacks.math.columbia.edu/tag/0774)
* [Stacks Project, Tag 0776](https://stacks.math.columbia.edu/tag/0776)
* [Stacks Project, Tag 0778](https://stacks.math.columbia.edu/tag/0778)
* [Stacks Project, Tag 0779](https://stacks.math.columbia.edu/tag/0779)
* [Stacks Project, Tag 06WH](https://stacks.math.columbia.edu/tag/06WH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u w

namespace AlgebraicGeometry.Stack.AlgebraicStacks

attribute [local instance] FlatFppf.isContinuous_inclusion' FlatFppf.isCocontinuous_inclusion'

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)

/-- The inclusions `i : QCoh ⊆ LQCoh^fbc` of **Stacks 0778** commute with the inverse images
along a 1-morphism of algebraic stacks: both composites are the inverse image of modules,
restricted to the quasi-coherent ones. -/
def quasicoherentPullbackCompQuasicoherentToLqcohFbcIso
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) :
    quasicoherentPullback B S hS f ⋙ quasicoherentToLqcohFbc B E h S hS 𝒳 ≅
      quasicoherentToLqcohFbc B E h S hS 𝒴 ⋙ lqcohSheafFbcFppfModulesPullback B E h S hS f :=
  Iso.refl _

/-- The restriction to the flat-fppf site inverts the adjunction map `Q(𝓕) ⟶ 𝓕` of the coherator of
**Stacks 0778**, at every object `𝓕` of `LQCoh^fbc(𝒪_𝒳)`. -/
theorem isIso_modulePullback_map_ι_map_lqcohFbcCoheratorAdjunction_counit_app
    (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (A : (lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒳).FullSubcategory) :
    IsIso ((FlatFppf.modulePullback B S hS 𝒳).map
      ((lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒳).ι.map
        ((lqcohFbcCoheratorAdjunction B E h S hS 𝒳).counit.app A))) := by
  have hc := isIso_modulePullback_map_counit_app_of_isCartesianAlongFlatAffine B S hS 𝒳
    (coheratorAdjunction B S hS 𝒳) A.obj
    (isCartesianAlongFlatAffine_of_lqcohSheafFbcFppfModules B E h S hS A.obj A.property)
  have hform := Adjunction.map_restrictFullyFaithful_counit_app (coheratorAdjunction B S hS 𝒳)
    (Functor.FullyFaithful.id _) (lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒳).fullyFaithfulι
    (Functor.leftUnitor _ ≪≫ ((lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒳).liftCompιIso
      (quasicoherentInclusion B S hS 𝒳)
      (lqcohSheafFbcFppfModules_quasicoherentInclusion B E h S hS 𝒳)).symm)
    (Functor.rightUnitor _).symm A
  simp only [Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app, Functor.leftUnitor_inv_app,
    Functor.rightUnitor_hom_app] at hform
  rw [show (lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒳).ι.map
      ((lqcohFbcCoheratorAdjunction B E h S hS 𝒳).counit.app A) = _ from
    hform.trans (Category.id_comp _)]
  exact hc

variable {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)

/-- **The canonical comparison `f^* ∘ Q_𝒴 ⟶ Q_𝒳 ∘ f^*`** for a 1-morphism `f : 𝒳 ⟶ 𝒴` of
algebraic stacks, `Q` the coherators of **Stacks 0778**: the mate, under the adjunctions
`i ⊣ Q` of `𝒳` and of `𝒴`, of the identification `i ∘ f^* = f^* ∘ i` of the inverse images of
quasi-coherent modules and of modules in `LQCoh^fbc`.  At `𝓕` it is the map
`f^* Q_𝒴(𝓕) ⟶ Q_𝒳(f^*𝓕)` corresponding to `f^*` of the adjunction map `Q_𝒴(𝓕) ⟶ 𝓕`. -/
def lqcohFbcCoheratorPullbackComparison :
    lqcohFbcCoherator B E h S hS 𝒴 ⋙ quasicoherentPullback B S hS f ⟶
      lqcohSheafFbcFppfModulesPullback B E h S hS f ⋙ lqcohFbcCoherator B E h S hS 𝒳 :=
  mateEquiv (lqcohFbcCoheratorAdjunction B E h S hS 𝒴)
    (lqcohFbcCoheratorAdjunction B E h S hS 𝒳)
    (quasicoherentPullbackCompQuasicoherentToLqcohFbcIso B E h S hS f).hom

/-- The comparison map at `𝓕` followed by the counit at `f^*𝓕` is `f^*` of the counit at `𝓕`. -/
private theorem map_comparison_app_comp_counit
    (A : (lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒴).FullSubcategory) :
    (quasicoherentToLqcohFbc B E h S hS 𝒳).map
        ((lqcohFbcCoheratorPullbackComparison B E h S hS f).app A) ≫
      (lqcohFbcCoheratorAdjunction B E h S hS 𝒳).counit.app
        ((lqcohSheafFbcFppfModulesPullback B E h S hS f).obj A) =
    (lqcohSheafFbcFppfModulesPullback B E h S hS f).map
      ((lqcohFbcCoheratorAdjunction B E h S hS 𝒴).counit.app A) := by
  have hsq := mateEquiv_counit (lqcohFbcCoheratorAdjunction B E h S hS 𝒴)
    (lqcohFbcCoheratorAdjunction B E h S hS 𝒳)
    (quasicoherentPullbackCompQuasicoherentToLqcohFbcIso B E h S hS f).hom A
  simp only [quasicoherentPullbackCompQuasicoherentToLqcohFbcIso, Iso.refl_hom, NatTrans.id_app]
    at hsq
  exact hsq

/-- **Stacks 0GQJ.** Let `f : 𝒳 ⟶ 𝒴` be a flat morphism of algebraic stacks.  Then
`Q_𝒳 ∘ f^* = f^* ∘ Q_𝒴`, with `Q_𝒳` and `Q_𝒴` the coherators of **Stacks 0778**: the canonical
comparison `f^* Q_𝒴(𝓕) ⟶ Q_𝒳(f^*𝓕)` is an isomorphism for every `𝓕` in `LQCoh^fbc(𝒪_𝒴)`. -/
@[stacks 0GQJ "the canonical comparison f^* ∘ Q_𝒴 ⟶ Q_𝒳 ∘ f^*, the mate of i ∘ f^* = f^* ∘ i \
  under the adjunctions of Stacks 0778, is an isomorphism"]
theorem isIso_lqcohFbcCoheratorPullbackComparison (hf : AlgebraicStacks.IsFlat B S hS f) :
    IsIso (lqcohFbcCoheratorPullbackComparison B E h S hS f) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro A
  let r := FlatFppf.modulePullback B S hS 𝒳
  let ιX := (lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒳).ι
  have h₂ := isIso_modulePullback_map_ι_map_lqcohFbcCoheratorAdjunction_counit_app B E h S hS 𝒳
    ((lqcohSheafFbcFppfModulesPullback B E h S hS f).obj A)
  have h₄ : IsIso (r.map (ιX.map ((lqcohSheafFbcFppfModulesPullback B E h S hS f).map
      ((lqcohFbcCoheratorAdjunction B E h S hS 𝒴).counit.app A)))) := by
    refine FlatFppf.isIso_modulePullback_map_of_bijective B S hS 𝒳 _ (fun x hx => ?_)
    exact FlatFppf.bijective_app_of_isIso_modulePullback_map B S hS 𝒴 _
      (isIso_modulePullback_map_ι_map_lqcohFbcCoheratorAdjunction_counit_app B E h S hS 𝒴 A) _
      (FlatFppf.flatObject_map B S hS f hf ⟨x, hx⟩)
  have h₃ := @IsIso.of_isIso_fac_right _ _ _ _ _ _ _ _ h₂ h₄
    ((r.map_comp _ _).symm.trans (congrArg r.map ((ιX.map_comp _ _).symm.trans
      (congrArg ιX.map (map_comparison_app_comp_counit B E h S hS f A)))))
  exact @Functor.FullyFaithful.isIso_of_isIso_map _ _ _ _ _
    (fullyFaithfulQuasicoherentInclusionCompModulePullback B S hS 𝒳) _ _ _ h₃

/-- **Stacks 0GQJ**, as a natural isomorphism: for a flat morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks,
`f^* ∘ Q_𝒴 ≅ Q_𝒳 ∘ f^*` on `LQCoh^fbc(𝒪_𝒴)`, by the canonical comparison
`AlgebraicGeometry.Stack.AlgebraicStacks.lqcohFbcCoheratorPullbackComparison`. -/
def lqcohFbcCoheratorPullbackIso (hf : AlgebraicStacks.IsFlat B S hS f) :
    lqcohFbcCoherator B E h S hS 𝒴 ⋙ quasicoherentPullback B S hS f ≅
      lqcohSheafFbcFppfModulesPullback B E h S hS f ⋙ lqcohFbcCoherator B E h S hS 𝒳 :=
  haveI := isIso_lqcohFbcCoheratorPullbackComparison B E h S hS f hf
  asIso (lqcohFbcCoheratorPullbackComparison B E h S hS f)

/-- The forward map of `AlgebraicGeometry.Stack.AlgebraicStacks.lqcohFbcCoheratorPullbackIso` is
the canonical comparison. -/
@[simp]
theorem lqcohFbcCoheratorPullbackIso_hom (hf : AlgebraicStacks.IsFlat B S hS f) :
    (lqcohFbcCoheratorPullbackIso B E h S hS f hf).hom =
      lqcohFbcCoheratorPullbackComparison B E h S hS f :=
  rfl

/-- The comparison map at `𝓕`, followed by the adjunction map of `𝒳` at `f^*𝓕`, is `f^*` of the
adjunction map of `𝒴` at `𝓕`: this characterizes the comparison map of **Stacks 0GQJ**. -/
theorem quasicoherentToLqcohFbc_map_lqcohFbcCoheratorPullbackComparison_app_comp_counit
    (A : (lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒴).FullSubcategory) :
    (quasicoherentToLqcohFbc B E h S hS 𝒳).map
        ((lqcohFbcCoheratorPullbackComparison B E h S hS f).app A) ≫
      (lqcohFbcCoheratorAdjunction B E h S hS 𝒳).counit.app
        ((lqcohSheafFbcFppfModulesPullback B E h S hS f).obj A) =
    (lqcohSheafFbcFppfModulesPullback B E h S hS f).map
      ((lqcohFbcCoheratorAdjunction B E h S hS 𝒴).counit.app A) :=
  map_comparison_app_comp_counit B E h S hS f A
end AlgebraicGeometry.Stack.AlgebraicStacks

end
