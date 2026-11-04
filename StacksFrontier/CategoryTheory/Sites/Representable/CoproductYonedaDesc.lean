module

public import Mathlib.CategoryTheory.Sites.LocallySurjective

/-! # Coverings become surjective after sheafification

## Main results

* `coprodYonedaDesc`: the canonical morphism `∐_i h_{U_i} ⟶ h_U` of presheaves induced by a
  family of morphisms `U_i ⟶ U`.
* `isLocallySurjective_coprodYonedaDesc`: if `{U_i ⟶ U}` is a covering of the site, then this
  morphism is locally
  surjective, i.e. becomes an epimorphism after sheafification (Stacks 00WT).

Tags covered: 00WT.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

/-- The canonical morphism `∐_{i ∈ I} h_{U i} ⟶ h_X` of presheaves of sets induced by a family
of morphisms `f_i : U i ⟶ X`, where `h_(-) := yoneda.obj`. -/
noncomputable def coprodYonedaDesc
    {C : Type u} [Category.{v} C]
    {I : Type v} (U : I → C) (X : C) (f : ∀ i, U i ⟶ X) :
    (∐ fun i => yoneda.obj (U i)) ⟶ yoneda.obj X :=
  Sigma.desc fun i => yoneda.map (f i)

/-- **Stacks 00WT.** Let `(C, J)` be a site. If `{f_i : U_i ⟶ U}_{i ∈ I}` is a covering of `U`,
then the canonical map `∐_i h_{U_i} ⟶ h_U` of presheaves of sets is locally surjective for
`J`; equivalently, it becomes an epimorphism after sheafification. -/
@[stacks 00WT]
theorem isLocallySurjective_coprodYonedaDesc
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    {I : Type v} (U : I → C) (X : C) (f : ∀ i, U i ⟶ X)
    (hf : Sieve.generate (Presieve.ofArrows U f) ∈ J X) :
    Presheaf.IsLocallySurjective J (coprodYonedaDesc U X f) := by
  refine ⟨?_⟩
  intro V s
  refine J.superset_covering ?_ (J.pullback_stable s hf)
  rintro W g ⟨Y, h, k, ⟨i⟩, hcomp⟩
  refine ⟨(Sigma.ι (fun i => yoneda.obj (U i)) i).app (op W) h, ?_⟩
  rw [← ConcreteCategory.comp_apply, ← NatTrans.comp_app, coprodYonedaDesc, Sigma.ι_desc]
  exact hcomp
