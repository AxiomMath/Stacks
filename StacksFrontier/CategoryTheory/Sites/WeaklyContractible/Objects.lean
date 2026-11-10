module

public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Order.CompletePartialOrder
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Weakly contractible objects of a site

For an object `U` of a site `(C, J)`, every covering `{U_i → U}` of `U` admits a right inverse
to its sheafified covering map `π^# : ∐ h_{U_i}^# ⟶ h_U^#` if and only if every locally
surjective morphism `φ : F ⟶ G` of sheaves of sets is surjective on sections over `U`.

## Main definitions

* `Stacks.WeaklyContractible.piSharp`: the sheafified covering map `π^#`.
* `Stacks.WeaklyContractible.HasRightInverse`: the map `π^#` has a right inverse.
* `Stacks.WeaklyContractible.sheafSectionEquiv`: the bijection `Hom_{Sh}(h_V^#, G) ≃ G(V)`.

## Main results

* `hasRightInverse_iff_isLocallySurjective_surjective`: the equivalence above.
-/

@[expose] public section

open CategoryTheory Limits Opposite

universe v u

variable {C : Type u} [Category.{v} C] [Small.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J (Type v)]

/-- The sheafification `h_V^#` of the representable presheaf `h_V = yoneda.obj V`. -/
@[sga "4 VIII 7.9.1" "partial"]
noncomputable abbrev Stacks.WeaklyContractible.reprSheaf (V : C) : Sheaf J (Type v) :=
  (presheafToSheaf J (Type v)).obj (yoneda.obj V)

variable {I : Type v} {U : C} (Ui : I → C) (f : ∀ i, Ui i ⟶ U)

/-- The sheaf `∐ h_{U_i}^#` of a family `{U_i}_{i ∈ I}`, the sheafification of the presheaf
coproduct `∐ h_{U_i}`. -/
noncomputable abbrev Stacks.WeaklyContractible.coprodReprSheaf : Sheaf J (Type v) :=
  (presheafToSheaf J (Type v)).obj (∐ fun i => yoneda.obj (Ui i))

/-- The presheaf morphism `π : ∐ h_{U_i} ⟶ h_U` whose `i`-th component is
`yoneda.map (f i)`. -/
noncomputable def Stacks.WeaklyContractible.piPre : (∐ fun i => yoneda.obj (Ui i)) ⟶ yoneda.obj U :=
  Sigma.desc fun i => yoneda.map (f i)

/-- The sheafified covering map `π^# : ∐ h_{U_i}^# ⟶ h_U^#`. -/
noncomputable def Stacks.WeaklyContractible.piSharp :
    Stacks.WeaklyContractible.coprodReprSheaf J Ui ⟶ Stacks.WeaklyContractible.reprSheaf J U :=
  (presheafToSheaf J (Type v)).map (Stacks.WeaklyContractible.piPre Ui f)

/-- The sheafified covering map `π^#` of `{U_i → U}` has a right inverse: there is `σ` with
`σ ≫ π^# = 𝟙`. -/
def Stacks.WeaklyContractible.HasRightInverse : Prop :=
  ∃ σ : Stacks.WeaklyContractible.reprSheaf J U ⟶ Stacks.WeaklyContractible.coprodReprSheaf J Ui,
    σ ≫ Stacks.WeaklyContractible.piSharp J Ui f = 𝟙 _

namespace Stacks.WeaklyContractible

/-- The bijection `Hom_{Sh}(h_V^#, G) ≃ G(V)`, the sheafification adjunction
`Hom_{Sh}(h_V^#, G) ≃ Hom_{PSh}(h_V, G)` followed by the Yoneda bijection. -/
noncomputable def sheafSectionEquiv (V : C) (G : Sheaf J (Type v)) :
    (reprSheaf J V ⟶ G) ≃ ((sheafToPresheaf J (Type v)).obj G).obj (op V) :=
  ((sheafificationAdjunction J (Type v)).homEquiv (yoneda.obj V) G).trans yonedaEquiv

omit [Small.{v, u} C] in
/-- Naturality of `sheafSectionEquiv` in `G`: postcomposing a map `g : h_V^# ⟶ F` with
`φ : F ⟶ G` and then taking the corresponding section equals applying `φ` on sections to
the section corresponding to `g`. -/
lemma sheafSectionEquiv_naturality (V : C) {F G : Sheaf J (Type v)} (φ : F ⟶ G)
    (g : reprSheaf J V ⟶ F) :
    sheafSectionEquiv J V G (g ≫ φ) =
      φ.hom.app (op V) (sheafSectionEquiv J V F g) := by
  simp only [sheafSectionEquiv, Equiv.trans_apply]
  exact (congrArg yonedaEquiv
    (Adjunction.homEquiv_naturality_right (sheafificationAdjunction J (Type v)) g φ)).trans
    (yonedaEquiv_comp _ _)

omit [Small.{v, u} C] in
/-- The sheafification `α^#` of a locally surjective presheaf map `α : P ⟶ Q` is locally
surjective. -/
lemma isLocallySurjective_presheafToSheaf_map {P Q : Cᵒᵖ ⥤ Type v} (α : P ⟶ Q)
    [Presheaf.IsLocallySurjective J α] :
    Sheaf.IsLocallySurjective ((presheafToSheaf J (Type v)).map α) := by
  have hsurj : ∀ R : Cᵒᵖ ⥤ Type v, Presheaf.IsLocallySurjective J (toSheafify J R) := by
    intro R
    rw [Presheaf.isLocallySurjective_iff_range_sheafify_eq_top']
    set G := Subfunctor.sheafify J (Subfunctor.range (toSheafify J R)) with hG
    have hFsheaf : Presheaf.IsSheaf J (sheafify J R) :=
      ((presheafToSheaf J (Type v)).obj R).property
    have hGsheaf : Presheaf.IsSheaf J G.toFunctor :=
      (isSheaf_iff_isSheaf_of_type J _).mpr
        ((Subfunctor.range (toSheafify J R)).sheafify_isSheaf
          ((isSheaf_iff_isSheaf_of_type J _).mp hFsheaf))
    have hfac : Subfunctor.toRangeSheafify J (toSheafify J R) ≫ G.ι = toSheafify J R :=
      hom_ext_yoneda fun X => congrFun rfl
    rw [Subfunctor.eq_top_iff_isIso]
    have hsplit : IsSplitEpi G.ι := by
      refine IsSplitEpi.mk
        ⟨⟨sheafifyLift J (Subfunctor.toRangeSheafify J (toSheafify J R)) hGsheaf, ?_⟩⟩
      refine sheafify_hom_ext J _ _ hFsheaf ?_
      rw [Category.comp_id, ← Category.assoc, toSheafify_sheafifyLift, hfac]
    exact isIso_of_mono_of_isSplitEpi G.ι
  have : Presheaf.IsLocallySurjective J (toSheafify J P) := hsurj P
  have : Presheaf.IsLocallySurjective J (toSheafify J Q) := hsurj Q
  have : Presheaf.IsLocallySurjective J (α ≫ toSheafify J Q) := inferInstance
  exact Presheaf.isLocallySurjective_of_isLocallySurjective_fac J
    (f₁ := toSheafify J P) (f₂ := ((presheafToSheaf J (Type v)).map α).hom)
    (f₃ := α ≫ toSheafify J Q) (toSheafify_naturality J α).symm

omit [Small.{v, u} C] [HasSheafify J (Type v)] in
/-- If the sieve generated by a family `{Ui → U}` is a covering sieve, then the presheaf
map `π = piPre : ∐ h_{U_i} ⟶ h_U` is locally surjective. -/
lemma piPre_isLocallySurjective (hf : (Sieve.ofArrows Ui f) ∈ J U) :
    Presheaf.IsLocallySurjective J (Stacks.WeaklyContractible.piPre Ui f) := by
  constructor
  intro W g
  apply J.superset_covering (S := Sieve.pullback g (Sieve.ofArrows Ui f))
  · rintro V a ha
    rw [Sieve.pullback_apply, Sieve.mem_ofArrows_iff] at ha
    obtain ⟨i, b, hb⟩ := ha
    refine ⟨(Sigma.ι (fun i => yoneda.obj (Ui i)) i).app (op V) b, ?_⟩
    have hcomp : (Sigma.ι (fun i => yoneda.obj (Ui i)) i) ≫ Stacks.WeaklyContractible.piPre Ui f =
        yoneda.map (f i) :=
      Sigma.ι_comp_desc _ i
    rw [← NatTrans.comp_app_apply, hcomp]
    simp only [yoneda_map_app, yoneda_obj_map, Quiver.Hom.unop_op]
    exact hb.symm
  · exact J.pullback_stable g hf

omit [Small.{v, u} C] in
/-- The sheafified covering map `π^# = piSharp` of a covering `{Ui → U}` is a locally
surjective map of sheaves. -/
lemma piSharp_isLocallySurjective (hf : (Sieve.ofArrows Ui f) ∈ J U) :
    Sheaf.IsLocallySurjective (Stacks.WeaklyContractible.piSharp J Ui f) := by
  have := piPre_isLocallySurjective J Ui f hf
  exact isLocallySurjective_presheafToSheaf_map J (piPre Ui f)

/-- The total space `Σ V, {a : V ⟶ U // S a}` of arrows in a sieve `S` of `U` is
`Type v`-small. -/
lemma smallArrowSigma {U : C} (S : Sieve U) :
    Small.{v} (Σ (V : C), {a : V ⟶ U // S.arrows a}) := by
  infer_instance

omit [HasSheafify J (Type v)] in
/-- Every covering sieve `S` of `U` contains a covering sieve generated by a family
`{U_i → U}` indexed by a type `I : Type v`. -/
lemma exists_small_subcover {U : C} (S : Sieve U) (hS : S ∈ J U) :
    ∃ (I : Type v) (Ui : I → C) (f : ∀ i, Ui i ⟶ U),
      (Sieve.ofArrows Ui f) ∈ J U ∧ (Sieve.ofArrows Ui f) ≤ S := by
  classical
  have : Small.{v} (Σ (V : C), {a : V ⟶ U // S.arrows a}) := smallArrowSigma S
  set Ω := Σ (V : C), {a : V ⟶ U // S.arrows a} with hΩ
  have hmem : ∀ i : Shrink.{v} Ω, S.arrows ((equivShrink Ω).symm i).2.val :=
    fun i => ((equivShrink Ω).symm i).2.property
  have hle : Sieve.ofArrows (fun i => ((equivShrink Ω).symm i).1)
      (fun i => ((equivShrink Ω).symm i).2.val) ≤ S := by
    intro W g
    rw [Sieve.mem_ofArrows_iff]; rintro ⟨i, a, rfl⟩
    exact S.downward_closed (hmem i) a
  refine ⟨Shrink.{v} Ω, fun i => ((equivShrink Ω).symm i).1,
    fun i => ((equivShrink Ω).symm i).2.val, ?_, hle⟩
  refine J.superset_covering (fun W g hg => ?_) hS
  have hmk := Sieve.ofArrows_mk (fun i => ((equivShrink Ω).symm i).1)
    (fun i => ((equivShrink Ω).symm i).2.val) (equivShrink Ω ⟨W, ⟨g, hg⟩⟩)
  rwa [Equiv.symm_apply_apply] at hmk

/-- If every covering of `U` admits a right inverse to its sheafified covering map `π^#`, then
every locally surjective `φ : F ⟶ G` is surjective on sections over `U`. -/
theorem surjective_sections_of_hasRightInverse
    (h1 : ∀ (I : Type v) (Ui : I → C) (f : ∀ i, Ui i ⟶ U),
        (Sieve.ofArrows Ui f) ∈ J U → Stacks.WeaklyContractible.HasRightInverse J Ui f) :
    ∀ (F G : Sheaf J (Type v)) (φ : F ⟶ G), Sheaf.IsLocallySurjective φ →
        Function.Surjective ((sheafToPresheaf J (Type v)).map φ |>.app (op U)) := by
  intro F G φ hφ s
  set ŝ : reprSheaf J U ⟶ G := (sheafSectionEquiv J U G).symm s with hŝ
  have hImg : Presheaf.imageSieve φ.hom s ∈ J U := hφ.imageSieve_mem s
  obtain ⟨I', Ui', f', hcov, hle⟩ := exists_small_subcover J (Presheaf.imageSieve φ.hom s) hImg
  have hmem : ∀ i, Presheaf.imageSieve φ.hom s (f' i) := fun i =>
    hle _ (Sieve.ofArrows_mk Ui' f' i)
  obtain ⟨τ, hτ⟩ : ∃ τ : coprodReprSheaf J Ui' ⟶ F, τ ≫ φ = piSharp J Ui' f' ≫ ŝ := by
    set adj := sheafificationAdjunction J (Type v) with hadj
    set t : ∀ i, ((sheafToPresheaf J (Type v)).obj F).obj (op (Ui' i)) :=
      fun i => Presheaf.localPreimage φ.hom s (f' i) (hmem i) with ht
    set α : (∐ fun i => yoneda.obj (Ui' i)) ⟶ (sheafToPresheaf J (Type v)).obj F :=
      Sigma.desc (fun i => yonedaEquiv.symm (t i)) with hα
    refine ⟨(adj.homEquiv _ F).symm α, ?_⟩
    apply (adj.homEquiv (∐ fun i => yoneda.obj (Ui' i)) G).injective
    rw [Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply, hŝ, piSharp,
      show (sheafSectionEquiv J U G).symm s
        = (adj.homEquiv (yoneda.obj U) G).symm (yonedaEquiv.symm s) from rfl,
      Adjunction.homEquiv_naturality_left, Equiv.apply_symm_apply]
    apply Limits.Sigma.hom_ext
    intro i
    rw [hα, ← Category.assoc, Sigma.ι_comp_desc, piPre, ← Category.assoc, Sigma.ι_comp_desc]
    apply yonedaEquiv.injective
    rw [yonedaEquiv_comp, yonedaEquiv_comp, Equiv.apply_symm_apply, yonedaEquiv_yoneda_map]
    exact Presheaf.app_localPreimage φ.hom s (f' i) (hmem i)
  obtain ⟨σ, hσ⟩ := h1 I' Ui' f' hcov
  refine ⟨sheafSectionEquiv J U F (σ ≫ τ), ?_⟩
  rw [show (ConcreteCategory.hom (((sheafToPresheaf J (Type v)).map φ).app (op U)))
        ((sheafSectionEquiv J U F) (σ ≫ τ))
      = φ.hom.app (op U) (sheafSectionEquiv J U F (σ ≫ τ)) from rfl,
    ← sheafSectionEquiv_naturality, Category.assoc, hτ, ← Category.assoc, hσ,
    Category.id_comp]
  exact (sheafSectionEquiv J U G).apply_symm_apply s

omit [Small.{v, u} C] in
/-- If every locally surjective map of sheaves is surjective on sections over `U`, then every
covering `{U_i → U}` admits a right inverse to its sheafified covering map `π^#`. -/
theorem hasRightInverse_of_surjective_sections
    (h2 : ∀ (F G : Sheaf J (Type v)) (φ : F ⟶ G), Sheaf.IsLocallySurjective φ →
        Function.Surjective ((sheafToPresheaf J (Type v)).map φ |>.app (op U))) :
    ∀ (I : Type v) (Ui : I → C) (f : ∀ i, Ui i ⟶ U),
        (Sieve.ofArrows Ui f) ∈ J U → Stacks.WeaklyContractible.HasRightInverse J Ui f := by
  intro I Ui f hf
  have hls : Sheaf.IsLocallySurjective (piSharp J Ui f) := piSharp_isLocallySurjective J Ui f hf
  set idU := sheafSectionEquiv J U (reprSheaf J U) (𝟙 (reprSheaf J U)) with hidU
  obtain ⟨s, hs⟩ := h2 (coprodReprSheaf J Ui) (reprSheaf J U) (piSharp J Ui f) hls idU
  refine ⟨(sheafSectionEquiv J U (coprodReprSheaf J Ui)).symm s, ?_⟩
  apply (sheafSectionEquiv J U (reprSheaf J U)).injective
  rwa [sheafSectionEquiv_naturality, Equiv.apply_symm_apply]

end Stacks.WeaklyContractible

/-- Let `C` be a site with Grothendieck topology `J`, and let `U`
be an object of `C`. The following are equivalent.

1. For every covering `{U_i → U}_{i ∈ I}` of `U`, the sheafified covering map
   `π^# : ∐ h_{U_i}^# ⟶ h_U^#` admits a right inverse (a section) `σ`, i.e.
   `σ ≫ π^# = 𝟙`.

2. For every surjection (locally surjective morphism) of sheaves of sets `φ : F ⟶ G`,
   the induced map on sections over `U`, `φ_U : F(U) → G(U)`, is surjective. -/
@[stacks 090K]
theorem hasRightInverse_iff_isLocallySurjective_surjective :
    (∀ (I : Type v) (Ui : I → C) (f : ∀ i, Ui i ⟶ U),
        (Sieve.ofArrows Ui f) ∈ J U → Stacks.WeaklyContractible.HasRightInverse J Ui f) ↔
    (∀ (F G : Sheaf J (Type v)) (φ : F ⟶ G), Sheaf.IsLocallySurjective φ →
        Function.Surjective ((sheafToPresheaf J (Type v)).map φ |>.app (op U))) :=
  ⟨Stacks.WeaklyContractible.surjective_sections_of_hasRightInverse J,
    Stacks.WeaklyContractible.hasRightInverse_of_surjective_sections J⟩
