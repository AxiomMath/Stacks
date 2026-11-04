module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkFreeCover
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.LocallyFreeSite

/-!
# Finite local freeness as section-level trivialisation data

A sheaf of modules `M` over a sheaf of rings `R` on a space is finite locally free, in the sense
of Stacks Tag 01C6, when it has local generators data which is both a local free basis and finite
in number. This file shows that this is equivalent to section-level trivialisation data: a cover
`U i` of the space and, over each `U i`, finitely many sections of `M`, indexed by `ULift (Fin m)`,
such that taking `R(V)`-linear combinations of them is a bijection onto `M(V)` for every open
`V ≤ U i`.

## Main definitions

* `Stacks.SheafOfModules.combSections`: the `R(V)`-linear combination of a finite family of
  sections of `M` over `U`, restricted to an open `V ≤ U`.

## Main results

* `Stacks.SheafOfModules.exists_localTrivialisation`: **a finite locally free sheaf of modules
  has section-level trivialisation data**: a cover, and over each member finitely many sections
  whose combinations give every section over every smaller open, uniquely.
* `Stacks.SheafOfModules.isFiniteLocallyFree_of_combSections_bijective`: **the converse**:
  section-level trivialisation data makes a sheaf of modules finite locally free.
* `Stacks.SheafOfModules.bijective_val_app_of_isIso`: an invertible morphism of sheaves of
  modules is bijective on sections over every object.

## References

* [Stacks Project, Tag 01C6](https://stacks.math.columbia.edu/tag/01C6)
-/

@[expose] public section

open CategoryTheory Limits Opposite TopologicalSpace SheafOfModules

universe u v u'

namespace Stacks.SheafOfModules

/-! ### Linear combinations of a finite family of sections -/

section Comb

variable {C : Type u'} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}

/-- The `R(V)`-linear combination, with coefficients `c`, of a finite family `s` of sections of
`M` over `U`, restricted along a morphism `f : V ⟶ U` of the site. -/
noncomputable def combSections (M : SheafOfModules.{u} R) {U : C} {ι : Type u} [Fintype ι]
    (s : ι → ToType (M.val.obj (op U))) {V : C} (f : V ⟶ U)
    (c : ι → ToType (R.obj.obj (op V))) : ToType (M.val.obj (op V)) :=
  ∑ i : ι, c i • res M f (s i)

variable (M : SheafOfModules.{u} R) {U : C} {ι : Type u} [Fintype ι]
  (s : ι → ToType (M.val.obj (op U)))

/-- Restricting a combination restricts its coefficients. -/
lemma res_combSections {V W : C} (f : V ⟶ U) (g : W ⟶ V)
    (c : ι → ToType (R.obj.obj (op V))) :
    res M g (combSections M s f c) = combSections M s (g ≫ f) fun i => resR R g (c i) := by
  rw [combSections, combSections, res_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [res_smul, res_res]

/-- Combinations are additive in the coefficients. -/
lemma combSections_add {V : C} (f : V ⟶ U) (c d : ι → ToType (R.obj.obj (op V))) :
    combSections M s f (fun i => c i + d i) = combSections M s f c + combSections M s f d := by
  rw [combSections, combSections, combSections, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => add_smul _ _ _

/-- Combinations are homogeneous in the coefficients. -/
lemma combSections_smul {V : C} (f : V ⟶ U) (a : ToType (R.obj.obj (op V)))
    (c : ι → ToType (R.obj.obj (op V))) :
    combSections M s f (fun i => a * c i) = a • combSections M s f c := by
  rw [combSections, combSections, Finset.smul_sum]
  exact Finset.sum_congr rfl fun i _ => mul_smul _ _ _

/-- A finite sum of combinations is the combination of the summed coefficients. -/
lemma combSections_sum {V : C} (f : V ⟶ U) {κ : Type*} (t : Finset κ)
    (c : κ → ι → ToType (R.obj.obj (op V))) :
    ∑ j ∈ t, combSections M s f (c j) = combSections M s f fun i => ∑ j ∈ t, c j i := by
  simp only [combSections]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => by rw [Finset.sum_smul]

/-- Bijectivity of a combination map is unchanged by reindexing the family. -/
lemma bijective_combSections_reindex {κ : Type u} [Fintype κ] (ee : κ ≃ ι) {V : C} (f : V ⟶ U)
    (h : Function.Bijective (combSections M s f)) :
    Function.Bijective (combSections M (fun a => s (ee a)) f) := by
  have hre : Function.Bijective
      fun (c : κ → ToType (R.obj.obj (op V))) (i : ι) => c (ee.symm i) := by
    refine ⟨fun c d hcd => funext fun b => ?_, fun g => ⟨fun b => g (ee b), funext fun i => ?_⟩⟩
    · have hb : c (ee.symm (ee b)) = d (ee.symm (ee b)) := congrFun hcd (ee b)
      rwa [ee.symm_apply_apply] at hb
    · exact congrArg g (ee.apply_symm_apply i)
  have hfun : (fun c : κ → ToType (R.obj.obj (op V)) =>
      combSections M s f fun i => c (ee.symm i)) = combSections M (fun a => s (ee a)) f := by
    funext c
    refine Eq.trans (Equiv.sum_comp ee
      (fun i : ι => c (ee.symm i) • res M f (s i))).symm ?_
    exact Finset.sum_congr rfl fun a _ => by rw [ee.symm_apply_apply]
  exact hfun ▸ h.comp hre

end Comb

/-! ### Bijectivity on sections of an invertible morphism -/

section Bijective

variable {C : Type u'} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}

/-- **An invertible morphism of sheaves of modules is bijective on sections** over every object
of the site. -/
lemma bijective_val_app_of_isIso {M N : SheafOfModules.{u} R} (f : M ⟶ N) [IsIso f] (V : Cᵒᵖ) :
    Function.Bijective fun x : ToType (M.val.obj V) => f.val.app V x := by
  refine Function.bijective_iff_has_inverse.2
    ⟨fun y => (inv f).val.app V y, fun x => ?_, fun y => ?_⟩
  · exact congrArg (fun g : M ⟶ M => g.val.app V x) (IsIso.hom_inv_id f)
  · exact congrArg (fun g : N ⟶ N => g.val.app V y) (IsIso.inv_hom_id f)

end Bijective

/-! ### The two forms of finite local freeness -/

section Opens

variable {X : TopCat.{u}} {R : Sheaf (Opens.grothendieckTopology (X : Type u)) RingCat.{u}}

/-- Combinations of a family of sections are the values of the morphism out of the free sheaf of
modules on the slice site which that family determines. -/
lemma combSections_eq_freeToOver_app (M : SheafOfModules.{u} R) {U : Opens X} {ι : Type u}
    [Fintype ι] (s : ι → ToType (M.val.obj (op U))) {V : Opens X} (f : V ⟶ U)
    (c : ι → ToType (R.obj.obj (op V))) :
    combSections M s f c = (freeToOver M s).val.app (op (Over.mk f)) (ofCoords f c) :=
  (freeToOver_app_ofCoords M s f c).symm

/-- **The combinations of a generating family which is a local basis are bijective.** -/
lemma bijective_combSections_generators (M : SheafOfModules.{u} R) {U : Opens X}
    (σ : (M.over U).GeneratingSections) [Fintype σ.I] (hσ : IsIso σ.π) ⦃V : Opens X⦄
    (f : V ⟶ U) :
    Function.Bijective
      (combSections M (fun a => (σ.s a).eval (op (Over.mk (𝟙 U)))) f) := by
  classical
  have := hσ
  have hof : Function.Bijective (ofCoords (R := R) (ι := σ.I) f) :=
    Function.bijective_iff_has_inverse.2
      ⟨coords f, fun c => coords_ofCoords f c, fun e => ofCoords_coords f e⟩
  have hπ := (bijective_val_app_of_isIso σ.π (op (Over.mk f))).comp hof
  have h1 : σ.π = freeToOver M (fun a => (σ.s a).eval (op (Over.mk (𝟙 U)))) :=
    freeHomEquiv_symm_eq_freeToOver M σ.s
  have hfun : (fun c : σ.I → ToType (R.obj.obj (op V)) =>
        σ.π.val.app (op (Over.mk f)) (ofCoords f c))
      = combSections M (fun a => (σ.s a).eval (op (Over.mk (𝟙 U)))) f := by
    funext c
    rw [h1]
    exact freeToOver_app_ofCoords M _ f c
  exact hfun ▸ hπ

/-- **A finite locally free sheaf of modules has section-level trivialisation data.** There is a
cover of the space and, over each member, finitely many sections of the sheaf such that taking
linear combinations of them is a bijection onto the sections over every smaller open. -/
theorem exists_localTrivialisation (M : SheafOfModules.{u} R)
    (h : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} M) :
    ∃ (I : Type u) (U : I → Opens X) (m : I → ℕ)
      (s : ∀ i, ULift.{u} (Fin (m i)) → ToType (M.val.obj (op (U i)))),
      ⨆ i, U i = ⊤ ∧ ∀ (i : I) ⦃V : Opens X⦄ (f : V ⟶ U i),
        Function.Bijective (combSections M (s i) f) := by
  obtain ⟨q, hfree, hfin⟩ := h.exists_isFiniteLocallyFreeData
  have hfinite : ∀ i, Finite (q.generators i).I := fun i => (hfin.isFiniteType i).finite
  let : ∀ i, Fintype (q.generators i).I := fun i => Fintype.ofFinite _
  refine ⟨q.I, q.X, fun i => Nat.card (q.generators i).I,
    fun i a => (q.generators i).s
      ((Equiv.ulift.trans (Finite.equivFin (q.generators i).I).symm) a) |>.eval
        (op (Over.mk (𝟙 (q.X i)))), (Opens.coversTop_iff _ _).mp q.coversTop, fun i V f => ?_⟩
  exact bijective_combSections_reindex M _
    (Equiv.ulift.trans (Finite.equivFin (q.generators i).I).symm) f
    (bijective_combSections_generators M (q.generators i) (hfree.isIso i) f)

/-- **Section-level trivialisation data makes a sheaf of modules finite locally free.** -/
theorem isFiniteLocallyFree_of_combSections_bijective (M : SheafOfModules.{u} R)
    {I : Type u} (U : I → Opens X) (hU : ⨆ i, U i = ⊤) (m : I → ℕ)
    (s : ∀ i, ULift.{u} (Fin (m i)) → ToType (M.val.obj (op (U i))))
    (hbij : ∀ (i : I) ⦃V : Opens X⦄ (f : V ⟶ U i),
      Function.Bijective (combSections M (s i) f)) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} M := by
  have key : ∀ i, Nonempty (_root_.SheafOfModules.free.{u} (ULift.{u} (Fin (m i)))
      ≅ M.over (U i)) := by
    intro i
    refine ⟨(nonempty_over_iso_free_of_inj_of_surj M (s i) (fun V f => (hbij i f).1)
      (fun V f t y hy => ?_)).some.symm⟩
    obtain ⟨c, hc⟩ := (hbij i f).2 t
    refine ⟨V, 𝟙 V, hy, c, ?_⟩
    rw [res_id, Category.id_comp]
    exact hc.symm
  exact Stacks.Modules.isFiniteLocallyFree_of_free_iso_family.{u, u, u}
    (fun i => inferInstance) U ((Opens.coversTop_iff _ U).mpr hU) fun i => (key i).some

end Opens

end Stacks.SheafOfModules

end
