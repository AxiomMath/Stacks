module

public import StacksFrontier.AlgebraicGeometry.Spaces.AtlasMorphismDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeMorphismSheaf

/-!
# Gluing morphisms of algebraic spaces over a scheme along a covering of the scheme

Let `z : Z ⟶ T₀` and `x : X ⟶ T₀` be morphisms of algebraic spaces to a scheme `T₀` of the big fppf
site, and let `{vᵢ : Vᵢ ⟶ T₀}` be a covering family. Morphisms `Z ×_{T₀} Vᵢ ⟶ X` over `T₀` which
agree on overlaps glue to a unique morphism `Z ⟶ X` over `T₀`. This is the sheaf property of the
relative morphism functor `Mor_{T₀}(Z, X)` of Stacks 05Y3, part (1), read at `T₀` itself.

## Main results

* `AlgebraicGeometry.C1590Private.exists_hom_of_local`: compatible local morphisms glue.
* `AlgebraicGeometry.C1590Private.hom_ext_of_local`: morphisms over `T₀` agreeing locally are
  equal.

## References

* [Stacks Project, Tag 05Y3](https://stacks.math.columbia.edu/tag/05Y3)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.C1590Private

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- Equal pairs of Stacks 05Y1 have equal second components, read through any lift into the two
fibre products. -/
theorem RelativeMorphism.lift_morphism_eq {Z X Q T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {z : Z ⟶ Q} {x : X ⟶ Q} {r r' : Space.RelativeMorphism B S hS Z X Q z x T} (h : r = r')
    {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (w : P ⟶ T) (k : P ⟶ Z) (hk : w ≫ r.base = k ≫ z) :
    pullback.lift w k hk ≫ r.morphism = pullback.lift w k (h ▸ hk) ≫ r'.morphism := by
  subst h
  rfl

/-- The map between fibre products induced by `f : A ⟶ B` over `g : B ⟶ Y` is the lift of
`fst ≫ f` and `snd`. -/
private theorem pullback_map_comp_id_eq_lift {C : Type*} [Category C] [HasPullbacks C]
    {A B Y Z : C} (f : A ⟶ B) (g : B ⟶ Y) (z : Z ⟶ Y) :
    pullback.map (f ≫ g) z g z f (𝟙 Z) (𝟙 Y) (by simp) (by simp) =
      pullback.lift (pullback.fst _ _ ≫ f) (pullback.snd _ _)
        (by rw [Category.assoc, pullback.condition]) := by
  apply pullback.hom_ext
  · simp only [pullback.lift_fst]
  · simp only [Category.comp_id, pullback.lift_snd]

variable {Z X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {T₀ : BigFppfOver B S hS}

/-- **Morphisms over a scheme agreeing locally on a covering of it are equal.** Two morphisms
`m, m' : Z ⟶ X` to a sheaf whose restrictions to `Vᵢ ×_{T₀} Z` agree for a covering family
`{vᵢ : Vᵢ ⟶ T₀}` are equal. -/
theorem hom_ext_of_local (hX : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X)
    (z : Z ⟶ yoneda.obj T₀) {I : Type*}
    (V : I → BigFppfOver B S hS) (v : ∀ i, V i ⟶ T₀)
    (hv : Sieve.ofArrows V v ∈ BigFppfOver.topology B S hS T₀) {m m' : Z ⟶ X}
    (h : ∀ i, pullback.snd (yoneda.map (v i)) z ≫ m = pullback.snd (yoneda.map (v i)) z ≫ m') :
    m = m' := by
  have hXt := (isSheaf_iff_isSheaf_of_type (BigFppfOver.topology B S hS) X).mp hX
  ext T y
  refine (hXt _ ((BigFppfOver.topology B S hS).pullback_stable (z.app T y) hv)).isSeparatedFor.ext
    fun T' g hg => ?_
  obtain ⟨W, k, _, ⟨i⟩, hk⟩ := hg
  change X.map g.op (m.app T y) = X.map g.op (m'.app T y)
  rw [← NatTrans.naturality_apply, ← NatTrans.naturality_apply]
  let y' := Z.map g.op y
  have hzy' : yoneda.map k ≫ yoneda.map (v i) = yonedaEquiv.symm y' ≫ z := by
    rw [← Functor.map_comp]
    apply yonedaEquiv.injective
    rw [yonedaEquiv_yoneda_map, yonedaEquiv_comp, Equiv.apply_symm_apply]
    change k ≫ v i = z.app (op T') (Z.map g.op y)
    rwa [NatTrans.naturality_apply]
  have key : yonedaEquiv.symm y' ≫ m = yonedaEquiv.symm y' ≫ m' := by
    rw [← pullback.lift_snd (yoneda.map k) (yonedaEquiv.symm y') hzy', Category.assoc,
      Category.assoc, h i]
  simpa only [yonedaEquiv_comp, Equiv.apply_symm_apply] using congrArg yonedaEquiv key

/-- **Compatible local morphisms over a covering of the base glue.** Let `z : Z ⟶ T₀` and
`x : X ⟶ T₀` be morphisms of algebraic spaces to a scheme, `{vᵢ : Vᵢ ⟶ T₀}` a covering family,
and `μᵢ : Vᵢ ×_{T₀} Z ⟶ X` morphisms over `T₀` which agree after restriction to any `W` mapping to
two members compatibly. Then there is a morphism `m : Z ⟶ X` over `T₀` restricting to every
`μᵢ`. -/
theorem exists_hom_of_local (hZ : IsAlgebraicSpace B S hS Z) (hX : IsAlgebraicSpace B S hS X)
    (z : Z ⟶ yoneda.obj T₀) (x : X ⟶ yoneda.obj T₀) {I : Type*}
    (V : I → BigFppfOver B S hS) (v : ∀ i, V i ⟶ T₀)
    (hv : Sieve.ofArrows V v ∈ BigFppfOver.topology B S hS T₀)
    (μ : ∀ i, pullback (yoneda.map (v i)) z ⟶ X)
    (hμ : ∀ i, μ i ≫ x = pullback.snd (yoneda.map (v i)) z ≫ z)
    (hcompat : ∀ (i j : I) {W : BigFppfOver B S hS} (gi : W ⟶ V i) (gj : W ⟶ V j)
      (h : yoneda.map gi ≫ yoneda.map (v i) = yoneda.map gj ≫ yoneda.map (v j)),
      pullback.lift (pullback.fst _ _ ≫ yoneda.map gi) (pullback.snd _ _)
          (by rw [Category.assoc, pullback.condition]) ≫ μ i =
        pullback.lift (pullback.fst (yoneda.map gi ≫ yoneda.map (v i)) z ≫ yoneda.map gj)
          (pullback.snd _ _) (by rw [Category.assoc, ← h, pullback.condition]) ≫ μ j) :
    ∃ m : Z ⟶ X, m ≫ x = z ∧ ∀ i, pullback.snd (yoneda.map (v i)) z ≫ m = μ i := by
  have hQ : IsAlgebraicSpace B S hS (yoneda.obj T₀) := isAlgebraicSpace_yoneda B S hS T₀
  let F := Space.relativeHom B S hS Z X (yoneda.obj T₀) z x hZ hX hQ
  let sec := fun T => Space.relativeHomSections B S hS Z X (yoneda.obj T₀) z x hZ hX hQ T
  have hF : Presieve.IsSheafFor F (Presieve.ofArrows V v) :=
    (Presieve.isSheafFor_iff_generate (P := F) _).mpr
      (((isSheaf_iff_isSheaf_of_type (BigFppfOver.topology B S hS) F).mp
        (Space.isSheaf_relativeHom B S hS Z X (yoneda.obj T₀) z x hZ hX hQ)) _ hv)
  let p : ∀ i, Space.RelativeMorphism B S hS Z X (yoneda.obj T₀) z x (yoneda.obj (V i)) :=
    fun i => ⟨yoneda.map (v i), μ i, hμ i⟩
  have hcomp : Presieve.Arrows.Compatible F v (fun i => (sec (V i)).symm (p i)) := by
    intro i j W gi gj hg
    apply (sec W).injective
    rw [Space.relativeHomSections_map, Space.relativeHomSections_map, Equiv.apply_symm_apply,
      Equiv.apply_symm_apply]
    have hbase : yoneda.map gi ≫ yoneda.map (v i) = yoneda.map gj ≫ yoneda.map (v j) := by
      rw [← Functor.map_comp, hg, Functor.map_comp]
    refine Space.RelativeMorphism.ext_of_base_eq hbase ?_
    change pullback.map _ z _ z (yoneda.map gi) (𝟙 Z) (𝟙 _) _ _ ≫ μ i =
      (pullback.congrHom hbase rfl).hom ≫ pullback.map _ z _ z (yoneda.map gj) (𝟙 Z) (𝟙 _) _ _ ≫
        μ j
    have e₁ := pullback_map_comp_id_eq_lift (yoneda.map gi) (yoneda.map (v i)) z
    have e₂ : (pullback.congrHom hbase rfl).hom ≫
        pullback.map (yoneda.map gj ≫ yoneda.map (v j)) z (yoneda.map (v j)) z
          (yoneda.map gj) (𝟙 Z) (𝟙 _) (by simp) (by simp) =
        pullback.lift (pullback.fst (yoneda.map gi ≫ yoneda.map (v i)) z ≫ yoneda.map gj)
          (pullback.snd _ _) (by rw [Category.assoc, ← hbase, pullback.condition]) := by
      apply pullback.hom_ext
      · simp only [Category.assoc, pullback.map_fst, pullback.congrHom_hom, pullback.lift_fst_assoc]
        exact (pullback.lift_fst _ _ _).symm
      · simp only [Category.assoc, Category.comp_id, pullback.congrHom_hom,
          pullback.lift_snd]
    refine (congrArg (· ≫ μ i) e₁).trans ((hcompat i j gi gj hbase).trans ?_)
    rw [← Category.assoc, e₂]
  obtain ⟨t, ht, -⟩ := (Presieve.isSheafFor_arrows_iff F v).1 hF _ hcomp
  let q := sec T₀ t
  have hq : ∀ i, Space.RelativeMorphism.restrict (yoneda.map (v i)) q = p i := by
    intro i
    have := congrArg (sec (V i)) (ht i)
    rwa [Space.relativeHomSections_map, Equiv.apply_symm_apply] at this
  have hbase : q.base = 𝟙 _ := by
    refine hom_ext_of_local hQ.isSheaf (𝟙 _) V v hv fun i => ?_
    have hb : yoneda.map (v i) ≫ q.base = yoneda.map (v i) :=
      congrArg Space.RelativeMorphism.base (hq i)
    have hc : pullback.snd (yoneda.map (v i)) (𝟙 (yoneda.obj T₀)) =
        pullback.fst (yoneda.map (v i)) (𝟙 (yoneda.obj T₀)) ≫ yoneda.map (v i) := by
      rw [pullback.condition, Category.comp_id]
    rw [hc, Category.assoc, hb, Category.comp_id]
  refine ⟨pullback.lift z (𝟙 Z) (by simp [hbase]) ≫ q.morphism, ?_, fun i => ?_⟩
  · rw [Category.assoc, q.commutes, ← Category.assoc, pullback.lift_snd, Category.id_comp]
  · have hk : pullback.fst (yoneda.map (v i)) z ≫
        (Space.RelativeMorphism.restrict (yoneda.map (v i)) q).base =
          pullback.snd (yoneda.map (v i)) z ≫ z := by
      rw [Space.RelativeMorphism.restrict_base, hbase, Category.comp_id, pullback.condition]
    have key := RelativeMorphism.lift_morphism_eq (hq i) (pullback.fst (yoneda.map (v i)) z)
      (pullback.snd _ _) hk
    rw [pullback.lift_fst_snd, Category.id_comp] at key
    change pullback.lift _ _ hk ≫ pullback.map _ z _ z (yoneda.map (v i)) (𝟙 Z) (𝟙 _) _ _ ≫
      q.morphism = μ i at key
    rw [← key, ← Category.assoc, ← Category.assoc]
    congr 1
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst]
      rw [← Category.assoc, pullback.lift_fst]
      exact pullback.condition.symm
    · simp only [Category.assoc, pullback.lift_snd, Category.comp_id]

end AlgebraicGeometry.C1590Private

end
