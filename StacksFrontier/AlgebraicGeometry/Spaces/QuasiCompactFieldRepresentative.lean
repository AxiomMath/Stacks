module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.ConnectedNeighborhoods
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompact
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.RelationFibers
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae

/-!
# Quasi-compactness of a field-valued representative with finite étale fibre products

Let `F` be an algebraic space over a scheme `S` and let `p` be a field-valued point of `F`. If
for every étale chart `ψ : h_V ⟶ F` by an *affine* scheme the fibre product `V ×_F Spec k` is
finite over `Spec k`, then the morphism `Spec k ⟶ F` presented by `p` is quasi-compact.

## Main results

* `AlgebraicGeometry.Space.isQuasiCompact_fieldMorphism_of_isFinite_pullback`: the
  quasi-compactness criterion.

## References

* [Stacks Project, Tag 03JV](https://stacks.math.columbia.edu/tag/03JV)
* [Stacks Project, Tag 03KG](https://stacks.math.columbia.edu/tag/03KG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- A scheme which is étale and finite over the spectrum of a field has finitely many
points. -/
private theorem finite_of_isFinite_of_etale_over_subsingleton {T T' : Scheme.{u}}
    (f : T ⟶ T') (hfin : _root_.AlgebraicGeometry.IsFinite f)
    (hetale : Etale f) (hsub : Subsingleton T') : Finite T := by
  have := (AlgebraicGeometry.locallyQuasiFinite_of_etale f).2
  rcases isEmpty_or_nonempty T with hE | hT
  · infer_instance
  · obtain ⟨t⟩ := hT
    have hfib := f.finite_preimage_singleton (f.base t)
    refine Set.finite_univ_iff.mp (hfib.subset fun z _ ↦ ?_)
    exact Subsingleton.elim (α := T') _ _

/-- A field-valued point of an algebraic space over `S` presents it by a quasi-compact morphism as
soon as every cartesian square exhibiting the fibre product of the presenting morphism with an
étale chart by an affine scheme has its projection to the field spectrum a finite morphism. -/
theorem isQuasiCompact_fieldMorphism_of_isFinite_pullback
    (hF : IsAlgebraicSpace B S hS F) (p : FieldValuedPoint B S hS F)
    (hfin : ∀ (V : BigFppfOver B S hS), IsAffine ((BigFppfOver.toScheme B S hS).obj V) →
      ∀ (ψ : yoneda.obj V ⟶ F), (MorphismProperty.inverseImage
          (@Etale.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS)).presheaf ψ →
        ∀ {W : BigFppfOver B S hS} (a : W ⟶ V) (g : W ⟶ p.siteObject),
          IsPullback (yoneda.map a) (yoneda.map g) ψ (fieldMorphism B S hS F p) →
          _root_.AlgebraicGeometry.IsFinite ((BigFppfOver.toScheme B S hS).map g)) :
    IsQuasiCompact B S hS (fieldMorphism B S hS F p) := by
  classical
  let Q := BigFppfOver.toScheme B S hS
  let fm := fieldMorphism B S hS F p
  obtain ⟨V, φ, hsurjφ, hetaleφ⟩ := hF.exists_atlas
  let 𝒰 := (Q.obj V).affineCover
  let Vi : 𝒰.I₀ → BigFppfOver B S hS := fun j ↦ Stacks.SeparationLocal.openObj B S hS V (𝒰.f j)
  let ιi : ∀ j, Vi j ⟶ V := fun j ↦ Stacks.SeparationLocal.openObjHom B S hS V (𝒰.f j)
  let ψi : ∀ j, yoneda.obj (Vi j) ⟶ F := fun j ↦ yoneda.map (ιi j) ≫ φ
  have hViaff (j : 𝒰.I₀) : IsAffine (Q.obj (Vi j)) := by
    show IsAffine (𝒰.X j)
    infer_instance
  have hιi (j : 𝒰.I₀) : Etale (Q.map (ιi j)) := by
    show Etale (𝒰.f j)
    infer_instance
  have hψi (j : 𝒰.I₀) : (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) Q).presheaf (ψi j) := by
    have := isMultiplicative_presheaf_etale B S hS
    exact MorphismProperty.comp_mem _ _ _
      ((presheaf_yoneda_map_iff B S hS Etale.etale_isStableUnderBaseChange (ιi j)).2
        (hιi j)) hetaleφ
  have hιcov (z : Q.obj V) : ∃ j, ∃ w, Q.map (ιi j) w = z := by
    have hz : z ∈ ⋃ j, Set.range (𝒰.f j).base := by rw [𝒰.iUnion_range]; trivial
    exact Set.mem_iUnion.1 hz
  have hcov : IsEtaleCovering B S hS (fun j ↦ yoneda.obj (Vi j)) ψi := by
    refine ⟨hF, fun j ↦ isAlgebraicSpace_yoneda B S hS (Vi j),
      fun j ↦ isEtale_of_presheaf_etale B S hS (hψi j), ?_⟩
    refine Set.eq_univ_of_forall fun x ↦ Set.mem_iUnion.2 ?_
    obtain ⟨u, hu⟩ := (surjective_iff_surjective_pointsMap B S hS F hF V φ).mp hsurjφ x
    obtain ⟨j, y, hy⟩ :=
      exists_pointsMap_yonedaMap_eq_of_jointly_surjective B S hS ιi hιcov u
    refine ⟨j, y, ?_⟩
    rw [show ψi j = yoneda.map (ιi j) ≫ φ from rfl, pointsMap_comp, Function.comp_apply, hy, hu]
  refine isQuasiCompact_of_isEtaleCovering B S hS
    (isAlgebraicSpace_yoneda B S hS p.siteObject) hF fm hcov fun j ↦ ?_
  let rep := (hψi j).rep
  let a : rep.pullback fm ⟶ Vi j := rep.fst' fm
  let g : rep.pullback fm ⟶ p.siteObject := rep.snd fm
  have sq : IsPullback (yoneda.map a) (yoneda.map g) (ψi j) fm := rep.isPullback' fm
  have hgfin : _root_.AlgebraicGeometry.IsFinite (Q.map g) :=
    hfin (Vi j) (hViaff j) (ψi j) (hψi j) a g sq
  have hgetale : Etale (Q.map g) := (hψi j).property fm (yoneda.map a) g sq
  have _ : Finite (Q.obj (rep.pullback fm)) :=
    finite_of_isFinite_of_etale_over_subsingleton (Q.map g) hgfin hgetale
      (subsingleton_toScheme_siteObject B S hS F p)
  have hqc : QuasiCompact (Q.map a) := by
    rw [quasiCompact_iff_forall_isAffineOpen]
    exact fun _ _ ↦ (Set.toFinite _).isCompact
  have : HasPullback (ψi j) fm := sq.hasPullback
  refine isQuasiCompact_of_isIso_comp B S hS sq.isoPullback.hom ?_
  rw [sq.isoPullback_hom_fst]
  exact quasiCompact_schemeMap_isQuasiCompact B S hS a hqc

end AlgebraicGeometry.Space

end
