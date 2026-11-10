module

public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.MorphismDescentData
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.ModificationsHenselianLocalRing
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.IntegralFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.ProperKernelPairReduction
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactEtaleLocalTarget

/-!
# A finite morphism of finite presentation onto a limit comes from a stage

Let `D` be a directed inverse system of quasi-compact, quasi-separated algebraic spaces with
affine transition morphisms, under the chapter's convention of Section 70.2 (tag 07SD), with
algebraic limit `lim D`.  A finite morphism of finite presentation `T ⟶ lim D` is the base
change of a finite morphism of finite presentation `T_i ⟶ D_i` at some stage.

## Main results

* `AlgebraicGeometry.Space.exists_isFinite_model_of_siteContainsBaseChangeLimits`: the descent of
  a finite morphism of finite presentation to a stage.

## Implementation notes

Stacks 084Z is stated for the data `AlgebraicGeometry.Space.MorphismDescentData` of Situation
084W.  Here the base system is `D` itself, the morphism to descend is the model
`f₀ = T_{i₀} ⟶ D_{i₀}` given by Stacks 07SK, and its target is the stage `D_{i₀}` over itself.
The limit morphism `f` of the situation is a chosen fibre product, isomorphic as an arrow to
`T ⟶ lim D`, so it is finite because finiteness is stable under base change
(`AlgebraicGeometry.Space.isFinite_of_isPullback`), an isomorphism of arrows being a cartesian
square.

## References

* [Stacks Project, Tag 07SK](https://stacks.math.columbia.edu/tag/07SK)
* [Stacks Project, Tag 084Z](https://stacks.math.columbia.edu/tag/084Z)
* [Stacks Project, Tag 0GV1](https://stacks.math.columbia.edu/tag/0GV1)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (hZ : B.Contains (⊤_ Scheme.{u}))

/-- **A finite morphism of finite presentation onto the limit of a system comes from a stage**,
under the chapter's convention.  Let `D` be a directed inverse system of quasi-compact,
quasi-separated algebraic spaces with affine transition morphisms satisfying
`AlgebraicGeometry.Space.SiteContainsBaseChangeLimits`, with algebraic limit.  If `T ⟶ lim D` is
finite and of finite presentation, there are a stage `i` and a finite morphism of finite
presentation `T_i ⟶ D_i` whose base change to `lim D` is `T`. -/
theorem exists_isFinite_model_of_siteContainsBaseChangeLimits
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
    (hAffine : ∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom B S hS (D.map f))
    (hQc : ∀ i, IsQuasiCompactSpace B S hS (D.obj i))
    (hQs : ∀ i, IsAbsolutelyQuasiSeparated B S hS hZ (D.obj i))
    (hconv : SiteContainsBaseChangeLimits B S hS D)
    (hDlim : IsAlgebraicSpace B S hS (limit D))
    (T : Over (limit D)) (hT : IsAlgebraicSpace B S hS T.left)
    (hfin : IsFinite B S hS T.hom) (hfp : IsFinitePresentation B S hS T.hom) :
    ∃ (i : I) (Tᵢ : Over (D.obj (op i))), IsAlgebraicSpace B S hS Tᵢ.left ∧
      IsFinite B S hS Tᵢ.hom ∧ IsFinitePresentation B S hS Tᵢ.hom ∧
      Nonempty (T ≅ (Over.pullback (limit.π D (op i))).obj Tᵢ) := by
  obtain ⟨i₀, T₀, hT₀, hT₀fp, ⟨e⟩⟩ :=
    exists_model_of_finitePresentation_of_siteContainsBaseChangeLimits B S hS hZ D hD hAffine
      hQc hQs hconv hDlim T hT hfp
  have hT₀qc : IsQuasiCompactSpace B S hS T₀.left :=
    isQuasiCompactSpace_source_of_isQuasiCompact B S hS (hD _) (hQc _) hT₀fp.2.1
  have hT₀qs : IsAbsolutelyQuasiSeparated B S hS hZ T₀.left :=
    isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS hZ hT₀ (hQs _) hT₀fp.2.2
  let M : MorphismDescentData B S hS hZ I :=
    { base := D
      base_isAlgebraicSpace := fun i => hD (op i)
      transition_affine := hAffine
      initial := i₀.unop
      source₀ := T₀.left
      target₀ := D.obj i₀
      sourceToBase := T₀.hom
      targetToBase := 𝟙 _
      map₀ := T₀.hom
      map₀_over := Category.comp_id _
      source₀_isAlgebraicSpace := hT₀
      target₀_isAlgebraicSpace := hD _
      base₀_quasiCompact := hQc _
      base₀_quasiSeparated := hQs _
      source₀_quasiCompact := hT₀qc
      source₀_quasiSeparated := hT₀qs
      target₀_quasiCompact := hQc _
      target₀_quasiSeparated := hQs _ }
  have hml : IsFinite B S hS (M.toMorphismDescentSituation hconv).mapLimit := by
    have hfst : (M.toMorphismDescentSituation hconv).mapLimit ≫
        pullback.fst (limit.π D i₀) (𝟙 (D.obj i₀)) = pullback.fst (limit.π D i₀) T₀.hom :=
      pullback.lift_fst _ _ _
    have hw : e.inv.left ≫ T.hom = pullback.snd T₀.hom (limit.π D i₀) := Over.w e.inv
    have : IsIso e.inv.left := inferInstanceAs (IsIso ((Over.forget _).map e.inv))
    have hiso : IsIso (pullback.fst (limit.π D i₀) (𝟙 (D.obj i₀))) :=
      (IsPullback.of_hasPullback (limit.π D i₀) (𝟙 _)).isIso_fst_of_isIso
    have sq : IsPullback ((pullbackSymmetry (limit.π D i₀) T₀.hom).hom ≫ e.inv.left)
        (M.toMorphismDescentSituation hconv).mapLimit T.hom
        (pullback.fst (limit.π D i₀) (𝟙 (D.obj i₀))) :=
      @IsPullback.of_horiz_isIso _ _ _ _ _ _ _ _ _ _ inferInstance hiso ⟨by
        rw [Category.assoc, hw, pullbackSymmetry_hom_comp_snd]
        exact hfst.symm⟩
    exact isFinite_of_isPullback B S hS sq hfin
  obtain ⟨i, hi, hfi⟩ := M.exists_isFinite_mapAt hconv hml
    (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS hT₀fp.1)
  set g : D.obj (op i) ⟶ D.obj i₀ := D.map (homOfLE hi).op
  refine ⟨i, (Over.pullback g).obj T₀,
    isAlgebraicSpace_pullback B S hS T₀.hom g hT₀ (hD _) (hD _), ?_,
    isFinitePresentation_pullback_snd B S hS T₀.hom g hT₀ (hD _) (hD _) hT₀fp, ?_⟩
  · have hfst : (M.toMorphismDescentSituation hconv).mapAt i hi ≫
        pullback.fst g (𝟙 (D.obj i₀)) = pullback.fst g T₀.hom :=
      pullback.lift_fst _ _ _
    have hiso : IsIso (pullback.fst g (𝟙 (D.obj i₀))) :=
      (IsPullback.of_hasPullback g (𝟙 _)).isIso_fst_of_isIso
    have hsnd : pullback.snd T₀.hom g = (pullbackSymmetry T₀.hom g).hom ≫
        (M.toMorphismDescentSituation hconv).mapAt i hi ≫ pullback.fst g (𝟙 (D.obj i₀)) :=
      (pullbackSymmetry_hom_comp_fst T₀.hom g).symm.trans
        (congrArg (fun z => (pullbackSymmetry T₀.hom g).hom ≫ z) hfst.symm)
    change IsFinite B S hS (pullback.snd T₀.hom g)
    rw [hsnd]
    exact isFinite_comp B S hS (isFinite_of_isIso_hom B S hS _)
      (isFinite_comp B S hS hfi (@isFinite_of_isIso_hom B S hS _ _ _ hiso))
  · have hw : limit.π D (op i) ≫ g = limit.π D i₀ := limit.w D (homOfLE hi).op
    exact ⟨e ≪≫ Over.isoMk (f := (Over.pullback (limit.π D i₀)).obj T₀)
      (g := (Over.pullback (limit.π D (op i) ≫ g)).obj T₀)
      (pullback.congrHom (rfl : T₀.hom = T₀.hom) hw.symm) (by simp) ≪≫
        (Over.pullbackComp (limit.π D (op i)) g).app T₀⟩

end AlgebraicGeometry.Space

end
