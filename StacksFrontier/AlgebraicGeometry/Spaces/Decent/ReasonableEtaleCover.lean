module

public import StacksFrontier.AlgebraicGeometry.Descent.Germs.EtaleQuasiFinite
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.UniversallyBoundedQuasiFinite
public import StacksFrontier.AlgebraicGeometry.SigmaPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.FinitenessConditions
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.UniversallyBoundedFibresDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.UniversallyBoundedFibresOpenCover
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteCoproduct
public import StacksFrontier.AlgebraicGeometry.Spaces.Glueing.FppfCovering
public import StacksFrontier.AlgebraicGeometry.Spaces.Reasonable
public import StacksFrontier.CategoryTheory.Sites.Representable.CoproductYonedaDesc

/-!
# Reasonableness and jointly surjective bounded étale covers

Stacks 03JT says that two conditions on an algebraic space `X` over a scheme `S` are
equivalent: `(1)` there is a jointly surjective family of étale scheme charts of `X`, each with
universally bounded fibres, and `(2)` every étale chart of `X` by an affine scheme has
universally bounded fibres. Condition `(2)` is
`AlgebraicGeometry.Space.IsReasonableSpace`, the formulation of reasonableness the library
carries. This file proves both implications and records the equivalence.

For `(2) ⇒ (1)`: an algebraic space has an étale chart whose source is a disjoint union of
affine schemes, by Stacks 03FX; the affine summands then form a jointly surjective family of
affine étale charts, and `(2)` bounds the fibres of each of them.

For `(1) ⇒ (2)`: let `ψ : U ⟶ X` be an étale chart with `U` affine. Each fibre product
`U ×_X U_i` is represented by an object of the site whose two projections are étale, and the
projections to `U` are jointly surjective on points because the family is. An affine open `W`
of `U ×_X U_i` is quasi-compact, so the fibres of `W ⟶ U_i` are universally bounded by
Stacks 03JA, and Stacks 03JM composes that bound with the one for `U_i ⟶ X`. Finitely many
such `W` cover `U` because `U` is quasi-compact; the fibres of their coproduct over `X` are
bounded because bounded fibres are detected on the summands of a coproduct, and the coproduct
maps onto `U` by a surjective flat morphism, so the bound descends by Stacks 03JP.

## Main results

* `AlgebraicGeometry.Space.isReasonableSpace_iff_exists_boundedEtaleCover`: **Stacks 03JT**.
* `AlgebraicGeometry.Space.exists_boundedEtaleCover_of_isReasonableSpace` and
  `AlgebraicGeometry.Space.isReasonableSpace_of_boundedEtaleCover`: its two implications. The
  first produces a family of charts by *affine* schemes, which is more than condition `(1)`
  asks for and is what a client needing an affine chart uses.

## Implementation notes

Joint surjectivity is local surjectivity of the induced morphism out of the coproduct of the
representable presheaves, as in `AlgebraicGeometry.Space.IsVeryReasonableSpace`. In `(2) ⇒ (1)`
the coproduct morphism of the family factors as the coproduct morphism of the summand
inclusions followed by the chart, and local surjectivity holds for each factor: for the summand
inclusions because a jointly surjective family of open immersions is a Zariski, hence fppf,
covering (Stacks 00WT), and for the chart because it is surjective and étale after every
representable base change.

In `(1) ⇒ (2)` the two notions of universally bounded fibres have to be interchanged, since
Stacks 03JA concludes in the form of Stacks 03J4 for a morphism of schemes while Stacks 03JM
consumes the form of Stacks 03JL for a morphism to a presheaf; they agree for a morphism of
the site by `AlgebraicGeometry.Space.hasUniversallyBoundedFibers_yoneda_map_iff`.

## References

* [Stacks Project, Tag 00WT](https://stacks.math.columbia.edu/tag/00WT)
* [Stacks Project, Tag 03FX](https://stacks.math.columbia.edu/tag/03FX)
* [Stacks Project, Tag 03JA](https://stacks.math.columbia.edu/tag/03JA)
* [Stacks Project, Tag 03JL](https://stacks.math.columbia.edu/tag/03JL)
* [Stacks Project, Tag 03JM](https://stacks.math.columbia.edu/tag/03JM)
* [Stacks Project, Tag 03JP](https://stacks.math.columbia.edu/tag/03JP)
* [Stacks Project, Tag 03JT](https://stacks.math.columbia.edu/tag/03JT)
-/
@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The implication (2) ⇒ (1) of Stacks 03JT. A reasonable algebraic space over `S` — one all
of whose étale charts by affine schemes have universally bounded fibres — has a jointly
surjective family of étale charts by affine schemes with universally bounded fibres.

The family is the one of Stacks 03FX: an étale chart of the space whose source is a disjoint
union of affine schemes, taken summand by summand. -/
theorem exists_boundedEtaleCover_of_isReasonableSpace
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X)
    (h : IsReasonableSpace B S hS X) :
    ∃ (I : Type u) (U : I → BigFppfOver B S hS) (φ : ∀ i, yoneda.obj (U i) ⟶ X),
      Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) (Sigma.desc φ) ∧
      ∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj (U i)) ∧
        (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) (φ i) ∧
        HasUniversallyBoundedFibers B S hS (U i) (φ i) := by
  obtain ⟨U, f, I, W, j, e, hfS, hfE, hWaff, hje, hjimm, hjetale, -⟩ :=
    IsAlgebraicSpace.exists_affine_coproduct_atlas B S hS X hX
  refine ⟨I, W, fun i ↦ yoneda.map (j i) ≫ f, ?_, fun i ↦ ⟨hWaff i, hjetale i,
    h (W i) (hWaff i) _ (hjetale i)⟩⟩
  have hsurj : ∀ x : (BigFppfOver.toScheme B S hS).obj U,
      ∃ (i : I) (y : (BigFppfOver.toScheme B S hS).obj (W i)),
        ((BigFppfOver.toScheme B S hS).map (j i)).base y = x := by
    intro x
    obtain ⟨i, y, hy⟩ :=
      exists_sigmaι_eq (fun i ↦ (BigFppfOver.toScheme B S hS).obj (W i)) (e.inv.base x)
    refine ⟨i, y, ?_⟩
    rw [← hje i, Scheme.Hom.comp_apply, hy, ← Scheme.Hom.comp_apply, e.inv_hom_id]
    rfl
  have hcover : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS)
      (coprodYonedaDesc W U j) :=
    isLocallySurjective_coprodYonedaDesc _ W U j
      (generate_ofArrows_mem_topology_of_openCover B S hS W j hjimm hsurj)
  have hchart : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) f :=
    isLocallySurjective_of_surjective_etale B S hS f hfS hfE
  have hdesc : (Sigma.desc fun i ↦ yoneda.map (j i) ≫ f) = coprodYonedaDesc W U j ≫ f := by
    refine Sigma.hom_ext _ _ fun i ↦ ?_
    rw [Sigma.ι_comp_desc, coprodYonedaDesc, ← Category.assoc, Sigma.ι_comp_desc]
  rw [hdesc]
  exact Presheaf.isLocallySurjective_comp _ _ _

/-- **Stacks 03JT, the implication (1) ⇒ (2).** If an algebraic space over `S` carries a jointly
surjective family of étale charts by schemes whose fibres are universally bounded, then every
étale chart of it by an affine scheme has universally bounded fibres.

Let `ψ : U ⟶ X` be an étale chart with `U` affine. Each fibre product `U ×_X U_i` is
represented by an object of the site whose two projections are étale, and the projections to
`U` are jointly surjective on points because the family is. Around a point of `U ×_X U_i` over
a given point of `U` choose an affine open `W`; then `W ⟶ U_i` is locally quasi-finite and of
finite type with quasi-compact source, so its fibres are universally bounded by Stacks 03JA,
and Stacks 03JM composes that bound with the bound for `U_i ⟶ X` to bound the fibres of
`W ⟶ X`. Finitely many such `W` suffice because `U` is quasi-compact; the fibres of their
coproduct over `X` are bounded because bounded fibres are detected on the summands, and the
coproduct maps onto `U` by a surjective flat morphism, so the bound descends to `ψ` by
Stacks 03JP. -/
theorem isReasonableSpace_of_boundedEtaleCover
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X)
    {I : Type u} (Ui : I → BigFppfOver B S hS) (φ : ∀ i, yoneda.obj (Ui i) ⟶ X)
    (hloc : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) (Sigma.desc φ))
    (hetale : ∀ i, (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) (φ i))
    (hbnd : ∀ i, HasUniversallyBoundedFibers B S hS (Ui i) (φ i)) :
    IsReasonableSpace B S hS X := by
  classical
  have hlas : IsZariskiLocalAtSource (@AlgebraicGeometry.Etale.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.Etale)
  have hec : MorphismProperty.IsStableUnderComposition (@AlgebraicGeometry.Etale.{u}) :=
    etale_isStableUnderComposition
  intro U hUaff ψ hψ
  have hsq : ∀ i, IsPullback (yoneda.map (hψ.rep.fst' (φ i)))
      (yoneda.map (hψ.rep.snd (φ i))) ψ (φ i) := fun i ↦ hψ.rep.isPullback' (φ i)
  -- Around every point of the chart, an affine open of a fibre product with a bound over `X`.
  have key : ∀ y : (BigFppfOver.toScheme B S hS).obj U,
      ∃ (W : BigFppfOver B S hS) (ρ : W ⟶ U),
        Etale ((BigFppfOver.toScheme B S hS).map ρ) ∧
        y ∈ Set.range ((BigFppfOver.toScheme B S hS).map ρ).base ∧
        HasUniversallyBoundedFibers B S hS W (yoneda.map ρ ≫ ψ) := by
    intro y
    obtain ⟨i, z, hz⟩ := exists_point_factor_of_cover B S hS
      (fun i ↦ hψ.rep.pullback (φ i)) (fun i ↦ hψ.rep.fst' (φ i))
      (pullback_family_sieve_cover B S hS ψ Ui φ hloc hψ.rep) y
    obtain ⟨O, hOaff, hzO, -⟩ := exists_isAffineOpen_mem_and_subset
      (X := (BigFppfOver.toScheme B S hS).obj (hψ.rep.pullback (φ i))) (x := z) (U := ⊤)
      trivial
    have hOa : IsAffine O.toScheme := hOaff
    refine ⟨openObj B S hS (hψ.rep.pullback (φ i)) O,
      openIncl B S hS (hψ.rep.pullback (φ i)) O ≫ hψ.rep.fst' (φ i), ?_, ?_, ?_⟩
    · rw [Functor.map_comp, toScheme_map_openIncl]
      exact MorphismProperty.comp_mem _ _ _ (inferInstanceAs (Etale O.ι))
        ((hetale i).property ψ (yoneda.map (hψ.rep.snd (φ i))) (hψ.rep.fst' (φ i)) (hsq i).flip)
    · rw [Functor.map_comp, toScheme_map_openIncl]
      exact ⟨⟨z, hzO⟩, hz⟩
    · have hWEt : Etale ((BigFppfOver.toScheme B S hS).map
          (openIncl B S hS (hψ.rep.pullback (φ i)) O ≫ hψ.rep.snd (φ i))) := by
        rw [Functor.map_comp, toScheme_map_openIncl]
        exact MorphismProperty.comp_mem _ _ _ (inferInstanceAs (Etale O.ι))
          (hψ.property_snd (φ i))
      obtain ⟨hft, hqf⟩ := locallyQuasiFinite_of_etale ((BigFppfOver.toScheme B S hS).map
        (openIncl B S hS (hψ.rep.pullback (φ i)) O ≫ hψ.rep.snd (φ i)))
      have hcs : CompactSpace ((BigFppfOver.toScheme B S hS).obj
          (openObj B S hS (hψ.rep.pullback (φ i)) O)) := by
        rw [toScheme_obj_openObj]
        infer_instance
      obtain ⟨N, hN⟩ := hasUniversallyBoundedFibers_of_locallyQuasiFinite
        ((BigFppfOver.toScheme B S hS).map
          (openIncl B S hS (hψ.rep.pullback (φ i)) O ≫ hψ.rep.snd (φ i)))
      have h3 := hasUniversallyBoundedFibers_comp B S hS
        (openIncl B S hS (hψ.rep.pullback (φ i)) O ≫ hψ.rep.snd (φ i)) (φ i)
        (hasUniversallyBoundedFibers_yoneda_map_of_boundsFiberDegrees B S hS _ N hN) (hbnd i)
      have heq : yoneda.map (openIncl B S hS (hψ.rep.pullback (φ i)) O ≫
            hψ.rep.snd (φ i)) ≫ φ i =
          yoneda.map (openIncl B S hS (hψ.rep.pullback (φ i)) O ≫
            hψ.rep.fst' (φ i)) ≫ ψ := by
        rw [Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc, (hsq i).w]
      rwa [heq] at h3
  choose W ρ hρEt hρmem hρbnd using key
  -- Finitely many of them cover the affine, hence quasi-compact, chart.
  have hUcs : CompactSpace ((BigFppfOver.toScheme B S hS).obj U) := by
    have := hUaff
    infer_instance
  have hopen : ∀ y, IsOpen (Set.range ((BigFppfOver.toScheme B S hS).map (ρ y)).base) :=
    fun y ↦ have := hρEt y
      ((BigFppfOver.toScheme B S hS).map (ρ y)).isOpenMap.isOpen_range
  obtain ⟨t, ht⟩ := CompactSpace.elim_nhds_subcover
    (fun y ↦ Set.range ((BigFppfOver.toScheme B S hS).map (ρ y)).base)
    fun y ↦ (hopen y).mem_nhds (hρmem y)
  -- Their coproduct maps onto the chart by a surjective flat morphism.
  set Wf : {y : (BigFppfOver.toScheme B S hS).obj U // y ∈ t} → BigFppfOver B S hS :=
    fun l ↦ W l.1
  set ρsig : BigFppfOver.sigmaObj B S hS Wf ⟶ U :=
    Cofan.IsColimit.desc (BigFppfOver.isColimit_sigmaCofan B S hS Wf) fun l ↦ ρ l.1
  have hfac : ∀ l, BigFppfOver.sigmaIncl B S hS Wf l ≫ ρsig = ρ l.1 := fun l ↦
    Cofan.IsColimit.fac (BigFppfOver.isColimit_sigmaCofan B S hS Wf) (fun l ↦ ρ l.1) l
  have hincopen : ∀ l, _root_.AlgebraicGeometry.IsOpenImmersion
      ((BigFppfOver.toScheme B S hS).map (BigFppfOver.sigmaIncl B S hS Wf l)) := by
    intro l
    rw [BigFppfOver.toScheme_map_sigmaIncl]
    exact inferInstanceAs (_root_.AlgebraicGeometry.IsOpenImmersion
      (Sigma.ι (fun i ↦ (BigFppfOver.toScheme B S hS).obj (Wf i)) l))
  have hincsurj : ∀ w : (BigFppfOver.toScheme B S hS).obj (BigFppfOver.sigmaObj B S hS Wf),
      ∃ (l : {y : (BigFppfOver.toScheme B S hS).obj U // y ∈ t})
        (z : (BigFppfOver.toScheme B S hS).obj (Wf l)),
        (BigFppfOver.toScheme B S hS).map (BigFppfOver.sigmaIncl B S hS Wf l) z = w := by
    intro w
    obtain ⟨l, z, hzw⟩ :=
      exists_sigmaι_eq (fun l ↦ (BigFppfOver.toScheme B S hS).obj (Wf l)) w
    exact ⟨l, z, by rwa [BigFppfOver.toScheme_map_sigmaIncl]⟩
  have hsigbnd : HasUniversallyBoundedFibers B S hS (BigFppfOver.sigmaObj B S hS Wf)
      (yoneda.map ρsig ≫ ψ) := by
    refine hasUniversallyBoundedFibers_of_finite_openCover B S hS _
      (MorphismProperty.comp_mem _ _ _
        (Functor.relativelyRepresentable.map yoneda ρsig) hψ.rep)
      Wf (BigFppfOver.sigmaIncl B S hS Wf) hincopen hincsurj fun l ↦ ?_
    rw [← Category.assoc, ← Functor.map_comp, hfac l]
    exact hρbnd l.1
  -- The coproduct maps onto the chart, étale and hence flat, so the bound descends.
  let 𝒲 : ((BigFppfOver.toScheme B S hS).obj
      (BigFppfOver.sigmaObj B S hS Wf)).OpenCover :=
    Scheme.Cover.mkOfCovers _ (fun l ↦ (BigFppfOver.toScheme B S hS).obj (Wf l))
      (fun l ↦ (BigFppfOver.toScheme B S hS).map (BigFppfOver.sigmaIncl B S hS Wf l))
      hincsurj fun l ↦ hincopen l
  have hsigEt : Etale ((BigFppfOver.toScheme B S hS).map ρsig) := by
    refine IsZariskiLocalAtSource.of_openCover (𝒰 := 𝒲) fun l ↦ ?_
    change Etale ((BigFppfOver.toScheme B S hS).map (BigFppfOver.sigmaIncl B S hS Wf l) ≫
      (BigFppfOver.toScheme B S hS).map ρsig)
    rw [← Functor.map_comp, hfac l]
    exact hρEt l.1
  have hsigSurj : Surjective ((BigFppfOver.toScheme B S hS).map ρsig) := by
    refine ⟨fun y ↦ ?_⟩
    obtain ⟨l, hl, x, hx⟩ := Set.mem_iUnion₂.mp (ht.ge (Set.mem_univ y))
    refine ⟨(BigFppfOver.toScheme B S hS).map
      (BigFppfOver.sigmaIncl B S hS Wf ⟨l, hl⟩) x, ?_⟩
    rwa [← Scheme.Hom.comp_apply, ← Functor.map_comp, hfac ⟨l, hl⟩]
  exact hasUniversallyBoundedFibers_of_comp_of_surjective_flat B S hS hX ρsig ψ hsigbnd

/-- **Stacks 03JT.** For an algebraic space `X` over `S` the following are equivalent: `(1)`
there is a jointly surjective family of étale charts of `X` by schemes, each with universally
bounded fibres, and `(2)` every étale chart of `X` by an affine scheme has universally bounded
fibres, which is `AlgebraicGeometry.Space.IsReasonableSpace`. -/
@[stacks 03JT]
theorem isReasonableSpace_iff_exists_boundedEtaleCover
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X) :
    IsReasonableSpace B S hS X ↔
      ∃ (I : Type u) (U : I → BigFppfOver B S hS) (φ : ∀ i, yoneda.obj (U i) ⟶ X),
        Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) (Sigma.desc φ) ∧
        ∀ i, (MorphismProperty.presheaf (MorphismProperty.inverseImage
          (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS))) (φ i) ∧
          HasUniversallyBoundedFibers B S hS (U i) (φ i) := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · obtain ⟨I, Ui, φ, hloc, hmem⟩ := exists_boundedEtaleCover_of_isReasonableSpace B S hS X hX h
    exact ⟨I, Ui, φ, hloc, fun i ↦ ⟨(hmem i).2.1, (hmem i).2.2⟩⟩
  · rintro ⟨I, Ui, φ, hloc, hmem⟩
    exact isReasonableSpace_of_boundedEtaleCover B S hS X hX Ui φ hloc
      (fun i ↦ (hmem i).1) fun i ↦ (hmem i).2

end AlgebraicGeometry.Space

end
