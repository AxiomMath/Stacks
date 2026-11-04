module

public import StacksFrontier.AlgebraicGeometry.Spaces.Diagonal
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.InvariantSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheafAlgebraic
public import StacksFrontier.AlgebraicGeometry.Spaces.Representable

/-!
# The diagonal of a sheaf from a representable surjective étale atlas

Let `F` be a sheaf on the big fppf site of a scheme `S` which has a representable, surjective,
étale morphism `f : h_U ⟶ F` from an object `U` of the site. Granted effective descent along the
surjective étale morphisms of the site at the monomorphisms locally of finite type, the absolute
diagonal `Δ_F : F ⟶ F ⨯ F` is representable, and `F` is an algebraic space. This gives the
criteria of Stacks 0BGQ and 0BGR under that descent hypothesis.

## Main results

* `AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_of_coveringSieve`: effective
  descent along the covering sieves of the site implies it along the single surjective étale
  morphisms of the site.
* `AlgebraicGeometry.Space.presheaf_diag_of_kernelPair_of_etaleDescent`: a property `Q` of
  morphisms of schemes which is stable under base change and descends effectively along the
  surjective étale morphisms of the site holds for every represented base change of `Δ_F`, and
  those base changes are representable, as soon as `Q` holds for the morphism `R ⟶ U ×_S U`
  attached to the kernel pair of a representable surjective étale atlas.
* `AlgebraicGeometry.relativelyRepresentable_diag_of_surjective_etale_atlas`: the absolute
  diagonal of such a sheaf is representable.
* `AlgebraicGeometry.isAlgebraicSpace_of_surjective_etale_atlas_of_etaleDescent`: the criterion
  of Stacks 0BGQ, and
  `AlgebraicGeometry.isAlgebraicSpace_of_relativelyRepresentable_surjective_etale_of_etaleDescent`:
  the criterion of Stacks 0BGR, both granted that one descent hypothesis.

## References

* [Stacks Project, Tag 0BGQ](https://stacks.math.columbia.edu/tag/0BGQ)
* [Stacks Project, Tag 0BGR](https://stacks.math.columbia.edu/tag/0BGR)
* [Stacks Project, Tag 02X4](https://stacks.math.columbia.edu/tag/02X4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

namespace Space

/-! ### Comparing the two descent predicates -/

/-- **Effective descent along the covering sieves of the site implies effective descent along
its single surjective étale morphisms**, for a property of morphisms of schemes stable under
base change. -/
theorem isEffectiveDescentAlongSurjectiveEtale_of_coveringSieve
    {P : MorphismProperty Scheme.{u}} [P.IsStableUnderBaseChange]
    (hdesc : IsEffectiveDescentAlongCoveringSieve B S hS P) :
    IsEffectiveDescentAlongSurjectiveEtale B S hS P := by
  have hbc := MorphismProperty.relative_isStableUnderBaseChange (F := yoneda)
    (P.inverseImage (BigFppfOver.toScheme B S hS))
  have _hri : MorphismProperty.RespectsIso
      ((P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf) := hbc.respectsIso
  intro X Y f hX hY a c h q hqs hqe A m r sq hr
  have hrq : (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf
      (pullback.snd f (yoneda.map q ≫ h)) := by
    rw [← (IsPullback.of_hasPullback f (yoneda.map q ≫ h)).isoIsPullback_hom_snd _ _ sq]
    exact MorphismProperty.RespectsIso.precomp _ _ _ hr
  refine hdesc f hX hY h (Sieve.generate (Presieve.singleton q))
    (sieve_generate_singleton_mem_topology_over B S hS q hqs hqe) ?_
  intro b p hp
  obtain ⟨d, e, q', hq', hfac⟩ := hp
  cases hq'
  have hpq : yoneda.map p ≫ h = yoneda.map e ≫ yoneda.map q ≫ h := by
    rw [← hfac, Functor.map_comp, Category.assoc]
  have hbase : IsPullback
      (pullback.fst (pullback.snd f (yoneda.map q ≫ h)) (yoneda.map e))
      (pullback.snd (pullback.snd f (yoneda.map q ≫ h)) (yoneda.map e))
      (pullback.snd f (yoneda.map q ≫ h)) (yoneda.map e) := IsPullback.of_hasPullback _ _
  have hbig : IsPullback
      (pullback.fst (pullback.snd f (yoneda.map q ≫ h)) (yoneda.map e) ≫
        pullback.fst f (yoneda.map q ≫ h))
      (pullback.snd (pullback.snd f (yoneda.map q ≫ h)) (yoneda.map e)) f
      (yoneda.map p ≫ h) := by
    rw [hpq]
    exact hbase.paste_horiz (IsPullback.of_hasPullback f (yoneda.map q ≫ h))
  rw [← (IsPullback.of_hasPullback f (yoneda.map p ≫ h)).isoIsPullback_hom_snd _ _ hbig]
  exact MorphismProperty.RespectsIso.precomp _ _ _ (hbc.of_isPullback hbase hrq)

/-! ### The diagonal -/

/-- **The diagonal of a sheaf with a representable surjective étale atlas, from effective descent
along one surjective étale morphism.** Let `F` be a sheaf on the big fppf site of `S` with a
representable, surjective, étale atlas `f : h_U ⟶ F`, let `s, t : R ⟶ U` be the kernel pair of
`f`, and let `Q` be a property of morphisms of schemes which is stable under base change, which
descends effectively along the surjective étale morphisms of the site, and which holds for the
morphism `R ⟶ U ×_S U` built from `s` and `t`. Then every represented base change of the
absolute diagonal of `F` is representable and has `Q`. -/
theorem presheaf_diag_of_kernelPair_of_etaleDescent (Q : MorphismProperty Scheme.{u})
    [Q.IsStableUnderBaseChange]
    (hdesc : IsEffectiveDescentAlongSurjectiveEtale B S hS Q)
    (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F)
    {U R : BigFppfOver B S hS} {f : yoneda.obj U ⟶ F} {s t : R ⟶ U}
    (hst : IsPullback (yoneda.map s) (yoneda.map t) f f)
    (hsurj : MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)) f)
    (hetale : MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)) f)
    (hQ : Q ((BigFppfOver.toScheme B S hS).map (prod.lift s t))) :
    (MorphismProperty.presheaf (Q.inverseImage (BigFppfOver.toScheme B S hS))) (diag F) := by
  have _hQri : Q.RespectsIso := MorphismProperty.IsStableUnderBaseChange.respectsIso
  have _hri : MorphismProperty.RespectsIso
      (Q.inverseImage (BigFppfOver.toScheme B S hS)) :=
    MorphismProperty.RespectsIso.inverseImage _ _
  have hq : yoneda.relativelyRepresentable f := hsurj.rep
  have hmono : Mono (prod.lift (yoneda.map (prod.fst : U ⨯ U ⟶ U)) (yoneda.map prod.snd)) :=
    inferInstanceAs (Mono (prodComparison yoneda U U))
  have hjSq : IsPullback (yoneda.map s ≫ f) (yoneda.map (prod.lift s t)) (diag F)
      (prod.lift (yoneda.map (prod.fst : U ⨯ U ⟶ U) ≫ f) (yoneda.map prod.snd ≫ f)) :=
    isPullback_diag_of_isPullback f hst hmono
      (by rw [← Functor.map_comp, prod.lift_fst]) (by rw [← Functor.map_comp, prod.lift_snd])
  refine (MorphismProperty.presheaf_iff_forall_presheaf_pullback_snd _ _).2 ?_
  intro a g
  obtain ⟨b₁, c₁, α₁, hsq₁⟩ := hq (g ≫ (prod.fst : F ⨯ F ⟶ F))
  obtain ⟨b₂, c₂, α₂, hsq₂⟩ := hq (yoneda.map c₁ ≫ g ≫ (prod.snd : F ⨯ F ⟶ F))
  rw [← yoneda.map_preimage α₁] at hsq₁
  rw [← yoneda.map_preimage α₂] at hsq₂
  have hcs : Surjective ((BigFppfOver.toScheme B S hS).map (c₂ ≫ c₁)) := by
    have h₁ : Surjective ((BigFppfOver.toScheme B S hS).map c₁) := hsurj.property _ _ c₁ hsq₁
    have h₂ : Surjective ((BigFppfOver.toScheme B S hS).map c₂) := hsurj.property _ _ c₂ hsq₂
    rw [Functor.map_comp]
    infer_instance
  have hce : Etale ((BigFppfOver.toScheme B S hS).map (c₂ ≫ c₁)) := by
    have h₁ : Etale ((BigFppfOver.toScheme B S hS).map c₁) := hetale.property _ _ c₁ hsq₁
    have h₂ : Etale ((BigFppfOver.toScheme B S hS).map c₂) := hetale.property _ _ c₂ hsq₂
    rw [Functor.map_comp]
    infer_instance
  have key₁ : yoneda.map (c₂ ≫ yoneda.preimage α₁) ≫ f =
      yoneda.map (c₂ ≫ c₁) ≫ g ≫ (prod.fst : F ⨯ F ⟶ F) := by
    rw [Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc, hsq₁.w]
  have key₂ : yoneda.map (yoneda.preimage α₂) ≫ f =
      yoneda.map (c₂ ≫ c₁) ≫ g ≫ (prod.snd : F ⨯ F ⟶ F) := by
    rw [hsq₂.w, Functor.map_comp, Category.assoc]
  have hfac : yoneda.map (c₂ ≫ c₁) ≫ g =
      yoneda.map (prod.lift (c₂ ≫ yoneda.preimage α₁) (yoneda.preimage α₂)) ≫
        prod.lift (yoneda.map (prod.fst : U ⨯ U ⟶ U) ≫ f) (yoneda.map prod.snd ≫ f) := by
    refine prod.hom_ext ?_ ?_
    · conv_rhs => rw [Category.assoc, prod.lift_fst, ← Category.assoc, ← Functor.map_comp,
        prod.lift_fst]
      rw [Category.assoc, key₁]
    · conv_rhs => rw [Category.assoc, prod.lift_snd, ← Category.assoc, ← Functor.map_comp,
        prod.lift_snd]
      rw [Category.assoc, key₂]
  have hpb : IsPullback
      (Limits.pullback.fst (prod.lift s t)
        (prod.lift (c₂ ≫ yoneda.preimage α₁) (yoneda.preimage α₂)))
      (Limits.pullback.snd (prod.lift s t)
        (prod.lift (c₂ ≫ yoneda.preimage α₁) (yoneda.preimage α₂)))
      (prod.lift s t) (prod.lift (c₂ ≫ yoneda.preimage α₁) (yoneda.preimage α₂)) :=
    IsPullback.of_hasPullback _ _
  have hbig := (yoneda.map_isPullback hpb).paste_horiz hjSq
  rw [← hfac] at hbig
  refine hdesc (diag F) hF (isSheaf_prod_self B S hS hF) g (c₂ ≫ c₁) hcs hce _ _ hbig ?_
  exact (presheaf_yoneda_map_iff B S hS ‹Q.IsStableUnderBaseChange› _).2
    (Q.of_isPullback ((BigFppfOver.toScheme B S hS).map_isPullback hpb) hQ)

end Space

/-- **The absolute diagonal of a sheaf with a representable surjective étale atlas is
representable**, granted effective descent along the surjective étale morphisms of the site at
the monomorphisms locally of finite type. -/
theorem relativelyRepresentable_diag_of_surjective_etale_atlas
    (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F)
    {U : BigFppfOver B S hS} (f : yoneda.obj U ⟶ F)
    (hsurj : MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)) f)
    (hetale : MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)) f)
    (hdesc : Space.IsEffectiveDescentAlongSurjectiveEtale B S hS
      (MorphismProperty.monomorphisms Scheme.{u} ⊓ @LocallyOfFiniteType)) :
    yoneda.relativelyRepresentable (diag F) :=
  have _hbc : MorphismProperty.IsStableUnderBaseChange
      (MorphismProperty.monomorphisms Scheme.{u} ⊓ @LocallyOfFiniteType) := .inf
  have hj := Space.locallyOfFiniteType_and_mono_toScheme_kernelPairToProd B S hS f hetale
  (Space.presheaf_diag_of_kernelPair_of_etaleDescent B S hS _ hdesc hF
    (hetale.rep.isPullback' f) hsurj hetale ⟨hj.2, hj.1⟩).rep

/-- **Stacks 0BGQ, granted effective descent along the surjective étale morphisms of the site
at the monomorphisms locally of finite type.** A sheaf `F` on the big fppf site over `S` which has
a representable, surjective, étale morphism `f : h_U ⟶ F` from an object `U` of the site is an
algebraic space over `S`. -/
theorem isAlgebraicSpace_of_surjective_etale_atlas_of_etaleDescent
    (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F)
    (U : BigFppfOver B S hS) (f : yoneda.obj U ⟶ F)
    (hsurj : MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)) f)
    (hetale : MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)) f)
    (hdesc : Space.IsEffectiveDescentAlongSurjectiveEtale B S hS
      (MorphismProperty.monomorphisms Scheme.{u} ⊓ @LocallyOfFiniteType)) :
    IsAlgebraicSpace B S hS F where
  isSheaf := hF
  diagonal_representable :=
    relativelyRepresentable_diag_of_surjective_etale_atlas B S hS hF f hsurj hetale hdesc
  exists_atlas := ⟨U, f, hsurj, hetale⟩

/-- **Stacks 0BGR, granted effective descent along the surjective étale morphisms of the site
at the monomorphisms locally of finite type.** A sheaf `F` on the big fppf site over `S` which has
a representable, surjective, étale morphism `a : G ⟶ F` from an algebraic space `G` over `S` is
an algebraic space over `S`. Representability of `a` is part of each of `hs` and `he`. -/
theorem isAlgebraicSpace_of_relativelyRepresentable_surjective_etale_of_etaleDescent
    {G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hG : IsAlgebraicSpace B S hS G)
    (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F)
    (a : G ⟶ F)
    (hs : MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)) a)
    (he : MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)) a)
    (hdesc : Space.IsEffectiveDescentAlongSurjectiveEtale B S hS
      (MorphismProperty.monomorphisms Scheme.{u} ⊓ @LocallyOfFiniteType)) :
    IsAlgebraicSpace B S hS F := by
  obtain ⟨U, f, hfs, hfe⟩ := hG.exists_atlas
  exact isAlgebraicSpace_of_surjective_etale_atlas_of_etaleDescent B S hS hF U (f ≫ a)
    (MorphismProperty.comp_mem _ _ _ hfs hs) (MorphismProperty.comp_mem _ _ _ hfe he) hdesc

end AlgebraicGeometry

end
