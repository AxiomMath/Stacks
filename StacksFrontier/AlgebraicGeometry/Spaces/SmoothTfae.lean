module

public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Subfunctor.Image
public import Mathlib.Data.List.TFAE
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.SmoothLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartAtPointOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothMorphismProperty

/-!
# Characterizations of a smooth morphism of algebraic spaces (Stacks 03ZF)

Nine conditions on a morphism `f : X ⟶ Y` of algebraic spaces over `S` are equivalent:
smoothness in the sense of Tag 03ZC, smoothness at every point, smoothness of every
scheme-valued base change, smoothness of every *affine* scheme-valued base change, smoothness
of one surjective étale base change, smoothness of the composite with one surjective étale
chart of the source, the chart conditions (1) and (2) of Tag 03MJ for `Smooth`, and Zariski
locality on the target and on the source.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.Space.isSmooth_tfae`: **Stacks 03ZF**.

## Implementation notes

The equivalences are organised around the chart conditions. Conditions (1), (7) and (8) are
the definition of Tag 03ZC and the two chart conditions of Tag 03MJ, equivalent by Tag 03MJ
itself; (1) and (2) are the pointwise criterion of Tag 04RF, parts (2) and (3), applied with
`P = Smooth` and its étale locality from Tag 04R3; (3) and (4) are base change (Tag 03ZE) in
one direction, and in the other direction the affine base changes of an étale chart already
cover, so the chart condition can be checked on them; (5) and (6) are single-chart forms,
produced from a surjective étale presentation by Tag 02X1 and recognised by Tag 03EC; and (9)
is Tag 03BZ, the identification of Zariski coverings with coverings of the point space,
together with smoothness being preserved by restriction to an open subspace.

## References

* [Stacks Project, Tag 03ZF](https://stacks.math.columbia.edu/tag/03ZF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space


private theorem etaleOver_isMultiplicative
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).IsMultiplicative where
  id_mem U := by
    change Etale ((BigFppfOver.toScheme B S hS).map (𝟙 U))
    rw [CategoryTheory.Functor.map_id]
    infer_instance
  comp_mem f g hf hg := by
    change Etale ((BigFppfOver.toScheme B S hS).map f) at hf
    change Etale ((BigFppfOver.toScheme B S hS).map g) at hg
    change Etale ((BigFppfOver.toScheme B S hS).map (f ≫ g))
    rw [CategoryTheory.Functor.map_comp]
    exact Etale.etale_comp _ _

attribute [local instance] etaleOver_isMultiplicative

private theorem etaleOver_isStableUnderBaseChange
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).IsStableUnderBaseChange := by
  let T := BigFppfOver.toScheme B S hS
  let : PreservesLimitsOfShape WalkingCospan T := by
    apply comp_preservesLimitsOfShape
  refine ⟨?_⟩
  intro X Y Y' Z f g f' g' sq hg
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := @Etale.{u}) (sq.map T) hg

attribute [local instance] etaleOver_isStableUnderBaseChange

/-- Surjectivity of the underlying scheme morphism is stable under base change in the site. -/
private instance surjectiveOver_isStableUnderBaseChange
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).IsStableUnderBaseChange := by
  let T := BigFppfOver.toScheme B S hS
  let : PreservesLimitsOfShape WalkingCospan T := by
    apply comp_preservesLimitsOfShape
  refine ⟨?_⟩
  intro X Y Y' Z f g f' g' sq hg
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := @Surjective.{u}) (sq.map T) hg

private theorem source_chart_gives_surjective_etale_chart
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (U : BigFppfOver B S hS) (p : yoneda.obj U ⟶ X)
    (hpSurj : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf p)
    (hpEtale : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf p)
    (hf : IsSmooth B S hS (p ≫ f)) :
    HoldsOnSurjectiveEtaleChart B S hS
      (@Smooth.{u} : MorphismProperty Scheme.{u}) f := by
  let T := BigFppfOver.toScheme B S hS
  let QSurj := MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u}) T
  let QEtale := MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u}) T
  let : QEtale.presheaf.IsStableUnderComposition :=
    MorphismProperty.relative_isStableUnderComposition QEtale
  let : QSurj.presheaf.IsStableUnderComposition :=
    MorphismProperty.relative_isStableUnderComposition QSurj
  obtain ⟨V, q, hqSurj, hqEtale⟩ := hY.exists_atlas
  obtain ⟨W, α, β, hpb⟩ := hqEtale.1 (p ≫ f)
  have hαEtale : QEtale.presheaf (yoneda.map α) :=
    MorphismProperty.relative_map (F := yoneda) (hqEtale.2 (p ≫ f) β α hpb)
  have hαSurj : QSurj.presheaf (yoneda.map α) :=
    MorphismProperty.relative_map (F := yoneda) (hqSurj.2 (p ≫ f) β α hpb)
  have hsourceEtale : QEtale.presheaf (yoneda.map α ≫ p) :=
    MorphismProperty.comp_mem QEtale.presheaf _ _ hαEtale hpEtale
  have hsourceSurj : QSurj.presheaf (yoneda.map α ≫ p) :=
    MorphismProperty.comp_mem QSurj.presheaf _ _ hαSurj hpSurj
  have hmapSmooth : Smooth (T.map (yoneda.preimage β)) := by
    apply hf W V (yoneda.map α) q (yoneda.preimage β) hαEtale hqEtale
    simpa only [yoneda.map_preimage, Category.assoc] using hpb.w
  refine ⟨W, V, yoneda.map α ≫ p, q, yoneda.preimage β, hsourceEtale, hqEtale,
    hsourceSurj, ?_, hmapSmooth⟩
  simpa only [yoneda.map_preimage, Category.assoc] using hpb.w

/-- Being an algebraic space is invariant under isomorphism of presheaves. -/
public alias algebraicSpace_of_iso := isAlgebraicSpace_of_iso

private theorem top_openSubspace
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) :
    IsOpenSubspace B S hS (⊤ : Subfunctor F) := by
  let topSub : Subfunctor F := ⊤
  let topIso : topSub.toFunctor ≅ F :=
    { hom := topSub.ι
      inv := Subfunctor.lift (𝟙 F) (by intro T x hx; simp [topSub])
      hom_inv_id := by ext T x; rfl
      inv_hom_id := by ext T x; rfl }
  refine ⟨algebraicSpace_of_iso B S hS topIso.symm hF, ?_⟩
  let Q := MorphismProperty.presheaf
    (MorphismProperty.inverseImage (@AlgebraicGeometry.IsOpenImmersion.{u} :
      MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))
  let : Q.IsMultiplicative := inferInstance
  let : Q.RespectsIso := inferInstance
  exact MorphismProperty.RespectsIso.postcomp Q topSub.ι
    (𝟙 topSub.toFunctor) (Q.id_mem _)

private theorem top_singleton_zariskiCover
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) :
    IsZariskiCover B S hS PUnit (fun _ => (⊤ : Subfunctor F)) := by
  refine ⟨fun _ => top_openSubspace B S hS hF, ?_⟩
  apply Presheaf.isLocallySurjective_of_surjective
  intro T x
  refine ⟨(Sigma.ι (fun _ : PUnit => (⊤ : Subfunctor F).toFunctor) PUnit.unit).app T
    ⟨x, trivial⟩, ?_⟩
  change (((Sigma.ι (fun _ : PUnit => (⊤ : Subfunctor F).toFunctor) PUnit.unit) ≫
    Sigma.desc (fun _ : PUnit => (⊤ : Subfunctor F).ι)).app T) ⟨x, trivial⟩ = x
  rw [Sigma.ι_comp_desc]
  rfl

private theorem open_immersion_presheaf_etale
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (e : F ⟶ G)
    (he : IsOpenImmersion B S hS e) :
    (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf e := by
  let T := BigFppfOver.toScheme B S hS
  let QOpen := MorphismProperty.presheaf
    (MorphismProperty.inverseImage (@AlgebraicGeometry.IsOpenImmersion.{u} :
      MorphismProperty Scheme.{u}) T)
  change QOpen e at he
  change yoneda.relativelyRepresentable e ∧
    (∀ ⦃A C⦄ (g : yoneda.obj A ⟶ G) (fst : yoneda.obj C ⟶ F)
      (snd : C ⟶ A), IsPullback fst (yoneda.map snd) e g → Etale (T.map snd))
  refine ⟨he.1, ?_⟩
  intro A C g fst snd sq
  have : AlgebraicGeometry.IsOpenImmersion (T.map snd) := he.2 g fst snd sq
  infer_instance

private theorem smooth_implies_smooth_on_top_opens
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hf : IsSmooth B S hS f) :
    ∃ (I : Type u) (V : I → Subfunctor Y),
      IsZariskiCover B S hS I V ∧
      ∀ i, ∃ (J : Type u)
        (U : J → Subfunctor (pullback f (V i).ι)),
        IsZariskiCover B S hS J U ∧
        ∀ j, IsSmooth B S hS
          ((U j).ι ≫ pullback.snd f (V i).ι) := by
  let topY : Subfunctor Y := ⊤
  let pb := pullback f topY.ι
  let topPB : Subfunctor pb := ⊤
  have hpb : IsAlgebraicSpace B S hS pb :=
    AlgebraicGeometry.isAlgebraicSpace_pullback B S hS f topY.ι hX
      (top_openSubspace B S hS hY).1 hY
  refine ⟨PUnit, (fun _ => topY), ?_, ?_⟩
  · exact top_singleton_zariskiCover B S hS hY
  · intro i
    refine ⟨PUnit, (fun _ => topPB), ?_, ?_⟩
    · exact top_singleton_zariskiCover B S hS hpb
    · intro j
      change IsSmooth B S hS (topPB.ι ≫ pullback.snd f topY.ι)
      change HoldsOnEveryEtaleChart B S hS
        (@Smooth.{u} : MorphismProperty Scheme.{u})
        (topPB.ι ≫ pullback.snd f topY.ι)
      intro U V a b h ha hb hab
      let T := BigFppfOver.toScheme B S hS
      let QEtale := MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u}) T
      let : MorphismProperty.IsStableUnderComposition
          (@Etale.{u} : MorphismProperty Scheme.{u}) := etale_isStableUnderComposition
      let : QEtale.IsStableUnderComposition :=
        MorphismProperty.IsStableUnderComposition.inverseImage (F := T)
      let : QEtale.presheaf.IsStableUnderComposition :=
        MorphismProperty.relative_isStableUnderComposition QEtale
      let a' := a ≫ topPB.ι ≫ pullback.fst f topY.ι
      let b' := b ≫ topY.ι
      have htopPB : QEtale.presheaf topPB.ι :=
        open_immersion_presheaf_etale B S hS topPB.ι
          (top_openSubspace B S hS hpb).2
      have htopY : QEtale.presheaf topY.ι :=
        open_immersion_presheaf_etale B S hS topY.ι
          (top_openSubspace B S hS hY).2
      have hfst : QEtale.presheaf (pullback.fst f topY.ι) := by
        let topIso : topY.toFunctor ≅ Y :=
          { hom := topY.ι
            inv := Subfunctor.lift (𝟙 Y) (by intro Z y hy; simp [topY])
            hom_inv_id := by ext Z y; rfl
            inv_hom_id := by ext Z y; rfl }
        have : IsIso topY.ι :=
          ⟨topIso.inv, topIso.hom_inv_id, topIso.inv_hom_id⟩
        have : IsIso (pullback.fst f topY.ι) := by infer_instance
        refine ⟨Functor.relativelyRepresentable.of_isIso yoneda _, ?_⟩
        intro A C g fst snd sq
        have : IsIso (yoneda.map snd) := sq.isIso_snd_of_isIso
        have : IsIso snd := Yoneda.fullyFaithful.isIso_of_isIso_map _
        have : IsIso (T.map snd) := by infer_instance
        let : MorphismProperty.IsMultiplicative
            (@Etale.{u} : MorphismProperty Scheme.{u}) :=
          HasRingHomProperty.isMultiplicative RingHom.Etale.stableUnderComposition
            RingHom.Etale.containsIdentities
        let : MorphismProperty.ContainsIdentities
            (@Etale.{u} : MorphismProperty Scheme.{u}) :=
          (inferInstance : MorphismProperty.IsMultiplicative
            (@Etale.{u} : MorphismProperty Scheme.{u})).toContainsIdentities
        let : MorphismProperty.RespectsIso
            (@Etale.{u} : MorphismProperty Scheme.{u}) :=
          MorphismProperty.IsStableUnderBaseChange.respectsIso
        exact MorphismProperty.isomorphisms_le_of_containsIdentities (@Etale.{u})
          (T.map snd) inferInstance
      have ha' : QEtale.presheaf a' := by
        dsimp [a']
        exact MorphismProperty.comp_mem QEtale.presheaf _ _ ha
          (MorphismProperty.comp_mem QEtale.presheaf _ _ htopPB hfst)
      have hb' : QEtale.presheaf b' := by
        dsimp [b']
        exact MorphismProperty.comp_mem QEtale.presheaf _ _ hb htopY
      have hab' : yoneda.map h ≫ b' = a' ≫ f := by
        dsimp [a', b']
        calc
          yoneda.map h ≫ b ≫ topY.ι = (yoneda.map h ≫ b) ≫ topY.ι := by simp
          _ = (a ≫ topPB.ι ≫ pullback.snd f topY.ι) ≫ topY.ι := by rw [hab]
          _ = a ≫ topPB.ι ≫ pullback.fst f topY.ι ≫ f := by
            rw [Category.assoc, Category.assoc, pullback.condition]
      exact hf U V a' b' h ha' hb' hab'

theorem isSmooth_precomp_iso
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (e : F ≅ G) (f : G ⟶ H) (hf : IsSmooth B S hS f) :
    IsSmooth B S hS (e.hom ≫ f) := by
  intro U V a b h ha hb hw
  exact hf U V (a ≫ e.hom) b h
    (MorphismProperty.RespectsIso.postcomp _ e.hom a ha) hb
    (by simpa only [Category.assoc] using hw)

private theorem isSmoothAt_of_openImmersion
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F)
    (q : F ⟶ X) [Mono q] (hq : IsOpenImmersion B S hS q)
    (f : X ⟶ Y) (hf : IsSmooth B S hS (q ≫ f))
    (x : points B S hS F) :
    IsSmoothAt B S hS f (pointsMap B S hS F q x) := by
  let e := asIso (Subfunctor.toRange q)
  have he : e.inv ≫ q = (Subfunctor.range q).ι :=
    e.inv_comp_eq.2 (Subfunctor.toRange_ι q).symm
  refine ⟨Subfunctor.range q, ⟨algebraicSpace_of_iso B S hS e hF, ?_⟩,
    pointsMap B S hS F e.hom x, ?_, ?_⟩
  · rw [← he]
    exact MorphismProperty.RespectsIso.precomp _ e.inv q hq
  · rw [← pointsMap_comp_apply]
    rfl
  · rw [← he, Category.assoc]
    exact isSmooth_precomp_iso B S hS e.symm (q ≫ f) hf

/-- Smoothness is checked on every étale chart iff it is checked on one surjective étale chart. -/
private theorem isSmooth_iff_holdsOnSurjectiveEtaleChart
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) :
    IsSmooth B S hS f ↔
      HoldsOnSurjectiveEtaleChart B S hS (@Smooth.{u} : MorphismProperty Scheme.{u}) f := by
  simpa [IsSmooth] using
    (holdsOnEveryEtaleChart_iff_surjectiveChart
      (B := B) (S := S) (hS := hS)
      (P := (@Smooth.{u} : MorphismProperty Scheme.{u}))
      (hP := AlgebraicGeometry.Smooth.isEtaleLocalOnSourceAndTarget)
      (hF := hX) (hG := hY) (f := f))

private theorem isSmooth_of_zariskiCovers
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (I : Type u) (V : I → Subfunctor Y)
    (hV : IsZariskiCover B S hS I V)
    (hU : ∀ i, ∃ (J : Type u) (U : J → Subfunctor (pullback f (V i).ι)),
      IsZariskiCover B S hS J U ∧
      ∀ j, IsSmooth B S hS ((U j).ι ≫ pullback.snd f (V i).ι)) :
    IsSmooth B S hS f := by
  apply (holdsOnEveryEtaleChart_iff_forall_atPoint B S hS _
    AlgebraicGeometry.Smooth.isEtaleLocalOnSourceAndTarget hX hY f).2
  intro x
  apply (holdsOnEveryEtaleChartAtPoint_iff_exists_open B S hS _
    AlgebraicGeometry.Smooth.isEtaleLocalOnSourceAndTarget hX hY f x).2
  have hvcover := (isZariskiCover_iff_iUnion_points
    B S hS Y hY I V hV.1).1 hV
  have hxmem : pointsMap B S hS X f x ∈
      ⋃ i, Set.range (pointsMap B S hS (V i).toFunctor (V i).ι) := by
    rw [hvcover]
    trivial
  obtain ⟨i, v, hv⟩ := Set.mem_iUnion.mp hxmem
  let Xsp : AlgebraicSpaces B S hS := ⟨X, hX⟩
  let Ysp : AlgebraicSpaces B S hS := ⟨Y, hY⟩
  let Vsp : AlgebraicSpaces B S hS := ⟨(V i).toFunctor, (hV.1 i).1⟩
  let fsp : Xsp ⟶ Ysp := ObjectProperty.homMk f
  let vsp : Vsp ⟶ Ysp := ObjectProperty.homMk (V i).ι
  have sq := AlgebraicSpaces.isPullback_fiberProduct B S hS fsp vsp
  obtain ⟨w, hwx, hwv⟩ := exists_point_of_isPullback B S hS sq x v hv.symm
  have hP := AlgebraicGeometry.isAlgebraicSpace_pullback B S hS f (V i).ι hX (hV.1 i).1 hY
  obtain ⟨J, U, hUc, hUs⟩ := hU i
  have hucover := (isZariskiCover_iff_iUnion_points
    B S hS _ hP J U hUc.1).1 hUc
  have hwmem : w ∈ ⋃ j, Set.range (pointsMap B S hS (U j).toFunctor (U j).ι) := by
    rw [hucover]
    trivial
  obtain ⟨j, u, hu⟩ := Set.mem_iUnion.mp hwmem
  have hfst : IsOpenImmersion B S hS (pullback.fst f (V i).ι) :=
    isOpenImmersion_of_isPullback B S hS sq.flip (hV.1 i).2
  have hq : IsOpenImmersion B S hS ((U j).ι ≫ pullback.fst f (V i).ι) :=
    MorphismProperty.comp_mem _ _ _ (hUc.1 j).2 hfst
  have hvEt : IsEtale B S hS (V i).ι := by
    intro T a ha
    exact MorphismProperty.comp_mem _ _ _ ha
      (open_immersion_presheaf_etale B S hS (V i).ι (hV.1 i).2)
  have hs := isSmooth_comp B S hS (hUc.1 j).1 (hV.1 i).1 hY
    ((U j).ι ≫ pullback.snd f (V i).ι) (V i).ι (hUs j)
    (isSmooth_of_isEtale B S hS hY hvEt)
  have hs' : IsSmooth B S hS (((U j).ι ≫ pullback.fst f (V i).ι) ≫ f) := by
    simpa only [Category.assoc, pullback.condition] using hs
  have hpt := isSmoothAt_of_openImmersion B S hS (hUc.1 j).1 _ hq f hs' u
  have hux : pointsMap B S hS (U j).toFunctor
      ((U j).ι ≫ pullback.fst f (V i).ι) u = x := by
    rw [pointsMap_comp_apply, hu]
    exact hwx
  rw [hux] at hpt
  obtain ⟨W, hW, z, hz, hsW⟩ := hpt
  exact ⟨W, hW, ⟨z, hz⟩, hsW⟩

private theorem etale_presheaf_of_comp
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F)
    (_hG : IsAlgebraicSpace B S hS G)
    (U : BigFppfOver B S hS) (a : yoneda.obj U ⟶ F) (q : F ⟶ G)
    (hq : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf q)
    (haq : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (a ≫ q)) :
    (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a := by
  let T := BigFppfOver.toScheme B S hS
  let Q := (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u}) T).presheaf
  obtain ⟨V, b, hbSurj, hbEtale⟩ := hF.exists_atlas
  obtain ⟨W, c, h, hw, hcSurj, hcEtale⟩ :=
    exists_surjective_etale_presentation_lift B S hS
      (isAlgebraicSpace_yoneda B S hS U) hF a V b hbSurj hbEtale
  have hcq : Q (c ≫ (a ≫ q)) := MorphismProperty.comp_mem Q _ _ hcEtale haq
  have hbq : Q (b ≫ q) := MorphismProperty.comp_mem Q _ _ hbEtale hq
  have hh : Etale (T.map h) := etale_of_etale_charts
    B S hS (c ≫ (a ≫ q)) (b ≫ q) hcq hbq h (by
      simpa only [Category.assoc] using congrArg (fun t => t ≫ q) hw.symm)
  have ha : IsEtale B S hS a :=
    (isEtale_iff_exists_etale_chart_square B S hS
      (isAlgebraicSpace_yoneda B S hS U) hF a).2
      ⟨W, V, c, b, h, hw, hcSurj, hcEtale, hbEtale, hh⟩
  simpa using ha U (𝟙 _) (MorphismProperty.id_mem Q _)

private theorem isSmooth_of_affine_baseChange
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hf : ∀ (Z : BigFppfOver B S hS) (g : yoneda.obj Z ⟶ Y),
      IsAffine ((BigFppfOver.toScheme B S hS).obj Z) →
        IsSmooth B S hS (pullback.snd f g)) :
    IsSmooth B S hS f := by
  let T := BigFppfOver.toScheme B S hS
  let Q := (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u}) T).presheaf
  let : PreservesLimitsOfShape WalkingCospan T := by
    apply comp_preservesLimitsOfShape
  intro U V a b h ha hb hw
  let : IsZariskiLocalAtTarget (@Smooth.{u} : MorphismProperty Scheme.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtTarget (P := @Smooth)
  apply IsZariskiLocalAtTarget.of_openCover (P := @Smooth) (T.obj V).affineCover
  intro i
  let Z₀ := (T.obj V).affineCover.X i
  let g₀ := (T.obj V).affineCover.f i
  have hZ₀ : B.Contains Z₀ := Scheme.size_lt_of_isOpenImmersion g₀ V.left.property
  let Z : BigFppfOver B S hS :=
    Over.mk (⟨g₀ ≫ V.hom.hom⟩ : B.obj hZ₀ ⟶ B.obj hS)
  let g : Z ⟶ V := Over.homMk (ObjectProperty.homMk g₀) rfl
  let W := pullback h g
  let c : W ⟶ U := pullback.fst h g
  let k : W ⟶ Z := pullback.snd h g
  have hg : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u}) T) g := by
    change Etale g₀
    infer_instance
  have hbc : Q (yoneda.map g ≫ b) :=
    MorphismProperty.comp_mem Q _ _ (MorphismProperty.relative_map (F := yoneda) hg) hb
  have hc : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u}) T) c :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := @Etale.{u}) ((IsPullback.of_hasPullback h g).flip.map T) hg
  have hca : Q (yoneda.map c ≫ a) := MorphismProperty.comp_mem Q _ _
    (MorphismProperty.relative_map (F := yoneda) hc) ha
  let d := yoneda.map g ≫ b
  have hcomm : (yoneda.map c ≫ a) ≫ f = yoneda.map k ≫ d := by
    dsimp [d, c, k]
    simp only [Category.assoc, ← hw, ← yoneda.map_comp_assoc, pullback.condition]
  let l : yoneda.obj W ⟶ pullback f d := pullback.lift (yoneda.map c ≫ a) (yoneda.map k) hcomm
  have hP := AlgebraicGeometry.isAlgebraicSpace_pullback B S hS f d hX
    (isAlgebraicSpace_yoneda B S hS Z) hY
  have hfst : Q (pullback.fst f d) :=
    (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback
      (IsPullback.of_hasPullback f d).flip hbc
  have hl : Q l := etale_presheaf_of_comp B S hS hP hX W l (pullback.fst f d)
    hfst (by simpa only [l, pullback.lift_fst] using hca)
  have hsm : Smooth (T.map k) := hf Z d (Scheme.isAffine_affineCover (T.obj V) i) W Z l (𝟙 _) k hl
    (MorphismProperty.id_mem Q _) (by simp only [Category.comp_id, l, pullback.lift_snd])
  have sq : IsPullback (T.map c) (T.map k) (T.map h) g₀ :=
    (IsPullback.of_hasPullback h g).map T
  change Smooth (pullback.snd (T.map h) g₀)
  rw [← sq.isoPullback_inv_snd]
  let : MorphismProperty.RespectsIso (@Smooth.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  exact MorphismProperty.RespectsIso.precomp (@Smooth) sq.isoPullback.inv (T.map k) hsm


/-- The pointwise, scheme-local, étale-local, and Zariski-local criteria for
smoothness of a morphism of algebraic spaces. -/
@[stacks 03ZF]
theorem isSmooth_tfae
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) :
    List.TFAE [
      IsSmooth B S hS f,
      (∀ x : points B S hS X, IsSmoothAt B S hS f x),
      (∀ (Z : BigFppfOver B S hS) (g : yoneda.obj Z ⟶ Y),
        IsSmooth B S hS (pullback.snd f g)),
      (∀ (Z : BigFppfOver B S hS) (g : yoneda.obj Z ⟶ Y),
        IsAffine ((BigFppfOver.toScheme B S hS).obj Z) →
          IsSmooth B S hS (pullback.snd f g)),
      (∃ (V : BigFppfOver B S hS) (g : yoneda.obj V ⟶ Y),
        (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS)).presheaf g ∧
        (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS)).presheaf g ∧
        IsSmooth B S hS (pullback.snd f g)),
      (∃ (U : BigFppfOver B S hS) (p : yoneda.obj U ⟶ X),
        (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS)).presheaf p ∧
        (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS)).presheaf p ∧
        IsSmooth B S hS (p ≫ f)),
      HoldsOnEveryEtaleChart B S hS
        (@Smooth.{u} : MorphismProperty Scheme.{u}) f,
      HoldsOnSurjectiveEtaleChart B S hS
        (@Smooth.{u} : MorphismProperty Scheme.{u}) f,
      (∃ (I : Type u) (V : I → Subfunctor Y),
        IsZariskiCover B S hS I V ∧
        ∀ i, ∃ (J : Type u)
          (U : J → Subfunctor (pullback f (V i).ι)),
          IsZariskiCover B S hS J U ∧
          ∀ j, IsSmooth B S hS
            ((U j).ι ≫ pullback.snd f (V i).ι))
    ] := by
  tfae_have 1 ↔ 7 := Iff.rfl
  tfae_have 1 ↔ 2 := by
    change HoldsOnEveryEtaleChart B S hS (@Smooth.{u}) f ↔ _
    rw [holdsOnEveryEtaleChart_iff_forall_atPoint B S hS _
      AlgebraicGeometry.Smooth.isEtaleLocalOnSourceAndTarget hX hY f]
    refine forall_congr' fun x => ?_
    rw [holdsOnEveryEtaleChartAtPoint_iff_exists_open B S hS _
      AlgebraicGeometry.Smooth.isEtaleLocalOnSourceAndTarget hX hY f x]
    exact ⟨fun ⟨U, hU, ⟨x', hx'⟩, hf⟩ => ⟨U, hU, x', hx', hf⟩,
      fun ⟨U, hU, x', hx', hf⟩ => ⟨U, hU, ⟨x', hx'⟩, hf⟩⟩
  tfae_have 3 → 5 := by
    intro h
    obtain ⟨V, g, hgSurj, hgEtale⟩ := hY.exists_atlas
    exact ⟨V, g, hgSurj, hgEtale, h V g⟩
  tfae_have 1 → 3 := by
    intro hf Z g
    let Xsp : AlgebraicSpaces B S hS := ⟨X, hX⟩
    let Ysp : AlgebraicSpaces B S hS := ⟨Y, hY⟩
    let Zsp : AlgebraicSpaces B S hS :=
      ⟨yoneda.obj Z, isAlgebraicSpace_yoneda B S hS Z⟩
    let fsp : Xsp ⟶ Ysp := ObjectProperty.homMk f
    let gsp : Zsp ⟶ Ysp := ObjectProperty.homMk g
    exact (isSmooth_isStableUnderBaseChange B S hS).of_isPullback
      (AlgebraicSpaces.isPullback_fiberProduct B S hS fsp gsp) hf
  tfae_have 3 → 4 := fun h Z g _ => h Z g
  tfae_have 7 ↔ 8 := isSmooth_iff_holdsOnSurjectiveEtaleChart B S hS hX hY f
  tfae_have 5 → 6 := by
    rintro ⟨V, g, hgSurj, hgEtale, hSmooth⟩
    let P := pullback f g
    have hP : IsAlgebraicSpace B S hS P :=
      AlgebraicGeometry.isAlgebraicSpace_pullback B S hS f g hX
        (isAlgebraicSpace_yoneda B S hS V) hY
    obtain ⟨U, a, haSurj, haEtale⟩ := hP.exists_atlas
    let T := BigFppfOver.toScheme B S hS
    let QSurj := MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u}) T
    let QEtale := MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u}) T
    let : QEtale.presheaf.IsStableUnderComposition :=
      MorphismProperty.relative_isStableUnderComposition QEtale
    let : QSurj.presheaf.IsStableUnderComposition :=
      MorphismProperty.relative_isStableUnderComposition QSurj
    have hpull : IsPullback (pullback.snd f g) (pullback.fst f g) g f :=
      (IsPullback.of_hasPullback f g).flip
    have hfstEtale : QEtale.presheaf (pullback.fst f g) :=
      (MorphismProperty.relative_isStableUnderBaseChange QEtale).of_isPullback hpull hgEtale
    have hfstSurj : QSurj.presheaf (pullback.fst f g) :=
      (MorphismProperty.relative_isStableUnderBaseChange QSurj).of_isPullback hpull hgSurj
    have hpEtale : QEtale.presheaf (a ≫ pullback.fst f g) :=
      MorphismProperty.comp_mem QEtale.presheaf _ _ haEtale hfstEtale
    have hpSurj : QSurj.presheaf (a ≫ pullback.fst f g) :=
      MorphismProperty.comp_mem QSurj.presheaf _ _ haSurj hfstSurj
    let : QEtale.presheaf.IsMultiplicative :=
      MorphismProperty.relative_isMultiplicative QEtale
    let : QSurj.IsMultiplicative :=
      MorphismProperty.IsMultiplicative.instInverseImage (P := @Surjective.{u}) T
    let : QSurj.presheaf.IsMultiplicative :=
      MorphismProperty.relative_isMultiplicative QSurj
    have hidEtale : QEtale.presheaf (𝟙 (yoneda.obj V)) := QEtale.presheaf.id_mem _
    have hidEtaleU : QEtale.presheaf (𝟙 (yoneda.obj U)) := QEtale.presheaf.id_mem _
    have hidSurj : QSurj.presheaf (𝟙 (yoneda.obj U)) := QSurj.presheaf.id_mem _
    let p : yoneda.obj U ⟶ X := a ≫ pullback.fst f g
    let h := yoneda.preimage (a ≫ pullback.snd f g)
    have hmapSmooth : Smooth (T.map h) := by
      apply hSmooth U V a (𝟙 (yoneda.obj V)) h haEtale hidEtale
      simp [h]
    have hcomm : yoneda.map h ≫ g = p ≫ f := by
      dsimp [h]
      rw [yoneda.map_preimage]
      dsimp [p]
      simp [Category.assoc, pullback.condition]
    have hsurj : HoldsOnSurjectiveEtaleChart B S hS
        (@Smooth.{u} : MorphismProperty Scheme.{u})
        (p ≫ f) := by
      exact ⟨U, V, 𝟙 (yoneda.obj U), g, h, hidEtaleU, hgEtale, hidSurj,
        hcomm, hmapSmooth⟩
    have hpSmooth : IsSmooth B S hS (p ≫ f) :=
      (isSmooth_iff_holdsOnSurjectiveEtaleChart B S hS (isAlgebraicSpace_yoneda B S hS U) hY _).2
        hsurj
    exact ⟨U, p, hpSurj, hpEtale, hpSmooth⟩
  tfae_have 6 → 8 := by
    rintro ⟨U, p, hpSurj, hpEtale, hpSmooth⟩
    exact source_chart_gives_surjective_etale_chart B S hS hY f U p hpSurj hpEtale hpSmooth
  tfae_have 8 → 9 := fun h8 => smooth_implies_smooth_on_top_opens B S hS hX hY f
    ((isSmooth_iff_holdsOnSurjectiveEtaleChart B S hS hX hY f).2 h8)
  tfae_have 9 → 1 := fun ⟨I, V, hV, hU⟩ => isSmooth_of_zariskiCovers B S hS hX hY f I V hV hU
  tfae_have 4 → 1 := isSmooth_of_affine_baseChange B S hS hX hY f
  tfae_finish

end AlgebraicGeometry.Space

end
