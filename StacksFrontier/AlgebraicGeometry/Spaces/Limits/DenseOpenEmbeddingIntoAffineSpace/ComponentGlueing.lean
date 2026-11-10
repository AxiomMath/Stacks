module

public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DenseOpenEmbeddingIntoAffineSpace.ComponentImmersions
import all StacksFrontier.AlgebraicGeometry.Spaces.Limits.DenseOpenEmbeddingIntoAffineSpace.ComponentImmersions

/-!
# Glueing the component-wise immersions

The disjoint opens produced for the irreducible components of `Y` glue to a single affine-open
union `W ⟶ Y`, a coproduct of schemes; the immersions of the pieces into affine spaces assemble
to an immersion of `W` into a coproduct of affine spaces, which is then composed with an
immersion of that coproduct into a single affine space.  This proves Stacks 088N,
`AlgebraicGeometry.Space.exists_denseOpen_isImmersion_affineSpaceOver`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Opposite TopologicalSpace TopCat

universe u v

namespace AlgebraicGeometry.Space

attribute [local instance]
  AlgebraicGeometry.Space.preservesLimitsOfShape_walkingCospan_toScheme

set_option synthInstance.maxHeartbeats 400000 in
-- `inferInstance` for `HasPullbacks` of presheaves on the big fppf site is a deep search
/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance hasPullbacks_presheaf_ComponentGlueing
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    HasPullbacks ((AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

local instance (priority := high) hasPullback_presheaf_ComponentGlueing
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y Z : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-- The preimage of a base-change-stable property of schemes under `toScheme` is stable under
base change. -/
private instance inverseImage_toScheme_isStableUnderBaseChange
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange] :
    (P.inverseImage (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).IsStableUnderBaseChange :=
  ⟨by
    intro _ _ _ _ _ _ _ _ h hf
    exact MorphismProperty.of_isPullback (P := P)
      (h.map (AlgebraicGeometry.BigFppfOver.toScheme B S hS)) hf⟩

private theorem exists_factor_through_schematicLocus
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Y : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (A : AlgebraicGeometry.BigFppfOver B S hS) (j : yoneda.obj A ⟶ Y)
    (hj : AlgebraicGeometry.Space.IsOpenImmersion B S hS j) :
    ∃ k : yoneda.obj A ⟶ (AlgebraicGeometry.Space.schematicLocus B S hS Y).toFunctor,
      k ≫ (AlgebraicGeometry.Space.schematicLocus B S hS Y).ι = j := by
  let := AlgebraicGeometry.Space.mono_of_isOpenImmersion B S hS j hj
  let G := Subfunctor.range j
  let e : yoneda.obj A ≅ G.toFunctor := asIso (Subfunctor.toRange j)
  have hG : AlgebraicGeometry.Space.IsOpenSubspace B S hS G :=
    isOpenSubspace_range_of_open B S hS j (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS A) hj
  have hGrep : G.toFunctor.IsRepresentable :=
    ⟨A, ⟨(Functor.RepresentableBy.yoneda A).ofIso e⟩⟩
  have hle := AlgebraicGeometry.Space.le_schematicLocus B S hS Y G hG hGrep
  refine ⟨e.hom ≫ Subfunctor.homOfLe hle, ?_⟩
  simpa only [Category.assoc, Subfunctor.homOfLe_ι, e, G, asIso_hom] using Subfunctor.toRange_ι j

private theorem exists_common_scheme_of_openImmersions
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Y : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY : AlgebraicGeometry.IsAlgebraicSpace B S hS Y) {I : Type*}
    (A : I → AlgebraicGeometry.BigFppfOver B S hS) (j : ∀ c, yoneda.obj (A c) ⟶ Y)
    (hj : ∀ c, AlgebraicGeometry.Space.IsOpenImmersion B S hS (j c)) :
    ∃ (T : AlgebraicGeometry.BigFppfOver B S hS) (t : yoneda.obj T ⟶ Y)
      (k : ∀ c, A c ⟶ T),
      AlgebraicGeometry.Space.IsOpenImmersion B S hS t ∧
      (∀ c, _root_.AlgebraicGeometry.IsOpenImmersion
        ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (k c))) ∧
      (∀ c, yoneda.map (k c) ≫ t = j c) := by
  let L := AlgebraicGeometry.Space.schematicLocus B S hS Y
  let :=
    (isOpenSubspace_and_isRepresentable_schematicLocus_of_isAlgebraicSpace B S hS hY).2
  let T := L.toFunctor.reprX
  let e : yoneda.obj T ≅ L.toFunctor := L.toFunctor.reprW
  let t := e.hom ≫ L.ι
  choose l hl using fun c => exists_factor_through_schematicLocus B S hS (A c) (j c) (hj c)
  let k := fun c => yoneda.preimage (l c ≫ e.inv)
  have ht : AlgebraicGeometry.Space.IsOpenImmersion B S hS t :=
    MorphismProperty.RespectsIso.precomp _ e.hom L.ι
      (isOpenSubspace_and_isRepresentable_schematicLocus_of_isAlgebraicSpace
        B S hS hY).1.2
  have hk : ∀ c, yoneda.map (k c) ≫ t = j c := by
    intro c
    simp only [k, Functor.map_preimage, t, Category.assoc, Iso.inv_hom_id_assoc]
    exact hl c
  refine ⟨T, t, k, ht, ?_, hk⟩
  intro c
  let Q := MorphismProperty.inverseImage (@AlgebraicGeometry.IsOpenImmersion.{u})
    (AlgebraicGeometry.BigFppfOver.toScheme B S hS)
  have hkt : Q.presheaf (yoneda.map (k c) ≫ t) := (hk c).symm ▸ hj c
  have hmono : Mono t := AlgebraicGeometry.Space.mono_of_isOpenImmersion B S hS t ht
  have sq : IsPullback (yoneda.map (k c)) (𝟙 _) t (yoneda.map (k c) ≫ t) :=
    IsPullback.of_vert_isIso_mono ⟨by simp⟩
  have hkp : Q.presheaf (yoneda.map (k c)) :=
    (MorphismProperty.relative_isStableUnderBaseChange Q).of_isPullback sq.flip hkt
  exact MorphismProperty.of_relative_map (P := Q) hkp


private theorem exists_fieldPoint_of_schemePoint
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (U : AlgebraicGeometry.BigFppfOver B S hS)
    (x : (AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj U) :
    ∃ p : AlgebraicGeometry.Space.FieldValuedPoint B S hS (yoneda.obj U),
      AlgebraicGeometry.Space.schemePoint B S hS U p = x := by
  let X := (AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj U
  let hK := B.residueField_spec_contains U.left.property x
  let f : B.obj hK ⟶ U.left := ObjectProperty.homMk (X.fromSpecResidueField x)
  let p : AlgebraicGeometry.Space.FieldValuedPoint B S hS (yoneda.obj U) :=
    ⟨X.residueField x, hK, (f ≫ U.hom).hom, Over.homMk f⟩
  exact ⟨p, Scheme.fromSpecResidueField_apply x _⟩

private theorem disjoint_scheme_ranges_of_disjoint_pointsMap_ranges
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Y : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {A D T : AlgebraicGeometry.BigFppfOver B S hS} (k : A ⟶ T) (l : D ⟶ T)
    (t : yoneda.obj T ⟶ Y)
    (hk : _root_.AlgebraicGeometry.IsOpenImmersion
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map k))
    (hl : _root_.AlgebraicGeometry.IsOpenImmersion
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map l))
    (hd : Disjoint
      (Set.range (AlgebraicGeometry.Space.pointsMap B S hS (yoneda.obj A) (yoneda.map k ≫ t)))
      (Set.range (AlgebraicGeometry.Space.pointsMap B S hS (yoneda.obj D) (yoneda.map l ≫ t)))) :
    Disjoint (Set.range ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map k))
      (Set.range ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map l)) := by
  refine Set.disjoint_left.mpr fun z hz hz' => ?_
  obtain ⟨p, hp⟩ := exists_fieldPoint_of_schemePoint B S hS T z
  obtain ⟨a, ha⟩ := point_lift_of_schemePoint_mem_range B S hS k hk p (hp ▸ hz)
  obtain ⟨d, hd'⟩ := point_lift_of_schemePoint_mem_range B S hS l hl p (hp ▸ hz')
  apply Set.disjoint_left.mp hd
  · exact ⟨a, (pointsMap_comp_point B S hS (yoneda.map k) t a).trans
      (congrArg (AlgebraicGeometry.Space.pointsMap B S hS (yoneda.obj T) t) ha)⟩
  · exact ⟨d, (pointsMap_comp_point B S hS (yoneda.map l) t d).trans
      (congrArg (AlgebraicGeometry.Space.pointsMap B S hS (yoneda.obj T) t) hd')⟩

/-- A coproduct of finitely many schemes of the site `B` lies in the site. -/
private theorem contains_sigma (B : AlgebraicGeometry.BigFppfSite.{u}) {I : Type*} [Finite I]
    (F : I → Scheme.{u}) (hF : ∀ c, B.Contains (F c)) : B.Contains (∐ F) := by
  classical
  let : Small.{u} I := inferInstance
  let e := Sigma.whiskerEquiv (f := fun c : Shrink.{u} I => F ((equivShrink I).symm c))
    (g := F) (equivShrink I).symm (fun _ => Iso.refl _)
  change (∐ F).size < B.cutoff
  rw [← Scheme.size_congr e]
  exact Scheme.size_sigmaObj_lt B.aleph0_lt_cutoff B.aleph0_lt_cutoff_cof
    Cardinal.mk_le_aleph0 _ fun c => hF _

private theorem exists_disjoint_union_openImmersion
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Y : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY : AlgebraicGeometry.IsAlgebraicSpace B S hS Y) {I : Type*} [Finite I]
    (A : I → AlgebraicGeometry.BigFppfOver B S hS) (j : ∀ c, yoneda.obj (A c) ⟶ Y)
    (hj : ∀ c, AlgebraicGeometry.Space.IsOpenImmersion B S hS (j c))
    (hd : Pairwise (fun c d => Disjoint
      (Set.range (AlgebraicGeometry.Space.pointsMap B S hS (yoneda.obj (A c)) (j c)))
      (Set.range (AlgebraicGeometry.Space.pointsMap B S hS (yoneda.obj (A d)) (j d))))) :
    ∃ (W : AlgebraicGeometry.BigFppfOver B S hS) (q : yoneda.obj W ⟶ Y)
      (ι : ∀ c, A c ⟶ W),
      AlgebraicGeometry.Space.IsOpenImmersion B S hS q ∧
      (∀ c, yoneda.map (ι c) ≫ q = j c) ∧
      Nonempty (IsColimit (Cofan.mk ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj W)
        (fun c => (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (ι c)))) := by
  classical
  let G := AlgebraicGeometry.BigFppfOver.toScheme B S hS
  obtain ⟨T, t, k, ht, hk, hkt⟩ := exists_common_scheme_of_openImmersions B S hS hY A j hj
  let : Small.{u} I := inferInstance
  let F := fun c => G.obj (A c)
  have hW : B.Contains (∐ F) := contains_sigma B F fun c => (A c).left.property
  let W : AlgebraicGeometry.BigFppfOver B S hS := Over.mk (ObjectProperty.homMk
    (X := B.obj hW) (Y := B.obj hS) (Sigma.desc fun c => (A c).hom.hom))
  let ι : ∀ c, A c ⟶ W := fun c => Over.homMk
    (ObjectProperty.homMk (Sigma.ι F c)) (by
      apply ObjectProperty.hom_ext
      exact Sigma.ι_comp_desc (fun c => (A c).hom.hom) c)
  let g : W ⟶ T := Over.homMk (ObjectProperty.homMk (Sigma.desc fun c => G.map (k c))) (by
    apply ObjectProperty.hom_ext
    change (Sigma.desc fun c => G.map (k c)) ≫ T.hom.hom =
      Sigma.desc (fun c => (A c).hom.hom)
    apply Sigma.hom_ext
    intro c
    simp only [Sigma.ι_comp_desc_assoc, Sigma.ι_comp_desc]
    exact congrArg (fun f => f.hom) (k c).w)
  have hg : AlgebraicGeometry.Space.IsOpenImmersion B S hS (yoneda.map g) := by
    let Q := MorphismProperty.inverseImage (@AlgebraicGeometry.IsOpenImmersion.{u}) G
    apply MorphismProperty.relative_map (P := Q)
    change _root_.AlgebraicGeometry.IsOpenImmersion (Sigma.desc fun c => G.map (k c))
    let (c : I) : _root_.AlgebraicGeometry.IsOpenImmersion (G.map (k c)) := hk c
    apply isOpenImmersion_sigmaDesc
    intro c d hcd
    apply disjoint_scheme_ranges_of_disjoint_pointsMap_ranges B S hS (k c) (k d) t (hk c) (hk d)
    simpa only [hkt] using hd hcd
  have hι (c : I) : ι c ≫ g = k c := by
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    exact Sigma.ι_comp_desc (fun c => G.map (k c)) c
  refine ⟨W, yoneda.map g ≫ t, ι, openImmersion_comp B S hS _ _ hg ht, ?_, ?_⟩
  · intro c
    rw [← Category.assoc, ← yoneda.map_comp, hι, hkt]
  · exact ⟨coproductIsCoproduct F⟩

private theorem affineSpace_over_locallyOfFiniteType
    (n : ℕ) (S : Scheme.{u}) :
    LocallyOfFiniteType (AffineSpace.over (ULift.{u} (Fin n)) S).hom := by
  have hfp : LocallyOfFinitePresentation
      (AffineSpace.over (ULift.{u} (Fin n)) S).hom :=
    (inferInstance : LocallyOfFinitePresentation
      (𝔸(ULift.{u} (Fin n); S) ↘ S))
  refine ⟨?_⟩
  intro U hU V hV e
  exact RingHom.FiniteType.of_finitePresentation
    (hfp.finitePresentation_appLE hU hV e)

private theorem exists_immersion_sigma_affineSpace
    {I : Type*} [Finite I] (n : I → ℕ) (S : Scheme.{u}) :
    ∃ (m : ℕ) (j : (∐ fun c => AffineSpace (ULift.{u} (Fin (n c))) S) ⟶
      AffineSpace (ULift.{u} (Fin m)) S),
      _root_.AlgebraicGeometry.IsImmersion j ∧ j ≫ (AffineSpace.over (ULift.{u} (Fin m)) S).hom =
        Sigma.desc (fun c => (AffineSpace.over (ULift.{u} (Fin (n c))) S).hom) := by
  classical
  let : Small.{u} I := inferInstance
  let Z := ⊤_ Scheme.{u}
  let E := fun c => AffineSpace (ULift.{u} (Fin (n c))) Z
  let D := fun c => AffineSpace (ULift.{u} (Fin (n c))) S
  let p : (∐ E) ⟶ Z := Sigma.desc fun c => (AffineSpace.over (ULift.{u} (Fin (n c))) Z).hom
  let q : (∐ D) ⟶ S := Sigma.desc fun c => (AffineSpace.over (ULift.{u} (Fin (n c))) S).hom
  let f := terminal.from S
  let a : (∐ D) ⟶ ∐ E := Sigma.desc fun c =>
    AffineSpace.map (ULift.{u} (Fin (n c))) f ≫ Sigma.ι E c
  let : IsZariskiLocalAtSource (@LocallyOfFiniteType.{u}) :=
    AlgebraicGeometry.HasRingHomProperty.instIsZariskiLocalAtSource
      (Q := RingHom.FiniteType)
  let : LocallyOfFiniteType p := by
    apply IsZariskiLocalAtSource.of_openCover (P := @LocallyOfFiniteType) (sigmaOpenCover E)
    intro c
    change I at c
    change LocallyOfFiniteType (Sigma.ι E c ≫ p)
    dsimp only [p]
    rw [Sigma.ι_comp_desc]
    exact affineSpace_over_locallyOfFiniteType (n c) Z
  obtain ⟨m, i, hi, hip₀⟩ := AlgebraicGeometry.exists_immersion_affineSpace p
  have hip : i ≫ (AffineSpace.over (ULift.{u} (Fin m)) Z).hom = p := hip₀
  have hpull : IsPullback a q p f := by
    have h := (FinitaryPreExtensive.isUniversal_finiteCoproducts
      (coproductIsCoproduct E)).isPullback_of_isColimit_right
      (fun c => (AffineSpace.over (ULift.{u} (Fin (n c))) Z).hom) p f
      (fun c => AffineSpace.map (ULift.{u} (Fin (n c))) f)
      (fun c => (AffineSpace.over (ULift.{u} (Fin (n c))) S).hom)
      (fun c => AffineSpace.isPullback_map f) (coproductIsCoproduct D)
    have hdesc {T : Scheme.{u}} (k : ∀ c, D c ⟶ T) :
        Cofan.IsColimit.desc (coproductIsCoproduct D) k = Sigma.desc k :=
      Sigma.hom_ext _ _ fun c =>
        (Cofan.IsColimit.fac (coproductIsCoproduct D) k c).trans (Sigma.ι_comp_desc k c).symm
    simpa only [hdesc, Cofan.mk_pt, Cofan.mk_ι_app, Cofan.inj, a, q] using h
  have hA : IsPullback (AffineSpace.map (ULift.{u} (Fin m)) f)
      (AffineSpace.over (ULift.{u} (Fin m)) S).hom
      (AffineSpace.over (ULift.{u} (Fin m)) Z).hom f :=
    AffineSpace.isPullback_map f
  let j := hA.lift (a ≫ i) q
    ((Category.assoc a i _).trans ((congrArg (a ≫ ·) hip).trans hpull.w))
  have hj : IsPullback j a (AffineSpace.map (ULift.{u} (Fin m)) f) i := by
    apply IsPullback.of_right (h₁₂ := (AffineSpace.over (ULift.{u} (Fin m)) S).hom)
      (h₂₂ := (AffineSpace.over (ULift.{u} (Fin m)) Z).hom)
    · simpa only [j, hip, hA.lift_snd] using hpull.flip
    · exact hA.lift_fst _ _ _
    · exact hA.flip
  exact ⟨m, j, MorphismProperty.of_isPullback
    (P := @_root_.AlgebraicGeometry.IsImmersion) hj.flip hi, hA.lift_snd _ _ _⟩

private theorem isPullback_coproduct_component
    {C : Type*} [Category C] [FinitaryExtensive C]
    {I : Type*} [Finite I] {A E : I → C}
    (cA : Cofan A) (cE : Cofan E) (hA : IsColimit cA) (hE : IsColimit cE)
    (v : ∀ c, A c ⟶ E c) (f : cA.pt ⟶ cE.pt)
    (hf : ∀ c, cA.inj c ≫ f = v c ≫ cE.inj c) (c : I) :
    IsPullback (cA.inj c) (v c) f (cE.inj c) := by
  have hcomm : Discrete.natTrans (fun c => v c.as) ≫ cE.ι = cA.ι ≫ (Functor.const _).map f := by
    ext ⟨c⟩
    exact (hf c).symm
  exact ((FinitaryExtensive.isVanKampen_finiteCoproducts hE) cA
    (Discrete.natTrans (fun c => v c.as)) f hcomm (.of_discrete _)).mp ⟨hA⟩ ⟨c⟩

private theorem isPullback_prod_lift_right
    {C : Type*} [Category C] [HasBinaryProducts C] [HasPullbacks C]
    {A W E D X : C} {a : A ⟶ W} {v : A ⟶ E} {r : W ⟶ D} {e : E ⟶ D}
    (h : IsPullback a v r e) (f : W ⟶ X) :
    IsPullback a (prod.lift (a ≫ f) v) (prod.lift f r) (prod.map (𝟙 X) e) := by
  apply IsPullback.of_bot (v₂₁ := prod.snd) (v₂₂ := prod.snd)
  · simpa only [prod.lift_snd] using h
  · apply prod.hom_ext <;> simp [h.w]
  · refine ⟨⟨by simp⟩, ⟨PullbackCone.IsLimit.mk (by simp)
      (fun s => prod.lift (s.fst ≫ prod.fst) s.snd) ?_ ?_ ?_⟩⟩
    · intro s
      apply prod.hom_ext <;> simp [s.condition]
    · intro s
      simp
    · intro s m hm₁ hm₂
      apply prod.hom_ext
      · simpa using hm₁ =≫ prod.fst
      · simpa only [prod.lift_snd] using hm₂

private theorem presheaf_prodMap_id
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
    (X : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    {Y Z : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : Y ⟶ Z)
    (hf : (P.inverseImage (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf f) :
    (P.inverseImage (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf
      (prod.map (𝟙 X) f) := by
  have sq : IsPullback prod.snd (prod.map (𝟙 X) f) f prod.snd := by
    apply (IsPullback.of_prod_fst_with_id f X).of_iso'
      (prod.braiding X Y) (Iso.refl _) (prod.braiding X Z) (Iso.refl _)
    all_goals ext <;> simp
  let : (P.inverseImage
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf.IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange _
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback sq hf

private theorem exists_sigma_section
    {C : Type*} [Category.{u} C] {I : Type*} [Small.{u} I] (X : I → C ⥤ Type u)
    (obj : C) (element : (∐ X).obj obj) :
    ∃ index value, (Sigma.ι X index).app obj value = element := by
  obtain ⟨index, value, heq⟩ := Cofan.inj_jointly_surjective_of_isColimit
    (coproductIsCoproduct (fun index => (X index).obj obj))
    ((sigmaObjIso X obj).hom element)
  change (Sigma.ι (fun index => (X index).obj obj) index) value = _ at heq
  refine ⟨index, value, ?_⟩
  apply (CategoryTheory.mono_iff_injective _).mp
    (inferInstance : Mono (sigmaObjIso X obj).hom)
  simpa only [← types_comp_apply, ι_comp_sigmaObjIso_hom] using heq

/-- **Stacks 088N.**  Let `f : Y ⟶ X` be a morphism of algebraic spaces over `S` with `X`
Noetherian and `f` of finite presentation.  Then `Y` has a dense open subspace which admits,
over `X`, an immersion into relative affine `n`-space over `X`. -/
@[stacks 088N]
public theorem exists_denseOpen_isImmersion_affineSpaceOver
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hZ : B.Contains (⊤_ Scheme.{u}))
    {Y X : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : Y ⟶ X)
    (hY : AlgebraicGeometry.IsAlgebraicSpace B S hS Y)
    (hX : AlgebraicGeometry.IsAlgebraicSpace B S hS X)
    (hXN : AlgebraicGeometry.Space.IsNoetherian B S hS hZ X)
    (hf : AlgebraicGeometry.Space.IsFinitePresentation B S hS f) :
    ∃ (V : Subfunctor Y),
      AlgebraicGeometry.Space.IsOpenSubspace B S hS V ∧
      (letI : TopologicalSpace (AlgebraicGeometry.Space.points B S hS Y) :=
          AlgebraicGeometry.Space.pointTopology B S hS Y;
        DenseRange (AlgebraicGeometry.Space.pointsMap B S hS V.toFunctor V.ι)) ∧
      ∃ (n : ℕ) (i : V.toFunctor ⟶ AlgebraicGeometry.Space.affineSpaceOver B S hS X n),
        AlgebraicGeometry.Space.IsImmersion B S hS i ∧
          i ≫ prod.fst = V.ι ≫ f := by
  classical
  have hYN := AlgebraicGeometry.Space.isNoetherian_of_isFinitePresentation
    B S hS hZ f hY hX hf hXN
  let := AlgebraicGeometry.Space.pointTopology B S hS Y
  let : TopologicalSpace.NoetherianSpace (AlgebraicGeometry.Space.points B S hS Y) :=
    AlgebraicGeometry.Space.noetherianSpace_of_isQuasiCompact_of_isLocallyNoetherian
      B S hS Y hY hYN.1 hYN.2.2
  let : QuasiSober (AlgebraicGeometry.Space.points B S hS Y) :=
    AlgebraicGeometry.Space.quasiSober_points_of_isZariskiLocallyQuasiSeparatedOver B S hS hZ Y hY
      (isZariskiLocallyQuasiSeparatedOver_of_isAbsolutelyQuasiSeparated
        B S hS hZ hY hYN.2.1)
  let I := irreducibleComponents (AlgebraicGeometry.Space.points B S hS Y)
  have : Finite I := Set.finite_coe_iff.mpr
    TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
  have hpieces := fun C : I => exists_component_affine_open_factor_through_scheme
    B S hS hZ f hY hX hYN.2.1 hXN.2.1 inferInstance inferInstance C.1 C.2
  choose A j hA hj hsupport U a b hb hfac using hpieces
  have himmersions := fun c => exists_affineSpace_immersion_of_affine_open_factorization
    B S hS f hY hX
      (AlgebraicGeometry.Space.isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS hf.1)
      (A c) (U c) (j c) (hj c) (hA c) (a c) (b c) (hfac c)
  choose n i hi hifac using himmersions
  have hpresheafImmersions := fun c =>
    exists_immersion_affineSpaceOver_of_scheme_immersion B S hS (A c) (U c)
      (yoneda.preimage (a c)) (b c) (hb c) (n c) (i c) (hi c) (hifac c)
  choose jA hjA hjAfst using hpresheafImmersions
  let Esite (c : I) : AlgebraicGeometry.BigFppfOver B S hS :=
    Over.mk (ObjectProperty.homMk
      (X := B.obj (B.contains_affineSpace hS (n c))) (Y := B.obj hS)
      (AffineSpace.over (ULift.{u} (Fin (n c))) S).hom)
  let ρ (c : I) :
      ((Over.post (X := B.obj hS) B.inclusion).op ⋙
        yoneda.obj (Over.mk (AffineSpace.over (ULift.{u} (Fin (n c))) S).hom)) ≅
        yoneda.obj (Esite c) :=
    (restrictedYonedaIso (Over.post (X := B.obj hS) B.inclusion)).app (Esite c)
  let vSite (c : I) : A c ⟶ Esite c :=
    yoneda.preimage ((jA c ≫ prod.snd) ≫ (ρ c).hom)
  have hcoord (c : I) : jA c ≫ prod.snd =
      yoneda.map (vSite c) ≫ (ρ c).inv := by
    apply ((ρ c).cancel_iso_hom_right _ _).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact (yoneda.map_preimage _).symm
  have hdisjoint : Pairwise (fun c d : I => Disjoint
      (Set.range (AlgebraicGeometry.Space.pointsMap B S hS (yoneda.obj (A c)) (j c)))
      (Set.range (AlgebraicGeometry.Space.pointsMap B S hS (yoneda.obj (A d)) (j d)))) := by
    intro c d hcd
    exact (componentGenericOpen_disjoint c.2 (Subtype.val_injective.ne hcd)).mono
      (hsupport c).1 (hsupport d).1
  have hdense : Dense (⋃ c : I,
      Set.range (AlgebraicGeometry.Space.pointsMap B S hS (yoneda.obj (A c)) (j c))) := by
    intro x
    obtain ⟨C, hC, hxC⟩ := Set.mem_sUnion.mp
      (show x ∈ ⋃₀ irreducibleComponents (AlgebraicGeometry.Space.points B S hS Y) by
        rw [sUnion_irreducibleComponents]; trivial)
    exact closure_mono (Set.subset_iUnion _ (⟨C, hC⟩ : I)) ((hsupport ⟨C, hC⟩).2 hxC)
  obtain ⟨W, q, ι, hq, hιq, hcoprod⟩ :=
    exists_disjoint_union_openImmersion B S hS hY A j hj hdisjoint
  have hqdense : DenseRange (AlgebraicGeometry.Space.pointsMap B S hS (yoneda.obj W) q) := by
    apply hdense.mono
    rintro _ ⟨_, ⟨c, rfl⟩, p, rfl⟩
    refine ⟨AlgebraicGeometry.Space.pointsMap B S hS (yoneda.obj (A c)) (yoneda.map (ι c)) p, ?_⟩
    rw [← pointsMap_comp_point, hιq]
  let G := AlgebraicGeometry.BigFppfOver.toScheme B S hS
  let D := fun c : I => AffineSpace (ULift.{u} (Fin (n c))) S
  let : Small.{u} I := inferInstance
  let v : ∀ c, G.obj (A c) ⟶ D c := fun c =>
    G.map (vSite c)
  have hv (c : I) : v c ≫ (AffineSpace.over (ULift.{u} (Fin (n c))) S).hom =
      (A c).hom.hom :=
    congrArg (fun g => g.hom) (vSite c).w
  let hc := hcoprod.some
  let r : G.obj W ⟶ ∐ D :=
    Cofan.IsColimit.desc hc (fun c => v c ≫ Sigma.ι D c)
  have hD : B.Contains (∐ D) := contains_sigma B D fun c => (Esite c).left.property
  let qD : (∐ D) ⟶ S :=
    Sigma.desc fun c => (AffineSpace.over (ULift.{u} (Fin (n c))) S).hom
  have hr : r ≫ qD = W.hom.hom := by
    apply Cofan.IsColimit.hom_ext hc
    intro c
    change G.map (ι c) ≫ (r ≫ qD) = G.map (ι c) ≫ W.hom.hom
    have hrc : G.map (ι c) ≫ r = v c ≫ Sigma.ι D c :=
      Cofan.IsColimit.fac hc (fun c => v c ≫ Sigma.ι D c) c
    rw [← Category.assoc, hrc, Category.assoc, Sigma.ι_comp_desc, hv]
    exact (congrArg (fun g => g.hom) (ι c).w).symm
  let ESigma : AlgebraicGeometry.BigFppfOver B S hS :=
    Over.mk (ObjectProperty.homMk (X := B.obj hD) (Y := B.obj hS) qD)
  let rSite : W ⟶ ESigma := Over.homMk (ObjectProperty.homMk r) (by
    apply ObjectProperty.hom_ext
    exact hr)
  let ιD (c : I) : Esite c ⟶ ESigma := Over.homMk
    (ObjectProperty.homMk (Sigma.ι D c)) (by
      apply ObjectProperty.hom_ext
      exact Sigma.ι_comp_desc (fun c =>
        (AffineSpace.over (ULift.{u} (Fin (n c))) S).hom) c)
  have hrcomp (c : I) : ι c ≫ rSite = vSite c ≫ ιD c := by
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    exact Cofan.IsColimit.fac hc (fun c => v c ≫ Sigma.ι D c) c
  have hpbScheme (c : I) :
      IsPullback (G.map (ι c)) (v c) r (Sigma.ι D c) := by
    apply isPullback_coproduct_component
      (Cofan.mk (G.obj W) (fun c => G.map (ι c)))
      (Cofan.mk (∐ D) (Sigma.ι D)) hc (coproductIsCoproduct D) v r
      (fun c => Cofan.IsColimit.fac hc (fun c => v c ≫ Sigma.ι D c) c) c
  have hpbSite (c : I) : IsPullback (ι c) (vSite c) rSite (ιD c) :=
    IsPullback.of_map G (hrcomp c) (hpbScheme c)
  have hpbPresheaf (c : I) : IsPullback (yoneda.map (ι c))
      (yoneda.map (vSite c)) (yoneda.map rSite) (yoneda.map (ιD c)) :=
    yoneda.map_isPullback (hpbSite c)
  let jSigma : yoneda.obj W ⟶ X ⨯ yoneda.obj ESigma :=
    prod.lift (q ≫ f) (yoneda.map rSite)
  let kSigma (c : I) : X ⨯ yoneda.obj (Esite c) ⟶
      X ⨯ yoneda.obj ESigma := prod.map (𝟙 X) (yoneda.map (ιD c))
  let jLocal (c : I) : yoneda.obj (A c) ⟶ X ⨯ yoneda.obj (Esite c) :=
    prod.lift (yoneda.map (ι c) ≫ (q ≫ f)) (yoneda.map (vSite c))
  have hpbProd (c : I) :
      IsPullback (yoneda.map (ι c)) (jLocal c) jSigma (kSigma c) :=
    isPullback_prod_lift_right (hpbPresheaf c) (q ≫ f)
  have hjFirst (c : I) :
      yoneda.map (ι c) ≫ (q ≫ f) = jA c ≫ prod.fst := by
    calc
      yoneda.map (ι c) ≫ (q ≫ f) = j c ≫ f := by
        rw [← Category.assoc, hιq]
      _ = a c ≫ b c := (hfac c).symm
      _ = jA c ≫ prod.fst := by
        simpa only [yoneda.map_preimage] using (hjAfst c).symm
  have hjLocal (c : I) :
      jLocal c = jA c ≫ prod.map (𝟙 X) (ρ c).hom := by
    apply prod.hom_ext
    · simpa only [jLocal, prod.lift_fst, Category.assoc, prod.map_fst,
        Category.comp_id] using hjFirst c
    · simp only [jLocal, prod.lift_snd, Category.assoc, prod.map_snd]
      rw [← Category.assoc, hcoord, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hjLocalImmersion (c : I) :
      AlgebraicGeometry.Space.IsImmersion B S hS (jLocal c) := by
    let Q := MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.IsImmersion.{u}) G
    let : Q.presheaf.RespectsIso := inferInstance
    rw [hjLocal]
    exact MorphismProperty.RespectsIso.postcomp Q.presheaf
      (prod.mapIso (Iso.refl X) (ρ c)).hom (jA c) (hjA c)
  have hιDOpen (c : I) :
      AlgebraicGeometry.Space.IsOpenImmersion B S hS (yoneda.map (ιD c)) := by
    let Q := MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.IsOpenImmersion.{u}) G
    apply MorphismProperty.relative_map (P := Q)
    change _root_.AlgebraicGeometry.IsOpenImmersion (Sigma.ι D c)
    infer_instance
  have hkSigmaOpen (c : I) : AlgebraicGeometry.Space.IsOpenImmersion B S hS (kSigma c) :=
    presheaf_prodMap_id B S hS (@_root_.AlgebraicGeometry.IsOpenImmersion.{u}) X
      (yoneda.map (ιD c)) (hιDOpen c)
  have hcoverSite : Sieve.generate
      (Presieve.ofArrows (fun c : ULift.{u + 1} I => Esite c.down)
        (fun c => ιD c.down)) ∈
      AlgebraicGeometry.BigFppfOver.topology B S hS ESigma := by
    apply generated_over_fppf_family_mem_topology B S hS
      (fun c : ULift.{u + 1} I => Esite c.down) (fun c => ιD c.down)
    have hz : Presieve.ofArrows
        (fun c : ULift.{u + 1} I => G.obj (Esite c.down))
        (fun c => G.map (ιD c.down)) ∈
        Scheme.zariskiPrecoverage (G.obj ESigma) := by
      change Presieve.ofArrows (fun c : ULift.{u + 1} I => D c.down)
        (fun c => Sigma.ι D c.down) ∈ Scheme.zariskiPrecoverage (∐ D)
      rw [Scheme.ofArrows_mem_precoverage_iff (P := @_root_.AlgebraicGeometry.IsOpenImmersion.{u})]
      refine ⟨?_, ?_⟩
      · intro y
        let C := sigmaOpenCover D
        let c := C.idx y
        obtain ⟨z, hz⟩ := C.covers y
        refine ⟨ULift.up c, z, ?_⟩
        exact hz
      · intro c
        infer_instance
    exact Scheme.zariskiPrecoverage_le_fppfPrecoverage _ hz
  have hcoverRepresentable : Presheaf.IsLocallySurjective
      (AlgebraicGeometry.BigFppfOver.topology B S hS)
      (Sigma.desc (fun c : ULift.{u + 1} I => yoneda.map (ιD c.down))) := by
    constructor
    intro T t
    apply (AlgebraicGeometry.BigFppfOver.topology B S hS).superset_covering ?_
      ((AlgebraicGeometry.BigFppfOver.topology B S hS).pullback_stable t hcoverSite)
    rintro V a ⟨L, b, d, hd, h⟩
    rcases hd with ⟨c⟩
    refine ⟨(Sigma.ι (fun c : ULift.{u + 1} I => yoneda.obj (Esite c.down)) c).app
      (Opposite.op V) b, ?_⟩
    rw [← types_comp_apply, ← NatTrans.comp_app, Sigma.ι_comp_desc]
    change b ≫ ιD c.down = a ≫ t
    exact h
  have hcoverProduct : Presheaf.IsLocallySurjective
      (AlgebraicGeometry.BigFppfOver.topology B S hS)
      (Sigma.desc (fun c : ULift.{u + 1} I => kSigma c.down)) := by
    constructor
    intro T y
    let J := AlgebraicGeometry.BigFppfOver.topology B S hS
    apply J.superset_covering ?_
      (hcoverRepresentable.imageSieve_mem
        ((prod.snd : X ⨯ yoneda.obj ESigma ⟶ yoneda.obj ESigma).app (Opposite.op T) y))
    intro V a hmem
    obtain ⟨s, hs⟩ := hmem
    obtain ⟨c, z, hcz⟩ := exists_sigma_section
      (fun c : ULift.{u + 1} I => yoneda.obj (Esite c.down)) (Opposite.op V) s
    rw [← hcz] at hs
    let yV := (X ⨯ yoneda.obj ESigma).map a.op y
    have hs' : (yoneda.map (ιD c.down)).app (Opposite.op V) z =
        (prod.snd : X ⨯ yoneda.obj ESigma ⟶ yoneda.obj ESigma).app
          (Opposite.op V) yV := by
      simpa only [yV, ← NatTrans.naturality_apply, ← types_comp_apply,
        ← NatTrans.comp_app, Sigma.ι_comp_desc] using hs
    let k : yoneda.obj V ⟶ X ⨯ yoneda.obj (Esite c.down) :=
      prod.lift (yonedaEquiv.symm
        ((prod.fst : X ⨯ yoneda.obj ESigma ⟶ X).app (Opposite.op V) yV))
        (yonedaEquiv.symm z)
    let w : (X ⨯ yoneda.obj (Esite c.down)).obj (Opposite.op V) :=
      yonedaEquiv k
    refine ⟨(Sigma.ι (fun c : ULift.{u + 1} I => X ⨯ yoneda.obj (Esite c.down)) c).app
      (Opposite.op V) w, ?_⟩
    rw [← types_comp_apply, ← NatTrans.comp_app, Sigma.ι_comp_desc]
    change (kSigma c.down).app (Opposite.op V) w = yV
    apply yonedaEquiv.symm.injective
    rw [← yonedaEquiv_symm_naturality_right, Equiv.symm_apply_apply]
    apply prod.hom_ext
    · apply yonedaEquiv.injective
      simp [kSigma, k, yonedaEquiv_comp]
    · apply yonedaEquiv.injective
      simp only [kSigma, prod.map_snd, Category.assoc, k]
      calc
        yonedaEquiv (prod.lift
            (yonedaEquiv.symm ((prod.fst : X ⨯ yoneda.obj ESigma ⟶ X).app
              (Opposite.op V) yV)) (yonedaEquiv.symm z) ≫
            prod.snd ≫ yoneda.map (ιD c.down)) =
            (yoneda.map (ιD c.down)).app (Opposite.op V) z := by
              rw [← Category.assoc, prod.lift_snd, yonedaEquiv_comp,
                Equiv.apply_symm_apply]
        _ = _ := hs'
        _ = yonedaEquiv (yonedaEquiv.symm yV ≫ prod.snd) := by
          rw [yonedaEquiv_comp, Equiv.apply_symm_apply]
  let C := Shrink.{u} I
  let d : C → I := (equivShrink I).symm
  let K (t : C) : X ⨯ yoneda.obj (Esite (d t)) ⟶
      X ⨯ yoneda.obj ESigma := kSigma (d t)
  let U (t : C) : Subfunctor (X ⨯ yoneda.obj ESigma) := Subfunctor.range (K t)
  have hcoverRange : Presheaf.IsLocallySurjective
      (AlgebraicGeometry.BigFppfOver.topology B S hS)
      (Sigma.desc (fun t : C => (U t).ι)) := by
    constructor
    intro T y
    let J := AlgebraicGeometry.BigFppfOver.topology B S hS
    apply J.superset_covering ?_ (hcoverProduct.imageSieve_mem y)
    rintro V a ⟨s, hs⟩
    obtain ⟨c, z, hcz⟩ := exists_sigma_section
      (fun c : ULift.{u + 1} I => X ⨯ yoneda.obj (Esite c.down)) (Opposite.op V) s
    rw [← hcz] at hs
    let t : C := (equivShrink I) c.down
    have htd : d t = c.down := Equiv.symm_apply_apply (equivShrink I) c.down
    let z' : (X ⨯ yoneda.obj (Esite (d t))).obj (Opposite.op V) := htd ▸ z
    let w : (U t).toFunctor.obj (Opposite.op V) :=
      (Subfunctor.toRange (K t)).app (Opposite.op V) z'
    refine ⟨(Sigma.ι (fun t : C => (U t).toFunctor) t).app (Opposite.op V) w, ?_⟩
    rw [← types_comp_apply, ← NatTrans.comp_app, Sigma.ι_comp_desc]
    change ((Subfunctor.toRange (K t) ≫ (U t).ι).app (Opposite.op V)) z' = _
    rw [Subfunctor.toRange_ι]
    rw [← types_comp_apply, ← NatTrans.comp_app, Sigma.ι_comp_desc] at hs
    change (kSigma (d t)).app (Opposite.op V) z' = _
    have transport {i j : I} (h : i = j)
        (x : (X ⨯ yoneda.obj (Esite j)).obj (Opposite.op V))
        (hx : (kSigma j).app (Opposite.op V) x =
          (X ⨯ yoneda.obj ESigma).map a.op y) :
        (kSigma i).app (Opposite.op V) (h ▸ x) =
          (X ⨯ yoneda.obj ESigma).map a.op y := by
      cases h
      exact hx
    exact transport htd z hs
  have hProdAlg (E : AlgebraicGeometry.BigFppfOver B S hS) :
      AlgebraicGeometry.IsAlgebraicSpace B S hS (X ⨯ yoneda.obj E) := by
    have hTerm : AlgebraicGeometry.IsAlgebraicSpace B S hS
        (⊤_ ((AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u)) := by
      let R₀ : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u :=
        yoneda.obj (Over.mk (𝟙 (B.obj hS)))
      have hR₀ : AlgebraicGeometry.IsAlgebraicSpace B S hS R₀ :=
        AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS (Over.mk (𝟙 (B.obj hS)))
      let : PreservesLimit (Functor.empty.{0}
          (AlgebraicGeometry.BigFppfOver B S hS)) yoneda := inferInstance
      have hR₀term : IsTerminal R₀ :=
        (Over.mkIdTerminal : IsTerminal (Over.mk (𝟙 (B.obj hS)))).isTerminalObj yoneda _
      exact isAlgebraicSpace_of_presheafIso B S hS
        (hR₀term.uniqueUpToIso terminalIsTerminal) hR₀
    exact isAlgebraicSpace_of_presheafIso B S hS
      (prodIsoPullback X (yoneda.obj E)).symm
      (AlgebraicGeometry.isAlgebraicSpace_pullback B S hS
        (terminal.from X) (terminal.from (yoneda.obj E)) hX
        (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS E) hTerm)
  have (t : C) : Mono (K t) :=
    AlgebraicGeometry.Space.mono_of_isOpenImmersion B S hS (K t) (hkSigmaOpen (d t))
  let eK (t : C) : X ⨯ yoneda.obj (Esite (d t)) ≅ (U t).toFunctor :=
    asIso (Subfunctor.toRange (K t))
  have hUopen (t : C) : AlgebraicGeometry.Space.IsOpenSubspace B S hS (U t) :=
    isOpenSubspace_range_of_open B S hS (K t) (hProdAlg (Esite (d t))) (hkSigmaOpen (d t))
  have hCover : AlgebraicGeometry.Space.IsZariskiCover B S hS C U := ⟨hUopen, hcoverRange⟩
  have hLocal (t : C) : AlgebraicGeometry.Space.IsImmersion B S hS
      (pullback.snd jSigma (U t).ι) := by
    have hpbrange : IsPullback (yoneda.map (ι (d t)))
        (jLocal (d t) ≫ (eK t).hom) jSigma (U t).ι := by
      apply (hpbProd (d t)).of_iso (Iso.refl _) (Iso.refl _)
        (eK t) (Iso.refl _)
      · simp
      · simp
      · simp
      · simpa only [Iso.refl_hom, Category.comp_id, K, U, eK, asIso_hom] using
          (Subfunctor.toRange_ι (K t)).symm
    let Q := MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.IsImmersion.{u}) G
    let : Q.presheaf.RespectsIso := inferInstance
    change Q.presheaf (pullback.snd jSigma (U t).ι)
    rw [← MorphismProperty.cancel_left_of_respectsIso
      (P := Q.presheaf) hpbrange.isoPullback.hom]
    rw [hpbrange.isoPullback_hom_snd]
    exact MorphismProperty.RespectsIso.postcomp Q.presheaf (eK t).hom
      (jLocal (d t)) (hjLocalImmersion (d t))
  have hjSigma : AlgebraicGeometry.Space.IsImmersion B S hS jSigma := by
    apply ((AlgebraicGeometry.Space.isImmersion_tfae_of_isAlgebraicSpace
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS W)
      (hProdAlg ESigma) jSigma).out 5 1).mp
    exact ⟨C, U, hCover, hLocal⟩
  obtain ⟨m, eD, heD, heDfac⟩ := exists_immersion_sigma_affineSpace n S
  have hFinal : B.Contains (AffineSpace (ULift.{u} (Fin m)) S) :=
    B.contains_affineSpace hS m
  let EFinal : AlgebraicGeometry.BigFppfOver B S hS :=
    Over.mk (ObjectProperty.homMk
      (X := B.obj hFinal) (Y := B.obj hS)
      (AffineSpace.over (ULift.{u} (Fin m)) S).hom)
  let eDSite : ESigma ⟶ EFinal := Over.homMk
    (ObjectProperty.homMk eD) (by
      apply ObjectProperty.hom_ext
      exact heDfac)
  let R : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u :=
    (Over.post (X := B.obj hS) B.inclusion).op ⋙
      yoneda.obj (Over.mk (AffineSpace.over (ULift.{u} (Fin m)) S).hom)
  let ρFinal : R ≅ yoneda.obj EFinal :=
    (restrictedYonedaIso (Over.post (X := B.obj hS) B.inclusion)).app EFinal
  let aD : yoneda.obj ESigma ⟶ R := yoneda.map eDSite ≫ ρFinal.inv
  have haD : AlgebraicGeometry.Space.IsImmersion B S hS aD := by
    let Q := MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.IsImmersion.{u}) G
    have heDSite : AlgebraicGeometry.Space.IsImmersion B S hS (yoneda.map eDSite) := by
      have := inverseImage_toScheme_isStableUnderBaseChange B S hS
        (@_root_.AlgebraicGeometry.IsImmersion.{u})
      apply MorphismProperty.relative_map (P := Q)
      exact heD
    exact MorphismProperty.RespectsIso.postcomp Q.presheaf ρFinal.inv
      (yoneda.map eDSite) heDSite
  let aW : yoneda.obj W ⟶ R := yoneda.map rSite ≫ aD
  let iW : yoneda.obj W ⟶ AlgebraicGeometry.Space.affineSpaceOver B S hS X m :=
    prod.lift (q ≫ f) aW
  have hiW : AlgebraicGeometry.Space.IsImmersion B S hS iW := by
    have hProd : AlgebraicGeometry.Space.IsImmersion B S hS (prod.map (𝟙 X) aD) :=
      presheaf_prodMap_id B S hS (@_root_.AlgebraicGeometry.IsImmersion.{u}) X aD haD
    have hcomp : iW = jSigma ≫ prod.map (𝟙 X) aD := by
      apply prod.hom_ext
      · dsimp only [iW, jSigma]
        rw [Category.assoc, prod.map_fst, Category.comp_id, prod.lift_fst]
        simp only [prod.lift_fst]
      · simp only [iW, prod.lift_snd]
        change aW = (jSigma ≫ prod.map (𝟙 X) aD) ≫ prod.snd
        calc
          aW = yoneda.map rSite ≫ aD := rfl
          _ = (jSigma ≫ prod.snd) ≫ aD := by simp only [jSigma, prod.lift_snd]
          _ = (jSigma ≫ prod.map (𝟙 X) aD) ≫ prod.snd := by
            simp only [Category.assoc, prod.map_snd]
    rw [hcomp]
    exact immersion_comp B S hS jSigma (prod.map (𝟙 X) aD) hjSigma hProd
  let := AlgebraicGeometry.Space.mono_of_isOpenImmersion B S hS q hq
  let V := Subfunctor.range q
  let e : yoneda.obj W ≅ V.toFunctor := asIso (Subfunctor.toRange q)
  have he : V.ι = e.inv ≫ q := by
    rw [Iso.eq_inv_comp]
    exact Subfunctor.toRange_ι q
  have hV : AlgebraicGeometry.Space.IsOpenSubspace B S hS V :=
    isOpenSubspace_range_of_open B S hS q (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS W) hq
  refine ⟨V, hV, ?_, m, e.inv ≫ iW,
    MorphismProperty.RespectsIso.precomp _ e.inv iW hiW, ?_⟩
  · apply hqdense.mono
    rintro _ ⟨p, rfl⟩
    refine ⟨AlgebraicGeometry.Space.pointsMap B S hS (yoneda.obj W) e.hom p, ?_⟩
    rw [← pointsMap_comp_point]
    change AlgebraicGeometry.Space.pointsMap B S hS (yoneda.obj W)
      (Subfunctor.toRange q ≫ V.ι) p = _
    rw [Subfunctor.toRange_ι]
  · simp only [iW, Category.assoc, prod.lift_fst, he]

end AlgebraicGeometry.Space

end
