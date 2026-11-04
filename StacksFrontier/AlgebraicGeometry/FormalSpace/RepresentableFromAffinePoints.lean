module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableLocalOnSourceAndTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedEtaleSiteMorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.SiteCoproductLargeValued
public import StacksFrontier.CategoryTheory.Limits.CoproductPullback
public import StacksFrontier.CategoryTheory.Sites.InfinitaryExtensive

/-!
# Representability by algebraic spaces from the affine points of the target

Let `S` be a scheme contained in a big fppf site `𝔅`. A morphism `Φ : X ⟶ Y` of fppf sheaves
over `S` is representable by algebraic spaces as soon as its base change along every point of
`Y` out of an *affine* object of the site is represented by an object of the site whose size is
bounded by that of the point. The same hypothesis detects that the morphism is locally of finite
type and quasi-compact.

## Main definitions

* `AlgebraicGeometry.FormalSpace.CompactPullbackRepresentable`: the base change of `Φ` along
  every point of `Y` out of a quasi-compact object of the site is represented by an object of
  the site, with projection of finite type.
* `AlgebraicGeometry.FormalSpace.CompactPullbackRepresentableOfSizeLe`: the base change of `Φ`
  along every such point is represented by an object of the site of size at most that of the
  point, with projection satisfying a given property.

## Main results

* `AlgebraicGeometry.FormalSpace.isRepresentableByAlgebraicSpacesULift_of_affine_pullback`:
  under `CompactPullbackRepresentable`, `Φ` is representable by algebraic spaces.
* `AlgebraicGeometry.FormalSpace.exists_surjective_etale_cover_isPullback_of_compact_pullback`:
  for a property of morphisms of schemes which is Zariski-local on the source and
  multiplicative, every point of `Y` has a surjective étale covering over which the base change
  of `Φ` is represented by an object of the site, with projection satisfying the property.
* `AlgebraicGeometry.FormalSpace.isLocallyOfFiniteTypeULift_pullback_of_compact_pullback` and
  `AlgebraicGeometry.FormalSpace.isQuasiCompactULift_of_compact_pullback`: the base change of
  `Φ` along every point is locally of finite type, and `Φ` is quasi-compact.

## References

* [Stacks Project, Tag 01JJ](https://stacks.math.columbia.edu/tag/01JJ)
* [Stacks Project, Tag 0AN5](https://stacks.math.columbia.edu/tag/0AN5)
* [Stacks Project, Tag 0BGR](https://stacks.math.columbia.edu/tag/0BGR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Cardinal

universe u

namespace AlgebraicGeometry.FormalSpace

variable (𝔅 : BigFppfSite.{u}) (S : Scheme.{u}) (hS : 𝔅.Contains S)

/-- The affine opens of an object of the big fppf site of `S`, as a family of objects of the
site covering it by open immersions, together with the bound on the index type and on the
members by the size of the object. -/
private theorem exists_affineOpens_cover_site (T : BigFppfOver 𝔅 S hS) :
    ∃ (ι : Type u) (X : ι → BigFppfOver 𝔅 S hS) (gX : ∀ i, X i ⟶ T),
      (∀ i, IsAffine ((BigFppfOver.toScheme 𝔅 S hS).obj (X i))) ∧
      (∀ i, IsOpenImmersion ((BigFppfOver.toScheme 𝔅 S hS).map (gX i))) ∧
      (∀ x : (BigFppfOver.toScheme 𝔅 S hS).obj T,
        ∃ i, x ∈ Set.range ((BigFppfOver.toScheme 𝔅 S hS).map (gX i))) ∧
      #ι ≤ ((BigFppfOver.toScheme 𝔅 S hS).obj T).size ∧
      ∀ i, ((BigFppfOver.toScheme 𝔅 S hS).obj (X i)).size ≤
        ((BigFppfOver.toScheme 𝔅 S hS).obj T).size := by
  classical
  set W : Scheme.{u} := (BigFppfOver.toScheme 𝔅 S hS).obj T
  let hU (i : W.affineOpens) : 𝔅.Contains (i.1 : Scheme.{u}) :=
    Scheme.size_lt_of_isOpenImmersion i.1.ι T.left.property
  let fO (i : W.affineOpens) : 𝔅.obj (hU i) ⟶ T.left :=
    𝔅.inclusion.preimage
      (show 𝔅.inclusion.obj (𝔅.obj (hU i)) ⟶ 𝔅.inclusion.obj T.left from i.1.ι)
  let X (i : W.affineOpens) : BigFppfOver 𝔅 S hS := Over.mk (fO i ≫ T.hom)
  let gX (i : W.affineOpens) : X i ⟶ T := Over.homMk (fO i) (by simp [X])
  have hfmap (i : W.affineOpens) : (BigFppfOver.toScheme 𝔅 S hS).map (gX i) = i.1.ι :=
    𝔅.inclusion.map_preimage _
  refine ⟨W.affineOpens, X, gX, fun i => i.2, fun i => ?_, fun x => ?_,
    Scheme.mk_affineOpens_le_size W, fun i => Scheme.size_coe_opens_le W i.1⟩
  · rw [hfmap i]
    infer_instance
  · obtain ⟨i, hxi⟩ := TopologicalSpace.Opens.mem_iSup.mp
      ((iSup_affineOpens_eq_top W).ge (Set.mem_univ x))
    refine ⟨i, ⟨x, hxi⟩, ?_⟩
    rw [hfmap i]
    rfl

/-- A colimiting cofan stays colimiting after replacing each summand by an isomorphic
object. -/
private def isColimit_cofan_comp_iso {D : Type*} [Category* D] {ι : Type*}
    {F G : ι → D} {P : D} (f : ∀ i, F i ⟶ P) (hf : IsColimit (Cofan.mk P f))
    (e : ∀ i, G i ≅ F i) : IsColimit (Cofan.mk P fun i => (e i).hom ≫ f i) := by
  refine Cofan.IsColimit.mk _
    (fun s => Cofan.IsColimit.desc hf fun i => (e i).inv ≫ s.inj i) (fun s i => ?_)
    (fun s m hm => ?_)
  · have hd := Cofan.IsColimit.fac hf (fun i => (e i).inv ≫ s.inj i) i
    simp only [cofan_mk_inj] at hd ⊢
    simp [hd]
  · refine Cofan.IsColimit.hom_ext hf _ _ fun i => ?_
    have hd := Cofan.IsColimit.fac hf (fun i => (e i).inv ≫ s.inj i) i
    have h2 := hm i
    simp only [cofan_mk_inj, Category.assoc] at hd h2 ⊢
    rw [hd, ← h2, Iso.inv_hom_id_assoc]

/-- The base change of `Φ` along every point of `Y` out of a quasi-compact object of the site is
represented by an object of the site whose projection is locally of finite type and
quasi-compact. -/
abbrev CompactPullbackRepresentable {X Y : FppfSheaf 𝔅 S hS} (Φ : X ⟶ Y) : Prop :=
  ∀ (U : BigFppfOver 𝔅 S hS), CompactSpace ((BigFppfOver.toScheme 𝔅 S hS).obj U) →
    ∀ ξ : (BigFppfOver.topology 𝔅 S hS).uliftYoneda.{u + 1}.obj U ⟶ Y,
    ∃ (W : BigFppfOver 𝔅 S hS) (p : W ⟶ U)
      (r : (BigFppfOver.topology 𝔅 S hS).uliftYoneda.{u + 1}.obj W ⟶ X),
      IsPullback r ((BigFppfOver.topology 𝔅 S hS).uliftYoneda.{u + 1}.map p) Φ ξ ∧
      AlgebraicGeometry.LocallyOfFiniteType ((BigFppfOver.toScheme 𝔅 S hS).map p) ∧
      AlgebraicGeometry.QuasiCompact ((BigFppfOver.toScheme 𝔅 S hS).map p)

/-- The base change of `Φ` along every point of `Y` out of a quasi-compact object of the site is
represented by an object of the site whose projection satisfies `P` and whose size is at most
that of the point. -/
abbrev CompactPullbackRepresentableOfSizeLe (P : MorphismProperty Scheme.{u})
    {X Y : FppfSheaf 𝔅 S hS} (Φ : X ⟶ Y) : Prop :=
  ∀ (U : BigFppfOver 𝔅 S hS), CompactSpace ((BigFppfOver.toScheme 𝔅 S hS).obj U) →
    ∀ ξ : (BigFppfOver.topology 𝔅 S hS).uliftYoneda.{u + 1}.obj U ⟶ Y,
    ∃ (W : BigFppfOver 𝔅 S hS) (p : W ⟶ U)
      (r : (BigFppfOver.topology 𝔅 S hS).uliftYoneda.{u + 1}.obj W ⟶ X),
      IsPullback r ((BigFppfOver.topology 𝔅 S hS).uliftYoneda.{u + 1}.map p) Φ ξ ∧
      P ((BigFppfOver.toScheme 𝔅 S hS).map p) ∧
      ((BigFppfOver.toScheme 𝔅 S hS).obj W).size ≤
        ((BigFppfOver.toScheme 𝔅 S hS).obj U).size

/-- `AlgebraicGeometry.FormalSpace.CompactPullbackRepresentable` implies
`AlgebraicGeometry.FormalSpace.CompactPullbackRepresentableOfSizeLe` for the property
`AlgebraicGeometry.LocallyOfFiniteType`. -/
theorem compactPullbackRepresentableOfSizeLe_of_compactPullbackRepresentable
    {X Y : FppfSheaf 𝔅 S hS} {Φ : X ⟶ Y} (h : CompactPullbackRepresentable 𝔅 S hS Φ) :
    CompactPullbackRepresentableOfSizeLe 𝔅 S hS
      (@AlgebraicGeometry.LocallyOfFiniteType.{u}) Φ := by
  intro U hU ξ
  obtain ⟨W, p, r, hsq, hlft, hqc⟩ := h U hU ξ
  have _ := hlft
  have _ := hqc
  exact ⟨W, p, r, hsq, hlft, Scheme.size_le_of_locallyOfFiniteType_of_quasiCompact
    ((BigFppfOver.toScheme 𝔅 S hS).map p)⟩

/-- Let `P` be a property of morphisms of schemes which is Zariski-local on the source and
multiplicative, and suppose `CompactPullbackRepresentableOfSizeLe P Φ`. Then every point
`ξ` of `Y` out of an object `T` of the site has a surjective étale covering `q : V ⟶ T` by an
object of the site, together with an object `V'` of the site representing the base change of
`Φ` along `V ⟶ T ⟶ Y` whose projection `k : V' ⟶ V` satisfies `P`. -/
theorem exists_surjective_etale_cover_isPullback_of_compact_pullback
    (P : MorphismProperty Scheme.{u}) [IsZariskiLocalAtSource P] [P.IsMultiplicative]
    {X Y : FppfSheaf 𝔅 S hS} (Φ : X ⟶ Y)
    (h : CompactPullbackRepresentableOfSizeLe 𝔅 S hS P Φ)
    (T : BigFppfOver 𝔅 S hS)
    (ξ : (BigFppfOver.topology 𝔅 S hS).uliftYoneda.{u + 1}.obj T ⟶ Y) :
    ∃ (V V' : BigFppfOver 𝔅 S hS) (q : V ⟶ T) (k : V' ⟶ V)
      (r : (BigFppfOver.topology 𝔅 S hS).uliftYoneda.{u + 1}.obj V' ⟶ X),
      Surjective ((BigFppfOver.toScheme 𝔅 S hS).map q) ∧
      Etale ((BigFppfOver.toScheme 𝔅 S hS).map q) ∧
      P ((BigFppfOver.toScheme 𝔅 S hS).map k) ∧
      IsPullback r ((BigFppfOver.topology 𝔅 S hS).uliftYoneda.{u + 1}.map k) Φ
        ((BigFppfOver.topology 𝔅 S hS).uliftYoneda.{u + 1}.map q ≫ ξ) := by
  classical
  obtain ⟨ι, Xf, gX, haff, hopen, hcovT, hιsize, hXsize⟩ :=
    exists_affineOpens_cover_site 𝔅 S hS T
  obtain ⟨V, j, q, hjq, hjopen, -, hqsurj, hqet, -, ⟨hcofanV⟩⟩ :=
    BigFppfOver.exists_surjective_etale_sigma_of_etaleCover 𝔅 S hS Xf T gX
      (fun i => by have _ := hopen i; infer_instance) hcovT
      T.left.property hιsize hXsize
  set J := BigFppfOver.topology 𝔅 S hS
  set ζ : J.uliftYoneda.{u + 1}.obj V ⟶ Y := J.uliftYoneda.{u + 1}.map q ≫ ξ with hζ
  set fam : ∀ i, J.uliftYoneda.{u + 1}.obj (Xf i) ⟶ Y :=
    fun i => J.uliftYoneda.{u + 1}.map (gX i) ≫ ξ
  choose W p r sq hPp hpsize using fun i =>
    h (Xf i) (by have _ := haff i; infer_instance) (fam i)
  have hWsize : ∀ i, ((BigFppfOver.toScheme 𝔅 S hS).obj (W i)).size ≤
      ((BigFppfOver.toScheme 𝔅 S hS).obj T).size := fun i => (hpsize i).trans (hXsize i)
  obtain ⟨V', j', hj'open, hj'cov, -, ⟨hj'site⟩, ⟨hcofanV'⟩⟩ :=
    BigFppfOver.exists_isColimitUliftYoneda_of_size_le 𝔅 S hS W T.left.property
      hιsize hWsize
  have hApb : IsPullback (pullback.fst ζ Φ) (pullback.snd ζ Φ) ζ Φ :=
    IsPullback.of_hasPullback ζ Φ
  have hAcofan := Sheaf.isColimitCofanMkPullback J
    (fun i => J.uliftYoneda.{u + 1}.map (j i)) hcofanV (pullback.fst ζ Φ)
  have hpaste : ∀ i, IsPullback
      (pullback.snd (J.uliftYoneda.{u + 1}.map (j i)) (pullback.fst ζ Φ) ≫ pullback.snd ζ Φ)
      (pullback.fst (J.uliftYoneda.{u + 1}.map (j i)) (pullback.fst ζ Φ)) Φ (fam i) := by
    intro i
    have hcomp : J.uliftYoneda.{u + 1}.map (j i) ≫ ζ = fam i := by
      rw [hζ, ← Category.assoc, ← Functor.map_comp, hjq i]
    exact hcomp ▸ ((IsPullback.of_hasPullback
      (J.uliftYoneda.{u + 1}.map (j i)) (pullback.fst ζ Φ)).flip.paste_horiz hApb.flip)
  obtain ⟨e, hesnd⟩ : ∃ e : ∀ i, J.uliftYoneda.{u + 1}.obj (W i) ≅
      pullback (J.uliftYoneda.{u + 1}.map (j i)) (pullback.fst ζ Φ),
      ∀ i, (e i).hom ≫
        pullback.fst (J.uliftYoneda.{u + 1}.map (j i)) (pullback.fst ζ Φ) =
        J.uliftYoneda.{u + 1}.map (p i) :=
    ⟨fun i => (sq i).isoIsPullback _ _ (hpaste i),
      fun i => (sq i).isoIsPullback_hom_snd _ _ (hpaste i)⟩
  have hAcofan2 := isColimit_cofan_comp_iso _ hAcofan e
  obtain ⟨eA, heAhom⟩ : ∃ eA : pullback ζ Φ ≅ J.uliftYoneda.{u + 1}.obj V',
      ∀ i, ((e i).hom ≫
        pullback.snd (J.uliftYoneda.{u + 1}.map (j i)) (pullback.fst ζ Φ)) ≫ eA.hom =
        J.uliftYoneda.{u + 1}.map (j' i) :=
    ⟨hAcofan2.coconePointUniqueUpToIso hcofanV',
      fun i => IsColimit.comp_coconePointUniqueUpToIso_hom hAcofan2 hcofanV' ⟨i⟩⟩
  set k : V' ⟶ V := Cofan.IsColimit.desc hj'site (fun i => p i ≫ j i)
  have hkfac : ∀ i, j' i ≫ k = p i ≫ j i := Cofan.IsColimit.fac hj'site _
  have heAinj : ∀ i, J.uliftYoneda.{u + 1}.map (j' i) ≫ eA.inv =
      (e i).hom ≫ pullback.snd (J.uliftYoneda.{u + 1}.map (j i)) (pullback.fst ζ Φ) := by
    intro i
    rw [← heAhom i, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have heAk : eA.inv ≫ pullback.fst ζ Φ = J.uliftYoneda.{u + 1}.map k := by
    refine Cofan.IsColimit.hom_ext hcofanV' _ _ fun i => ?_
    calc J.uliftYoneda.{u + 1}.map (j' i) ≫ eA.inv ≫ pullback.fst ζ Φ
        = ((e i).hom ≫ pullback.snd (J.uliftYoneda.{u + 1}.map (j i))
            (pullback.fst ζ Φ)) ≫ pullback.fst ζ Φ := by
          rw [← Category.assoc, heAinj i]
      _ = (e i).hom ≫ pullback.fst (J.uliftYoneda.{u + 1}.map (j i)) (pullback.fst ζ Φ) ≫
            J.uliftYoneda.{u + 1}.map (j i) := by
          rw [Category.assoc, pullback.condition]
      _ = J.uliftYoneda.{u + 1}.map (p i) ≫ J.uliftYoneda.{u + 1}.map (j i) := by
          rw [← Category.assoc, hesnd i]
      _ = J.uliftYoneda.{u + 1}.map (j' i) ≫ J.uliftYoneda.{u + 1}.map k := by
          rw [← Functor.map_comp, ← Functor.map_comp, hkfac i]
  have hkP : P ((BigFppfOver.toScheme 𝔅 S hS).map k) := by
    set 𝒰 : ((BigFppfOver.toScheme 𝔅 S hS).obj V').OpenCover.{u} :=
      { I₀ := ι
        X := fun i => (BigFppfOver.toScheme 𝔅 S hS).obj (W i)
        f := fun i => (BigFppfOver.toScheme 𝔅 S hS).map (j' i)
        mem₀ := by
          rw [Scheme.presieve₀_mem_precoverage_iff]
          exact ⟨hj'cov, hj'open⟩ }
    refine IsZariskiLocalAtSource.of_openCover 𝒰 fun i => ?_
    show P ((BigFppfOver.toScheme 𝔅 S hS).map (j' i) ≫ (BigFppfOver.toScheme 𝔅 S hS).map k)
    rw [← Functor.map_comp, hkfac i, Functor.map_comp]
    have _ := hjopen i
    exact P.comp_mem _ _ (hPp i)
      (IsZariskiLocalAtSource.of_isOpenImmersion ((BigFppfOver.toScheme 𝔅 S hS).map (j i)))
  refine ⟨V, V', q, k, eA.inv ≫ pullback.snd ζ Φ, hqsurj, hqet, hkP, ?_⟩
  exact hApb.flip.of_iso eA (Iso.refl _) (Iso.refl _) (Iso.refl _)
    ((Category.comp_id _).trans (eA.hom_inv_id_assoc _).symm)
    (((Category.comp_id _).trans (eA.hom_inv_id_assoc _).symm).trans
      (congrArg (fun z => eA.hom ≫ z) heAk))
    ((Category.comp_id _).trans (Category.id_comp _).symm)
    ((Category.comp_id _).trans (Category.id_comp _).symm)

/-- Under `CompactPullbackRepresentable Φ`, every point of `Y` out of an object `T` of the site
has a surjective étale covering `V ⟶ T` by an object of the site over which the base change of
`Φ` is represented by an object `V'` of the site, with projection `V' ⟶ V` locally of finite
type. -/
private theorem exists_etaleCover_isPullback_of_affine_pullback
    {X Y : FppfSheaf 𝔅 S hS} (Φ : X ⟶ Y) (h : CompactPullbackRepresentable 𝔅 S hS Φ)
    (T : BigFppfOver 𝔅 S hS)
    (ξ : (BigFppfOver.topology 𝔅 S hS).uliftYoneda.{u + 1}.obj T ⟶ Y) :
    ∃ (V V' : BigFppfOver 𝔅 S hS) (q : V ⟶ T) (k : V' ⟶ V)
      (r : (BigFppfOver.topology 𝔅 S hS).uliftYoneda.{u + 1}.obj V' ⟶ X),
      Surjective ((BigFppfOver.toScheme 𝔅 S hS).map q) ∧
      Etale ((BigFppfOver.toScheme 𝔅 S hS).map q) ∧
      AlgebraicGeometry.LocallyOfFiniteType ((BigFppfOver.toScheme 𝔅 S hS).map k) ∧
      IsPullback r ((BigFppfOver.topology 𝔅 S hS).uliftYoneda.{u + 1}.map k) Φ
        ((BigFppfOver.topology 𝔅 S hS).uliftYoneda.{u + 1}.map q ≫ ξ) := by
  have : IsZariskiLocalAtSource (@AlgebraicGeometry.LocallyOfFiniteType.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.FiniteType)
  exact exists_surjective_etale_cover_isPullback_of_compact_pullback 𝔅 S hS
    (@AlgebraicGeometry.LocallyOfFiniteType.{u}) Φ
    (compactPullbackRepresentableOfSizeLe_of_compactPullbackRepresentable 𝔅 S hS h) T ξ

/-- A pullback square over `f ≫ ξ` yields a pullback square of `f` and `g` over the pullback
of `ξ` and `Φ`. -/
private theorem exists_isPullback_lift_of_isPullback {C : Type*} [Category* C] {A B Z X Y : C}
    {r : A ⟶ X} {g : A ⟶ B} {Φ : X ⟶ Y} {f : B ⟶ Z} {ξ : Z ⟶ Y}
    [HasPullback ξ Φ] (hsq : IsPullback r g Φ (f ≫ ξ)) :
    ∃ a : A ⟶ pullback ξ Φ, a ≫ pullback.fst ξ Φ = g ≫ f ∧
      IsPullback a g (pullback.fst ξ Φ) f := by
  have hcond : (g ≫ f) ≫ ξ = r ≫ Φ := (Category.assoc _ _ _).trans hsq.w.symm
  have hafst : pullback.lift (g ≫ f) r hcond ≫ pullback.fst ξ Φ = g ≫ f := pullback.lift_fst _ _ _
  refine ⟨pullback.lift (g ≫ f) r hcond, hafst, IsPullback.of_right ?_ hafst
    (IsPullback.of_hasPullback ξ Φ).flip⟩
  rwa [pullback.lift_snd]

/-- **Representability by algebraic spaces is detected on the affine points of the target.**
A morphism `Φ : X ⟶ Y` of fppf sheaves over `S` is representable by algebraic spaces as soon
as its base change along every point of `Y` whose source is an affine object of the site is
represented by an object of the site whose projection is of finite type. -/
theorem isRepresentableByAlgebraicSpacesULift_of_affine_pullback
    {X Y : FppfSheaf 𝔅 S hS} (Φ : X ⟶ Y) (h : CompactPullbackRepresentable 𝔅 S hS Φ) :
    Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} 𝔅 S hS Φ.hom := by
  classical
  refine isRepresentable_of_forall_surjective_etale_cover 𝔅 S hS Φ ?_
  intro T ξp
  obtain ⟨V, V', q, k, r, hqsurj, hqet, -, hsq⟩ :=
    exists_etaleCover_isPullback_of_affine_pullback 𝔅 S hS Φ h T ⟨ξp⟩
  refine ⟨V, q, hqsurj, hqet, ?_⟩
  have hpre := hsq.map (sheafToPresheaf (BigFppfOver.topology 𝔅 S hS) (Type (u + 1)))
  exact Space.isAlgebraicSpaceULift_of_iso 𝔅 S hS
    hpre.flip.isoPullback (Space.isAlgebraicSpaceULift_uliftYoneda.{u + 1} 𝔅 S hS V')

/-- **Being locally of finite type is detected on the quasi-compact points of the target.**
For a morphism satisfying the hypothesis, the base change along *every* scheme-valued point
of the target is locally of finite type. -/
theorem isLocallyOfFiniteTypeULift_pullback_of_compact_pullback
    {X Y : FppfSheaf 𝔅 S hS} (Φ : X ⟶ Y) (h : CompactPullbackRepresentable 𝔅 S hS Φ)
    (T : BigFppfOver 𝔅 S hS) (ξp : (uliftYoneda.{u + 1}).obj T ⟶ Y.val) :
    Space.IsLocallyOfFiniteTypeULift.{u + 1} 𝔅 S hS (pullback.fst ξp Φ.hom) := by
  classical
  obtain ⟨V, V', q, k, r, hqsurj, hqet, hklft, hsq⟩ :=
    exists_etaleCover_isPullback_of_affine_pullback 𝔅 S hS Φ h T ⟨ξp⟩
  have hpre := hsq.map (sheafToPresheaf (BigFppfOver.topology 𝔅 S hS) (Type (u + 1)))
  obtain ⟨a, hafst, htop⟩ := exists_isPullback_lift_of_isPullback hpre
  have hbet := Space.relative_uliftYoneda_map 𝔅 S hS
    (@AlgebraicGeometry.Etale.{u}) q hqet
  have hbsurj := Space.relative_uliftYoneda_map 𝔅 S hS
    (@AlgebraicGeometry.Surjective.{u}) q hqsurj
  exact Space.holdsOnEveryEtaleChartULift_of_surjectiveChart 𝔅 S hS _
    AlgebraicGeometry.LocallyOfFiniteType.isEtaleLocalOnSourceAndTarget
    (isRepresentableByAlgebraicSpacesULift_of_affine_pullback 𝔅 S hS Φ h T ξp)
    (Space.isAlgebraicSpaceULift_uliftYoneda.{u + 1} 𝔅 S hS T) V' V a
    ((uliftYoneda.{u + 1}).map q) k
    (Space.relative_of_isPullback 𝔅 S hS htop hbet) hbet
    (Space.relative_of_isPullback 𝔅 S hS htop hbsurj) hafst.symm hklft

/-- **Quasi-compactness is detected on the quasi-compact points of the target.** A morphism
satisfying the hypothesis is quasi-compact. -/
theorem isQuasiCompactULift_of_compact_pullback
    {X Y : FppfSheaf 𝔅 S hS} (Φ : X ⟶ Y) (h : CompactPullbackRepresentable 𝔅 S hS Φ) :
    Space.IsQuasiCompactULift.{u + 1} 𝔅 S hS Φ.hom := by
  classical
  intro Z _ hZqc γ
  obtain ⟨U₀, c, hU₀c, hcSurj, hcEtale⟩ := hZqc
  obtain ⟨W₀, p₀, r₀, hsq₀, -, hqc₀⟩ := h U₀ hU₀c ⟨c ≫ γ⟩
  have hpre := hsq₀.map (sheafToPresheaf (BigFppfOver.topology 𝔅 S hS) (Type (u + 1)))
  obtain ⟨m, -, htop⟩ := exists_isPullback_lift_of_isPullback hpre
  have _ := hqc₀
  have _ := hU₀c
  refine ⟨W₀, m, QuasiCompact.compactSpace_of_compactSpace
    ((BigFppfOver.toScheme 𝔅 S hS).map p₀), Space.relative_of_isPullback 𝔅 S hS htop hcSurj,
    (Space.isEtaleULift_iff_relative_etale 𝔅 S hS m).mpr
      (Space.relative_of_isPullback 𝔅 S hS htop
        ((Space.isEtaleULift_iff_relative_etale 𝔅 S hS c).mp hcEtale))⟩

end AlgebraicGeometry.FormalSpace

end
