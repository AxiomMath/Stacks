module

public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import Mathlib.CategoryTheory.Sites.CoverPreserving
public import StacksFrontier.AlgebraicGeometry.Cohomology.ProperOverBase.Functoriality
public import StacksFrontier.AlgebraicGeometry.Etale.FShriekSubsheaf
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZeroBaseChange.Localization
public import StacksFrontier.AlgebraicGeometry.Etale.SupportedSections
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.MorphismComposition
public import StacksFrontier.AlgebraicGeometry.Etale.FShriekOpenInclusion.RestrictionAdjunction
import all StacksFrontier.AlgebraicGeometry.Etale.FShriekOpenInclusion.RestrictionAdjunction

/-!
# Extending a section with proper support by zero along an open immersion

Let `f : X ⟶ Y` be a separated morphism locally of finite type in a big étale site and let
`j : X' ⟶ X` be an open immersion in that site. An abelian sheaf `F` on the small étale site
of `X` restricts to a sheaf `F'` on the small étale site of `X'`. A section of the
proper-support direct image `(j ≫ f)_! F'` extends by zero to a section of `f_! F`: its
support is proper over the test object, hence closed in the fibre product, so the section and
the zero section on the complement of that support glue. This file proves the elementary facts
on supports used for this (supports of `0`, `-s` and `s - t`, sums and negatives of sections
with proper support, a section is determined by its restriction to an open containing its
support) and the existence of the extension.

## Main results

* `AlgebraicGeometry.SmallEtale.closedImmersion_of_proper_comp_separated`: a closed immersion
  into an open subscheme is a closed immersion of the ambient scheme as soon as the composite is
  proper over a separated base.
* `AlgebraicGeometry.SmallEtale.supportSection_neg_eq`: the support of `-s` is the support of
  `s`.

## References

* [Stacks Project, Tag 0F53](https://stacks.math.columbia.edu/tag/0F53)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u v

namespace AlgebraicGeometry.SmallEtale

/-- A closed immersion into an open subscheme is a closed immersion of the ambient scheme as
soon as the composite is proper over a separated base. -/
public theorem closedImmersion_of_proper_comp_separated
    {Z U' U V : Scheme.{u}} (i : Z ⟶ U') (k : U' ⟶ U) (p : U ⟶ V)
    [IsClosedImmersion i] [IsOpenImmersion k] [IsSeparated p]
    (h : IsProper (i ≫ k ≫ p)) : IsClosedImmersion (i ≫ k) := by
  have : IsProper ((i ≫ k) ≫ p) := by simpa [Category.assoc] using h
  exact (IsClosedImmersion.iff_isProper_and_mono (i ≫ k)).2
    ⟨IsProper.of_comp (i ≫ k) p, inferInstance⟩

private theorem scheme_range_comp {A B C : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C) :
    Set.range (f ≫ g).base = g.base '' Set.range f.base := by
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]

/-- The comparison isomorphism `pullback (f ≫ g) ≅ pullback g ⋙ pullback f` of pullback
functors between slice categories is compatible with the two projections: pulling back in two
steps and then projecting twice is projecting once along the composite. -/
theorem over_pullbackComp_fst
    {C : Type*} [Category C] {X Y Z : C}
    (f : X ⟶ Y) (g : Y ⟶ Z) [HasPullbacksAlong f] [HasPullbacksAlong g]
    (V : Over Z) :
    ((Over.pullbackComp f g).hom.app V).left ≫
        pullback.fst ((Over.pullback g).obj V).hom f ≫ pullback.fst V.hom g =
      pullback.fst V.hom (f ≫ g) := by
  have h := conjugateEquiv_counit (Over.mapPullbackAdj (f ≫ g))
      ((Over.mapPullbackAdj f).comp (Over.mapPullbackAdj g))
      (Over.mapComp f g).symm.hom V
  have h' : (Over.map f ⋙ Over.map g).map
      ((Over.pullbackComp f g).hom.app V) ≫
      ((Over.mapPullbackAdj f).comp (Over.mapPullbackAdj g)).counit.app V =
      (Over.mapComp f g).symm.hom.app ((Over.pullback (f ≫ g)).obj V) ≫
      (Over.mapPullbackAdj (f ≫ g)).counit.app V := by
    simpa [Over.pullbackComp] using h
  have hl := congrArg (fun k => k.left) h'
  simp [Over.mapPullbackAdj_counit_app, Over.mapComp, Over.pullbackComp]

private theorem supportSection_zero
    (B : BigEtaleSite.{u}) (X : Scheme.{u}) (hX : B.Contains X)
    (F : Sheaf (SmallEtale.topology B X hX) AddCommGrpCat.{v})
    (U : SmallEtale B X hX) :
    SmallEtale.supportSection B X hX F U 0 = ∅ := by
  have htop : SmallEtale.zeroOpen B X hX F U 0 = ⊤ := by
    apply le_antisymm le_top
    have hzero : F.obj.map (𝟙 U).op (0 : F.obj.obj (op U)) = 0 := by simp
    have h := (SmallEtale.map_eq_zero_iff_le_zeroOpen
      B X hX F U 0 U (𝟙 U)).mp hzero
    simpa [Scheme.Hom.opensRange_of_isIso] using h
  simp [SmallEtale.supportSection, htop]

/-- The support of `-s` is the support of `s`. -/
public theorem supportSection_neg_eq (B : BigEtaleSite.{u})
    (X : Scheme.{u}) (hX : B.Contains X)
    (F : Sheaf (SmallEtale.topology B X hX) AddCommGrpCat.{v})
    (U : SmallEtale B X hX) (s : F.obj.obj (op U)) :
    SmallEtale.supportSection B X hX F U (-s) =
      SmallEtale.supportSection B X hX F U s := by
  simp [SmallEtale.supportSection, zeroOpen_neg]

private theorem supportSection_sub_subset (B : BigEtaleSite.{u})
    (X : Scheme.{u}) (hX : B.Contains X)
    (F : Sheaf (SmallEtale.topology B X hX) AddCommGrpCat.{v})
    (U : SmallEtale B X hX) (s t : F.obj.obj (op U)) :
    SmallEtale.supportSection B X hX F U (s - t) ⊆
      SmallEtale.supportSection B X hX F U s ∪
        SmallEtale.supportSection B X hX F U t := by
  calc
    _ = SmallEtale.supportSection B X hX F U (s + -t) := by
      rw [sub_eq_add_neg]
    _ ⊆ SmallEtale.supportSection B X hX F U s ∪
        SmallEtale.supportSection B X hX F U (-t) :=
      SmallEtale.supportSection_add_subset B X hX F U s (-t)
    _ = SmallEtale.supportSection B X hX F U s ∪
        SmallEtale.supportSection B X hX F U t := by
      rw [supportSection_neg_eq]

/-- A base-change-stable property of `g` passes to the projection of its pullback along any
object over the target, after applying the inclusion of the big étale site. -/
private theorem inclusion_map_pullback_fst_of_isStableUnderBaseChange
    (B : BigEtaleSite.{u}) (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
    {X Y : B.Scheme} (V : SmallEtale B Y.obj Y.property) (g : X ⟶ Y) (hg : P (B.inclusion.map g)) :
    P (B.inclusion.map (pullback.fst V.obj.hom g)) := by
  let := hasPullbacks_bigEtaleSite B
  let : PreservesLimitsOfShape WalkingCospan B.inclusion :=
    preservesPullbacks_bigEtaleSiteInclusion B
  exact MorphismProperty.of_isPullback
    (IsPullback.map B.inclusion (IsPullback.of_hasPullback V.obj.hom g).flip) hg

private theorem properSupportSections_add
    (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)
    [LocallyOfFiniteType (B.inclusion.map f)]
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{v})
    (V : SmallEtale B Y.obj Y.property)
    (s t : F.obj.obj (op ((smallEtaleBaseChange B f).obj V)))
    (hs : SmallEtale.properSupportSections B f F V s)
    (ht : SmallEtale.properSupportSections B f F V t) :
    SmallEtale.properSupportSections B f F V (s + t) := by
  let U := (smallEtaleBaseChange B f).obj V
  let p := B.inclusion.map (pullback.fst V.obj.hom f)
  let : LocallyOfFiniteType p :=
    inclusion_map_pullback_fst_of_isStableUnderBaseChange B @LocallyOfFiniteType V f
      inferInstance
  let Zs : TopologicalSpace.Closeds ((SmallEtale.toScheme B X.obj X.property).obj U) :=
    (SmallEtale.zeroOpen B X.obj X.property F U s).compl
  let Zt : TopologicalSpace.Closeds ((SmallEtale.toScheme B X.obj X.property).obj U) :=
    (SmallEtale.zeroOpen B X.obj X.property F U t).compl
  change IsProperOver p Zs at hs
  change IsProperOver p Zt at ht
  have hsup : IsProperOver p (Zs ⊔ Zt) := by
    have h := isProperOver_iSup p
      (fun b : Bool => if b then Zs else Zt) (by
        intro b
        cases b with
        | false => simpa [Zt] using ht
        | true => simpa [Zs] using hs)
    simpa [iSup_bool_eq] using h
  exact isProperOver_of_le p (SmallEtale.supportSection_add_subset B X.obj X.property F U s t)
    hsup

private theorem properSupportSections_neg
    (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)
    [LocallyOfFiniteType (B.inclusion.map f)]
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{v})
    (V : SmallEtale B Y.obj Y.property)
    (s : F.obj.obj (op ((smallEtaleBaseChange B f).obj V)))
    (hs : SmallEtale.properSupportSections B f F V s) :
    SmallEtale.properSupportSections B f F V (-s) := by
  change IsProper ((Scheme.IdealSheafData.vanishingIdeal
    (SmallEtale.zeroOpen B X.obj X.property F
      ((smallEtaleBaseChange B f).obj V) (-s)).compl).subschemeι ≫
      B.inclusion.map (pullback.fst V.obj.hom f))
  rw [zeroOpen_neg]
  exact hs

private theorem restriction_eq_zero_of_support_subset
    (B : BigEtaleSite.{u}) (X : Scheme.{u}) (hX : B.Contains X)
    (F : Sheaf (SmallEtale.topology B X hX) AddCommGrpCat.{v})
    (U U' : SmallEtale B X hX) (φ : U' ⟶ U)
    [IsOpenImmersion ((SmallEtale.toScheme B X hX).map φ)]
    (s : F.obj.obj (op U))
    (hs : SmallEtale.supportSection B X hX F U s ⊆
      Set.range ((SmallEtale.toScheme B X hX).map φ).base)
    (hzero : F.obj.map φ.op s = 0) : s = 0 := by
  let φs := (SmallEtale.toScheme B X hX).map φ
  let Z : TopologicalSpace.Closeds ((SmallEtale.toScheme B X hX).obj U) :=
    ⟨SmallEtale.supportSection B X hX F U s,
      SmallEtale.isClosed_supportSection B X hX F U s⟩
  let Z' : TopologicalSpace.Closeds ((SmallEtale.toScheme B X hX).obj U') :=
    ⟨Set.preimage φs.base (Z : Set _), Z.isClosed.preimage φs.continuous⟩
  let Zi := Scheme.IdealSheafData.vanishingIdeal Z'
  let i' : Zi.subscheme ⟶ (SmallEtale.toScheme B X hX).obj U' := Zi.subschemeι
  let : IsClosedImmersion i' := inferInstance
  have hi : Set.range i'.base = (Z' : Set _) := by
    rw [Scheme.IdealSheafData.range_subschemeι,
      Scheme.IdealSheafData.coe_support_vanishingIdeal]
  have hcomp : Set.range (i' ≫ φs).base = (Z : Set _) := by
    rw [scheme_range_comp, hi]
    exact Set.image_preimage_eq_of_subset hs
  let : IsPreimmersion (i' ≫ φs) := inferInstance
  let : IsClosedImmersion (i' ≫ φs) :=
    IsClosedImmersion.of_isPreimmersion _ (hcomp ▸ Z.isClosed)
  have hpre : Set.preimage φs.base (Set.range (i' ≫ φs).base) =
      Set.preimage ((SmallEtale.toScheme B X hX).map (𝟙 U')).base (Set.range i'.base) := by
    rw [hcomp, hi]
    rfl
  have ht : SmallEtale.supportSection B X hX F U s ⊆
      Set.range (i' ≫ φs).base := by
    rw [hcomp]
    exact subset_rfl
  let E := SmallEtale.supportedSectionsEquiv B X hX F U U' φ Zi.subscheme i'
  let t : {a : F.obj.obj (op U) //
      SmallEtale.supportSection B X hX F U a ⊆
        Set.range (i' ≫ φs).base} := ⟨s, ht⟩
  let z : {a : F.obj.obj (op U) //
      SmallEtale.supportSection B X hX F U a ⊆
        Set.range (i' ≫ φs).base} := ⟨0, by simp [supportSection_zero]⟩
  have htres := SmallEtale.supportedSectionsEquiv_restrict B X hX F U U' φ
    Zi.subscheme i' U' (𝟙 U') hpre t
  have hzres := SmallEtale.supportedSectionsEquiv_restrict B X hX F U U' φ
    Zi.subscheme i' U' (𝟙 U') hpre z
  have hval : (E t).val = (E z).val := by
    have htres' : (E t).val = F.obj.map φ.op t.val := by simpa using htres
    have hzres' : (E z).val = F.obj.map φ.op z.val := by simpa using hzres
    rw [htres', hzres']
    simpa [t, z] using hzero
  exact congrArg Subtype.val (E.injective (Subtype.ext hval))

private theorem section_eq_of_restrict_eq (B : BigEtaleSite.{u})
    (X : Scheme.{u}) (hX : B.Contains X)
    (F : Sheaf (SmallEtale.topology B X hX) AddCommGrpCat.{v})
    (U U' : SmallEtale B X hX) (φ : U' ⟶ U)
    [IsOpenImmersion ((SmallEtale.toScheme B X hX).map φ)]
    (s t : F.obj.obj (op U))
    (hs : SmallEtale.supportSection B X hX F U s ⊆
      Set.range ((SmallEtale.toScheme B X hX).map φ).base)
    (ht : SmallEtale.supportSection B X hX F U t ⊆
      Set.range ((SmallEtale.toScheme B X hX).map φ).base)
    (hres : F.obj.map φ.op s = F.obj.map φ.op t) : s = t := by
  have hzero : F.obj.map φ.op (s - t) = 0 := by
    rw [map_sub, hres, sub_self]
  have hsub : SmallEtale.supportSection B X hX F U (s - t) ⊆
      Set.range ((SmallEtale.toScheme B X hX).map φ).base :=
    (supportSection_sub_subset B X hX F U s t).trans (Set.union_subset hs ht)
  exact sub_eq_zero.mp
    (restriction_eq_zero_of_support_subset B X hX F U U' φ (s - t) hsub hzero)

private theorem openInclusionExtendSection_exists
    (B : BigEtaleSite.{u}) {X' X Y : B.Scheme}
    (j : X' ⟶ X) (f : X ⟶ Y)
    [IsOpenImmersion (B.inclusion.map j)]
    [IsSeparated (B.inclusion.map f)]
    [LocallyOfFiniteType (B.inclusion.map f)]
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{v})
    (V : SmallEtale B Y.obj Y.property)
    (sOld : ((((smallEtaleBaseChange B j).sheafPullback AddCommGrpCat.{v}
      (SmallEtale.topology B X.obj X.property)
      (SmallEtale.topology B X'.obj X'.property)).obj F).obj.obj
        (op ((smallEtaleBaseChange B (j ≫ f)).obj V))))
    (hsOld : SmallEtale.properSupportSections B (j ≫ f)
      (((smallEtaleBaseChange B j).sheafPullback AddCommGrpCat.{v}
        (SmallEtale.topology B X.obj X.property)
        (SmallEtale.topology B X'.obj X'.property)).obj F) V sOld) :
    let F' := ((smallEtaleBaseChange B j).sheafPullback AddCommGrpCat.{v}
      (SmallEtale.topology B X.obj X.property)
      (SmallEtale.topology B X'.obj X'.property)).obj F
    ∃ s : F.obj.obj (op ((smallEtaleBaseChange B f).obj V)),
      SmallEtale.supportSection B X.obj X.property F
          ((smallEtaleBaseChange B f).obj V) s =
        (B.inclusion.map (pullback.fst
          ((smallEtaleBaseChange B f).obj V).obj.hom j)).base ''
        SmallEtale.supportSection B X'.obj X'.property F'
            ((smallEtaleBaseChange B j).obj ((smallEtaleBaseChange B f).obj V))
            (F'.obj.map
              ((smallEtaleBaseChange_compIso B X' X Y j f).val.hom.app V).op
              sOld) ∧
      SmallEtale.properSupportSections B f F V s ∧
      F'.obj.map
          ((smallEtaleBaseChange_compIso B X' X Y j f).val.hom.app V).op sOld =
        (((smallEtaleBaseChange B j).sheafAdjunctionContinuous AddCommGrpCat.{v}
          (SmallEtale.topology B X.obj X.property)
          (SmallEtale.topology B X'.obj X'.property)).unit.app F).hom.app
        (op ((smallEtaleBaseChange B f).obj V)) s := by
  let F' := ((smallEtaleBaseChange B j).sheafPullback AddCommGrpCat.{v}
    (SmallEtale.topology B X.obj X.property)
    (SmallEtale.topology B X'.obj X'.property)).obj F
  let : LocallyOfFiniteType (B.inclusion.map (j ≫ f)) := by
    change LocallyOfFiniteType (B.inclusion.map j ≫ B.inclusion.map f)
    infer_instance
  let W := (smallEtaleBaseChange B f).obj V
  let W' := (smallEtaleBaseChange B j).obj W
  let Wold := (smallEtaleBaseChange B (j ≫ f)).obj V
  let e := (smallEtaleBaseChange_compIso B X' X Y j f).val
  let eHom := e.hom.app V
  let eInv := e.inv.app V
  let T' := SmallEtale.toScheme B X'.obj X'.property
  let eHomS := T'.map eHom
  let eInvS := T'.map eInv
  let sNew := F'.obj.map eHom.op sOld
  let post := postcompose B j
  let U' := post.obj W'
  let φ := openBaseChangeMap B j W
  let PF := (post.sheafPushforwardContinuous AddCommGrpCat.{v}
    (SmallEtale.topology B X'.obj X'.property)
    (SmallEtale.topology B X.obj X.property)).obj F
  let eOpen := (openRestrictionIso B j).app F
  let t' := eOpen.inv.hom.app (op W') sNew
  have hU' : (SmallEtale.toScheme B X.obj X.property).obj U' =
      T'.obj ((smallEtaleBaseChange B f ⋙ smallEtaleBaseChange B j).obj V) := by
    dsimp [U', post, postcompose, smallEtalePostcompose, W', W, T']
  let eInvToU := eInvS ≫ eqToHom hU'.symm
  have hCast : eqToHom hU'.symm = 𝟙 _ := by
    cases hU'
    rfl
  let φs : (SmallEtale.toScheme B X.obj X.property).obj U' ⟶
      (SmallEtale.toScheme B X.obj X.property).obj W := by
    change (SmallEtale.toScheme B X.obj X.property).obj
      ((postcompose B j).obj ((smallEtaleBaseChange B j).obj W)) ⟶ _
    exact (SmallEtale.toScheme B X.obj X.property).map φ
  have hInv : (SmallEtale.inclusion B X'.obj X'.property).map eInv =
      (Over.pullbackComp j f).hom.app V.obj := by
    have he := smallEtaleBaseChange_compIso_app B X' X Y j f V
    apply (cancel_mono ((SmallEtale.inclusion B X'.obj X'.property).map eHom)).1
    have h₁ : (SmallEtale.inclusion B X'.obj X'.property).map eInv ≫
        (SmallEtale.inclusion B X'.obj X'.property).map eHom = 𝟙 _ := by
      rw [← Functor.map_comp]
      simp [eInv, eHom, e]
    have h₂ : (Over.pullbackComp j f).hom.app V.obj ≫
        (SmallEtale.inclusion B X'.obj X'.property).map eHom = 𝟙 _ := by
      rw [he]
      simp
    exact h₁.trans h₂.symm
  have hfgB :
      ((SmallEtale.inclusion B X'.obj X'.property).map eInv).left ≫
          pullback.fst ((Over.pullback f).obj V.obj).hom j ≫
            pullback.fst V.obj.hom f =
        pullback.fst V.obj.hom (j ≫ f) := by
    rw [congrArg (fun g => g.left) hInv]
    exact over_pullbackComp_fst j f V.obj
  have hInvS : eInvS = B.inclusion.map ((Over.pullbackComp j f).hom.app V.obj).left := by
    change B.inclusion.map ((SmallEtale.inclusion B X'.obj X'.property).map eInv).left = _
    exact congrArg (fun g => B.inclusion.map g.left) hInv
  have hφs : φs = B.inclusion.map (pullback.fst W.obj.hom j) := by
    dsimp [φs, φ, openBaseChangeMap]
    rfl
  have hWobj : W.obj = (Over.pullback f).obj V.obj :=
    smallEtaleBaseChange_obj_obj B f V
  have hOldObj : T'.obj ((smallEtaleBaseChange B (j ≫ f)).obj V) =
      B.inclusion.obj (pullback (Over.hom V.obj) (j ≫ f)) := by
    dsimp [T', SmallEtale.toScheme, BigEtaleOver.toScheme]
  have hfg1 :
      ((Over.pullbackComp j f).hom.app V.obj).left ≫
          pullback.fst W.obj.hom j ≫ pullback.fst V.obj.hom f =
        pullback.fst V.obj.hom (j ≫ f) := by
    cases hWobj
    exact over_pullbackComp_fst j f V.obj
  let pOld := B.inclusion.map (pullback.fst V.obj.hom (j ≫ f))
  let p := B.inclusion.map (pullback.fst V.obj.hom f)
  let k := eInvToU ≫ φs
  have hfg : k ≫ p = pOld := by
    cases hWobj
    dsimp [k, p, pOld, eInvToU]
    rw [hCast, hInvS, hφs]
    have hm := congrArg B.inclusion.map hfg1
    simp only [B.inclusion.map_comp] at hm ⊢
    exact hm
  let Zold : TopologicalSpace.Closeds
      ((SmallEtale.toScheme B X'.obj X'.property).obj Wold) :=
    ⟨SmallEtale.supportSection B X'.obj X'.property F' Wold sOld,
      SmallEtale.isClosed_supportSection
        B X'.obj X'.property F' Wold sOld⟩
  have hleft : eHomS ≫ eInvS = 𝟙 _ := by
    have h : eHom ≫ eInv = 𝟙 _ := by simp [eHom, eInv, e]
    change T'.map eHom ≫ T'.map eInv = _
    rw [← T'.map_comp, h]
    simp
  have hright : eInvS ≫ eHomS = 𝟙 _ := by
    have h : eInv ≫ eHom = 𝟙 _ := by simp [eHom, eInv, e]
    change T'.map eInv ≫ T'.map eHom = _
    rw [← T'.map_comp, h]
    simp
  let iOld := (Scheme.IdealSheafData.vanishingIdeal Zold).subschemeι
  have hiOld : Set.range iOld.base = (Zold : Set _) := by
    rw [Scheme.IdealSheafData.range_subschemeι,
      Scheme.IdealSheafData.coe_support_vanishingIdeal]
  let i := iOld ≫ eInvToU
  let eSupport :
      SmallEtale.supportSection B X'.obj X'.property F' W' sNew =
        Set.image eInvS.base (Zold : Set _) := by
    have hres := supportSection_restrict_eq B X'.obj X'.property F' Wold W' eHom sOld
    have hset : Set.image eInvS.base (Zold : Set _) =
        Set.preimage eHomS.base (Zold : Set _) :=
      congrFun (Set.image_eq_preimage_of_inverse
        (fun y => by simpa using congrArg (fun g => g.base y) hright)
        (fun x => by simpa using congrArg (fun g => g.base x) hleft)) _
    calc
      _ = Set.preimage eHomS.base
          (SmallEtale.supportSection B X'.obj X'.property F' Wold sOld) := hres
      _ = Set.preimage eHomS.base (Zold : Set _) := rfl
      _ = Set.image eInvS.base (Zold : Set _) := hset.symm
  have hIsoApp : eOpen.hom.hom.app (op W') t' = sNew := by
    dsimp [t']
    rw [← ConcreteCategory.comp_apply]
    simp
  have hIsoSupport := supportSection_iso_app_eq B X'.obj X'.property PF F'
    eOpen W' t'
  rw [hIsoApp] at hIsoSupport
  have hPostSupport := supportSection_postcompose_eq B j F W' t'
  have hTransfer :
      SmallEtale.supportSection B X.obj X.property F U' t' =
        SmallEtale.supportSection B X'.obj X'.property F' W' sNew := by
    calc
      _ = SmallEtale.supportSection B X'.obj X'.property
            ((post.sheafPushforwardContinuous AddCommGrpCat.{v}
              (SmallEtale.topology B X'.obj X'.property)
              (SmallEtale.topology B X.obj X.property)).obj F) W' t' :=
          hPostSupport.symm
      _ = SmallEtale.supportSection B X'.obj X'.property F' W' sNew :=
          hIsoSupport.symm
  have hSupportI :
      SmallEtale.supportSection B X.obj X.property F U' t' =
        Set.range i.base := by
    rw [hTransfer, eSupport]
    change Set.image eInvS.base (Zold : Set _) =
      Set.range (iOld ≫ eInvS).base
    rw [scheme_range_comp, hiOld]
  let : IsClosedImmersion iOld := inferInstance
  let : IsIso eInvS := by
    dsimp [eInvS]
    infer_instance
  let : IsClosedImmersion i := inferInstance
  let sSub : {a : F.obj.obj (op U') //
      SmallEtale.supportSection B X.obj X.property F U' a ⊆
        Set.range i.base} := ⟨t', by rw [hSupportI]⟩
  let : IsClosedImmersion i := inferInstance
  let : IsOpenImmersion ((SmallEtale.toScheme B X.obj X.property).map φ) :=
    openBaseChangeMap_isOpenImmersion B j W
  let : IsOpenImmersion φs := openBaseChangeMap_isOpenImmersion B j W
  let : LocallyOfFiniteType pOld :=
    inclusion_map_pullback_fst_of_isStableUnderBaseChange B @LocallyOfFiniteType V (j ≫ f)
      inferInstance
  let : LocallyOfFiniteType p :=
    inclusion_map_pullback_fst_of_isStableUnderBaseChange B @LocallyOfFiniteType V f
      inferInstance
  have hpSeparated : IsSeparated p :=
    inclusion_map_pullback_fst_of_isStableUnderBaseChange B @IsSeparated V f inferInstance
  let : IsClosedImmersion (i ≫ (SmallEtale.toScheme B X.obj X.property).map φ) := by
    have hcompProper : IsProper (i ≫ (SmallEtale.toScheme B X.obj X.property).map φ ≫ p) := by
      change IsProper ((iOld ≫ eInvToU) ≫ φs ≫ p)
      have hcomp : (iOld ≫ eInvToU) ≫ φs ≫ p = iOld ≫ pOld := by
        calc
          _ = iOld ≫ ((eInvToU ≫ φs) ≫ p) :=
            congrArg (fun q => q ≫ p) (Category.assoc iOld eInvToU φs)
          _ = iOld ≫ pOld := by rw [hfg]
      rw [hcomp]
      exact hsOld
    exact @closedImmersion_of_proper_comp_separated _ _ _ _ i φs p
      inferInstance inferInstance hpSeparated hcompProper
  let s := (extendSupportedSection B X.obj X.property F W U' φ
    (Scheme.IdealSheafData.vanishingIdeal Zold).subscheme i sSub).val
  have hsOpen : F.obj.map φ.op s = t' :=
    extendSupportedSection_restrict B X.obj X.property F W U' φ
      (Scheme.IdealSheafData.vanishingIdeal Zold).subscheme i sSub
  have hsUnit : F'.obj.map eHom.op sOld =
      (((smallEtaleBaseChange B j).sheafAdjunctionContinuous AddCommGrpCat.{v}
        (SmallEtale.topology B X.obj X.property)
        (SmallEtale.topology B X'.obj X'.property)).unit.app F).hom.app (op W) s := by
    have hUnit' : eOpen.hom.hom.app (op W') (F.obj.map φ.op s) =
        (((smallEtaleBaseChange B j).sheafAdjunctionContinuous AddCommGrpCat.{v}
          (SmallEtale.topology B X.obj X.property)
          (SmallEtale.topology B X'.obj X'.property)).unit.app F).hom.app (op W) s := by
      simpa [eOpen, W'] using openRestrictionIso_unit_app B j F W s
    change sNew = _
    have h1 : sNew = eOpen.hom.hom.app (op W') (F.obj.map φ.op s) := by
      rw [hsOpen]
      exact hIsoApp.symm
    exact h1.trans hUnit'
  have hsupp : SmallEtale.supportSection B X.obj X.property F W s =
      (B.inclusion.map (pullback.fst W.obj.hom j)).base ''
        SmallEtale.supportSection B X'.obj X'.property F' W' sNew := by
    have h := supportSection_extendSupportedSection_eq B X.obj X.property F W U' φ
      (Scheme.IdealSheafData.vanishingIdeal Zold).subscheme i sSub
    calc
      _ = ((SmallEtale.toScheme B X.obj X.property).map φ).base ''
          SmallEtale.supportSection B X.obj X.property F U' t' := h
      _ = (B.inclusion.map (pullback.fst W.obj.hom j)).base ''
          SmallEtale.supportSection B X'.obj X'.property F' W' sNew := by
        rw [hTransfer]
        rfl
  have hsProper : SmallEtale.properSupportSections B f F V s := by
    have hproper : IsProperOver pOld Zold := by
      change IsProper ((Scheme.IdealSheafData.vanishingIdeal Zold).subschemeι ≫ pOld)
      exact hsOld
    let Zimage : TopologicalSpace.Closeds _ :=
      ⟨k.base '' (Zold : Set _),
        isClosed_image_of_isProperOver
          pOld p k hfg Zold hproper⟩
    have himage := isProperOver_image
      pOld p k hfg Zold hproper
    have hcarrier : SmallEtale.supportSection B X.obj X.property F W s =
        k.base '' (Zold : Set _) := by
      calc
        _ = φs.base '' SmallEtale.supportSection B X.obj X.property F U' t' := by
          rw [hsupp, ← hTransfer, hφs]
          rfl
        _ = φs.base '' Set.range i.base := by rw [hSupportI]
        _ = Set.range (i ≫ φs).base := (scheme_range_comp i φs).symm
        _ = Set.range (iOld ≫ k).base := by
          have hassoc : i ≫ φs = iOld ≫ k := by
            dsimp [i, k]
            exact Category.assoc iOld eInvToU φs
          exact congrArg (fun q => Set.range q.base) hassoc
        _ = k.base '' (Zold : Set _) := by rw [scheme_range_comp, hiOld]
    have hZ : (⟨SmallEtale.supportSection B X.obj X.property F W s,
        SmallEtale.isClosed_supportSection
          B X.obj X.property F W s⟩ : TopologicalSpace.Closeds _) = Zimage :=
      TopologicalSpace.Closeds.ext hcarrier
    change IsProper ((Scheme.IdealSheafData.vanishingIdeal
      (⟨SmallEtale.supportSection B X.obj X.property F W s,
        SmallEtale.isClosed_supportSection
          B X.obj X.property F W s⟩ : TopologicalSpace.Closeds _)).subschemeι ≫ p)
    rw [hZ]
    exact himage
  exact ⟨s, hsupp, hsProper, hsUnit⟩

end AlgebraicGeometry.SmallEtale

end
