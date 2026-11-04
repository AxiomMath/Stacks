module

public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Cancellation
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FiniteTypeLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Scheme.Glueing.DoubledOriginBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteHullOfIntegral
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.FinitePart.AlgebraicSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.ThickeningAffineOverAffineBase.PresentationLift
public import StacksFrontier.RingTheory.Flat.TruncatedPolynomial

/-!
# The doubled origin: pairs of the finite part read on schemes

Preliminaries for Stacks 04QI (`AlgebraicGeometry.Space.doubledOrigin_finitePart`): base change
of the pairs of Stacks 04PC read through factorizations, morphisms of schemes read as morphisms
of algebraic spaces (`schemeSpaceMap_hom_comp`, `schemeSpaceMap_hom_id`), the open subspace of a
pair for a morphism of the site as the range of an open subscheme of the pullback of the site
(`FiniteOpenSubspace.exists_eq_range`, `wholeFiniteOpenSubspace`), and the doubled origin as a
morphism of the big fppf site of `Spec k` (`doubledCoordHom`, `doubledOriginFinitePart`,
`chartSection`).
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

/-! ### Base change of pairs, read through factorizations -/

namespace FiniteOpenSubspace

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X Y : AlgebraicSpaces B S hS} {f : X ⟶ Y}

/-- Two pairs of Stacks 04PC over the same algebraic space with the same morphism to the target
are equal as soon as both open subspaces are everything. -/
theorem ext_of_subspace_eq_top {T : AlgebraicSpaces B S hS}
    {p q : FiniteOpenSubspace B S hS f T} (h : p.toBase = q.toBase)
    (hp : p.subspace = ⊤) (hq : q.subspace = ⊤) : p = q := by
  rcases p with ⟨a, Z, hZ, hZf⟩
  rcases q with ⟨b, Z', hZ', hZf'⟩
  dsimp only at h hp hq
  subst h
  have hZZ : Z = Z' := hp.trans hq.symm
  subst hZZ
  rfl

namespace IsBaseChange

variable {T T' : BigFppfOver B S hS} {h : T' ⟶ T}
  {p : FiniteOpenSubspace B S hS f (schemeSpace T)}
  {q : FiniteOpenSubspace B S hS f (schemeSpace T')}

/-- The comparison of morphisms to the target carried by a base change of pairs, with the
morphism of the base read as a morphism of algebraic spaces. -/
theorem toBase_hom_eq (hpq : IsBaseChange B S hS f h p q) :
    q.toBase.hom = (schemeSpaceMap h).hom ≫ p.toBase.hom :=
  hpq.1

/-- The canonical morphism `T' ×_Y X ⟶ T ×_Y X` of ambient fibre products underlying a base
change of pairs: `h` on the first factor and the identity on `X`. -/
noncomputable def ambientMap (hpq : IsBaseChange B S hS f h p q) :
    pullback q.toBase.hom f.hom ⟶ pullback p.toBase.hom f.hom :=
  pullback.map _ _ _ _ (schemeSpaceMap h).hom (𝟙 _) (𝟙 _)
    (by rw [Category.comp_id, hpq.toBase_hom_eq]) (by rw [Category.id_comp, Category.comp_id])

/-- The first projection of `ambientMap` is the first projection followed by `h`. -/
@[reassoc (attr := simp)]
theorem ambientMap_fst (hpq : IsBaseChange B S hS f h p q) :
    hpq.ambientMap ≫ pullback.fst p.toBase.hom f.hom =
      pullback.fst q.toBase.hom f.hom ≫ (schemeSpaceMap h).hom :=
  pullback.lift_fst _ _ _

/-- The second projection of `ambientMap` is the second projection. -/
@[reassoc (attr := simp)]
theorem ambientMap_snd (hpq : IsBaseChange B S hS f h p q) :
    hpq.ambientMap ≫ pullback.snd p.toBase.hom f.hom = pullback.snd q.toBase.hom f.hom := by
  rw [ambientMap, pullback.lift_snd, Category.comp_id]

/-- The open subspace of a base change of a pair is the preimage of the original one, read
through factorizations: a morphism into `T' ×_Y X` factors through the new open subspace exactly
when its composite with the canonical morphism to `T ×_Y X` factors through the original one. -/
theorem exists_comp_ι_eq_iff (hpq : IsBaseChange B S hS f h p q)
    {G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (s : G ⟶ pullback q.toBase.hom f.hom) :
    (∃ l, l ≫ q.subspace.ι = s) ↔ ∃ l, l ≫ p.subspace.ι = s ≫ hpq.ambientMap := by
  obtain ⟨j, sq₀, hj⟩ := hpq.2
  have sq : IsPullback (q.subspace.ι ≫ pullback.fst q.toBase.hom f.hom) j
      (schemeSpaceMap h).hom (p.subspace.ι ≫ pullback.fst p.toBase.hom f.hom) := sq₀
  have w : j ≫ p.subspace.ι ≫ pullback.fst p.toBase.hom f.hom =
      q.subspace.ι ≫ pullback.fst q.toBase.hom f.hom ≫ (schemeSpaceMap h).hom := by
    simpa only [Category.assoc] using sq.w.symm
  constructor
  · rintro ⟨l, rfl⟩
    refine ⟨l ≫ j, pullback.hom_ext ?_ ?_⟩
    · rw [Category.assoc, Category.assoc, w, Category.assoc, Category.assoc, ambientMap_fst]
    · rw [Category.assoc, Category.assoc, hj, Category.assoc, Category.assoc, ambientMap_snd]
  · rintro ⟨l, hl⟩
    have hw : (s ≫ pullback.fst q.toBase.hom f.hom) ≫ (schemeSpaceMap h).hom =
        l ≫ p.subspace.ι ≫ pullback.fst p.toBase.hom f.hom := by
      rw [← Category.assoc l, hl, Category.assoc, Category.assoc, ambientMap_fst]
    refine ⟨sq.lift _ _ hw, pullback.hom_ext ?_ ?_⟩
    · rw [Category.assoc, sq.lift_fst]
    · rw [Category.assoc, ← hj, ← Category.assoc, sq.lift_snd, ← Category.assoc l, hl,
        Category.assoc, ambientMap_snd]

/-- The base change of a pair whose open subspace is everything has open subspace everything. -/
theorem subspace_eq_top (hpq : IsBaseChange B S hS f h p q) (hp : p.subspace = ⊤) :
    q.subspace = ⊤ := by
  obtain ⟨l, hl⟩ := (hpq.exists_comp_ι_eq_iff (𝟙 _)).mpr
    ⟨Subfunctor.lift (𝟙 _ ≫ hpq.ambientMap) (by rw [hp]; exact le_top), Subfunctor.lift_ι _ _⟩
  have : Epi q.subspace.ι := epi_of_epi_fac hl
  rw [← Subfunctor.range_ι q.subspace, Subfunctor.range_eq_top]

end IsBaseChange

end FiniteOpenSubspace



/-! ### Morphisms of schemes read as morphisms of algebraic spaces -/

section SchemeSpaceMap

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The morphism of presheaves underlying `AlgebraicGeometry.schemeSpaceMap` is functorial. -/
@[reassoc]
theorem schemeSpaceMap_hom_comp {U V W : BigFppfOver B S hS} (g : U ⟶ V) (g' : V ⟶ W) :
    (schemeSpaceMap g).hom ≫ (schemeSpaceMap g').hom = (schemeSpaceMap (g ≫ g')).hom :=
  (yoneda.map_comp g g').symm

/-- The morphism of presheaves underlying `AlgebraicGeometry.schemeSpaceMap` preserves
identities. -/
theorem schemeSpaceMap_hom_id (U : BigFppfOver B S hS) :
    (schemeSpaceMap (𝟙 U)).hom = 𝟙 _ :=
  yoneda.map_id U

end SchemeSpaceMap


/-- A morphism factors through the inclusion of the range of a monomorphism exactly when it
factors through the monomorphism. -/
theorem _root_.CategoryTheory.Subfunctor.exists_comp_range_ι_eq_iff {C : Type*} [Category C]
    {F F' G : C ⥤ Type u} (g : F' ⟶ F) [Mono g] (t : G ⟶ F) :
    (∃ l, l ≫ (Subfunctor.range g).ι = t) ↔ ∃ l, l ≫ g = t := by
  constructor
  · rintro ⟨l, rfl⟩
    have h : inv (Subfunctor.toRange g) ≫ g = (Subfunctor.range g).ι := by
      rw [IsIso.inv_comp_eq, Subfunctor.toRange_ι]
    exact ⟨l ≫ inv (Subfunctor.toRange g), by rw [Category.assoc, h]⟩
  · rintro ⟨l, rfl⟩
    exact ⟨l ≫ Subfunctor.toRange g, by simp⟩

/-! ### Pairs for a morphism of the site, read on schemes -/

section Represent

attribute [local instance] BigFppfSite.hasPullbacks_schemes
  Space.preservesLimitsOfShape_walkingCospan_toScheme

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {Xs Ys : BigFppfOver B S hS}
  (fs : Xs ⟶ Ys)

/-- The pullback square of the site, read as a square of algebraic spaces, is a pullback of
presheaves. -/
theorem isPullback_schemeSpaceMap_pullback {T : BigFppfOver B S hS} (b : T ⟶ Ys) :
    IsPullback (schemeSpaceMap (pullback.fst b fs)).hom (schemeSpaceMap (pullback.snd b fs)).hom
      (schemeSpaceMap b).hom (schemeSpaceMap fs).hom :=
  (IsPullback.of_hasPullback b fs).map yoneda

/-- The identification of the representable presheaf of the pullback of the site with the
ambient fibre product of a pair whose morphism to the target is `b`. -/
noncomputable def ambientIso {T : BigFppfOver B S hS} (b : T ⟶ Ys)
    {α : schemeSpace T ⟶ schemeSpace Ys} (hα : α = schemeSpaceMap b) :
    (schemeSpace (pullback b fs)).obj ≅ pullback α.hom (schemeSpaceMap fs).hom :=
  (show IsPullback (schemeSpaceMap (pullback.fst b fs)).hom
      (schemeSpaceMap (pullback.snd b fs)).hom α.hom (schemeSpaceMap fs).hom by
    subst hα
    exact isPullback_schemeSpaceMap_pullback fs b).isoPullback

/-- The forward map of `ambientIso` followed by the first projection is the first projection of
the pullback of the site. -/
@[reassoc (attr := simp)]
theorem ambientIso_hom_fst {T : BigFppfOver B S hS} (b : T ⟶ Ys)
    {α : schemeSpace T ⟶ schemeSpace Ys} (hα : α = schemeSpaceMap b) :
    (ambientIso fs b hα).hom ≫ pullback.fst _ _ = (schemeSpaceMap (pullback.fst b fs)).hom :=
  IsPullback.isoPullback_hom_fst _

/-- The forward map of `ambientIso` followed by the second projection is the second projection
of the pullback of the site. -/
@[reassoc (attr := simp)]
theorem ambientIso_hom_snd {T : BigFppfOver B S hS} (b : T ⟶ Ys)
    {α : schemeSpace T ⟶ schemeSpace Ys} (hα : α = schemeSpaceMap b) :
    (ambientIso fs b hα).hom ≫ pullback.snd _ _ = (schemeSpaceMap (pullback.snd b fs)).hom :=
  IsPullback.isoPullback_hom_snd _

/-- A monomorphism of the site gives a monomorphism of presheaves into the ambient fibre product. -/
private theorem mono_schemeSpaceMap_hom_comp_ambientIso {T W : BigFppfOver B S hS}
    (b : T ⟶ Ys) (j : W ⟶ pullback b fs) [Mono j] {α : schemeSpace T ⟶ schemeSpace Ys}
    (hα : α = schemeSpaceMap b) : Mono ((schemeSpaceMap j).hom ≫ (ambientIso fs b hα).hom) :=
  have : Mono (yoneda.map j) := inferInstance
  @mono_comp _ _ _ _ _ (yoneda.map j) _ _ (IsIso.mono_of_iso (ambientIso fs b hα).hom)

/-- **Open subspaces of a pair, read on schemes.** The open subspace of a pair of Stacks 04PC over
`T` for a morphism `fs` of the site, with morphism `b` to the target, is the range of an open
subscheme of the pullback `T ×_Y X` of the site; when `T` is affine, that open subscheme is finite
over `T`. -/
theorem FiniteOpenSubspace.exists_eq_range {T : BigFppfOver B S hS}
    (z : FiniteOpenSubspace B S hS (schemeSpaceMap fs) (schemeSpace T)) (b : T ⟶ Ys)
    (hz : z.toBase = schemeSpaceMap b) :
    ∃ (W : BigFppfOver B S hS) (j : W ⟶ pullback b fs),
      _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map j) ∧
      z.subspace = Subfunctor.range ((schemeSpaceMap j).hom ≫ (ambientIso fs b hz).hom) ∧
      (IsAffine ((BigFppfOver.toScheme B S hS).obj T) →
        _root_.AlgebraicGeometry.IsFinite
          ((BigFppfOver.toScheme B S hS).map (j ≫ pullback.fst b fs))) := by
  set e := ambientIso fs b hz
  have hop := z.isOpen.2
  have sq := hop.rep.isPullback e.hom
  have : IsIso (hop.rep.fst e.hom) := sq.isIso_fst_of_isIso e.isIso_hom
  have hw : hop.rep.fst e.hom ≫ z.subspace.ι =
      (schemeSpaceMap (hop.rep.snd e.hom)).hom ≫ e.hom := sq.w
  refine ⟨hop.rep.pullback e.hom, hop.rep.snd e.hom, hop.property_snd e.hom, ?_, ?_⟩
  · calc z.subspace = Subfunctor.range z.subspace.ι := (Subfunctor.range_ι _).symm
      _ = Subfunctor.range (hop.rep.fst e.hom ≫ z.subspace.ι) := by
        rw [Subfunctor.range_comp, Subfunctor.range_eq_top (p := hop.rep.fst e.hom),
          Subfunctor.image_top]
      _ = _ := congrArg Subfunctor.range hw
  · intro hT
    let ξ : yoneda.obj T ⟶ (schemeSpace T).obj := 𝟙 (yoneda.obj T)
    obtain ⟨V, p, i, -, hp, sqV⟩ := z.finite_projection T hT ξ
    have : IsIso i := sqV.isIso_fst_of_isIso (IsIso.id _)
    have hi : i ≫ z.subspace.ι ≫ pullback.fst z.toBase.hom (schemeSpaceMap fs).hom =
        yoneda.map p :=
      sqV.w.trans (Category.comp_id _)
    set φ := yoneda.preimage (hop.rep.fst e.hom ≫ inv i)
    have hφ : yoneda.map φ = hop.rep.fst e.hom ≫ inv i := yoneda.map_preimage _
    have : IsIso (yoneda.map φ) := by rw [hφ]; infer_instance
    have : IsIso φ := Yoneda.fullyFaithful.isIso_of_isIso_map _
    have t2 : (schemeSpaceMap (pullback.fst b fs)).hom = e.hom ≫ pullback.fst _ _ :=
      (ambientIso_hom_fst fs b hz).symm
    have t4 : z.subspace.ι ≫ pullback.fst z.toBase.hom (schemeSpaceMap fs).hom =
        inv i ≫ yoneda.map p :=
      (IsIso.eq_inv_comp i).mpr hi
    have hfac : hop.rep.snd e.hom ≫ pullback.fst b fs = φ ≫ p := by
      refine yoneda.map_injective ?_
      exact (yoneda.map_comp _ _).trans <|
        (congrArg ((schemeSpaceMap (hop.rep.snd e.hom)).hom ≫ ·) t2).trans <|
        (Category.assoc _ _ _).symm.trans <|
        (congrArg (· ≫ pullback.fst z.toBase.hom (schemeSpaceMap fs).hom) hw.symm).trans <|
        (Category.assoc _ _ _).trans <|
        (congrArg (hop.rep.fst e.hom ≫ ·) t4).trans <|
        (Category.assoc _ _ _).symm.trans <|
        (congrArg (· ≫ yoneda.map p) hφ.symm).trans (yoneda.map_comp _ _).symm
    rw [hfac, CategoryTheory.Functor.map_comp]
    infer_instance

/-- The inclusion of the whole of a presheaf on the big fppf site, as a subfunctor, is an open
immersion. -/
theorem isOpenImmersion_top_ι (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :
    IsOpenImmersion B S hS (⊤ : Subfunctor F).ι := by
  have : (MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.IsOpenImmersion.{u})
      (BigFppfOver.toScheme B S hS)).RespectsIso :=
    MorphismProperty.RespectsIso.inverseImage _ _
  refine MorphismProperty.relative.of_exists (fun a g => ⟨a, g ≫ inv (⊤ : Subfunctor F).ι, 𝟙 a,
    IsPullback.of_vert_isIso ⟨by simp⟩, ?_⟩)
  rw [MorphismProperty.inverseImage_iff, CategoryTheory.Functor.map_id]
  infer_instance

/-- The pair of Stacks 04PC over `T` for the morphism of algebraic spaces underlying `fs`, whose
morphism to `Y` is `b` and whose open subspace is the whole of `T ×_Y X`; it exists as soon as the
base change of `fs` along `b` is finite. -/
noncomputable def wholeFiniteOpenSubspace {T : BigFppfOver B S hS} (b : T ⟶ Ys)
    (hb : _root_.AlgebraicGeometry.IsFinite
      ((BigFppfOver.toScheme B S hS).map (pullback.fst b fs))) :
    FiniteOpenSubspace B S hS (schemeSpaceMap fs) (schemeSpace T) where
  toBase := schemeSpaceMap b
  subspace := ⊤
  isOpen := ⟨AlgebraicGeometry.isAlgebraicSpace_of_iso B S hS
      (asIso (⊤ : Subfunctor (pullback (schemeSpaceMap b).hom (schemeSpaceMap fs).hom)).ι)
      (isAlgebraicSpace_pullback B S hS _ _ (schemeSpace T).property
        (schemeSpace Xs).property (schemeSpace Ys).property),
    isOpenImmersion_top_ι _⟩
  finite_projection := by
    let e := ambientIso fs b (rfl : schemeSpaceMap b = schemeSpaceMap b)
    have he : e.inv ≫ (schemeSpaceMap (pullback.fst b fs)).hom =
        pullback.fst (schemeSpaceMap b).hom (schemeSpaceMap fs).hom :=
      (Iso.inv_comp_eq e).mpr (ambientIso_hom_fst fs b _).symm
    have hk : IsIso
        ((⊤ : Subfunctor (pullback (schemeSpaceMap b).hom (schemeSpaceMap fs).hom)).ι ≫ e.inv) :=
      inferInstance
    exact isFinite_of_isPullback B S hS (f := (schemeSpaceMap (pullback.fst b fs)).hom)
      (g := 𝟙 (schemeSpace T).obj)
      (k := (⊤ : Subfunctor (pullback (schemeSpaceMap b).hom (schemeSpaceMap fs).hom)).ι ≫ e.inv)
      (IsPullback.of_horiz_isIso
        ⟨(Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) he).trans (Category.comp_id _).symm)⟩)
      (isFinite_yoneda_map_of_isFinite hb)

/-- The morphism to the target of `wholeFiniteOpenSubspace fs b hb` is the one underlying `b`. -/
@[simp]
theorem wholeFiniteOpenSubspace_toBase {T : BigFppfOver B S hS} (b : T ⟶ Ys)
    (hb : _root_.AlgebraicGeometry.IsFinite
      ((BigFppfOver.toScheme B S hS).map (pullback.fst b fs))) :
    (wholeFiniteOpenSubspace fs b hb).toBase = schemeSpaceMap b :=
  rfl

/-- The open subspace of `wholeFiniteOpenSubspace fs b hb` is the whole fibre product. -/
@[simp]
theorem wholeFiniteOpenSubspace_subspace {T : BigFppfOver B S hS} (b : T ⟶ Ys)
    (hb : _root_.AlgebraicGeometry.IsFinite
      ((BigFppfOver.toScheme B S hS).map (pullback.fst b fs))) :
    (wholeFiniteOpenSubspace fs b hb).subspace = ⊤ :=
  rfl


/-- **Factorizations through the open subscheme of a pair.** Let `z` be a pair of Stacks 04PC
over `T` with morphism `b` to the target, whose open subspace is the range of a monomorphism
`j : W ⟶ T ×_Y X` of the site. A morphism `y : A ⟶ T ×_Y X` of the site factors through `j`
as soon as the corresponding morphism of presheaves factors through the open subspace. -/
theorem FiniteOpenSubspace.exists_comp_eq_of_exists {T : BigFppfOver B S hS}
    {z : FiniteOpenSubspace B S hS (schemeSpaceMap fs) (schemeSpace T)} {b : T ⟶ Ys}
    (hz : z.toBase = schemeSpaceMap b) {W : BigFppfOver B S hS} {j : W ⟶ pullback b fs}
    [Mono j]
    (hzj : z.subspace = Subfunctor.range ((schemeSpaceMap j).hom ≫ (ambientIso fs b hz).hom))
    {A : BigFppfOver B S hS} (y : A ⟶ pullback b fs)
    (hy : ∃ l, l ≫ z.subspace.ι = (schemeSpaceMap y).hom ≫ (ambientIso fs b hz).hom) :
    ∃ g : A ⟶ W, g ≫ j = y := by
  set e := ambientIso fs b hz
  rw [hzj] at hy
  have := mono_schemeSpaceMap_hom_comp_ambientIso fs b j hz
  obtain ⟨m', hm'⟩ := (Subfunctor.exists_comp_range_ι_eq_iff _ _).mp hy
  have hm'' : m' ≫ (schemeSpaceMap j).hom = (schemeSpaceMap y).hom := by
    rw [← cancel_mono e.hom, Category.assoc, hm']
  refine ⟨yoneda.preimage m', yoneda.map_injective ?_⟩
  exact (yoneda.map_comp _ _).trans
    ((congrArg (· ≫ yoneda.map j) (yoneda.map_preimage m')).trans hm'')

/-- A morphism of the site whose underlying morphism of schemes has image inside the image of an
open immersion of the site factors through it. -/
theorem exists_comp_eq_of_range_subset {A W P : BigFppfOver B S hS} (j : W ⟶ P)
    [_root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map j)]
    (y : A ⟶ P)
    (hy : Set.range ((BigFppfOver.toScheme B S hS).map y) ⊆
      Set.range ((BigFppfOver.toScheme B S hS).map j)) :
    ∃ m : A ⟶ W, m ≫ j = y := by
  let q := BigFppfOver.toScheme B S hS
  let m₀ := IsOpenImmersion.lift (q.map j) (q.map y) hy
  have hm₀ : m₀ ≫ q.map j = q.map y := IsOpenImmersion.lift_fac _ _ _
  have hw : ObjectProperty.homMk m₀ ≫ W.hom = A.hom := by
    refine ObjectProperty.hom_ext _ ?_
    have h1 := congrArg (fun φ => φ.hom) (Over.w j)
    have h2 := congrArg (fun φ => φ.hom) (Over.w y)
    simp only [ObjectProperty.FullSubcategory.comp_hom] at h1 h2 ⊢
    rw [← h1, ← Category.assoc]
    exact (congrArg (· ≫ P.hom.hom) hm₀).trans h2
  exact ⟨Over.homMk (ObjectProperty.homMk m₀) hw, q.map_injective ((q.map_comp _ _).trans hm₀)⟩

/-- **Factorizations through the open subscheme of a pair, read on points.** Let `z` be a pair of
Stacks 04PC over `T` with morphism `b` to the target, whose open subspace is the range of an open
immersion `j : W ⟶ T ×_Y X` of the site. A morphism `y : A ⟶ T ×_Y X` of the site factors
through the open subspace exactly when its image lies in the image of `j`. -/
theorem FiniteOpenSubspace.exists_comp_ι_eq_iff_range_subset {T : BigFppfOver B S hS}
    {z : FiniteOpenSubspace B S hS (schemeSpaceMap fs) (schemeSpace T)} {b : T ⟶ Ys}
    (hz : z.toBase = schemeSpaceMap b) {W : BigFppfOver B S hS} {j : W ⟶ pullback b fs}
    [_root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map j)]
    (hzj : z.subspace = Subfunctor.range ((schemeSpaceMap j).hom ≫ (ambientIso fs b hz).hom))
    {A : BigFppfOver B S hS} (y : A ⟶ pullback b fs) :
    (∃ l, l ≫ z.subspace.ι = (schemeSpaceMap y).hom ≫ (ambientIso fs b hz).hom) ↔
      Set.range ((BigFppfOver.toScheme B S hS).map y) ⊆
        Set.range ((BigFppfOver.toScheme B S hS).map j) := by
  have : Mono j := (BigFppfOver.toScheme B S hS).mono_of_mono_map inferInstance
  constructor
  · intro h
    obtain ⟨g, rfl⟩ := FiniteOpenSubspace.exists_comp_eq_of_exists fs hz hzj y h
    rintro _ ⟨a, rfl⟩
    exact ⟨_, (Scheme.Hom.comp_apply _ _ a).symm.trans
      (congrArg (fun f => f a) ((BigFppfOver.toScheme B S hS).map_comp g j).symm)⟩
  · intro h
    obtain ⟨m, rfl⟩ := exists_comp_eq_of_range_subset j y h
    have := mono_schemeSpaceMap_hom_comp_ambientIso fs b j hz
    rw [hzj, Subfunctor.exists_comp_range_ι_eq_iff]
    exact ⟨(schemeSpaceMap m).hom, by rw [← Category.assoc, schemeSpaceMap_hom_comp]⟩

/-- Two pairs of Stacks 04PC over `T` with the same morphism `b` to the target are equal as soon
as the same morphisms `y : A ⟶ T ×_Y X` of the site factor through their open subspaces. -/
theorem FiniteOpenSubspace.ext_of_iff {T : BigFppfOver B S hS}
    {z z' : FiniteOpenSubspace B S hS (schemeSpaceMap fs) (schemeSpace T)} {b : T ⟶ Ys}
    (hz : z.toBase = schemeSpaceMap b) (hz' : z'.toBase = schemeSpaceMap b)
    (h : ∀ (A : BigFppfOver B S hS) (y : A ⟶ pullback b fs),
      (∃ l, l ≫ z.subspace.ι = (schemeSpaceMap y).hom ≫ (ambientIso fs b hz).hom) ↔
        ∃ l, l ≫ z'.subspace.ι = (schemeSpaceMap y).hom ≫ (ambientIso fs b hz').hom) :
    z = z' := by
  rcases z with ⟨a, Z, hZ, hZf⟩
  rcases z' with ⟨a', Z', hZ', hZf'⟩
  dsimp only at hz hz' h
  subst hz hz'
  have hZZ : Z = Z' := by
    refine Subfunctor.ext (funext fun A => Set.ext fun x => ?_)
    obtain ⟨A⟩ := A
    let e := ambientIso fs b (rfl : schemeSpaceMap b = schemeSpaceMap b)
    let y : A ⟶ pullback b fs := yoneda.preimage
      (show yoneda.obj A ⟶ yoneda.obj (pullback b fs) from yonedaEquiv.symm x ≫ e.inv)
    have hy : yonedaEquiv ((schemeSpaceMap y).hom ≫ e.hom) = x := by
      have h1 : (schemeSpaceMap y).hom = yonedaEquiv.symm x ≫ e.inv := yoneda.map_preimage _
      rw [h1, Category.assoc, Iso.inv_hom_id, Category.comp_id, Equiv.apply_symm_apply]
    rw [← hy, Subfunctor.mem_obj_iff_exists, Subfunctor.mem_obj_iff_exists]
    exact h A y
  subst hZZ
  rfl

/-- The pair of Stacks 04PC over `T` with morphism `b` to the target whose open subspace is the
range of an open immersion `j : W ⟶ T ×_Y X` of the site with `W` finite over `T`. -/
noncomputable def FiniteOpenSubspace.ofOpenImmersion {T W : BigFppfOver B S hS} (b : T ⟶ Ys)
    (j : W ⟶ pullback b fs)
    [_root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map j)]
    (hfin : _root_.AlgebraicGeometry.IsFinite
      ((BigFppfOver.toScheme B S hS).map (j ≫ pullback.fst b fs))) :
    FiniteOpenSubspace B S hS (schemeSpaceMap fs) (schemeSpace T) :=
  have : Mono j := (BigFppfOver.toScheme B S hS).mono_of_mono_map inferInstance
  have : Mono (yoneda.map j) := inferInstance
  let e := ambientIso fs b (rfl : schemeSpaceMap b = schemeSpaceMap b)
  have : Mono ((schemeSpaceMap j).hom ≫ e.hom) :=
    @mono_comp _ _ _ _ _ (yoneda.map j) _ e.hom (IsIso.mono_of_iso e.hom)
  have hZι := Subfunctor.toRange_ι ((schemeSpaceMap j).hom ≫ e.hom)
  { toBase := schemeSpaceMap b
    subspace := Subfunctor.range ((schemeSpaceMap j).hom ≫ e.hom)
    isOpen := ⟨AlgebraicGeometry.isAlgebraicSpace_of_iso B S hS
        (asIso (Subfunctor.toRange _)).symm (isAlgebraicSpace_yoneda B S hS W), by
      refine (MorphismProperty.cancel_left_of_respectsIso _ (Subfunctor.toRange _) _).mp ?_
      rw [hZι]
      exact MorphismProperty.RespectsIso.postcomp _ e.hom _
        ((presheaf_yoneda_map_iff B S hS inferInstance j).mpr inferInstance)⟩
    finite_projection := by
      have hsq : inv (Subfunctor.toRange _) ≫ (schemeSpaceMap (j ≫ pullback.fst b fs)).hom =
          ((Subfunctor.range ((schemeSpaceMap j).hom ≫ e.hom)).ι ≫ pullback.fst _ _) ≫ 𝟙 _ := by
        rw [Category.comp_id, IsIso.inv_comp_eq, ← Category.assoc, hZι, Category.assoc,
          ambientIso_hom_fst, schemeSpaceMap_hom_comp]
      exact isFinite_of_isPullback B S hS (IsPullback.of_horiz_isIso ⟨hsq⟩)
        (isFinite_yoneda_map_of_isFinite hfin) }

/-- The morphism to the target of `FiniteOpenSubspace.ofOpenImmersion fs b j hfin` is the one
underlying `b`. -/
theorem FiniteOpenSubspace.ofOpenImmersion_toBase {T W : BigFppfOver B S hS} (b : T ⟶ Ys)
    (j : W ⟶ pullback b fs)
    [_root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map j)]
    (hfin : _root_.AlgebraicGeometry.IsFinite
      ((BigFppfOver.toScheme B S hS).map (j ≫ pullback.fst b fs))) :
    (FiniteOpenSubspace.ofOpenImmersion fs b j hfin).toBase = schemeSpaceMap b :=
  rfl

/-- The open subspace of `FiniteOpenSubspace.ofOpenImmersion fs b j hfin` is the range of `j`,
transported along `ambientIso`. -/
theorem FiniteOpenSubspace.ofOpenImmersion_subspace {T W : BigFppfOver B S hS} (b : T ⟶ Ys)
    (j : W ⟶ pullback b fs)
    [_root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map j)]
    (hfin : _root_.AlgebraicGeometry.IsFinite
      ((BigFppfOver.toScheme B S hS).map (j ≫ pullback.fst b fs))) :
    (FiniteOpenSubspace.ofOpenImmersion fs b j hfin).subspace =
      Subfunctor.range ((schemeSpaceMap j).hom ≫ (ambientIso fs b
        (FiniteOpenSubspace.ofOpenImmersion_toBase fs b j hfin)).hom) :=
  rfl

end Represent

/-! ### The doubled origin as a morphism of the big fppf site of `Spec k` -/

section Objects

variable (B : BigFppfSite.{u}) (k : Type u) [Field k] (hk : B.Contains (Spec (.of k))) (n : ℕ)

include hk in
/-- Affine `n`-space over `k` with its origin doubled belongs to every big fppf site containing
`Spec k`: it is covered by two affine charts and is locally of finite type over affine space. -/
theorem contains_affineSpaceWithDoubledZero : B.Contains (affineSpaceWithDoubledZero k n) := by
  have : LocallyOfFiniteType (coordinateMorphism k n) := by
    have := locallyOfFinitePresentation_coordinateMorphism k n
    infer_instance
  refine Scheme.size_lt_of_locallyOfFiniteType_of_affineCover B.aleph0_lt_cutoff
    B.cutoff_isStrongPrelimit (coordinateMorphism k n) (I := ULift.{u} (Fin 2))
    (fun i => ⟨(chartInclusion k n i.down).opensRange, isAffineOpen_opensRange _⟩) ?_ ?_
    (contains_spec_of_finiteType B (R' := MvPolynomial (Fin n) k) hk)
  · refine top_unique (fun x _ => ?_)
    obtain ⟨i, y, hy⟩ := (doubledZeroGlueData k n).ι_jointly_surjective x
    exact Opens.mem_iSup.mpr ⟨i, y, hy⟩
  · exact Cardinal.mk_le_aleph0.trans
      ((Scheme.aleph0_le_size _).trans (Cardinal.self_le_power _ Cardinal.one_le_aleph0))

/-- The structure morphism of affine `n`-space over `k`. -/
noncomputable abbrev affineSpaceStructure : Spec (.of (MvPolynomial (Fin n) k)) ⟶ Spec (.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k (MvPolynomial (Fin n) k)))

/-- Affine `n`-space over `k`, as an object of the big fppf site of `Spec k`. -/
noncomputable abbrev affineSpaceObj : BigFppfOver B (Spec (.of k)) hk :=
  BigFppfOver.mk B (Spec (.of k)) hk
    (contains_spec_of_finiteType B (R' := MvPolynomial (Fin n) k) hk)
    (affineSpaceStructure k n)

/-- Affine `n`-space over `k` with its origin doubled, as an object of the big fppf site of
`Spec k`. -/
noncomputable abbrev doubledOriginAffineSpaceObj : BigFppfOver B (Spec (.of k)) hk :=
  BigFppfOver.mk B (Spec (.of k)) hk (contains_affineSpaceWithDoubledZero B k hk n)
    (coordinateMorphism k n ≫ affineSpaceStructure k n)

/-- The coordinate morphism of affine space with doubled origin, as a morphism of the big fppf
site of `Spec k`. -/
noncomputable abbrev doubledCoordHom :
    doubledOriginAffineSpaceObj B k hk n ⟶ affineSpaceObj B k hk n :=
  BigFppfOver.homMk B (Spec (.of k)) hk
    (contains_spec_of_finiteType B (R' := MvPolynomial (Fin n) k) hk)
    (affineSpaceStructure k n) (coordinateMorphism k n) rfl

/-- The `i`-th chart inclusion of affine space with doubled origin, as a morphism of the big
fppf site of `Spec k`. -/
noncomputable abbrev chartHom (i : Fin 2) :
    affineSpaceObj B k hk n ⟶ doubledOriginAffineSpaceObj B k hk n :=
  BigFppfOver.homMk B (Spec (.of k)) hk (contains_affineSpaceWithDoubledZero B k hk n)
    (coordinateMorphism k n ≫ affineSpaceStructure k n) (chartInclusion k n i)
    (by exact (reassoc_of% ((coordinateMorphismData k n).property i)) (affineSpaceStructure k n))

/-- The morphism of schemes underlying `doubledCoordHom` is `coordinateMorphism k n`. -/
@[simp]
theorem toScheme_map_doubledCoordHom :
    (BigFppfOver.toScheme B (Spec (.of k)) hk).map (doubledCoordHom B k hk n) =
      coordinateMorphism k n :=
  rfl

/-- The morphism of schemes underlying `chartHom B k hk n i` is `chartInclusion k n i`. -/
@[simp]
theorem toScheme_map_chartHom (i : Fin 2) :
    (BigFppfOver.toScheme B (Spec (.of k)) hk).map (chartHom B k hk n i) = chartInclusion k n i :=
  rfl

/-- Each chart inclusion is a section of the coordinate morphism. -/
@[reassoc (attr := simp)]
theorem chartHom_doubledCoordHom (i : Fin 2) :
    chartHom B k hk n i ≫ doubledCoordHom B k hk n = 𝟙 _ :=
  (BigFppfOver.toScheme B (Spec (.of k)) hk).map_injective (by
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id]
    exact (coordinateMorphismData k n).property i)


/-- `Spec k`, as an object of the big fppf site of `Spec k`. -/
noncomputable abbrev pointObj : BigFppfOver B (Spec (.of k)) hk :=
  BigFppfOver.mk B (Spec (.of k)) hk hk (𝟙 _)

/-- The origin of affine `n`-space over `k`, as a `k`-point. -/
noncomputable abbrev originHom : pointObj B k hk ⟶ affineSpaceObj B k hk n :=
  BigFppfOver.homMk B (Spec (.of k)) hk
    (contains_spec_of_finiteType B (R' := MvPolynomial (Fin n) k) hk)
    (affineSpaceStructure k n)
    (Spec.map (CommRingCat.ofHom (MvPolynomial.aeval fun _ : Fin n => (0 : k)).toRingHom)) (by
      have h : CommRingCat.ofHom (algebraMap k (MvPolynomial (Fin n) k)) ≫
          CommRingCat.ofHom (MvPolynomial.aeval fun _ : Fin n => (0 : k)).toRingHom = 𝟙 _ := by
        ext x
        simp
      exact (Spec.map_comp _ _).symm.trans ((congrArg Spec.map h).trans (Spec.map_id _)))

/-- A morphism to affine space given by a ring map sending every coordinate to a nilpotent
element maps every point off the complement of the origin. -/
theorem spec_map_notMem_puncturedAffineSpace {R : CommRingCat.{u}}
    (φ : CommRingCat.of (MvPolynomial (Fin n) k) ⟶ R)
    (hφ : ∀ i, IsNilpotent (φ (MvPolynomial.X i))) (x : Spec R) :
    Spec.map φ x ∉ puncturedAffineSpace k n := by
  intro hx
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
  exact (PrimeSpectrum.mem_basicOpen _ _).mp hi (nilpotent_iff_mem_prime.mp (hφ i) _ x.isPrime)

/-- The origin is mapped off the complement of the origin. -/
theorem originHom_notMem_puncturedAffineSpace
    (x : (BigFppfOver.toScheme B (Spec (.of k)) hk).obj (pointObj B k hk)) :
    (BigFppfOver.toScheme B (Spec (.of k)) hk).map (originHom B k hk n) x ∉
      puncturedAffineSpace k n :=
  spec_map_notMem_puncturedAffineSpace k n _ (fun i => by simp) x


include hk in
/-- The `m`-th infinitesimal neighbourhood of a rational point belongs to every big fppf site
containing `Spec k`. -/
theorem contains_spec_thickeningRing (m : ℕ) : B.Contains (Spec (.of (thickeningRing k m))) :=
  Scheme.size_Spec_lt_of_finiteType B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit k _ hk

/-- `Spec k[t]/(t^(m+1))`, as an object of the big fppf site of `Spec k`. -/
noncomputable abbrev thickeningObj (m : ℕ) : BigFppfOver B (Spec (.of k)) hk :=
  BigFppfOver.mk B (Spec (.of k)) hk (contains_spec_thickeningRing B k hk m)
    (Spec.map (CommRingCat.ofHom (algebraMap k (thickeningRing k m))))

/-- The morphism `Spec k[t]/(t^(m+1)) ⟶ Y` given by sending every coordinate to `t`. -/
noncomputable abbrev thickeningHom (m : ℕ) : thickeningObj B k hk m ⟶ affineSpaceObj B k hk n :=
  BigFppfOver.homMk B (Spec (.of k)) hk
    (contains_spec_of_finiteType B (R' := MvPolynomial (Fin n) k) hk)
    (affineSpaceStructure k n)
    (Spec.map (CommRingCat.ofHom (thickeningCoordinates n m).toRingHom)) (by
      have h : CommRingCat.ofHom (algebraMap k (MvPolynomial (Fin n) k)) ≫
          CommRingCat.ofHom (thickeningCoordinates (k := k) n m).toRingHom =
            CommRingCat.ofHom (algebraMap k (thickeningRing k m)) := by
        ext x
        simp
      exact (Spec.map_comp _ _).symm.trans (congrArg Spec.map h))

/-- The rational point `Spec k ⟶ Spec k[t]/(t^(m+1))`. -/
noncomputable abbrev thickeningInclusion (m : ℕ) : pointObj B k hk ⟶ thickeningObj B k hk m :=
  BigFppfOver.homMk B (Spec (.of k)) hk (contains_spec_thickeningRing B k hk m)
    (Spec.map (CommRingCat.ofHom (algebraMap k (thickeningRing k m))))
    (Spec.map (CommRingCat.ofHom (thickeningResidue (k := k) m).toRingHom)) (by
      have h : CommRingCat.ofHom (algebraMap k (thickeningRing k m)) ≫
          CommRingCat.ofHom (thickeningResidue (k := k) m).toRingHom = 𝟙 _ := by
        ext x
        simp
      exact (Spec.map_comp _ _).symm.trans ((congrArg Spec.map h).trans (Spec.map_id _)))

/-- The rational point of `Spec k[t]/(t^(m+1))` lies over the origin. -/
theorem thickeningInclusion_thickeningHom (m : ℕ) :
    thickeningInclusion B k hk m ≫ thickeningHom B k hk n m = originHom B k hk n :=
  (BigFppfOver.toScheme B (Spec (.of k)) hk).map_injective (by
    rw [CategoryTheory.Functor.map_comp]
    refine (Spec.map_comp _ _).symm.trans (congrArg Spec.map ?_)
    ext1
    exact congrArg AlgHom.toRingHom (thickeningResidue_comp_thickeningCoordinates n m))

/-- The infinitesimal neighbourhoods of the origin are mapped off the complement of the
origin. -/
theorem thickeningHom_notMem_puncturedAffineSpace (m : ℕ)
    (x : (BigFppfOver.toScheme B (Spec (.of k)) hk).obj (thickeningObj B k hk m)) :
    (BigFppfOver.toScheme B (Spec (.of k)) hk).map (thickeningHom B k hk n m) x ∉
      puncturedAffineSpace k n :=
  spec_map_notMem_puncturedAffineSpace k n _
    (fun i => by simpa using isNilpotent_thickeningParameter m) x

/-- The finite part `(X/Y)_fin` of the coordinate morphism of affine space with doubled origin,
over the big fppf site of `Spec k`. -/
noncomputable abbrev doubledOriginFinitePart :
    FinitePartPresheaf B (Spec (.of k)) hk (schemeSpaceMap (doubledCoordHom B k hk n)) :=
  finiteOpenSubspacePresheaf B (Spec (.of k)) hk (schemeSpaceMap (doubledCoordHom B k hk n))

variable {B k hk n}

/-- The `i`-th chart section of the ambient fibre product `T ×_Y X` of a pair of Stacks 04PC for
the coordinate morphism: its component in `T` is the identity and its component in `X` is the
morphism to `Y` followed by the `i`-th chart inclusion. -/
noncomputable def chartSection {T : BigFppfOver B (Spec (.of k)) hk}
    (z : FiniteOpenSubspace B (Spec (.of k)) hk (schemeSpaceMap (doubledCoordHom B k hk n))
      (schemeSpace T)) (i : Fin 2) :
    (schemeSpace T).obj ⟶ pullback z.toBase.hom (schemeSpaceMap (doubledCoordHom B k hk n)).hom :=
  pullback.lift (𝟙 _) (z.toBase.hom ≫ (schemeSpaceMap (chartHom B k hk n i)).hom) (by
    rw [Category.id_comp, Category.assoc, schemeSpaceMap_hom_comp, chartHom_doubledCoordHom,
      schemeSpaceMap_hom_id, Category.comp_id])

/-- The first projection of `chartSection z i` is the identity. -/
@[reassoc (attr := simp)]
theorem chartSection_fst {T : BigFppfOver B (Spec (.of k)) hk}
    (z : FiniteOpenSubspace B (Spec (.of k)) hk (schemeSpaceMap (doubledCoordHom B k hk n))
      (schemeSpace T)) (i : Fin 2) :
    chartSection z i ≫ pullback.fst _ _ = 𝟙 _ :=
  pullback.lift_fst _ _ _

/-- The second projection of `chartSection z i` is the morphism to the target followed by the
`i`-th chart. -/
@[reassoc (attr := simp)]
theorem chartSection_snd {T : BigFppfOver B (Spec (.of k)) hk}
    (z : FiniteOpenSubspace B (Spec (.of k)) hk (schemeSpaceMap (doubledCoordHom B k hk n))
      (schemeSpace T)) (i : Fin 2) :
    chartSection z i ≫ pullback.snd _ _ =
      z.toBase.hom ≫ (schemeSpaceMap (chartHom B k hk n i)).hom :=
  pullback.lift_snd _ _ _

/-- Base change of pairs carries chart sections to chart sections. -/
theorem FiniteOpenSubspace.IsBaseChange.chartSection_ambientMap
    {T T' : BigFppfOver B (Spec (.of k)) hk} {h : T' ⟶ T}
    {p : FiniteOpenSubspace B (Spec (.of k)) hk (schemeSpaceMap (doubledCoordHom B k hk n))
      (schemeSpace T)}
    {q : FiniteOpenSubspace B (Spec (.of k)) hk (schemeSpaceMap (doubledCoordHom B k hk n))
      (schemeSpace T')}
    (hpq : FiniteOpenSubspace.IsBaseChange B (Spec (.of k)) hk _ h p q) (i : Fin 2) :
    chartSection q i ≫ hpq.ambientMap = (schemeSpaceMap h).hom ≫ chartSection p i := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, FiniteOpenSubspace.IsBaseChange.ambientMap_fst, chartSection_fst_assoc,
      Category.assoc, chartSection_fst, Category.comp_id]
  · rw [Category.assoc, FiniteOpenSubspace.IsBaseChange.ambientMap_snd, chartSection_snd,
      Category.assoc, chartSection_snd, hpq.toBase_hom_eq, Category.assoc]

end Objects

end AlgebraicGeometry.Space

end
