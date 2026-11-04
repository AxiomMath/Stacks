module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.ClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.Size.Monomorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.Representability

/-!
# Loci cut out by closed, generalization-stable conditions on points

Let `F` be a presheaf on the big fppf site of a scheme `S` and `G ⊆ F` a subfunctor. Suppose that
for every scheme `U` of the site and every section `x ∈ F(U)` there is a subset `Z ⊆ |U|` which is
closed and stable under generalization, such that a morphism `h : W ⟶ U` of the site pulls `x`
back into `G` exactly when `h` maps `|W|` into `Z`. Then the inclusion `G ⟶ F` is representable by
*flat closed immersions*: its base change to `U` along `x` is the flat closed subscheme of `U` with
underlying set `Z` (Stacks 04PW), and the base change is that subscheme because, by the same
lemma, a morphism of schemes whose image lies in `Z` factors through it. If moreover every such
`Z` is open, the inclusion is representable by morphisms that are at the same time open and
closed immersions.

This is the shape of every numerical-invariant substack of the source's chapter on moduli
stacks: the locus where finitely or infinitely many locally constant functions take prescribed
values is an intersection of open and closed sets, hence closed and stable under generalization,
and open when the intersection is finite.

## Main definitions

* `AlgebraicGeometry.Space.IsCutOutByPoints`: after base change to every scheme of the site, a
  subfunctor is cut out by a set of points with a prescribed property.

## Main results

* `AlgebraicGeometry.Space.exists_flat_closedImmersion_factors_iff`: a closed,
  generalization-stable subset `Z` of the underlying scheme of an object `U` of the site is the
  image of a flat closed immersion `V ⟶ U` of the site through which a morphism `W ⟶ U` factors
  exactly when its image lies in `Z`; when `Z` is open, that closed immersion is also an open
  immersion.
* `AlgebraicGeometry.Space.relative_closedImmersion_flat_ι`: a subfunctor cut out, after every
  base change to a scheme, by a closed generalization-stable set of points has flat closed
  immersions as represented base changes of its inclusion.
* `AlgebraicGeometry.Space.relative_openImmersion_closedImmersion_ι`: the same, with open and
  closed immersions, when the sets of points are moreover open.
* `AlgebraicGeometry.Space.isCutOutByPoints_of_isLocallyConstant` and
  `AlgebraicGeometry.Space.isCutOutByPoints_isClopen_of_isLocallyConstant`: the locus where a
  family of locally constant functions, compatible with restriction, takes prescribed values is
  of the first kind, and of the second kind when the family is finite.
* `AlgebraicGeometry.Space.IsCutOutByPoints.preimage`: inverse images along morphisms of
  presheaves preserve these conditions.

## Implementation notes

The presheaves are allowed to take values in `Type (max w u)`, and representability is taken
along `CategoryTheory.uliftYoneda.{w}`, as in
`AlgebraicGeometry.Space.IsClosedImmersionULift`: the functors this file is applied to classify
closed subspaces or quotient modules of base changes, and those live one universe above the
schemes of the site. For `w = 0` this is representability along the Yoneda embedding up to the
universe lift.

A flat closed immersion is expressed as the conjunction of the two properties of morphisms of
schemes; for a representable morphism, flatness in the sense of Stacks 03ML is flatness of the
represented base changes (`AlgebraicGeometry.Space.isFlat_iff_presheaf`), so this is the
source's "flat closed immersion".

## References

* [Stacks Project, Tag 04PW](https://stacks.math.columbia.edu/tag/04PW)
* [Stacks Project, Tag 02YU](https://stacks.math.columbia.edu/tag/02YU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe w u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A flat closed subscheme whose support is open is an open subscheme: the open subscheme on
the support and the closed immersion factor through each other (the first by Stacks 04PW, the
second because an open immersion lifts every morphism landing in its image), and both are
monomorphisms. -/
theorem isOpenImmersion_subschemeι_of_isOpen {X : Scheme.{u}} (I : X.IdealSheafData)
    [Flat I.subschemeι] (hopen : IsOpen (I.support : Set X)) :
    _root_.AlgebraicGeometry.IsOpenImmersion I.subschemeι := by
  let O : X.Opens := ⟨I.support, hopen⟩
  have hO : Set.range O.ι = Set.range I.subschemeι := by
    rw [Scheme.Opens.range_ι, I.range_subschemeι]
    rfl
  let l : I.subscheme ⟶ O := IsOpenImmersion.lift O.ι I.subschemeι hO.ge
  have hl : l ≫ O.ι = I.subschemeι := IsOpenImmersion.lift_fac O.ι I.subschemeι hO.ge
  obtain ⟨k, hk, -⟩ := existsUnique_lift_of_flat_closedImmersion I O.ι
    (by rw [hO, I.range_subschemeι])
  have hkl : k ≫ l = 𝟙 _ := (cancel_mono O.ι).1 (by simp [hl, hk])
  have hlk : l ≫ k = 𝟙 _ := (cancel_mono I.subschemeι).1 (by simp [hk, hl])
  have : IsIso l := ⟨k, hlk, hkl⟩
  rw [← hl]
  infer_instance

/-- **The locus of a closed, generalization-stable set of points of a scheme of the site.**  For
an object `U` of the big fppf site of `S` and a subset `Z` of the underlying scheme of `U` which is
closed and stable under generalization, there is a morphism `s : V ⟶ U` of the site whose
underlying morphism of schemes is a flat closed immersion with image `Z`, and through which a
morphism `h : W ⟶ U` of the site factors exactly when `h` maps into `Z`.  When `Z` is moreover
open, `s` is also an open immersion.

The subscheme is the flat closed subscheme of Stacks 04PW with support `Z`; it belongs to the site
because a closed immersion is a quasi-compact monomorphism (Stacks 04VA). -/
theorem exists_flat_closedImmersion_factors_iff (U : BigFppfOver B S hS)
    (Z : Set ((BigFppfOver.toScheme B S hS).obj U)) (hZ : IsClosed Z)
    (hgen : StableUnderGeneralization Z) :
    ∃ (V : BigFppfOver B S hS) (s : V ⟶ U),
      _root_.AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map s) ∧
      Flat ((BigFppfOver.toScheme B S hS).map s) ∧
      (IsOpen Z → _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map s)) ∧
      ∀ ⦃W : BigFppfOver B S hS⦄ (h : W ⟶ U),
        (∃ k : W ⟶ V, k ≫ s = h) ↔ Set.range ((BigFppfOver.toScheme B S hS).map h) ⊆ Z := by
  obtain ⟨I, hIflat, hIsupp⟩ :=
    (support_bijOn_flat_closedImmersions ((BigFppfOver.toScheme B S hS).obj U)).surjOn
      (show (⟨Z, hZ⟩ : Closeds ((BigFppfOver.toScheme B S hS).obj U)) ∈
        {C : Closeds ((BigFppfOver.toScheme B S hS).obj U) |
          StableUnderGeneralization (C : Set ((BigFppfOver.toScheme B S hS).obj U))} from hgen)
  have : Flat I.subschemeι := hIflat
  have hsupp : (I.support : Set ((BigFppfOver.toScheme B S hS).obj U)) = Z :=
    congrArg (fun C : Closeds ((BigFppfOver.toScheme B S hS).obj U) =>
      (C : Set ((BigFppfOver.toScheme B S hS).obj U))) hIsupp
  have hcont : B.Contains I.subscheme :=
    lt_of_le_of_lt (Scheme.size_le_of_mono_quasiCompact I.subschemeι) U.left.2
  let V : BigFppfOver B S hS :=
    BigFppfOver.mk B S hS hcont (I.subschemeι ≫ B.inclusion.map U.hom)
  let s : V ⟶ U := Over.homMk (ObjectProperty.homMk I.subschemeι) (by
    apply ObjectProperty.hom_ext
    rfl)
  have hs : (BigFppfOver.toScheme B S hS).map s = I.subschemeι := rfl
  refine ⟨V, s, inferInstanceAs (_root_.AlgebraicGeometry.IsClosedImmersion I.subschemeι),
    inferInstanceAs (Flat I.subschemeι),
    fun hopen => isOpenImmersion_subschemeι_of_isOpen I (by rwa [hsupp]),
    fun W h => ⟨?_, fun hh => ?_⟩⟩
  · rintro ⟨k, rfl⟩
    rw [Functor.map_comp, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hs,
      ← hsupp, ← I.range_subschemeι]
    exact Set.image_subset_range _ _
  · obtain ⟨k₀, hk₀, -⟩ := existsUnique_lift_of_flat_closedImmersion I
      ((BigFppfOver.toScheme B S hS).map h) (by rwa [hsupp])
    refine ⟨Over.homMk (ObjectProperty.homMk k₀) ?_, BigFppfOver.map_toScheme_injective B S hS hk₀⟩
    apply ObjectProperty.hom_ext
    show k₀ ≫ I.subschemeι ≫ B.inclusion.map U.hom = B.inclusion.map W.hom
    rw [← Category.assoc, hk₀]
    exact congrArg B.inclusion.map (Over.w h)

variable {B S hS}

/-- The condition on a subfunctor `G` of a presheaf `F` on the big fppf site of `S` that, after
base change to every scheme `U` of the site along every section `x ∈ F(U)`, it is cut out by a
set of points of `U` satisfying `p`: a morphism `h : W ⟶ U` pulls `x` back into `G` exactly when it
maps the points of `W` into that set. -/
def IsCutOutByPoints {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max w u)} (G : Subfunctor F)
    (p : ∀ U : BigFppfOver B S hS, Set ((BigFppfOver.toScheme B S hS).obj U) → Prop) : Prop :=
  ∀ (U : BigFppfOver B S hS) (x : F.obj (Opposite.op U)),
    ∃ Z : Set ((BigFppfOver.toScheme B S hS).obj U), p U Z ∧
      ∀ ⦃W : BigFppfOver B S hS⦄ (h : W ⟶ U),
        F.map h.op x ∈ G.obj (Opposite.op W) ↔
          Set.range ((BigFppfOver.toScheme B S hS).map h) ⊆ Z

/-- Being cut out by sets of points is inherited by inverse images: if `G ⊆ F'` is cut out by
sets of points satisfying `p`, so is its inverse image along any morphism `φ : F ⟶ F'`, by the
same sets, since `φ` commutes with restriction. -/
theorem IsCutOutByPoints.preimage {F F' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max w u)}
    {G : Subfunctor F'}
    {p : ∀ U : BigFppfOver B S hS, Set ((BigFppfOver.toScheme B S hS).obj U) → Prop}
    (hG : IsCutOutByPoints G p) (φ : F ⟶ F') : IsCutOutByPoints (G.preimage φ) p := by
  intro U x
  obtain ⟨Z, hZ, hGZ⟩ := hG U (φ.app _ x)
  refine ⟨Z, hZ, fun W h => ?_⟩
  rw [← hGZ h, ← NatTrans.naturality_apply]
  exact Iff.rfl

/-- Being cut out by sets of points satisfying `p` is monotone in `p`. -/
theorem IsCutOutByPoints.mono {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max w u)} {G : Subfunctor F}
    {p q : ∀ U : BigFppfOver B S hS, Set ((BigFppfOver.toScheme B S hS).obj U) → Prop}
    (hG : IsCutOutByPoints G p) (hpq : ∀ U Z, p U Z → q U Z) : IsCutOutByPoints G q :=
  fun U x => (hG U x).imp fun Z hZ => ⟨hpq U Z hZ.1, hZ.2⟩

/-- The represented base change of the inclusion of a subfunctor along a section, when that
section is cut out by a morphism `s` of the site through which exactly the morphisms pulling the
section back into the subfunctor factor, and `s` is a monomorphism. -/
theorem isPullback_ι_of_factors_iff {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max w u)}
    (G : Subfunctor F) {U V : BigFppfOver B S hS} (s : V ⟶ U) [Mono s]
    (g : uliftYoneda.{w}.obj U ⟶ F)
    (hs : ∀ ⦃W : BigFppfOver B S hS⦄ (h : W ⟶ U),
      (∃ k : W ⟶ V, k ≫ s = h) ↔ F.map h.op (uliftYonedaEquiv g) ∈ G.obj (Opposite.op W)) :
    IsPullback
      (uliftYonedaEquiv.symm ⟨F.map s.op (uliftYonedaEquiv g), (hs s).1 ⟨𝟙 V, by simp⟩⟩ :
        uliftYoneda.{w}.obj V ⟶ G.toFunctor)
      (uliftYoneda.{w}.map s) G.ι g := by
  set x := uliftYonedaEquiv g with hx
  have hgapp : ∀ (W : (BigFppfOver B S hS)ᵒᵖ) (h : W.unop ⟶ U),
      g.app W (ULift.up h) = F.map h.op x := by
    intro W h
    rw [hx, uliftYonedaEquiv_naturality]
    exact congrArg (g.app W) (congrArg ULift.up (by simp))
  refine IsPullback.of_forall_isPullback_app fun W => ?_
  rw [Types.isPullback_iff]
  refine ⟨?_, ?_, ?_⟩
  · ext ⟨k⟩
    show F.map k.op (F.map s.op x) = g.app W (ULift.up (k ≫ s))
    rw [hgapp, ← FunctorToTypes.map_comp_apply]
    rfl
  · rintro ⟨a⟩ ⟨b⟩ ⟨-, hab⟩
    exact congrArg ULift.up ((cancel_mono s).1 (congrArg ULift.down hab))
  · rintro ⟨y, hy⟩ ⟨h⟩ hyh
    have hyh' : y = F.map h.op x := (hyh.trans (hgapp W h) :)
    obtain ⟨k, hk⟩ := (hs h).2 (hyh' ▸ hy)
    refine ⟨ULift.up k, Subtype.ext ?_, congrArg ULift.up hk⟩
    show F.map k.op (F.map s.op x) = y
    rw [hyh', ← hk, ← FunctorToTypes.map_comp_apply]
    rfl

/-- A morphism of the site whose underlying morphism of schemes is a closed immersion is a
monomorphism. -/
private theorem mono_of_isClosedImmersion_map {U V : BigFppfOver B S hS} {s : V ⟶ U}
    (hcl : _root_.AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map s)) :
    Mono s :=
  (BigFppfOver.toScheme B S hS).mono_of_mono_map (by have := hcl; infer_instance)

/-- The inverse image of an intersection of two isomorphism-stable properties of morphisms of
schemes along a functor is isomorphism-stable. -/
private theorem respectsIso_inverseImage_inf {C : Type*} [Category C] (F : C ⥤ Scheme.{u})
    (P Q : MorphismProperty Scheme.{u}) [P.RespectsIso] [Q.RespectsIso] :
    (MorphismProperty.inverseImage (P ⊓ Q) F).RespectsIso :=
  MorphismProperty.RespectsIso.inverseImage _ _

/-- **A subfunctor cut out by closed, generalization-stable sets of points is a flat closed
subfunctor.**  If, after base change to every scheme `U` of the site along every section of `F`
over `U`, the subfunctor `G ⊆ F` is cut out by a closed subset of `|U|` stable under
generalization, then every represented base change of the inclusion `G ⟶ F` is a flat closed
immersion of schemes: it is the flat closed subscheme of Stacks 04PW on that subset. -/
theorem relative_closedImmersion_flat_ι {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max w u)}
    (G : Subfunctor F)
    (hG : IsCutOutByPoints G fun _ Z => IsClosed Z ∧ StableUnderGeneralization Z) :
    (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsClosedImmersion.{u} ⊓ @Flat.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative uliftYoneda.{w} G.ι := by
  have : MorphismProperty.RespectsIso (@Flat.{u}) := by
    apply MorphismProperty.respectsIso_of_isStableUnderComposition
    intro X Y f (hf : IsIso f)
    infer_instance
  have := respectsIso_inverseImage_inf (BigFppfOver.toScheme B S hS)
    (@_root_.AlgebraicGeometry.IsClosedImmersion.{u}) (@Flat.{u})
  apply MorphismProperty.relative.of_exists
  intro U g
  obtain ⟨Z, ⟨hZ, hgen⟩, hGZ⟩ := hG U (uliftYonedaEquiv g)
  obtain ⟨V, s, hcl, hfl, -, hfac⟩ := exists_flat_closedImmersion_factors_iff B S hS U Z hZ hgen
  have := mono_of_isClosedImmersion_map hcl
  exact ⟨V, _, s, isPullback_ι_of_factors_iff G s g fun W h => (hfac h).trans (hGZ h).symm,
    hcl, hfl⟩

/-- **A subfunctor cut out by open and closed sets of points is an open and closed subfunctor.**
If, after base change to every scheme `U` of the site along every section of `F` over `U`, the
subfunctor `G ⊆ F` is cut out by an open and closed subset of `|U|`, then every represented base
change of the inclusion `G ⟶ F` is at the same time an open immersion and a closed immersion of
schemes. -/
theorem relative_openImmersion_closedImmersion_ι {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max w u)}
    (G : Subfunctor F) (hG : IsCutOutByPoints G fun _ Z => IsClopen Z) :
    (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsOpenImmersion.{u} ⊓
        @_root_.AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative uliftYoneda.{w} G.ι := by
  have := respectsIso_inverseImage_inf (BigFppfOver.toScheme B S hS)
    (@_root_.AlgebraicGeometry.IsOpenImmersion.{u})
    (@_root_.AlgebraicGeometry.IsClosedImmersion.{u})
  apply MorphismProperty.relative.of_exists
  intro U g
  obtain ⟨Z, hZ, hGZ⟩ := hG U (uliftYonedaEquiv g)
  obtain ⟨V, s, hcl, -, hop, hfac⟩ := exists_flat_closedImmersion_factors_iff B S hS U Z
    hZ.isClosed hZ.isOpen.stableUnderGeneralization
  have := mono_of_isClosedImmersion_map hcl
  exact ⟨V, _, s, isPullback_ι_of_factors_iff G s g fun W h => (hfac h).trans (hGZ h).symm,
    hop hZ.isOpen, hcl⟩

/-- An intersection of open and closed subsets of a topological space is closed and stable under
generalization: an open set contains every generalization of each of its points. -/
theorem isClosed_and_stableUnderGeneralization_iInter_isClopen {X : Type*} [TopologicalSpace X]
    {ι : Sort*} {C : ι → Set X} (hC : ∀ i, IsClopen (C i)) :
    IsClosed (⋂ i, C i) ∧ StableUnderGeneralization (⋂ i, C i) :=
  ⟨isClosed_iInter fun i => (hC i).isClosed,
    fun _ _ hxy hy => Set.mem_iInter.2 fun i =>
      (hC i).isOpen.stableUnderGeneralization hxy (Set.mem_iInter.1 hy i)⟩

section Numerical

variable {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max w u)} {I : Type*} {β : Type*}
  (G : Subfunctor F) (P : I → β)
  (χ : ∀ (U : BigFppfOver B S hS), F.obj (Opposite.op U) → I →
    (BigFppfOver.toScheme B S hS).obj U → β)

/-- A morphism `h : W ⟶ U` pulls `x` back into `G` exactly when it maps `|W|` into the locus where
all the functions `χ_x i` take the prescribed values `P i`. -/
private theorem map_mem_iff_range_subset_iInter
    (hbc : ∀ ⦃U W : BigFppfOver B S hS⦄ (h : W ⟶ U) (x : F.obj (Opposite.op U)) (i : I)
      (t : (BigFppfOver.toScheme B S hS).obj W),
      χ W (F.map h.op x) i t = χ U x i ((BigFppfOver.toScheme B S hS).map h t))
    (hG : ∀ U x, x ∈ G.obj (Opposite.op U) ↔ ∀ i t, χ U x i t = P i)
    {U W : BigFppfOver B S hS} (x : F.obj (Opposite.op U)) (h : W ⟶ U) :
    F.map h.op x ∈ G.obj (Opposite.op W) ↔
      Set.range ((BigFppfOver.toScheme B S hS).map h) ⊆ ⋂ i, {t | χ U x i t = P i} := by
  rw [hG]
  constructor
  · rintro hx _ ⟨t, rfl⟩
    exact Set.mem_iInter.2 fun i => (hbc h x i t).symm.trans (hx i t)
  · intro hx i t
    exact (hbc h x i t).trans (Set.mem_iInter.1 (hx ⟨t, rfl⟩) i)

/-- **A subfunctor cut out by prescribed values of locally constant functions.**  Suppose every
section `x ∈ F(U)` carries functions `χ_x i : |U| → β`, compatible with restriction, and that `x`
lies in `G` exactly when `χ_x i t = P i` for all `i` and `t`.  Then after base change along `x` the
subfunctor `G` is cut out by the locus where all `χ_x i` take the prescribed values; when each
`χ_x i` is locally constant that locus is an intersection of open and closed sets, hence closed
and stable under generalization. -/
theorem isCutOutByPoints_of_isLocallyConstant
    (hχ : ∀ U x i, IsLocallyConstant (χ U x i))
    (hbc : ∀ ⦃U W : BigFppfOver B S hS⦄ (h : W ⟶ U) (x : F.obj (Opposite.op U)) (i : I)
      (t : (BigFppfOver.toScheme B S hS).obj W),
      χ W (F.map h.op x) i t = χ U x i ((BigFppfOver.toScheme B S hS).map h t))
    (hG : ∀ U x, x ∈ G.obj (Opposite.op U) ↔ ∀ i t, χ U x i t = P i) :
    IsCutOutByPoints G fun _ Z => IsClosed Z ∧ StableUnderGeneralization Z := by
  intro U x
  refine ⟨⋂ i, {t | χ U x i t = P i},
    isClosed_and_stableUnderGeneralization_iInter_isClopen fun i =>
      (hχ U x i).isClopen_fiber (P i),
    fun W h => map_mem_iff_range_subset_iInter G P χ hbc hG x h⟩

/-- **The finite case.**  Under the hypotheses of
`AlgebraicGeometry.Space.isCutOutByPoints_of_isLocallyConstant`, when the index set is finite the
locus where all the functions take the prescribed values is a finite intersection of open and
closed sets, hence open and closed. -/
theorem isCutOutByPoints_isClopen_of_isLocallyConstant [Finite I]
    (hχ : ∀ U x i, IsLocallyConstant (χ U x i))
    (hbc : ∀ ⦃U W : BigFppfOver B S hS⦄ (h : W ⟶ U) (x : F.obj (Opposite.op U)) (i : I)
      (t : (BigFppfOver.toScheme B S hS).obj W),
      χ W (F.map h.op x) i t = χ U x i ((BigFppfOver.toScheme B S hS).map h t))
    (hG : ∀ U x, x ∈ G.obj (Opposite.op U) ↔ ∀ i t, χ U x i t = P i) :
    IsCutOutByPoints G fun _ Z => IsClopen Z := by
  intro U x
  refine ⟨⋂ i, {t | χ U x i t = P i},
    isClopen_iInter_of_finite fun i => (hχ U x i).isClopen_fiber (P i),
    fun W h => map_mem_iff_range_subset_iInter G P χ hbc hG x h⟩

end Numerical

end AlgebraicGeometry.Space

end
