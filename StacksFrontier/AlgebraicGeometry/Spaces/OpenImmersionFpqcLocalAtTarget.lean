module

public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Pullbacks
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.BinaryProducts
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FpqcCoveringBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.FpqcMorphismDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.FpqcOpenSubspaceDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenCover
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation

/-!
# Being an open immersion is fpqc local on the base

A morphism of algebraic spaces over `S` is an open immersion when it is representable and all
of its represented base changes are open immersions of schemes (Stacks 02YU). This file proves
that the property is local on the base for the fpqc topology of Stacks 03YH, which is
**Stacks 041X**.

The base-change half is immediate from Stacks 02YW. For the descent half, the image of each
base change `X ×_Y Y_i ⟶ Y_i` is an open subspace of `Y_i`, and these glue, by the descent of
open subspaces along an fpqc covering (Stacks 04P1), to an open subspace `W ⊆ Y`. Descent of
morphisms along an fpqc covering (Stacks 04P2) then produces mutually inverse morphisms between
`W` and `X` over `Y`, so `X ⟶ Y` is `W ⊆ Y` read through an isomorphism.

## Main results

* `AlgebraicGeometry.Space.openImmersion_isLocalAtTarget_fpqc`: **Stacks 041X**.

## Implementation notes

The morphism property is `AlgebraicGeometry.Space.openImmersionProperty`, the open-immersion
predicate on the category of algebraic spaces over `S`, and locality is expressed through
`CategoryTheory.MorphismProperty.IsLocalAtTarget` at the fpqc precoverage
`AlgebraicGeometry.Space.Topology.precoverage`, exactly as for the sibling properties in
`StacksFrontier/AlgebraicGeometry/Spaces/Descent/Fpqc/`. That class carries both halves of
"fpqc local on the base": `pullbackSnd` is the ascent and `of_forall_pullbackSnd` the descent.

The two glueing inputs are used through the chosen fibre products of Stacks 02X2, so the
argument repeatedly compares a canonical pullback in the category of algebraic spaces with the
corresponding pullback of underlying presheaves; `isOpenImmersion_pullback_iff` is that
comparison for the open-immersion predicate.

## References

* [Stacks Project, Tag 02YU](https://stacks.math.columbia.edu/tag/02YU)
* [Stacks Project, Tag 02YW](https://stacks.math.columbia.edu/tag/02YW)
* [Stacks Project, Tag 03MQ](https://stacks.math.columbia.edu/tag/03MQ)
* [Stacks Project, Tag 03YH](https://stacks.math.columbia.edu/tag/03YH)
* [Stacks Project, Tag 04P1](https://stacks.math.columbia.edu/tag/04P1)
* [Stacks Project, Tag 04P2](https://stacks.math.columbia.edu/tag/04P2)
* [Stacks Project, Tag 041X](https://stacks.math.columbia.edu/tag/041X)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w w'

namespace AlgebraicGeometry.Space

/-- The open-immersion predicate does not distinguish the chosen fibre product of algebraic
spaces from the pullback of the underlying presheaves. -/
private lemma isOpenImmersion_pullback_iff
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Z) (g : Y ⟶ Z) :
    IsOpenImmersion B S hS (Limits.pullback.snd f.hom g.hom) ↔
      IsOpenImmersion B S hS (Limits.pullback.snd f g).hom := by
  let sq := AlgebraicSpaces.isPullback_fiberProduct B S hS f g
  let hchosen := IsPullback.of_hasPullback f g
  let e := sq.isoIsPullback _ _ hchosen
  have he : e.hom.hom ≫ (Limits.pullback.snd f g).hom =
      Limits.pullback.snd f.hom g.hom :=
    congrArg (fun k => k.hom) (sq.isoIsPullback_hom_snd _ _ hchosen)
  let R : MorphismProperty (BigFppfOver B S hS) :=
    MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)
  let Q := MorphismProperty.presheaf R
  have : Q.RespectsIso :=
    (MorphismProperty.relative_isStableUnderBaseChange R).respectsIso
  rw [← he]
  exact Q.cancel_left_of_respectsIso e.hom.hom _

/-- The inverse of the isomorphism of a monomorphism onto its range composes with the
monomorphism to the inclusion of the range. -/
private lemma inv_asIso_toRange_comp {C : Type w} [Category.{w'} C] {F G : C ⥤ Type u} (p : F ⟶ G)
    [Mono p] : (asIso (Subfunctor.toRange p)).inv ≫ p = (Subfunctor.range p).ι :=
  (asIso _).inv_comp_eq.mpr (Subfunctor.toRange_ι p).symm

/-- The image of an open immersion out of an algebraic space over `S` is an open subspace of
its target: the morphism is a monomorphism, so its source is isomorphic to its image. -/
private lemma range_isOpenSubspace
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hf : IsOpenImmersion B S hS f.hom) :
    IsOpenSubspace B S hS (Subfunctor.range f.hom) := by
  let Q := MorphismProperty.inverseImage (@AlgebraicGeometry.IsOpenImmersion.{u} :
    MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)
  have : Mono f.hom := mono_of_presheaf_isOpenImmersion hf
  let U : Subfunctor Y.1 := Subfunctor.range f.hom
  have hUOpen : IsOpenImmersion B S hS U.ι := by
    let Q' := MorphismProperty.presheaf Q
    exact inv_asIso_toRange_comp f.hom ▸ MorphismProperty.RespectsIso.precomp Q'
      (asIso (Subfunctor.toRange f.hom)).inv f.hom hf
  exact ⟨isAlgebraicSpace_of_iso B S hS (asIso (Subfunctor.toRange f.hom)) X.property, hUOpen⟩

/-- The image of the second projection of a pullback of presheaves of types is the preimage of
the image of the first leg. -/
private lemma range_pullbackSnd {C : Type w} [Category.{w'} C]
    {F G H : C ⥤ Type u} (f : F ⟶ H) (g : G ⟶ H) :
    Subfunctor.range (Limits.pullback.snd f g) =
      (Subfunctor.range f).preimage g := by
  ext d x
  change x ∈ Set.range ((Limits.pullback.snd f g).app d) ↔
    g.app d x ∈ Set.range (f.app d)
  have h := Limits.Types.range_pullbackSnd (f.app d) (g.app d)
  constructor
  · rintro ⟨y, rfl⟩
    change ((Limits.pullback.snd f g).app d y) ∈
      (g.app d) ⁻¹' Set.range (f.app d)
    rw [← h]
    exact ⟨(Limits.pullbackObjIso f g d).hom y,
      congrArg (fun k => k y) (Limits.pullbackObjIso_hom_comp_snd f g d)⟩
  · intro hx
    obtain ⟨y, hy⟩ : x ∈ Set.range (Limits.pullback.snd (f.app d) (g.app d)) := by
      rwa [h]
    exact ⟨(Limits.pullbackObjIso f g d).inv y,
      (congrArg (fun k => k y) (Limits.pullbackObjIso_inv_comp_snd f g d)).trans hy⟩

/-- The preimage of a subfunctor along a morphism of presheaves is a fibre product. -/
private lemma isPullback_subfunctor_preimage {C : Type w} [Category.{w'} C]
    {F F' : C ⥤ Type u} (G : Subfunctor F) (p : F' ⟶ F) :
    IsPullback (G.fromPreimage p) (G.preimage p).ι G.ι p := by
  refine IsPullback.of_forall_isPullback_app fun d => ?_
  rw [Limits.Types.isPullback_iff]
  refine ⟨by simpa using congrArg (fun k => k.app d) (G.fromPreimage_ι p),
    fun x y h => Subtype.ext h.2, ?_⟩
  intro x y h
  refine ⟨⟨y, ?_⟩, ?_, rfl⟩
  · change p.app d y ∈ G.obj d
    rw [← h]
    exact x.property
  · exact Subtype.ext h.symm

/-- Two morphisms into the first factor of a cospan whose second projection is a monomorphism
agree as soon as they are compatible with a common morphism into the second factor. -/
private lemma eq_of_pullbackSnd_mono {C : Type w} [Category.{w'} C]
    {X Y Z T : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g]
    [Mono (Limits.pullback.snd f g)] {a b : T ⟶ X} {t : T ⟶ Y}
    (ha : a ≫ f = t ≫ g) (hb : b ≫ f = t ≫ g) : a = b := by
  have h : Limits.pullback.lift a t ha = Limits.pullback.lift b t hb :=
    (cancel_mono (Limits.pullback.snd f g)).mp
      (by rw [Limits.pullback.lift_snd, Limits.pullback.lift_snd])
  have h' := congrArg (· ≫ Limits.pullback.fst f g) h
  rwa [Limits.pullback.lift_fst, Limits.pullback.lift_fst] at h'

/-- An fpqc covering family of algebraic spaces over `S` is an epimorphic family. -/
private lemma hom_ext_of_fpqcCovering
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {I : Type v} {X : I → AlgebraicSpaces B S hS}
    {Y Z : AlgebraicSpaces B S hS} (q : ∀ i, X i ⟶ Y)
    (hq : IsFpqcCovering B S hS (fun i => (q i).hom))
    {a b : Y ⟶ Z} (hab : ∀ i, q i ≫ a = q i ≫ b) : a = b := by
  obtain ⟨d, _, hu⟩ := existsUnique_desc_of_fpqcCovering B S hS q hq Z (fun i => q i ≫ a)
    fun i j => by
      simpa only [Category.assoc] using
        (AlgebraicSpaces.isPullback_fiberProduct B S hS (q i) (q j)).w =≫ a
  exact (hu a (fun _ => rfl)).trans (hu b (fun i => (hab i).symm)).symm

/-- The descent half of **Stacks 041X**: a morphism of algebraic spaces over `S` whose base
change along every member of an fpqc covering of the target is an open immersion is an open
immersion. -/
private lemma isOpenImmersion_of_fpqcCovering
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {I : Type v} {Y : AlgebraicSpaces B S hS}
    {Yᵢ : I → AlgebraicSpaces B S hS}
    (g : ∀ i, Yᵢ i ⟶ Y)
    (hcover : IsFpqcCovering B S hS (fun i => (g i).hom))
    {X : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hbase : ∀ i, IsOpenImmersion B S hS
      (Limits.pullback.snd f.hom (g i).hom)) :
    IsOpenImmersion B S hS f.hom := by
  let f' (i : I) : AlgebraicSpaces.fiberProduct B S hS f (g i) ⟶ Yᵢ i :=
    ObjectProperty.homMk (Limits.pullback.snd f.hom (g i).hom)
  let W' (i : I) : {W : Subfunctor (Yᵢ i).1 // IsOpenSubspace B S hS W} :=
    ⟨Subfunctor.range (f' i).hom, range_isOpenSubspace B S hS (f' i) (hbase i)⟩
  have hW' (i : I) : (W' i).1 = (Subfunctor.range f.hom).preimage (g i).hom :=
    range_pullbackSnd f.hom (g i).hom
  have hcompatible : ∀ i j,
      (W' i).1.preimage (Limits.pullback.fst (g i).hom (g j).hom) =
        (W' j).1.preimage (Limits.pullback.snd (g i).hom (g j).hom) := by
    intro i j
    rw [hW', hW', ← Subfunctor.preimage_comp, ← Subfunctor.preimage_comp,
      Limits.pullback.condition]
  obtain ⟨W, hW, _⟩ :=
    existsUnique_openSubspace_of_fpqcCovering B S hS g hcover W' hcompatible
  let Wsp : AlgebraicSpaces B S hS := ⟨W.1.toFunctor, W.2.1⟩
  let wι : Wsp ⟶ Y := ObjectProperty.homMk W.1.ι
  let P₀ (i : I) := AlgebraicSpaces.fiberProduct B S hS (g i) wι
  let pW (i : I) : P₀ i ⟶ Wsp := ObjectProperty.homMk
    (Limits.pullback.snd (g i).hom wι.hom)
  have hpWcover : IsFpqcCovering B S hS (fun i => (pW i).hom) :=
    isFpqcCovering_pullback B S hS g wι hcover
  let W'sp (i : I) : AlgebraicSpaces B S hS :=
    ⟨(W' i).1.toFunctor, (W' i).2.1⟩
  let sqW (i : I) := isPullback_subfunctor_preimage W.1 (g i).hom
  let ePre (i : I) : (W.1.preimage (g i).hom).toFunctor ≅ (P₀ i).obj :=
    (sqW i).flip.isoIsPullback _ _ (IsPullback.of_hasPullback (g i).hom W.1.ι)
  let eWP (i : I) : W'sp i ≅ P₀ i := ObjectProperty.isoMk _
    ((eqToIso (congrArg Subfunctor.toFunctor (hW i).symm)) ≪≫ ePre i)
  have (i : I) : Mono (f' i).hom := mono_of_presheaf_isOpenImmersion (hbase i)
  have (i : I) : IsIso (Subfunctor.toRange (f' i).hom) := inferInstance
  let localInverse (i : I) : W'sp i ⟶ X := ObjectProperty.homMk
    ((asIso (Subfunctor.toRange (f' i).hom)).inv ≫
      Limits.pullback.fst f.hom (g i).hom)
  let localMap (i : I) : P₀ i ⟶ X := (eWP i).inv ≫ localInverse i
  have hlocal (i : I) : localMap i ≫ f = pW i ≫ wι := by
    have htoRangeInv := inv_asIso_toRange_comp (f' i).hom
    have hcast :
        (eqToIso (congrArg Subfunctor.toFunctor (hW i).symm)).inv ≫ (W' i).1.ι =
          (W.1.preimage (g i).hom).ι := by
      simpa using (subfunctor_eqToHom_ι (hW i))
    have heWPfst : (eWP i).inv.hom ≫ (W' i).1.ι =
        Limits.pullback.fst (g i).hom W.1.ι := by
      change (ePre i).inv ≫
          (eqToIso (congrArg Subfunctor.toFunctor (hW i).symm)).inv ≫ (W' i).1.ι =
        Limits.pullback.fst (g i).hom W.1.ι
      rw [hcast]
      exact (sqW i).flip.isoIsPullback_inv_fst _ _
        (IsPullback.of_hasPullback (g i).hom W.1.ι)
    have hInvBase : (localInverse i).hom ≫ f.hom = (W' i).1.ι ≫ (g i).hom := by
      change ((asIso (Subfunctor.toRange (f' i).hom)).inv ≫
        Limits.pullback.fst f.hom (g i).hom) ≫ f.hom = _
      calc
        _ = (asIso (Subfunctor.toRange (f' i).hom)).inv ≫
            (Limits.pullback.fst f.hom (g i).hom ≫ f.hom) := Category.assoc _ _ _
        _ = (asIso (Subfunctor.toRange (f' i).hom)).inv ≫
            (Limits.pullback.snd f.hom (g i).hom ≫ (g i).hom) :=
          congrArg _ Limits.pullback.condition
        _ = ((asIso (Subfunctor.toRange (f' i).hom)).inv ≫
            Limits.pullback.snd f.hom (g i).hom) ≫ (g i).hom :=
          (Category.assoc _ _ _).symm
        _ = (W' i).1.ι ≫ (g i).hom := congrArg (fun k => k ≫ (g i).hom) htoRangeInv
    apply ObjectProperty.hom_ext
    change ((eWP i).inv.hom ≫ (localInverse i).hom) ≫ f.hom =
      Limits.pullback.snd (g i).hom W.1.ι ≫ W.1.ι
    rw [Category.assoc, hInvBase, ← Category.assoc, heWPfst]
    exact Limits.pullback.condition
  let pT (i : I) : P₀ i ⟶ Yᵢ i := ObjectProperty.homMk
    (Limits.pullback.fst (g i).hom wι.hom)
  have hpT (i : I) : pT i ≫ g i = pW i ≫ wι :=
    ObjectProperty.hom_ext _ Limits.pullback.condition
  have hlocalCompatible : ∀ i j,
      (ObjectProperty.homMk (Limits.pullback.fst (pW i).hom (pW j).hom) :
        AlgebraicSpaces.fiberProduct B S hS (pW i) (pW j) ⟶ P₀ i) ≫ localMap i =
      (ObjectProperty.homMk (Limits.pullback.snd (pW i).hom (pW j).hom) :
        AlgebraicSpaces.fiberProduct B S hS (pW i) (pW j) ⟶ P₀ j) ≫ localMap j := by
    intro i j
    have : Mono (Limits.pullback.snd f.hom (g i).hom) :=
      mono_of_presheaf_isOpenImmersion (hbase i)
    let q₀ : AlgebraicSpaces.fiberProduct B S hS (pW i) (pW j) ⟶ P₀ i :=
      ObjectProperty.homMk (Limits.pullback.fst (pW i).hom (pW j).hom)
    let q₁ : AlgebraicSpaces.fiberProduct B S hS (pW i) (pW j) ⟶ P₀ j :=
      ObjectProperty.homMk (Limits.pullback.snd (pW i).hom (pW j).hom)
    have hq : q₀ ≫ pW i = q₁ ≫ pW j := ObjectProperty.hom_ext _ Limits.pullback.condition
    have h₀ : (q₀ ≫ localMap i) ≫ f = (q₀ ≫ pT i) ≫ g i := by
      simp only [Category.assoc]
      rw [hlocal, hpT]
    have h₁ : (q₁ ≫ localMap j) ≫ f = (q₀ ≫ pT i) ≫ g i := by
      calc
        (q₁ ≫ localMap j) ≫ f = (q₁ ≫ pW j) ≫ wι := by
          rw [Category.assoc, hlocal, ← Category.assoc]
        _ = (q₀ ≫ pW i) ≫ wι := by rw [hq]
        _ = (q₀ ≫ pT i) ≫ g i := by
          rw [Category.assoc, Category.assoc, hpT]
    apply ObjectProperty.hom_ext
    exact eq_of_pullbackSnd_mono f.hom (g i).hom
      (t := (q₀ ≫ pT i).hom) (congrArg (fun k => k.hom) h₀)
        (congrArg (fun k => k.hom) h₁)
  obtain ⟨descentMap, hdescentLocal, _⟩ :=
    existsUnique_desc_of_fpqcCovering B S hS
      pW hpWcover X localMap hlocalCompatible
  have hdescentBase : descentMap ≫ f = wι := by
    apply hom_ext_of_fpqcCovering B S hS pW hpWcover
    intro i
    rw [← Category.assoc, hdescentLocal, hlocal]
  let PX (i : I) := AlgebraicSpaces.fiberProduct B S hS (g i) f
  let qX (i : I) : PX i ⟶ X := ObjectProperty.homMk
    (Limits.pullback.snd (g i).hom f.hom)
  have hqXcover : IsFpqcCovering B S hS (fun i => (qX i).hom) :=
    isFpqcCovering_pullback B S hS g f hcover
  let X' (i : I) := AlgebraicSpaces.fiberProduct B S hS f (g i)
  let qX' (i : I) : X' i ⟶ X := ObjectProperty.homMk
    (Limits.pullback.fst f.hom (g i).hom)
  let swapIso (i : I) : PX i ≅ X' i := ObjectProperty.isoMk _
    (Limits.pullbackSymmetry (g i).hom f.hom)
  let rangeIso (i : I) : X' i ≅ W'sp i := ObjectProperty.isoMk _
    (asIso (Subfunctor.toRange (f' i).hom))
  let xLocal (i : I) : PX i ⟶ Wsp :=
    (swapIso i).hom ≫ (rangeIso i).hom ≫ (eWP i).hom ≫ pW i
  have hxLocal (i : I) : xLocal i ≫ descentMap = qX i := by
    have hlocalMap' : localMap i = (eWP i).inv ≫ (rangeIso i).inv ≫ qX' i := rfl
    have hcancel : (rangeIso i).hom ≫ (eWP i).hom ≫ localMap i = qX' i := by
      rw [hlocalMap']
      simp only [Iso.hom_inv_id_assoc]
    calc
      xLocal i ≫ descentMap =
          (swapIso i).hom ≫ ((rangeIso i).hom ≫ (eWP i).hom ≫
            (pW i ≫ descentMap)) := by simp only [xLocal, Category.assoc]
      _ = (swapIso i).hom ≫ ((rangeIso i).hom ≫ (eWP i).hom ≫ localMap i) := by
        rw [hdescentLocal]
      _ = (swapIso i).hom ≫ qX' i := by rw [hcancel]
      _ = qX i := ObjectProperty.hom_ext _ (Limits.pullbackSymmetry_hom_comp_fst (g i).hom f.hom)
  have : Mono wι := (ObjectProperty.ι _).mono_of_mono_map (inferInstanceAs (Mono W.1.ι))
  have hxLocalBase (i : I) : xLocal i ≫ wι = qX i ≫ f := by
    rw [← hdescentBase, ← Category.assoc, hxLocal]
  have hxCompatible : ∀ i j,
      (ObjectProperty.homMk (Limits.pullback.fst (qX i).hom (qX j).hom) :
        AlgebraicSpaces.fiberProduct B S hS (qX i) (qX j) ⟶ PX i) ≫ xLocal i =
      (ObjectProperty.homMk (Limits.pullback.snd (qX i).hom (qX j).hom) :
        AlgebraicSpaces.fiberProduct B S hS (qX i) (qX j) ⟶ PX j) ≫ xLocal j := by
    intro i j
    let r₀ : AlgebraicSpaces.fiberProduct B S hS (qX i) (qX j) ⟶ PX i :=
      ObjectProperty.homMk (Limits.pullback.fst (qX i).hom (qX j).hom)
    let r₁ : AlgebraicSpaces.fiberProduct B S hS (qX i) (qX j) ⟶ PX j :=
      ObjectProperty.homMk (Limits.pullback.snd (qX i).hom (qX j).hom)
    have hr : r₀ ≫ qX i = r₁ ≫ qX j := ObjectProperty.hom_ext _ Limits.pullback.condition
    apply (cancel_mono wι).mp
    change (r₀ ≫ xLocal i) ≫ wι = (r₁ ≫ xLocal j) ≫ wι
    calc
      (r₀ ≫ xLocal i) ≫ wι = (r₀ ≫ qX i) ≫ f := by
        rw [Category.assoc, hxLocalBase, ← Category.assoc]
      _ = (r₁ ≫ qX j) ≫ f := by rw [hr]
      _ = (r₁ ≫ xLocal j) ≫ wι := by
        rw [Category.assoc r₁ (xLocal j), hxLocalBase, ← Category.assoc]
  obtain ⟨inverseMap, hinverseLocal, _⟩ :=
    existsUnique_desc_of_fpqcCovering B S hS
      qX hqXcover Wsp xLocal hxCompatible
  have hinverseBase : inverseMap ≫ wι = f := by
    apply hom_ext_of_fpqcCovering B S hS qX hqXcover
    intro i
    rw [← Category.assoc, hinverseLocal, hxLocalBase]
  have hinverseDescent : inverseMap ≫ descentMap = 𝟙 X := by
    apply hom_ext_of_fpqcCovering B S hS qX hqXcover
    intro i
    rw [← Category.assoc, hinverseLocal, hxLocal, Category.comp_id]
  have hdescentInverse : descentMap ≫ inverseMap = 𝟙 Wsp := by
    apply (cancel_mono wι).mp
    rw [Category.assoc, hinverseBase, hdescentBase, Category.id_comp]
  have : IsIso inverseMap.hom :=
    ⟨⟨descentMap.hom, congrArg (fun k => k.hom) hinverseDescent,
      congrArg (fun k => k.hom) hdescentInverse⟩⟩
  let Q := MorphismProperty.presheaf
    (MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))
  have : Q.RespectsIso := inferInstance
  have hopen : Q (inverseMap.hom ≫ wι.hom) :=
    MorphismProperty.RespectsIso.precomp Q inverseMap.hom wι.hom W.2.2
  change Q f.hom
  rw [← hinverseBase]
  exact hopen

/-- **Stacks 041X.** Being an open immersion of algebraic spaces over `S` is local on the base
for the fpqc topology. -/
@[stacks 041X]
instance openImmersion_isLocalAtTarget_fpqc
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    (openImmersionProperty B S hS).IsLocalAtTarget
      (Topology.precoverage.{u, v} .fpqc B S hS) := by
  apply MorphismProperty.IsLocalAtTarget.mk_of_iff
  intro X Y f R hR
  constructor
  · intro hf U g _ _
    exact isOpenImmersion_of_isPullback B S hS (IsPullback.of_hasPullback f g) hf
  · intro hf
    obtain ⟨I, Yi, g, rfl, hcover⟩ := hR
    exact isOpenImmersion_of_fpqcCovering B S hS g hcover.2.2 f fun i =>
      (isOpenImmersion_pullback_iff B S hS f (g i)).mpr (hf (g i) (Presieve.ofArrows.mk i))

end AlgebraicGeometry.Space

end
