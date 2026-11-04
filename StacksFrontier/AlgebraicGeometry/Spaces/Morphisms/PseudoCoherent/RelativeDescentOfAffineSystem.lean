module

public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.RelativeDescentSchemeLimit
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.RelativelyPerfectColimit
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.AlternatingCech.DiagonalComplementQuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperBaseChange
public import StacksFrontier.CategoryTheory.Limits.PullbackOfLimitCones
public import StacksFrontier.AlgebraicGeometry.EventualLimitProperties.Basic
public import Mathlib.CategoryTheory.Presentable.Directed

/-!
# Situation 0DKU from a directed system of affine objects of the site

Let `T` be a directed system of affine objects of the big fppf site of `S`, indexed by the
opposite of a directed preorder, whose underlying schemes have a limit cone `d`. A flat, finitely
presented morphism `p₀ : X₀ ⟶ T a₀` at one stage and a cartesian square exhibiting `X ⟶ d.pt` as
its base change to the limit make up a Situation 0DKU: the stages are the represented algebraic
spaces of `T`, the limit is the vertex of `d`, and the base changes to the later stages are fibre
products of presheaves. This is the Situation of the source's proof of Stacks 0DKX, for the
system of the spectra of the finitely generated subrings of a ring.

## Main definitions

* `AlgebraicGeometry.Space.RelativeDescentSituation.ofAffineSystem`: the Situation 0DKU.

## Main results

* `AlgebraicGeometry.Space.RelativeDescentSituation.isSchemeLimit_ofAffineSystem`: its limit is a
  limit of schemes (`AlgebraicGeometry.Space.RelativeDescentSituation.IsSchemeLimit`).
* `AlgebraicGeometry.Space.RelativeDescentSituation.isProper_stageStructure_of_isProper`: in any
  Situation 0DKU the base changes `Xᵢ ⟶ Yᵢ` are proper once `X₀ ⟶ Y₀` is.

## Implementation notes

The limit is given as the cone `d` in the site and is a limit of algebraic spaces because the
forgetful functor to schemes reflects connected limits and the Yoneda embedding preserves limits.
The proof of `isSchemeLimit_ofAffineSystem` is that of
`AlgebraicGeometry.Space.ComplexesSituation.isSchemeLimit_descentSituation`, for a system of
objects of the site rather than of test schemes over a Situation 0DLE: a representation of the
base changes along an affine chart `Z ⟶ T a₀` is, on underlying schemes, the base change of the
limit cone along `Z ⟶ T a₀`, and a fibre product of limit cones is a limit cone.

## References

* [Stacks Project, Tag 0DKU](https://stacks.math.columbia.edu/tag/0DKU)
* [Stacks Project, Tag 0DKX](https://stacks.math.columbia.edu/tag/0DKX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space.RelativeDescentSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {α : Type u} [Preorder α] [IsDirected α (· ≤ ·)] [Nonempty α]
  (T : αᵒᵖ ⥤ BigFppfOver B S hS) (d : Cone T)
  (hd : IsLimit ((BigFppfOver.toScheme B S hS).mapCone d))
  (hT : ∀ a, IsAffine ((BigFppfOver.toScheme B S hS).obj (T.obj a)))
  (a₀ : α) {X₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX₀ : IsAlgebraicSpace B S hS X₀)
  (p₀ : X₀ ⟶ yoneda.obj (T.obj (op a₀))) (hflat : IsFlat B S hS p₀)
  (hfp : IsFinitePresentation B S hS p₀)
  {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
  (toInitial : X ⟶ X₀) (toLimit : X ⟶ yoneda.obj d.pt)
  (hpb : IsPullback toLimit toInitial (yoneda.map (d.π.app (op a₀))) p₀)

attribute [local instance] IsCofiltered.isConnected in
/-- The vertex of `d` is the limit of `T` in the site, read as algebraic spaces. -/
def isLimitYonedaMapCone : IsLimit (yoneda.mapCone d) :=
  isLimitOfPreserves yoneda (isLimitOfReflects (BigFppfOver.toScheme B S hS) hd)

/-- The transition morphism `T b ⟶ T a` of the system, for `a ≤ b`, read as algebraic spaces. -/
abbrev affineSystemMap {a b : α} (h : a ≤ b) :
    yoneda.obj (T.obj (op b)) ⟶ yoneda.obj (T.obj (op a)) :=
  yoneda.map (T.map (homOfLE h).op)

omit [IsDirected α (· ≤ ·)] [Nonempty α] in
/-- The transition morphisms of the system compose. -/
theorem affineSystemMap_comp {a b c : α} (hab : a ≤ b) (hbc : b ≤ c) :
    affineSystemMap T hbc ≫ affineSystemMap T hab = affineSystemMap T (hab.trans hbc) := by
  rw [affineSystemMap, affineSystemMap, affineSystemMap, ← yoneda.map_comp, ← T.map_comp]
  rfl

variable {T d} in
include hd hT hX₀ hflat hfp hX hpb in
/-- **Situation 0DKU of a directed system of affine objects of the site.** The stages are the
represented algebraic spaces of a directed system `T` of affine objects of the site whose
underlying schemes have the vertex of `d` as their limit; the flat finitely presented space over
the stage `a₀` is `p₀ : X₀ ⟶ T a₀`, its base changes to the later stages are the fibre products of
presheaves, and its base change to the limit is a given cartesian square `X ⟶ d.pt`. -/
def ofAffineSystem (hZ : B.Contains (⊤_ Scheme.{u})) : RelativeDescentSituation B S hS hZ α where
  Y := T ⋙ yoneda
  limitCone := yoneda.mapCone d
  isLimit := isLimitYonedaMapCone T d hd
  stage_isAlgebraicSpace a := isAlgebraicSpace_yoneda B S hS _
  limit_isAlgebraicSpace := isAlgebraicSpace_yoneda B S hS _
  stage_isQuasiCompact a := isQuasiCompactSpace_yoneda_of_isAffine B S hS _ (hT (op a))
  stage_isQuasiSeparated a :=
    haveI := hT (op a)
    isAbsolutelyQuasiSeparated_yoneda_obj B S hS hZ _ inferInstance
  transition_isAffine a b h :=
    haveI := hT (op a)
    haveI := hT (op b)
    isAffineHom_yoneda_map B S hS (T.map (homOfLE h).op)
  i₀ := a₀
  X₀ := X₀
  p₀ := p₀
  initial_isAlgebraicSpace := hX₀
  initial_isFlat := hflat
  initial_isFinitePresentation := hfp
  Xᵢ a h := pullback p₀ (affineSystemMap T h)
  stageX_isAlgebraicSpace a h :=
    isAlgebraicSpace_pullback B S hS _ _ hX₀ (isAlgebraicSpace_yoneda B S hS _)
      (isAlgebraicSpace_yoneda B S hS _)
  toX₀ a h := pullback.fst _ _
  toYᵢ a h := pullback.snd _ _
  stage_isPullback a h := (IsPullback.of_hasPullback p₀ (affineSystemMap T h)).flip
  fᵢⱼ a b ha hb h := pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ affineSystemMap T h) (by
    rw [pullback.condition, Category.assoc, affineSystemMap_comp])
  fᵢⱼ_toYᵢ a b ha hb h := pullback.lift_snd _ _ _
  fᵢⱼ_toX₀ a b ha hb h := pullback.lift_fst _ _ _
  X := X
  X_isAlgebraicSpace := hX
  toInitial := toInitial
  toLimit := toLimit
  limit_isPullback := hpb
  fᵢ a h := pullback.lift toInitial (toLimit ≫ yoneda.map (d.π.app (op a))) (by
    rw [← hpb.w, Category.assoc, affineSystemMap, ← yoneda.map_comp, d.w])
  fᵢ_toYᵢ a h := pullback.lift_snd _ _ _
  fᵢ_toX₀ a h := pullback.lift_fst _ _ _

/-! ### The limit is a limit of schemes -/

attribute [local instance] CategoryTheory.Limits.comp_preservesLimitsOfShape in
/-- The functor to schemes preserves fibre products. -/
local instance preservesPullbacks_bigFppfOverToScheme_ofAffineSystem :
    PreservesLimitsOfShape WalkingCospan (BigFppfOver.toScheme B S hS) :=
  comp_preservesLimitsOfShape _ _

variable {T d hd hT a₀ hX₀ p₀ hflat hfp hX toInitial toLimit hpb} in
attribute [local instance] IsCofiltered.isConnected in
/-- **The limit of `ofAffineSystem` is a limit of schemes on affine charts.** The projection
`d.pt ⟶ T a₀` is a morphism of affine schemes, and a representation of the base changes along an
affine chart `Z ⟶ T a₀` is, on underlying schemes, the base change of the limit cone of the
`T a`, `a ≥ a₀`, along `Z ⟶ T a₀`, which is a limit cone because a fibre product of limit cones
is a limit cone (`CategoryTheory.Limits.isLimitOfIsPullbackOfIsLimit`). -/
theorem isSchemeLimit_ofAffineSystem (hZ : B.Contains (⊤_ Scheme.{u})) :
    (ofAffineSystem hd hT a₀ hX₀ p₀ hflat hfp hX toInitial toLimit hpb hZ).IsSchemeLimit := by
  set D' := ofAffineSystem hd hT a₀ hX₀ p₀ hflat hfp hX toInitial toLimit hpb hZ
  let toS := BigFppfOver.toScheme B S hS
  have : ∀ i, IsAffine ((T ⋙ toS).obj i) := hT
  have hpt : IsAffine (toS.obj d.pt) := EventualLimit.isAffine_of_isLimit (T ⋙ toS) _ hd
  refine ⟨?_, fun Z z R => ⟨?_⟩⟩
  · have : IsAffine (toS.obj (T.obj (op a₀))) := hT _
    exact isAffineHom_yoneda_map B S hS (U := d.pt) (V := T.obj (op a₀)) (d.π.app (op a₀))
  -- the index of the stages beyond `a₀`, and its initial inclusion
  let K := D'.LaterIndex
  let k₀ : K := ⟨a₀, le_rfl⟩
  have hk₀ : ∀ k : K, k₀ ≤ k := fun k => k.2
  have : Nonempty K := ⟨k₀⟩
  have : IsDirected K (· ≤ ·) := ⟨fun x y => by
    obtain ⟨c, hxc, hyc⟩ := directed_of (· ≤ ·) x.1 y.1
    exact ⟨⟨c, x.2.trans hxc⟩, hxc, hyc⟩⟩
  let incl : K ⥤ α := (Subtype.mono_coe (fun a : α => a₀ ≤ a)).functor
  have : incl.Final := Functor.final_of_exists_of_isFiltered _
    (fun a => by
      obtain ⟨c, hac, hc₀⟩ := directed_of (· ≤ ·) a a₀
      exact ⟨⟨c, hc₀⟩, ⟨homOfLE hac⟩⟩)
    (fun {_ c} _ _ => ⟨c, 𝟙 _, Subsingleton.elim _ _⟩)
  let Y' : Kᵒᵖ ⥤ Scheme.{u} := incl.op ⋙ T ⋙ toS
  let L : Cone Y' := (toS.mapCone d).whisker incl.op
  have hL : IsLimit L :=
    (Functor.Initial.isLimitWhiskerEquiv incl.op _).symm hd
  -- the maps of the representation, as morphisms of the site
  let P : ∀ k : K, R.W.obj (op k) ⟶ T.obj (op k.1) := fun k =>
    Yoneda.fullyFaithful.preimage (R.p k)
  have hP : ∀ k, yoneda.map (P k) = R.p k := fun k => Yoneda.fullyFaithful.map_preimage _
  let Pc : R.c.pt ⟶ d.pt := Yoneda.fullyFaithful.preimage R.pc
  have hPc : yoneda.map Pc = R.pc := Yoneda.fullyFaithful.map_preimage _
  let z₀ : (BigAffineFppf.inclusion B S hS).obj Z ⟶ T.obj (op a₀) :=
    Yoneda.fullyFaithful.preimage z
  have hz₀ : yoneda.map z₀ = z := Yoneda.fullyFaithful.map_preimage _
  -- the equations of the representation, in the site
  have hyo : ∀ {P' X' Y'} {fst : P' ⟶ X'} {snd : P' ⟶ Y'} {f : X' ⟶ T.obj (op a₀)}
      {g : Y' ⟶ T.obj (op a₀)}, IsPullback (yoneda.map fst) (yoneda.map snd) (yoneda.map f)
        (yoneda.map g) → IsPullback fst snd f g := fun H =>
    IsPullback.of_map yoneda (yoneda.map_injective
      ((yoneda.map_comp _ _).trans (H.w.trans (yoneda.map_comp _ _).symm))) H
  have hsq : ∀ k : K, IsPullback (P k) (R.q k) (T.map (homOfLE (hk₀ k)).op) z₀ := fun k =>
    hyo (by
      rw [hP k, hz₀]
      exact R.isPullback k)
  have hsqc : IsPullback Pc R.qc (d.π.app (op a₀)) z₀ :=
    hyo (by
      rw [hPc, hz₀]
      exact R.isPullback_pt)
  have hp : ∀ (i j : K) (h : i ≤ j), R.W.map (homOfLE h).op ≫ P i =
      P j ≫ T.map (homOfLE (show i.1 ≤ j.1 from h)).op := fun i j h =>
    yoneda.map_injective (by
      rw [Functor.map_comp, Functor.map_comp, hP, hP]
      exact R.map_p i j h)
  have hπp : ∀ k : K, R.c.π.app (op k) ≫ P k = Pc ≫ d.π.app (op k.1) :=
    fun k => yoneda.map_injective (by
      rw [Functor.map_comp, Functor.map_comp, hP, hPc]
      exact R.π_p k)
  have hmor : ∀ {k k' : Kᵒᵖ} (f : k ⟶ k'), f = (homOfLE (leOfHom f.unop)).op :=
    fun _ => Subsingleton.elim _ _
  -- the three diagrams and the two transformations
  let Zs := toS.obj ((BigAffineFppf.inclusion B S hS).obj Z)
  let α₁ : Y' ⟶ (Functor.const Kᵒᵖ).obj (Y'.obj (op k₀)) :=
    { app := fun k => Y'.map (homOfLE (hk₀ k.unop)).op
      naturality := fun k k' f => by
        simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id]
        rw [← Y'.map_comp]
        rfl }
  let β₁ : (Functor.const Kᵒᵖ).obj Zs ⟶ (Functor.const Kᵒᵖ).obj (Y'.obj (op k₀)) :=
    (Functor.const Kᵒᵖ).map (toS.map z₀)
  let π₁ : R.W ⋙ toS ⟶ Y' :=
    { app := fun k => toS.map (P k.unop)
      naturality := fun k k' f => by
        rw [hmor f]
        show toS.map (R.W.map (homOfLE _).op) ≫ toS.map (P k'.unop) =
          toS.map (P k.unop) ≫ toS.map (T.map (homOfLE _).op)
        rw [← toS.map_comp, ← toS.map_comp, hp] }
  let π₂ : R.W ⋙ toS ⟶ (Functor.const Kᵒᵖ).obj Zs :=
    { app := fun k => toS.map (R.q k.unop)
      naturality := fun k k' f => by
        rw [hmor f]
        simp [← toS.map_comp, R.map_q] }
  exact CategoryTheory.Limits.isLimitOfIsPullbackOfIsLimit (α := α₁) (β := β₁) (π₁ := π₁) (π₂ := π₂)
    (c₁ := L) (c₂ := constCone Kᵒᵖ Zs) (c₃ := constCone Kᵒᵖ (Y'.obj (op k₀)))
    (d := toS.mapCone R.c) (z₁ := toS.map Pc) (z₂ := toS.map R.qc)
    (g₁ := L.π.app (op k₀)) (g₂ := toS.map z₀)
    (fun k => (hsq k.unop).map toS) hL (isLimitConstCone _ _) (isLimitConstCone _ _)
    (hsqc.map toS)
    (fun k => by
      show toS.map (R.c.π.app (op k.unop)) ≫ toS.map (P k.unop) =
        toS.map Pc ≫ toS.map (d.π.app (op k.unop.1))
      rw [← toS.map_comp, ← toS.map_comp, hπp])
    (fun k => by
      show toS.map (R.c.π.app (op k.unop)) ≫ toS.map (R.q k.unop) = toS.map R.qc ≫ 𝟙 _
      rw [← toS.map_comp, R.π_q, Category.comp_id])
    (fun k => by
      show L.π.app k ≫ α₁.app k = L.π.app (op k₀) ≫ 𝟙 _
      rw [Category.comp_id]
      exact L.w (homOfLE (hk₀ k.unop)).op)
    (fun k => by
      show 𝟙 _ ≫ toS.map z₀ = toS.map z₀ ≫ 𝟙 _
      rw [Category.id_comp, Category.comp_id])

/-! ### Properness of the base changes -/

/-- The base changes `Xᵢ ⟶ Yᵢ` of a Situation 0DKU are proper once `X₀ ⟶ Y₀` is: properness is
stable under base change (Stacks 04WP). -/
theorem isProper_stageStructure_of_isProper {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type*}
    [Preorder I] [IsDirected I (· ≤ ·)] (D : RelativeDescentSituation B S hS hZ I)
    (hp : IsProper B S hS D.p₀) (i : D.LaterIndex) :
    IsProper B S hS (D.stageStructure i).hom :=
  MorphismProperty.of_isPullback (P := fun ⦃F G : AlgebraicSpaces B S hS⦄ (f : F ⟶ G) =>
    IsProper B S hS f.hom) (D.isPullback_stageStructure i).flip
    (show IsProper B S hS D.initialStructure.hom from hp)

end AlgebraicGeometry.Space.RelativeDescentSituation

end
