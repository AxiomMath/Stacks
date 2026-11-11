module

public import Mathlib.CategoryTheory.Sites.Subcanonical
public import Mathlib.CategoryTheory.Sites.SubcanonicalOver
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.StackOfSheafTorsors
public import StacksFrontier.CategoryTheory.Sites.Descent.IsStack.SieveDescentDatum
public import StacksFrontier.CategoryTheory.Sites.Glueing.GlueingSheaves
public import StacksFrontier.CategoryTheory.Sites.Glueing.MapsOfSheavesGlue
public import StacksFrontier.CategoryTheory.Sites.Localization.SheavesOverRepresentable
public import StacksFrontier.CategoryTheory.Sites.Stack.Groupoid
public import StacksFrontier.CategoryTheory.Sites.Stack.StackBridge.DescentDatum
import StacksFrontier.AlgebraicGeometry.Topologies.Fppf
import StacksFrontier.CategoryTheory.Sites.LocallySurjectiveBaseChange
import StacksFrontier.CategoryTheory.Sites.Stack.StackBridge.ReverseEffective
import all StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.StackOfSheafTorsors
import all StacksFrontier.CategoryTheory.Sites.Glueing.GlueingSheaves

/-!
# Effectivity of descent for torsors for a group object over a sheaf

Let `S` be a scheme in a big fppf site, let `ℬ` be a sheaf on the big fppf site of `S` and let
`𝒢 ⟶ ℬ` be a map of sheaves carrying a group law over `ℬ`. Stacks 04UM asserts that the functor
`p : 𝒢/ℬ-Torsors ⥤ (Sch/S)_fppf` of Stacks 04UL defines a stack in groupoids over the big fppf
site of `S`, that is, the three conditions of Stacks 02ZI. Conditions (1) and (2) are
`AlgebraicGeometry.Space.SheafTorsors.projection_isFiberedInGroupoids` and
`AlgebraicGeometry.Space.SheafTorsors.projection_isomIsSheaf`. This file proves condition (3),
effectivity of descent data, and assembles the three.

## Main results

* `AlgebraicGeometry.Space.SheafTorsors.projection_effectiveDescent`: **Stacks 04UM**,
  condition (3) of Stacks 02ZI for `p : 𝒢/ℬ-Torsors ⥤ (Sch/S)_fppf`: every descent datum
  relative to a covering family of the big fppf site of `S` is effective.
* `AlgebraicGeometry.Space.SheafTorsors.projection_isStackInGroupoids`: **Stacks 04UM**, the
  three conditions together.
* `AlgebraicGeometry.Space.SheafTorsors.projection_hasEffectiveDescent`: condition (3) of
  Stacks 026F, the sieve-indexed form of the same assertion.

## Implementation notes

The glueing is the glueing of sheaves on the slice sites, Stacks 04TR, applied to the descent
datum of sheaves underlying the given datum of torsors; the action and the two torsor conditions
are then carried along, being fppf-local on the base. The sections of a torsor live in the
universe of the morphisms of the site, one below the universe of its objects, while the glued
sheaf produced by Stacks 04TR has its sections one universe up; the passage back down is the
subcovering by a family indexed in the lower universe, which the big fppf site admits, together
with the replacement of the sections of the glued sheaf by a model of them in that universe.

## References

* [Stacks Project, Tag 04UM](https://stacks.math.columbia.edu/tag/04UM)
* [Stacks Project, Tag 02ZI](https://stacks.math.columbia.edu/tag/02ZI)
* [Stacks Project, Tag 04UL](https://stacks.math.columbia.edu/tag/04UL)
* [Stacks Project, Tag 04TR](https://stacks.math.columbia.edu/tag/04TR)
-/

@[expose] public noncomputable section

-- The values of `CategoryTheory.GrothendieckTopology.pseudofunctorOver` are the categories of
-- sheaves on the slices only after that definition is unfolded; the composites below mix the two
-- spellings, so it is unfolded at the transparency instances and unification use.
attribute [local instance_reducible] CategoryTheory.GrothendieckTopology.pseudofunctorOver
  CategoryTheory.LocallyDiscrete.mkPseudofunctor CategoryTheory.pseudofunctorOfIsLocallyDiscrete
  Quiver.Hom.toLoc AlgebraicGeometry.Space.sheafPullbackGroup CategoryTheory.Functor.mapGrp
attribute [local implicit_reducible] AlgebraicGeometry.Space.SheafTorsors.projection
  CategoryTheory.Functor.Fiber CategoryTheory.Functor.Fiber.fiberInclusion

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open MonoidalCategory
open scoped MonoidalCategory MonObj

universe u w
universe u₁ v₁ u₂ w₁

namespace AlgebraicGeometry.Space

namespace SheafTorsors

variable {𝒞 : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : 𝒞.Contains S}
  {B : (AlgebraicGeometry.BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u}

private theorem bigFppf_closedUnderPullbacks (𝒞 : AlgebraicGeometry.BigFppfSite.{u}) :
    (AlgebraicGeometry.schemeSizeBelow 𝒞.cutoff).IsClosedUnderLimitsOfShape WalkingCospan := by
  refine ⟨fun T ⟨p⟩ => ?_⟩
  let f := p.diag.map WalkingCospan.Hom.inl
  let g := p.diag.map WalkingCospan.Hom.inr
  have e : T ≅ pullback f g := (IsPullback.of_isLimit_cone p.isLimit).isoPullback
  change T.size < 𝒞.cutoff
  rw [Scheme.size_congr e]
  exact Scheme.size_pullback_lt f g
    (p.prop_diag_obj WalkingCospan.left) (p.prop_diag_obj WalkingCospan.right)

private theorem existsUnique_section_glue_ofArrows
    {D : Type u₁} [Category.{v₁, u₁} D] [HasPullbacks D] (J : GrothendieckTopology D)
    {P : Dᵒᵖ ⥤ Type u₂} (hP : Presheaf.IsSheaf J P)
    {U : D} {I : Type w₁} {V : I → D} (f : ∀ i, V i ⟶ U)
    (hcover : Sieve.ofArrows V f ∈ J U)
    (Vij : I → I → D) (pr₁ : ∀ i j, Vij i j ⟶ V i)
    (pr₂ : ∀ i j, Vij i j ⟶ V j)
    (hVij : ∀ i j, IsPullback (pr₁ i j) (pr₂ i j) (f i) (f j))
    (s : ∀ i, P.obj (Opposite.op (V i)))
    (hs : ∀ i j, P.map (pr₁ i j).op (s i) = P.map (pr₂ i j).op (s j)) :
    ∃! t : P.obj (Opposite.op U), ∀ i, P.map (f i).op t = s i := by
  have hsheaf : Presieve.IsSheafFor P (Presieve.ofArrows V f) := by
    apply (Presieve.isSheafFor_iff_generate (Presieve.ofArrows V f)).2
    simpa [Sieve.ofArrows] using hP.isSheafFor (Sieve.ofArrows V f) hcover
  have hcompat : Presieve.Arrows.PullbackCompatible P f s := by
    intro i j
    have h := congrArg (P.map ((hVij i j).isoPullback.inv).op) (hs i j)
    simpa only [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp,
      (hVij i j).isoPullback_inv_fst, (hVij i j).isoPullback_inv_snd] using h
  exact (Presieve.isSheafFor_arrows_iff_pullbacks P f).mp hsheaf s hcompat

private def groupChartIso
    (G : Grp (Over B)) {U V : AlgebraicGeometry.BigFppfOver 𝒞 S hS}
    (f : V ⟶ U) (b : yoneda.obj U ⟶ B) (b' : yoneda.obj V ⟶ B)
    (hf : yoneda.map f ≫ b = b') :
    sheafPullbackGroup G V b' ≅
      (Over.pullback (yoneda.map f)).mapGrp.obj (sheafPullbackGroup G U b) :=
  eqToIso (congrArg (sheafPullbackGroup G V) hf.symm) ≪≫ sheafPullbackGroupCompIso G f b

private theorem isIso_leftSMul_ofIsos
    {E : Type u₁} [Category.{v₁} E] [CartesianMonoidalCategory E]
    {R R' M M' : E} [MonObj R] [MonObj R'] [ModObj R M]
    (e : R ≅ R') [IsMonHom e.hom] (d : M ≅ M') [IsIso (ModObj.leftSMul R M)] :
    letI := ModObj.ofIso e d
    IsIso (ModObj.leftSMul R' M') := by
  let := ModObj.ofIso e d
  have h : ModObj.leftSMul R' M' =
      (e.inv ⊗ₘ d.inv) ≫ ModObj.leftSMul R M ≫ (d.hom ⊗ₘ d.hom) := by
    apply CartesianMonoidalCategory.hom_ext
    · simp only [ModObj.leftSMul_fst, Category.assoc,
        CartesianMonoidalCategory.tensorHom_fst, ModObj.leftSMul_fst_assoc]
      rfl
    · simp only [ModObj.leftSMul_snd, Category.assoc,
        CartesianMonoidalCategory.tensorHom_snd, ModObj.leftSMul_snd_assoc]
      rw [← Category.assoc, CartesianMonoidalCategory.tensorHom_snd,
        Category.assoc, d.inv_hom_id, Category.comp_id]
  rw [h]
  infer_instance

variable (G : Grp (Over B))
variable {G}
private theorem groupChartIso_fst_fst
    (G : Grp (Over B)) {U V : AlgebraicGeometry.BigFppfOver 𝒞 S hS}
    (f : V ⟶ U) (b : yoneda.obj U ⟶ B) (b' : yoneda.obj V ⟶ B)
    (hf : yoneda.map f ≫ b = b') :
    (groupChartIso G f b b' hf).hom.hom.hom.left ≫
        pullback.fst (pullback.snd G.X.hom b) (yoneda.map f) ≫ pullback.fst G.X.hom b =
      pullback.fst G.X.hom b' := by
  subst b'
  simp only [groupChartIso, eqToIso_refl, Iso.refl_trans]
  change (((Over.pullbackComp (yoneda.map f) b).hom.app G.X) ≫ 𝟙 _).left ≫ _ ≫ _ = _
  simp only [Category.comp_id]
  exact pullbackComp_hom_app_fst_fst (yoneda.map f) b G.X

private theorem Hom.comp_sec_app
    {T T' : SheafTorsors G} (φ : Hom T T') {V W : AlgebraicGeometry.BigFppfOver 𝒞 S hS}
    (hT : T.base = V) (hT' : T'.base = W) (f : V ⟶ W)
    (hf : φ.base = eqToHom hT ≫ f ≫ eqToHom hT'.symm) :
    T.sec.app (Opposite.op V) (eqToHom hT.symm) =
      T'.sec.app (Opposite.op V) (f ≫ eqToHom hT'.symm) := by
  have h := congrArg (fun α : yoneda.obj T.base ⟶ B =>
    α.app (Opposite.op V) (eqToHom hT.symm)) φ.comp_sec
  simpa [NatTrans.comp_app, yoneda_map_app, hf, Category.assoc] using h.symm

private theorem section_restrict
    {V W U : AlgebraicGeometry.BigFppfOver 𝒞 S hS} (f : W ⟶ V)
    (b : yoneda.obj U ⟶ B) (hU : U = V) :
    B.map (Opposite.op f) (b.app (Opposite.op V) (eqToHom hU.symm)) =
      b.app (Opposite.op W) (f ≫ eqToHom hU.symm) := by
  have h := congrArg (fun k => k (eqToHom hU.symm)) (b.naturality (Opposite.op f))
  simpa [yoneda_obj_obj, ConcreteCategory.comp_apply] using h.symm

variable (G)
private def torsorFiberPresheaf {U : AlgebraicGeometry.BigFppfOver 𝒞 S hS}
    (T : SheafTorsors G) (hTU : T.base = U) : (Over U)ᵒᵖ ⥤ Type u :=
  OverShriek.fiber (𝟙 (yoneda.obj U)) (T.total.hom ≫ yoneda.map (eqToHom hTU))

private theorem torsorFiberPresheaf_isSheaf {U : AlgebraicGeometry.BigFppfOver 𝒞 S hS}
    (T : SheafTorsors G) (hTU : T.base = U) :
    Presheaf.IsSheaf ((AlgebraicGeometry.BigFppfOver.topology 𝒞 S hS).over U)
      (torsorFiberPresheaf G T hTU) := by
  let J := AlgebraicGeometry.BigFppfOver.topology 𝒞 S hS
  have hF' : Presheaf.IsSheaf (J.over U) ((Over.forget U).op ⋙ T.total.left) :=
    (Over.forget U).op_comp_isSheaf_of_isSheaf (J.over U) J T.total.left T.isSheaf
  have hU' : Presheaf.IsSheaf (J.over U) ((Over.forget U).op ⋙ yoneda.obj U) :=
    (Over.forget U).op_comp_isSheaf_of_isSheaf (J.over U) J (yoneda.obj U)
      ((isAlgebraicSpace_yoneda 𝒞 S hS U).isSheaf)
  rw [isSheaf_iff_isSheaf_of_type]
  exact OverShriek.isSheaf_fiber (K := J.over U) (𝟙 (yoneda.obj U))
    (T.total.hom ≫ yoneda.map (eqToHom hTU))
    ((isSheaf_iff_isSheaf_of_type (J.over U) _).1 hF')
    (((isSheaf_iff_isSheaf_of_type (J.over U) _).1 hU').isSeparated)

private def fiberMapOver
    {C : Type u₁} [Category.{v₁} C] {U V : C} (f : V ⟶ U)
    (P : Over (yoneda.obj U)) (Q : Over (yoneda.obj V))
    (g : Q.left ⟶ P.left) (hg : g ≫ P.hom = Q.hom ≫ yoneda.map f) :
    OverShriek.fiber (𝟙 (yoneda.obj V)) Q.hom ⟶
      (Over.map f).op ⋙ OverShriek.fiber (𝟙 (yoneda.obj U)) P.hom where
  app W := ↾fun s => ⟨g.app _ s.1, by
    change P.hom.app _ (g.app _ s.1) = W.unop.hom ≫ f
    exact (congrArg (fun k => k.app (Opposite.op W.unop.left) s.1) hg).trans
      (congrArg (· ≫ f) s.2)⟩
  naturality {W W'} k := by
    ext s
    apply Subtype.ext
    exact g.naturality_apply k.unop.left.op s.1

private theorem fiberMapOver_bijective
    {C : Type u₁} [Category.{v₁} C] {U V : C} (f : V ⟶ U)
    (P : Over (yoneda.obj U)) (Q : Over (yoneda.obj V))
    (g : Q.left ⟶ P.left) (hg : IsPullback g Q.hom P.hom (yoneda.map f))
    (W : (Over V)ᵒᵖ) : Function.Bijective ((fiberMapOver f P Q g hg.w).app W) := by
  let E := (evaluation Cᵒᵖ (Type v₁)).obj (Opposite.op W.unop.left)
  refine ⟨fun x y h => Subtype.ext (Types.ext_of_isPullback (hg.map E)
    (congrArg Subtype.val h) (x.2.trans y.2.symm)), fun s => ?_⟩
  obtain ⟨t, ht, ht'⟩ := Types.exists_of_isPullback (hg.map E) s.1 W.unop.hom s.2
  exact ⟨⟨t, ht'⟩, Subtype.ext ht⟩

private noncomputable def fiberIsoOfPullback
    {C : Type u₁} [Category.{v₁} C] {U V : C} (f : V ⟶ U)
    (P : Over (yoneda.obj U)) (Q : Over (yoneda.obj V))
    (g : Q.left ⟶ P.left) (hg : IsPullback g Q.hom P.hom (yoneda.map f)) :
    OverShriek.fiber (𝟙 (yoneda.obj V)) Q.hom ≅
      (Over.map f).op ⋙ OverShriek.fiber (𝟙 (yoneda.obj U)) P.hom :=
  NatIso.ofComponents
    (fun W => (Equiv.ofBijective ((fiberMapOver f P Q g hg.w).app W)
      (fiberMapOver_bijective f P Q g hg W)).toIso)
    (fun k => (fiberMapOver f P Q g hg.w).naturality k)

private theorem isLocallySurjective_of_covering_family
    {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C)
    {P Q : Cᵒᵖ ⥤ Type u₂} (p : P ⟶ Q)
    {I : Type w₁} {Q' : I → Cᵒᵖ ⥤ Type u₂} (q : ∀ i, Q' i ⟶ Q)
    (hq : ∀ (W : C) (x : Q.obj (Opposite.op W)), familyImageSieve q x ∈ J W)
    {P' : I → Cᵒᵖ ⥤ Type u₂} (a : ∀ i, P' i ⟶ P) (p' : ∀ i, P' i ⟶ Q' i)
    (hw : ∀ i, a i ≫ p = p' i ≫ q i)
    (hp : ∀ i, Presheaf.IsLocallySurjective J (p' i)) :
    Presheaf.IsLocallySurjective J p := by
  constructor
  intro W x
  apply J.transitive (hq W x)
  rintro Z f ⟨i, t, ht⟩
  have := hp i
  apply J.superset_covering _ (Presheaf.imageSieve_mem J (p' i) t)
  rintro Y g ⟨s, hs⟩
  refine ⟨(a i).app _ s, ?_⟩
  change p.app _ ((a i).app _ s) = Q.map (g ≫ f).op x
  calc
    _ = (q i).app _ ((p' i).app _ s) :=
      congrArg (fun k => k.app (Opposite.op Y) s) (hw i)
    _ = (q i).app _ ((Q' i).map g.op t) := congrArg ((q i).app _) hs
    _ = Q.map g.op ((q i).app _ t) := (q i).naturality_apply g.op t
    _ = _ := by rw [ht]; simp only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply]

theorem isIso_of_covering_pullbacks
    {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C)
    {P Q R : Cᵒᵖ ⥤ Type u₂} (hP : Presheaf.IsSheaf J P)
    (hQ : Presheaf.IsSheaf J Q) (p : P ⟶ R) (q : Q ⟶ R)
    (g : P ⟶ Q) (hg : g ≫ q = p)
    {I : Type w₁} {R' P' Q' : I → Cᵒᵖ ⥤ Type u₂}
    (ρ : ∀ i, R' i ⟶ R) (π : ∀ i, P' i ⟶ P) (τ : ∀ i, Q' i ⟶ Q)
    (p' : ∀ i, P' i ⟶ R' i) (q' : ∀ i, Q' i ⟶ R' i)
    (hπ : ∀ i, IsPullback (π i) (p' i) p (ρ i))
    (hτ : ∀ i, IsPullback (τ i) (q' i) q (ρ i))
    (hcover : ∀ (W : C) (x : Q.obj (Opposite.op W)), familyImageSieve τ x ∈ J W)
    (e : ∀ i, P' i ≅ Q' i) (he : ∀ i, π i ≫ g = (e i).hom ≫ τ i)
    (he' : ∀ i, (e i).hom ≫ q' i = p' i) : IsIso g := by
  have hinj (W : C) (x y : P.obj (Opposite.op W))
      (hxy : g.app _ x = g.app _ y) : x = y := by
    apply (hP.isSheafFor _ (hcover W (g.app _ x))).isSeparatedFor.ext
    rintro Z f ⟨i, t, ht⟩
    let E := (evaluation Cᵒᵖ (Type u₂)).obj (Opposite.op Z)
    have hx : p.app _ (P.map f.op x) = (ρ i).app _ ((q' i).app _ t) := by
      rw [← congrArg (fun k => k.app (Opposite.op Z) (P.map f.op x)) hg,
        NatTrans.comp_app, ConcreteCategory.comp_apply, g.naturality_apply, ← ht]
      exact congrArg (fun k => k.app (Opposite.op Z) t) (hτ i).w
    have hy : p.app _ (P.map f.op y) = (ρ i).app _ ((q' i).app _ t) := by
      rw [← congrArg (fun k => k.app (Opposite.op Z) (P.map f.op y)) hg,
        NatTrans.comp_app, ConcreteCategory.comp_apply, g.naturality_apply, ← hxy, ← ht]
      exact congrArg (fun k => k.app (Opposite.op Z) t) (hτ i).w
    obtain ⟨x', hx', hxp⟩ := Types.exists_of_isPullback ((hπ i).map E)
      (P.map f.op x) ((q' i).app _ t) hx
    obtain ⟨y', hy', hyp⟩ := Types.exists_of_isPullback ((hπ i).map E)
      (P.map f.op y) ((q' i).app _ t) hy
    have hEq : (e i).hom.app _ x' = (e i).hom.app _ y' := by
      apply Types.ext_of_isPullback ((hτ i).map E)
      · calc
          _ = g.app _ ((π i).app _ x') :=
            (congrArg (fun k => k.app (Opposite.op Z) x') (he i)).symm
          _ = g.app _ ((π i).app _ y') := by
            change (π i).app (Opposite.op Z) x' = P.map f.op x at hx'
            change (π i).app (Opposite.op Z) y' = P.map f.op y at hy'
            rw [hx', hy', g.naturality_apply, g.naturality_apply, hxy]
          _ = _ := congrArg (fun k => k.app (Opposite.op Z) y') (he i)
      · exact (congrArg (fun k => k.app (Opposite.op Z) x') (he' i)).trans
          (hxp.trans (hyp.symm.trans
            (congrArg (fun k => k.app (Opposite.op Z) y') (he' i)).symm))
    have hEq' : x' = y' := by simpa using congrArg ((e i).inv.app (Opposite.op Z)) hEq
    exact hx'.symm.trans ((congrArg ((π i).app _) hEq').trans hy')
  obtain ⟨g', hg', -⟩ := exists_hom_of_familyImageSieve J hP τ hcover
    (fun i => (e i).inv ≫ π i) (fun W i j s t hst => hinj _ _ _ (by
      calc
        _ = (τ i).app _ s := by
          change (((e i).inv ≫ π i) ≫ g).app _ s = _
          simp only [Category.assoc, he, Iso.inv_hom_id_assoc]
        _ = (τ j).app _ t := hst
        _ = _ := by
          change _ = (((e j).inv ≫ π j) ≫ g).app _ t
          simp only [Category.assoc, he, Iso.inv_hom_id_assoc]))
  have hright : g' ≫ g = 𝟙 Q := by
    apply hom_ext_of_familyImageSieve J hQ τ hcover
    intro i
    rw [← Category.assoc, hg', Category.assoc, he]
    simp
  have hleft : g ≫ g' = 𝟙 P := by
    ext W x
    exact hinj _ _ _ (congrArg (fun k => k.app W (g.app W x)) hright)
  exact ⟨⟨g', hleft, hright⟩⟩

@[implicit_reducible] private def modObjOfJointlyFaithful
    {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
    {I : Type w} {D : I → Type u₂} [∀ i, Category.{w₁} (D i)]
    [∀ i, MonoidalCategory (D i)] (F : ∀ i, C ⥤ D i) [∀ i, (F i).Monoidal]
    (R M : C) [MonObj R]
    (hF : ∀ {X : C} (f g : X ⟶ M), (∀ i, (F i).map f = (F i).map g) → f = g) (a : R ⊗ M ⟶ M)
    (act : ∀ i, letI := (F i).monObjObj R; ModObj ((F i).obj R) ((F i).obj M))
    (ha : ∀ i, Functor.LaxMonoidal.μ (F i) R M ≫ (F i).map a = (act i).smul) :
    ModObj R M := by
  refine ⟨a, ?_, ?_⟩
  · change η[R] ▷ M ≫ a = (λ_ M).hom
    apply hF
    intro i
    let H := F i
    let := H.monObjObj R
    let := act i
    change H.map _ = H.map _
    apply (cancel_epi (Functor.LaxMonoidal.ε H ▷ H.obj M ≫
      Functor.LaxMonoidal.μ H (𝟙_ C) M)).1
    calc
      _ = (Functor.LaxMonoidal.ε H ≫ H.map (η[R])) ▷ H.obj M ≫
          (Functor.LaxMonoidal.μ H R M ≫ H.map a) := by
        simp only [Functor.map_comp, Category.assoc, comp_whiskerRight]
        slice_lhs 2 3 => rw [← Functor.LaxMonoidal.μ_natural_left H (η[R]) M]
        simp only [Category.assoc]
      _ = η[H.obj R] ▷ H.obj M ≫ γ[H.obj R, H.obj M] := by rw [ha]; rfl
      _ = (λ_ (H.obj M)).hom := ModObj.one_smul (M := H.obj R) (H.obj M)
      _ = _ := by simpa only [Category.assoc] using Functor.LaxMonoidal.left_unitality H M
  · change μ[R] ▷ M ≫ a = (α_ R R M).hom ≫ R ◁ a ≫ a
    apply hF
    intro i
    let H := F i
    let := H.monObjObj R
    let := act i
    change H.map _ = H.map _
    apply (cancel_epi (Functor.LaxMonoidal.μ H R R ▷ H.obj M ≫
      Functor.LaxMonoidal.μ H (R ⊗ R) M)).1
    calc
      _ = (Functor.LaxMonoidal.μ H R R ≫ H.map (μ[R])) ▷ H.obj M ≫
          (Functor.LaxMonoidal.μ H R M ≫ H.map a) := by
        simp only [Functor.map_comp, Category.assoc, comp_whiskerRight]
        slice_lhs 2 3 => rw [← Functor.LaxMonoidal.μ_natural_left H (μ[R]) M]
        simp only [Category.assoc]
      _ = μ[H.obj R] ▷ H.obj M ≫ γ[H.obj R, H.obj M] := by rw [ha]; rfl
      _ = (α_ (H.obj R) (H.obj R) (H.obj M)).hom ≫
          H.obj R ◁ γ[H.obj R, H.obj M] ≫ γ[H.obj R, H.obj M] :=
        ModObj.mul_smul (M := H.obj R) (H.obj M)
      _ = (α_ (H.obj R) (H.obj R) (H.obj M)).hom ≫
          H.obj R ◁ (Functor.LaxMonoidal.μ H R M ≫ H.map a) ≫
            (Functor.LaxMonoidal.μ H R M ≫ H.map a) := by rw [ha]
      _ = _ := by
        simp only [Functor.map_comp, whiskerLeft_comp, Category.assoc]
        slice_lhs 3 4 => rw [Functor.LaxMonoidal.μ_natural_right H R a]
        simp only [Category.assoc]
        slice_rhs 1 3 => rw [Functor.LaxMonoidal.associativity H R R M]
        simp only [Category.assoc]


private theorem familyImageSieve_pullback_fst_mem
    {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C)
    {P Y : Cᵒᵖ ⥤ Type u₂} (p : P ⟶ Y)
    {I : Type w₁} {Y' : I → Cᵒᵖ ⥤ Type u₂} (ρ : ∀ i, Y' i ⟶ Y)
    (hρ : ∀ (W : C) (x : Y.obj (Opposite.op W)), familyImageSieve ρ x ∈ J W)
    (W : C) (x : P.obj (Opposite.op W)) :
    familyImageSieve (fun i => pullback.fst p (ρ i)) x ∈ J W := by
  apply J.superset_covering _ (hρ W (p.app _ x))
  rintro Z f ⟨i, y, hy⟩
  obtain ⟨t, ht, -⟩ := Types.exists_of_isPullback
    ((IsPullback.of_hasPullback p (ρ i)).map
      ((evaluation Cᵒᵖ (Type u₂)).obj (Opposite.op Z)))
    (P.map f.op x) y ((p.naturality_apply f.op x).trans hy.symm)
  exact ⟨i, t, ht⟩

private theorem over_pullback_jointly_faithful
    {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C)
    {Y : Cᵒᵖ ⥤ Type u₂} {I : Type w₁} {Y' : I → Cᵒᵖ ⥤ Type u₂}
    (ρ : ∀ i, Y' i ⟶ Y)
    (hρ : ∀ (W : C) (x : Y.obj (Opposite.op W)), familyImageSieve ρ x ∈ J W)
    (M : Over Y) (hM : Presheaf.IsSheaf J M.left)
    {X : Over Y} (a b : X ⟶ M)
    (h : ∀ i, (Over.pullback (ρ i)).map a = (Over.pullback (ρ i)).map b) : a = b := by
  apply Over.OverMorphism.ext
  apply hom_ext_of_familyImageSieve J hM (fun i => pullback.fst X.hom (ρ i))
    (familyImageSieve_pullback_fst_mem J X.hom ρ hρ)
  intro i
  have e := congrArg (fun k => k.left ≫ pullback.fst M.hom (ρ i)) (h i)
  simpa only [Over.pullback_map_left, pullback.lift_fst] using e

private theorem pullback_map_isPullback_snd
    {C : Type u₁} [Category.{v₁} C] [HasPullbacks C]
    {R M Y R' M' Y' : C} {r : R ⟶ Y} {m : M ⟶ Y}
    {r' : R' ⟶ Y'} {m' : M' ⟶ Y'}
    (α : R' ⟶ R) (π : M' ⟶ M) (ρ : Y' ⟶ Y)
    (hR : IsPullback α r' r ρ) (hM : π ≫ m = m' ≫ ρ) :
    IsPullback (pullback.map r' m' r m α π ρ hR.w.symm hM.symm)
      (pullback.snd r' m') (pullback.snd r m) π := by
  apply IsPullback.of_right (h₁₂ := pullback.fst r m) (h₂₂ := m)
    _ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback r m)
  simpa only [pullback.lift_fst, hM] using
    (IsPullback.of_hasPullback r' m').paste_horiz hR

private theorem isPullback_of_cartesian_cospan
    {C : Type u₁} [Category.{v₁} C]
    {A A₁ A₂ A₀ B B₁ B₂ B₀ : C}
    {a₁ : A ⟶ A₁} {a₂ : A ⟶ A₂} {f₁ : A₁ ⟶ A₀} {f₂ : A₂ ⟶ A₀}
    {b₁ : B ⟶ B₁} {b₂ : B ⟶ B₂} {g₁ : B₁ ⟶ B₀} {g₂ : B₂ ⟶ B₀}
    {p : A ⟶ B} {p₁ : A₁ ⟶ B₁} {p₂ : A₂ ⟶ B₂} {p₀ : A₀ ⟶ B₀}
    (h₁ : IsPullback a₁ p p₁ b₁) (h₂ : a₂ ≫ p₂ = p ≫ b₂)
    (h₃ : f₁ ≫ p₀ = p₁ ≫ g₁) (h₄ : IsPullback f₂ p₂ p₀ g₂)
    (hb : IsPullback b₁ b₂ g₁ g₂) (ha : a₁ ≫ f₁ = a₂ ≫ f₂) :
    IsPullback a₁ a₂ f₁ f₂ := by
  have h := h₁.paste_vert hb
  rw [← h₂, ← h₃] at h
  exact IsPullback.of_bot h ha h₄

section LocalActions

attribute [local instance] Over.cartesianMonoidalCategory

private abbrev pullbackTensorMap
    {C : Type u₁} [Category.{v₁} C] {Y Y' : Cᵒᵖ ⥤ Type u₂}
    (ρ : Y' ⟶ Y) (R M : Over Y) :=
  (Functor.LaxMonoidal.μ (Over.pullback ρ) R M).left ≫
    pullback.fst (R ⊗ M).hom ρ

private theorem pullbackChart_isPullback
    {C : Type u₁} [Category.{v₁} C] [HasPullbacks C]
    {Y Y' : C} (ρ : Y' ⟶ Y) (R : Over Y) (R' : Over Y')
    (e : R' ≅ (Over.pullback ρ).obj R) :
    IsPullback (e.hom.left ≫ pullback.fst R.hom ρ) R'.hom R.hom ρ := by
  have : IsIso e.hom.left := ((Over.forget Y').mapIso e).isIso_hom
  have h : IsPullback e.hom.left R'.hom (pullback.snd R.hom ρ) (𝟙 Y') :=
    IsPullback.of_horiz_isIso ⟨by simpa using Over.w e.hom⟩
  simpa only [Category.id_comp] using h.paste_horiz (IsPullback.of_hasPullback R.hom ρ)

private theorem tensorChartMap_eq
    {C : Type u₁} [Category.{v₁} C] {Y Y' : Cᵒᵖ ⥤ Type u₂}
    (ρ : Y' ⟶ Y) (R M : Over Y) (R' M' : Over Y')
    (eR : R' ≅ (Over.pullback ρ).obj R) (eM : M' ≅ (Over.pullback ρ).obj M)
    (hR : R'.hom ≫ ρ = (eR.hom.left ≫ pullback.fst R.hom ρ) ≫ R.hom)
    (hM : M'.hom ≫ ρ = (eM.hom.left ≫ pullback.fst M.hom ρ) ≫ M.hom) :
    (eR.hom ⊗ₘ eM.hom).left ≫ pullbackTensorMap ρ R M =
      pullback.map R'.hom M'.hom R.hom M.hom
        (eR.hom.left ≫ pullback.fst R.hom ρ)
        (eM.hom.left ≫ pullback.fst M.hom ρ) ρ hR hM := by
  apply pullback.hom_ext
  · simp only [pullbackTensorMap, Category.assoc, Over.μ_pullback_left_fst_fst,
      pullback.lift_fst]
    rw [Over.tensorHom_left, pullback.lift_fst_assoc, Category.assoc]
  · simp only [pullbackTensorMap, Category.assoc, Over.μ_pullback_left_fst_snd,
      pullback.lift_snd]
    rw [Over.tensorHom_left, pullback.lift_snd_assoc, Category.assoc]

private theorem modObj_ofIso_smul_comp
    {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
    {R R' M M' : C} [MonObj R] [MonObj R'] [ModObj R M]
    (eR : R ≅ R') [IsMonHom eR.hom] (eM : M ≅ M') :
    (eR.hom ⊗ₘ eM.hom) ≫ (ModObj.ofIso eR eM).smul = γ[R, M] ≫ eM.hom := by
  change (eR.hom ⊗ₘ eM.hom) ≫ (eR.inv ⊗ₘ eM.inv) ≫ γ[R, M] ≫ eM.hom = _
  rw [← Category.assoc, MonoidalCategory.tensorHom_comp_tensorHom]
  simp

private theorem pullbackTensorMap_hom
    {C : Type u₁} [Category.{v₁} C] {Y Y' : Cᵒᵖ ⥤ Type u₂}
    (ρ : Y' ⟶ Y) (R M : Over Y) :
    pullbackTensorMap ρ R M ≫ (R ⊗ M).hom =
      ((Over.pullback ρ).obj R ⊗ (Over.pullback ρ).obj M).hom ≫ ρ := by
  dsimp only [pullbackTensorMap]
  rw [Category.assoc, pullback.condition, ← Category.assoc]
  exact congrArg (· ≫ ρ) (Over.w (Functor.LaxMonoidal.μ (Over.pullback ρ) R M))

private theorem pullbackTensorMap_covering
    {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C)
    {Y : Cᵒᵖ ⥤ Type u₂} {I : Type w₁} {Y' : I → Cᵒᵖ ⥤ Type u₂}
    (ρ : ∀ i, Y' i ⟶ Y)
    (hρ : ∀ (W : C) (x : Y.obj (Opposite.op W)), familyImageSieve ρ x ∈ J W)
    (R M : Over Y) (W : C) (x : (R ⊗ M).left.obj (Opposite.op W)) :
    familyImageSieve (fun i => pullbackTensorMap (ρ i) R M) x ∈ J W := by
  let e (i : I) := (Over.forget (Y' i)).mapIso
    (asIso (Functor.LaxMonoidal.μ (Over.pullback (ρ i)) R M))
  change familyImageSieve (fun i => (e i).hom ≫ pullback.fst (R ⊗ M).hom (ρ i)) x ∈ J W
  rw [familyImageSieve_comp_iso]
  exact familyImageSieve_pullback_fst_mem J (R ⊗ M).hom ρ hρ W x

private theorem exists_actionMap_of_pullbacks
    {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C)
    {Y : Cᵒᵖ ⥤ Type u₂} (hY : Presheaf.IsSheaf J Y)
    {I : Type w₁} {Y' : I → Cᵒᵖ ⥤ Type u₂} (ρ : ∀ i, Y' i ⟶ Y)
    (hρ : ∀ (W : C) (x : Y.obj (Opposite.op W)), familyImageSieve ρ x ∈ J W)
    (R M : Over Y) (hM : Presheaf.IsSheaf J M.left)
    (a : ∀ i, (Over.pullback (ρ i)).obj R ⊗ (Over.pullback (ρ i)).obj M ⟶
      (Over.pullback (ρ i)).obj M)
    (hc : ∀ (W : C) (i j : I)
      (s : ((Over.pullback (ρ i)).obj R ⊗ (Over.pullback (ρ i)).obj M).left.obj
        (Opposite.op W))
      (t : ((Over.pullback (ρ j)).obj R ⊗ (Over.pullback (ρ j)).obj M).left.obj
        (Opposite.op W)),
      (pullbackTensorMap (ρ i) R M).app _ s = (pullbackTensorMap (ρ j) R M).app _ t →
      ((a i).left ≫ pullback.fst M.hom (ρ i)).app _ s =
        ((a j).left ≫ pullback.fst M.hom (ρ j)).app _ t) :
    ∃ α : R ⊗ M ⟶ M, ∀ i,
      Functor.LaxMonoidal.μ (Over.pullback (ρ i)) R M ≫ (Over.pullback (ρ i)).map α = a i := by
  obtain ⟨α, hα, -⟩ := exists_hom_of_familyImageSieve J hM
    (fun i => pullbackTensorMap (ρ i) R M) (pullbackTensorMap_covering J ρ hρ R M)
    (fun i => (a i).left ≫ pullback.fst M.hom (ρ i)) hc
  have hαhom : α ≫ M.hom = (R ⊗ M).hom := by
    apply hom_ext_of_familyImageSieve J hY (fun i => pullbackTensorMap (ρ i) R M)
      (pullbackTensorMap_covering J ρ hρ R M)
    intro i
    rw [← Category.assoc, hα, Category.assoc, pullback.condition, ← Category.assoc]
    exact (congrArg (· ≫ ρ i) (Over.w (a i))).trans (pullbackTensorMap_hom (ρ i) R M).symm
  refine ⟨Over.homMk α hαhom, ?_⟩
  intro i
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · simpa only [Over.comp_left, Over.pullback_map_left, Over.homMk_left, Category.assoc,
      pullback.lift_fst, pullbackTensorMap] using hα i
  · exact (Over.w (Functor.LaxMonoidal.μ (Over.pullback (ρ i)) R M ≫
      (Over.pullback (ρ i)).map (Over.homMk α hαhom))).trans (Over.w (a i)).symm

private theorem exists_modObj_of_pullbacks
    {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C)
    {Y : Cᵒᵖ ⥤ Type u₂} (hY : Presheaf.IsSheaf J Y)
    {I : Type w₁} {Y' : I → Cᵒᵖ ⥤ Type u₂} (ρ : ∀ i, Y' i ⟶ Y)
    (hρ : ∀ (W : C) (x : Y.obj (Opposite.op W)), familyImageSieve ρ x ∈ J W)
    (R M : Over Y) [MonObj R] (hM : Presheaf.IsSheaf J M.left)
    (act : ∀ i, letI := (Over.pullback (ρ i)).monObjObj R;
      ModObj ((Over.pullback (ρ i)).obj R) ((Over.pullback (ρ i)).obj M))
    (hc : ∀ (W : C) (i j : I)
      (s : ((Over.pullback (ρ i)).obj R ⊗ (Over.pullback (ρ i)).obj M).left.obj
        (Opposite.op W))
      (t : ((Over.pullback (ρ j)).obj R ⊗ (Over.pullback (ρ j)).obj M).left.obj
        (Opposite.op W)),
      (pullbackTensorMap (ρ i) R M).app _ s = (pullbackTensorMap (ρ j) R M).app _ t →
      ((act i).smul.left ≫ pullback.fst M.hom (ρ i)).app _ s =
        ((act j).smul.left ≫ pullback.fst M.hom (ρ j)).app _ t) :
    ∃ act' : ModObj R M, ∀ i,
      Functor.LaxMonoidal.μ (Over.pullback (ρ i)) R M ≫
        (Over.pullback (ρ i)).map act'.smul = (act i).smul := by
  obtain ⟨α, hα⟩ := exists_actionMap_of_pullbacks J hY ρ hρ R M hM
    (fun i => (act i).smul) hc
  exact ⟨modObjOfJointlyFaithful (fun i => Over.pullback (ρ i)) R M
    (fun a b h => over_pullback_jointly_faithful J ρ hρ M hM a b h) α act hα, hα⟩

private theorem over_pullback_jointly_reflects_isIso
    {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C)
    {Y : Cᵒᵖ ⥤ Type u₂} {I : Type w₁} {Y' : I → Cᵒᵖ ⥤ Type u₂}
    (ρ : ∀ i, Y' i ⟶ Y)
    (hρ : ∀ (W : C) (x : Y.obj (Opposite.op W)), familyImageSieve ρ x ∈ J W)
    {P Q : Over Y} (hP : Presheaf.IsSheaf J P.left)
    (hQ : Presheaf.IsSheaf J Q.left) (g : P ⟶ Q)
    (hg : ∀ i, IsIso ((Over.pullback (ρ i)).map g)) : IsIso g := by
  have : IsIso g.left := by
    apply isIso_of_covering_pullbacks J hP hQ P.hom Q.hom g.left (Over.w g)
      ρ (fun i => pullback.fst P.hom (ρ i)) (fun i => pullback.fst Q.hom (ρ i))
      (fun i => pullback.snd P.hom (ρ i)) (fun i => pullback.snd Q.hom (ρ i))
      (fun i => IsPullback.of_hasPullback _ _) (fun i => IsPullback.of_hasPullback _ _)
      (familyImageSieve_pullback_fst_mem J Q.hom ρ hρ)
      (fun i => by
        have := hg i
        exact (Over.forget (Y' i)).mapIso (asIso ((Over.pullback (ρ i)).map g)))
      (fun i => (pullback.lift_fst _ _ _).symm) (fun i => Over.w ((Over.pullback (ρ i)).map g))
  have : IsIso ((Over.forget Y).map g) := ‹IsIso g.left›
  exact isIso_of_reflects_iso g (Over.forget Y)

private theorem isIso_map_leftSMul_iff
    {E : Type u₁} [Category.{v₁} E] [CartesianMonoidalCategory E]
    {E' : Type u₂} [Category.{w₁} E'] [CartesianMonoidalCategory E']
    (F : E ⥤ E') [F.Monoidal] (R M : E) [MonObj R] [ModObj R M] :
    letI := F.monObjObj R
    letI := mapModObj F R M
    IsIso (ModObj.leftSMul (F.obj R) (F.obj M)) ↔ IsIso (F.map (ModObj.leftSMul R M)) := by
  let := F.monObjObj R
  let := mapModObj F R M
  have h : ModObj.leftSMul (F.obj R) (F.obj M) =
      Functor.LaxMonoidal.μ F R M ≫ F.map (ModObj.leftSMul R M) ≫
        Functor.OplaxMonoidal.δ F M M := by
    apply CartesianMonoidalCategory.hom_ext
    · simp only [ModObj.leftSMul_fst, Category.assoc, Functor.OplaxMonoidal.δ_fst,
        ← F.map_comp, ModObj.leftSMul_fst]
      rfl
    · simp only [ModObj.leftSMul_snd, Category.assoc, Functor.OplaxMonoidal.δ_snd,
        ← F.map_comp, ModObj.leftSMul_snd, Functor.Monoidal.μ_snd]
  rw [h, isIso_comp_left_iff, isIso_comp_right_iff]

private theorem isIso_leftSMul_of_pullbacks
    {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C)
    {Y : Cᵒᵖ ⥤ Type u₂} (hY : Presheaf.IsSheaf J Y)
    {I : Type w₁} {Y' : I → Cᵒᵖ ⥤ Type u₂} (ρ : ∀ i, Y' i ⟶ Y)
    (hρ : ∀ (W : C) (x : Y.obj (Opposite.op W)), familyImageSieve ρ x ∈ J W)
    (R M : Over Y) [MonObj R] [ModObj R M]
    (hR : Presheaf.IsSheaf J R.left) (hM : Presheaf.IsSheaf J M.left)
    (h : ∀ i, letI := (Over.pullback (ρ i)).monObjObj R;
      letI := mapModObj (Over.pullback (ρ i)) R M;
      IsIso (ModObj.leftSMul ((Over.pullback (ρ i)).obj R) ((Over.pullback (ρ i)).obj M))) :
    IsIso (ModObj.leftSMul R M) := by
  exact over_pullback_jointly_reflects_isIso J ρ hρ
    (isSheaf_pullback J R.hom M.hom hR hM hY)
    (isSheaf_pullback J M.hom M.hom hM hM hY) _
    fun i => (isIso_map_leftSMul_iff (Over.pullback (ρ i)) R M).1 (h i)

private theorem exists_pseudoTorsor_of_pullbacks
    {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C)
    {Y : Cᵒᵖ ⥤ Type u₂} (hY : Presheaf.IsSheaf J Y)
    {I : Type w₁} {Y' : I → Cᵒᵖ ⥤ Type u₂} (ρ : ∀ i, Y' i ⟶ Y)
    (hρ : ∀ (W : C) (x : Y.obj (Opposite.op W)), familyImageSieve ρ x ∈ J W)
    (R M : Over Y) [MonObj R]
    (hR : Presheaf.IsSheaf J R.left) (hM : Presheaf.IsSheaf J M.left)
    (act : ∀ i, letI := (Over.pullback (ρ i)).monObjObj R;
      ModObj ((Over.pullback (ρ i)).obj R) ((Over.pullback (ρ i)).obj M))
    (hc : ∀ (W : C) (i j : I)
      (s : ((Over.pullback (ρ i)).obj R ⊗ (Over.pullback (ρ i)).obj M).left.obj
        (Opposite.op W))
      (t : ((Over.pullback (ρ j)).obj R ⊗ (Over.pullback (ρ j)).obj M).left.obj
        (Opposite.op W)),
      (pullbackTensorMap (ρ i) R M).app _ s = (pullbackTensorMap (ρ j) R M).app _ t →
      ((act i).smul.left ≫ pullback.fst M.hom (ρ i)).app _ s =
        ((act j).smul.left ≫ pullback.fst M.hom (ρ j)).app _ t)
    (hT : ∀ i, letI := (Over.pullback (ρ i)).monObjObj R;
      letI := act i;
      IsIso (ModObj.leftSMul ((Over.pullback (ρ i)).obj R) ((Over.pullback (ρ i)).obj M)))
    (hloc : ∀ i, Presheaf.IsLocallySurjective J (pullback.snd M.hom (ρ i))) :
    ∃ act' : ModObj R M,
      (letI := act'; IsIso (ModObj.leftSMul R M)) ∧
      Presheaf.IsLocallySurjective J M.hom ∧
      ∀ i, Functor.LaxMonoidal.μ (Over.pullback (ρ i)) R M ≫
        (Over.pullback (ρ i)).map act'.smul = (act i).smul := by
  obtain ⟨act', hact⟩ := exists_modObj_of_pullbacks J hY ρ hρ R M hM act hc
  let := act'
  refine ⟨act', ?_, ?_, hact⟩
  · apply isIso_leftSMul_of_pullbacks J hY ρ hρ R M hR hM
    intro i
    let := (Over.pullback (ρ i)).monObjObj R
    have he : mapModObj (Over.pullback (ρ i)) R M = act i :=
      ModObj.ext _ _ (hact i)
    rw [he]
    exact hT i
  · exact isLocallySurjective_of_covering_family J M.hom ρ hρ
      (fun i => pullback.fst M.hom (ρ i)) (fun i => pullback.snd M.hom (ρ i))
      (fun i => pullback.condition) hloc

end LocalActions

private theorem isPullback_of_normalizedProjection
    {U V : AlgebraicGeometry.BigFppfOver 𝒞 S hS} (T : SheafTorsors G) (hT : T.base = V)
    (f : V ⟶ U) (P : Over (yoneda.obj U)) (π : T.total.left ⟶ P.left)
    (hπ : IsPullback π (normalizedProjection G T hT) P.hom (yoneda.map f)) :
    IsPullback π T.total.hom P.hom (yoneda.map (eqToHom hT ≫ f)) := by
  subst V
  simpa [normalizedProjection] using hπ

private abbrev restrictionOfHom {U V : AlgebraicGeometry.BigFppfOver 𝒞 S hS}
    {T T' : SheafTorsors G} (hT : (projection G).obj T = U)
    (hT' : (projection G).obj T' = V) (f : V ⟶ U) (φ : T' ⟶ T)
    (hφ : φ.base = eqToHom hT' ≫ f ≫ eqToHom hT.symm) :
    Functor.Restriction (projection G) f T hT := by
  have hl : (projection G).IsHomLift
      (eqToHom hT' ≫ f ≫ eqToHom hT.symm) φ := by
    rw [← hφ]
    exact CategoryTheory.IsHomLift.map _ _
  letI := hl
  exact ⟨T', hT', φ, hl,
    (projection_isFiberedInGroupoids G).isStronglyCartesian_homLift _ φ⟩

private theorem torsorHom_eq_of_comp {T₁ T₂ T₃ : SheafTorsors G} (φ : T₂ ⟶ T₃)
    {a b : T₁ ⟶ T₂} (hf : a.base = b.base) (h : a ≫ φ = b ≫ φ) : a = b := by
  apply Hom.ext hf
  apply φ.isPullback.hom_ext
  · exact congrArg Hom.map h
  · rw [a.isPullback.w, b.isPullback.w, hf]

private theorem restriction_compTo_eq {U V W : AlgebraicGeometry.BigFppfOver 𝒞 S hS}
    (T : SheafTorsors G) (hT : (projection G).obj T = U) (f : V ⟶ U) (k : W ⟶ V)
    {l : W ⟶ U} (hl : l = k ≫ f)
    (r : Functor.Restriction (projection G) f T hT)
    (s : Functor.Restriction (projection G) l T hT) (a : s.pt ⟶ r.pt)
    (ha : a.base = eqToHom s.hpt ≫ k ≫ eqToHom r.hpt.symm)
    (h : a ≫ r.hom = s.hom) :
    Functor.Restriction.compTo (projection G) k f hl r s = a :=
  torsorHom_eq_of_comp G r.hom ((restriction_compTo_f G T hT f k hl r s).trans ha.symm)
    ((Functor.Restriction.compTo_hom _ _ _ _ _ _).trans h.symm)

section FiberSheaves
open Opposite
private def torsorFiberOver (U : AlgebraicGeometry.BigFppfOver 𝒞 S hS) :
    (projection G).Fiber U ⥤ Over (yoneda.obj U) where
  obj T := Over.mk (normalizedProjection G T.1 T.2)
  map {T T'} φ := Over.homMk φ.1.map (by
    have := φ.2
    have hφ := CategoryTheory.IsHomLift.fac' (projection G) (𝟙 U) φ.1
    have hp := hom_normalized_isPullback G T.2 T'.2 φ.1 (𝟙 U) hφ
    simpa using hp.w)
  map_id _ := by ext; rfl
  map_comp _ _ := by ext; rfl

private def torsorFiberSheaf (U : AlgebraicGeometry.BigFppfOver 𝒞 S hS) :
    (projection G).Fiber U ⥤
      Sheaf ((AlgebraicGeometry.BigFppfOver.topology 𝒞 S hS).over U) (Type u) :=
  ObjectProperty.lift _ (torsorFiberOver G U ⋙ OverShriek.fiberFunctor (𝟙 (yoneda.obj U)))
    (fun T => torsorFiberPresheaf_isSheaf G T.1 T.2)


private def torsorFiberSheafPullbackIso
    [(projection G).IsFibered]
    {U V : AlgebraicGeometry.BigFppfOver 𝒞 S hS}
    (T : (projection G).Fiber U) (f : V ⟶ U) :
    (torsorFiberSheaf G V).obj (Functor.pullbackFiber (projection G) T f) ≅
      ((AlgebraicGeometry.BigFppfOver.topology 𝒞 S hS).overMapPullback (Type u) f).obj
        ((torsorFiberSheaf G U).obj T) := by
  let φ := Functor.IsPreFibered.pullbackMap T.2 f
  have hφ := CategoryTheory.IsHomLift.fac' (projection G) f φ
  have hp := hom_normalized_isPullback G
    (Functor.IsPreFibered.pullbackObj_proj T.2 f) T.2 φ f hφ
  let e := fiberIsoOfPullback f
    (Over.mk (normalizedProjection G T.1 T.2))
    (Over.mk (normalizedProjection G _ (Functor.IsPreFibered.pullbackObj_proj T.2 f)))
    φ.map hp
  exact ⟨⟨e.hom⟩, ⟨e.inv⟩, Sheaf.hom_ext e.hom_inv_id, Sheaf.hom_ext e.inv_hom_id⟩

private theorem torsorFiberSheafPullbackIso_restriction
    [(projection G).IsFibered]
    {U V : AlgebraicGeometry.BigFppfOver 𝒞 S hS}
    (T : SheafTorsors G) (hT : T.base = U) (f : V ⟶ U)
    (r : Functor.Restriction (projection G) f T hT) :
    (torsorFiberSheaf G V).map r.fiberIso.inv ≫
        (torsorFiberSheafPullbackIso G (Functor.Fiber.mk hT) f).hom =
      (⟨(fiberIsoOfPullback f (Over.mk (normalizedProjection G T hT))
        (Over.mk (normalizedProjection G r.pt r.hpt)) r.hom.map
        (restriction_isPullback G T hT f r)).hom⟩ :
          (torsorFiberSheaf G V).obj (Functor.Fiber.mk r.hpt) ⟶
          ((AlgebraicGeometry.BigFppfOver.topology 𝒞 S hS).overMapPullback (Type u) f).obj
            ((torsorFiberSheaf G U).obj (Functor.Fiber.mk hT))) := by
  ext W x
  exact Subtype.ext (congrArg (fun k => k.app (op W.unop.left) x.val)
    (congrArg Hom.map r.fiberIso_inv_fac))

private theorem torsorFiberSheafPullbackIso_naturality
    [(projection G).IsFibered]
    {U V : AlgebraicGeometry.BigFppfOver 𝒞 S hS}
    {T T' : (projection G).Fiber U} (α : T ⟶ T') (f : V ⟶ U) :
    (torsorFiberSheafPullbackIso G T f).hom ≫
        ((AlgebraicGeometry.BigFppfOver.topology 𝒞 S hS).overMapPullback (Type u) f).map
          ((torsorFiberSheaf G U).map α) =
      (torsorFiberSheaf G V).map (Functor.pullbackFiberHom α f) ≫
        (torsorFiberSheafPullbackIso G T' f).hom := by
  ext W s
  apply Subtype.ext
  have hg := congrArg (fun φ => φ.map) (Functor.pullbackFiberHom_fac α f)
  exact (congrArg (fun k => k s.1) (NatTrans.congr_app hg (op W.unop.left))).symm

private theorem torsorFiberSheafPullbackIso_comp
    [(projection G).IsFibered]
    {U V W : AlgebraicGeometry.BigFppfOver 𝒞 S hS}
    (T : (projection G).Fiber U) (f : V ⟶ U) (g : W ⟶ V) :
    (torsorFiberSheaf G W).map (Functor.pullbackFiberCompIso T f g).hom ≫
        (torsorFiberSheafPullbackIso G T (g ≫ f)).hom =
      (torsorFiberSheafPullbackIso G (Functor.pullbackFiber (projection G) T f) g).hom ≫
        ((AlgebraicGeometry.BigFppfOver.topology 𝒞 S hS).overMapPullback (Type u) g).map
          (torsorFiberSheafPullbackIso G T f).hom ≫
        (((AlgebraicGeometry.BigFppfOver.topology 𝒞 S hS).pseudofunctorOver (Type u)).mapComp
          f.op.toLoc g.op.toLoc).inv.toNatTrans.app ((torsorFiberSheaf G U).obj T) := by
  apply Sheaf.hom_ext
  ext Z s
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    GrothendieckTopology.pseudofunctorOver_mapComp_inv_toNatTrans_app_hom_app]
  apply Subtype.ext
  have h := Functor.pullbackFiberCompIso'_hom_fac T f g (g ≫ f) rfl
  have hg := congrArg (fun φ => φ.map) h
  have hs := congrArg (fun k => k s.1) (NatTrans.congr_app hg (op Z.unop.left))
  change _ = T.1.total.left.map (𝟙 (op Z.unop.left))
    ((Functor.IsPreFibered.pullbackMap
      (Functor.pullbackFiber (projection G) T f).2 g ≫
      Functor.IsPreFibered.pullbackMap T.2 f).map.app (op Z.unop.left) s.1)
  rw [CategoryTheory.Functor.map_id]
  exact hs

section Descent
variable [(projection G).IsFibered]
variable {U : AlgebraicGeometry.BigFppfOver 𝒞 S hS} {I : Type w}
  {V : I → AlgebraicGeometry.BigFppfOver 𝒞 S hS} {f : ∀ i, V i ⟶ U}
  {Vij : I → I → AlgebraicGeometry.BigFppfOver 𝒞 S hS} {pr₁ : ∀ i j, Vij i j ⟶ V i}
  {pr₂ : ∀ i j, Vij i j ⟶ V j}
  {hVij : ∀ i j, IsPullback (pr₁ i j) (pr₂ i j) (f i) (f j)}
  {Vijk : I → I → I → AlgebraicGeometry.BigFppfOver 𝒞 S hS}
  {s₁₂ : ∀ i j k, Vijk i j k ⟶ Vij i j} {s₂₃ : ∀ i j k, Vijk i j k ⟶ Vij j k}
  {hVijk : ∀ i j k, IsPullback (s₁₂ i j k) (s₂₃ i j k) (pr₂ i j) (pr₁ j k)}
  {q₁ : ∀ i j k, Vijk i j k ⟶ V i} {q₂ : ∀ i j k, Vijk i j k ⟶ V j}
  {q₃ : ∀ i j k, Vijk i j k ⟶ V k}
  {hq₁ : ∀ i j k, q₁ i j k = s₁₂ i j k ≫ pr₁ i j}
  {hq₂ : ∀ i j k, q₂ i j k = s₁₂ i j k ≫ pr₂ i j}
  {hq₃ : ∀ i j k, q₃ i j k = s₂₃ i j k ≫ pr₂ j k}
  (D : Functor.DescentDatum (projection G) V f Vij pr₁ pr₂ hVij Vijk s₁₂ s₂₃ hVijk q₁ q₂ q₃
    hq₁ hq₂ hq₃)


private def torsorDescentSheafIso {W : AlgebraicGeometry.BigFppfOver 𝒞 S hS}
    (i j : I) (p : W ⟶ V i) (q : W ⟶ V j) (h : p ≫ f i = q ≫ f j) :
    ((AlgebraicGeometry.BigFppfOver.topology 𝒞 S hS).overMapPullback (Type u) p).obj
        ((torsorFiberSheaf G (V i)).obj (Functor.Fiber.mk (D.hx i))) ≅
      ((AlgebraicGeometry.BigFppfOver.topology 𝒞 S hS).overMapPullback (Type u) q).obj
        ((torsorFiberSheaf G (V j)).obj (Functor.Fiber.mk (D.hx j))) :=
  (torsorFiberSheafPullbackIso G (Functor.Fiber.mk (D.hx i)) p).symm ≪≫
    (torsorFiberSheaf G W).mapIso (D.glue i j p q h) ≪≫
    torsorFiberSheafPullbackIso G (Functor.Fiber.mk (D.hx j)) q

private theorem torsorDescentSheafIso_self {W : AlgebraicGeometry.BigFppfOver 𝒞 S hS}
    (i : I) (p : W ⟶ V i) :
    (torsorDescentSheafIso G D i i p p rfl).hom = 𝟙 _ := by
  simp [torsorDescentSheafIso, D.glue_self]

private theorem torsorDescentSheafIso_trans {W : AlgebraicGeometry.BigFppfOver 𝒞 S hS}
    (i j k : I) (p : W ⟶ V i) (q : W ⟶ V j) (r : W ⟶ V k)
    (h₁ : p ≫ f i = q ≫ f j) (h₂ : q ≫ f j = r ≫ f k) :
    (torsorDescentSheafIso G D i j p q h₁).hom ≫
        (torsorDescentSheafIso G D j k q r h₂).hom =
      (torsorDescentSheafIso G D i k p r (h₁.trans h₂)).hom := by
  simp only [torsorDescentSheafIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Category.assoc ((torsorFiberSheaf G W).map _) _,
    ← CategoryTheory.Functor.map_comp, D.glue_trans]

private theorem torsorDescentSheafIso_pullHom
    {W Z : AlgebraicGeometry.BigFppfOver 𝒞 S hS}
    (i j : I) (p : W ⟶ V i) (q : W ⟶ V j) (h : p ≫ f i = q ≫ f j)
    (g : Z ⟶ W) (h' : (g ≫ p) ≫ f i = (g ≫ q) ≫ f j) :
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom
      (F := (AlgebraicGeometry.BigFppfOver.topology 𝒞 S hS).pseudofunctorOver (Type u))
      (torsorDescentSheafIso G D i j p q h).hom g (g ≫ p) (g ≫ q) rfl rfl =
      (torsorDescentSheafIso G D i j (g ≫ p) (g ≫ q) h').hom := by
  let Ti := Functor.Fiber.mk (D.hx i)
  let Tj := Functor.Fiber.mk (D.hx j)
  let R := torsorFiberSheaf G Z
  let c := (Functor.pullbackFiberCompIso Ti p g).hom
  refine (cancel_epi (R.map c ≫ (torsorFiberSheafPullbackIso G Ti (g ≫ p)).hom)).mp ?_
  simp only [torsorDescentSheafIso, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Category.assoc]
  conv_lhs => rw [← Category.assoc, torsorFiberSheafPullbackIso_comp]
  have ec {Y : AlgebraicGeometry.BigFppfOver 𝒞 S hS} (a : W ⟶ Y) :
      ((AlgebraicGeometry.BigFppfOver.topology 𝒞 S hS).pseudofunctorOver (Type u)).mapComp'
        a.op.toLoc g.op.toLoc (g ≫ a).op.toLoc (by grind) =
      ((AlgebraicGeometry.BigFppfOver.topology 𝒞 S hS).pseudofunctorOver (Type u)).mapComp
        a.op.toLoc g.op.toLoc :=
    Pseudofunctor.mapComp'_eq_mapComp
      (F := (AlgebraicGeometry.BigFppfOver.topology 𝒞 S hS).pseudofunctorOver (Type u))
      a.op.toLoc g.op.toLoc
  simp only [Pseudofunctor.LocallyDiscreteOpToCat.pullHom, ec, Ti, R, c,
    Category.assoc, CategoryTheory.Functor.map_comp, Iso.hom_inv_id_assoc]
  let L := (AlgebraicGeometry.BigFppfOver.topology 𝒞 S hS).overMapPullback (Type u) g
  let ai := torsorFiberSheafPullbackIso G Ti p
  let aj := torsorFiberSheafPullbackIso G Tj q
  let bi := torsorFiberSheafPullbackIso G
    (Functor.pullbackFiber (projection G) Ti p) g
  let bj := torsorFiberSheafPullbackIso G
    (Functor.pullbackFiber (projection G) Tj q) g
  -- The coherence isomorphisms of `pseudofunctorOver` are those of `overMapPullback`, spelled
  -- here on the categories of sheaves so that the composites below are formed in one category.
  let di := (((AlgebraicGeometry.BigFppfOver.topology 𝒞 S hS).overMapPullbackComp (Type u)
      g p).app ((torsorFiberSheaf G (V i)).obj Ti)).symm
  let dj := (((AlgebraicGeometry.BigFppfOver.topology 𝒞 S hS).overMapPullbackComp (Type u)
      g q).app ((torsorFiberSheaf G (V j)).obj Tj)).symm
  change bi.hom ≫ L.map ai.hom ≫ di.inv ≫ di.hom ≫ L.map ai.inv ≫
      L.map ((torsorFiberSheaf G W).map (D.glue i j p q h).hom) ≫
      L.map aj.hom ≫ dj.inv = _
  simp only [Iso.inv_hom_id_assoc, ← L.map_comp_assoc]
  simp only [Iso.hom_inv_id_assoc, L.map_comp]
  have hn : bi.hom ≫ L.map ((torsorFiberSheaf G W).map (D.glue i j p q h).hom) =
      R.map (Functor.pullbackFiberHom (D.glue i j p q h).hom g) ≫ bj.hom :=
    torsorFiberSheafPullbackIso_naturality G (D.glue i j p q h).hom g
  simp only [Category.assoc]
  rw [← Category.assoc bi.hom (L.map ((torsorFiberSheaf G W).map (D.glue i j p q h).hom)), hn]
  have hcj : bj.hom ≫ L.map aj.hom ≫ dj.inv =
      R.map (Functor.pullbackFiberCompIso Tj q g).hom ≫
        (torsorFiberSheafPullbackIso G Tj (g ≫ q)).hom :=
    (torsorFiberSheafPullbackIso_comp G Tj q g).symm
  rw [Category.assoc, hcj]
  simp only [← Category.assoc, ← CategoryTheory.Functor.map_comp]
  congr 2
  rw [D.pullbackFiberHom_glue i j p q h g (g ≫ p) rfl (g ≫ q) rfl h']
  simp only [Tj, Functor.pullbackFiberCompIso, Category.assoc, Iso.inv_hom_id, Category.comp_id]


private def torsorSheafDescentData :
    ((AlgebraicGeometry.BigFppfOver.topology 𝒞 S hS).pseudofunctorOver (Type u)).DescentData f where
  obj i := (torsorFiberSheaf G (V i)).obj (Functor.Fiber.mk (D.hx i))
  hom {W} q {i j} p₁ p₂ h₁ h₂ :=
    (torsorDescentSheafIso G D i j p₁ p₂ (h₁.trans h₂.symm)).hom
  hom_self := by
    intro W q i p hp
    exact torsorDescentSheafIso_self G D i p
  hom_comp := by
    intro W q i j k p₁ p₂ p₃ h₁ h₂ h₃
    exact torsorDescentSheafIso_trans G D i j k p₁ p₂ p₃ _ _
  pullHom_hom := by
    intro W' W g q q' hq i j p₁ p₂ h₁ h₂ gp₁ gp₂ hg₁ hg₂
    subst gp₁ gp₂ q'
    exact torsorDescentSheafIso_pullHom G D i j p₁ p₂ _ g _

private theorem torsorDescentSheafIso_overlap (i j : I) :
    ((torsorFiberSheaf G (Vij i j)).map (D.xrij i j).fiberIso.inv ≫
        (torsorFiberSheafPullbackIso G (Functor.Fiber.mk (D.hx i)) (pr₁ i j)).hom) ≫
        (torsorDescentSheafIso G D i j (pr₁ i j) (pr₂ i j) (hVij i j).w).hom =
      (torsorFiberSheaf G (Vij i j)).map (Functor.fibreHomMk (D.φ_fibreHom i j)) ≫
        ((torsorFiberSheaf G (Vij i j)).map (D.xrji i j).fiberIso.inv ≫
          (torsorFiberSheafPullbackIso G (Functor.Fiber.mk (D.hx j)) (pr₂ i j)).hom) := by
  simp only [torsorDescentSheafIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Category.assoc, Iso.hom_inv_id_assoc, ← D.glueIso_eq_glue,
    Functor.DescentDatum.glueIso_hom, Functor.Restriction.fiberMor,
    Functor.map_comp]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_assoc]

end Descent

end FiberSheaves

private def descentComponentIso {C : Type u₁} [Category.{v₁} C]
    (J : GrothendieckTopology C) {U : C} (H : Sheaf (J.over U) (Type u₂))
    {I : Type w₁} {V : I → C} {f : ∀ i, V i ⟶ U}
    (D : (J.pseudofunctorOver (Type u₂)).DescentData f)
    (e : ((J.pseudofunctorOver (Type u₂)).toDescentData f).obj H ≅ D) (i : I) :
    (J.overMapPullback (Type u₂) (f i)).obj H ≅ D.obj i where
  hom := e.hom.hom i
  inv := e.inv.hom i
  hom_inv_id := congrArg (fun a => a.hom i) e.hom_inv_id
  inv_hom_id := congrArg (fun a => a.hom i) e.inv_hom_id

section SmallSheafDescent
open Opposite Pseudofunctor.LocallyDiscreteOpToCat
variable {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C)
  {U : C} {I : Type w₁} {V : I → C} (f : ∀ i, V i ⟶ U)

private def liftSheafDescentData
    (D : (J.pseudofunctorOver (Type u₂)).DescentData f) :
    (J.pseudofunctorOver (Type (max u₂ w))).DescentData f where
  obj i := (sheafCompose (J.over (V i)) uliftFunctor.{w, u₂}).obj (D.obj i)
  hom {W} q {i j} p₁ p₂ h₁ h₂ :=
    ⟨Functor.whiskerRight (D.hom q p₁ p₂ h₁ h₂).hom uliftFunctor⟩
  hom_self := by
    intro W q i p hp
    exact congrArg ((sheafCompose (J.over W) uliftFunctor.{w, u₂}).map) (D.hom_self q p hp)
  hom_comp := by
    intro W q i j k p₁ p₂ p₃ h₁ h₂ h₃
    exact congrArg ((sheafCompose (J.over W) uliftFunctor.{w, u₂}).map)
      (D.hom_comp q p₁ p₂ p₃ h₁ h₂ h₃)
  pullHom_hom := by
    intro W' W g q q' hq i j p₁ p₂ h₁ h₂ gp₁ gp₂ hg₁ hg₂
    subst gp₁ gp₂ q'
    have h := D.pullHom_hom g q (g ≫ q) rfl p₁ p₂ h₁ h₂ (g ≫ p₁) (g ≫ p₂) rfl rfl
    apply Sheaf.hom_ext
    ext Z x
    cases Z with
    | op Z =>
      obtain ⟨Z, z, rfl⟩ := Over.mk_surjective Z
      have hh := congrArg (fun a =>
        CategoryTheory.GrothendieckTopology.Stacks.SheafGluing.DescentDataEssSurj.appS
          (D.obj i) (D.obj j) a z x.down) h
      rw (transparency := .default)
        [CategoryTheory.GrothendieckTopology.Stacks.SheafGluing.DescentDataEssSurj.appS_pullHom
          (D.obj i) (D.obj j) (D.hom q p₁ p₂ h₁ h₂) g (g ≫ p₁) (g ≫ p₂) rfl rfl z] at hh
      let Mi := (sheafCompose (J.over (V i)) uliftFunctor.{w, u₂}).obj (D.obj i)
      let Mj := (sheafCompose (J.over (V j)) uliftFunctor.{w, u₂}).obj (D.obj j)
      let α : (J.overMapPullback (Type (max u₂ w)) p₁).obj Mi ⟶
          (J.overMapPullback (Type (max u₂ w)) p₂).obj Mj :=
        ⟨Functor.whiskerRight (D.hom q p₁ p₂ h₁ h₂).hom uliftFunctor.{w, u₂}⟩
      change (CategoryTheory.GrothendieckTopology.Stacks.SheafGluing.DescentDataEssSurj.appS Mi Mj
        (pullHom (F := J.pseudofunctorOver (Type (max u₂ w))) α
          g (g ≫ p₁) (g ≫ p₂) rfl rfl) z) x = _
      rw (transparency := .default)
        [CategoryTheory.GrothendieckTopology.Stacks.SheafGluing.DescentDataEssSurj.appS_pullHom
          Mi Mj α g (g ≫ p₁) (g ≫ p₂) rfl rfl z]
      exact congrArg ULift.up hh

end SmallSheafDescent

private theorem bigFppf_topology_eq (𝒞 : AlgebraicGeometry.BigFppfSite.{u}) :
    𝒞.topology = (Scheme.fppfPrecoverage.comap 𝒞.inclusion).toGrothendieck := by
  apply le_antisymm
  · apply Precoverage.toGrothendieck_mono
    rintro X R ⟨E, rfl, hE⟩
    exact hE.1
  · rw [Precoverage.toGrothendieck_le_iff_le_toPrecoverage]
    intro X R hR
    let E : Covering 𝒞.Schemes := ⟨X, R.preZeroHypercover⟩
    have hE : AlgebraicGeometry.IsFppfCovering E := by
      simpa [E, AlgebraicGeometry.IsFppfCovering] using hR
    obtain ⟨E', hE', h⟩ := 𝒞.fppf_has_representative E hE
    obtain ⟨e, he⟩ := h
    obtain ⟨Y, F⟩ := E'
    dsimp [E] at e
    subst Y
    have heq : R = F.presieve₀ := by
      simpa [E] using PreZeroHypercover.presieve₀_eq_of_combinatoriallyEquivalent he
    rw [GrothendieckTopology.mem_toPrecoverage_iff, heq]
    exact Precoverage.generate_mem_toGrothendieck ⟨F, rfl, hE'⟩

private theorem small_subcover
    {C : Type u₁} [Category.{v₁} C] (K : Precoverage C)
    [K.IsStableUnderComposition] [K.IsStableUnderBaseChange] [K.HasPullbacks] [K.HasIsos]
    [Precoverage.Small.{u₂} K]
    {U : C} {I : Type w₁} {V : I → C} (f : ∀ i, V i ⟶ U)
    (hf : Sieve.ofArrows V f ∈ K.toGrothendieck U) :
    ∃ (A : Type u₂) (a : A → I), Sieve.ofArrows (V ∘ a) (fun j => f (a j)) ∈
      K.toGrothendieck U := by
  classical
  obtain ⟨R, hR, hRf⟩ := Precoverage.mem_toGrothendieck_iff_of_isStableUnderComposition.mp hf
  let E : K.ZeroHypercover U := ⟨R.preZeroHypercover, by simpa using hR⟩
  let E' := E.restrictIndexOfSmall.{u₂}
  have he (j : E'.I₀) : Sieve.ofArrows V f (E'.f j) :=
    hRf _ _ (Precoverage.ZeroHypercover.Small.restrictFun E j).2
  have hh (j : E'.I₀) : ∃ (i : I) (g : E'.X j ⟶ V i), g ≫ f i = E'.f j := by
    rcases he j with ⟨Y, g, k, ⟨i⟩, hk⟩
    exact ⟨i, g, hk⟩
  choose a g hg using hh
  refine ⟨E'.I₀, a, K.toGrothendieck.superset_covering ?_
    (Precoverage.generate_mem_toGrothendieck E'.mem₀)⟩
  apply (Sieve.generate_le_iff _ _).mpr
  rintro Y k ⟨j⟩
  exact ⟨V (a j), g j, f (a j), Presieve.ofArrows.mk j, hg j⟩

private theorem bigFppfOver_small_subcover
    {U : AlgebraicGeometry.BigFppfOver 𝒞 S hS} {I : Type w}
    {V : I → AlgebraicGeometry.BigFppfOver 𝒞 S hS}
    (f : ∀ i, V i ⟶ U)
    (hf : Sieve.ofArrows V f ∈ AlgebraicGeometry.BigFppfOver.topology 𝒞 S hS U) :
    ∃ (A : Type u) (a : A → I), Sieve.ofArrows (V ∘ a) (fun j => f (a j)) ∈
      AlgebraicGeometry.BigFppfOver.topology 𝒞 S hS U := by
  let := bigFppf_closedUnderPullbacks 𝒞
  let : Scheme.fppfPrecoverage.HasIsos := ⟨fun f _ =>
    Scheme.Hom.singleton_mem_fppfPrecoverage f⟩
  let : Precoverage.Small.{u} Scheme.fppfPrecoverage := by
    unfold Scheme.fppfPrecoverage
    infer_instance
  let K := Scheme.fppfPrecoverage.comap 𝒞.inclusion
  have ht : AlgebraicGeometry.BigFppfOver.topology 𝒞 S hS =
      (K.comap (Over.forget (𝒞.obj hS))).toGrothendieck := by
    change 𝒞.topology.over (𝒞.obj hS) = _
    rw [bigFppf_topology_eq, over_toGrothendieck_eq_toGrothendieck_comap_forget]
  rw [ht] at hf ⊢
  exact small_subcover (K.comap (Over.forget (𝒞.obj hS))) f hf

section SmallGluing
open Opposite
variable {C : Type u₁} [Category.{v₁} C] [HasPullbacks C]
  (J : GrothendieckTopology C) {U : C} {I : Type w₁} {V : I → C}
  (f : ∀ i, V i ⟶ U)

private theorem small_sections_of_small_subcover
    {F : Sheaf (J.over U) (Type w)}
    (A : Type u₂) (a : A → I)
    (ha : Sieve.ofArrows (V ∘ a) (fun j => f (a j)) ∈ J U)
    (hloc : ∀ (j : A) (W : Over (V (a j))),
      Small.{u₂} (F.obj.obj (op ((Over.map (f (a j))).obj W))))
    (W : Over U) : Small.{u₂} (F.obj.obj (op W)) := by
  let X (j : A) : Over U := Over.mk (pullback.fst (f (a j)) W.hom ≫ f (a j))
  let g (j : A) : X j ⟶ W := Over.homMk (pullback.snd (f (a j)) W.hom)
    pullback.condition.symm
  have hg : Sieve.ofArrows X g ∈ J.over U W := by
    rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
    change Sieve.ofArrows (fun j => pullback (f (a j)) W.hom)
      (fun j => pullback.snd (f (a j)) W.hom) ∈ J W.left
    rw [Sieve.ofArrows_eq_pullback_of_isPullback (fun j => f (a j))
      (fun j => (IsPullback.of_hasPullback (f (a j)) W.hom).flip)]
    exact J.pullback_stable _ ha
  have (j : A) : Small.{u₂} (F.obj.obj (op (X j))) :=
    hloc j (Over.mk (pullback.fst (f (a j)) W.hom))
  apply small_of_injective (f := fun s : F.obj.obj (op W) => fun j => F.obj.map (g j).op s)
  intro s t h
  apply (F.property.isSheafFor _ hg).isSeparatedFor.ext
  rintro Z k ⟨Y, l, m, ⟨j⟩, rfl⟩
  simpa only [op_comp, CategoryTheory.Functor.map_comp, ConcreteCategory.comp_apply]
    using congrArg (F.obj.map l.op) (congrFun h j)

private def shrinkPresheafIso (P : Cᵒᵖ ⥤ Type (max u₂ w))
    [FunctorToTypes.Small.{u₂} P] :
    FunctorToTypes.shrink.{u₂} P ⋙ uliftFunctor.{w, u₂} ≅ P :=
  NatIso.ofComponents (fun W =>
    (Equiv.ulift.trans (equivShrink.{u₂} (P.obj W)).symm).toIso)
    (by intro X Y f; ext x; exact (equivShrink (P.obj Y)).symm_apply_apply _)

private def shrinkSheaf (F : Sheaf J (Type (max u₂ w)))
    [FunctorToTypes.Small.{u₂} F.obj] : Sheaf J (Type u₂) :=
  ⟨FunctorToTypes.shrink.{u₂} F.obj, Presheaf.isSheaf_of_isSheaf_comp J _ uliftFunctor.{w, u₂}
    ((Presheaf.isSheaf_of_iso_iff (shrinkPresheafIso F.obj)).2 F.property)⟩

omit [HasPullbacks C] in
private theorem lift_ofObj_hom
    (H : Sheaf (J.over U) (Type u₂)) {W : C} (q : W ⟶ U)
    {i j : I} (p₁ : W ⟶ V i) (p₂ : W ⟶ V j)
    (h₁ : p₁ ≫ f i = q) (h₂ : p₂ ≫ f j = q) :
    (sheafCompose (J.over W) uliftFunctor.{w, u₂}).map
      ((Pseudofunctor.DescentData.ofObj (F := J.pseudofunctorOver (Type u₂)) (f := f) H).hom
        q p₁ p₂ h₁ h₂) =
    (Pseudofunctor.DescentData.ofObj (F := J.pseudofunctorOver (Type (max u₂ w))) (f := f)
      ((sheafCompose (J.over U) uliftFunctor.{w, u₂}).obj H)).hom q p₁ p₂ h₁ h₂ := by
  apply Sheaf.hom_ext
  ext Z x
  cases Z with
  | op Z =>
    obtain ⟨Z, z, rfl⟩ := Over.mk_surjective Z
    simp only [Pseudofunctor.DescentData.ofObj_hom]
    have hi :=
      CategoryTheory.GrothendieckTopology.Stacks.SheafGluing.DescentDataEssSurj.mapComp'_inv_app
        (f i) p₁ q h₁ H z
    have hj :=
      CategoryTheory.GrothendieckTopology.Stacks.SheafGluing.DescentDataEssSurj.mapComp'_hom_app
        (f j) p₂ q h₂ H z
    have hi' :=
      CategoryTheory.GrothendieckTopology.Stacks.SheafGluing.DescentDataEssSurj.mapComp'_inv_app
        (f i) p₁ q h₁ ((sheafCompose (J.over U) uliftFunctor.{w, u₂}).obj H) z
    have hj' :=
      CategoryTheory.GrothendieckTopology.Stacks.SheafGluing.DescentDataEssSurj.mapComp'_hom_app
        (f j) p₂ q h₂ ((sheafCompose (J.over U) uliftFunctor.{w, u₂}).obj H) z
    dsimp only [CategoryTheory.GrothendieckTopology.Stacks.SheafGluing.DescentDataEssSurj.app]
      at hi hj hi' hj'
    let ai := ((J.pseudofunctorOver (Type u₂)).mapComp' (f i).op.toLoc p₁.op.toLoc q.op.toLoc
      (by grind)).inv.toNatTrans.app H
    let aj := ((J.pseudofunctorOver (Type u₂)).mapComp' (f j).op.toLoc p₂.op.toLoc q.op.toLoc
      (by grind)).hom.toNatTrans.app H
    let bi := ((J.pseudofunctorOver (Type (max u₂ w))).mapComp'
      (f i).op.toLoc p₁.op.toLoc q.op.toLoc (by grind)).inv.toNatTrans.app
      ((sheafCompose (J.over U) uliftFunctor.{w, u₂}).obj H)
    let bj := ((J.pseudofunctorOver (Type (max u₂ w))).mapComp'
      (f j).op.toLoc p₂.op.toLoc q.op.toLoc (by grind)).hom.toNatTrans.app
      ((sheafCompose (J.over U) uliftFunctor.{w, u₂}).obj H)
    change ULift.up (aj.hom.app (op (Over.mk z)) (ai.hom.app (op (Over.mk z)) x.down)) =
      bj.hom.app (op (Over.mk z)) (bi.hom.app (op (Over.mk z)) x)
    dsimp only [ai, aj, bi, bj]
    rw [hi, hj, hi', hj']
    rfl

private def lowerDescentIso
    (H : Sheaf (J.over U) (Type u₂))
    (D : (J.pseudofunctorOver (Type u₂)).DescentData f)
    (e : (Pseudofunctor.DescentData.ofObj (F := J.pseudofunctorOver (Type (max u₂ w))) (f := f)
        ((sheafCompose (J.over U) uliftFunctor.{w, u₂}).obj H)) ≅
      liftSheafDescentData J f D) :
    (Pseudofunctor.DescentData.ofObj (F := J.pseudofunctorOver (Type u₂)) (f := f) H) ≅ D := by
  let ei (i : I) : (J.overMapPullback (Type u₂) (f i)).obj H ≅ D.obj i :=
    (sheafCompose (J.over (V i)) uliftFunctor.{w, u₂}).preimageIso
      (descentComponentIso J _ _ e i)
  refine Pseudofunctor.DescentData.isoMk ei ?_
  intro W q i j p₁ p₂ h₁ h₂
  apply (sheafCompose (J.over W) uliftFunctor.{w, u₂}).map_injective
  rw [Functor.map_comp, Functor.map_comp, lift_ofObj_hom]
  change (J.overMapPullback (Type (max u₂ w)) p₁).map
      ((sheafCompose (J.over (V i)) uliftFunctor.{w, u₂}).map (ei i).hom) ≫ _ =
    _ ≫ (J.overMapPullback (Type (max u₂ w)) p₂).map
      ((sheafCompose (J.over (V j)) uliftFunctor.{w, u₂}).map (ei j).hom)
  have hi : (sheafCompose (J.over (V i)) uliftFunctor.{w, u₂}).map (ei i).hom = e.hom.hom i :=
    Functor.map_preimage _ _
  have hj : (sheafCompose (J.over (V j)) uliftFunctor.{w, u₂}).map (ei j).hom = e.hom.hom j :=
    Functor.map_preimage _ _
  rw [hi, hj]
  exact e.hom.comm q p₁ p₂ h₁ h₂

private theorem small_sheaf_descent
    (hf : Sieve.ofArrows V f ∈ J U)
    (A : Type u₂) (a : A → I)
    (ha : Sieve.ofArrows (V ∘ a) (fun j => f (a j)) ∈ J U)
    (D : (J.pseudofunctorOver (Type u₂)).DescentData f) :
    ∃ H : Sheaf (J.over U) (Type u₂),
      Nonempty (((J.pseudofunctorOver (Type u₂)).toDescentData f).obj H ≅ D) := by
  let L := J.pseudofunctorOver (Type (max u₁ v₁ u₂ w₁))
  let D' : L.DescentData f := liftSheafDescentData.{max u₁ v₁ w₁, u₁, v₁, u₂, w₁} J f D
  let := J.essSurj_toDescentData_pseudofunctorOver (Type (max u₁ v₁ u₂ w₁)) f hf
  let H := (L.toDescentData f).objPreimage D'
  let e := (L.toDescentData f).objObjPreimageIso D'
  have hloc (j : A) (W : Over (V (a j))) :
      Small.{u₂} (H.obj.obj (op ((Over.map (f (a j))).obj W))) := by
    let eij := (sheafToPresheaf (J.over (V (a j))) (Type (max u₁ v₁ u₂ w₁))).mapIso
      (descentComponentIso J H D' e (a j))
    have : Small.{u₂} ((D'.obj (a j)).obj.obj (op W)) := by
      change Small.{u₂} (ULift.{max u₁ v₁ w₁} ((D.obj (a j)).obj.obj (op W)))
      infer_instance
    let inj : H.obj.obj (op ((Over.map (f (a j))).obj W)) →
        (D'.obj (a j)).obj.obj (op W) := eij.hom.app (op W)
    exact small_of_injective (f := inj) (ConcreteCategory.bijective_of_isIso
      (eij.hom.app (op W))).1
  let : FunctorToTypes.Small.{u₂} H.obj := fun W =>
    small_sections_of_small_subcover J f A a ha hloc W.unop
  let Hs := shrinkSheaf.{max u₁ v₁ w₁, max u₁ v₁, v₁, u₂} (J.over U) H
  let es : (sheafCompose (J.over U) uliftFunctor.{max u₁ v₁ w₁, u₂}).obj Hs ≅ H :=
    { hom := ⟨(shrinkPresheafIso.{max u₁ v₁ w₁, max u₁ v₁, v₁, u₂} H.obj).hom⟩
      inv := ⟨(shrinkPresheafIso.{max u₁ v₁ w₁, max u₁ v₁, v₁, u₂} H.obj).inv⟩
      hom_inv_id :=
        Sheaf.hom_ext (shrinkPresheafIso.{max u₁ v₁ w₁, max u₁ v₁, v₁, u₂} H.obj).hom_inv_id
      inv_hom_id :=
        Sheaf.hom_ext (shrinkPresheafIso.{max u₁ v₁ w₁, max u₁ v₁, v₁, u₂} H.obj).inv_hom_id }
  exact ⟨Hs, ⟨lowerDescentIso J f Hs D ((L.toDescentData f).mapIso es ≪≫ e)⟩⟩

end SmallGluing

section FiberCharts
open Opposite
variable {C : Type u₁} [Category.{v₁} C] {U V : C}

private theorem isPullback_fiberCoproductToBase
    {A P : Cᵒᵖ ⥤ Type v₁} (ρ : yoneda.obj V ⟶ A) (p : P ⟶ A) :
    IsPullback (OverShriek.fiberCoproductToBase ρ p)
      (OverShriek.presheafToYoneda (OverShriek.fiber ρ p)) p ρ := by
  apply IsPullback.iff_app.mpr
  intro W
  apply (Types.isPullback_iff _ _ _ _).mpr
  refine ⟨NatTrans.congr_app (OverShriek.fiberCoproductToBase_comp ρ p) W, ?_, ?_⟩
  · intro x y h
    exact Sigma.subtype_ext h.2 h.1
  · intro x y h
    exact ⟨⟨y, x, h⟩, rfl, rfl⟩

private def fiberIsoMap (f : V ⟶ U)
    (P : Over (yoneda.obj U)) (Q : Over (yoneda.obj V))
    (e : OverShriek.fiber (𝟙 (yoneda.obj V)) Q.hom ≅
      OverShriek.fiber (yoneda.map f) P.hom) : Q.left ⟶ P.left :=
  ((OverShriek.presheafCounitIso (U := V)).app Q).inv.left ≫
    (OverShriek.presheafFunctor.mapIso e).hom ≫
    OverShriek.fiberCoproductToBase (yoneda.map f) P.hom

private theorem fiberIsoMap_isPullback (f : V ⟶ U)
    (P : Over (yoneda.obj U)) (Q : Over (yoneda.obj V))
    (e : OverShriek.fiber (𝟙 (yoneda.obj V)) Q.hom ≅
      OverShriek.fiber (yoneda.map f) P.hom) :
    IsPullback (fiberIsoMap f P Q e) Q.hom P.hom (yoneda.map f) := by
  let d : Q ≅ Over.mk (OverShriek.presheafToYoneda (OverShriek.fiber (yoneda.map f) P.hom)) :=
    ((OverShriek.presheafCounitIso (U := V)).app Q).symm ≪≫
      OverShriek.presheafFunctorToOver.mapIso e
  have : IsIso d.hom.left := ((Over.forget (yoneda.obj V)).mapIso d).isIso_hom
  have h : IsPullback d.hom.left Q.hom
      (OverShriek.presheafToYoneda (OverShriek.fiber (yoneda.map f) P.hom)) (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨(Over.w d.hom).trans (Category.comp_id _).symm⟩
  have hd : d.hom.left ≫ OverShriek.fiberCoproductToBase (yoneda.map f) P.hom =
      fiberIsoMap f P Q e := by
    simp only [fiberIsoMap]
    rfl
  have hp := h.paste_horiz (isPullback_fiberCoproductToBase (yoneda.map f) P.hom)
  rwa [hd, Category.id_comp] at hp

private theorem fiberIsoMap_fiber (f : V ⟶ U)
    (P : Over (yoneda.obj U)) (Q : Over (yoneda.obj V))
    (e : OverShriek.fiber (𝟙 (yoneda.obj V)) Q.hom ≅
      OverShriek.fiber (yoneda.map f) P.hom) :
    fiberMapOver f P Q (fiberIsoMap f P Q e) (fiberIsoMap_isPullback f P Q e).w = e.hom := by
  ext W x
  apply Subtype.ext
  change (e.hom.app (op (Over.mk (Q.hom.app (op W.unop.left) x.val))) ⟨x.val, rfl⟩).val =
    (e.hom.app W x).val
  let k : W.unop ⟶ Over.mk (Q.hom.app (op W.unop.left) x.val) :=
    Over.homMk (𝟙 W.unop.left) (by simpa using x.property)
  have hn := e.hom.naturality_apply k.op ⟨x.val, rfl⟩
  have hh := congrArg Subtype.val hn
  simp only [OverShriek.fiber, k, Over.homMk_left, Quiver.Hom.unop_op, op_id,
    Opposite.op_unop] at hh
  simp at hh
  exact hh.symm

private theorem isSheaf_of_fiber (J : GrothendieckTopology C)
    (P : Over (yoneda.obj U)) (hU : Presheaf.IsSheaf J (yoneda.obj U))
    (hP : Presheaf.IsSheaf (J.over U) (OverShriek.fiber (𝟙 (yoneda.obj U)) P.hom)) :
    Presheaf.IsSheaf J P.left := by
  rw [isSheaf_iff_isSheaf_of_type] at hU hP ⊢
  intro W R hR x hx
  obtain ⟨f, hf, hfu⟩ := hU R hR _ (hx.map P.hom)
  have key {A : Over U} (a : A ⟶ Over.mk f) (ha : R.arrows a.left) :
      P.hom.app (op A.left) (x a.left ha) = A.hom :=
    (hf a.left ha).symm.trans (Over.w a)
  let y : Presieve.FamilyOfElements
      (OverShriek.fiber (𝟙 (yoneda.obj U)) P.hom)
      ((Sieve.overEquiv (Over.mk f)).symm R).arrows :=
    fun A a ha => ⟨x a.left ha, key a ha⟩
  have hy : y.Compatible := by
    intro A A₁ A₂ a₁ a₂ b₁ b₂ hb₁ hb₂ hab
    exact Subtype.ext (hx a₁.left a₂.left hb₁ hb₂ (congrArg Over.Hom.left hab))
  obtain ⟨t, ht, htu⟩ := hP _ (J.overEquiv_symm_mem_over (Over.mk f) R hR) y hy
  refine ⟨t.val, ?_, ?_⟩
  · intro Z a ha
    exact congrArg Subtype.val (ht (Over.homMk a rfl : Over.mk (a ≫ f) ⟶ Over.mk f) ha)
  · intro z hz
    have hzf : P.hom.app (op W) z = f := hfu _ (hz.map P.hom)
    exact congrArg Subtype.val (htu ⟨z, hzf⟩ (fun A a ha => Subtype.ext (hz a.left ha)))

private theorem isSheaf_overShriek_presheaf (J : GrothendieckTopology C)
    (H : Sheaf (J.over U) (Type v₁))
    (hU : Presheaf.IsSheaf J (yoneda.obj U)) :
    Presheaf.IsSheaf J (OverShriek.presheaf H.obj) :=
  isSheaf_of_fiber J (OverShriek.presheafFunctorToOver.obj H.obj) hU
    ((Presheaf.isSheaf_of_iso_iff (OverShriek.presheafUnitIsoApp H.obj)).mp H.property)

private def sheafChartIso (f : V ⟶ U) (H : (Over U)ᵒᵖ ⥤ Type v₁)
    (Q : Over (yoneda.obj V))
    (e : OverShriek.fiber (𝟙 (yoneda.obj V)) Q.hom ≅ (Over.map f).op ⋙ H) :
    OverShriek.fiber (𝟙 (yoneda.obj V)) Q.hom ≅
      OverShriek.fiber (yoneda.map f) (OverShriek.presheafToYoneda H) :=
  e ≪≫ Functor.isoWhiskerLeft (Over.map f).op (OverShriek.presheafUnitIsoApp H)

private def sheafChart (f : V ⟶ U) (H : (Over U)ᵒᵖ ⥤ Type v₁)
    (Q : Over (yoneda.obj V))
    (e : OverShriek.fiber (𝟙 (yoneda.obj V)) Q.hom ≅ (Over.map f).op ⋙ H) :
    Q.left ⟶ OverShriek.presheaf H :=
  fiberIsoMap f (OverShriek.presheafFunctorToOver.obj H) Q (sheafChartIso f H Q e)

private theorem sheafChart_isPullback (f : V ⟶ U) (H : (Over U)ᵒᵖ ⥤ Type v₁)
    (Q : Over (yoneda.obj V))
    (e : OverShriek.fiber (𝟙 (yoneda.obj V)) Q.hom ≅ (Over.map f).op ⋙ H) :
    IsPullback (sheafChart f H Q e) Q.hom (OverShriek.presheafToYoneda H) (yoneda.map f) :=
  fiberIsoMap_isPullback f (OverShriek.presheafFunctorToOver.obj H) Q (sheafChartIso f H Q e)

private theorem sheafChart_apply (f : V ⟶ U) (H : (Over U)ᵒᵖ ⥤ Type v₁)
    (Q : Over (yoneda.obj V))
    (e : OverShriek.fiber (𝟙 (yoneda.obj V)) Q.hom ≅ (Over.map f).op ⋙ H)
    (W : Over V) (x : (OverShriek.fiber (𝟙 (yoneda.obj V)) Q.hom).obj (op W)) :
    (sheafChart f H Q e).app (op W.left) x.val =
      ⟨W.hom ≫ f, e.hom.app (op W) x⟩ :=
  congrArg (fun k => (k.app (op W) x).val)
    (fiberIsoMap_fiber f (OverShriek.presheafFunctorToOver.obj H) Q (sheafChartIso f H Q e))

private theorem sigma_ofObj_hom
    (J : GrothendieckTopology C) (H : Sheaf (J.over U) (Type v₁))
    {I : Type w₁} {V : I → C} (f : ∀ i, V i ⟶ U)
    {W Z : C} (q : W ⟶ U) {i j : I} (p₁ : W ⟶ V i) (p₂ : W ⟶ V j)
    (h₁ : p₁ ≫ f i = q) (h₂ : p₂ ≫ f j = q) (z : Z ⟶ W)
    (x : H.obj.obj (op (Over.mk ((z ≫ p₁) ≫ f i)))) :
    (⟨(z ≫ p₂) ≫ f j,
      ((Pseudofunctor.DescentData.ofObj (F := J.pseudofunctorOver (Type v₁))
        (f := f) H).hom q p₁ p₂ h₁ h₂).hom.app (op (Over.mk z)) x⟩ :
      (OverShriek.presheaf H.obj).obj (op Z)) = ⟨(z ≫ p₁) ≫ f i, x⟩ := by
  let ai := ((J.pseudofunctorOver (Type v₁)).mapComp' (f i).op.toLoc p₁.op.toLoc q.op.toLoc
    (by grind)).inv.toNatTrans.app H
  let aj := ((J.pseudofunctorOver (Type v₁)).mapComp' (f j).op.toLoc p₂.op.toLoc q.op.toLoc
    (by grind)).hom.toNatTrans.app H
  change (⟨(z ≫ p₂) ≫ f j, aj.hom.app (op (Over.mk z)) (ai.hom.app (op (Over.mk z)) x)⟩ :
    (OverShriek.presheaf H.obj).obj (op Z)) = _
  dsimp only [ai, aj]
  rw [show (((J.pseudofunctorOver (Type v₁)).mapComp' (f i).op.toLoc p₁.op.toLoc
      q.op.toLoc (by grind)).inv.toNatTrans.app H).hom.app (op (Over.mk z)) = _ from
      CategoryTheory.GrothendieckTopology.Stacks.SheafGluing.DescentDataEssSurj.mapComp'_inv_app
        (f i) p₁ q h₁ H z,
    show (((J.pseudofunctorOver (Type v₁)).mapComp' (f j).op.toLoc p₂.op.toLoc
      q.op.toLoc (by grind)).hom.toNatTrans.app H).hom.app (op (Over.mk z)) = _ from
      CategoryTheory.GrothendieckTopology.Stacks.SheafGluing.DescentDataEssSurj.mapComp'_hom_app
        (f j) p₂ q h₂ H z]
  dsimp only [CategoryTheory.GrothendieckTopology.Stacks.SheafGluing.DescentDataEssSurj.rest]
  exact (OverShriek.sigmaMk_eq_self H.obj _ _ rfl).trans
    (OverShriek.sigmaMk_eq_self H.obj x _ rfl)

private theorem sigma_descent_inv
    (J : GrothendieckTopology C) (H : Sheaf (J.over U) (Type v₁))
    {I : Type w₁} {V : I → C} {f : ∀ i, V i ⟶ U}
    (D : (J.pseudofunctorOver (Type v₁)).DescentData f)
    (e : ((J.pseudofunctorOver (Type v₁)).toDescentData f).obj H ≅ D)
    {W Z : C} (q : W ⟶ U) {i j : I} (p₁ : W ⟶ V i) (p₂ : W ⟶ V j)
    (h₁ : p₁ ≫ f i = q) (h₂ : p₂ ≫ f j = q) (z : Z ⟶ W)
    (x : (D.obj i).obj.obj (op (Over.mk (z ≫ p₁)))) :
    (⟨(z ≫ p₂) ≫ f j, (e.inv.hom j).hom.app (op (Over.mk (z ≫ p₂)))
      ((D.hom q p₁ p₂ h₁ h₂).hom.app (op (Over.mk z)) x)⟩ :
      (OverShriek.presheaf H.obj).obj (op Z)) =
    ⟨(z ≫ p₁) ≫ f i, (e.inv.hom i).hom.app (op (Over.mk (z ≫ p₁))) x⟩ := by
  have h := congrArg (fun a => a.hom.app (op (Over.mk z)) x) (e.inv.comm q p₁ p₂ h₁ h₂)
  change ((Pseudofunctor.DescentData.ofObj (F := J.pseudofunctorOver (Type v₁))
      (f := f) H).hom q p₁ p₂ h₁ h₂).hom.app (op (Over.mk z))
      ((e.inv.hom i).hom.app (op (Over.mk (z ≫ p₁))) x) =
    (e.inv.hom j).hom.app (op (Over.mk (z ≫ p₂)))
      ((D.hom q p₁ p₂ h₁ h₂).hom.app (op (Over.mk z)) x) at h
  rw [← h]
  exact sigma_ofObj_hom J H f q p₁ p₂ h₁ h₂ z _

end FiberCharts

/-- **Stacks 04UM.** Condition (3) of Stacks 02ZI for the functor
`p : 𝒢/ℬ-Torsors ⥤ (Sch/S)_fppf` of Stacks 04UL: every descent datum of `𝒢/ℬ-Torsors`
relative to a covering family of the big fppf site of `S` is effective. -/
@[stacks 04UM "condition (3): descent data are effective"]
theorem projection_effectiveDescent
    (hB : Presheaf.IsSheaf (BigFppfOver.topology 𝒞 S hS) B)
    (hG : Presheaf.IsSheaf (BigFppfOver.topology 𝒞 S hS) G.X.left) :
    ∀ {U : BigFppfOver 𝒞 S hS} {I : Type w} (V : I → BigFppfOver 𝒞 S hS)
      (f : ∀ i, V i ⟶ U), Sieve.ofArrows V f ∈ BigFppfOver.topology 𝒞 S hS U →
      ∀ (Vij : I → I → BigFppfOver 𝒞 S hS)
        (pr₁ : ∀ i j, Vij i j ⟶ V i) (pr₂ : ∀ i j, Vij i j ⟶ V j)
        (hVij : ∀ i j, IsPullback (pr₁ i j) (pr₂ i j) (f i) (f j))
        (Vijk : I → I → I → BigFppfOver 𝒞 S hS)
        (s₁₂ : ∀ i j k, Vijk i j k ⟶ Vij i j) (s₂₃ : ∀ i j k, Vijk i j k ⟶ Vij j k)
        (hVijk : ∀ i j k, IsPullback (s₁₂ i j k) (s₂₃ i j k) (pr₂ i j) (pr₁ j k))
        (q₁ : ∀ i j k, Vijk i j k ⟶ V i) (q₂ : ∀ i j k, Vijk i j k ⟶ V j)
        (q₃ : ∀ i j k, Vijk i j k ⟶ V k)
        (hq₁ : ∀ i j k, q₁ i j k = s₁₂ i j k ≫ pr₁ i j)
        (hq₂ : ∀ i j k, q₂ i j k = s₁₂ i j k ≫ pr₂ i j)
        (hq₃ : ∀ i j k, q₃ i j k = s₂₃ i j k ≫ pr₂ j k)
        (D : Functor.DescentDatum (projection G) V f Vij pr₁ pr₂ hVij Vijk s₁₂ s₂₃ hVijk
          q₁ q₂ q₃ hq₁ hq₂ hq₃),
        D.IsEffective := by
  -- Glue the local sheaves and their actions, using the cocycle data, to build a global
  -- torsor and an effective descent isomorphism.
  intro U I V f hf Vij pr₁ pr₂ hVij Vijk s₁₂ s₂₃ hVijk q₁ q₂ q₃ hq₁ hq₂ hq₃ D
  let s : ∀ i, B.obj (Opposite.op (V i)) := fun i =>
    (D.x i).sec.app (Opposite.op (V i)) (eqToHom (D.hx i).symm)
  have hbi (i j : I) : (D.xrij i j).hom.base =
      eqToHom (D.xrij i j).hpt ≫ pr₁ i j ≫ eqToHom (D.hx i).symm :=
    hom_base_eq G (D.xrij i j).hom _ inferInstance
  have hbj (i j : I) : (D.xrji i j).hom.base =
      eqToHom (D.xrji i j).hpt ≫ pr₂ i j ≫ eqToHom (D.hx j).symm :=
    hom_base_eq G (D.xrji i j).hom _ inferInstance
  have hbij (i j : I) : (D.φ i j).base =
      eqToHom (D.xrij i j).hpt ≫ eqToHom (D.xrji i j).hpt.symm :=
    hom_base_eq G (D.φ i j) _ (D.φ_fibreHom i j)
  have hfib (i j : I) :
      (D.φ i j ≫ (D.xrji i j).hom).base =
        eqToHom (D.xrij i j).hpt ≫ pr₂ i j ≫ eqToHom (D.hx j).symm := by
    change (D.φ i j).base ≫ (D.xrji i j).hom.base = _
    rw [hbij, hbj]
    simp
  have hs : ∀ i j,
      B.map (Opposite.op (pr₁ i j)) (s i) =
        B.map (Opposite.op (pr₂ i j)) (s j) := by
    intro i j
    calc
      B.map (Opposite.op (pr₁ i j)) (s i) =
          (D.x i).sec.app (Opposite.op (Vij i j))
            (pr₁ i j ≫ eqToHom (D.hx i).symm) :=
        section_restrict (pr₁ i j) (D.x i).sec (D.hx i)
      _ = (D.xrij i j).pt.sec.app (Opposite.op (Vij i j))
            (eqToHom (D.xrij i j).hpt.symm) := by
        symm
        exact Hom.comp_sec_app (D.xrij i j).hom (D.xrij i j).hpt
          (D.hx i) (pr₁ i j) (hbi i j)
      _ = (D.xrji i j).pt.sec.app (Opposite.op (Vij i j))
            (eqToHom (D.xrji i j).hpt.symm) := by
        have harg : eqToHom (D.xrij i j).hpt.symm ≫ (D.φ i j).base =
            eqToHom (D.xrji i j).hpt.symm := by
          simp [hbij i j]
        have h := congrArg (fun α : yoneda.obj (D.xrij i j).pt.base ⟶ B =>
          α.app (Opposite.op (Vij i j)) (eqToHom (D.xrij i j).hpt.symm))
          (D.φ i j).comp_sec
        have h' := congrArg ((D.xrji i j).pt.sec.app (Opposite.op (Vij i j))) harg
        have hcomp : (D.xrji i j).pt.sec.app (Opposite.op (Vij i j))
              ((yoneda.map (D.φ i j).base).app (Opposite.op (Vij i j))
                (eqToHom (D.xrij i j).hpt.symm)) =
            (D.xrij i j).pt.sec.app (Opposite.op (Vij i j))
              (eqToHom (D.xrij i j).hpt.symm) := by
          simpa only [NatTrans.comp_app, ConcreteCategory.comp_apply] using h
        have h'' : (D.xrji i j).pt.sec.app (Opposite.op (Vij i j))
              ((yoneda.map (D.φ i j).base).app (Opposite.op (Vij i j))
                (eqToHom (D.xrij i j).hpt.symm)) =
            (D.xrji i j).pt.sec.app (Opposite.op (Vij i j))
              (eqToHom (D.xrji i j).hpt.symm) := by
          rwa [yoneda_map_app]
        exact hcomp.symm.trans h''
      _ = (D.x j).sec.app (Opposite.op (Vij i j))
            (pr₂ i j ≫ eqToHom (D.hx j).symm) :=
        Hom.comp_sec_app (D.xrji i j).hom (D.xrji i j).hpt (D.hx j) (pr₂ i j) (hbj i j)
      _ = B.map (Opposite.op (pr₂ i j)) (s j) :=
        (section_restrict (pr₂ i j) (D.x j).sec (D.hx j)).symm
  obtain ⟨b, hb, -⟩ := existsUnique_section_glue_ofArrows
    (AlgebraicGeometry.BigFppfOver.topology 𝒞 S hS) hB f hf Vij pr₁ pr₂ hVij s hs
  suffices H : ∃ (T : SheafTorsors G) (hT : (projection G).obj T = U)
      (π : ∀ i, D.x i ⟶ T),
      (∀ i, (π i).base = eqToHom (D.hx i) ≫ f i ≫ eqToHom hT.symm) ∧
      (∀ i j, D.φ i j ≫ (D.xrji i j).hom ≫ π j = (D.xrij i j).hom ≫ π i) by
    obtain ⟨T, hT, π, hπ, hc⟩ := H
    let xr (i : I) := restrictionOfHom G hT (D.hx i) (f i) (π i) (hπ i)
    refine ⟨T, hT, xr, fun i => 𝟙 (D.x i), ?_, fun i => inferInstance, ?_⟩
    · intro i
      change (projection G).IsHomLift (eqToHom (D.hx i) ≫ eqToHom (D.hx i).symm)
        (𝟙 (D.x i))
      simp
    · intro i j
      have hr : ((D.xrij i j).hom ≫ π i).base =
          eqToHom (D.xrij i j).hpt ≫ (pr₁ i j ≫ f i) ≫ eqToHom hT.symm := by
        change (D.xrij i j).hom.base ≫ (π i).base = _
        rw [hbi, hπ]
        simp
      let r := restrictionOfHom G hT (D.xrij i j).hpt (pr₁ i j ≫ f i)
        ((D.xrij i j).hom ≫ π i) hr
      have hir : Functor.FibreHom (projection G) r.pt (D.xrij i j).pt
          r.hpt (D.xrij i j).hpt (𝟙 (D.xrij i j).pt) := by
        change (projection G).IsHomLift
          (eqToHom (D.xrij i j).hpt ≫ eqToHom (D.xrij i j).hpt.symm)
            (𝟙 (D.xrij i j).pt)
        simpa only [eqToHom_trans, eqToHom_refl] using
          (CategoryTheory.IsHomLift.id (p := projection G)
            (a := (D.xrij i j).pt) rfl)
      refine ⟨r, 𝟙 _, D.φ i j, hir, D.φ_fibreHom i j,
        inferInstance, D.φ_iso i j, ?_, ?_, Category.id_comp _⟩
      · change (𝟙 _) ≫ Functor.Restriction.compTo (projection G) (pr₁ i j) (𝟙 (V i))
            (by simp) (Functor.Restriction.id (projection G) (D.x i) (D.hx i)) (D.xrij i j) =
          Functor.Restriction.compTo (projection G) (pr₁ i j) (f i) rfl (xr i) r ≫ (𝟙 _)
        simp only [Category.id_comp, Category.comp_id]
        have hid := Functor.Restriction.compTo_hom (projection G) (pr₁ i j) (𝟙 (V i))
          (by simp) (Functor.Restriction.id (projection G) (D.x i) (D.hx i)) (D.xrij i j)
        have hmain := restriction_compTo_eq G T hT (f i) (pr₁ i j) rfl (xr i) r (D.xrij i j).hom
          (hbi i j) rfl
        change _ ≫ 𝟙 (D.x i) = (D.xrij i j).hom at hid
        rw [Category.comp_id] at hid
        exact hid.trans hmain.symm
      · change D.φ i j ≫ Functor.Restriction.compTo (projection G) (pr₂ i j) (𝟙 (V j))
            (by simp) (Functor.Restriction.id (projection G) (D.x j) (D.hx j)) (D.xrji i j) =
          Functor.Restriction.compTo (projection G) (pr₂ i j) (f j) (hVij i j).w (xr j) r ≫ (𝟙 _)
        simp only [Category.comp_id]
        have hid := Functor.Restriction.compTo_hom (projection G) (pr₂ i j) (𝟙 (V j))
          (by simp) (Functor.Restriction.id (projection G) (D.x j) (D.hx j)) (D.xrji i j)
        have hmain := restriction_compTo_eq G T hT (f j) (pr₂ i j) (hVij i j).w (xr j) r
          (D.φ i j ≫ (D.xrji i j).hom) (hfib i j) (by simpa [Category.assoc] using hc i j)
        change _ ≫ 𝟙 (D.x j) = (D.xrji i j).hom at hid
        rw [Category.comp_id] at hid
        exact (congrArg (D.φ i j ≫ ·) hid).trans hmain.symm
  let J := AlgebraicGeometry.BigFppfOver.topology 𝒞 S hS
  let := (projection_isFiberedInGroupoids G).isFibered
  let Ds := torsorSheafDescentData G D
  obtain ⟨A, a, ha⟩ := bigFppfOver_small_subcover f hf
  obtain ⟨H, ⟨e⟩⟩ := small_sheaf_descent J f hf A a ha Ds
  let P := OverShriek.presheafFunctorToOver.obj H.obj
  have hP : Presheaf.IsSheaf J P.left :=
    isSheaf_overShriek_presheaf J H ((isAlgebraicSpace_yoneda 𝒞 S hS U).isSheaf)
  let ei (i : I) := (sheafToPresheaf (J.over (V i)) (Type u)).mapIso
    (descentComponentIso J H Ds e i).symm
  let π (i : I) : (D.x i).total.left ⟶ P.left :=
    sheafChart (f i) H.obj (Over.mk (normalizedProjection G (D.x i) (D.hx i))) (ei i)
  have hπ (i : I) : IsPullback (π i) (normalizedProjection G (D.x i) (D.hx i))
      P.hom (yoneda.map (f i)) :=
    sheafChart_isPullback (f i) H.obj
      (Over.mk (normalizedProjection G (D.x i) (D.hx i))) (ei i)
  have hπc (i j : I) : (D.φ i j).map ≫ (D.xrji i j).hom.map ≫ π j =
      (D.xrij i j).hom.map ≫ π i := by
    ext W x
    let z := (normalizedProjection G (D.xrij i j).pt (D.xrij i j).hpt).app W x
    let t : (torsorFiberPresheaf G (D.xrij i j).pt (D.xrij i j).hpt).obj
        (Opposite.op (Over.mk z)) := ⟨x, rfl⟩
    let R := torsorFiberSheaf G (Vij i j)
    let φ := R.map (Functor.fibreHomMk (D.φ_fibreHom i j))
    let ai := fiberIsoOfPullback (pr₁ i j)
      (Over.mk (normalizedProjection G (D.x i) (D.hx i)))
      (Over.mk (normalizedProjection G (D.xrij i j).pt (D.xrij i j).hpt))
      (D.xrij i j).hom.map (restriction_isPullback G (D.x i) (D.hx i) _ (D.xrij i j))
    let aj := fiberIsoOfPullback (pr₂ i j)
      (Over.mk (normalizedProjection G (D.x j) (D.hx j)))
      (Over.mk (normalizedProjection G (D.xrji i j).pt (D.xrji i j).hpt))
      (D.xrji i j).hom.map (restriction_isPullback G (D.x j) (D.hx j) _ (D.xrji i j))
    let xi := ai.hom.app (Opposite.op (Over.mk z)) t
    let xj := aj.hom.app (Opposite.op (Over.mk z)) (φ.hom.app (Opposite.op (Over.mk z)) t)
    have htrans := torsorDescentSheafIso_overlap G D i j
    rw [torsorFiberSheafPullbackIso_restriction,
      torsorFiberSheafPullbackIso_restriction] at htrans
    have hxij : ((Ds.hom (pr₁ i j ≫ f i) (pr₁ i j) (pr₂ i j) rfl (hVij i j).w.symm).hom.app
        (Opposite.op (Over.mk z))) xi = xj :=
      congrArg (fun k => k.hom.app (Opposite.op (Over.mk z)) t) htrans
    have hd := sigma_descent_inv J H Ds e (pr₁ i j ≫ f i)
      (pr₁ i j) (pr₂ i j) rfl (hVij i j).w.symm z xi
    rw [hxij] at hd
    have ci := sheafChart_apply (f i) H.obj
      (Over.mk (normalizedProjection G (D.x i) (D.hx i))) (ei i)
      (Over.mk (z ≫ pr₁ i j)) xi
    have cj := sheafChart_apply (f j) H.obj
      (Over.mk (normalizedProjection G (D.x j) (D.hx j))) (ei j)
      (Over.mk (z ≫ pr₂ i j)) xj
    exact cj.trans (hd.trans ci.symm)
  let b' : yoneda.obj U ⟶ B := yonedaEquiv.symm b
  have hb' (i : I) : yoneda.map (f i) ≫ b' = normalizedSection G (D.x i) (D.hx i) := by
    apply yonedaEquiv.injective
    change B.map (𝟙 (V i) ≫ f i).op b =
      (D.x i).sec.app (Opposite.op (V i)) (𝟙 (V i) ≫ eqToHom (D.hx i).symm)
    simpa only [Category.id_comp] using hb i
  let f' (i : I) : (D.x i).base ⟶ U := eqToHom (D.hx i) ≫ f i
  have hb'' (i : I) : yoneda.map (f' i) ≫ b' = (D.x i).sec := by
    simp only [f', Functor.map_comp, Category.assoc, hb', normalizedSection]
    simp
  have hπ' (i : I) : IsPullback (π i) (D.x i).total.hom P.hom (yoneda.map (f' i)) :=
    isPullback_of_normalizedProjection G (D.x i) (D.hx i) (f i) P (π i) (hπ i)
  have hρ : ∀ W x, familyImageSieve (fun i => yoneda.map (f' i)) x ∈ J W := by
    intro W x
    have he : familyImageSieve (fun i => yoneda.map (f' i)) x =
        familyImageSieve (fun i => yoneda.map (f i)) x := by
      ext Z g
      constructor
      · rintro ⟨i, k, hk⟩
        exact ⟨i, k ≫ eqToHom (D.hx i), by simpa [f', Category.assoc] using hk⟩
      · rintro ⟨i, k, hk⟩
        exact ⟨i, k ≫ eqToHom (D.hx i).symm, by simpa [f', Category.assoc] using hk⟩
    rw [he]
    exact familyImageSieve_mem_of_isPullback J (𝟙 (yoneda.obj U)) f hf
      (fun i => yoneda.map (f i)) (fun i => 𝟙 _)
      (fun i => IsPullback.id_vert _) W x
  have hPloc : Presheaf.IsLocallySurjective J P.hom :=
    isLocallySurjective_of_covering_family J P.hom (fun i => yoneda.map (f' i)) hρ
      π (fun i => (D.x i).total.hom) (fun i => (hπ' i).w)
      (fun i => (D.x i).isLocallySurjective)
  let R := (sheafPullbackGroup G U b').X
  let eg (i : I) : (D.x i).group ≅ (Over.pullback (yoneda.map (f' i))).obj R :=
    (Grp.forget _).mapIso (groupChartIso G (f' i) b' (D.x i).sec (hb'' i))
  let em (i : I) : (D.x i).total ≅ (Over.pullback (yoneda.map (f' i))).obj P :=
    Over.isoMk (hπ' i).isoPullback (hπ' i).isoPullback_hom_snd
  let (i : I) : MonObj ((Over.pullback (yoneda.map (f' i))).obj R) :=
    (Over.pullback (yoneda.map (f' i))).monObjObj R
  have (i : I) : IsMonHom (eg i).hom :=
    (groupChartIso G (f' i) b' (D.x i).sec (hb'' i)).hom.hom.isMonHom_hom
  let acts (i : I) : ModObj ((Over.pullback (yoneda.map (f' i))).obj R)
      ((Over.pullback (yoneda.map (f' i))).obj P) := ModObj.ofIso (eg i) (em i)
  have hacts (i : I) : let := acts i;
      IsIso (ModObj.leftSMul ((Over.pullback (yoneda.map (f' i))).obj R)
        ((Over.pullback (yoneda.map (f' i))).obj P)) := by
    have := (D.x i).isPseudoTorsor
    exact isIso_leftSMul_ofIsos (eg i) (em i)
  let cg (i : I) := (eg i).hom.left ≫ pullback.fst R.hom (yoneda.map (f' i))
  have hcg (i : I) : IsPullback (cg i) (D.x i).group.hom R.hom (yoneda.map (f' i)) :=
    pullbackChart_isPullback (yoneda.map (f' i)) R (D.x i).group (eg i)
  have hem (i : I) : (em i).hom.left ≫ pullback.fst P.hom (yoneda.map (f' i)) = π i :=
    (hπ' i).isoPullback_hom_fst
  let ap (i : I) := pullback.map (D.x i).group.hom (D.x i).total.hom R.hom P.hom
    (cg i) (π i) (yoneda.map (f' i)) (hcg i).w.symm (hπ' i).w.symm
  have hap (i : I) : ((eg i).hom ⊗ₘ (em i).hom).left ≫
      pullbackTensorMap (yoneda.map (f' i)) R P = ap i := by
    have h := tensorChartMap_eq (yoneda.map (f' i)) R P (D.x i).group (D.x i).total
      (eg i) (em i) (hcg i).w.symm
      (by rw [hem]; exact (hπ' i).w.symm)
    simpa only [hem] using h
  have hapb (i : I) : IsPullback (ap i) (pullback.snd (D.x i).group.hom (D.x i).total.hom)
      (pullback.snd R.hom P.hom) (π i) :=
    pullback_map_isPullback_snd (cg i) (π i) (yoneda.map (f' i)) (hcg i) (hπ' i).w
  have hπij (i j : I) : IsPullback (D.xrij i j).hom.map
      (D.φ i j ≫ (D.xrji i j).hom).map (π i) (π j) := by
    apply isPullback_of_cartesian_cospan
      (restriction_isPullback G (D.x i) (D.hx i) (pr₁ i j) (D.xrij i j))
      (hom_normalized_isPullback G (D.xrij i j).hpt (D.hx j)
        (D.φ i j ≫ (D.xrji i j).hom) (pr₂ i j) (hfib i j)).w
      (hπ i).w (hπ j) ((hVij i j).map yoneda) (hπc i j).symm
  have hbase (i j : I) : (D.xrij i j).hom.base ≫ f' i =
      (D.φ i j ≫ (D.xrji i j).hom).base ≫ f' j := by
    rw [hbi, hfib]
    simp only [f', Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    rw [(hVij i j).w]
  have hcgfst (i : I) : cg i ≫ pullback.fst G.X.hom b' =
      pullback.fst G.X.hom (D.x i).sec :=
    groupChartIso_fst_fst G (f' i) b' (D.x i).sec (hb'' i)
  have hcgcomp (i j : I) :
      groupBaseChange (D.xrij i j).hom.base (D.xrij i j).hom.comp_sec ≫ cg i =
        groupBaseChange (D.φ i j ≫ (D.xrji i j).hom).base
          (D.φ i j ≫ (D.xrji i j).hom).comp_sec ≫ cg j := by
    apply pullback.hom_ext
    · simp only [Category.assoc, hcgfst, groupBaseChange_fst]
    · change _ ≫ R.hom = _ ≫ R.hom
      have hi := (hcg i).w
      have hj := (hcg j).w
      simp only [SheafTorsors.group, sheafPullbackGroup_X_hom] at hi hj
      simp only [Category.assoc, hi, hj, groupBaseChange_snd_assoc,
        ← Functor.map_comp]
      exact congrArg (fun k => pullback.snd G.X.hom (D.xrij i j).pt.sec ≫ yoneda.map k)
        (hbase i j)
  have hacomp (i j : I) : homActionBaseChange G (D.xrij i j).hom ≫ ap i =
      homActionBaseChange G (D.φ i j ≫ (D.xrji i j).hom) ≫ ap j := by
    apply pullback.hom_ext
    · simp only [ap, SheafTorsors.group, sheafPullbackGroup_X_hom, Category.assoc,
        pullback.lift_fst, homActionBaseChange, actionBaseChange, pullback.lift_fst_assoc]
      rw [hcgcomp]
    · simp only [ap, SheafTorsors.group, sheafPullbackGroup_X_hom, Category.assoc,
        pullback.lift_snd, homActionBaseChange, actionBaseChange, pullback.lift_snd_assoc]
      exact congrArg (pullback.snd (D.xrij i j).pt.group.hom (D.xrij i j).pt.total.hom ≫ ·)
        (hπc i j).symm
  have hapij (i j : I) : IsPullback (homActionBaseChange G (D.xrij i j).hom)
      (homActionBaseChange G (D.φ i j ≫ (D.xrji i j).hom)) (ap i) (ap j) :=
    isPullback_of_cartesian_cospan
      (pullback_map_isPullback_snd
        (groupBaseChange (D.xrij i j).hom.base (D.xrij i j).hom.comp_sec)
        (D.xrij i j).hom.map (yoneda.map (D.xrij i j).hom.base)
        (groupBaseChange_isPullback G (D.xrij i j).hom) (D.xrij i j).hom.isPullback.w)
      (actionBaseChange_snd _ _ _ _) (hapb i).w (hapb j) (hπij i j) (hacomp i j)
  have hac : ∀ (W : AlgebraicGeometry.BigFppfOver 𝒞 S hS) (i j : I)
      (x : ((D.x i).group ⊗ (D.x i).total).left.obj (Opposite.op W))
      (y : ((D.x j).group ⊗ (D.x j).total).left.obj (Opposite.op W)),
      (ap i).app _ x = (ap j).app _ y →
      (actionMap (D.x i) ≫ π i).app _ x =
        (actionMap (D.x j) ≫ π j).app _ y := by
    intro W i j x y hxy
    obtain ⟨z, rfl, rfl⟩ := Types.exists_of_isPullback
      ((hapij i j).map ((evaluation _ _).obj (Opposite.op W))) x y hxy
    have hc : homActionBaseChange G (D.xrij i j).hom ≫ actionMap (D.x i) ≫ π i =
        homActionBaseChange G (D.φ i j ≫ (D.xrji i j).hom) ≫
          actionMap (D.x j) ≫ π j := by
      rw [← Category.assoc, ← (D.xrij i j).hom.smul_comp, Category.assoc,
        ← Category.assoc (homActionBaseChange G (D.φ i j ≫ (D.xrji i j).hom)),
        ← (D.φ i j ≫ (D.xrji i j).hom).smul_comp, Category.assoc]
      exact congrArg (actionMap (D.xrij i j).pt ≫ ·) (hπc i j).symm
    exact congrArg (fun k => k.app (Opposite.op W) z) hc
  let et (i : I) := (Over.forget (yoneda.obj (D.x i).base)).mapIso
    (MonoidalCategory.tensorIso (eg i) (em i))
  have het (i : I) : (et i).inv ≫ ap i = pullbackTensorMap (yoneda.map (f' i)) R P := by
    rw [← hap]
    change (et i).inv ≫ (et i).hom ≫ _ = _
    simp
  have hetact (i : I) : (acts i).smul.left ≫ pullback.fst P.hom (yoneda.map (f' i)) =
      (et i).inv ≫ actionMap (D.x i) ≫ π i := by
    change (((eg i).inv ⊗ₘ (em i).inv).left ≫ actionMap (D.x i) ≫
      (em i).hom.left) ≫ _ = _
    simp only [Category.assoc, hem]
    rfl
  have hcacts : ∀ (W : AlgebraicGeometry.BigFppfOver 𝒞 S hS) (i j : I)
      (x : ((Over.pullback (yoneda.map (f' i))).obj R ⊗
        (Over.pullback (yoneda.map (f' i))).obj P).left.obj (Opposite.op W))
      (y : ((Over.pullback (yoneda.map (f' j))).obj R ⊗
        (Over.pullback (yoneda.map (f' j))).obj P).left.obj (Opposite.op W)),
      (pullbackTensorMap (yoneda.map (f' i)) R P).app _ x =
        (pullbackTensorMap (yoneda.map (f' j)) R P).app _ y →
      ((acts i).smul.left ≫ pullback.fst P.hom (yoneda.map (f' i))).app _ x =
        ((acts j).smul.left ≫ pullback.fst P.hom (yoneda.map (f' j))).app _ y := by
    intro W i j x y hxy
    rw [hetact, hetact]
    apply hac W i j ((et i).inv.app _ x) ((et j).inv.app _ y)
    change ((et i).inv ≫ ap i).app _ x = ((et j).inv ≫ ap j).app _ y
    rwa [het, het]
  have hR : Presheaf.IsSheaf J R.left :=
    isSheaf_pullback J G.X.hom b' hG
      ((isAlgebraicSpace_yoneda 𝒞 S hS U).isSheaf) hB
  have hloc (i : I) : Presheaf.IsLocallySurjective J
      (pullback.snd P.hom (yoneda.map (f' i))) := by
    let := hPloc
    exact Presheaf.isLocallySurjective_of_isPullback J (IsPullback.of_hasPullback _ _).flip
  obtain ⟨act, hactIso, _, hact⟩ := exists_pseudoTorsor_of_pullbacks J
    ((isAlgebraicSpace_yoneda 𝒞 S hS U).isSheaf) (fun i => yoneda.map (f' i)) hρ
    R P hR hP acts hcacts hacts hloc
  let T : SheafTorsors G := ⟨U, b', P, act, hP, hactIso, hPloc⟩
  have ha (i : I) : actionMap (D.x i) ≫ π i = ap i ≫ actionMap T := by
    have hi := congrArg (fun k => ((eg i).hom ⊗ₘ (em i).hom).left ≫
      k.left ≫ pullback.fst P.hom (yoneda.map (f' i))) (hact i)
    have hm := congrArg (fun k => k.left ≫ pullback.fst P.hom (yoneda.map (f' i)))
      (modObj_ofIso_smul_comp (eg i) (em i))
    have hm' : ((eg i).hom ⊗ₘ (em i).hom).left ≫ (acts i).smul.left ≫
        pullback.fst P.hom (yoneda.map (f' i)) = actionMap (D.x i) ≫ π i := by
      simpa only [Over.comp_left, Category.assoc, hem] using hm
    rw [hm'] at hi
    symm
    calc
      ap i ≫ actionMap T = ((eg i).hom ⊗ₘ (em i).hom).left ≫
          pullbackTensorMap (yoneda.map (f' i)) R P ≫ act.smul.left := by
        change ap i ≫ act.smul.left = _
        rw [← hap, Category.assoc]
      _ = _ := by
        simpa only [Over.comp_left, Over.pullback_map_left, Category.assoc,
          pullback.lift_fst, pullbackTensorMap] using hi
  have hcgT (i : I) : cg i = groupBaseChange (T := D.x i) (T' := T) (f' i) (hb'' i) :=
    pullback.hom_ext
      ((hcgfst i).trans (groupBaseChange_fst (T := D.x i) (T' := T) (f' i) (hb'' i)).symm)
      ((hcg i).w.trans (groupBaseChange_snd (T := D.x i) (T' := T) (f' i) (hb'' i)).symm)
  have hapT (i : I) : ap i = actionBaseChange (T := D.x i) (T' := T)
      (f' i) (hb'' i) (π i) (hπ' i).w.symm :=
    pullback.hom_ext
      ((pullback.lift_fst _ _ _).trans
        ((congrArg (pullback.fst (D.x i).group.hom (D.x i).total.hom ≫ ·) (hcgT i)).trans
          (actionBaseChange_fst (T := D.x i) (T' := T) (f' i) (hb'' i)
            (π i) (hπ' i).w.symm).symm))
      ((pullback.lift_snd _ _ _).trans
        (actionBaseChange_snd (T := D.x i) (T' := T) (f' i) (hb'' i)
          (π i) (hπ' i).w.symm).symm)
  let πT (i : I) : D.x i ⟶ T :=
    ⟨f' i, hb'' i, π i, hπ' i, (ha i).trans (congrArg (· ≫ actionMap T) (hapT i))⟩
  refine ⟨T, rfl, πT, ?_, ?_⟩
  · intro i
    change f' i = eqToHom (D.hx i) ≫ f i ≫ eqToHom rfl
    simp [f']
  · intro i j
    apply Hom.ext
    · change (D.φ i j).base ≫ (D.xrji i j).hom.base ≫ f' j = (D.xrij i j).hom.base ≫ f' i
      exact (Category.assoc _ _ _).symm.trans (hbase i j).symm
    · exact hπc i j


/-- **Stacks 04UM.** The functor `p : 𝒢/ℬ-Torsors ⥤ (Sch/S)_fppf` of Stacks 04UL is a stack in
groupoids over the big fppf site of `S`: the three conditions of Stacks 02ZI, namely
`AlgebraicGeometry.Space.SheafTorsors.projection_isFiberedInGroupoids`,
`AlgebraicGeometry.Space.SheafTorsors.projection_isomIsSheaf` and
`AlgebraicGeometry.Space.SheafTorsors.projection_effectiveDescent`. -/
@[stacks 04UM]
theorem projection_isStackInGroupoids
    (hB : Presheaf.IsSheaf (BigFppfOver.topology 𝒞 S hS) B)
    (hG : Presheaf.IsSheaf (BigFppfOver.topology 𝒞 S hS) G.X.left) :
    Functor.IsStackInGroupoids.{w} (projection G) (BigFppfOver.topology 𝒞 S hS) where
  isFiberedInGroupoids := projection_isFiberedInGroupoids G
  isom_isSheaf := projection_isomIsSheaf G hB
  effective_descent := projection_effectiveDescent G hB hG

/-- Condition (3) of Stacks 026F for `p : 𝒢/ℬ-Torsors ⥤ (Sch/S)_fppf`: every descent datum
relative to a covering *sieve* of the big fppf site of `S` is effective. This is the
sieve-indexed reading of `AlgebraicGeometry.Space.SheafTorsors.projection_effectiveDescent`,
obtained from it by `CategoryTheory.Functor.hasEffectiveDescent_of_isStackInGroupoids`: a
covering sieve is the sieve generated by the family of all of its arrows, and that family is
indexed in the universe `max u₁ v₁` at which the conditions of Stacks 02ZI are consumed. -/
theorem projection_hasEffectiveDescent
    (hB : Presheaf.IsSheaf (BigFppfOver.topology 𝒞 S hS) B)
    (hG : Presheaf.IsSheaf (BigFppfOver.topology 𝒞 S hS) G.X.left) :
    letI : (projection G).IsFibered := (projection_isFiberedInGroupoids G).isFibered
    Functor.HasEffectiveDescent (projection G) (BigFppfOver.topology 𝒞 S hS) := by
  let : (projection G).IsFibered := (projection_isFiberedInGroupoids G).isFibered
  exact Functor.hasEffectiveDescent_of_isStackInGroupoids
    (projection_isStackInGroupoids G hB hG)

end SheafTorsors

end AlgebraicGeometry.Space

end
