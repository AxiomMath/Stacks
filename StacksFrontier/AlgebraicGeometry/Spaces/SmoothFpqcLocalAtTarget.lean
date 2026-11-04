module

public import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
public import Mathlib.CategoryTheory.Limits.Types.Coproducts
public import Mathlib.CategoryTheory.MorphismProperty.Descent
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.SmoothFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductAlgebraic
public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductInclusion
public import StacksFrontier.AlgebraicGeometry.Spaces.Coverings
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteCoproductSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.FpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeAsSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallZariskiSite
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothTfae
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.FibreProducts
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.Sheafification

/-!
# Smoothness of morphisms of algebraic spaces is fpqc local on the base (Stacks 0429)

Smoothness, as a property of morphisms in the category of algebraic spaces over `S`, is local
on the base for the fpqc topology of Tag 03YH.

## Main definitions

No new definitions are introduced; the property itself is
`AlgebraicGeometry.Space.smoothMorphismProperty`.

## Main results

* `AlgebraicGeometry.Space.smooth_isLocalAtTarget_fpqc`: smoothness of morphisms of algebraic
  spaces over `S` is local on the base for the fpqc topology.

## Implementation notes

The proof is one application of the fpqc criterion of Tag 041J, which reduces fpqc locality on
the base to three conditions, each proved here:

* compatibility with finite coproducts. A finite coproduct of algebraic spaces is an algebraic
  space (Tag 02WQ at a finite index type) and is computed in sheaves, so the comparison with the
  coproduct in the category of algebraic spaces is an isomorphism; the inclusions are open
  immersions (Tag 0F15), hence smooth and monomorphisms, and smoothness of the induced map on
  the coproduct is condition (9) of Tag 03ZF, the Zariski-local one, applied to the covering by
  the summands.
* testing smoothness on affine scheme-valued points: condition (4) of Tag 03ZF.
* descent along a surjective flat map of affine schemes: condition (4) of Tag 03ZF again, with
  Mathlib's flat descent for morphism properties of schemes supplying the descent step.

The sheaf-level work needs presheaves on the big fppf site to be sheafifiable, which is
Tag 021V and is available as instances from
`StacksFrontier.AlgebraicGeometry.Topologies.Fppf.Sheafification`.

## References

* [Stacks Project, Tag 0429](https://stacks.math.columbia.edu/tag/0429)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

attribute [local instance] AlgebraicGeometry.preservesPullbacks_bigFppfOverToScheme
  AlgebraicGeometry.hasPullbacks_bigFppfOver

universe u v w w'

attribute [local instance] AlgebraicGeometry.Space.schemeCutoff_hasPullbacks

/-- The Yoneda embedding of the big fppf site over `S` preserves pullbacks. -/
noncomputable local instance yoneda_preservesPullbacks_bigFppfOver
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
  PreservesLimitsOfShape WalkingCospan
    (CategoryTheory.yoneda : BigFppfOver B S hS ⥤ _) := inferInstance

private theorem exists_finite_coproduct_bigFppfOver
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {n : ℕ} (U : Fin n → BigFppfOver B S hS) :
    ∃ (V : BigFppfOver B S hS) (j : ∀ i, U i ⟶ V),
      Nonempty (IsColimit (Cofan.mk V j)) := by
  classical
  let C := BigFppfOver B S hS
  let Tfun := BigFppfOver.toScheme B S hS
  let Vscheme : Scheme.{u} := ∐ fun i : Fin n => Tfun.obj (U i)
  have hVscheme : Vscheme.size < B.cutoff := by
    let W : Scheme.{u} := ∐ fun i : ULift.{u} (Fin n) => Tfun.obj (U i.down)
    have hW : W.size < B.cutoff := by
      dsimp [W]
      apply Scheme.size_sigmaObj_lt B.aleph0_lt_cutoff B.aleph0_lt_cutoff_cof
      · simp
      · intro i
        exact (U i.down).left.property
    have e : Vscheme ≅ W := by
      dsimp [Vscheme, W]
      exact Sigma.whiskerEquiv (C := Scheme.{u})
        (f := fun i : Fin n => Tfun.obj (U i))
        (g := fun i : ULift.{u} (Fin n) => Tfun.obj (U i.down))
        Equiv.ulift.symm (fun _ => Iso.refl _)
    rw [Scheme.size_congr e]
    exact hW
  let Vsite : B.Schemes := B.obj hVscheme
  let κ : ∀ i : Fin n, (U i).left ⟶ Vsite := fun i =>
    B.inclusion.preimage (Sigma.ι (fun i => Tfun.obj (U i)) i)
  let cSite : Cofan (fun i : Fin n => (U i).left) := Cofan.mk Vsite κ
  have hcScheme : IsColimit (Cofan.mk Vscheme
      (fun i : Fin n => Sigma.ι (fun i : Fin n => Tfun.obj (U i)) i)) :=
    coproductIsCoproduct (fun i : Fin n => Tfun.obj (U i))
  have hκ (i : Fin n) : B.inclusion.map (κ i) =
      Sigma.ι (fun i : Fin n => Tfun.obj (U i)) i := B.inclusion.map_preimage _
  have hκsite (i : Fin n) : B.inclusion.map (cSite.inj i) =
      Sigma.ι (fun i : Fin n => Tfun.obj (U i)) i := hκ i
  have hcSite : IsColimit cSite := by
    refine Cofan.IsColimit.mk cSite (fun t => B.inclusion.preimage
      (hcScheme.desc (Cofan.mk (B.inclusion.obj t.pt)
        (fun i => B.inclusion.map (t.inj i))))) ?_ ?_
    · intro t i
      apply B.inclusion.map_injective
      rw [Functor.map_comp, B.inclusion.map_preimage, hκsite]
      exact Cofan.IsColimit.inj_desc _ hcScheme i
    · intro t m hm
      apply B.inclusion.map_injective
      rw [B.inclusion.map_preimage]
      apply Cofan.IsColimit.hom_ext hcScheme
      intro i
      calc
        Sigma.ι (fun j : Fin n => Tfun.obj (U j)) i ≫ B.inclusion.map m =
            B.inclusion.map (cSite.inj i) ≫ B.inclusion.map m := by rw [hκsite]
        _ = B.inclusion.map (t.inj i) := by rw [← Functor.map_comp, hm i]
        _ = Sigma.ι (fun j : Fin n => Tfun.obj (U j)) i ≫
            hcScheme.desc (Cofan.mk (B.inclusion.obj t.pt)
              (fun j => B.inclusion.map (t.inj j))) := by
          symm
          exact Cofan.IsColimit.inj_desc _ hcScheme i
  let bmap : Vsite ⟶ B.obj hS := B.inclusion.preimage
    (Sigma.desc fun i : Fin n => B.inclusion.map (U i).hom)
  have hbmap (i : Fin n) : B.inclusion.map (κ i) ≫
      B.inclusion.map bmap = B.inclusion.map (U i).hom := by
    rw [hκ, B.inclusion.map_preimage]
    simp
  let V : C := Over.mk bmap
  let j : ∀ i : Fin n, U i ⟶ V := fun i => Over.homMk (κ i) (by
    apply B.inclusion.map_injective
    exact hbmap i)
  let cOver : Cofan U := Cofan.mk V j
  let d (t : Cofan U) : Vsite ⟶ t.pt.left :=
    hcSite.desc (Cofan.mk t.pt.left fun i => (t.inj i).left)
  have hd (t : Cofan U) : d t ≫ t.pt.hom = bmap := by
    apply Cofan.IsColimit.hom_ext hcSite
    intro i
    calc
      κ i ≫ (d t ≫ t.pt.hom) = (κ i ≫ d t) ≫ t.pt.hom := by simp [Category.assoc]
      _ = (t.inj i).left ≫ t.pt.hom := by
        congr 1
        exact Cofan.IsColimit.fac hcSite (fun k => (t.inj k).left) i
      _ = (U i).hom := (t.inj i).w
      _ = κ i ≫ bmap := (j i).w.symm
  have hcOver : IsColimit cOver := by
    refine Cofan.IsColimit.mk cOver (fun t => Over.homMk (d t) (hd t)) ?_ ?_
    · intro t i
      apply Over.OverMorphism.ext
      exact Cofan.IsColimit.fac hcSite (fun k => (t.inj k).left) i
    · intro t m hm
      apply Over.OverMorphism.ext
      apply Cofan.IsColimit.hom_ext hcSite
      intro i
      calc
        κ i ≫ m.left = (t.inj i).left := by
          exact congrArg (fun q : U i ⟶ t.pt => q.left) (hm i)
        _ = κ i ≫ d t := by
          symm
          exact Cofan.IsColimit.fac hcSite (fun k => (t.inj k).left) i
  exact ⟨V, j, ⟨hcOver⟩⟩

private def cofanAsCocone {C : Type w} [Category.{w'} C] {I : Type v}
    {X : I → C} (c : Cofan X) : Cocone (Discrete.functor X) where
  pt := c.pt
  ι := {
    app := fun i => c.inj i.as
    naturality := by
      intro i j f
      have hij : i = j := Discrete.ext (Discrete.eq_of_hom f)
      subst j
      simp }

private def cofanCoconeIsColimit {C : Type w} [Category.{w'} C] {I : Type v}
    {X : I → C} {c : Cofan X} (hc : IsColimit c) :
    IsColimit (cofanAsCocone c) := by
  refine IsColimit.mk (fun t => hc.desc (Cofan.mk t.pt fun i => t.ι.app (Discrete.mk i)))
    ?_ ?_
  · intro t i
    exact Cofan.IsColimit.fac hc (fun j => t.ι.app (Discrete.mk j)) i.as
  · intro t m hm
    apply Cofan.IsColimit.hom_ext hc
    intro i
    calc
      c.inj i ≫ m = t.ι.app (Discrete.mk i) := hm (Discrete.mk i)
      _ = c.inj i ≫ Cofan.IsColimit.desc hc
          (fun j => t.ι.app (Discrete.mk j)) :=
        (Cofan.IsColimit.fac hc (fun j => t.ι.app (Discrete.mk j)) i).symm


private theorem smooth_pullback_snd_iff
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y Z : AlgebraicSpaces B S hS}
    (f : X ⟶ Z) (g : Y ⟶ Z) :
    (smoothMorphismProperty B S hS) (Limits.pullback.snd f g) ↔
      IsSmooth B S hS (Limits.pullback.snd f.hom g.hom) := by
  let hp := AlgebraicSpaces.isPullback_fiberProduct B S hS f g
  let e := hp.isoPullback
  let q : AlgebraicSpaces.fiberProduct B S hS f g ⟶ Y :=
    ObjectProperty.homMk (Limits.pullback.snd f.hom g.hom)
  have hcomm : e.symm.hom ≫ q = Limits.pullback.snd f g := hp.isoPullback_inv_snd
  let eArrow : Arrow.mk (Limits.pullback.snd f g) ≅ Arrow.mk q :=
    Arrow.isoMk (f := Arrow.mk (Limits.pullback.snd f g))
      (g := Arrow.mk q) e.symm (Iso.refl _) (by simpa using hcomm)
  rw [((smoothMorphismProperty B S hS).arrow_mk_iso_iff eArrow)]
  rfl

private noncomputable def algebraicSpaceSheaf
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS) :
    Sheaf (BigFppfOver.topology B S hS) (Type u) :=
  ⟨X.obj, X.property.isSheaf⟩

private def algebraicSpaceSheafMap
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) :
    algebraicSpaceSheaf B S hS X ⟶ algebraicSpaceSheaf B S hS Y :=
  ⟨f.hom⟩

private noncomputable def algebraicSpaceCofan_isColimit_of_sheafCofan
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {I : Type v} (X : I → AlgebraicSpaces B S hS)
    (G : Sheaf (BigFppfOver.topology B S hS) (Type u))
    (ι : ∀ i, algebraicSpaceSheaf B S hS (X i) ⟶ G)
    (hG : IsColimit (Cofan.mk G ι)) (hGalg : IsAlgebraicSpace B S hS G.obj) :
    IsColimit (Cofan.mk ⟨G.obj, hGalg⟩ (fun i =>
      ObjectProperty.homMk (ι i).hom)) := by
  refine Cofan.IsColimit.mk _ (fun t => ObjectProperty.homMk (hG.desc
    (Cofan.mk (algebraicSpaceSheaf B S hS t.pt)
      fun i => algebraicSpaceSheafMap B S hS (t.inj i))).hom) ?_ ?_
  · intro t i
    apply ObjectProperty.hom_ext
    exact congrArg (fun f => f.hom) (Cofan.IsColimit.fac hG
      (fun j => algebraicSpaceSheafMap B S hS (t.inj j)) i)
  · intro t m hm
    apply ObjectProperty.hom_ext
    have heq : algebraicSpaceSheafMap B S hS m =
        hG.desc (Cofan.mk (algebraicSpaceSheaf B S hS t.pt)
          (fun i => algebraicSpaceSheafMap B S hS (t.inj i))) := by
      apply Cofan.IsColimit.hom_ext hG
      intro i
      calc
        ι i ≫ algebraicSpaceSheafMap B S hS m =
            algebraicSpaceSheafMap B S hS
              (ObjectProperty.homMk (ι i).hom ≫ m) := rfl
        _ = algebraicSpaceSheafMap B S hS (t.inj i) :=
          congrArg (algebraicSpaceSheafMap B S hS) (hm i)
        _ = ι i ≫ hG.desc (Cofan.mk (algebraicSpaceSheaf B S hS t.pt)
            (fun j => algebraicSpaceSheafMap B S hS (t.inj j))) :=
          (Cofan.IsColimit.fac hG
            (fun j => algebraicSpaceSheafMap B S hS (t.inj j)) i).symm
    exact congrArg (fun f => f.hom) heq

private theorem range_sigma_desc_eq_iSup
    {C : Type (u + 1)} [Category.{u} C]
    {I : Type v} [Small.{u} I] {F : I → Cᵒᵖ ⥤ Type u}
    {G : Cᵒᵖ ⥤ Type u} (f : ∀ i, F i ⟶ G) :
    Subfunctor.range (Sigma.desc f) = ⨆ i, Subfunctor.range (f i) := by
  classical
  ext U x
  let hcEval := isColimitOfPreserves ((evaluation Cᵒᵖ (Type u)).obj U) (coproductIsCoproduct F)
  simp only [Subfunctor.range_obj, Set.mem_range, Subfunctor.iSup_obj,
    Set.mem_iUnion]
  constructor
  · rintro ⟨z, rfl⟩
    obtain ⟨⟨i⟩, y, rfl⟩ := Types.jointly_surjective_of_isColimit hcEval z
    exact ⟨i, y, congrArg (fun q => q.app U y) (Sigma.ι_desc f i).symm⟩
  · rintro ⟨i, y, rfl⟩
    exact ⟨(Sigma.ι F i).app U y, congrArg (fun q => q.app U y) (Sigma.ι_desc f i)⟩

private theorem locallySurjective_sigma_desc_of_denseImage
    {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
    {I : Type v} [Small.{u} I] {F : I → Cᵒᵖ ⥤ Type u}
    {G : Cᵒᵖ ⥤ Type u} (f : ∀ i, F i ⟶ G)
    (hdense : (⨆ i, Subfunctor.range (f i)).sheafify J = ⊤) :
    Presheaf.IsLocallySurjective J (Sigma.desc f) := by
  rw [Presheaf.isLocallySurjective_iff_range_sheafify_eq_top', range_sigma_desc_eq_iSup f, hdense]

private theorem locallySurjective_sigma_desc_of_sheafCoproduct
    {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
    {I : Type v} [Small.{u} I] (F : I → Sheaf J (Type u)) (G : Sheaf J (Type u))
    (ι : ∀ i, F i ⟶ G) (hc : IsColimit (Cofan.mk G ι)) :
    Presheaf.IsLocallySurjective J (Sigma.desc fun i => (ι i).hom) := by
  classical
  let T : Subfunctor G.obj := ⨆ i, Subfunctor.range (ι i).hom
  let H : Sheaf J (Type u) :=
    ⟨(T.sheafify J).toFunctor,
      (isSheaf_iff_isSheaf_of_type J _).mpr
        (T.sheafify_isSheaf ((isSheaf_iff_isSheaf_of_type J _).mp G.property))⟩
  let k : H ⟶ G := ⟨Subfunctor.ι (T.sheafify J)⟩
  let η (i : I) : F i ⟶ H :=
    ⟨Subfunctor.lift (ι i).hom
      ((le_iSup (fun j => Subfunctor.range (ι j).hom) i).trans
        (Subfunctor.le_sheafify J T))⟩
  have hfac (i : I) : η i ≫ k = ι i := by
    apply Sheaf.hom_ext
    ext U x
    rfl
  let d : G ⟶ H := Cofan.IsColimit.desc hc η
  have hd : d ≫ k = 𝟙 G := by
    apply Cofan.IsColimit.hom_ext hc
    intro i
    calc
      (Cofan.mk G ι).inj i ≫ (d ≫ k) =
          ((Cofan.mk G ι).inj i ≫ d) ≫ k := (Category.assoc _ _ _).symm
      _ = η i ≫ k := by rw [Cofan.IsColimit.fac]
      _ = (Cofan.mk G ι).inj i := hfac i
      _ = (Cofan.mk G ι).inj i ≫ 𝟙 G := by simp
  have htop : T.sheafify J = ⊤ := by
    ext U x
    refine ⟨fun _ => trivial, fun _ => ?_⟩
    let y := d.hom.app U x
    have hy : (Subfunctor.ι (T.sheafify J)).app U y = x := by
      simpa [d, k] using congrArg (fun q : G ⟶ G => q.hom.app U x) hd
    exact hy ▸ y.property
  exact locallySurjective_sigma_desc_of_denseImage (J := J) (fun i => (ι i).hom) htop

private theorem isSmooth_of_isOpenImmersion
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y)
    (f : X ⟶ Y) (hf : IsOpenImmersion B S hS f) :
    IsSmooth B S hS f := by
  let Tfun := BigFppfOver.toScheme B S hS
  have hopenSmooth :
      (MorphismProperty.inverseImage (@AlgebraicGeometry.IsOpenImmersion.{u}) Tfun) ≤
        (MorphismProperty.inverseImage (@Smooth.{u}) Tfun) := by
    apply MorphismProperty.monotone_inverseImage
    intro A A' q hq
    let : AlgebraicGeometry.IsOpenImmersion q := hq
    exact inferInstance
  change (MorphismProperty.inverseImage
    (@AlgebraicGeometry.IsOpenImmersion.{u}) Tfun).relative yoneda f at hf
  have hrelSmooth :
      (MorphismProperty.inverseImage (@Smooth.{u}) Tfun).relative yoneda f := by
    refine ⟨hf.1, ?_⟩
    intro A A' g fst snd hpb
    exact hopenSmooth _ (hf.2 g fst snd hpb)
  let : MorphismProperty.IsLocalAtTarget (@Smooth.{u}) Scheme.fppfPrecoverage :=
    MorphismProperty.IsLocalAtTarget.of_le Scheme.fppfPrecoverage_le_fpqcPrecoverage
  have hiff := holdsOnEveryEtaleChart_iff_relative
    B S hS (@Smooth.{u} : MorphismProperty Scheme.{u})
    AlgebraicGeometry.Smooth.isEtaleLocalOnSourceAndTarget hX hY f hf.1
  exact hiff.mpr hrelSmooth

/-- A colimit cofan of finitely many algebraic spaces has open-immersion inclusions, and the
induced map from the coproduct of presheaves is locally surjective. -/
private theorem isOpenImmersion_and_locallySurjective_of_isColimit
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) {n : ℕ}
    (X : Fin n → AlgebraicSpaces B S hS) (X₀ : AlgebraicSpaces B S hS)
    (ιX : ∀ i, X i ⟶ X₀) (hX : IsColimit (Cofan.mk X₀ ιX)) :
    (∀ i, IsOpenImmersion B S hS (ιX i).hom) ∧
      Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS)
        (Sigma.desc fun i => (ιX i).hom) := by
  let C := BigFppfOver B S hS
  let Tfun := BigFppfOver.toScheme B S hS
  let : HasWeakSheafify (BigFppfOver.topology B S hS) (Type u) :=
    (hasSheafifyBigFppfOver B S hS).isRightAdjoint
  let : HasColimitsOfShape (Discrete (Fin n))
      (Sheaf (BigFppfOver.topology B S hS) (Type u)) :=
    CategoryTheory.Sheaf.instHasColimitsOfShape
  choose U a hsurj hetale using fun i : Fin n => (X i).property.exists_atlas
  obtain ⟨Vx, jx, hVxNonempty⟩ := exists_finite_coproduct_bigFppfOver B S hS U
  let hVx := Classical.choice hVxNonempty
  let Fx : Fin n → Sheaf (BigFppfOver.topology B S hS) (Type u) :=
    fun i => algebraicSpaceSheaf B S hS (X i)
  let Gx : Sheaf (BigFppfOver.topology B S hS) (Type u) := ∐ Fx
  have hcGx : IsColimit (Cofan.mk Gx (fun i => Sigma.ι Fx i)) :=
    coproductIsCoproduct Fx
  have hGxAlg : IsAlgebraicSpace B S hS Gx.obj :=
    AlgebraicGeometry.isAlgebraicSpace_coproduct B S hS
      (F := fun i => (X i).obj) (hF := fun i => (X i).property)
      Gx (fun i => Sigma.ι Fx i) hcGx U a hsurj hetale Vx jx hVx
  let Xcop : AlgebraicSpaces B S hS := ⟨Gx.obj, hGxAlg⟩
  have hcXcop : IsColimit (Cofan.mk Xcop (fun i =>
      ObjectProperty.homMk (Sigma.ι Fx i).hom)) :=
    algebraicSpaceCofan_isColimit_of_sheafCofan B S hS X Gx
      (fun i => Sigma.ι Fx i) hcGx hGxAlg
  let eX := hcXcop.coconePointUniqueUpToIso hX
  let X₀sheaf := algebraicSpaceSheaf B S hS X₀
  let eXsh : Gx ≅ X₀sheaf := {
    hom := algebraicSpaceSheafMap B S hS eX.hom
    inv := algebraicSpaceSheafMap B S hS eX.inv
    hom_inv_id := by
      apply Sheaf.hom_ext
      exact congrArg (fun q => q.hom)
        (congrArg (algebraicSpaceSheafMap B S hS) eX.hom_inv_id)
    inv_hom_id := by
      apply Sheaf.hom_ext
      exact congrArg (fun q => q.hom)
        (congrArg (algebraicSpaceSheafMap B S hS) eX.inv_hom_id) }
  have hXmaps : ∀ i, (Sigma.ι Fx i).hom ≫ eXsh.hom.hom = (ιX i).hom := by
    intro i
    have h := IsColimit.comp_coconePointUniqueUpToIso_hom hcXcop hX (Discrete.mk i)
    exact congrArg (fun q => q.hom) h
  let hXlsCop := locallySurjective_sigma_desc_of_sheafCoproduct
    Fx Gx (fun i => Sigma.ι Fx i) hcGx
  have hXls : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS)
      (Sigma.desc fun i => (ιX i).hom) := by
    have : IsIso eXsh.hom := Iso.isIso_hom eXsh
    have : IsIso eXsh.hom.hom := by
      show IsIso ((sheafToPresheaf _ _).map eXsh.hom)
      exact Functor.map_isIso _ _
    let : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS)
        eXsh.hom.hom := by infer_instance
    let : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS)
        (Sigma.desc fun i => (Sigma.ι Fx i).hom) := hXlsCop
    have hcomp : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS)
        (Sigma.desc (fun i => (Sigma.ι Fx i).hom) ≫ eXsh.hom.hom) := by infer_instance
    have hdesc : Sigma.desc (fun i => (Sigma.ι Fx i).hom) ≫ eXsh.hom.hom =
        Sigma.desc (fun i => (ιX i).hom) := by
      apply Sigma.hom_ext
      intro i
      have hright :
          Sigma.ι (fun i => (Fx i).obj) i ≫ Sigma.desc (fun i => (ιX i).hom) =
            (ιX i).hom := by
        dsimp only [Fx, algebraicSpaceSheaf]
        exact Sigma.ι_desc _ _
      dsimp only [Fx, algebraicSpaceSheaf] at hright
      rw [← Category.assoc, Sigma.ι_desc]
      exact (hXmaps i).trans hright.symm
    rw [hdesc] at hcomp
    exact hcomp
  refine ⟨fun i => ?_, hXls⟩
  let hcSplit := splitColimit (fun i => Sigma.ι Fx i) hcGx i
  have h := coproductInl_isOpenImmersion B S hS
    (Fx i) _ Gx (Sigma.ι Fx i) _ hcSplit
  have : IsIso eX.hom.hom := by infer_instance
  let Q := MorphismProperty.presheaf (MorphismProperty.inverseImage
    (@AlgebraicGeometry.IsOpenImmersion.{u}) Tfun)
  let : Q.RespectsIso := inferInstance
  have hfac : (Sigma.ι Fx i).hom ≫ eX.hom.hom = (ιX i).hom := hXmaps i
  show Q (ιX i).hom
  rw [← hfac]
  exact MorphismProperty.RespectsIso.postcomp Q eX.hom.hom _ h

private theorem smooth_finite_coproduct
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    ∀ (n : ℕ) (X Y : Fin n → AlgebraicSpaces B S hS)
      (f : ∀ i, X i ⟶ Y i) (X₀ Y₀ : AlgebraicSpaces B S hS)
      (ιX : ∀ i, X i ⟶ X₀) (ιY : ∀ i, Y i ⟶ Y₀) (g : X₀ ⟶ Y₀),
      IsColimit (Cofan.mk X₀ ιX) → IsColimit (Cofan.mk Y₀ ιY) →
      (∀ i, f i ≫ ιY i = ιX i ≫ g) →
      (∀ i, smoothMorphismProperty B S hS (f i)) →
      smoothMorphismProperty B S hS g := by
  intro n X Y f X₀ Y₀ ιX ιY g hX hY hcomm hf
  obtain ⟨hXopen, hXls⟩ :=
    isOpenImmersion_and_locallySurjective_of_isColimit B S hS X X₀ ιX hX
  obtain ⟨hYopen, -⟩ :=
    isOpenImmersion_and_locallySurjective_of_isColimit B S hS Y Y₀ ιY hY
  let Xindex := ULift.{u} (Fin n)
  let Xopen : Xindex → Subfunctor X₀.obj := fun i =>
    Subfunctor.range (ιX i.down).hom
  have hXopens : ∀ i : Xindex, IsOpenSubspace B S hS (Xopen i) := by
    intro i
    have : Mono (ιX i.down).hom :=
      mono_of_isOpenImmersion B S hS (ιX i.down).hom (hXopen i.down)
    simpa [Xopen] using isOpenSubspace_range_of_open B S hS (ιX i.down).hom
      (X i.down).property (hXopen i.down)
  have hXlsRange : Presheaf.IsLocallySurjective
      (BigFppfOver.topology B S hS)
      (Sigma.desc fun i : Xindex => (Xopen i).ι) := by
    have hdense := (Presheaf.isLocallySurjective_iff_range_sheafify_eq_top'
      (BigFppfOver.topology B S hS) _).mp hXls
    have hrange := range_sigma_desc_eq_iSup (fun i : Fin n => (ιX i).hom)
    have hdenseUnion : (⨆ i : Fin n, Subfunctor.range (ιX i).hom).sheafify
        (BigFppfOver.topology B S hS) = ⊤ := by
      simpa [hrange] using hdense
    have hEq : (⨆ i : Xindex, Subfunctor.range ((Xopen i).ι)) =
        ⨆ i : Fin n, Subfunctor.range (ιX i).hom := by
      calc
        (⨆ i : Xindex, Subfunctor.range ((Xopen i).ι)) =
            ⨆ i : Xindex, Xopen i := by
          apply iSup_congr
          intro i
          exact Subfunctor.range_ι (Xopen i)
        _ = ⨆ i : Fin n, Subfunctor.range (ιX i).hom := by
          show (⨆ i : ULift (Fin n), Subfunctor.range (ιX i.down).hom) = _
          exact iSup_ulift
            (fun i : ULift (Fin n) => Subfunctor.range (ιX i.down).hom)
    apply locallySurjective_sigma_desc_of_denseImage
      (J := BigFppfOver.topology B S hS)
      (fun i : Xindex => (Xopen i).ι)
    rw [hEq]
    exact hdenseUnion
  have hXcover : IsZariskiCover B S hS Xindex Xopen :=
    ⟨hXopens, hXlsRange⟩
  have hYsmooth : ∀ i, IsSmooth B S hS (ιY i).hom := by
    intro i
    exact isSmooth_of_isOpenImmersion B S hS (Y i).property Y₀.property
      (ιY i).hom (hYopen i)
  have hcompXi : ∀ i, IsSmooth B S hS
      ((ιX i).hom ≫ g.hom) := by
    intro i
    have hfi : IsSmooth B S hS (f i).hom := hf i
    have hcomp := isSmooth_comp B S hS (X i).property
      (Y i).property Y₀.property (f i).hom (ιY i).hom hfi (hYsmooth i)
    have hcommi : (f i).hom ≫ (ιY i).hom = (ιX i).hom ≫ g.hom :=
      congrArg (fun q => q.hom) (hcomm i)
    rw [← hcommi]
    exact hcomp
  have hcompRange : ∀ i : Fin n, IsSmooth B S hS
      ((Xopen (ULift.up i)).ι ≫ g.hom) := by
    intro i
    have : Mono (ιX i).hom := mono_of_isOpenImmersion B S hS
      (ιX i).hom (hXopen i)
    let Q := smoothMorphismProperty B S hS
    let : Q.RespectsIso := inferInstance
    let XopenObj : AlgebraicSpaces B S hS :=
      ⟨(Xopen (ULift.up i)).toFunctor, (hXopens (ULift.up i)).1⟩
    let e : X i ≅ XopenObj := by
      let erange := asIso (Subfunctor.toRange (ιX i).hom)
      refine {
        hom := ObjectProperty.homMk erange.hom
        inv := ObjectProperty.homMk erange.inv
        hom_inv_id := ?_
        inv_hom_id := ?_ }
      · apply ObjectProperty.hom_ext
        exact erange.hom_inv_id
      · apply ObjectProperty.hom_ext
        exact erange.inv_hom_id
    let : IsIso e.hom := Iso.isIso_hom e
    let j : XopenObj ⟶ X₀ := ObjectProperty.homMk (Xopen (ULift.up i)).ι
    have hfac : (e.hom ≫ j).hom = (ιX i).hom := by
      show (Subfunctor.toRange (ιX i).hom ≫ (Xopen (ULift.up i)).ι) = _
      simp [Xopen]
    have hcompIso : Q (e.hom ≫ (j ≫ g)) := by
      show IsSmooth B S hS ((e.hom ≫ j).hom ≫ g.hom)
      rw [hfac]
      exact hcompXi i
    have hcomp : Q (j ≫ g) :=
      (Q.cancel_left_of_respectsIso e.hom _).mp hcompIso
    show IsSmooth B S hS ((Xopen (ULift.up i)).ι ≫ g.hom)
    exact hcomp
  have hpointwise : ∀ x : points B S hS X₀.obj,
      IsSmoothAt B S hS g.hom x := by
    have hpointCover :=
      (isZariskiCover_iff_iUnion_points
        B S hS X₀.obj X₀.property Xindex Xopen hXopens).mp hXcover
    intro x
    have hx : x ∈ ⋃ i : Xindex, Set.range
        (pointsMap B S hS (Xopen i).toFunctor (Xopen i).ι) := by
      rw [hpointCover]
      exact Set.mem_univ x
    rcases Set.mem_iUnion.mp hx with ⟨i, ⟨y, hy⟩⟩
    refine ⟨Xopen i, hXopens i, y, hy, ?_⟩
    exact hcompRange i.down
  have hTFAE := isSmooth_tfae B S hS X₀.property Y₀.property g.hom
  exact (hTFAE.out 1 2).mpr hpointwise

private theorem smooth_iff_affine_pullback
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    ∀ {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y),
      smoothMorphismProperty B S hS f ↔
        ∀ (T : BigAffineFppf B S hS)
          (g : schemeSpace
            ((BigAffineFppf.inclusion B S hS).obj T) ⟶ Y),
          smoothMorphismProperty B S hS (pullback.snd f g) := by
  intro X Y f
  show IsSmooth B S hS f.hom ↔ _
  have hTFAE := isSmooth_tfae B S hS X.property Y.property f.hom
  have hiff := (hTFAE.out 1 4)
  constructor
  · intro hf T g
    apply (smooth_pullback_snd_iff B S hS f g).mpr
    exact hiff.mp hf
      ((BigAffineFppf.inclusion B S hS).obj T)
      g.hom (BigAffineFppf.isAffine_toScheme_obj B S hS T)
  · intro h
    apply hiff.mpr
    intro Z g hZ
    let T : BigAffineFppf B S hS := ⟨Z, hZ⟩
    let hg : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj T) ⟶ Y.obj := g
    have hP := h T (ObjectProperty.homMk
      (X := schemeSpace
        ((BigAffineFppf.inclusion B S hS).obj T)) (Y := Y) hg)
    change (smoothMorphismProperty B S hS)
      (Limits.pullback.snd f (ObjectProperty.homMk
        (X := schemeSpace
          ((BigAffineFppf.inclusion B S hS).obj T)) (Y := Y) hg)) at hP
    have hsm := (smooth_pullback_snd_iff B S hS f (ObjectProperty.homMk
      (X := schemeSpace
        ((BigAffineFppf.inclusion B S hS).obj T)) (Y := Y) hg)).mp hP
    have hmap : (ObjectProperty.homMk
        (X := schemeSpace
          ((BigAffineFppf.inclusion B S hS).obj T)) (Y := Y) hg).hom = g := by
      rfl
    rw [hmap] at hsm
    exact hsm

private theorem smooth_of_affine_fpqc_pullback
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    ∀ (T T' : BigAffineFppf B S hS) (g : T' ⟶ T),
      Flat ((BigAffineFppf.toScheme B S hS).map g) →
      Surjective ((BigAffineFppf.toScheme B S hS).map g) →
      ∀ (X : AlgebraicSpaces B S hS)
        (f : X ⟶ schemeSpace
          ((BigAffineFppf.inclusion B S hS).obj T)),
        smoothMorphismProperty B S hS (pullback.snd f
          (schemeSpaceMap
            ((BigAffineFppf.inclusion B S hS).map g))) →
        smoothMorphismProperty B S hS f := by
  intro T T' g hgFlat hgSurj X f hf
  let C := BigFppfOver B S hS
  let Tfun : C ⥤ Scheme := BigFppfOver.toScheme B S hS
  let T₀ := (BigAffineFppf.inclusion B S hS).obj T
  let T'₀ := (BigAffineFppf.inclusion B S hS).obj T'
  let g₀ : T'₀ ⟶ T₀ := (BigAffineFppf.inclusion B S hS).map g
  obtain ⟨U, a, haSurj, haEtale⟩ := X.property.exists_atlas
  let u : U ⟶ T₀ := yoneda.preimage (a ≫ f.hom)
  have huf : a ≫ f.hom = yoneda.map u := by
    exact (yoneda.map_preimage (a ≫ f.hom)).symm
  have hg₀ : yoneda.map g₀ =
      (schemeSpaceMap (B := B) (S := S) (hS := hS) g₀).hom := rfl
  let W : C := Limits.pullback u g₀
  let Pobj := AlgebraicSpaces.fiberProduct B S hS f
    (schemeSpaceMap (B := B) (S := S) (hS := hS) g₀)
  have hW : IsPullback (yoneda.map (Limits.pullback.fst u g₀))
      (yoneda.map (Limits.pullback.snd u g₀)) (yoneda.map u) (yoneda.map g₀) :=
    (IsPullback.of_hasPullback u g₀).map yoneda
  let Qobj := Limits.pullback a (Limits.pullback.fst f.hom (yoneda.map g₀))
  let e₁ : yoneda.obj W ≅ Limits.pullback (yoneda.map u) (yoneda.map g₀) :=
    hW.isoPullback
  let e₂ : Limits.pullback (yoneda.map u) (yoneda.map g₀) ≅ Qobj :=
    (Limits.pullback.congrHom huf rfl).symm ≪≫
      (Limits.pullbackRightPullbackFstIso f.hom (yoneda.map g₀) a).symm
  let e : yoneda.obj W ≅ Qobj := e₁ ≪≫ e₂
  let qchart := Limits.pullback.snd a (Limits.pullback.fst f.hom (yoneda.map g₀))
  let p' : yoneda.obj W ⟶ Pobj.obj := e.hom ≫ qchart
  let QEtale := MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u}) Tfun
  have hpEtale : QEtale.presheaf p' := by
    let : QEtale.IsStableUnderBaseChange := by
      refine ⟨?_⟩
      intro X₁ X₂ Y₂ X₃ fst snd f₁ g₁ sq hg
      exact Etale.etale_isStableUnderBaseChange.of_isPullback (sq.map Tfun) hg
    let : QEtale.presheaf.IsStableUnderBaseChange :=
      MorphismProperty.relative_isStableUnderBaseChange QEtale
    have hq : QEtale.presheaf qchart :=
      MorphismProperty.IsStableUnderBaseChange.of_isPullback
        (IsPullback.of_hasPullback a (Limits.pullback.fst f.hom
          (schemeSpaceMap (B := B) (S := S) (hS := hS) g₀).hom)) haEtale
    show QEtale.presheaf (e.hom ≫ qchart)
    exact MorphismProperty.RespectsIso.precomp QEtale.presheaf e.hom _ hq
  have hcomm : yoneda.map (Limits.pullback.snd u g₀) ≫ 𝟙 (yoneda.obj T'₀) =
      p' ≫ (Limits.pullback.snd f.hom
        (schemeSpaceMap (B := B) (S := S) (hS := hS) g₀).hom) := by
    rw [Category.comp_id]
    show yoneda.map (Limits.pullback.snd u g₀) =
      e.hom ≫ qchart ≫ Limits.pullback.snd f.hom (yoneda.map g₀)
    have hstep : e₂.hom ≫ qchart ≫ Limits.pullback.snd f.hom
        (yoneda.map g₀) =
        Limits.pullback.snd (yoneda.map u) (yoneda.map g₀) := by
      dsimp [e₂, qchart]
      -- The target here mentions `(schemeSpace T₀).obj` where the pullback lemmas expect
      -- `yoneda.obj T₀`. The two are definitionally equal, but only through the semireducible
      -- `AlgebraicGeometry.schemeSpace`, so `simp` reports `made no progress` with an
      -- application type mismatch between the two spellings. Removing the option fails, and
      -- `dsimp [schemeSpace, schemeSpaceMap]` to normalize the spelling first and a `show` of
      -- the normalized goal leave the same mismatch one layer further in. This is the
      -- only `set_option` in the file, and it is scoped to this single `simp`; the other
      -- options of this kind are unnecessary here.
      set_option backward.isDefEq.respectTransparency false in
        simp [Iso.trans_hom, Iso.symm_hom, Category.assoc, pullback.map,
          pullbackRightPullbackFstIso_inv_snd_snd, pullback.congrHom_inv]
    calc
      yoneda.map (Limits.pullback.snd u g₀) =
          e₁.hom ≫ Limits.pullback.snd (yoneda.map u) (yoneda.map g₀) :=
        hW.isoPullback_hom_snd.symm
      _ = e₁.hom ≫ e₂.hom ≫ qchart ≫ Limits.pullback.snd f.hom
          (yoneda.map g₀) := by
        simpa [Category.assoc] using congrArg (fun q => e₁.hom ≫ q) hstep.symm
      _ = e.hom ≫ qchart ≫ Limits.pullback.snd f.hom
          (yoneda.map g₀) := rfl
  have hf' : IsSmooth B S hS
      (Limits.pullback.snd f.hom
        (schemeSpaceMap (B := B) (S := S) (hS := hS) g₀).hom) :=
    (smooth_pullback_snd_iff B S hS f
      (schemeSpaceMap (B := B) (S := S) (hS := hS) g₀)).mp hf
  have hTFAE' := isSmooth_tfae B S hS Pobj.property
    (schemeSpace T'₀).property
    (Limits.pullback.snd f.hom
      (schemeSpaceMap (B := B) (S := S) (hS := hS) g₀).hom)
  have hAll := (hTFAE'.out 1 7).mp hf'
  have hsmooth' : Smooth (Tfun.map (Limits.pullback.snd u g₀)) := by
    apply hAll W T'₀ p' (𝟙 _) (Limits.pullback.snd u g₀) hpEtale
    · let QEtale' := MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u}) Tfun
      show yoneda.relativelyRepresentable (𝟙 (yoneda.obj T'₀)) ∧ _
      let idIso := Iso.refl (yoneda.obj T'₀)
      have : IsIso idIso.hom := idIso.isIso_hom
      refine ⟨Functor.relativelyRepresentable.of_isIso yoneda idIso.hom, ?_⟩
      intro A C' b fst snd sq
      have hIso : IsIso (yoneda.map snd) := sq.isIso_snd_of_isIso idIso.isIso_hom
      let := hIso
      have : IsIso snd := Yoneda.fullyFaithful.isIso_of_isIso_map _
      have : IsIso (Tfun.map snd) := by infer_instance
      show Etale (Tfun.map snd)
      exact inferInstance
    · exact hcomm
  have hdesc : Smooth (Tfun.map u) := by
    let : IsAffine (Tfun.obj T₀) := (BigAffineFppf.isAffine_toScheme_obj B S hS T)
    let : IsAffine (Tfun.obj T'₀) := (BigAffineFppf.isAffine_toScheme_obj B S hS T')
    let Psm : MorphismProperty Scheme.{u} := @Smooth
    let Qfpqc : MorphismProperty Scheme.{u} := @Surjective ⊓ @Flat ⊓ @QuasiCompact
    let : Psm.RespectsIso := inferInstance
    exact MorphismProperty.of_pullback_snd_of_descendsAlong
      (P := Psm) (Q := Qfpqc)
      (show Qfpqc (Tfun.map g₀) from
        ⟨⟨hgSurj, hgFlat⟩, inferInstance⟩)
      (by
        have hpb := (IsPullback.of_hasPullback u g₀).map Tfun
        let e := hpb.isoPullback
        have he : e.hom ≫ Limits.pullback.snd (Tfun.map u) (Tfun.map g₀) =
            Tfun.map (Limits.pullback.snd u g₀) := hpb.isoPullback_hom_snd
        have hcomp : Smooth
            (e.hom ≫ Limits.pullback.snd (Tfun.map u) (Tfun.map g₀)) := by
          rw [he]
          exact hsmooth'
        exact (MorphismProperty.cancel_left_of_respectsIso
          (P := Psm) e.hom _).mp hcomp)
  have hchart : HoldsOnEveryEtaleChart B S hS
      (@Smooth.{u} : MorphismProperty Scheme.{u}) (yoneda.map u) := by
    have hrep := holdsOnEveryEtaleChart_iff_representable
      (B := B) (S := S) (hS := hS) (P := @Smooth)
      (hP := AlgebraicGeometry.Smooth.isEtaleLocalOnSourceAndTarget)
      (F := yoneda.obj U) (G := yoneda.obj T₀) (f := yoneda.map u)
    let eU : (yoneda.obj U).reprX ≅ U :=
      yoneda.preimageIso (yoneda.obj U).reprW
    let eT : (yoneda.obj T₀).reprX ≅ T₀ :=
      yoneda.preimageIso (yoneda.obj T₀).reprW
    let u₀ := yoneda.preimage
      ((yoneda.obj U).reprW.hom ≫ yoneda.map u ≫ (yoneda.obj T₀).reprW.inv)
    have hu₀ : eU.hom ≫ u = u₀ ≫ eT.hom := by
      apply yoneda.map_injective
      simp [u₀, eU, eT, Functor.map_preimage, Category.assoc]
    have hArrow : Arrow.mk u₀ ≅ Arrow.mk u :=
      Arrow.isoMk (f := Arrow.mk u₀) (g := Arrow.mk u) eU eT hu₀
    have hnorm : Smooth (Tfun.map u₀) := by
      let Qsm := MorphismProperty.inverseImage (@Smooth.{u}) Tfun
      let : MorphismProperty.IsStableUnderComposition
          (@Smooth.{u} : MorphismProperty Scheme.{u}) := inferInstance
      let : MorphismProperty.IsStableUnderComposition Qsm := {
        comp_mem := by
          intro A A' A'' f g hf hg
          change Smooth (Tfun.map f) at hf
          change Smooth (Tfun.map g) at hg
          show Smooth (Tfun.map (f ≫ g))
          rw [Functor.map_comp]
          exact MorphismProperty.comp_mem (@Smooth.{u}) _ _ hf hg }
      have hIso : MorphismProperty.isomorphisms C ≤ Qsm := by
        intro A A' e he
        show Smooth (Tfun.map e)
        have : IsIso (Tfun.map e) := Functor.map_isIso Tfun e
        exact inferInstance
      let : MorphismProperty.RespectsIso Qsm :=
        MorphismProperty.respectsIso_of_isStableUnderComposition hIso
      exact (Qsm.arrow_mk_iso_iff hArrow).mpr hdesc
    apply hrep.mpr
    show Smooth (Tfun.map
      (yoneda.preimage ((yoneda.obj U).reprW.hom ≫ yoneda.map u ≫
        (yoneda.obj T₀).reprW.inv)))
    exact hnorm
  have hcomp : IsSmooth B S hS (a ≫ f.hom) := by
    show HoldsOnEveryEtaleChart B S hS
      (@Smooth.{u} : MorphismProperty Scheme.{u}) (a ≫ f.hom)
    rw [huf]
    exact hchart
  have hTFAE := isSmooth_tfae B S hS X.property
    (schemeSpace T₀).property f.hom
  apply (hTFAE.out 1 6).mpr
  exact ⟨U, a, haSurj, haEtale, hcomp⟩

/-- Smoothness of algebraic-space morphisms is fpqc local on the base. -/
@[stacks 0429]
instance smooth_isLocalAtTarget_fpqc (B : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) :
    (smoothMorphismProperty B S hS).IsLocalAtTarget
      (Topology.precoverage.{u, v} .fpqc B S hS) :=
  isLocalAtTarget_fpqc_of_affineDescent B S hS
    (smoothMorphismProperty B S hS) (smooth_finite_coproduct B S hS)
    (smooth_iff_affine_pullback B S hS) (smooth_of_affine_fpqc_pullback B S hS)

end AlgebraicGeometry.Space

end
