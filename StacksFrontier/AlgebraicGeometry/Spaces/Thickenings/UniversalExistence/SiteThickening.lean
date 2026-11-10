module

public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.UniversalExistence.FirstOrderClauseAndAffineSize
import all StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.UniversalExistence.FirstOrderClauseAndAffineSize

/-!
# Universal thickening existence: universal thickenings inside the site

Universal first order thickenings of morphisms of the big fppf site, read as algebraic spaces
through the Yoneda embedding, their lifting properties as morphisms of the site, and the étaleness
of the comparison between two universal thickenings of the site.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Spaces.UniversalThickening

open AlgebraicGeometry.Space

private lemma schemeChart_pullback_projection
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicGeometry.AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (U : AlgebraicGeometry.Space.SmallEtale B S hS X.1)
    (V : AlgebraicGeometry.Space.SmallEtale B S hS Y.1)
    (A : Over X) (C : Over Y)
    (hA : A = AlgebraicGeometry.Space.chartOver B S hS X U)
    (hC : C = AlgebraicGeometry.Space.chartOver B S hS Y V)
    (k : A.left ⟶ C.left) (hs : IsPullback k A.hom C.hom f) :
    ∃ p : (AlgebraicGeometry.Space.SmallEtale.toOver B S hS X.1).obj U ⟶
        (AlgebraicGeometry.Space.SmallEtale.toOver B S hS Y.1).obj V,
      HEq k.hom (yoneda.map p) ∧
      IsPullback (yoneda.map p) U.1.hom V.1.hom f.hom := by
  subst A C
  let p := yoneda.preimage k.hom
  have hp : yoneda.map p = k.hom := yoneda.map_preimage k.hom
  have h := AlgebraicGeometry.AlgebraicSpaces.isPullback_hom B S hS hs
  change IsPullback k.hom U.1.hom V.1.hom f.hom at h
  exact ⟨p, heq_of_eq hp.symm, hp.symm ▸ h⟩

private lemma smallBaseChange_projection_schemeMap
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicGeometry.AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom)
    (V : AlgebraicGeometry.Space.SmallEtale B S hS Y.1) :
    ∃ p : (AlgebraicGeometry.Space.SmallEtale.toOver B S hS X.1).obj
        ((AlgebraicGeometry.Space.smallBaseChange B S hS f hf).obj V) ⟶
        (AlgebraicGeometry.Space.SmallEtale.toOver B S hS Y.1).obj V,
      HEq ((AlgebraicGeometry.Space.smallBaseChange_projection B S hS f hf).app V).hom
        (yoneda.map p) ∧
      IsPullback (yoneda.map p)
        ((AlgebraicGeometry.Space.smallBaseChange B S hS f hf).obj V).1.hom V.1.hom f.hom :=
  schemeChart_pullback_projection B S hS f _ V _ _
    (AlgebraicGeometry.Space.comparisonFunctor_obj B S hS X _)
    (AlgebraicGeometry.Space.comparisonFunctor_obj B S hS Y V) _
    (AlgebraicGeometry.Space.smallBaseChange_isPullback B S hS f hf V)

private lemma isFirstOrderThickening_yoneda_range
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {T U : AlgebraicGeometry.BigFppfOver B S hS} (i : T ⟶ U)
    (hi : Stacks.Thickenings.IsFirstOrderThickening
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map i)) :
    AlgebraicGeometry.Space.IsFirstOrderThickening B S hS (AlgebraicGeometry.schemeSpace U)
      (Subfunctor.range (yoneda.map i)) :=
  AlgebraicGeometry.Space.isFirstOrderThickening_range_yoneda_map B S hS i ⟨hi.1, hi.2⟩

/-- A universal first-order thickening of objects of the site is one of the algebraic spaces
they represent. -/
private lemma universalThickening_yoneda_range
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Z Z' X : AlgebraicGeometry.BigFppfOver B S hS} (i : Z ⟶ Z') (p : Z' ⟶ X)
    (hu : Stacks.Thickenings.IsUniversalFirstOrderThickening
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (i ≫ p))
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map i)
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map p)) :
    AlgebraicGeometry.Space.IsUniversalFirstOrderThickening B S hS
      (Subfunctor.range (yoneda.map i)) (AlgebraicGeometry.schemeSpaceMap p) :=
  AlgebraicGeometry.Space.isUniversalFirstOrderThickening_range_yoneda_map B S hS i p hu

/-- A morphism of the site lies over the structure morphisms after applying the scheme functor. -/
private lemma toScheme_map_comp_hom
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {V U : AlgebraicGeometry.BigFppfOver B S hS} (q : V ⟶ U) :
    (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map q ≫ U.hom.hom = V.hom.hom :=
  congrArg (fun f => f.hom) q.w

/-- The inclusion of a universal thickening lies over the structure morphism of the source. -/
private lemma inclusion_comp_toBase_comp_hom
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {V U : AlgebraicGeometry.BigFppfOver B S hS} (q : V ⟶ U)
    (t : Stacks.Thickenings.UniversalFirstOrderThickening
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map q)) :
    t.inclusion ≫ (t.toBase ≫ U.hom.hom) = V.hom.hom := by
  rw [← Category.assoc, t.isUniversal.inclusion_toBase]
  exact toScheme_map_comp_hom B S hS q

private lemma exists_site_universalThickening
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {V U : AlgebraicGeometry.BigFppfOver B S hS} (q : V ⟶ U)
    (t : Stacks.Thickenings.UniversalFirstOrderThickening
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map q))
    (ht : B.Contains t.ambient) :
    ∃ (V' : AlgebraicGeometry.BigFppfOver B S hS) (i : V ⟶ V') (p : V' ⟶ U),
      i ≫ p = q ∧
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj V' = t.ambient ∧
      HEq ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map i) t.inclusion ∧
      HEq ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map p) t.toBase ∧
      Stacks.Thickenings.IsFirstOrderThickening
        ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map i) ∧
      Stacks.Thickenings.IsUniversalFirstOrderThickening
        ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map q)
        ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map i)
        ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map p) ∧
      AlgebraicGeometry.Space.IsUniversalFirstOrderThickening B S hS
        (Subfunctor.range (yoneda.map i)) (AlgebraicGeometry.schemeSpaceMap p) := by
  let F := AlgebraicGeometry.BigFppfOver.toScheme B S hS
  let V' : AlgebraicGeometry.BigFppfOver B S hS :=
    Over.mk (ObjectProperty.homMk (t.toBase ≫ U.hom.hom) : B.obj ht ⟶ B.obj hS)
  let i : V ⟶ V' := Over.homMk (ObjectProperty.homMk t.inclusion)
    (by apply ObjectProperty.hom_ext; exact inclusion_comp_toBase_comp_hom B S hS q t)
  let p : V' ⟶ U := Over.homMk (ObjectProperty.homMk t.toBase) rfl
  have hcomp : i ≫ p = q := F.map_injective t.isUniversal.inclusion_toBase
  have hu : Stacks.Thickenings.IsUniversalFirstOrderThickening
      (F.map (i ≫ p)) (F.map i) (F.map p) := by
    rw [hcomp]
    exact t.isUniversal
  exact ⟨V', i, p, hcomp, rfl, HEq.rfl, HEq.rfl, t.isUniversal.isFirstOrderThickening,
    t.isUniversal, universalThickening_yoneda_range B S hS i p hu⟩

/-- **`Stacks.Spaces.UniversalThickening.exists_site_universalThickening` with the scheme-level
universal property in the conclusion, and without the transport data.**

The lemma above returns the ambient scheme of `t` as an *equality* `F.obj V' = t.ambient`
together with two `HEq`s relating `F.map i` and `F.map p` to `t.inclusion` and `t.toBase`.  A
consumer wanting the scheme-level universal property at `V'` must therefore `subst` that
equality and strip the `HEq`s, and doing so inside a context that already holds a universal
property exhausts the heartbeat budget — see the implementation note on
`Stacks.Spaces.UniversalThickening.isUniversalFirstOrderThickening_of_iso` below.

The property is free, though: the proof above constructs it on the way to
`universalThickening_yoneda_range` and then drops it.  This states it, and drops the transport
data instead, which no consumer has needed.  It is a separate declaration rather than an extra
conjunct on the existing one because the existing one is on the base, and a base declaration's
statement stays as it is.

`i` and `p` are built from `t.inclusion` and `t.toBase`, so the two are definitionally `F.map i`
and `F.map p` and the universal property is `t.isUniversal` unchanged. -/
public lemma exists_site_universalThickening_of_universalProperty
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {V U : AlgebraicGeometry.BigFppfOver B S hS} (q : V ⟶ U)
    (t : Stacks.Thickenings.UniversalFirstOrderThickening
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map q))
    (ht : B.Contains t.ambient) :
    ∃ (V' : AlgebraicGeometry.BigFppfOver B S hS) (i : V ⟶ V') (p : V' ⟶ U),
      i ≫ p = q ∧
      Stacks.Thickenings.IsFirstOrderThickening
        ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map i) ∧
      Stacks.Thickenings.IsUniversalFirstOrderThickening
        ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map q)
        ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map i)
        ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map p) ∧
      AlgebraicGeometry.Space.IsUniversalFirstOrderThickening B S hS
        (Subfunctor.range (yoneda.map i)) (AlgebraicGeometry.schemeSpaceMap p) := by
  obtain ⟨V', i, p, hcomp, -, -, -, hi, hu, hy⟩ := exists_site_universalThickening B S hS q t ht
  exact ⟨V', i, p, hcomp, hi, hu, hy⟩

private lemma bridge_siteHom_of_schemeMap
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {V W : AlgebraicGeometry.BigFppfOver B S hS}
    (f : (AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj V ⟶
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj W)
    (hf : f ≫ W.hom.hom = V.hom.hom) :
    ∃ g : V ⟶ W,
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map g = f := by
  let g : V ⟶ W := Over.homMk (ObjectProperty.homMk f)
    (by apply ObjectProperty.hom_ext; exact hf)
  exact ⟨g, rfl⟩

private lemma bridge_site_lift_of_universalThickening
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {A A' R R' W : AlgebraicGeometry.BigFppfOver B S hS}
    (iA : A ⟶ A')
    (hiA : Stacks.Thickenings.IsFirstOrderThickening
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map iA))
    (f : A ⟶ R) (b : A' ⟶ W) (r : R ⟶ W)
    (iR : R ⟶ R') (pR : R' ⟶ W)
    (hR : Stacks.Thickenings.IsUniversalFirstOrderThickening
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map r)
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map iR)
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map pR))
    (hcompat : iA ≫ b = f ≫ r) :
    ∃! k : A' ⟶ R', iA ≫ k = f ≫ iR ∧ k ≫ pR = b := by
  let F := AlgebraicGeometry.BigFppfOver.toScheme B S hS
  have hc : F.map iA ≫ F.map b = F.map f ≫ F.map r := by
    simpa only [← Functor.map_comp] using congrArg F.map hcompat
  obtain ⟨k, hk, uniq⟩ := hR.existsUnique_lift
    (F.map iA) hiA (F.map f) (F.map b) hc
  have hOver : k ≫ R'.hom.hom = A'.hom.hom := by
    rw [← toScheme_map_comp_hom B S hS pR, ← Category.assoc, hk.2,
      toScheme_map_comp_hom B S hS b]
  obtain ⟨kSite, hkSite⟩ := bridge_siteHom_of_schemeMap B S hS k hOver
  refine ⟨kSite, ?_, ?_⟩
  · constructor
    · apply F.map_injective
      rw [Functor.map_comp, Functor.map_comp, hkSite]
      exact hk.1
    · apply F.map_injective
      rw [Functor.map_comp, hkSite]
      exact hk.2
  · intro l hl
    apply F.map_injective
    rw [hkSite]
    apply uniq
    constructor
    · simpa only [Functor.map_comp] using congrArg F.map hl.1
    · simpa only [Functor.map_comp] using congrArg F.map hl.2

private lemma bridge_site_endomorphism_id_of_universalThickening
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {V V' U : AlgebraicGeometry.BigFppfOver B S hS}
    (i : V ⟶ V') (q : V ⟶ U) (p : V' ⟶ U)
    (hi : Stacks.Thickenings.IsFirstOrderThickening
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map i))
    (hu : Stacks.Thickenings.IsUniversalFirstOrderThickening
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map q)
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map i)
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map p))
    (hcomp : i ≫ p = q) (f : V' ⟶ V')
    (hres : i ≫ f = i) (hbase : f ≫ p = p) : f = 𝟙 V' := by
  obtain ⟨k, _, uniq⟩ := bridge_site_lift_of_universalThickening
    B S hS i hi (𝟙 V) p q i p hu (by simpa using hcomp)
  have hf : f = k := uniq f ⟨by simpa using hres, hbase⟩
  have hid : (𝟙 V') = k := uniq (𝟙 V') ⟨by simp, by simp⟩
  exact hf.trans hid.symm

private lemma bridge_site_hom_ext_of_universalThickening
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {A A' V V' U : AlgebraicGeometry.BigFppfOver B S hS}
    (iA : A ⟶ A')
    (hiA : Stacks.Thickenings.IsFirstOrderThickening
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map iA))
    (f : A ⟶ V) (b : A' ⟶ U) (q : V ⟶ U)
    (iV : V ⟶ V') (pV : V' ⟶ U)
    (hV : Stacks.Thickenings.IsUniversalFirstOrderThickening
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map q)
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map iV)
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map pV))
    (hcompat : iA ≫ b = f ≫ q)
    (k₁ k₂ : A' ⟶ V')
    (h₁ : iA ≫ k₁ = f ≫ iV ∧ k₁ ≫ pV = b)
    (h₂ : iA ≫ k₂ = f ≫ iV ∧ k₂ ≫ pV = b) : k₁ = k₂ := by
  obtain ⟨k, _, uniq⟩ := bridge_site_lift_of_universalThickening
    B S hS iA hiA f b q iV pV hV hcompat
  exact (uniq k₁ h₁).trans (uniq k₂ h₂).symm

private lemma bridge_liftedRelation_siteMaps
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {V U R W : AlgebraicGeometry.BigFppfOver B S hS}
    (q : V ⟶ U) (r : R ⟶ W) (α β : W ⟶ U) (s₀ t₀ : R ⟶ V)
    (D : Stacks.Thickenings.UniversalFirstOrderThickening
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map q))
    (H : Stacks.Thickenings.UniversalFirstOrderThickening
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map r))
    (hD : B.Contains D.ambient) (hH : B.Contains H.ambient)
    (k : H.ambient ⟶ D.ambient ⨯ D.ambient)
    (hs : H.inclusion ≫ k ≫ Limits.prod.fst =
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map s₀ ≫ D.inclusion)
    (ht : H.inclusion ≫ k ≫ Limits.prod.snd =
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map t₀ ≫ D.inclusion)
    (hα : k ≫ Limits.prod.fst ≫ D.toBase =
      H.toBase ≫ (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map α)
    (hβ : k ≫ Limits.prod.snd ≫ D.toBase =
      H.toBase ≫ (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map β)
    (hαuniv : Stacks.Thickenings.IsUniversalFirstOrderThickening
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map r ≫
        (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map α)
      H.inclusion (H.toBase ≫ (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map α))
    (hβuniv : Stacks.Thickenings.IsUniversalFirstOrderThickening
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map r ≫
        (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map β)
      H.inclusion (H.toBase ≫ (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map β)) :
    ∃ (V' R' : AlgebraicGeometry.BigFppfOver B S hS)
      (iV : V ⟶ V') (pV : V' ⟶ U)
      (iR : R ⟶ R') (pR : R' ⟶ W) (s t : R' ⟶ V'),
      iV ≫ pV = q ∧ iR ≫ pR = r ∧
      iR ≫ s = s₀ ≫ iV ∧ iR ≫ t = t₀ ≫ iV ∧
      s ≫ pV = pR ≫ α ∧ t ≫ pV = pR ≫ β ∧
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj V' = D.ambient ∧
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj R' = H.ambient ∧
      HEq ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map iV) D.inclusion ∧
      HEq ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map iR) H.inclusion ∧
      HEq ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map pV) D.toBase ∧
      HEq ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map pR) H.toBase ∧
      Stacks.Thickenings.IsFirstOrderThickening
        ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map iV) ∧
      Stacks.Thickenings.IsFirstOrderThickening
        ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map iR) ∧
      Stacks.Thickenings.IsUniversalFirstOrderThickening
        ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map q)
        ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map iV)
        ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map pV) ∧
      Stacks.Thickenings.IsUniversalFirstOrderThickening
        ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map r)
        ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map iR)
        ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map pR) ∧
      AlgebraicGeometry.Space.IsUniversalFirstOrderThickening B S hS
        (Subfunctor.range (yoneda.map iV)) (AlgebraicGeometry.schemeSpaceMap pV) ∧
      AlgebraicGeometry.Space.IsUniversalFirstOrderThickening B S hS
        (Subfunctor.range (yoneda.map iR)) (AlgebraicGeometry.schemeSpaceMap pR) ∧
      AlgebraicGeometry.Space.IsUniversalFirstOrderThickening B S hS
        (Subfunctor.range (yoneda.map iR))
        (AlgebraicGeometry.schemeSpaceMap (pR ≫ α)) ∧
      AlgebraicGeometry.Space.IsUniversalFirstOrderThickening B S hS
        (Subfunctor.range (yoneda.map iR))
        (AlgebraicGeometry.schemeSpaceMap (pR ≫ β)) ∧
      HEq ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map s)
        (k ≫ Limits.prod.fst) ∧
      HEq ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map t)
        (k ≫ Limits.prod.snd) := by
  let V' : AlgebraicGeometry.BigFppfOver B S hS :=
    Over.mk (ObjectProperty.homMk (D.toBase ≫ U.hom.hom) : B.obj hD ⟶ B.obj hS)
  let R' : AlgebraicGeometry.BigFppfOver B S hS :=
    Over.mk (ObjectProperty.homMk (H.toBase ≫ W.hom.hom) : B.obj hH ⟶ B.obj hS)
  let iV : V ⟶ V' := Over.homMk (ObjectProperty.homMk D.inclusion)
    (by apply ObjectProperty.hom_ext; exact inclusion_comp_toBase_comp_hom B S hS q D)
  let pV : V' ⟶ U := Over.homMk (ObjectProperty.homMk D.toBase) rfl
  let iR : R ⟶ R' := Over.homMk (ObjectProperty.homMk H.inclusion)
    (by apply ObjectProperty.hom_ext; exact inclusion_comp_toBase_comp_hom B S hS r H)
  let pR : R' ⟶ W := Over.homMk (ObjectProperty.homMk H.toBase) rfl
  have hcompV : iV ≫ pV = q := by
    apply (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map_injective
    exact D.isUniversal.inclusion_toBase
  have hcompR : iR ≫ pR = r := by
    apply (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map_injective
    exact H.isUniversal.inclusion_toBase
  have huV : AlgebraicGeometry.Space.IsUniversalFirstOrderThickening B S hS
      (Subfunctor.range (yoneda.map iV)) (AlgebraicGeometry.schemeSpaceMap pV) := by
    apply universalThickening_yoneda_range B S hS iV pV
    rw [hcompV]
    exact D.isUniversal
  have huR : AlgebraicGeometry.Space.IsUniversalFirstOrderThickening B S hS
      (Subfunctor.range (yoneda.map iR)) (AlgebraicGeometry.schemeSpaceMap pR) := by
    apply universalThickening_yoneda_range B S hS iR pR
    rw [hcompR]
    exact H.isUniversal
  have huRγ : ∀ γ : W ⟶ U, Stacks.Thickenings.IsUniversalFirstOrderThickening
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map r ≫
        (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map γ)
      H.inclusion (H.toBase ≫ (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map γ) →
      AlgebraicGeometry.Space.IsUniversalFirstOrderThickening B S hS
        (Subfunctor.range (yoneda.map iR)) (AlgebraicGeometry.schemeSpaceMap (pR ≫ γ)) := by
    intro γ hγ
    apply universalThickening_yoneda_range B S hS iR (pR ≫ γ)
    rw [← Category.assoc, hcompR]
    change Stacks.Thickenings.IsUniversalFirstOrderThickening
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (r ≫ γ))
      H.inclusion (H.toBase ≫ (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map γ)
    simpa only [Functor.map_comp] using hγ
  let mk (π : D.ambient ⨯ D.ambient ⟶ D.ambient) (γ : W ⟶ U)
      (h : k ≫ π ≫ D.toBase = H.toBase ≫ (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map γ) :
      R' ⟶ V' := Over.homMk (ObjectProperty.homMk (k ≫ π)) (by
    apply ObjectProperty.hom_ext
    change (k ≫ π) ≫ (D.toBase ≫ U.hom.hom) = H.toBase ≫ W.hom.hom
    rw [← toScheme_map_comp_hom B S hS γ, ← Category.assoc H.toBase, ← h]
    simp only [Category.assoc])
  have hmk : ∀ (π : D.ambient ⨯ D.ambient ⟶ D.ambient) (γ : W ⟶ U) (x : R ⟶ V)
      (h : k ≫ π ≫ D.toBase = H.toBase ≫ (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map γ)
      (hx : H.inclusion ≫ k ≫ π =
        (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map x ≫ D.inclusion),
      iR ≫ mk π γ h = x ≫ iV ∧ mk π γ h ≫ pV = pR ≫ γ := fun π γ x h hx =>
    ⟨(AlgebraicGeometry.BigFppfOver.toScheme B S hS).map_injective (by
      change H.inclusion ≫ (k ≫ π) =
        (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map x ≫ D.inclusion
      simpa only [Category.assoc] using hx),
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map_injective h⟩
  exact ⟨V', R', iV, pV, iR, pR, mk _ α hα, mk _ β hβ,
    hcompV, hcompR, (hmk _ _ _ hα hs).1, (hmk _ _ _ hβ ht).1,
    (hmk _ _ _ hα hs).2, (hmk _ _ _ hβ ht).2,
    rfl, rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl,
    D.isUniversal.isFirstOrderThickening, H.isUniversal.isFirstOrderThickening,
    D.isUniversal, H.isUniversal,
    huV, huR, huRγ α hαuniv, huRγ β hβuniv, HEq.rfl, HEq.rfl⟩

private lemma etale_lift_of_universalThickenings
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y' Z' : AlgebraicGeometry.AlgebraicSpaces B S hS}
    (Y : Subfunctor Y'.1) (Z : Subfunctor Z'.1)
    (p : Y' ⟶ X) (q : Z' ⟶ X)
    (hY : AlgebraicGeometry.Space.IsUniversalFirstOrderThickening B S hS Y p)
    (hZ : AlgebraicGeometry.Space.IsUniversalFirstOrderThickening B S hS Z q)
    (a : Z.toFunctor ⟶ Y.toFunctor) (ha : AlgebraicGeometry.Space.IsEtale B S hS a)
    (k : Z' ⟶ Y') (hk : k ≫ p = q)
    (hki : Z.ι ≫ k.hom = a ≫ Y.ι) :
    AlgebraicGeometry.Space.IsEtale B S hS k.hom ∧ IsPullback a Z.ι Y.ι k.hom := by
  let Z₀ : AlgebraicGeometry.AlgebraicSpaces B S hS := ⟨Z.toFunctor, hZ.firstOrder.choose.1.1⟩
  obtain ⟨W', g, j, hg, hsq⟩ :=
    etaleExtendsAlongFirstOrderThickening B S hS (Z := Z₀) Y hY.firstOrder a ha
  have : Mono j := hsq.mono_snd_of_mono
  let W := Subfunctor.range j
  let e : Z.toFunctor ≅ W.toFunctor := asIso (Subfunctor.toRange j)
  let b := e.inv ≫ a
  have hbsq : IsPullback b W.ι Y.ι g.hom := by
    apply hsq.of_iso e (Iso.refl _) (Iso.refl _) (Iso.refl _)
    · simp [b]
    · simpa only [e, asIso_hom, Iso.refl_hom, Category.comp_id] using
        (Subfunctor.toRange_ι j).symm
    · simp
    · simp
  have hb : e.hom ≫ b = a := by simp [b]
  have hki' : Z.ι ≫ k.hom = e.hom ≫ b ≫ Y.ι := by
    rw [← Category.assoc, hb]
    exact hki
  obtain ⟨het, hpb⟩ := isEtale_of_universalThickening_comparison B S hS
    Y Z W p q hY hZ g hg b hbsq e k hk hki'
  exact ⟨het, by simpa only [hb] using hpb⟩

private lemma bridge_etale_of_universalSiteThickenings
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {V R V' R' U : AlgebraicGeometry.BigFppfOver B S hS}
    (iV : V ⟶ V') (iR : R ⟶ R')
    (pV : V' ⟶ U) (pR : R' ⟶ U)
    (hiV : Stacks.Thickenings.IsFirstOrderThickening
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map iV))
    (hiR : Stacks.Thickenings.IsFirstOrderThickening
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map iR))
    (hV : AlgebraicGeometry.Space.IsUniversalFirstOrderThickening B S hS
      (Subfunctor.range (yoneda.map iV)) (AlgebraicGeometry.schemeSpaceMap pV))
    (hR : AlgebraicGeometry.Space.IsUniversalFirstOrderThickening B S hS
      (Subfunctor.range (yoneda.map iR)) (AlgebraicGeometry.schemeSpaceMap pR))
    (f : R ⟶ V) (f' : R' ⟶ V')
    (hf : Etale ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map f))
    (hcomm : iR ≫ f' = f ≫ iV) (hbase : f' ≫ pV = pR) :
    Etale ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map f') ∧
      IsPullback (yoneda.map f) (yoneda.map iR)
        (yoneda.map iV) (yoneda.map f') := by
  let F := AlgebraicGeometry.BigFppfOver.toScheme B S hS
  let P := MorphismProperty.inverseImage
    (@Etale.{u} : MorphismProperty Scheme.{u}) F
  let Z := Subfunctor.range (yoneda.map iR)
  let Y := Subfunctor.range (yoneda.map iV)
  have : IsClosedImmersion (F.map iR) := hiR.1
  have : IsClosedImmersion (F.map iV) := hiV.1
  have : Mono iR := F.mono_of_mono_map (inferInstance : Mono (F.map iR))
  have : Mono iV := F.mono_of_mono_map (inferInstance : Mono (F.map iV))
  have : Mono (yoneda.map iR) := (NatTrans.mono_iff_mono_app _).mpr fun T =>
    (ConcreteCategory.mono_iff_injective_of_preservesPullback _).mpr fun a b hab =>
      (cancel_mono iR).mp hab
  have : Mono (yoneda.map iV) := (NatTrans.mono_iff_mono_app _).mpr fun T =>
    (ConcreteCategory.mono_iff_injective_of_preservesPullback _).mpr fun a b hab =>
      (cancel_mono iV).mp hab
  let eR : yoneda.obj R ≅ Z.toFunctor := asIso (Subfunctor.toRange (yoneda.map iR))
  let eV : yoneda.obj V ≅ Y.toFunctor := asIso (Subfunctor.toRange (yoneda.map iV))
  let a : Z.toFunctor ⟶ Y.toFunctor := eR.inv ≫ yoneda.map f ≫ eV.hom
  let : MorphismProperty.IsStableUnderBaseChange
      (@Etale.{u} : MorphismProperty Scheme.{u}) :=
    Etale.etale_isStableUnderBaseChange
  let : MorphismProperty.RespectsIso
      (@Etale.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  let : P.RespectsIso :=
    MorphismProperty.RespectsIso.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) F
  have hpres : P.presheaf (yoneda.map f) := by
    apply MorphismProperty.relative.of_exists
    intro T g
    obtain ⟨g₀, rfl⟩ := yoneda.map_surjective g
    refine ⟨Limits.pullback f g₀, yoneda.map (Limits.pullback.fst f g₀),
      Limits.pullback.snd f g₀, (IsPullback.of_hasPullback f g₀).map yoneda, ?_⟩
    change Etale (F.map (Limits.pullback.snd f g₀))
    exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
      ((IsPullback.of_hasPullback f g₀).map F) hf
  have hEtf : AlgebraicGeometry.Space.IsEtale B S hS (yoneda.map f) := by
    intro T φ hφ
    let : P.IsStableUnderComposition :=
      ⟨fun f g hf hg => by
        change Etale (F.map (f ≫ g))
        rw [Functor.map_comp]
        let : Etale (F.map f) := hf
        let : Etale (F.map g) := hg
        infer_instance⟩
    exact MorphismProperty.comp_mem P.presheaf φ (yoneda.map f) hφ hpres
  have ha : AlgebraicGeometry.Space.IsEtale B S hS a := by
    intro T φ hφ
    have hφ' : P.presheaf (φ ≫ eR.inv) :=
      (P.presheaf.cancel_right_of_respectsIso φ eR.inv).mpr hφ
    have hmid := hEtf T (φ ≫ eR.inv) hφ'
    have hlast : P.presheaf ((φ ≫ eR.inv ≫ yoneda.map f) ≫ eV.hom) :=
      (P.presheaf.cancel_right_of_respectsIso _ eV.hom).mpr hmid
    simpa only [a, Category.assoc] using hlast
  have hZfac : Z.ι = eR.inv ≫ yoneda.map iR := by
    calc
      Z.ι = eR.inv ≫ (eR.hom ≫ Z.ι) := by simp
      _ = eR.inv ≫ yoneda.map iR := by
        rw [show eR.hom ≫ Z.ι = yoneda.map iR from
          Subfunctor.toRange_ι (yoneda.map iR)]
  have hki : Z.ι ≫ yoneda.map f' = a ≫ Y.ι := by
    calc
      Z.ι ≫ yoneda.map f' =
          eR.inv ≫ yoneda.map (iR ≫ f') := by
            rw [hZfac, Functor.map_comp]
            simp only [Category.assoc]
      _ = eR.inv ≫ yoneda.map (f ≫ iV) := by rw [hcomm]
      _ = a ≫ Y.ι := by
        simp only [Functor.map_comp, a, Category.assoc]
        rw [← Subfunctor.toRange_ι (yoneda.map iV)]
        rfl
  have hk : AlgebraicGeometry.schemeSpaceMap f' ≫
      AlgebraicGeometry.schemeSpaceMap pV = AlgebraicGeometry.schemeSpaceMap pR := by
    apply ObjectProperty.hom_ext
    change yoneda.map f' ≫ yoneda.map pV = yoneda.map pR
    simpa only [← Functor.map_comp] using congrArg yoneda.map hbase
  obtain ⟨het, hpb⟩ := etale_lift_of_universalThickenings B S hS
    Y Z (AlgebraicGeometry.schemeSpaceMap pV) (AlgebraicGeometry.schemeSpaceMap pR)
    hV hR a ha (AlgebraicGeometry.schemeSpaceMap f') hk hki
  have hid : P.presheaf (𝟙 (yoneda.obj R')) :=
    AlgebraicGeometry.presheaf_id_of_iso B S hS _ (fun _ _ g hg => by
      have : IsIso g := hg
      change Etale ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map g)
      infer_instance) R'
  have het' : P.presheaf (yoneda.map f') := by
    have h := het R' (𝟙 _) hid
    change P.presheaf (𝟙 (yoneda.obj R') ≫ yoneda.map f') at h
    simpa only [Category.id_comp] using h
  have hpb' : IsPullback (yoneda.map f) (yoneda.map iR)
      (yoneda.map iV) (yoneda.map f') := by
    apply hpb.of_iso' eR eV (Iso.refl _) (Iso.refl _)
    · change (eR.hom ≫ eR.inv) ≫ (yoneda.map f ≫ eV.hom) =
        yoneda.map f ≫ eV.hom
      rw [eR.hom_inv_id, Category.id_comp]
    · exact Subfunctor.toRange_ι (yoneda.map iR)
    · exact Subfunctor.toRange_ι (yoneda.map iV)
    · change yoneda.map f' = yoneda.map f' ≫ 𝟙 _
      simp
  exact ⟨MorphismProperty.of_relative_map (F := yoneda) (P := P) het', hpb'⟩

end Stacks.Spaces.UniversalThickening

end
