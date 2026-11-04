module

public import StacksFrontier.AlgebraicGeometry.EssSurj.IsoDescentCompat
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.MorphismDescentGlue
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.ReflectIso
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedLimitDescentEq
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Descent of vertical morphisms for the stack of polarized proper schemes

Over the limit of a cofiltered inverse system of affine schemes, a vertical morphism between the
base changes of two polarized families defined at a finite stage already comes from a morphism at
a later stage. This is the descent condition of Stacks 07XL which makes the comparison functor
`colim 𝒫olarized_{Tᵢ} ⥤ 𝒫olarized_T` full.

## Main results

* `AlgebraicGeometry.exists_stage_comparison_morphism`: **Stacks 01ZM (2)** together with
  **Stacks 081E**, for two finitely presented morphisms over a stage: an identification of their
  base changes to the limit comes from a morphism over a later stage, cartesian over the transition
  morphism.
* `AlgebraicGeometry.exists_stage_isIso_pullback_map`: **Stacks 01ZR (2)** together with the
  reflection of isomorphisms of Stacks 01ZR (3), descending an isomorphism of pullbacks of
  finitely presented modules from the limit to a stage.
* `AlgebraicGeometry.exists_stage_comparison`: a morphism of total spaces and an isomorphism of
  pullbacks of finitely presented modules over it descend together to one stage.
* `AlgebraicGeometry.descentHom_polarizedSliceProjection`: the condition
  `Deformation.Artin.DescentHom` for `𝒫olarized`.
* `AlgebraicGeometry.full_colimitComparison_polarized`: the comparison functor
  `colim 𝒫olarized_{Tᵢ} ⥤ 𝒫olarized_T` of Stacks 07XL is full.

## References

* [Stacks Project, Tag 0D43](https://stacks.math.columbia.edu/tag/0D43)
* [Stacks Project, Tag 07XL](https://stacks.math.columbia.edu/tag/07XL)
* [Stacks Project, Tag 01ZM](https://stacks.math.columbia.edu/tag/01ZM)
* [Stacks Project, Tag 01ZR](https://stacks.math.columbia.edu/tag/01ZR)
* [Stacks Project, Tag 081E](https://stacks.math.columbia.edu/tag/081E)
* [Stacks Project, Tag 003S](https://stacks.math.columbia.edu/tag/003S)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

open Stacks.AlgebraicGeometry.ModuleLimits (canHom canIso canStep canHom_comp
  canonical_eq_of_further_step canHom_rfl isFinitePresentation_pullback isIso_canHom
  canIso_hom
  exists_map_of_pullback_canonical_of_isLimit' exists_isIso_pullback_map_of_isLimit)

universe u

namespace AlgebraicGeometry

/-! ### Two morphisms of polarized families with the same base map and total map -/

namespace PolarizedFamily

variable {B : BigFppfSite.{u}}

/-- Two morphisms of polarized families agree as soon as their base maps, their maps of total
spaces and the underlying morphisms of their comparisons of polarizations agree. -/
theorem Hom.ext' {X Y : PolarizedFamily B} {f g : X ⟶ Y} (hbase : f.baseMap = g.baseMap)
    (htotal : f.totalMap = g.totalMap)
    (hline : (Hom.lineBundleIso f).hom ≍ (Hom.lineBundleIso g).hom) : f = g := by
  obtain ⟨fb, ft, fc, fi⟩ := f
  obtain ⟨gb, gt, gc, gi⟩ := g
  obtain rfl : fb = gb := hbase
  obtain rfl : ft = gt := htotal
  obtain rfl : fc = gc := rfl
  exact Hom.ext rfl rfl (heq_of_eq (Iso.ext (eq_of_heq hline)))

end PolarizedFamily

/-- The canonical identification of an iterated pullback of modules with the pullback along the
composite, written with `CategoryTheory.eqToHom` for the transport. -/
private theorem canHom_eq_eqToHom {W Z X : Scheme.{u}} (q : W ⟶ Z) (g : Z ⟶ X) (pi : W ⟶ X)
    (hpi : q ≫ g = pi) (F : X.Modules) :
    canHom q g pi hpi F = (Scheme.Modules.pullbackComp q g).hom.app F ≫
      eqToHom (congrArg (fun k => (Scheme.Modules.pullback k).obj F) hpi) := by
  subst hpi
  rw [canHom_rfl]
  simp

/-- The inverse of an isomorphism cancels the isomorphism appearing to its right. -/
private theorem inv_comp_hom_comp {C : Type*} [Category C] {P Q R : C} (e : P ≅ Q)
    (t : Q ⟶ R) : e.inv ≫ e.hom ≫ t = t := by
  rw [← Category.assoc, e.inv_hom_id, Category.id_comp]

/-- An isomorphism cancels its inverse appearing to its right. -/
private theorem hom_comp_inv_comp {C : Type*} [Category C] {P Q R : C} (e : P ≅ Q)
    (t : P ⟶ R) : e.hom ≫ e.inv ≫ t = t := by
  rw [← Category.assoc, e.hom_inv_id, Category.id_comp]

/-- An endomorphism which is the identity disappears from a composite after any functor. -/
private theorem functor_map_comp_eq_of_eq_id {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {A : C} {u : A ⟶ A} (hu : u = 𝟙 A) {R : D} (t : F.obj A ⟶ R) : F.map u ≫ t = t := by
  rw [hu, F.map_id, Category.id_comp]

/-- Cancel an isomorphism occurring inverted on the right of one side of an equation of
composites. -/
private theorem comp_eq_of_comp_eq_comp_inv {C : Type*} [Category C] {P Q R S T : C} {A : P ⟶ Q}
    {c₁ : Q ⟶ R} {c₂ : P ⟶ S} {m : S ⟶ T} {L : Q ⟶ T} (e : R ≅ T) (hL : L = c₁ ≫ e.hom)
    (h : A ≫ c₁ = c₂ ≫ m ≫ e.inv) : A ≫ L = c₂ ≫ m := by
  rw [hL, ← Category.assoc, h, Category.assoc, Category.assoc, e.inv_hom_id, Category.comp_id]

/-! ### The transition morphisms of a system of base changes -/

/-- The transition morphism of the base changes over a stage commutes with the second
projections. -/
private theorem pullbackDiagram_map_comp_snd {I : Type u} [Category.{u} I] (DS : I ⥤ Scheme.{u})
    (i : I) {T : Scheme.{u}} (f : T ⟶ DS.obj i) {j k : Over i} (ee : j ⟶ k) :
    (pullbackDiagram DS i f).map ee ≫ pullback.snd (DS.map k.hom) f =
      pullback.snd (DS.map j.hom) f := by
  rw [pullbackDiagram_map]
  exact pullback.lift_snd _ _ _

/-- The images of a morphism over `i` and of its target structure morphism compose to the image of
the source structure morphism. -/
private theorem map_left_comp_map_hom {I : Type u} [Category.{u} I] (DS : I ⥤ Scheme.{u}) {i : I}
    {j k : Over i} (ee : j ⟶ k) : DS.map ee.left ≫ DS.map k.hom = DS.map j.hom := by
  rw [← DS.map_comp, Over.w ee]

/-- The transition morphism of the inverse system of base changes of a scheme over a stage is
itself a base change: the square it forms with the first projections over the transition morphism
of the ambient system is cartesian. -/
@[sga "1 XIII 1.0" "partial"]
theorem isPullback_pullbackDiagram_map {I : Type u} [Category.{u} I] (DS : I ⥤ Scheme.{u})
    (i : I) {T : Scheme.{u}} (f : T ⟶ DS.obj i) {j k : Over i} (ee : j ⟶ k) :
    IsPullback ((pullbackDiagram DS i f).map ee) (pullback.fst (DS.map j.hom) f)
      (pullback.fst (DS.map k.hom) f) (DS.map ee.left) := by
  have hfst : (pullbackDiagram DS i f).map ee ≫ pullback.fst (DS.map k.hom) f =
      pullback.fst (DS.map j.hom) f ≫ DS.map ee.left := by
    rw [pullbackDiagram_map]; exact pullback.lift_fst _ _ _
  refine IsPullback.of_right ?_ hfst (IsPullback.of_hasPullback (DS.map k.hom) f).flip
  rw [pullbackDiagram_map_comp_snd, map_left_comp_map_hom]
  exact (IsPullback.of_hasPullback (DS.map j.hom) f).flip

/-! ### Descending the comparison of total spaces -/

/-- **Stacks 01ZM (2) and 081E for two morphisms over a stage of a cofiltered system of affine
schemes.** If the base changes to the limit of two finitely presented morphisms over a stage are
identified, compatibly with their projections to the limit, then over some later stage there is a
morphism from the base change of the first to the second scheme whose square with the transition
morphism is cartesian, and which recovers the given identification over the limit. -/
theorem exists_stage_comparison_morphism {I : Type u} [Category.{u} I] [IsCofiltered I]
    (DS : I ⥤ Scheme.{u}) [∀ j : I, IsAffine (DS.obj j)] (cS : Cone DS) (hcS : IsLimit cS)
    (i : I) {Xi Yi XT : Scheme.{u}} (fi : Xi ⟶ DS.obj i) (gi : Yi ⟶ DS.obj i)
    (hfi : FinitePresentation fi) (hgi : FinitePresentation gi)
    {b : XT ⟶ cS.pt} {dt : XT ⟶ Xi} {gt : XT ⟶ Yi}
    (hd : IsPullback dt b fi (cS.π.app i)) (hg : IsPullback gt b gi (cS.π.app i)) :
    ∃ (k : I) (s : k ⟶ i) (cc : pullback (DS.map s) fi ⟶ Yi),
      IsPullback cc (pullback.fst (DS.map s) fi) gi (DS.map s) ∧
        ∀ u : XT ⟶ pullback (DS.map s) fi,
          u ≫ pullback.fst (DS.map s) fi = b ≫ cS.π.app k →
          u ≫ pullback.snd (DS.map s) fi = dt → u ≫ cc = gt := by
  have hdb : hd.isoPullback.inv ≫ b = pullback.snd fi (cS.π.app i) :=
    (Iso.inv_comp_eq hd.isoPullback).2 hd.isoPullback_hom_snd.symm
  have hsnd : (hd.isoPullback.symm ≪≫ hg.isoPullback).hom ≫
      pullback.snd gi (cS.π.app i) = pullback.snd fi (cS.π.app i) := by
    rw [Iso.trans_hom, Iso.symm_hom, Category.assoc, hg.isoPullback_hom_snd, hdb]
  obtain ⟨k, s, χ, α, β, hα, hβ, hcomm⟩ :=
    exists_iso_after_baseChange_compat DS cS hcS i (Over.mk fi) (Over.mk gi) hfi hgi
      (Over.isoMk (hd.isoPullback.symm ≪≫ hg.isoPullback) hsnd)
  have hχiso : IsIso χ.hom.left := by
    have h := (Over.forget (DS.obj k)).map_isIso χ.hom
    rwa [Over.forget_map] at h
  refine ⟨k, s, ((pullbackSymmetry (DS.map s) fi).hom ≫ χ.hom.left) ≫
    pullback.fst gi (DS.map s), ?_, ?_⟩
  · have hχw : χ.hom.left ≫ pullback.snd gi (DS.map s) = pullback.snd fi (DS.map s) :=
      Over.w χ.hom
    have hw : ((pullbackSymmetry (DS.map s) fi).hom ≫ χ.hom.left) ≫
        pullback.snd gi (DS.map s) = pullback.fst (DS.map s) fi ≫ 𝟙 (DS.obj k) := by
      rw [Category.assoc, hχw, pullbackSymmetry_hom_comp_snd, Category.comp_id]
    have h2 := (IsPullback.of_horiz_isIso ⟨hw⟩).paste_horiz
      (IsPullback.of_hasPullback gi (DS.map s))
    rwa [Category.id_comp] at h2
  · intro u hu1 hu2
    have hαinv : (hd.isoPullback.hom ≫ α.inv.left) ≫ α.hom.left = hd.isoPullback.hom := by
      rw [Category.assoc, ← Over.comp_left, α.inv_hom_id, Over.id_left]
      exact Category.comp_id _
    have hα' : pullback.fst ((Over.pullback (DS.map s)).obj (Over.mk fi)).hom (cS.π.app k) ≫
        pullback.fst fi (DS.map s) = α.hom.left ≫ pullback.fst fi (cS.π.app i) := hα.symm
    have hβ' : pullback.fst ((Over.pullback (DS.map s)).obj (Over.mk gi)).hom (cS.π.app k) ≫
        pullback.fst gi (DS.map s) = β.hom.left ≫ pullback.fst gi (cS.π.app i) := hβ.symm
    have hmapfst : ((Over.pullback (cS.π.app k)).map χ.hom).left ≫
        pullback.fst ((Over.pullback (DS.map s)).obj (Over.mk gi)).hom (cS.π.app k) =
        pullback.fst ((Over.pullback (DS.map s)).obj (Over.mk fi)).hom (cS.π.app k) ≫
          χ.hom.left := Stacks.GenericFlatness.overPullback_map_left_fst (cS.π.app k) χ.hom
    have hcommleft : α.hom.left ≫ hd.isoPullback.inv ≫ hg.isoPullback.hom =
        ((Over.pullback (cS.π.app k)).map χ.hom).left ≫ β.hom.left :=
      congrArg Over.Hom.left hcomm
    have hcond : pullback.fst ((Over.pullback (DS.map s)).obj (Over.mk fi)).hom (cS.π.app k) ≫
          pullback.snd fi (DS.map s) =
        pullback.snd ((Over.pullback (DS.map s)).obj (Over.mk fi)).hom (cS.π.app k) ≫
          cS.π.app k := pullback.condition
    have hvsnd : (hd.isoPullback.hom ≫ α.inv.left) ≫
        pullback.snd ((Over.pullback (DS.map s)).obj (Over.mk fi)).hom (cS.π.app k) = b := by
      have h : α.inv.left ≫
          pullback.snd ((Over.pullback (DS.map s)).obj (Over.mk fi)).hom (cS.π.app k) =
          pullback.snd fi (cS.π.app i) := Over.w α.inv
      rw [Category.assoc, h]
      exact hd.isoPullback_hom_snd
    have hu : u ≫ (pullbackSymmetry (DS.map s) fi).hom =
        (hd.isoPullback.hom ≫ α.inv.left) ≫
          pullback.fst ((Over.pullback (DS.map s)).obj (Over.mk fi)).hom (cS.π.app k) := by
      refine pullback.hom_ext (f := fi) (g := DS.map s) ?_ ?_
      · rw [Category.assoc, pullbackSymmetry_hom_comp_fst, hu2, Category.assoc, hα',
          ← Category.assoc, hαinv]
        exact hd.isoPullback_hom_fst.symm
      · rw [Category.assoc, pullbackSymmetry_hom_comp_snd, hu1, Category.assoc, hcond,
          ← Category.assoc, hvsnd]
    calc u ≫ (((pullbackSymmetry (DS.map s) fi).hom ≫ χ.hom.left) ≫
          pullback.fst gi (DS.map s))
        = (u ≫ (pullbackSymmetry (DS.map s) fi).hom) ≫
            χ.hom.left ≫ pullback.fst gi (DS.map s) := by simp only [Category.assoc]
      _ = (hd.isoPullback.hom ≫ α.inv.left) ≫
            (pullback.fst ((Over.pullback (DS.map s)).obj (Over.mk fi)).hom (cS.π.app k) ≫
              χ.hom.left) ≫ pullback.fst gi (DS.map s) := by
            rw [hu]; simp only [Category.assoc]
      _ = (hd.isoPullback.hom ≫ α.inv.left) ≫
            ((Over.pullback (cS.π.app k)).map χ.hom).left ≫
              pullback.fst ((Over.pullback (DS.map s)).obj (Over.mk gi)).hom (cS.π.app k) ≫
                pullback.fst gi (DS.map s) := by
            rw [← hmapfst]; simp only [Category.assoc]
      _ = (hd.isoPullback.hom ≫ α.inv.left) ≫
            ((Over.pullback (cS.π.app k)).map χ.hom).left ≫
              β.hom.left ≫ pullback.fst gi (cS.π.app i) := by rw [hβ']
      _ = ((hd.isoPullback.hom ≫ α.inv.left) ≫ α.hom.left) ≫
            hd.isoPullback.inv ≫ hg.isoPullback.hom ≫
              pullback.fst gi (cS.π.app i) := by
            simp only [Category.assoc]
            rw [← Category.assoc (Over.Hom.left ((Over.pullback (cS.π.app k)).map χ.hom)),
              ← hcommleft]
            simp only [Category.assoc]
      _ = gt := by
            rw [hαinv, Iso.hom_inv_id_assoc]
            exact hg.isoPullback_hom_fst

/-! ### Descending the comparison of polarizations -/

/-- **Stacks 01ZR (2) together with the reflection of isomorphisms of Stacks 01ZR (3).** An
isomorphism between the pullbacks to the limit of two finitely presented modules at a stage of a
cofiltered inverse system of quasi-compact quasi-separated schemes with affine transition
morphisms is, through the canonical identifications, the pullback of an isomorphism at a later
stage. -/
theorem exists_stage_isIso_pullback_map {J : Type u} [Category.{u} J] [IsCofiltered J]
    (G : J ⥤ Scheme.{u}) [∀ {a b : J} (g : a ⟶ b), IsAffineHom (G.map g)]
    (cG : Cone G) (hcG : IsLimit cG) [∀ a : J, CompactSpace (G.obj a)]
    [∀ a : J, QuasiSeparatedSpace (G.obj a)] (j₀ : J)
    (A Bm : (G.obj j₀).Modules) (hA : A.IsFinitePresentation) (hB : Bm.IsFinitePresentation)
    (N : (Scheme.Modules.pullback (X := cG.pt) (cG.π.app j₀)).obj A ≅
      (Scheme.Modules.pullback (X := cG.pt) (cG.π.app j₀)).obj Bm) :
    ∃ (j : J) (ee : j ⟶ j₀)
      (mm : (Scheme.Modules.pullback (G.map ee)).obj A ≅
        (Scheme.Modules.pullback (G.map ee)).obj Bm),
      (Scheme.Modules.pullback (X := cG.pt) (cG.π.app j)).map mm.hom ≫
          canHom (W := cG.pt) (cG.π.app j) (G.map ee) (cG.π.app j₀) (cG.w ee) Bm =
        canHom (W := cG.pt) (cG.π.app j) (G.map ee) (cG.π.app j₀) (cG.w ee) A ≫ N.hom := by
  obtain ⟨j₁, e₁, m₁, h₁⟩ :=
    exists_map_of_pullback_canonical_of_isLimit' G cG hcG j₀ A Bm N.hom
  have hA₁ : ((Scheme.Modules.pullback (G.map e₁)).obj A).IsFinitePresentation :=
    isFinitePresentation_pullback _ A
  have hB₁ : ((Scheme.Modules.pullback (G.map e₁)).obj Bm).IsFinitePresentation :=
    isFinitePresentation_pullback _ Bm
  have hiso : IsIso ((Scheme.Modules.pullback (cG.π.app j₁)).map m₁) := by
    have he : (Scheme.Modules.pullback (cG.π.app j₁)).map m₁ =
        canHom (cG.π.app j₁) (G.map e₁) (cG.π.app j₀) (cG.w e₁) A ≫ N.hom ≫
          inv (canHom (cG.π.app j₁) (G.map e₁) (cG.π.app j₀) (cG.w e₁) Bm) := by
      rw [← Category.assoc, ← h₁, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
    rw [he]
    infer_instance
  obtain ⟨j₂, e₂, h₂⟩ := exists_isIso_pullback_map_of_isLimit G cG hcG j₁
    ((Scheme.Modules.pullback (G.map e₁)).obj A)
    ((Scheme.Modules.pullback (G.map e₁)).obj Bm) m₁ hiso
  refine ⟨j₂, e₂ ≫ e₁,
    (canIso (G.map e₂) (G.map e₁) (G.map (e₂ ≫ e₁)) (G.map_comp e₂ e₁).symm A).symm ≪≫
      asIso ((Scheme.Modules.pullback (G.map e₂)).map m₁) ≪≫
        canIso (G.map e₂) (G.map e₁) (G.map (e₂ ≫ e₁)) (G.map_comp e₂ e₁).symm Bm, ?_⟩
  exact canonical_eq_of_further_step (cG.π.app j₂) (G.map e₂) (cG.π.app j₁) (cG.w e₂)
    (G.map e₁) (cG.π.app j₀) (cG.w e₁) (G.map (e₂ ≫ e₁)) (G.map_comp e₂ e₁).symm
    (cG.w (e₂ ≫ e₁)) m₁ N.hom h₁

/-! ### Transporting a descended morphism of modules to the later stage -/

/-- A morphism of pullbacks of modules along a transition morphism, read through the canonical
identifications of the two stages, satisfies over the limit the equation obtained from the one it
satisfies there before the transport. -/
private theorem pullback_map_eq_canHom_comp {L Zk Zj Xs Ys : Scheme.{u}}
    (πk : L ⟶ Zk) (m : Zk ⟶ Zj) (πj : L ⟶ Zj) (hm : πk ≫ m = πj)
    (p : Zj ⟶ Ys) (pk : Zk ⟶ Ys) (hp : m ≫ p = pk)
    (tp : L ⟶ Ys) (hpj : πj ≫ p = tp) (hpk : πk ≫ pk = tp)
    (q : Zj ⟶ Xs) (qk : Zk ⟶ Xs) (hq : m ≫ q = qk)
    (tq : L ⟶ Xs) (hqj : πj ≫ q = tq) (hqk : πk ≫ qk = tq)
    (F : Ys.Modules) (G : Xs.Modules)
    (N : (Scheme.Modules.pullback tp).obj F ⟶ (Scheme.Modules.pullback tq).obj G)
    (iAinv : (Scheme.Modules.pullback pk).obj F ⟶
      (Scheme.Modules.pullback m).obj ((Scheme.Modules.pullback p).obj F))
    (hiA : iAinv ≫ canHom m p pk hp F = 𝟙 _)
    (κBinv : (Scheme.Modules.pullback tq).obj G ⟶
      (Scheme.Modules.pullback πj).obj ((Scheme.Modules.pullback q).obj G))
    (hκB : κBinv ≫ canHom πj q tq hqj G = 𝟙 _)
    (mm₀ : (Scheme.Modules.pullback m).obj ((Scheme.Modules.pullback p).obj F) ⟶
      (Scheme.Modules.pullback m).obj ((Scheme.Modules.pullback q).obj G))
    (heq : (Scheme.Modules.pullback πk).map mm₀ ≫
          canHom πk m πj hm ((Scheme.Modules.pullback q).obj G) =
        canHom πk m πj hm ((Scheme.Modules.pullback p).obj F) ≫
          canHom πj p tp hpj F ≫ N ≫ κBinv) :
    (Scheme.Modules.pullback πk).map (iAinv ≫ mm₀ ≫ canHom m q qk hq G) ≫
        canHom πk qk tq hqk G = canHom πk pk tp hpk F ≫ N := by
  have cocA := canHom_comp πk m p πj pk tp hm hp hpj hpk F
  have cocB := canHom_comp πk m q πj qk tq hm hq hqj hqk G
  have hinv : (Scheme.Modules.pullback πk).map iAinv ≫
      (Scheme.Modules.pullback πk).map (canHom m p pk hp F) = 𝟙 _ := by
    rw [← Functor.map_comp, hiA, CategoryTheory.Functor.map_id]
  calc (Scheme.Modules.pullback πk).map (iAinv ≫ mm₀ ≫ canHom m q qk hq G) ≫
          canHom πk qk tq hqk G
      = (Scheme.Modules.pullback πk).map iAinv ≫
          (Scheme.Modules.pullback πk).map mm₀ ≫
            ((Scheme.Modules.pullback πk).map (canHom m q qk hq G) ≫
              canHom πk qk tq hqk G) := by
          rw [Functor.map_comp, Functor.map_comp]; simp only [Category.assoc]
    _ = (Scheme.Modules.pullback πk).map iAinv ≫
          ((Scheme.Modules.pullback πk).map mm₀ ≫
            canHom πk m πj hm ((Scheme.Modules.pullback q).obj G)) ≫
              canHom πj q tq hqj G := by
          rw [cocB]; simp only [Category.assoc]
    _ = (Scheme.Modules.pullback πk).map iAinv ≫
          (canHom πk m πj hm ((Scheme.Modules.pullback p).obj F) ≫
            canHom πj p tp hpj F ≫ N ≫ κBinv) ≫ canHom πj q tq hqj G := by rw [heq]
    _ = (Scheme.Modules.pullback πk).map iAinv ≫
          (canHom πk m πj hm ((Scheme.Modules.pullback p).obj F) ≫
            canHom πj p tp hpj F) ≫ N := by
          simp only [Category.assoc]
          rw [hκB, Category.comp_id]
    _ = (Scheme.Modules.pullback πk).map iAinv ≫
          ((Scheme.Modules.pullback πk).map (canHom m p pk hp F) ≫
            canHom πk pk tp hpk F) ≫ N := by rw [← cocA]
    _ = canHom πk pk tp hpk F ≫ N := by
          rw [← Category.assoc, ← Category.assoc, hinv, Category.id_comp]

/-! ### The two descents at one stage -/

/-- `AlgebraicGeometry.exists_stage_comparison` for a limit cone `cF` on the inverse system of
base changes of `fi` whose projections are compatible with `b` and `dt`, given a morphism `c₁` at a
stage `k₁` which is cartesian over the transition morphism and recovers `gt` over the limit. -/
private theorem exists_stage_comparison_module {I : Type u} [Category.{u} I] [IsCofiltered I]
    (DS : I ⥤ Scheme.{u}) [∀ j : I, IsAffine (DS.obj j)] (cS : Cone DS)
    (i : I) {Xi Yi : Scheme.{u}} (fi : Xi ⟶ DS.obj i) (gi : Yi ⟶ DS.obj i)
    (hfi : FinitePresentation fi)
    (cF : Cone (pullbackDiagram DS i fi)) (hcFl : IsLimit cF)
    {b : cF.pt ⟶ cS.pt} {dt : cF.pt ⟶ Xi} {gt : cF.pt ⟶ Yi}
    (hπfst : ∀ a : Over i, cF.π.app a ≫ pullback.fst (DS.map a.hom) fi = b ≫ cS.π.app a.left)
    (hπsnd : ∀ a : Over i, cF.π.app a ≫ pullback.snd (DS.map a.hom) fi = dt)
    {k₁ : I} (s₁ : k₁ ⟶ i) (c₁ : pullback (DS.map s₁) fi ⟶ Yi)
    (hpb₁ : IsPullback c₁ (pullback.fst (DS.map s₁) fi) gi (DS.map s₁))
    (h3₀ : (cF.π.app (Over.mk s₁) : cF.pt ⟶ pullback (DS.map s₁) fi) ≫ c₁ = gt)
    (xL : Xi.Modules) (yL : Yi.Modules)
    (hxL : xL.IsFinitePresentation) (hyL : yL.IsFinitePresentation)
    (N : (Scheme.Modules.pullback gt).obj yL ≅ (Scheme.Modules.pullback dt).obj xL) :
    ∃ (k : I) (s : k ⟶ i) (cc : pullback (DS.map s) fi ⟶ Yi)
      (mm : (Scheme.Modules.pullback cc).obj yL ≅
        (Scheme.Modules.pullback (pullback.snd (DS.map s) fi)).obj xL),
      IsPullback cc (pullback.fst (DS.map s) fi) gi (DS.map s) ∧
        ∀ u : cF.pt ⟶ pullback (DS.map s) fi,
          u ≫ pullback.fst (DS.map s) fi = b ≫ cS.π.app k →
          ∀ hu2 : u ≫ pullback.snd (DS.map s) fi = dt,
            ∃ hu3 : u ≫ cc = gt,
              (Scheme.Modules.pullback u).map mm.hom ≫
                  canHom u (pullback.snd (DS.map s) fi) dt hu2 xL =
                canHom u cc gt hu3 yL ≫ N.hom := by
  have hAff : ∀ {j k : I} (e : j ⟶ k), IsAffineHom (DS.map e) := fun _ => inferInstance
  have hqcfi := hfi.2.1
  have hqsfi := hfi.2.2
  have hXic : CompactSpace Xi := QuasiCompact.compactSpace_of_compactSpace fi
  have hXiq : QuasiSeparatedSpace Xi := quasiSeparatedSpace_of_quasiSeparated fi
  have hEaff : ∀ {a a' : Over i} (g : a ⟶ a'),
      IsAffineHom ((pullbackDiagram DS i fi).map g) :=
    fun g => isAffineHom_pullbackDiagram_map DS i fi g (hAff g.left)
  have hqcs : ∀ a : Over i, QuasiCompact (pullback.snd (DS.map a.hom) fi) := fun a =>
    have := hAff a.hom
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @QuasiCompact)
      (IsPullback.of_hasPullback (DS.map a.hom) fi) inferInstance
  have hqss : ∀ a : Over i, QuasiSeparated (pullback.snd (DS.map a.hom) fi) := fun a =>
    have := hAff a.hom
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @QuasiSeparated)
      (IsPullback.of_hasPullback (DS.map a.hom) fi) inferInstance
  have hEc : ∀ a : Over i, CompactSpace ((pullbackDiagram DS i fi).obj a) := by
    intro a
    have := hqcs a
    have h := QuasiCompact.compactSpace_of_compactSpace (pullback.snd (DS.map a.hom) fi)
    exact h
  have hEq : ∀ a : Over i, QuasiSeparatedSpace ((pullbackDiagram DS i fi).obj a) := by
    intro a
    have := hqss a
    have h := quasiSeparatedSpace_of_quasiSeparated (pullback.snd (DS.map a.hom) fi)
    exact h
  have h2₀ : (cF.π.app (Over.mk s₁) : cF.pt ⟶ pullback (DS.map s₁) fi) ≫
      pullback.snd (DS.map s₁) fi = dt := hπsnd (Over.mk s₁)
  have hAfp : ((Scheme.Modules.pullback c₁).obj yL).IsFinitePresentation :=
    isFinitePresentation_pullback c₁ yL
  have hBfp : ((Scheme.Modules.pullback (pullback.snd (DS.map s₁) fi)).obj
      xL).IsFinitePresentation := isFinitePresentation_pullback _ xL
  obtain ⟨NN, hNNhom⟩ : ∃ z : (Scheme.Modules.pullback (X := cF.pt)
        (cF.π.app (Over.mk s₁))).obj ((Scheme.Modules.pullback c₁).obj yL) ≅
      (Scheme.Modules.pullback (X := cF.pt) (cF.π.app (Over.mk s₁))).obj
        ((Scheme.Modules.pullback (pullback.snd (DS.map s₁) fi)).obj xL),
      z.hom = canHom (W := cF.pt) (cF.π.app (Over.mk s₁)) c₁ gt h3₀ yL ≫ N.hom ≫
        (canIso (W := cF.pt) (cF.π.app (Over.mk s₁)) (pullback.snd (DS.map s₁) fi) dt
          h2₀ xL).inv :=
    ⟨canIso (W := cF.pt) (cF.π.app (Over.mk s₁)) c₁ gt h3₀ yL ≪≫ N ≪≫
      (canIso (W := cF.pt) (cF.π.app (Over.mk s₁)) (pullback.snd (DS.map s₁) fi) dt
        h2₀ xL).symm, rfl⟩
  obtain ⟨j, ee, mm₀, heq₀⟩ :=
    exists_stage_isIso_pullback_map (pullbackDiagram DS i fi) cF hcFl (Over.mk s₁)
      ((Scheme.Modules.pullback c₁).obj yL)
      ((Scheme.Modules.pullback (pullback.snd (DS.map s₁) fi)).obj xL) hAfp hBfp NN
  rw [hNNhom] at heq₀
  have hsndj := pullbackDiagram_map_comp_snd DS i fi ee
  obtain ⟨mm, hmmhom⟩ : ∃ z : (Scheme.Modules.pullback
        (((pullbackDiagram DS i fi).map ee) ≫ c₁)).obj yL ≅
      (Scheme.Modules.pullback (pullback.snd (DS.map j.hom) fi)).obj xL,
      z.hom = (canIso ((pullbackDiagram DS i fi).map ee) c₁
            (((pullbackDiagram DS i fi).map ee) ≫ c₁) rfl yL).inv ≫
          mm₀.hom ≫ canHom ((pullbackDiagram DS i fi).map ee)
            (pullback.snd (DS.map s₁) fi) (pullback.snd (DS.map j.hom) fi) hsndj xL :=
    ⟨(canIso ((pullbackDiagram DS i fi).map ee) c₁
        (((pullbackDiagram DS i fi).map ee) ≫ c₁) rfl yL).symm ≪≫
      mm₀ ≪≫ canIso ((pullbackDiagram DS i fi).map ee) (pullback.snd (DS.map s₁) fi)
        (pullback.snd (DS.map j.hom) fi) hsndj xL, rfl⟩
  refine ⟨j.left, j.hom, (pullbackDiagram DS i fi).map ee ≫ c₁, mm, ?_, ?_⟩
  · have hpaste := (isPullback_pullbackDiagram_map DS i fi ee).paste_horiz hpb₁
    have hmapc : DS.map ee.left ≫ DS.map s₁ = DS.map j.hom := map_left_comp_map_hom DS ee
    rwa [hmapc] at hpaste
  · intro u hu1 hu2
    have hueq : u = cF.π.app j :=
      pullback.hom_ext (hu1.trans (hπfst j).symm) (hu2.trans (hπsnd j).symm)
    have hm : u ≫ ((pullbackDiagram DS i fi).map ee) = cF.π.app (Over.mk s₁) := by
      rw [hueq]
      exact cF.w ee
    have hu3 : u ≫ (((pullbackDiagram DS i fi).map ee) ≫ c₁) = gt :=
      (Category.assoc _ _ _).symm.trans ((congrArg (fun z => z ≫ c₁) hm).trans h3₀)
    refine ⟨hu3, ?_⟩
    rw [hmmhom]
    subst hueq
    refine Eq.trans ?_ (Eq.trans (pullback_map_eq_canHom_comp (L := cF.pt) (cF.π.app j)
      ((pullbackDiagram DS i fi).map ee)
      (cF.π.app (Over.mk s₁)) hm c₁
      (((pullbackDiagram DS i fi).map ee) ≫ c₁) rfl gt h3₀ hu3
      (pullback.snd (DS.map s₁) fi) (pullback.snd (DS.map j.hom) fi) hsndj dt h2₀ hu2
      yL xL N.hom
      (canIso ((pullbackDiagram DS i fi).map ee) c₁
        (((pullbackDiagram DS i fi).map ee) ≫ c₁) rfl yL).inv
      (canIso ((pullbackDiagram DS i fi).map ee) c₁
        (((pullbackDiagram DS i fi).map ee) ≫ c₁) rfl yL).inv_hom_id
      (canIso (W := cF.pt) (cF.π.app (Over.mk s₁)) (pullback.snd (DS.map s₁) fi) dt h2₀ xL).inv
      (canIso (W := cF.pt) (cF.π.app (Over.mk s₁)) (pullback.snd (DS.map s₁) fi) dt
        h2₀ xL).inv_hom_id
      mm₀.hom heq₀) ?_) <;> rfl

/-- **Descent of a comparison of total spaces together with a comparison of modules.** Let two
finitely presented morphisms over a stage of a cofiltered inverse system of affine schemes have
identified base changes to the limit, and let the pullbacks to the limit of two finitely presented
modules on their sources be identified over that identification. Then over some later stage there
is a morphism from the base change of the first morphism to the target of the second, cartesian
over the transition morphism, together with an isomorphism of the corresponding pullbacks of the
two modules, recovering the given data over the limit. -/
theorem exists_stage_comparison {I : Type u} [Category.{u} I] [IsCofiltered I]
    (DS : I ⥤ Scheme.{u}) [∀ j : I, IsAffine (DS.obj j)] (cS : Cone DS) (hcS : IsLimit cS)
    (i : I) {Xi Yi XT : Scheme.{u}} (fi : Xi ⟶ DS.obj i) (gi : Yi ⟶ DS.obj i)
    (hfi : FinitePresentation fi) (hgi : FinitePresentation gi)
    {b : XT ⟶ cS.pt} {dt : XT ⟶ Xi} {gt : XT ⟶ Yi}
    (hd : IsPullback dt b fi (cS.π.app i)) (hg : IsPullback gt b gi (cS.π.app i))
    (xL : Xi.Modules) (yL : Yi.Modules)
    (hxL : xL.IsFinitePresentation) (hyL : yL.IsFinitePresentation)
    (N : (Scheme.Modules.pullback gt).obj yL ≅ (Scheme.Modules.pullback dt).obj xL) :
    ∃ (k : I) (s : k ⟶ i) (cc : pullback (DS.map s) fi ⟶ Yi)
      (mm : (Scheme.Modules.pullback cc).obj yL ≅
        (Scheme.Modules.pullback (pullback.snd (DS.map s) fi)).obj xL),
      IsPullback cc (pullback.fst (DS.map s) fi) gi (DS.map s) ∧
        ∀ u : XT ⟶ pullback (DS.map s) fi,
          u ≫ pullback.fst (DS.map s) fi = b ≫ cS.π.app k →
          ∀ hu2 : u ≫ pullback.snd (DS.map s) fi = dt,
            ∃ hu3 : u ≫ cc = gt,
              (Scheme.Modules.pullback u).map mm.hom ≫
                  canHom u (pullback.snd (DS.map s) fi) dt hu2 xL =
                canHom u cc gt hu3 yL ≫ N.hom := by
  obtain ⟨k₁, s₁, c₁, hpb₁, hall₁⟩ :=
    exists_stage_comparison_morphism DS cS hcS i fi gi hfi hgi hd hg
  have hcFl : IsLimit ((pullbackCone DS cS i fi).extend hd.flip.isoPullback.hom) :=
    (isLimitPullbackCone DS cS hcS i fi).ofIsoLimit
      (Cone.ext hd.flip.isoPullback (fun _ => rfl)).symm
  have he1 : ∀ a : Over i, (pullbackCone DS cS i fi).π.app a ≫
      pullback.fst (DS.map a.hom) fi =
      pullback.fst (cS.π.app i) fi ≫ cS.π.app a.left := by
    intro a
    rw [pullbackCone_π_app]
    exact pullback.lift_fst _ _ _
  have he2 : ∀ a : Over i, (pullbackCone DS cS i fi).π.app a ≫
      pullback.snd (DS.map a.hom) fi = pullback.snd (cS.π.app i) fi := by
    intro a
    rw [pullbackCone_π_app]
    exact pullback.lift_snd _ _ _
  have hπfst : ∀ a : Over i,
      ((pullbackCone DS cS i fi).extend hd.flip.isoPullback.hom).π.app a ≫
        pullback.fst (DS.map a.hom) fi = b ≫ cS.π.app a.left := fun a =>
    (Category.assoc _ _ _).trans
      ((congrArg (fun z => hd.flip.isoPullback.hom ≫ z) (he1 a)).trans
        ((Category.assoc _ _ _).symm.trans
          (congrArg (fun z => z ≫ cS.π.app a.left) hd.flip.isoPullback_hom_fst)))
  have hπsnd : ∀ a : Over i,
      ((pullbackCone DS cS i fi).extend hd.flip.isoPullback.hom).π.app a ≫
        pullback.snd (DS.map a.hom) fi = dt := fun a =>
    (Category.assoc _ _ _).trans
      ((congrArg (fun z => hd.flip.isoPullback.hom ≫ z) (he2 a)).trans
        hd.flip.isoPullback_hom_snd)
  exact exists_stage_comparison_module DS cS i fi gi hfi
    ((pullbackCone DS cS i fi).extend hd.flip.isoPullback.hom) hcFl hπfst hπsnd s₁ c₁ hpb₁
    (hall₁ _ (hπfst (Over.mk s₁)) (hπsnd (Over.mk s₁))) xL yL hxL hyL N

/-! ### The comparison of polarizations of a fill-in -/

namespace PolarizedFamily

variable {B : BigFppfSite.{u}}

/-- The comparison of polarizations of the fill-in of Stacks 003S (b), written out. -/
theorem fillIn_lineBundleIso_hom {x y z : PolarizedFamily B} (φ : y ⟶ x) (ψ : z ⟶ x)
    (f : z.base ⟶ y.base) (hcomm : f ≫ φ.baseMap = ψ.baseMap) :
    (fillIn φ ψ f hcomm).lineBundleIso.hom =
      (Scheme.Modules.pullback (fillInTotalMap φ ψ f hcomm)).map φ.lineBundleIso.inv ≫
        (Scheme.Modules.pullbackComp (fillInTotalMap φ ψ f hcomm) φ.totalMap).hom.app
            x.lineBundle ≫
          eqToHom (congrArg (fun m => (Scheme.Modules.pullback m).obj x.lineBundle)
            (fillInTotalMap_comp_totalMap φ ψ f hcomm)) ≫ ψ.lineBundleIso.hom := rfl

/-- **A composite of morphisms of polarized families is a prescribed morphism** as soon as the
base maps and the maps of total spaces compose to those of the prescribed morphism and the two
comparisons of polarizations agree through the canonical identification of the iterated pullback
with the pullback along the composite. -/
theorem Hom.comp_eq_of_lineBundleIso_hom {x y z : PolarizedFamily B} (f : x ⟶ y) (g : y ⟶ z)
    (h : x ⟶ z) (hbase : f.baseMap ≫ g.baseMap = h.baseMap)
    (htotal : f.totalMap ≫ g.totalMap = h.totalMap)
    (hmod : (Scheme.Modules.pullback f.totalMap).map g.lineBundleIso.hom ≫ f.lineBundleIso.hom =
      canHom f.totalMap g.totalMap h.totalMap htotal z.lineBundle ≫ h.lineBundleIso.hom) :
    f ≫ g = h := by
  refine Hom.ext' hbase htotal ?_
  refine (heq_iff_eq_eqToHom_comp
    (congrArg (fun k => (Scheme.Modules.pullback k).obj z.lineBundle) htotal)).2 ?_
  change (Scheme.Modules.pullbackComp f.totalMap g.totalMap).inv.app z.lineBundle ≫
    (Scheme.Modules.pullback f.totalMap).map g.lineBundleIso.hom ≫ f.lineBundleIso.hom = _
  rw [hmod, canHom_eq_eqToHom, Category.assoc]
  exact inv_comp_hom_comp
    ((Scheme.Modules.pullbackComp f.totalMap g.totalMap).app z.lineBundle) _

/-- The converse of `AlgebraicGeometry.PolarizedFamily.Hom.comp_eq_of_lineBundleIso_hom`: from a
factorisation of a morphism of polarized families one reads off the equation its comparisons of
polarizations satisfy. -/
theorem Hom.lineBundleIso_hom_comp_of_comp_eq {x y z : PolarizedFamily B} (f : x ⟶ y) (g : y ⟶ z)
    (h : x ⟶ z) (htotal : f.totalMap ≫ g.totalMap = h.totalMap) (hfg : f ≫ g = h) :
    (Scheme.Modules.pullback f.totalMap).map g.lineBundleIso.hom ≫ f.lineBundleIso.hom =
      canHom f.totalMap g.totalMap h.totalMap htotal z.lineBundle ≫ h.lineBundleIso.hom := by
  have hheq : (f ≫ g).lineBundleIso.hom ≍ h.lineBundleIso.hom := by rw [hfg]
  have hh := (heq_iff_eq_eqToHom_comp
    (congrArg (fun k => (Scheme.Modules.pullback k).obj z.lineBundle) htotal)).1 hheq
  rw [canHom_eq_eqToHom, Category.assoc, ← hh]
  exact (hom_comp_inv_comp
    ((Scheme.Modules.pullbackComp f.totalMap g.totalMap).app z.lineBundle)
    ((Scheme.Modules.pullback f.totalMap).map g.lineBundleIso.hom ≫
      f.lineBundleIso.hom)).symm

end PolarizedFamily

/-! ### Descent of vertical morphisms -/

/-- **Descent of vertical morphisms for `𝒫olarized`.** A vertical morphism between the base
changes to the limit of a cofiltered inverse system of affine schemes of two polarized families
over a stage comes from a morphism at a later stage. -/
theorem descentHom_polarizedSliceProjection (B : BigFppfSite.{u}) {S : Scheme.{u}}
    (hS : B.Contains S) (hT : IsTerminal (B.obj hS)) {I : Type u} [Category.{u} I]
    [IsCofiltered I] (D : I ⥤ BigAffineFppf B S hS) (c : Cone D)
    (hc : IsLimit ((BigAffineFppf.toScheme B S hS).mapCone c)) :
    Deformation.Artin.DescentHom (polarizedSliceProjection B hS hT)
      (D ⋙ BigAffineFppf.inclusion B S hS) ((BigAffineFppf.inclusion B S hS).mapCone c) := by
  intro i xi yi x y
  obtain ⟨⟨xib, xit, xitb, xipr, xifl, xifp, xiL, xiLi, xiLa⟩, hxi⟩ := xi
  obtain ⟨⟨yib, yit, yitb, yipr, yifl, yifp, yiL, yiLi, yiLa⟩, hyi⟩ := yi
  obtain ⟨⟨xb, xt, xtb, xpr, xfl, xfp, xL, xLi, xLa⟩, hx⟩ := x
  obtain ⟨⟨yb, yt, ytb, ypr, yfl, yfp, yLm, yLmi, yLma⟩, hy⟩ := y
  obtain rfl : xib = ((D ⋙ BigAffineFppf.inclusion B S hS).obj i).left :=
    congrArg Comma.left hxi
  obtain rfl : yib = ((D ⋙ BigAffineFppf.inclusion B S hS).obj i).left :=
    congrArg Comma.left hyi
  obtain rfl : xb = ((BigAffineFppf.inclusion B S hS).mapCone c).pt.left :=
    congrArg Comma.left hx
  obtain rfl : yb = ((BigAffineFppf.inclusion B S hS).mapCone c).pt.left :=
    congrArg Comma.left hy
  intro δ ε hδ hε φ hφ
  have hbase : ∀ {x' y' : PolarizedFamily B} {V W : BigFppfOver B S hS} (g : V ⟶ W) (ψ : x' ⟶ y'),
      (polarizedSliceProjection B hS hT).IsHomLift g ψ → ψ.baseMap ≍ g.left := by
    intro x' y' V W g ψ hψ
    obtain rfl := IsHomLift.domain_eq (polarizedSliceProjection B hS hT) g ψ
    obtain rfl := IsHomLift.codomain_eq (polarizedSliceProjection B hS hT) g ψ
    rw [IsHomLift.eq_of_isHomLift (polarizedSliceProjection B hS hT) g ψ]
    exact HEq.rfl
  have hδb : δ.baseMap = (((BigAffineFppf.inclusion B S hS).mapCone c).π.app i).left :=
    eq_of_heq (hbase _ δ hδ)
  have hεb : ε.baseMap = (((BigAffineFppf.inclusion B S hS).mapCone c).π.app i).left :=
    eq_of_heq (hbase _ ε hε)
  have hφb : φ.baseMap = 𝟙 _ := eq_of_heq (hbase _ φ hφ)
  have hγb : (φ ≫ ε).baseMap =
      (((BigAffineFppf.inclusion B S hS).mapCone c).π.app i).left := by
    change φ.baseMap ≫ ε.baseMap = _
    rw [hφb, hεb, Category.id_comp]
  have hAffD : ∀ j : I, IsAffine ((D ⋙ BigAffineFppf.toScheme B S hS).obj j) :=
    fun j => BigAffineFppf.isAffine_toScheme_obj B S hS (D.obj j)
  have δcart : IsPullback δ.totalMap xtb xitb
      (((BigAffineFppf.toScheme B S hS).mapCone c).π.app i) := by
    have h : B.inclusion.map δ.baseMap =
        ((BigAffineFppf.toScheme B S hS).mapCone c).π.app i := by rw [hδb]; rfl
    rw [← h]
    exact δ.cartesian
  have γcart : IsPullback (φ ≫ ε).totalMap xtb yitb
      (((BigAffineFppf.toScheme B S hS).mapCone c).π.app i) := by
    have h : B.inclusion.map (φ ≫ ε).baseMap =
        ((BigAffineFppf.toScheme B S hS).mapCone c).π.app i := by rw [hγb]; rfl
    rw [← h]
    exact (φ ≫ ε).cartesian
  have hxiLfp : xiL.IsFinitePresentation :=
    @AlgebraicGeometry.SheafOfModules.isFinitePresentation_of_isInvertible xit xiL xiLi
  have hyiLfp : yiL.IsFinitePresentation :=
    @AlgebraicGeometry.SheafOfModules.isFinitePresentation_of_isInvertible yit yiL yiLi
  obtain ⟨k, s, cc, mm, hpb, hall⟩ := exists_stage_comparison
    (D ⋙ BigAffineFppf.toScheme B S hS) ((BigAffineFppf.toScheme B S hS).mapCone c) hc i
    xitb yitb xifp yifp δcart γcart xiL yiL hxiLfp hyiLfp
    ((φ ≫ ε).lineBundleIso ≪≫ δ.lineBundleIso.symm)
  let xiF : PolarizedFamily B :=
    { base := ((D ⋙ BigAffineFppf.inclusion B S hS).obj i).left, total := xit, toBase := xitb,
      proper := xipr, flat := xifl, finitePresentation := xifp, lineBundle := xiL,
      invertible := xiLi, relativelyAmple := xiLa }
  let yiF : PolarizedFamily B :=
    { base := ((D ⋙ BigAffineFppf.inclusion B S hS).obj i).left, total := yit, toBase := yitb,
      proper := yipr, flat := yifl, finitePresentation := yifp, lineBundle := yiL,
      invertible := yiLi, relativelyAmple := yiLa }
  let xkF : PolarizedFamily B :=
    xiF.stageBaseChange ((D ⋙ BigAffineFppf.inclusion B S hS).map s).left
  let ykF : PolarizedFamily B :=
    yiF.stageBaseChange ((D ⋙ BigAffineFppf.inclusion B S hS).map s).left
  let dx : xkF ⟶ xiF :=
    xiF.stageBaseChangeHom ((D ⋙ BigAffineFppf.inclusion B S hS).map s).left
  let dy : ykF ⟶ yiF :=
    yiF.stageBaseChangeHom ((D ⋙ BigAffineFppf.inclusion B S hS).map s).left
  have hcomm : (((BigAffineFppf.inclusion B S hS).mapCone c).π.app k).left ≫
      ((D ⋙ BigAffineFppf.inclusion B S hS).map s).left = δ.baseMap := by
    rw [hδb, ← Over.comp_left]
    exact congrArg Over.Hom.left (((BigAffineFppf.inclusion B S hS).mapCone c).w s)
  let δk := PolarizedFamily.fillIn dx δ
    (((BigAffineFppf.inclusion B S hS).mapCone c).π.app k).left hcomm
  have hδkfac : δk ≫ dx = δ := PolarizedFamily.fillIn_comp dx δ _ hcomm
  have h1 : δk.totalMap ≫
      Limits.pullback.fst ((D ⋙ BigAffineFppf.toScheme B S hS).map s) xitb =
      xtb ≫ ((BigAffineFppf.toScheme B S hS).mapCone c).π.app k :=
    PolarizedFamily.fillInTotalMap_comp_toBase dx δ _ hcomm
  have h2 : δk.totalMap ≫
      Limits.pullback.snd ((D ⋙ BigAffineFppf.toScheme B S hS).map s) xitb = δ.totalMap :=
    PolarizedFamily.fillInTotalMap_comp_totalMap dx δ _ hcomm
  obtain ⟨h3, hmod⟩ := hall δk.totalMap h1 h2
  let χ : xkF ⟶ yiF :=
    { baseMap := ((D ⋙ BigAffineFppf.inclusion B S hS).map s).left
      totalMap := cc
      cartesian := hpb
      lineBundleIso := mm }
  have hcomm2 : 𝟙 xkF.base ≫ dy.baseMap = χ.baseMap := Category.id_comp _
  let ψ : xkF ⟶ ykF := PolarizedFamily.fillIn dy χ (𝟙 xkF.base) hcomm2
  have hψfac : ψ ≫ dy = χ := PolarizedFamily.fillIn_comp dy χ _ hcomm2
  have hdxid : (Scheme.Modules.pullback δk.totalMap).map dx.lineBundleIso.hom ≫
      δk.lineBundleIso.hom = δk.lineBundleIso.hom :=
    functor_map_comp_eq_of_eq_id _ rfl _
  have hδklbi : δk.lineBundleIso.hom =
      canHom δk.totalMap dx.totalMap δ.totalMap
        (PolarizedFamily.fillInTotalMap_comp_totalMap dx δ _ hcomm) xiL ≫
        δ.lineBundleIso.hom :=
    hdxid.symm.trans (PolarizedFamily.Hom.lineBundleIso_hom_comp_of_comp_eq δk dx δ
      (PolarizedFamily.fillInTotalMap_comp_totalMap dx δ _ hcomm) hδkfac)
  have hmodb : (Scheme.Modules.pullback δk.totalMap).map mm.hom ≫
        canHom δk.totalMap dx.totalMap δ.totalMap
          (PolarizedFamily.fillInTotalMap_comp_totalMap dx δ _ hcomm) xiL =
      canHom δk.totalMap cc (φ ≫ ε).totalMap h3 yiL ≫
        ((φ ≫ ε).lineBundleIso.hom ≫ δ.lineBundleIso.inv) := by
    refine Eq.trans ?_ (Eq.trans hmod ?_) <;> rfl
  have hstep : (Scheme.Modules.pullback δk.totalMap).map mm.hom ≫ δk.lineBundleIso.hom =
      canHom δk.totalMap cc (φ ≫ ε).totalMap h3 yiL ≫ (φ ≫ ε).lineBundleIso.hom :=
    comp_eq_of_comp_eq_comp_inv δ.lineBundleIso hδklbi hmodb
  have hkey : δk ≫ χ = φ ≫ ε := by
    refine PolarizedFamily.Hom.comp_eq_of_lineBundleIso_hom δk χ (φ ≫ ε) ?_ h3 hstep
    change (((BigAffineFppf.inclusion B S hS).mapCone c).π.app k).left ≫
      ((D ⋙ BigAffineFppf.inclusion B S hS).map s).left = φ.baseMap ≫ ε.baseMap
    rw [hcomm, hδb, hφb, hεb, Category.id_comp]
  refine ⟨k, s, ⟨xkF, (polarizedProjection B).sliceAtTerminal_obj_eq hT rfl⟩,
    ⟨ykF, (polarizedProjection B).sliceAtTerminal_obj_eq hT rfl⟩, dx, dy, δk, ψ, ?_, ?_, ?_, ?_,
    hδkfac, ?_⟩
  · exact isHomLift_sliceAtTerminal hT ((D ⋙ BigAffineFppf.inclusion B S hS).map s) dx
      (Functor.IsHomLift.map (p := polarizedProjection B) dx)
  · exact isHomLift_sliceAtTerminal hT ((D ⋙ BigAffineFppf.inclusion B S hS).map s) dy
      (Functor.IsHomLift.map (p := polarizedProjection B) dy)
  · exact isHomLift_sliceAtTerminal hT
      (((BigAffineFppf.inclusion B S hS).mapCone c).π.app k) δk
      (Functor.IsHomLift.map (p := polarizedProjection B) δk)
  · exact isHomLift_sliceAtTerminal hT (𝟙 ((D ⋙ BigAffineFppf.inclusion B S hS).obj k)) ψ
      (Functor.IsHomLift.map (p := polarizedProjection B) ψ)
  · rw [hψfac]
    exact hkey

/-- **Fullness of the comparison functor of Stacks 07XL for `𝒫olarized`.** For every cofiltered
inverse system of affine schemes over the terminal base with limit `T`, the canonical functor
`colim 𝒫olarized_{Tᵢ} ⥤ 𝒫olarized_T` is full. -/
theorem full_colimitComparison_polarized (B : BigFppfSite.{u}) {S : Scheme.{u}}
    (hS : B.Contains S) (hT : IsTerminal (B.obj hS)) {I : Type u} [Category.{u} I]
    [IsCofiltered I] (D : I ⥤ BigAffineFppf B S hS) (c : Cone D)
    (hc : IsLimit ((BigAffineFppf.toScheme B S hS).mapCone c)) :
    letI : (polarizedSliceProjection B hS hT).IsFibered :=
      (polarizedProjection_isFiberedInGroupoids_unconditional.sliceAtTerminal hT).isFibered
    (Deformation.Artin.colimitComparison (polarizedSliceProjection B hS hT)
      (D ⋙ BigAffineFppf.inclusion B S hS)
      ((BigAffineFppf.inclusion B S hS).mapCone c)).Full :=
  let : (polarizedSliceProjection B hS hT).IsFibered :=
    (polarizedProjection_isFiberedInGroupoids_unconditional.sliceAtTerminal hT).isFibered
  Deformation.Artin.full_of_descentHom (polarizedSliceProjection B hS hT)
    (polarizedProjection_isFiberedInGroupoids_unconditional.sliceAtTerminal hT) _ _
    (descentHom_polarizedSliceProjection B hS hT D c hc)

end AlgebraicGeometry

end
