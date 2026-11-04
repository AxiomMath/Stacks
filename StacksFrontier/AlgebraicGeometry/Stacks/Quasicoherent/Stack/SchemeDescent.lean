module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Stack.SiteDescent
import all StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Stack.Fibre
import all StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Stack.SiteDescent

/-!
# Stacks 03YM, part 3: descent data on schemes and the stack condition

This file completes the proof of Stacks 03YM (re-exported by
`StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Stack`):

* the chosen fibre products `sitePullback` of the big fppf site and their images in schemes;
* the comparison `schemeDescentRestriction` of quasi-coherent descent data on schemes with
  descent data on the site, an equivalence whose essential surjectivity is `extendDescentData`;
* the identification `canonicalComparisonNatIso` of the comparison with the canonical descent
  functor of Stacks 023D;
* the fppf coverings of the site, `bigFppfOver_topology_eq_fppf`;
* conditions (2) and (3) of Stacks 026F via the two halves of Stacks 023T, and
  `Stacks.QCoh.projection_isStack`, **Stacks 03YM**.

## Main results

* `Stacks.QCoh.projection_isStack`: **Stacks 03YM**.

## References

* [Stacks Project, Tag 023T](https://stacks.math.columbia.edu/tag/023T)
* [Stacks Project, Tag 026F](https://stacks.math.columbia.edu/tag/026F)
* [Stacks Project, Tag 03YM](https://stacks.math.columbia.edu/tag/03YM)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

namespace Stacks.QCoh

universe u

universe w

variable {B : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local instance] isFibered_rawProjection

/-! ### Chosen fibre products in the site and their images in schemes -/

section SitePullbacks

open Limits

/-- A chosen fibre product in the big fppf site over `S`, built from the fibre product of the
underlying schemes; the cutoff bound of the site is preserved by `Scheme.size_pullback_lt`. -/
private noncomputable def sitePullback
    {X Y T : AlgebraicGeometry.BigFppfOver B S hS} (f : X ⟶ T) (g : Y ⟶ T) :
    ChosenPullback f g := by
  let a := (schemeFunctor (B := B) (S := S) (hS := hS)).map f
  let b := (schemeFunctor (B := B) (S := S) (hS := hS)).map g
  let P : B.Schemes := ⟨pullback a b,
    Scheme.size_pullback_lt a b X.left.property Y.left.property⟩
  let Q : AlgebraicGeometry.BigFppfOver B S hS :=
    Over.mk (Y := P) (ObjectProperty.homMk (pullback.fst a b ≫ X.hom.hom))
  let p₁ : Q ⟶ X := Over.homMk (ObjectProperty.homMk (pullback.fst a b))
  let p₂ : Q ⟶ Y := Over.homMk (ObjectProperty.homMk (pullback.snd a b)) (by
    apply ObjectProperty.hom_ext
    change pullback.snd a b ≫ Y.hom.hom = pullback.fst a b ≫ X.hom.hom
    have hf := congrArg (fun z => z.hom) (Over.w f)
    have hg := congrArg (fun z => z.hom) (Over.w g)
    change a ≫ T.hom.hom = X.hom.hom at hf
    change b ≫ T.hom.hom = Y.hom.hom at hg
    rw [← hf, ← hg, ← Category.assoc, ← Category.assoc, pullback.condition])
  have w : p₁ ≫ f = p₂ ≫ g := by
    ext
    exact pullback.condition
  refine {
    pullback := Q
    p₁ := p₁
    p₂ := p₂
    condition := w
    isLimit := PullbackCone.IsLimit.mk w (fun c => ?_) ?_ ?_ ?_ }
  · refine Over.homMk (ObjectProperty.homMk
      (pullback.lift c.fst.left.hom c.snd.left.hom ?_)) ?_
    · exact congrArg (fun z => z.left.hom) c.condition
    · apply ObjectProperty.hom_ext
      change (pullback.lift _ _ _) ≫ pullback.fst a b ≫ X.hom.hom = c.pt.hom.hom
      rw [pullback.lift_fst_assoc]
      exact congrArg (fun z => z.hom) (Over.w c.fst)
  · intro c
    ext
    exact pullback.lift_fst _ _ _
  · intro c
    ext
    exact pullback.lift_snd _ _ _
  · intro c m h₁ h₂
    ext
    apply pullback.hom_ext
    -- The right-hand side is `pullback.lift _ _ _ ≫ pullback.fst a b`; `pullback.lift_fst` is
    -- supplied as a term rather than rewritten with, because the chosen limit cone of the fibre
    -- product is not exposed and so a keyed rewrite cannot see through it.
    · refine Eq.trans ?_ (pullback.lift_fst _ _ _).symm
      simpa [p₁] using congrArg (fun z => z.left.hom) h₁
    · refine Eq.trans ?_ (pullback.lift_snd _ _ _).symm
      simpa [p₂] using congrArg (fun z => z.left.hom) h₂

/-- The image in schemes of `sitePullback f g`, a chosen fibre product of the underlying morphisms
of schemes. -/
private noncomputable def schemePullback
    {X Y T : AlgebraicGeometry.BigFppfOver B S hS} (f : X ⟶ T) (g : Y ⟶ T) :
    ChosenPullback (schemeFunctor.map f) (schemeFunctor.map g) where
  pullback := schemeFunctor.obj (sitePullback f g).pullback
  p₁ := schemeFunctor.map (sitePullback f g).p₁
  p₂ := schemeFunctor.map (sitePullback f g).p₂
  condition := by rw [← Functor.map_comp, ← Functor.map_comp, (sitePullback f g).condition]
  isLimit := (IsPullback.of_hasPullback _ _).isLimit
  p := schemeFunctor.map (sitePullback f g).p
  hp₁ := by rw [← Functor.map_comp, (sitePullback f g).hp₁]

/-- A chosen threefold fibre product of the images in schemes of three morphisms of the site: the
image of the chosen fibre product, in the site, of the two chosen pairwise fibre products over the
middle member, with the comparison to the chosen fibre product of the outer two members. -/
private noncomputable def schemePullback₃
    {X Y Z T : AlgebraicGeometry.BigFppfOver B S hS}
    (f : X ⟶ T) (g : Y ⟶ T) (h : Z ⟶ T) :
    ChosenPullback₃ (schemePullback f g) (schemePullback g h) (schemePullback f h) where
  chosenPullback := schemePullback (sitePullback f g).p₂ (sitePullback g h).p₁
  l :=
    { f := schemeFunctor.map ((sitePullback f h).isPullback.lift
        ((sitePullback (sitePullback f g).p₂ (sitePullback g h).p₁).p₁ ≫ (sitePullback f g).p₁)
        ((sitePullback (sitePullback f g).p₂ (sitePullback g h).p₁).p₂ ≫ (sitePullback g h).p₂)
        (by
          rw [Category.assoc, Category.assoc, (sitePullback f g).hp₁, (sitePullback g h).hp₂,
            ← (sitePullback f g).hp₂, ← (sitePullback g h).hp₁, ← Category.assoc,
            ← Category.assoc,
            (sitePullback (sitePullback f g).p₂ (sitePullback g h).p₁).condition]))
      f_p₁ := by
        change schemeFunctor.map _ ≫ schemeFunctor.map _ =
          schemeFunctor.map _ ≫ schemeFunctor.map _
        rw [← Functor.map_comp, ← Functor.map_comp, IsPullback.lift_fst]
      f_p₂ := by
        change schemeFunctor.map _ ≫ schemeFunctor.map _ =
          schemeFunctor.map _ ≫ schemeFunctor.map _
        rw [← Functor.map_comp, ← Functor.map_comp, IsPullback.lift_snd]
      f_p := by
        change schemeFunctor.map _ ≫ schemeFunctor.map _ =
          schemeFunctor.map _ ≫ schemeFunctor.map _
        rw [← Functor.map_comp, ← Functor.map_comp, ← (sitePullback f h).hp₁,
          IsPullback.lift_fst_assoc, Category.assoc, (sitePullback f g).hp₁] }

end SitePullbacks

/-! ### Quasi-coherent descent data on schemes read on the site -/

section SchemeRestriction

/-- The image under `schemeFunctor` of an equation between composites. -/
private lemma schemeFunctor_map_eq {X Y Z : AlgebraicGeometry.BigFppfOver B S hS}
    {a : X ⟶ Y} {b : Y ⟶ Z} {c : X ⟶ Z} (h : a ≫ b = c) :
    schemeFunctor.map a ≫ schemeFunctor.map b = schemeFunctor.map c := by
  rw [← Functor.map_comp, h]

variable {I : Type w} {U : AlgebraicGeometry.BigFppfOver B S hS}
  {X : I → AlgebraicGeometry.BigFppfOver B S hS} (f : ∀ i, X i ⟶ U)

/-- A quasi-coherent descent datum for the underlying family of schemes, read on the big fppf
site. -/
private noncomputable def schemeDescentRestrictionObj
    (D : AlgebraicGeometry.QuasicoherentDescentData (fun i => schemeFunctor.map (f i))) :
    restrictedQCohData f := ⟨{
    obj i := D.obj.obj i
    hom _ q _ _ a b ha hb := D.obj.hom (schemeFunctor.map q)
      (schemeFunctor.map a) (schemeFunctor.map b)
      (schemeFunctor_map_eq ha)
      (schemeFunctor_map_eq hb)
    -- The pullback map on the left is the one of the restriction of
    -- `modulePullbackPseudofunctor` along `schemeFunctor`, and the datum `D` supplies the one of
    -- `modulePullbackPseudofunctor`; `toPseudofunctor_comp_pullHom` identifies them, having been
    -- proved over a variable functor and pseudofunctor.
    pullHom_hom _ _ k q q' hq i j a b ha hb ka kb hka hkb :=
      (toPseudofunctor_comp_pullHom (schemeFunctor (B := B) (S := S) (hS := hS))
        AlgebraicGeometry.modulePullbackPseudofunctor
        (M₁ := D.obj.obj i) (M₂ := D.obj.obj j) (f₁ := a) (f₂ := b)
        (D.obj.hom (schemeFunctor.map q) (schemeFunctor.map a) (schemeFunctor.map b)
          (schemeFunctor_map_eq ha)
          (schemeFunctor_map_eq hb))
        k ka kb hka hkb).trans
      (D.obj.pullHom_hom (schemeFunctor.map k) (schemeFunctor.map q) (schemeFunctor.map q')
        (schemeFunctor_map_eq hq)
        (schemeFunctor.map a) (schemeFunctor.map b)
        (schemeFunctor_map_eq ha)
        (schemeFunctor_map_eq hb)
        (schemeFunctor.map ka) (schemeFunctor.map kb)
        (schemeFunctor_map_eq hka)
        (schemeFunctor_map_eq hkb))
    hom_self _ _ _ _ ha := D.obj.hom_self _ _ (schemeFunctor_map_eq ha)
    hom_comp _ _ _ _ _ _ _ _ ha hb hc := D.obj.hom_comp _ _ _ _
      (schemeFunctor_map_eq ha) (schemeFunctor_map_eq hb)
      (schemeFunctor_map_eq hc)
    }, D.property⟩

/-- Restriction of a morphism of quasi-coherent descent data to the big fppf site. -/
private noncomputable def schemeDescentRestrictionMap
    {D E : AlgebraicGeometry.QuasicoherentDescentData (fun i => schemeFunctor.map (f i))}
    (φ : D ⟶ E) :
    schemeDescentRestrictionObj f D ⟶ schemeDescentRestrictionObj f E :=
  ObjectProperty.homMk {
    hom i := φ.hom.hom i
    comm _ q _ _ a b ha hb := φ.hom.comm (schemeFunctor.map q)
      (schemeFunctor.map a) (schemeFunctor.map b)
      (schemeFunctor_map_eq ha)
      (schemeFunctor_map_eq hb) }

/-- Restriction of quasi-coherent descent data for the underlying family of schemes to descent data
on the big fppf site over `S`. -/
private noncomputable def schemeDescentRestriction :
    AlgebraicGeometry.QuasicoherentDescentData (fun i => schemeFunctor.map (f i)) ⥤
      restrictedQCohData f where
  obj := schemeDescentRestrictionObj f
  map := schemeDescentRestrictionMap f
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The transition morphisms of a restricted descent datum are those of the datum, at the images
of the morphisms.

One delta of `schemeDescentRestrictionObj` and nothing else: chained with
`canonicalDescentFunctor_obj_hom`, which performs the other crossing, this is what replaces a
single `rfl` across both. -/
private lemma schemeDescentRestriction_obj_hom
    (D : AlgebraicGeometry.QuasicoherentDescentData (fun i => schemeFunctor.map (f i)))
    {Y : AlgebraicGeometry.BigFppfOver B S hS} (q : Y ⟶ U) {i j : I}
    (a : Y ⟶ X i) (b : Y ⟶ X j) (ha : a ≫ f i = q) (hb : b ≫ f j = q) :
    ((schemeDescentRestriction f).obj D).obj.hom q a b ha hb =
      D.obj.hom (schemeFunctor.map q) (schemeFunctor.map a) (schemeFunctor.map b)
        (schemeFunctor_map_eq ha)
        (schemeFunctor_map_eq hb) :=
  rfl

/-- The component maps of a restricted morphism are the component maps of the morphism; stated
because the two sides live in hom-sets that agree only once `schemeDescentRestrictionObj`
unfolds. -/
private lemma schemeDescentRestriction_map_hom_hom
    {D E : AlgebraicGeometry.QuasicoherentDescentData (fun i => schemeFunctor.map (f i))}
    (φ : D ⟶ E) (i : I) :
    ((schemeDescentRestriction f).map φ).hom.hom i = φ.hom.hom i :=
  rfl

private lemma schemeDescentRestriction_faithful :
    (schemeDescentRestriction f).Faithful := by
  constructor
  intro D E φ ψ h
  apply ObjectProperty.hom_ext
  ext i
  exact (schemeDescentRestriction_map_hom_hom f φ i).symm.trans
    ((congrArg (fun a => a.hom.hom i) h).trans (schemeDescentRestriction_map_hom_hom f ψ i))

private lemma schemeDescentRestriction_full :
    (schemeDescentRestriction f).Full := by
  constructor
  intro D E φ
  let sq := fun i j => schemePullback (f i) (f j)
  let sq₃ := fun i j k => schemePullback₃ (f i) (f j) (f k)
  let ψ : Pseudofunctor.DescentData'.ofDescentData sq sq₃ D.obj ⟶
      Pseudofunctor.DescentData'.ofDescentData sq sq₃ E.obj := {
    hom := φ.hom.hom
    comm i j := φ.hom.comm (sitePullback (f i) (f j)).p
      (sitePullback (f i) (f j)).p₁ (sitePullback (f i) (f j)).p₂
      (sitePullback (f i) (f j)).hp₁ (sitePullback (f i) (f j)).hp₂ }
  refine ⟨ObjectProperty.homMk { hom := φ.hom.hom, comm := ?_ }, ?_⟩
  · intro Y q i j a b ha hb
    have hc := Pseudofunctor.DescentData'.comm ψ q a b ha hb
    simp only [Pseudofunctor.DescentData'.pullHom'_ofDescentData_hom] at hc
    exact hc
  · rfl

/-- The image in schemes of the chosen fibre product of the site is a fibre product. -/
private lemma sitePullback_isPullback {X Y T : AlgebraicGeometry.BigFppfOver B S hS}
    (f : X ⟶ T) (g : Y ⟶ T) :
    IsPullback (schemeFunctor.map (sitePullback f g).p₁) (schemeFunctor.map (sitePullback f g).p₂)
      (schemeFunctor.map f) (schemeFunctor.map g) :=
  IsPullback.of_hasPullback _ _

/-- A descent datum on the site, read as a quasi-coherent descent datum for the underlying family
of schemes, through the chosen fibre products of the site (`imageDescentData`).  Its components
are those of the given datum, hence quasi-coherent. -/
private noncomputable def extendDescentData (D : restrictedQCohData f) :
    AlgebraicGeometry.QuasicoherentDescentData (fun i => schemeFunctor.map (f i)) :=
  ⟨imageDescentData schemeFunctor AlgebraicGeometry.modulePullbackPseudofunctor
    (fun i j => sitePullback (f i) (f j)) (fun i j => sitePullback_isPullback (f i) (f j))
    (fun i j k => sitePullback (sitePullback (f i) (f j)).p₂ (sitePullback (f j) (f k)).p₁)
    (fun _ _ _ => sitePullback_isPullback _ _) D.obj, D.property⟩

/-- Restricting `extendDescentData f D` to the site returns the gluing morphisms of `D`. -/
private lemma schemeRestrictionExtend_hom (D : restrictedQCohData f)
    {Y : AlgebraicGeometry.BigFppfOver B S hS} (q : Y ⟶ U) {i j : I}
    (a : Y ⟶ X i) (b : Y ⟶ X j) (ha : a ≫ f i = q) (hb : b ≫ f j = q) :
    ((schemeDescentRestriction f).obj (extendDescentData f D)).obj.hom q a b ha hb =
      D.obj.hom q a b ha hb := by
  rw [schemeDescentRestriction_obj_hom]
  exact imageDescentData_hom schemeFunctor AlgebraicGeometry.modulePullbackPseudofunctor
    (fun i j => sitePullback (f i) (f j)) (fun i j => sitePullback_isPullback (f i) (f j))
    (fun i j k => sitePullback (sitePullback (f i) (f j)).p₂ (sitePullback (f j) (f k)).p₁)
    (fun i j k => sitePullback_isPullback _ _) D.obj q a b ha hb

/-- The components of the restriction of `extendDescentData f D` are those of `D`. -/
private lemma schemeRestrictionExtend_obj (D : restrictedQCohData f) (i : I) :
    ((schemeDescentRestriction f).obj (extendDescentData f D)).obj.obj i = D.obj.obj i :=
  rfl

/-- Restricting `extendDescentData f D` to the site returns `D`. -/
private noncomputable def schemeRestrictionExtendIso (D : restrictedQCohData f) :
    (schemeDescentRestriction f).obj (extendDescentData f D) ≅ D := by
  refine ObjectProperty.isoMk _ (Pseudofunctor.DescentData.isoMk
    (fun i => eqToIso (schemeRestrictionExtend_obj f D i)) ?_)
  intro Y q i j a b ha hb
  exact descentData_comm_of_eq (schemeRestrictionExtend_obj f D i)
    (schemeRestrictionExtend_obj f D j) _ _
    (heq_of_eq (schemeRestrictionExtend_hom f D q a b ha hb))

private lemma schemeDescentRestriction_essSurj :
    (schemeDescentRestriction f).EssSurj :=
  ⟨fun D => ⟨extendDescentData f D, ⟨schemeRestrictionExtendIso f D⟩⟩⟩

private lemma schemeDescentRestriction_isEquivalence :
    (schemeDescentRestriction f).IsEquivalence := by
  have := schemeDescentRestriction_faithful f
  have := schemeDescentRestriction_full f
  have := schemeDescentRestriction_essSurj f
  exact {}

end SchemeRestriction

/-! ### The comparison with the canonical descent functor -/

section CanonicalComparison

universe v

variable {U : AlgebraicGeometry.BigFppfOver B S hS}
  {I : Type v} {X : I → AlgebraicGeometry.BigFppfOver B S hS}
  (f : ∀ i, X i ⟶ U)

/-- The transition morphisms of the canonical descent datum of a quasi-coherent module are the
comparison isomorphisms of `AlgebraicGeometry.modulePullbackPseudofunctor`.

The one crossing performed here is that of `AlgebraicGeometry.canonicalDescentFunctor` with
`CategoryTheory.Pseudofunctor.DescentData.ofObj`, and it is routed through the
`@[simps]`-generated `CategoryTheory.Pseudofunctor.DescentData.ofObj_hom` rather than decided by
`whnf`. -/
private lemma canonicalDescentFunctor_obj_hom {J : Type v} {T : Scheme.{u}} {Z : J → Scheme.{u}}
    (g : ∀ i, Z i ⟶ T) (M : (qcohProp T).FullSubcategory)
    {Y : Scheme.{u}} (q : Y ⟶ T) {i j : J} (a : Y ⟶ Z i) (b : Y ⟶ Z j)
    (ha : a ≫ g i = q) (hb : b ≫ g j = q) :
    ((AlgebraicGeometry.canonicalDescentFunctor g).obj M).obj.hom q a b ha hb =
      (AlgebraicGeometry.modulePullbackPseudofunctor.mapComp' (g i).op.toLoc a.op.toLoc
          q.op.toLoc (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, ha])).inv.toNatTrans.app M.obj ≫
        (AlgebraicGeometry.modulePullbackPseudofunctor.mapComp' (g j).op.toLoc b.op.toLoc
            q.op.toLoc
            (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, hb])).hom.toNatTrans.app M.obj :=
  Pseudofunctor.DescentData.ofObj_hom (F := AlgebraicGeometry.modulePullbackPseudofunctor)
    (f := g) M.obj Y q i j a b ha hb

/-- The transition morphism that the canonical descent datum of `M` attaches to a pair of
morphisms of the site, read off the comparison isomorphisms of
`AlgebraicGeometry.modulePullbackPseudofunctor`.

The two spelling crossings — the restriction to the site and the canonical descent datum — are
performed one per declaration and chained here; deciding both in a single `rfl` exhausts the
heartbeat budget inside `whnf`. -/
private lemma canonicalRestriction_hom (M : modulesOn U)
    {Y : AlgebraicGeometry.BigFppfOver B S hS} (q : Y ⟶ U) {i j : I}
    (a : Y ⟶ X i) (b : Y ⟶ X j) (ha : a ≫ f i = q) (hb : b ≫ f j = q) :
    ((schemeDescentRestriction f).obj
        ((AlgebraicGeometry.canonicalDescentFunctor
          (fun i => schemeFunctor.map (f i))).obj M)).obj.hom q a b ha hb =
      (AlgebraicGeometry.modulePullbackPseudofunctor.mapComp'
          (schemeFunctor.map (f i)).op.toLoc (schemeFunctor.map a).op.toLoc
          (schemeFunctor.map q).op.toLoc
          (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, ← Functor.map_comp,
            ha])).inv.toNatTrans.app M.obj ≫
      (AlgebraicGeometry.modulePullbackPseudofunctor.mapComp'
          (schemeFunctor.map (f j)).op.toLoc (schemeFunctor.map b).op.toLoc
          (schemeFunctor.map q).op.toLoc
          (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, ← Functor.map_comp,
            hb])).hom.toNatTrans.app M.obj := by
  -- The two equalities are chained by rewriting, not by `Eq.trans`: each of `h₁` and `h₂` is
  -- cheap on its own, and so is each rewrite, whereas transitivity asks the unifier to cross the
  -- two spellings of the hom-set a second time inside one elaboration and exhausts the budget.
  have h₁ := schemeDescentRestriction_obj_hom f
    ((AlgebraicGeometry.canonicalDescentFunctor
      (fun i => schemeFunctor.map (f i))).obj M) q a b ha hb
  have h₂ := canonicalDescentFunctor_obj_hom (fun i => schemeFunctor.map (f i)) M
    (schemeFunctor.map q) (schemeFunctor.map a) (schemeFunctor.map b)
    (schemeFunctor_map_eq ha)
    (schemeFunctor_map_eq hb)
  rw [h₁, h₂]

private lemma canonicalSchemeTransition (M : modulesOn U)
    {Y : AlgebraicGeometry.BigFppfOver B S hS} (q : Y ⟶ U) {i j : I}
    (a : Y ⟶ X i) (b : Y ⟶ X j)
    (ha : a ≫ f i = q) (hb : b ≫ f j = q) :
    (moduleDescentToFiber
      ((schemeDescentRestriction f).obj
        ((AlgebraicGeometry.canonicalDescentFunctor
          (fun i => schemeFunctor.map (f i))).obj M))).hom q a b ha hb =
    moduleTransition ((modulePullback (f i)).obj M) ((modulePullback (f j)).obj M) a b
      (((modulePullbackCompIso' (f j) b q hb).app M).hom ≫
        ((modulePullbackCompIso' (f i) a q ha).app M).inv) := by
  rw [modulePullbackCompIso'_hom_comp_inv]
  refine congrArg (moduleTransition ((modulePullback (f i)).obj M)
    ((modulePullback (f j)).obj M) a b) ?_
  apply ObjectProperty.hom_ext
  -- The comparison isomorphisms of `restrictedModules` are those of
  -- `AlgebraicGeometry.modulePullbackPseudofunctor` at the images of the morphisms, which is the
  -- content of `toPseudofunctor_comp_mapComp'`.  Rewriting with it first leaves a `rfl` that
  -- unfolds only the restriction and the canonical descent datum; deciding the whole crossing in
  -- one `rfl` instead exhausts the heartbeat budget inside `whnf`.
  rw [toPseudofunctor_comp_mapComp' (schemeFunctor (B := B) (S := S) (hS := hS))
      AlgebraicGeometry.modulePullbackPseudofunctor (f j) b q hb,
    toPseudofunctor_comp_mapComp' (schemeFunctor (B := B) (S := S) (hS := hS))
      AlgebraicGeometry.modulePullbackPseudofunctor (f i) a q ha]
  exact canonicalRestriction_hom f M q b a hb ha

private noncomputable def canonicalComparisonIso (M : modulesOn U) :
    moduleDescentToFiber
      ((schemeDescentRestriction f).obj
        ((AlgebraicGeometry.canonicalDescentFunctor
          (fun i => schemeFunctor.map (f i))).obj M)) ≅
      ((Functor.IsFibered.pullbackPseudofunctor rawProjection).toDescentData f).obj
        (ofModule M) := by
  refine Pseudofunctor.DescentData.isoMk
    (fun i => modulePullbackComparison (f i) M) ?_
  intro Y q i j a b ha hb
  -- The canonical descent datum glues the chosen pullbacks by the canonical comparison, and that
  -- comparison is the contraction of one iterated chosen pullback followed by the expansion of
  -- the other; both identifications are library lemmas, so no definitional unfolding of
  -- `Pseudofunctor.toDescentData` is needed here.
  have hd : (((Functor.IsFibered.pullbackPseudofunctor rawProjection).toDescentData f).obj
        (ofModule M)).hom q a b ha hb =
      (Functor.pullbackFiberCompIso' (ofModule M) (f i) a q ha).hom ≫
        (Functor.pullbackFiberCompIso' (ofModule M) (f j) b q hb).inv :=
    (Functor.toDescentData_obj_hom rawProjection f (ofModule M) q a b ha hb
        (by rw [ha, hb])).trans
      (Functor.pullbackFiberCompIso'_hom_comp_inv rawProjection (ofModule M) (f i) (f j) a b q
        ha hb (by rw [ha, hb])).symm
  -- The two transition morphisms are replaced by `simp only` and not by `rw`: the goal carries
  -- the quasi-coherence property of the components of a descent datum spelled through
  -- `SheafOfModules.isQuasicoherent` rather than through `qcohProp`, so it is not type-correct at
  -- the transparency used for implicit arguments, and the motive a rewrite would build is
  -- rejected while `simp only`, which rebuilds the goal by congruence, is not.
  simp only [canonicalSchemeTransition f M q a b ha hb, hd]
  exact moduleCanonicalComparison M (f i) (f j) a b q ha hb

private noncomputable def canonicalComparisonNatIso :
    (AlgebraicGeometry.canonicalDescentFunctor (fun i => schemeFunctor.map (f i))).op ⋙
        (schemeDescentRestriction f).op ⋙ moduleDescentFunctor f ≅
      modulesToFiber U ⋙
        (Functor.IsFibered.pullbackPseudofunctor rawProjection).toDescentData f :=
  NatIso.ofComponents (fun M => canonicalComparisonIso f M.unop) (by
    intro M N φ
    ext i
    exact modulePullbackComparison_naturality (f i) φ.unop)

end CanonicalComparison

/-! ### The fppf coverings of the site -/

section DescentFacts

private lemma fppfPrecoverage_hasIsos :
    Scheme.fppfPrecoverage.{u}.HasIsos := by
  constructor
  intro X Y f hf
  apply Scheme.zariskiPrecoverage_le_fppfPrecoverage
  exact Precoverage.mem_coverings_of_isIso f

/-- The cutoff subcategory of the big fppf site creates fibre products, the size of a fibre product
being bounded in terms of the sizes of its two factors. -/
@[instance_reducible]
private noncomputable def cutoffCreatesPullbacks
    (B : AlgebraicGeometry.BigFppfSite.{u}) :
    CreatesLimitsOfShape Limits.WalkingCospan B.inclusion := by
  letI : ObjectProperty.IsClosedUnderIsomorphisms
      (fun X : Scheme.{u} => X.size < B.cutoff) := ⟨by
        intro X Y e h
        rwa [← Scheme.size_congr e]⟩
  letI : ObjectProperty.IsClosedUnderLimitsOfShape
      (fun X : Scheme.{u} => X.size < B.cutoff) Limits.WalkingCospan :=
    .mk' (by
      rintro _ ⟨F, hF⟩
      rw [Scheme.size_congr (Limits.HasLimit.isoOfNatIso (Limits.diagramIsoCospan F))]
      exact Scheme.size_pullback_lt _ _ (hF .left) (hF .right))
  infer_instance

private lemma bigFppfOver_topology_eq_fppf
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    AlgebraicGeometry.BigFppfOver.topology B S hS =
      (Scheme.fppfPrecoverage.comap
        (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).toGrothendieck := by
  let : CreatesLimitsOfShape Limits.WalkingCospan B.inclusion :=
    cutoffCreatesPullbacks B
  let : Limits.HasPullbacks B.Schemes :=
    hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape B.inclusion
  let : B.precoverage.IsStableUnderBaseChange := by
    rw [AlgebraicGeometry.bigFppf_precoverage_eq]
    infer_instance
  let : B.precoverage.HasPullbacks := inferInstance
  rw [AlgebraicGeometry.BigFppfOver.topology, AlgebraicGeometry.BigFppfSite.topology,
    over_toGrothendieck_eq_toGrothendieck_comap_forget]
  rw [AlgebraicGeometry.bigFppf_precoverage_eq, ← Precoverage.comap_comp]

end DescentFacts

/-! ### Conditions (2) and (3) together: the three conditions of Stacks 026F -/

/-- The canonical descent functor of an fpqc covering family of schemes is an equivalence: the two
halves of Stacks 023T.  Full faithfulness is
`AlgebraicGeometry.nonempty_fullyFaithful_canonicalDescentFunctor'` and essential surjectivity is
`AlgebraicGeometry.QuasicoherentDescentData.isEffective_fpqcPrecoverage`, effectivity being
membership in the essential image of that functor. -/
private lemma fpqcDescentFunctor_isEquivalence {T : Scheme.{u}} {I : Type (u + 1)}
    {Y : I → Scheme.{u}} (g : ∀ i, Y i ⟶ T)
    (hg : Presieve.ofArrows Y g ∈ Scheme.fpqcPrecoverage.{u} T) :
    (AlgebraicGeometry.canonicalDescentFunctor g).IsEquivalence := by
  classical
  let e := Classical.choice
    (AlgebraicGeometry.nonempty_fullyFaithful_canonicalDescentFunctor' g hg)
  let := e.full
  let := e.faithful
  let : (AlgebraicGeometry.canonicalDescentFunctor g).EssSurj :=
    ⟨fun D => AlgebraicGeometry.QuasicoherentDescentData.isEffective_fpqcPrecoverage
      ⟨I, Y, g⟩ hg D⟩
  exact {}

/-- The comparison from a fibre of `rawProjection` to the descent data of a family of the site
whose image in schemes is an fpqc covering is an equivalence.

The four comparisons of `canonicalComparisonNatIso` are each an equivalence: the canonical descent
functor by Stacks 023T, `schemeDescentRestriction` and `moduleDescentFunctor` by the two lemmas
above, and `modulesToFiber` by Stacks 04U3. -/
private lemma fiberDescent_isEquivalence_of_fpqc
    {U : AlgebraicGeometry.BigFppfOver B S hS}
    {I : Type (u + 1)} {X : I → AlgebraicGeometry.BigFppfOver B S hS}
    (f : ∀ i, X i ⟶ U)
    (hf : Presieve.ofArrows (fun i => schemeFunctor.obj (X i))
      (fun i => schemeFunctor.map (f i)) ∈ Scheme.fpqcPrecoverage (schemeFunctor.obj U)) :
    ((Functor.IsFibered.pullbackPseudofunctor rawProjection).toDescentData f).IsEquivalence := by
  let := fpqcDescentFunctor_isEquivalence (fun i => schemeFunctor.map (f i)) hf
  let := schemeDescentRestriction_isEquivalence f
  let := moduleDescentFunctor_isEquivalence f
  let := modulesToFiber_isEquivalence U
  have h₀ : ((AlgebraicGeometry.canonicalDescentFunctor
      (fun i => schemeFunctor.map (f i))).op ⋙
      (schemeDescentRestriction f).op ⋙ moduleDescentFunctor f).IsEquivalence := inferInstance
  have h₁ : (modulesToFiber U ⋙
      (Functor.IsFibered.pullbackPseudofunctor rawProjection).toDescentData f).IsEquivalence :=
    (Functor.isEquivalence_iff_of_iso (canonicalComparisonNatIso f)).mp h₀
  exact Functor.isEquivalence_of_comp_left (modulesToFiber U)
    ((Functor.IsFibered.pullbackPseudofunctor rawProjection).toDescentData f)

/-- Mathlib's stack condition for the pullback pseudofunctor of `rawProjection`, which is
conditions (2) and (3) of Stacks 026F by `isStack_pullbackPseudofunctor_iff`.

`CategoryTheory.Pseudofunctor.IsStack.of_precoverage` reduces the quantification over covering
sieves to one over the covering families of the comparison of Mathlib's fppf precoverage along the
functor to schemes, whose index types lie in `Type (u + 1)`. -/
private lemma qcohPullbackPseudofunctor_isStack
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    (Functor.IsFibered.pullbackPseudofunctor
      (rawProjection (B := B) (S := S) (hS := hS))).IsStack
      ((Scheme.fppfPrecoverage.comap
        (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).toGrothendieck) := by
  classical
  let p := rawProjection (B := B) (S := S) (hS := hS)
  let : p.IsFibered := isFibered_rawProjection
  let : Scheme.fppfPrecoverage.{u}.HasIsos := fppfPrecoverage_hasIsos
  let : CreatesLimitsOfShape Limits.WalkingCospan B.inclusion :=
    cutoffCreatesPullbacks B
  let : Limits.HasPullbacks B.Schemes :=
    hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape B.inclusion
  let : Limits.HasPullbacks (AlgebraicGeometry.BigFppfOver B S hS) := inferInstance
  let : Limits.PreservesLimitsOfShape Limits.WalkingCospan
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS) :=
    Limits.comp_preservesLimitsOfShape _ _
  let K := Scheme.fppfPrecoverage.comap
    (AlgebraicGeometry.BigFppfOver.toScheme B S hS)
  let : K.HasIsos := inferInstance
  let : K.IsStableUnderBaseChange := inferInstance
  let : K.IsStableUnderComposition := inferInstance
  apply Pseudofunctor.IsStack.of_precoverage
  intro V R hR
  obtain ⟨I, X, f, rfl⟩ := R.exists_eq_ofArrows
  apply (Pseudofunctor.isStackFor_ofArrows_iff _ f).2
  apply fiberDescent_isEquivalence_of_fpqc f
  apply Scheme.fppfPrecoverage_le_fpqcPrecoverage
  simpa only [K, Precoverage.mem_comap_iff, Presieve.map_ofArrows] using hR

/-! ### Stacks 03YM -/

/-- **Stacks 03YM.**  The projection `p : 𝒬𝒞oh ⟶ (Sch/S)_fppf` from quasi-coherent modules on the
schemes of the big fppf site over `S` to that site satisfies the three conditions of Stacks 026F:
it is a fibred category, the presheaves `Mor(x, y)` of Stacks 02ZB on each slice of the site are
sheaves, and every descent datum along a covering sieve is effective.

The three conditions are the three fields of `CategoryTheory.Functor.IsStack`.  Condition (1) is
the existence of the cartesian lifts given by the units of the pullback–pushforward adjunction,
and conditions (2) and (3) are Mathlib's stack condition for the pullback pseudofunctor of `p`
(`CategoryTheory.Functor.isStack_pullbackPseudofunctor_iff`), hence the statement that the
comparison from each fibre to the descent data of each fppf covering family is an equivalence.
That comparison is identified with the canonical descent functor of Stacks 023D on schemes
(`canonicalComparisonNatIso`), which is an equivalence by the two halves of Stacks 023T: full
faithfulness `AlgebraicGeometry.nonempty_fullyFaithful_canonicalDescentFunctor'` and effectivity
`AlgebraicGeometry.QuasicoherentDescentData.isEffective_fpqcPrecoverage`, both of which hold for
an arbitrary fpqc covering family, fppf coverings being fpqc coverings. -/
@[stacks 03YM, sga "1 VIII 1.1" "special case", sga "1 VIII 1.3" "special case"]
public theorem projection_isStack (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) :
    Functor.IsStack (projection (B := B) (S := S) (hS := hS))
      (AlgebraicGeometry.BigFppfOver.topology B S hS) := by
  have hp := qcohPullbackPseudofunctor_isStack B S hS
  rw [← bigFppfOver_topology_eq_fppf B S hS] at hp
  rw [← rawProjection_eq_projection]
  exact (Functor.isStack_pullbackPseudofunctor_iff
    (rawProjection (B := B) (S := S) (hS := hS))
    (AlgebraicGeometry.BigFppfOver.topology B S hS)).1 hp

end Stacks.QCoh

end
