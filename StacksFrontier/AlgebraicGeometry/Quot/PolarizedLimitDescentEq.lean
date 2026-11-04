module

public import StacksFrontier.AlgebraicGeometry.GenericFlatness.ImageBaseChange
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Relative
public import StacksFrontier.AlgebraicGeometry.ModuleDescent.InvertibleInput
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.ReflectIso
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedLimitDescent
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedStageBaseChange
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedStackUnconditional
public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingStageDescent

/-!
# Descent of equalities of vertical morphisms for the stack of polarized proper schemes

Over the limit of a cofiltered inverse system of affine schemes, two vertical morphisms of
polarized families at a finite stage which agree after base change to the limit already agree
after base change to a later stage. This is the descent condition of Stacks 07XL which makes the
comparison functor `colim 𝒫olarized_{Tᵢ} ⥤ 𝒫olarized_T` faithful.

## Main results

* `AlgebraicGeometry.descentEq_polarizedSliceProjection`: the condition
  `Deformation.Artin.DescentEq` for `𝒫olarized`.
* `AlgebraicGeometry.faithful_colimitComparison_polarized`: the comparison functor of
  Stacks 07XL for `𝒫olarized` is faithful.
* `AlgebraicGeometry.exists_stage_snd_comp_eq`: **Stacks 01ZM (3)** for two morphisms of
  finitely presented schemes over a stage, in the orientation the inverse systems of base
  changes use.
* `AlgebraicGeometry.exists_stage_pullbackDiagram_map_eq`: **Stacks 01ZR (3)** along the inverse
  system of base changes of a scheme over a stage.
* `AlgebraicGeometry.isHomLift_sliceAtTerminal`: lying over a morphism of base objects is
  unchanged by reindexing the base category to its slice at a terminal object.

## Implementation notes

A vertical morphism of polarized families carries two pieces of data, the map of total spaces and
the comparison of polarizations, and the second is typed through the first. The two are therefore
descended in succession: Stacks 01ZM (3) first makes the two maps of total spaces agree after base
change to a stage, which makes the two comparisons of polarizations parallel morphisms of finitely
presented modules on the total space of that stage; Stacks 01ZR (3), applied to the inverse system
of base changes of that total space indexed by the objects of the index category over the stage,
then makes them agree after one further transition morphism. The index object chosen for the
second step is the very object of that over category which the first step produced, so the module
descent runs on the nose over the total space the first step produced.

Equality of morphisms of polarized families is equality of the base maps and of the maps of total
spaces together with a heterogeneous equality of the comparisons of polarizations. The two
lemmas `AlgebraicGeometry.PolarizedFamily.Hom.comp_eq_of_pullback_lineBundleIso_heq` and
`AlgebraicGeometry.PolarizedFamily.Hom.pullback_lineBundleIso_heq_of_comp_eq` convert between that
heterogeneous equality, for a composite with a fixed morphism, and an equality of pullbacks of the
comparisons; that is where the bookkeeping is confined.

## References

* [Stacks Project, Tag 0D43](https://stacks.math.columbia.edu/tag/0D43)
* [Stacks Project, Tag 07XL](https://stacks.math.columbia.edu/tag/07XL)
* [Stacks Project, Tag 01ZM](https://stacks.math.columbia.edu/tag/01ZM)
* [Stacks Project, Tag 01ZR](https://stacks.math.columbia.edu/tag/01ZR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-! ### Two morphisms of polarized families with the same underlying maps -/

namespace PolarizedFamily

variable {B : BigFppfSite.{u}}

/-- The comparison of polarizations of a composite, written out. -/
private theorem comp_lineBundleIso {x y z : PolarizedFamily B} (η : z ⟶ x) (A : x ⟶ y) :
    (η ≫ A).lineBundleIso =
      (Scheme.Modules.pullbackComp η.totalMap A.totalMap).symm.app y.lineBundle ≪≫
        (Scheme.Modules.pullback η.totalMap).mapIso A.lineBundleIso ≪≫ η.lineBundleIso := rfl

/-- Two parallel morphisms of polarized families with the same base map and the same map of
total spaces become equal after precomposition with `η` as soon as their comparisons of
polarizations do so after pullback along the map of total spaces of `η`. -/
theorem Hom.comp_eq_of_pullback_lineBundleIso_heq {x y z : PolarizedFamily B}
    {A A' : x ⟶ y} (η : z ⟶ x) (hb : A.baseMap = A'.baseMap) (ht : A.totalMap = A'.totalMap)
    (h : (Scheme.Modules.pullback η.totalMap).map A.lineBundleIso.hom ≍
      (Scheme.Modules.pullback η.totalMap).map A'.lineBundleIso.hom) :
    η ≫ A = η ≫ A' := by
  obtain ⟨b, t, cc, j⟩ := A
  obtain ⟨b', t', cc', j'⟩ := A'
  obtain rfl : b = b' := hb
  obtain rfl : t = t' := ht
  obtain rfl : cc = cc' := rfl
  refine Hom.ext rfl rfl (heq_of_eq (Iso.ext ?_))
  rw [comp_lineBundleIso, comp_lineBundleIso]
  simp only [Iso.trans_hom, Functor.mapIso_hom]
  rw [eq_of_heq h]

/-- The converse: if two parallel morphisms of polarized families with the same base map and the
same map of total spaces agree after precomposition with `η`, then their comparisons of
polarizations agree after pullback along the map of total spaces of `η`. -/
theorem Hom.pullback_lineBundleIso_heq_of_comp_eq {x y z : PolarizedFamily B}
    {A A' : x ⟶ y} (η : z ⟶ x) (hb : A.baseMap = A'.baseMap) (ht : A.totalMap = A'.totalMap)
    (h : η ≫ A = η ≫ A') :
    (Scheme.Modules.pullback η.totalMap).map A.lineBundleIso.hom ≍
      (Scheme.Modules.pullback η.totalMap).map A'.lineBundleIso.hom := by
  obtain ⟨b, t, cc, j⟩ := A
  obtain ⟨b', t', cc', j'⟩ := A'
  obtain rfl : b = b' := hb
  obtain rfl : t = t' := ht
  obtain rfl : cc = cc' := rfl
  refine heq_of_eq ?_
  have hh0 := heq_lineBundleIso h
  have hh := congrArg Iso.hom (eq_of_heq hh0)
  rw [comp_lineBundleIso, comp_lineBundleIso] at hh
  simp only [Iso.trans_hom, Functor.mapIso_hom] at hh
  exact (cancel_mono η.lineBundleIso.hom).1 ((cancel_epi _).1 hh)

end PolarizedFamily

/-! ### Elementary transport lemmas -/

/-- A heterogeneous equality of morphisms with a common target is an equality after transporting
the source along the equality of sources. -/
theorem heq_iff_eq_eqToHom_comp {C : Type*} [Category C] {a a' b : C} (h : a = a')
    {f : a ⟶ b} {g : a' ⟶ b} : f ≍ g ↔ f = eqToHom h ≫ g := by
  subst h; simp

/-- Pulling back morphisms of modules along an isomorphism is injective. -/
theorem pullback_map_injective_of_isIso {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f]
    {F G : Y.Modules} {α β : F ⟶ G}
    (h : (Scheme.Modules.pullback f).map α = (Scheme.Modules.pullback f).map β) : α = β := by
  have h2 := congrArg (Scheme.Modules.pullback (inv f)).map h
  rw [Stacks.AlgebraicGeometry.ModuleLimits.pullback_map_comp_eq_iff (inv f) f (𝟙 Y)
    (by simp)] at h2
  exact Stacks.AlgebraicGeometry.ModuleLimits.map_eq_of_natIso
    (Scheme.Modules.pullbackId Y) h2

/-- A morphism lying over a morphism of base objects lies over the corresponding morphism of the
slice of the base category at a terminal object. -/
theorem isHomLift_sliceAtTerminal {𝒮 : Type*} [Category 𝒮] {C : Type*} [Category C]
    {T : C} {p : 𝒮 ⥤ C} (hT : IsTerminal T) {V W : Over T} {z w : 𝒮} (f : V ⟶ W) (φ : z ⟶ w)
    (h : p.IsHomLift f.left φ) : (p.sliceAtTerminal hT).IsHomLift f φ := by
  have := h
  refine IsHomLift.of_fac' _ f φ
    (p.sliceAtTerminal_obj_eq hT (IsHomLift.domain_eq p f.left φ))
    (p.sliceAtTerminal_obj_eq hT (IsHomLift.codomain_eq p f.left φ)) ?_
  apply Over.OverMorphism.ext
  rw [Over.comp_left, Over.comp_left, Over.eqToHom_left, Over.eqToHom_left,
    Functor.sliceAtTerminal_map_left]
  exact IsHomLift.fac' p f.left φ

/-! ### Two geometric descent steps, at the level of schemes and modules -/

/-- Pulling back morphisms of modules along a morphism is injective on equalities as soon as the
morphism becomes an isomorphism after one further precomposition. -/
theorem pullback_map_eq_of_comp_isIso {W Z X : Scheme.{u}} (q : W ⟶ Z) (g : Z ⟶ X)
    (pi : W ⟶ X) (hpi : q ≫ g = pi) [IsIso q] {F G : X.Modules} (α β : F ⟶ G)
    (h : (Scheme.Modules.pullback pi).map α = (Scheme.Modules.pullback pi).map β) :
    (Scheme.Modules.pullback g).map α = (Scheme.Modules.pullback g).map β :=
  pullback_map_injective_of_isIso q
    ((Stacks.AlgebraicGeometry.ModuleLimits.pullback_map_comp_eq_iff q g pi hpi α β).2 h)

/-- **Stacks 01ZM (3) for two morphisms over a stage of a cofiltered system of affine schemes.**
Two morphisms of finitely presented schemes over a stage which agree after base change to the
limit agree after base change to some later stage. -/
theorem exists_stage_snd_comp_eq {I : Type u} [Category.{u} I] [IsCofiltered I]
    (DS : I ⥤ Scheme.{u}) [∀ j : I, IsAffine (DS.obj j)] (cS : Cone DS) (hcS : IsLimit cS)
    (i : I) {Xi Yi T : Scheme.{u}} (fi : Xi ⟶ DS.obj i) (gi : Yi ⟶ DS.obj i)
    (hfi : FinitePresentation fi) (hgi : FinitePresentation gi)
    (a a' : Xi ⟶ Yi) (ha : a ≫ gi = fi) (ha' : a' ≫ gi = fi)
    {q : T ⟶ Xi} {t : T ⟶ cS.pt} (hq : IsPullback q t fi (cS.π.app i))
    (hqa : q ≫ a = q ≫ a') :
    ∃ (k : I) (e : k ⟶ i),
      pullback.snd (DS.map e) fi ≫ a = pullback.snd (DS.map e) fi ≫ a' := by
  have hAff : ∀ {j k : I} (e : j ⟶ k), IsAffineHom (DS.map e) := fun _ => inferInstance
  have hCpt : ∀ j : I, CompactSpace (DS.obj j) := fun _ => inferInstance
  have hQS : ∀ j : I, QuasiSeparatedSpace (DS.obj j) := fun _ => inferInstance
  have hpre : (Over.pullback (cS.π.app i)).map
        (Over.homMk a ha : (Over.mk fi : Over (DS.obj i)) ⟶ Over.mk gi) =
      (Over.pullback (cS.π.app i)).map
        (Over.homMk a' ha' : (Over.mk fi : Over (DS.obj i)) ⟶ Over.mk gi) := by
    refine Over.OverMorphism.ext (pullback.hom_ext ?_ ?_)
    · rw [Stacks.GenericFlatness.overPullback_map_left_fst,
        Stacks.GenericFlatness.overPullback_map_left_fst]
      have h3 : hq.isoPullback.inv ≫ q = pullback.fst fi (cS.π.app i) :=
        (congrArg (fun z => hq.isoPullback.inv ≫ z) hq.isoPullback_hom_fst.symm).trans
          (Iso.inv_hom_id_assoc _ _)
      simp only [Over.homMk_left, Over.mk_hom]
      rw [← h3, Category.assoc, Category.assoc, hqa]
    · rw [Stacks.GenericFlatness.overPullback_map_left_snd,
        Stacks.GenericFlatness.overPullback_map_left_snd]
  obtain ⟨k, e, hstage⟩ := eventually_eq_of_baseChange_eq DS cS hcS i (Over.mk fi) (Over.mk gi)
    hfi hgi (Over.homMk a ha) (Over.homMk a' ha') hpre
  refine ⟨k, e, ?_⟩
  have h4 : Over.Hom.left ((Over.pullback (DS.map e)).map
          (Over.homMk a ha : (Over.mk fi : Over (DS.obj i)) ⟶ Over.mk gi)) ≫
        pullback.fst (Over.mk gi : Over (DS.obj i)).hom (DS.map e) =
      Over.Hom.left ((Over.pullback (DS.map e)).map
          (Over.homMk a' ha' : (Over.mk fi : Over (DS.obj i)) ⟶ Over.mk gi)) ≫
        pullback.fst (Over.mk gi : Over (DS.obj i)).hom (DS.map e) := by
    rw [hstage]
  rw [Stacks.GenericFlatness.overPullback_map_left_fst,
    Stacks.GenericFlatness.overPullback_map_left_fst] at h4
  have h5 : pullback.fst fi (DS.map e) ≫ a = pullback.fst fi (DS.map e) ≫ a' := by
    simpa using h4
  rw [← pullbackSymmetry_hom_comp_fst, Category.assoc, Category.assoc, h5]

/-- **Stacks 01ZR (3) along the system of base changes of a scheme over a stage.** Two parallel
morphisms of finitely presented modules on the base change of `fi` to a stage whose pullbacks to
the base change to the limit agree already agree after one further transition morphism. -/
theorem exists_stage_pullbackDiagram_map_eq {I : Type u} [Category.{u} I]
    [IsCofiltered I] (DS : I ⥤ Scheme.{u}) [∀ j : I, IsAffine (DS.obj j)] (cS : Cone DS)
    (hcS : IsLimit cS) (i k₁ : I) (e₁ : k₁ ⟶ i) {Xi : Scheme.{u}} (fi : Xi ⟶ DS.obj i)
    (hXi : CompactSpace Xi)
    (F G : ((pullbackDiagram DS i fi).obj (Over.mk e₁)).Modules)
    (hF : F.IsFinitePresentation) (hG : G.IsFinitePresentation)
    (α β : F ⟶ G)
    (h : (Scheme.Modules.pullback ((pullbackCone DS cS i fi).π.app (Over.mk e₁))).map α =
      (Scheme.Modules.pullback ((pullbackCone DS cS i fi).π.app (Over.mk e₁))).map β) :
    ∃ (j₂ : Over i) (ee : j₂ ⟶ Over.mk e₁),
      (Scheme.Modules.pullback ((pullbackDiagram DS i fi).map ee)).map α =
        (Scheme.Modules.pullback ((pullbackDiagram DS i fi).map ee)).map β := by
  have hAff : ∀ {j k : I} (e : j ⟶ k), IsAffineHom (DS.map e) := fun _ => inferInstance
  have hEaff : ∀ {j k : Over i} (gg : j ⟶ k), IsAffineHom ((pullbackDiagram DS i fi).map gg) :=
    fun gg => isAffineHom_pullbackDiagram_map _ i fi gg (hAff gg.left)
  have hXi' := hXi
  have h0 : QuasiCompact (pullback.snd (DS.map (Over.mk e₁).hom) fi) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @QuasiCompact)
      (IsPullback.of_hasPullback (DS.map (Over.mk e₁).hom) fi) inferInstance
  have hEc : CompactSpace ((pullbackDiagram DS i fi).obj (Over.mk e₁)) :=
    @QuasiCompact.compactSpace_of_compactSpace _ _
      (pullback.snd (DS.map (Over.mk e₁).hom) fi) h0 hXi
  have hF' := hF
  have hG' := hG
  exact Stacks.AlgebraicGeometry.ModuleLimits.exists_pullback_map_eq_of_isLimit'
    (pullbackDiagram DS i fi) (pullbackCone DS cS i fi)
    (isLimitPullbackCone DS cS hcS i fi) (Over.mk e₁) F G α β h

/-! ### Descent of equalities of vertical morphisms -/

/-- The base map of a morphism of polarized families lying over `g` is the underlying map of `g`
up to the identifications of the bases. -/
private theorem baseMap_eq_eqToHom_comp_left_of_isHomLift {B : BigFppfSite.{u}} {S : Scheme.{u}}
    {hS : B.Contains S} (hT : IsTerminal (B.obj hS)) {V W : BigFppfOver B S hS}
    {x y : PolarizedFamily B} (g : V ⟶ W) (φ : x ⟶ y)
    (h : (polarizedSliceProjection B hS hT).IsHomLift g φ) (hx : x.base = V.left)
    (hy : y.base = W.left) : φ.baseMap = eqToHom hx ≫ g.left ≫ eqToHom hy.symm := by
  have h2 := congrArg Over.Hom.left (IsHomLift.fac' (polarizedSliceProjection B hS hT) g φ)
  rw [Over.comp_left, Over.comp_left, Over.eqToHom_left, Over.eqToHom_left] at h2
  exact h2.symm ▸ rfl

/-- **Descent of equalities of vertical morphisms for `𝒫olarized`.** Over the limit of a cofiltered
inverse system of affine schemes over the terminal base, two vertical morphisms of polarized
families at a stage which agree after base change to the limit agree after base change to a later
stage. -/
theorem descentEq_polarizedSliceProjection (B : BigFppfSite.{u}) {S : Scheme.{u}}
    (hS : B.Contains S) (hT : IsTerminal (B.obj hS)) {I : Type u} [Category.{u} I]
    [IsCofiltered I] (D : I ⥤ BigAffineFppf B S hS) (c : Cone D)
    (hc : IsLimit ((BigAffineFppf.toScheme B S hS).mapCone c)) :
    Deformation.Artin.DescentEq (polarizedSliceProjection B hS hT)
      (D ⋙ BigAffineFppf.inclusion B S hS) ((BigAffineFppf.inclusion B S hS).mapCone c) := by
  intro i xi yi x
  obtain ⟨⟨xib, xit, xitb, xipr, xifl, xifp, xiL, xiLi, xiLa⟩, hxi⟩ := xi
  obtain ⟨⟨yib, yit, yitb, yipr, yifl, yifp, yiL, yiLi, yiLa⟩, hyi⟩ := yi
  obtain ⟨⟨xb, xt, xtb, xpr, xfl, xfp, xL, xLi, xLa⟩, hx⟩ := x
  obtain rfl : xib = ((D ⋙ BigAffineFppf.inclusion B S hS).obj i).left :=
    congrArg Comma.left hxi
  obtain rfl : yib = ((D ⋙ BigAffineFppf.inclusion B S hS).obj i).left :=
    congrArg Comma.left hyi
  obtain rfl : xb = ((BigAffineFppf.inclusion B S hS).mapCone c).pt.left :=
    congrArg Comma.left hx
  intro δ hδ ψ ψ' hψ hψ' hδψ
  have hδi := hδ
  have hψi := hψ
  have hψi' := hψ'
  have hδb : δ.baseMap = (((BigAffineFppf.inclusion B S hS).mapCone c).π.app i).left := by
    simpa using baseMap_eq_eqToHom_comp_left_of_isHomLift hT _ δ hδ rfl rfl
  have hψb : ψ.baseMap = 𝟙 _ := by
    simpa using baseMap_eq_eqToHom_comp_left_of_isHomLift hT _ ψ hψ rfl rfl
  have hψb' : ψ'.baseMap = 𝟙 _ := by
    simpa using baseMap_eq_eqToHom_comp_left_of_isHomLift hT _ ψ' hψ' rfl rfl
  let xiF : PolarizedFamily B :=
    { base := ((D ⋙ BigAffineFppf.inclusion B S hS).obj i).left, total := xit, toBase := xitb,
      proper := xipr, flat := xifl, finitePresentation := xifp, lineBundle := xiL,
      invertible := xiLi, relativelyAmple := xiLa }
  let yiF : PolarizedFamily B :=
    { base := ((D ⋙ BigAffineFppf.inclusion B S hS).obj i).left, total := yit, toBase := yitb,
      proper := yipr, flat := yifl, finitePresentation := yifp, lineBundle := yiL,
      invertible := yiLi, relativelyAmple := yiLa }
  let xF : PolarizedFamily B :=
    { base := ((BigAffineFppf.inclusion B S hS).mapCone c).pt.left, total := xt, toBase := xtb,
      proper := xpr, flat := xfl, finitePresentation := xfp, lineBundle := xL,
      invertible := xLi, relativelyAmple := xLa }
  have hAffD : ∀ j : I, IsAffine ((D ⋙ BigAffineFppf.toScheme B S hS).obj j) :=
    fun j => BigAffineFppf.isAffine_toScheme_obj B S hS (D.obj j)
  have hAff : ∀ {j k : I} (e : j ⟶ k),
      IsAffineHom ((D ⋙ BigAffineFppf.toScheme B S hS).map e) := fun _ => inferInstance
  have hCpt : ∀ j : I, CompactSpace ((D ⋙ BigAffineFppf.toScheme B S hS).obj j) :=
    fun _ => inferInstance
  have hQS : ∀ j : I, QuasiSeparatedSpace ((D ⋙ BigAffineFppf.toScheme B S hS).obj j) :=
    fun _ => inferInstance
  have hδmap : B.inclusion.map δ.baseMap =
      ((BigAffineFppf.toScheme B S hS).mapCone c).π.app i := by rw [hδb]; rfl
  have δcart : IsPullback δ.totalMap xtb xitb
      (((BigAffineFppf.toScheme B S hS).mapCone c).π.app i) := by
    rw [← hδmap]; exact δ.cartesian
  have htot : δ.totalMap ≫ ψ.totalMap = δ.totalMap ≫ ψ'.totalMap := by
    simpa using congrArg PolarizedFamily.Hom.totalMap hδψ
  have hψw : ψ.totalMap ≫ yitb = xitb := by
    have h := ψ.cartesian.w
    rw [hψb, B.inclusion.map_id] at h
    simpa using h
  have hψw' : ψ'.totalMap ≫ yitb = xitb := by
    have h := ψ'.cartesian.w
    rw [hψb', B.inclusion.map_id] at h
    simpa using h
  obtain ⟨k₁, e₁, hsndψ⟩ := exists_stage_snd_comp_eq
    (D ⋙ BigAffineFppf.toScheme B S hS) ((BigAffineFppf.toScheme B S hS).mapCone c) hc i
    xitb yitb xifp yifp ψ.totalMap ψ'.totalMap hψw hψw' δcart htot
  let xk₁ : PolarizedFamily B :=
    xiF.stageBaseChange ((D ⋙ BigAffineFppf.inclusion B S hS).map e₁).left
  let dx₁ : xk₁ ⟶ xiF :=
    xiF.stageBaseChangeHom ((D ⋙ BigAffineFppf.inclusion B S hS).map e₁).left
  have hAb : (dx₁ ≫ ψ).baseMap = (dx₁ ≫ ψ').baseMap := by
    show dx₁.baseMap ≫ ψ.baseMap = dx₁.baseMap ≫ ψ'.baseMap
    rw [hψb, hψb']
  have hAt : (dx₁ ≫ ψ).totalMap = (dx₁ ≫ ψ').totalMap := hsndψ
  have hcomm1 : (((BigAffineFppf.inclusion B S hS).mapCone c).π.app k₁).left ≫
      ((D ⋙ BigAffineFppf.inclusion B S hS).map e₁).left = δ.baseMap := by
    rw [hδb, ← Over.comp_left]
    exact congrArg Over.Hom.left (((BigAffineFppf.inclusion B S hS).mapCone c).w e₁)
  obtain ⟨δk₁, hδk₁fac, hδk₁base, hδk₁tot, hδk₁bas⟩ :
      ∃ z : xF ⟶ xk₁, z ≫ dx₁ = δ ∧
        z.baseMap = (((BigAffineFppf.inclusion B S hS).mapCone c).π.app k₁).left ∧
        z.totalMap ≫ dx₁.totalMap = δ.totalMap ∧
        z.totalMap ≫ xk₁.toBase = xtb ≫ B.inclusion.map
          (((BigAffineFppf.inclusion B S hS).mapCone c).π.app k₁).left :=
    ⟨PolarizedFamily.fillIn dx₁ δ
        (((BigAffineFppf.inclusion B S hS).mapCone c).π.app k₁).left hcomm1,
      PolarizedFamily.fillIn_comp dx₁ δ _ hcomm1, rfl,
      PolarizedFamily.fillInTotalMap_comp_totalMap dx₁ δ _ hcomm1,
      PolarizedFamily.fillInTotalMap_comp_toBase dx₁ δ _ hcomm1⟩
  have hδk₁A : δk₁ ≫ (dx₁ ≫ ψ) = δk₁ ≫ (dx₁ ≫ ψ') := by
    rw [← Category.assoc, ← Category.assoc, hδk₁fac, hδψ]
  have hheq := PolarizedFamily.Hom.pullback_lineBundleIso_heq_of_comp_eq δk₁ hAb hAt hδk₁A
  have hobj : (Scheme.Modules.pullback (dx₁ ≫ ψ).totalMap).obj yiF.lineBundle =
      (Scheme.Modules.pullback (dx₁ ≫ ψ').totalMap).obj yiF.lineBundle :=
    congrArg (fun m => (Scheme.Modules.pullback m).obj yiF.lineBundle) hAt
  have hαβ : (Scheme.Modules.pullback δk₁.totalMap).map (dx₁ ≫ ψ).lineBundleIso.hom =
      (Scheme.Modules.pullback δk₁.totalMap).map
        (eqToHom hobj ≫ (dx₁ ≫ ψ').lineBundleIso.hom) := by
    rw [Functor.map_comp, eqToHom_map]
    exact (heq_iff_eq_eqToHom_comp _).1 hheq
  have δcartf : IsPullback xtb δ.totalMap
      (((BigAffineFppf.toScheme B S hS).mapCone c).π.app i) xitb := δcart.flip
  have hπ1 : (pullbackCone (D ⋙ BigAffineFppf.toScheme B S hS)
        ((BigAffineFppf.toScheme B S hS).mapCone c) i xitb).π.app (Over.mk e₁) ≫
        pullback.fst ((D ⋙ BigAffineFppf.toScheme B S hS).map (Over.mk e₁).hom) xitb =
      pullback.fst (((BigAffineFppf.toScheme B S hS).mapCone c).π.app i) xitb ≫
        ((BigAffineFppf.toScheme B S hS).mapCone c).π.app k₁ := by
    rw [pullbackCone_π_app]
    exact pullback.lift_fst _ _ _
  have hπ2 : (pullbackCone (D ⋙ BigAffineFppf.toScheme B S hS)
        ((BigAffineFppf.toScheme B S hS).mapCone c) i xitb).π.app (Over.mk e₁) ≫
        pullback.snd ((D ⋙ BigAffineFppf.toScheme B S hS).map (Over.mk e₁).hom) xitb =
      pullback.snd (((BigAffineFppf.toScheme B S hS).mapCone c).π.app i) xitb := by
    rw [pullbackCone_π_app]
    exact pullback.lift_snd _ _ _
  have hδk₁tm : δk₁.totalMap = δcartf.isoPullback.hom ≫
      (pullbackCone (D ⋙ BigAffineFppf.toScheme B S hS)
        ((BigAffineFppf.toScheme B S hS).mapCone c) i xitb).π.app (Over.mk e₁) := by
    refine pullback.hom_ext
      (f := (D ⋙ BigAffineFppf.toScheme B S hS).map (Over.mk e₁).hom) (g := xitb) ?_ ?_
    · refine hδk₁bas.trans (Eq.symm ?_)
      refine (Category.assoc _ _ _).trans ?_
      refine (congrArg (fun t => δcartf.isoPullback.hom ≫ t) hπ1).trans ?_
      refine (Category.assoc _ _ _).symm.trans ?_
      exact congrArg (fun t => t ≫ ((BigAffineFppf.toScheme B S hS).mapCone c).π.app k₁)
        δcartf.isoPullback_hom_fst
    · refine hδk₁tot.trans (Eq.symm ?_)
      refine (Category.assoc _ _ _).trans ?_
      refine (congrArg (fun t => δcartf.isoPullback.hom ≫ t) hπ2).trans ?_
      exact δcartf.isoPullback_hom_snd
  have hκ : (Scheme.Modules.pullback
        ((pullbackCone (D ⋙ BigAffineFppf.toScheme B S hS)
          ((BigAffineFppf.toScheme B S hS).mapCone c) i xitb).π.app (Over.mk e₁))).map
        (dx₁ ≫ ψ).lineBundleIso.hom =
      (Scheme.Modules.pullback
        ((pullbackCone (D ⋙ BigAffineFppf.toScheme B S hS)
          ((BigAffineFppf.toScheme B S hS).mapCone c) i xitb).π.app (Over.mk e₁))).map
        (eqToHom hobj ≫ (dx₁ ≫ ψ').lineBundleIso.hom) :=
    pullback_map_eq_of_comp_isIso δcartf.isoPullback.hom _ δk₁.totalMap hδk₁tm.symm _ _ hαβ
  have hxitQC : QuasiCompact xitb := xifp.2.1
  have hbaseC : CompactSpace
      (B.inclusion.obj ((D ⋙ BigAffineFppf.inclusion B S hS).obj i).left) := hCpt i
  have hxitC : CompactSpace xit := QuasiCompact.compactSpace_of_compactSpace xitb
  have hxiLfp : xiL.IsFinitePresentation :=
    @AlgebraicGeometry.SheafOfModules.isFinitePresentation_of_isInvertible xit xiL xiLi
  have hyiLfp : yiL.IsFinitePresentation :=
    @AlgebraicGeometry.SheafOfModules.isFinitePresentation_of_isInvertible yit yiL yiLi
  obtain ⟨j₂, ee, hmod⟩ := exists_stage_pullbackDiagram_map_eq
    (D ⋙ BigAffineFppf.toScheme B S hS) ((BigAffineFppf.toScheme B S hS).mapCone c) hc i k₁ e₁
    xitb hxitC _ _
    (Stacks.AlgebraicGeometry.ModuleLimits.isFinitePresentation_pullback _ yiL)
    (Stacks.AlgebraicGeometry.ModuleLimits.isFinitePresentation_pullback _ xiL)
    (dx₁ ≫ ψ).lineBundleIso.hom (eqToHom hobj ≫ (dx₁ ≫ ψ').lineBundleIso.hom) hκ
  let xkF : PolarizedFamily B :=
    xiF.stageBaseChange ((D ⋙ BigAffineFppf.inclusion B S hS).map j₂.hom).left
  let dx : xkF ⟶ xiF :=
    xiF.stageBaseChangeHom ((D ⋙ BigAffineFppf.inclusion B S hS).map j₂.hom).left
  have hcomm2 : ((D ⋙ BigAffineFppf.inclusion B S hS).map ee.left).left ≫
      ((D ⋙ BigAffineFppf.inclusion B S hS).map e₁).left =
      ((D ⋙ BigAffineFppf.inclusion B S hS).map j₂.hom).left := by
    rw [← Over.comp_left, ← Functor.map_comp]
    exact congrArg (fun t => Over.Hom.left ((D ⋙ BigAffineFppf.inclusion B S hS).map t))
      (Over.w ee)
  obtain ⟨dxe, hdxefac, hdxetot, hdxebas⟩ :
      ∃ z : xkF ⟶ xk₁, z ≫ dx₁ = dx ∧ z.totalMap ≫ dx₁.totalMap = dx.totalMap ∧
        z.totalMap ≫ xk₁.toBase = xkF.toBase ≫ B.inclusion.map
          ((D ⋙ BigAffineFppf.inclusion B S hS).map ee.left).left :=
    ⟨PolarizedFamily.fillIn dx₁ dx
        ((D ⋙ BigAffineFppf.inclusion B S hS).map ee.left).left hcomm2,
      PolarizedFamily.fillIn_comp dx₁ dx _ hcomm2,
      PolarizedFamily.fillInTotalMap_comp_totalMap dx₁ dx _ hcomm2,
      PolarizedFamily.fillInTotalMap_comp_toBase dx₁ dx _ hcomm2⟩
  have hEm1 : (pullbackDiagram (D ⋙ BigAffineFppf.toScheme B S hS) i xitb).map ee ≫
        pullback.fst ((D ⋙ BigAffineFppf.toScheme B S hS).map (Over.mk e₁).hom) xitb =
      pullback.fst ((D ⋙ BigAffineFppf.toScheme B S hS).map j₂.hom) xitb ≫
        (D ⋙ BigAffineFppf.toScheme B S hS).map ee.left := by
    rw [pullbackDiagram_map]
    exact pullback.lift_fst _ _ _
  have hEm2 : (pullbackDiagram (D ⋙ BigAffineFppf.toScheme B S hS) i xitb).map ee ≫
        pullback.snd ((D ⋙ BigAffineFppf.toScheme B S hS).map (Over.mk e₁).hom) xitb =
      pullback.snd ((D ⋙ BigAffineFppf.toScheme B S hS).map j₂.hom) xitb := by
    rw [pullbackDiagram_map]
    exact pullback.lift_snd _ _ _
  have hdxetm : dxe.totalMap =
      (pullbackDiagram (D ⋙ BigAffineFppf.toScheme B S hS) i xitb).map ee := by
    refine pullback.hom_ext
      (f := (D ⋙ BigAffineFppf.toScheme B S hS).map (Over.mk e₁).hom) (g := xitb) ?_ ?_
    · exact hdxebas.trans (Eq.symm hEm1)
    · exact hdxetot.trans (Eq.symm hEm2)
  refine ⟨j₂.left, j₂.hom, ⟨xkF, (polarizedProjection B).sliceAtTerminal_obj_eq hT rfl⟩, dx,
    ?_, ?_⟩
  · exact isHomLift_sliceAtTerminal hT ((D ⋙ BigAffineFppf.inclusion B S hS).map j₂.hom) dx
      (Functor.IsHomLift.map (p := polarizedProjection B) dx)
  · rw [← hdxefac, Category.assoc, Category.assoc]
    refine PolarizedFamily.Hom.comp_eq_of_pullback_lineBundleIso_heq dxe hAb hAt ?_
    rw [hdxetm]
    refine (heq_iff_eq_eqToHom_comp
      (congrArg (Scheme.Modules.pullback
        ((pullbackDiagram (D ⋙ BigAffineFppf.toScheme B S hS) i xitb).map ee)).obj hobj)).2
      (hmod.trans ?_)
    exact (Functor.map_comp _ _ _).trans (congrArg (fun t => t ≫ (Scheme.Modules.pullback
      ((pullbackDiagram (D ⋙ BigAffineFppf.toScheme B S hS) i xitb).map ee)).map
        (dx₁ ≫ ψ').lineBundleIso.hom) (eqToHom_map _ hobj))

/-- **Faithfulness of the comparison functor of Stacks 07XL for `𝒫olarized`.** For every
cofiltered inverse system of affine schemes over the terminal base with limit `T`, the canonical
functor `colim 𝒫olarized_{Tᵢ} ⥤ 𝒫olarized_T` is faithful. -/
theorem faithful_colimitComparison_polarized (B : BigFppfSite.{u}) {S : Scheme.{u}}
    (hS : B.Contains S) (hT : IsTerminal (B.obj hS)) {I : Type u} [Category.{u} I]
    [IsCofiltered I] (D : I ⥤ BigAffineFppf B S hS) (c : Cone D)
    (hc : IsLimit ((BigAffineFppf.toScheme B S hS).mapCone c)) :
    letI : (polarizedSliceProjection B hS hT).IsFibered :=
      (polarizedProjection_isFiberedInGroupoids_unconditional.sliceAtTerminal hT).isFibered
    (Deformation.Artin.colimitComparison (polarizedSliceProjection B hS hT)
      (D ⋙ BigAffineFppf.inclusion B S hS)
      ((BigAffineFppf.inclusion B S hS).mapCone c)).Faithful :=
  let : (polarizedSliceProjection B hS hT).IsFibered :=
    (polarizedProjection_isFiberedInGroupoids_unconditional.sliceAtTerminal hT).isFibered
  Deformation.Artin.faithful_of_descentEq (polarizedSliceProjection B hS hT)
    (polarizedProjection_isFiberedInGroupoids_unconditional.sliceAtTerminal hT) _ _
    (descentEq_polarizedSliceProjection B hS hT D c hc)

end AlgebraicGeometry

end
