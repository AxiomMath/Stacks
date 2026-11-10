module

public import StacksFrontier.AlgebraicGeometry.Quot.QuotFunctorSpaceDescent
public import StacksFrontier.AlgebraicGeometry.Quot.QuotientFunctorPoints
public import StacksFrontier.AlgebraicGeometry.Quot.QuotientRestriction
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat.PurityEtaleMorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleAllPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModulePullbackPermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.EtalePermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.FieldFibreEquivalences
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationEtaleDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints

/-!
# Quotients over an algebraic space and their descent along an étale chart

In Situation 082M a morphism `f : X ⟶ Y` of algebraic spaces over a scheme `S` of a big fppf site
is given together with a quasi-coherent `𝒪_X`-module `F`. The morphisms of sheaves from an
algebraic space `T` into the functor of quotients `Q_{F/X/Y}` of Stacks 082P are described as

`Mor(T, Q_{F/X/Y}) = {(h, F_T ⟶ Q) : h : T ⟶ Y, Q quasi-coherent and flat over T}`.

## Main definitions

* `AlgebraicGeometry.Space.QuotientSituation.SpaceQuotient.toMor`: the transformation of a pair,
  restricting it along the chart of every section of `T`.
* `AlgebraicGeometry.Space.QuotientSituation.morBase`: the morphism `T ⟶ Y` of a transformation.
* `AlgebraicGeometry.Space.QuotientSituation.fromMor`: the pair of a transformation, the quotient
  being descended from a surjective étale chart of `T`.
* `AlgebraicGeometry.Space.QuotientSituation.morEquivSpaceQuotientOfDescends`: the
  identification for any condition on quotients stable under restriction to schemes and
  descending along a chart.

## Main results

* `AlgebraicGeometry.Space.QuotientSituation.chartQuotient_compat`: the quotient over a chart
  has equal restrictions to the fibre product of the chart with itself.
* `AlgebraicGeometry.Space.QuotientSituation.morEquivSpaceQuotientOfAlgebraicSpace`:
  the identification above for `Q_{F/X/Y}`.
* `QuotientSituation.morEquivSpaceFinitePresentationQuotientOfAlgebraicSpace`:
  the identification for `Q^{fp}_{F/X/Y}`, for any proofs of its two inputs.
* `QuotientSituation.morEquivSpaceFinitePresentationQuotientOfAlgebraicSpaceUnconditional`:
  the identification for `Q^{fp}_{F/X/Y}`.

## References

* [Stacks Project, Tag 0D3U](https://stacks.math.columbia.edu/tag/0D3U)
* [Stacks Project, Tag 082P](https://stacks.math.columbia.edu/tag/082P)
* [Stacks Project, Tag 0262](https://stacks.math.columbia.edu/tag/0262)
* [Stacks Project, Tag 04W8](https://stacks.math.columbia.edu/tag/04W8)
* [Stacks Project, Tag 05VY](https://stacks.math.columbia.edu/tag/05VY)
* [Stacks Project, Tag 060V](https://stacks.math.columbia.edu/tag/060V)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Space.QuasiCoherentDescent (pairFst pairSnd)

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace QuotientSituation

variable (D : QuotientSituation B S hS) {T : AlgebraicSpaces B S hS}

/-! ### The base change along a chart -/

/-- The morphism of base changes induced by a morphism out of a test scheme commutes with the
projections to the base. -/
theorem spaceChartMap_comp_toSpace (h : T ⟶ D.Y) {U : BigFppfOver B S hS}
    (α : (schemeSpaceFunctor B S hS).obj U ⟶ T) :
    D.spaceChartMap h α ≫ D.spaceBaseToSpace h = D.projection (D.testAt (α ≫ h)) ≫ α :=
  (D.isPullback_spaceBaseChange h).lift_snd _ _ _

/-- A morphism of test schemes followed by the morphism of base changes of a chart is the
morphism of base changes of the composite chart. -/
theorem relativeMap_comp_spaceChartMap (h : T ⟶ D.Y) {U V : BigFppfOver B S hS}
    (α : (schemeSpaceFunctor B S hS).obj U ⟶ T) (α' : (schemeSpaceFunctor B S hS).obj V ⟶ T)
    (m : D.testAt (α' ≫ h) ⟶ D.testAt (α ≫ h))
    (hm : (schemeSpaceFunctor B S hS).map m.left ≫ α = α') :
    D.relativeMap m ≫ D.spaceChartMap h α = D.spaceChartMap h α' := by
  refine (D.isPullback_spaceBaseChange h).hom_ext ?_ ?_
  · rw [Category.assoc, D.spaceChartMap_comp_toSource, D.spaceChartMap_comp_toSource]
    exact baseChangeMap_comp_projection D.f m
  · rw [Category.assoc, D.spaceChartMap_comp_toSpace, D.spaceChartMap_comp_toSpace,
      ← Category.assoc, baseChangeMap_comp_inclusion D.f m, Category.assoc, hm]

/-- **The restriction of a quotient to a chart, pulled back along a morphism of test schemes,
is its restriction to the composite chart.** -/
theorem quotientPullback_spaceQuotientRestrict (hc : ModulePushforwardCoherence B S hS)
    (h : T ⟶ D.Y) {U V : BigFppfOver B S hS}
    (α : (schemeSpaceFunctor B S hS).obj U ⟶ T) (α' : (schemeSpaceFunctor B S hS).obj V ⟶ T)
    (m : D.testAt (α' ≫ h) ⟶ D.testAt (α ≫ h))
    (hm : (schemeSpaceFunctor B S hS).map m.left ≫ α = α')
    (K : Subobject (D.spaceBaseModule h)) :
    D.quotientPullback m (D.spaceQuotientRestrict h α K) = D.spaceQuotientRestrict h α' K :=
  (quotientRestrictAlong_comp D.F hc (D.relativeMap m) (D.spaceChartMap h α)
    (baseChangeMap_comp_projection D.f m) (D.spaceChartMap_comp_toSource h α)
    (by
      rw [Category.assoc, D.spaceChartMap_comp_toSource]
      exact baseChangeMap_comp_projection D.f m)
    K).symm.trans
    (quotientRestrictAlong_congr D.F (D.relativeMap_comp_spaceChartMap h α α' m hm) _
      (D.spaceChartMap_comp_toSource h α') K)

/-! ### The conditions of the source along a chart -/

/-- The restriction of a quotient over `T` to a chart is quasi-coherent and flat over the chart
when the quotient is quasi-coherent and flat over `T`. -/
theorem spaceQuotientRestrict_mem_quotients (h : T ⟶ D.Y) {U : BigFppfOver B S hS}
    (α : (schemeSpaceFunctor B S hS).obj U ⟶ T) (K : Subobject (D.spaceBaseModule h))
    (hK : K ∈ D.spaceQuotients h) :
    D.spaceQuotientRestrict h α K ∈ D.quotients (D.testAt (α ≫ h)) := by
  have := hK.1
  have hpb := isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
    (D.spaceChartMap h α) (cokernel K.arrow) hK.1
  refine ⟨SheafOfModules.IsQuasicoherentOnSite.of_iso
    (D.spaceQuotientRestrictCokernelIso h α K).symm hpb, ?_⟩
  exact IsFlatOver.of_iso B S hS (D.space (D.testAt (α ≫ h))).2
    (D.spaceQuotientRestrictCokernelIso h α K).symm
    (isFlatOver_modulePullback B S hS (D.isPullback_spaceChartMap h α) (cokernel K.arrow) hK.2)

/-! ### From a pair over `T` to a transformation -/

section ToMor

variable {Q : ∀ T : SchemesOver D.Y, Set (Subobject (D.baseChangeModule T))}
  {Qs : ∀ (T' : AlgebraicSpaces B S hS) (h : T' ⟶ D.Y), Set (Subobject (D.spaceBaseModule h))}
  (hres : ∀ {T' : AlgebraicSpaces B S hS} (h : T' ⟶ D.Y) {U : BigFppfOver B S hS}
    (α : (schemeSpaceFunctor B S hS).obj U ⟶ T') (K : Subobject (D.spaceBaseModule h)),
    K ∈ Qs T' h → D.spaceQuotientRestrict h α K ∈ Q (D.testAt (α ≫ h)))

/-- The restriction of a pair over `T` to a chart `α : U ⟶ T`, as an element of the total
presheaf at `U`: the composite `U ⟶ T ⟶ Y` together with the restricted quotient. -/
def spaceQuotientTotal (q : D.SpaceQuotient Qs T) {U : BigFppfOver B S hS}
    (α : (schemeSpaceFunctor B S hS).obj U ⟶ T) : D.TotalQuotient Q U :=
  ⟨α ≫ q.hom, D.spaceQuotientRestrict q.hom α q.ker, hres q.hom α q.ker q.mem⟩

/-- The morphism to `Y` of the restriction of a pair to a chart `α` is `α ≫ q.hom`. -/
@[simp]
theorem spaceQuotientTotal_hom (q : D.SpaceQuotient Qs T) {U : BigFppfOver B S hS}
    (α : (schemeSpaceFunctor B S hS).obj U ⟶ T) :
    (D.spaceQuotientTotal hres q α).hom = α ≫ q.hom :=
  rfl

/-- Equal charts give equal restrictions. -/
theorem spaceQuotientTotal_congr (q : D.SpaceQuotient Qs T) {U : BigFppfOver B S hS}
    {α α' : (schemeSpaceFunctor B S hS).obj U ⟶ T} (e : α = α') :
    D.spaceQuotientTotal hres q α = D.spaceQuotientTotal hres q α' := by
  subst e
  rfl

variable (hc : ModulePushforwardCoherence B S hS)
  (hQ : ∀ {T' T : SchemesOver D.Y} (m : T' ⟶ T) (K : Subobject (D.baseChangeModule T)),
    K ∈ Q T → D.quotientPullback m K ∈ Q T')

/-- **The restriction of a pair to charts is natural in the chart.** -/
theorem totalQuotientFunctor_map_spaceQuotientTotal (q : D.SpaceQuotient Qs T)
    {U V : BigFppfOver B S hS} (α : (schemeSpaceFunctor B S hS).obj U ⟶ T) (g : V ⟶ U) :
    (D.totalQuotientFunctor hc Q hQ).map g.op (D.spaceQuotientTotal hres q α) =
      D.spaceQuotientTotal hres q ((schemeSpaceFunctor B S hS).map g ≫ α) :=
  TotalQuotient.mk_eq_mk (h := (schemeSpaceFunctor B S hS).map g ≫ α ≫ q.hom)
    (D.quotientPullback_spaceQuotientRestrict hc q.hom α ((schemeSpaceFunctor B S hS).map g ≫ α)
      (D.testAtMap g (α ≫ q.hom)) rfl q.ker) _ _

/-- **The transformation determined by a pair over `T`.**  Its value at a section `t` of `T` over
a scheme `V` of the site is the restriction of the pair to the chart `t : V ⟶ T`. -/
def SpaceQuotient.toMor (q : D.SpaceQuotient Qs T) :
    T.obj ⋙ uliftFunctor.{u + 1, u} ⟶ D.totalQuotientFunctor hc Q hQ where
  app W := TypeCat.ofHom fun t ↦
    D.spaceQuotientTotal hres q (ObjectProperty.homMk (yonedaEquiv.symm t.down))
  naturality := by
    intro W W' g
    ext t
    obtain ⟨t⟩ := t
    change D.spaceQuotientTotal hres q (ObjectProperty.homMk (yonedaEquiv.symm (T.obj.map g t))) =
      (D.totalQuotientFunctor hc Q hQ).map g
        (D.spaceQuotientTotal hres q (ObjectProperty.homMk (yonedaEquiv.symm t)))
    exact (D.spaceQuotientTotal_congr hres q
      (ObjectProperty.hom_ext _ (yonedaEquiv_symm_map g t))).trans
      (D.totalQuotientFunctor_map_spaceQuotientTotal hres hc hQ q _ g.unop).symm

/-- The value of `q.toMor` at a section `t` is the restriction of `q` to the chart determined by
`t`. -/
theorem SpaceQuotient.toMor_app (q : D.SpaceQuotient Qs T) {V : BigFppfOver B S hS}
    (t : T.obj.obj (op V)) :
    (q.toMor D hres hc hQ).app (op V) (ULift.up t) =
      D.spaceQuotientTotal hres q (ObjectProperty.homMk (yonedaEquiv.symm t)) :=
  rfl

end ToMor

/-! ### Charts of an algebraic space -/

/-- A surjective étale chart `U ⟶ T` of an algebraic space by a scheme of the site. -/
structure SpaceChart (T : AlgebraicSpaces B S hS) where
  /-- The scheme of the chart. -/
  U : BigFppfOver B S hS
  /-- The chart. -/
  α : (schemeSpaceFunctor B S hS).obj U ⟶ T
  /-- It is étale. -/
  etale : IsEtale B S hS α.hom
  /-- It is surjective. -/
  surjective : IsSurjective B S hS α.hom

/-- Every algebraic space has a surjective étale chart (Stacks 025Y). -/
theorem nonempty_spaceChart (T : AlgebraicSpaces B S hS) : Nonempty (SpaceChart T) := by
  obtain ⟨U, a, hsurj, hetale⟩ := T.property.exists_atlas
  exact ⟨⟨U, ObjectProperty.homMk a, (isEtale_iff_presheaf_of_yoneda B S hS a).2 hetale,
    (surjective_iff_surjective_pointsMap B S hS T.1 T.2 U a).1 hsurj⟩⟩

/-- The fibre product of a chart with a morphism out of a scheme is a scheme of the site, and its
projection to the scheme is a surjective étale morphism of schemes of the site. -/
theorem SpaceChart.exists_isPullback (C : SpaceChart T) {V : BigFppfOver B S hS}
    (β : (schemeSpaceFunctor B S hS).obj V ⟶ T) :
    ∃ (V' : BigFppfOver B S hS) (a : V' ⟶ V) (b : V' ⟶ C.U),
      IsPullback ((schemeSpaceFunctor B S hS).map b) ((schemeSpaceFunctor B S hS).map a) C.α β ∧
        IsEtale B S hS ((schemeSpaceFunctor B S hS).map a).hom ∧
        IsSurjective B S hS ((schemeSpaceFunctor B S hS).map a).hom := by
  have hrel : yoneda.relativelyRepresentable C.α.hom :=
    T.property.diagonal_representable.of_diag C.α.hom
  have hsq := hrel.isPullback' β.hom
  have hsq' : IsPullback ((schemeSpaceFunctor B S hS).map (hrel.fst' β.hom))
      ((schemeSpaceFunctor B S hS).map (hrel.snd β.hom)) C.α β :=
    IsPullback.of_map (ObjectProperty.ι _) (ObjectProperty.hom_ext _ hsq.w) hsq
  refine ⟨_, hrel.snd β.hom, hrel.fst' β.hom, hsq', ?_, ?_⟩
  · exact isEtale_of_isPullback B S hS _ _ C.α β hsq' C.etale
  · exact surjective_pointsMap_of_isPullback B S hS hsq C.surjective

/-- Two charts agreeing after precomposition with morphisms of schemes give equal sections of `T`
on the common source. -/
private theorem map_yonedaEquiv_eq_of_comp_eq {U V W : BigFppfOver B S hS}
    {x : (schemeSpaceFunctor B S hS).obj U ⟶ T} {y : (schemeSpaceFunctor B S hS).obj V ⟶ T}
    {a : W ⟶ U} {b : W ⟶ V}
    (w : (schemeSpaceFunctor B S hS).map a ≫ x = (schemeSpaceFunctor B S hS).map b ≫ y) :
    T.obj.map a.op (yonedaEquiv x.hom) = T.obj.map b.op (yonedaEquiv y.hom) :=
  (yonedaEquiv_naturality x.hom a).trans
    ((congrArg (fun k => yonedaEquiv (k.hom : yoneda.obj W ⟶ T.obj)) w).trans
      (yonedaEquiv_naturality y.hom b).symm)

/-! ### Separation along a surjective étale morphism -/

/-- The morphism of base changes induced by a surjective étale morphism of test schemes is
surjective and étale. -/
theorem isEtale_isSurjective_relativeMap {T' T : SchemesOver D.Y} (m : T' ⟶ T)
    (he : IsEtale B S hS ((schemeSpaceFunctor B S hS).map m.left).hom)
    (hs : IsSurjective B S hS ((schemeSpaceFunctor B S hS).map m.left).hom) :
    IsEtale B S hS (D.relativeMap m).hom ∧ IsSurjective B S hS (D.relativeMap m).hom := by
  have sq := isPullback_baseChangeMap D.f m
  exact ⟨isEtale_of_isPullback B S hS _ _ _ _ sq.flip he,
    surjective_pointsMap_of_isPullback B S hS (AlgebraicSpaces.isPullback_hom B S hS sq.flip) hs⟩

/-- **Restriction of quotients along a surjective étale morphism is injective.** -/
theorem _root_.AlgebraicGeometry.Space.quotientRestrictAlong_injective_of_isEtale
    {A W W' : AlgebraicSpaces B S hS}
    (F : Modules.{u, u} B S hS A.1 A.2) {π : W ⟶ A} {π' : W' ⟶ A} (a : W' ⟶ W)
    (ha : a ≫ π = π') (he : IsEtale B S hS a.hom) (hs : IsSurjective B S hS a.hom) :
    Function.Injective (quotientRestrictAlong F a ha) :=
  quotientRestrictAlong_injective_of_reflects F a ha fun v hv =>
    eq_zero_of_forall_modulePullback_map_eq_zero_of_isFlat B S hS (fun _ : Unit => a)
      (fun _ => isFlat_of_isEtale B S hS he)
      ((isJointlySurjective_const_iff B S hS a.hom).2 hs) v fun _ => hv

/-- Pullback of quotients along a surjective étale morphism of test schemes is injective. -/
theorem quotientPullback_injective {T' T : SchemesOver D.Y} (m : T' ⟶ T)
    (he : IsEtale B S hS ((schemeSpaceFunctor B S hS).map m.left).hom)
    (hs : IsSurjective B S hS ((schemeSpaceFunctor B S hS).map m.left).hom) :
    Function.Injective (D.quotientPullback m) :=
  quotientRestrictAlong_injective_of_isEtale D.F (D.relativeMap m)
    (baseChangeMap_comp_projection D.f m) (D.isEtale_isSurjective_relativeMap m he hs).1
    (D.isEtale_isSurjective_relativeMap m he hs).2

/-! ### From a transformation to a pair over `T` -/

section FromMor

variable {Q : ∀ T : SchemesOver D.Y, Set (Subobject (D.baseChangeModule T))}
  (hc : ModulePushforwardCoherence B S hS)
  (hQ : ∀ {T' T : SchemesOver D.Y} (m : T' ⟶ T) (K : Subobject (D.baseChangeModule T)),
    K ∈ Q T → D.quotientPullback m K ∈ Q T')

/-- **Separation of the total presheaf along a surjective étale morphism.**  Two elements of the
total presheaf at `V` over the same morphism to `Y` agree as soon as their restrictions along a
surjective étale morphism `V' ⟶ V` of schemes of the site agree. -/
theorem totalQuotient_eq_of_map_eq {V V' : BigFppfOver B S hS} (a : V' ⟶ V)
    (he : IsEtale B S hS ((schemeSpaceFunctor B S hS).map a).hom)
    (hs : IsSurjective B S hS ((schemeSpaceFunctor B S hS).map a).hom)
    (q₁ q₂ : D.TotalQuotient Q V) (hh : q₁.hom = q₂.hom)
    (h : (D.totalQuotientFunctor hc Q hQ).map a.op q₁ =
      (D.totalQuotientFunctor hc Q hQ).map a.op q₂) : q₁ = q₂ := by
  obtain ⟨h₁, K₁, m₁⟩ := q₁
  obtain ⟨h₂, K₂, m₂⟩ := q₂
  dsimp only at hh
  subst hh
  have hk :
      D.quotientPullback (D.testAtMap a h₁) K₁ = D.quotientPullback (D.testAtMap a h₁) K₂ := by
    change (⟨(schemeSpaceFunctor B S hS).map a ≫ h₁,
        D.quotientPullback (D.testAtMap a h₁) K₁, hQ _ _ m₁⟩ : D.TotalQuotient Q V') =
      ⟨(schemeSpaceFunctor B S hS).map a ≫ h₁,
        D.quotientPullback (D.testAtMap a h₁) K₂, hQ _ _ m₂⟩ at h
    exact eq_of_heq (TotalQuotient.mk.inj h).2
  exact TotalQuotient.mk_eq_mk (D.quotientPullback_injective (D.testAtMap a h₁) he hs hk) _ _

/-- The kernel of the restriction of an element of the total presheaf, read over an equal
structure morphism, is the pullback of its kernel along the corresponding morphism of test
schemes. -/
theorem kerAt_totalQuotientFunctor_map {U V : BigFppfOver B S hS} (q : D.TotalQuotient Q U)
    {k : (schemeSpaceFunctor B S hS).obj U ⟶ D.Y} (e : q.hom = k) (g : V ⟶ U)
    {φ : (schemeSpaceFunctor B S hS).obj V ⟶ D.Y} (hφ : (schemeSpaceFunctor B S hS).map g ≫ k = φ)
    (e' : ((D.totalQuotientFunctor hc Q hQ).map g.op q).hom = φ) :
    ((D.totalQuotientFunctor hc Q hQ).map g.op q).kerAt e' =
      D.quotientPullback (CostructuredArrow.homMk g hφ : D.testAt φ ⟶ D.testAt k)
        (q.kerAt e) := by
  subst e
  subst hφ
  rfl

variable (v : T.obj ⋙ uliftFunctor.{u + 1, u} ⟶ D.totalQuotientFunctor hc Q hQ)

/-- **The morphism `T ⟶ Y` underlying a transformation into the total presheaf.**  Its value at a
section `t` is the structure morphism of the element at `t`, read as a section of `Y` by the
Yoneda bijection. -/
def morBase : T ⟶ D.Y :=
  ObjectProperty.homMk
    { app := fun W ↦ TypeCat.ofHom fun t ↦ yonedaEquiv ((v.app W (ULift.up t)).hom.hom)
      naturality := by
        intro W W' g
        ext t
        have hnat : v.app W' (ULift.up (T.obj.map g t)) =
            (D.totalQuotientFunctor hc Q hQ).map g (v.app W (ULift.up t)) :=
          types_congr_hom (v.naturality g) (ULift.up t)
        change yonedaEquiv ((v.app W' (ULift.up (T.obj.map g t))).hom.hom) =
          D.Y.obj.map g (yonedaEquiv ((v.app W (ULift.up t)).hom.hom))
        rw [hnat]
        exact (yonedaEquiv_naturality _ g.unop).symm }

/-- The element at a section `t` of `T` lies over the composite of the chart of `t` with the
morphism `T ⟶ Y` of the transformation. -/
theorem morBase_spec {V : BigFppfOver B S hS} (t : T.obj.obj (op V)) :
    (v.app (op V) (ULift.up t)).hom =
      ObjectProperty.homMk (yonedaEquiv.symm t) ≫ D.morBase hc hQ v := by
  refine ObjectProperty.hom_ext _ ?_
  apply yonedaEquiv.injective
  change _ = yonedaEquiv (yonedaEquiv.symm t ≫ (D.morBase hc hQ v).hom)
  rw [yonedaEquiv_comp, Equiv.apply_symm_apply]
  rfl

/-- The section of `T` over the scheme of a chart given by the chart. -/
abbrev SpaceChart.section (C : SpaceChart T) : T.obj.obj (op C.U) := yonedaEquiv C.α.hom

/-- The element of the total presheaf at the chart lies over the chart followed by `T ⟶ Y`. -/
theorem morBase_chart (C : SpaceChart T) :
    (v.app (op C.U) (ULift.up C.section)).hom = C.α ≫ D.morBase hc hQ v :=
  (D.morBase_spec hc hQ v C.section).trans (by
    congr 1
    exact ObjectProperty.hom_ext _ (Equiv.symm_apply_apply yonedaEquiv C.α.hom))

/-- The values of a transformation at two sections with equal restrictions to `W` have equal
restrictions. -/
private theorem map_app_eq_of_map_eq {U V W : BigFppfOver B S hS} (a : W ⟶ U) (b : W ⟶ V)
    {x : T.obj.obj (op U)} {y : T.obj.obj (op V)} (hxy : T.obj.map a.op x = T.obj.map b.op y) :
    (D.totalQuotientFunctor hc Q hQ).map a.op (v.app (op U) (ULift.up x)) =
      (D.totalQuotientFunctor hc Q hQ).map b.op (v.app (op V) (ULift.up y)) :=
  (types_congr_hom (v.naturality a.op) _).symm.trans
    ((congrArg (fun z => v.app (op W) (ULift.up z)) hxy).trans
      (types_congr_hom (v.naturality b.op) _))

/-- The quotient over the chart read off the transformation. -/
def chartQuotient (C : SpaceChart T) :
    Subobject (D.baseChangeModule (D.testAt (C.α ≫ D.morBase hc hQ v))) :=
  (v.app (op C.U) (ULift.up C.section)).kerAt (D.morBase_chart hc hQ v C)

/-- The one-member family of the base change of a chart, over the base change at `T`. -/
abbrev chartFamily (h : T ⟶ D.Y) (C : SpaceChart T) : Unit → AlgebraicSpaces B S hS :=
  fun _ => D.space (D.testAt (C.α ≫ h))

/-- The member of `AlgebraicGeometry.Space.QuotientSituation.chartFamily`. -/
abbrev chartFamilyMap (h : T ⟶ D.Y) (C : SpaceChart T) :
    ∀ i, D.chartFamily h C i ⟶ D.spaceBaseChange h :=
  fun _ => D.spaceChartMap h C.α

/-- The two restrictions of the quotient over the chart to the fibre product of the chart with
itself agree. -/
theorem chartQuotient_compat (C : SpaceChart T) :
    quotientRestrictAlong D.F (pairFst B S hS (D.chartFamily (D.morBase hc hQ v) C)
        (D.chartFamilyMap (D.morBase hc hQ v) C) () ()) rfl (D.chartQuotient hc hQ v C) =
      quotientRestrictAlong D.F (pairSnd B S hS (D.chartFamily (D.morBase hc hQ v) C)
        (D.chartFamilyMap (D.morBase hc hQ v) C) () ())
        (pairSnd_comp_eq _ _ (fun _ => D.spaceChartMap_comp_toSource _ C.α) () ())
        (D.chartQuotient hc hQ v C) := by
  obtain ⟨R, t, s, sq, -, -⟩ := C.exists_isPullback C.α
  have hw : (schemeSpaceFunctor B S hS).map t ≫ C.α ≫ (D.morBase hc hQ v) =
      ((schemeSpaceFunctor B S hS).map s ≫ C.α) ≫ (D.morBase hc hQ v) := by
    rw [← Category.assoc, ← sq.w]
  let sHat : D.testAt (((schemeSpaceFunctor B S hS).map s ≫ C.α) ≫ (D.morBase hc hQ v)) ⟶
      D.testAt (C.α ≫ (D.morBase hc hQ v)) :=
    D.testAtMap s (C.α ≫ (D.morBase hc hQ v))
  let tHat : D.testAt (((schemeSpaceFunctor B S hS).map s ≫ C.α) ≫ (D.morBase hc hQ v)) ⟶
      D.testAt (C.α ≫ (D.morBase hc hQ v)) :=
    CostructuredArrow.homMk t hw
  have hst : D.quotientPullback sHat (D.chartQuotient hc hQ v C) =
      D.quotientPullback tHat (D.chartQuotient hc hQ v C) := by
    have Eqq := map_app_eq_of_map_eq (D := D) hc hQ v s t
      (map_yonedaEquiv_eq_of_comp_eq (x := C.α) (y := C.α) sq.w)
    have e₀ := D.morBase_chart hc hQ v C
    have key : ∀ g : R ⟶ C.U, ((D.totalQuotientFunctor hc Q hQ).map g.op
        (v.app (op C.U) (ULift.up C.section))).hom =
          (schemeSpaceFunctor B S hS).map g ≫ C.α ≫ (D.morBase hc hQ v) := fun g => by
      change (schemeSpaceFunctor B S hS).map g ≫ (v.app (op C.U) (ULift.up C.section)).hom = _
      rw [e₀]
    have es := key s
    have et := (key t).trans hw
    calc D.quotientPullback sHat (D.chartQuotient hc hQ v C)
        = ((D.totalQuotientFunctor hc Q hQ).map s.op
            (v.app (op C.U) (ULift.up C.section))).kerAt es :=
          (D.kerAt_totalQuotientFunctor_map hc hQ _ e₀ s rfl es).symm
      _ = ((D.totalQuotientFunctor hc Q hQ).map t.op
            (v.app (op C.U) (ULift.up C.section))).kerAt et :=
          TotalQuotient.kerAt_congr Eqq es et
      _ = D.quotientPullback tHat (D.chartQuotient hc hQ v C) :=
          D.kerAt_totalQuotientFunctor_map hc hQ _ e₀ t hw et
  have hp : D.relativeMap tHat ≫ D.spaceChartMap (D.morBase hc hQ v) C.α =
      D.relativeMap sHat ≫ D.spaceChartMap (D.morBase hc hQ v) C.α :=
    (D.relativeMap_comp_spaceChartMap (D.morBase hc hQ v) C.α _ tHat sq.w.symm).trans
      (D.relativeMap_comp_spaceChartMap (D.morBase hc hQ v) C.α _ sHat rfl).symm
  have hPB : IsPullback (D.relativeMap sHat) (D.relativeMap tHat)
      (D.spaceChartMap (D.morBase hc hQ v) C.α) (D.spaceChartMap (D.morBase hc hQ v) C.α) := by
    have hout : IsPullback
        (D.projection (D.testAt (((schemeSpaceFunctor B S hS).map s ≫ C.α) ≫ (D.morBase hc hQ v)))
          ≫ (schemeSpaceFunctor B S hS).map t) (D.relativeMap sHat) C.α
          (D.projection (D.testAt (C.α ≫ (D.morBase hc hQ v))) ≫ C.α) :=
      (isPullback_baseChangeMap D.f sHat).flip.paste_horiz sq.flip
    have h1 : D.relativeMap tHat ≫ D.projection (D.testAt (C.α ≫ (D.morBase hc hQ v))) =
        D.projection (D.testAt (((schemeSpaceFunctor B S hS).map s ≫ C.α) ≫ (D.morBase hc hQ v))) ≫
          (schemeSpaceFunctor B S hS).map t :=
      baseChangeMap_comp_inclusion D.f tHat
    have h2 := D.spaceChartMap_comp_toSpace (D.morBase hc hQ v) C.α
    refine (IsPullback.of_right ?_ hp
      (D.isPullback_spaceChartMap (D.morBase hc hQ v) C.α).flip).flip
    rw [h1, h2]
    exact hout
  let e := hPB.isoIsPullback _ _ (AlgebraicSpaces.isPullback_fiberProduct B S hS
    (D.spaceChartMap (D.morBase hc hQ v) C.α) (D.spaceChartMap (D.morBase hc hQ v) C.α))
  have hι₁ : e.hom ≫ pairFst B S hS (D.chartFamily (D.morBase hc hQ v) C)
      (D.chartFamilyMap (D.morBase hc hQ v) C) () () = D.relativeMap sHat :=
    IsPullback.isoIsPullback_hom_fst _ _ hPB _
  have hι₂ : e.hom ≫ pairSnd B S hS (D.chartFamily (D.morBase hc hQ v) C)
      (D.chartFamilyMap (D.morBase hc hQ v) C) () () = D.relativeMap tHat :=
    IsPullback.isoIsPullback_hom_snd _ _ hPB _
  have : IsIso e.hom.hom := (ObjectProperty.ι _).map_isIso e.hom
  have hι0 : e.hom ≫ pairFst B S hS (D.chartFamily (D.morBase hc hQ v) C)
      (D.chartFamilyMap (D.morBase hc hQ v) C) () () ≫
        D.sourceProjection (D.testAt (C.α ≫ (D.morBase hc hQ v))) =
      D.sourceProjection
        (D.testAt (((schemeSpaceFunctor B S hS).map s ≫ C.α) ≫ (D.morBase hc hQ v))) :=
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) hι₁).trans
      (baseChangeMap_comp_projection D.f sHat))
  refine quotientRestrictAlong_injective_of_isEtale D.F e.hom hι0
    (isEtale_of_isIso B S hS e.hom.hom) (bijective_pointsMap_of_isIso B S hS e.hom.hom).2 ?_
  calc _ = quotientRestrictAlong D.F (e.hom ≫ pairFst B S hS (D.chartFamily (D.morBase hc hQ v) C)
          (D.chartFamilyMap (D.morBase hc hQ v) C) () ()) ((Category.assoc _ _ _).trans hι0)
          (D.chartQuotient hc hQ v C) :=
        (quotientRestrictAlong_comp D.F hc _ _ hι0 rfl _ _).symm
    _ = D.quotientPullback sHat (D.chartQuotient hc hQ v C) :=
        quotientRestrictAlong_congr D.F hι₁ _ _ _
    _ = D.quotientPullback tHat (D.chartQuotient hc hQ v C) := hst
    _ = quotientRestrictAlong D.F (e.hom ≫ pairSnd B S hS (D.chartFamily (D.morBase hc hQ v) C)
          (D.chartFamilyMap (D.morBase hc hQ v) C) () ())
          ((Category.assoc _ _ _).trans ((congrArg (e.hom ≫ ·) (pairSnd_comp_eq _ _
            (fun _ => D.spaceChartMap_comp_toSource _ C.α) () ())).trans hι0))
          (D.chartQuotient hc hQ v C) :=
        quotientRestrictAlong_congr D.F hι₂.symm _ _ _
    _ = _ := quotientRestrictAlong_comp D.F hc _ _ hι0 _ _ _

end FromMor

/-! ### The chart is an étale covering -/

/-- The base change of a chart is étale. -/
theorem isEtale_spaceChartMap (h : T ⟶ D.Y) (C : SpaceChart T) :
    IsEtale B S hS (D.spaceChartMap h C.α).hom :=
  isEtale_of_isPullback B S hS _ _ C.α _ (D.isPullback_spaceChartMap h C.α).flip C.etale

/-- The base change of a chart is surjective. -/
theorem isSurjective_spaceChartMap (h : T ⟶ D.Y) (C : SpaceChart T) :
    IsSurjective B S hS (D.spaceChartMap h C.α).hom :=
  surjective_pointsMap_of_isPullback B S hS
    (AlgebraicSpaces.isPullback_hom B S hS (D.isPullback_spaceChartMap h C.α).flip) C.surjective

/-- The base change of a chart is a one-member étale covering of the base change at `T`. -/
theorem isEtaleCovering_chartFamily (h : T ⟶ D.Y) (C : SpaceChart T) :
    IsEtaleCovering B S hS (fun i => (D.chartFamily h C i).1)
      (fun i => (D.chartFamilyMap h C i).hom) where
  target_isAlgebraicSpace := (D.spaceBaseChange h).2
  source_isAlgebraicSpace _ := (D.space _).2
  etale _ := D.isEtale_spaceChartMap h C
  jointly_surjective :=
    (isJointlySurjective_const_iff B S hS (D.spaceChartMap h C.α).hom).2
      (D.isSurjective_spaceChartMap h C)

/-- Restriction of quotients over `T` to a chart is injective. -/
theorem spaceQuotientRestrict_injective (h : T ⟶ D.Y) (C : SpaceChart T) :
    Function.Injective (D.spaceQuotientRestrict h C.α) :=
  quotientRestrictAlong_injective_of_isEtale D.F (D.spaceChartMap h C.α)
    (D.spaceChartMap_comp_toSource h C.α) (D.isEtale_spaceChartMap h C)
    (D.isSurjective_spaceChartMap h C)

/-! ### The identification -/

section Equivalence

variable {Q : ∀ T : SchemesOver D.Y, Set (Subobject (D.baseChangeModule T))}
  {Qs : ∀ (T' : AlgebraicSpaces B S hS) (h : T' ⟶ D.Y), Set (Subobject (D.spaceBaseModule h))}
  (hres : ∀ {T' : AlgebraicSpaces B S hS} (h : T' ⟶ D.Y) {U : BigFppfOver B S hS}
    (α : (schemeSpaceFunctor B S hS).obj U ⟶ T') (K : Subobject (D.spaceBaseModule h)),
    K ∈ Qs T' h → D.spaceQuotientRestrict h α K ∈ Q (D.testAt (α ≫ h)))
  (hc : ModulePushforwardCoherence B S hS)
  (hQ : ∀ {T' T : SchemesOver D.Y} (m : T' ⟶ T) (K : Subobject (D.baseChangeModule T)),
    K ∈ Q T → D.quotientPullback m K ∈ Q T')
  (hQq : ∀ (T' : SchemesOver D.Y) (K : Subobject (D.baseChangeModule T')), K ∈ Q T' →
    (cokernel K.arrow).IsQuasicoherentOnSite)
  (hdesc : ∀ (C : SpaceChart T) (h : T ⟶ D.Y) (K : Subobject (D.spaceBaseModule h)),
    (cokernel K.arrow).IsQuasicoherentOnSite →
      D.spaceQuotientRestrict h C.α K ∈ Q (D.testAt (C.α ≫ h)) → K ∈ Qs T h)
  (v : T.obj ⋙ uliftFunctor.{u + 1, u} ⟶ D.totalQuotientFunctor hc Q hQ)

include hQq in
/-- The quotient over the chart read off a transformation is the restriction of a quasi-coherent
quotient over `T`. -/
theorem exists_spaceQuotientRestrict_eq_chartQuotient (C : SpaceChart T) :
    ∃ K : Subobject (D.spaceBaseModule (D.morBase hc hQ v)),
      D.spaceQuotientRestrict (D.morBase hc hQ v) C.α K = D.chartQuotient hc hQ v C ∧
        (cokernel K.arrow).IsQuasicoherentOnSite := by
  obtain ⟨K, hK, hq⟩ := exists_quotientRestrictAlong_eq_of_isEtaleCovering
    (D.chartFamily (D.morBase hc hQ v) C) (D.chartFamilyMap _ C) hc D.F D.quasicoherent
    (πW := D.spaceBaseToSource _)
    (πY := fun _ => D.sourceProjection (D.testAt (C.α ≫ D.morBase hc hQ v)))
    (fun _ => D.spaceChartMap_comp_toSource _ C.α) (fun _ => D.isEtale_spaceChartMap _ C)
    (D.isEtaleCovering_chartFamily _ C) (fun _ => D.chartQuotient hc hQ v C)
    (fun _ => hQq _ _ (TotalQuotient.kerAt_mem _ _))
    (fun ⟨⟩ ⟨⟩ => D.chartQuotient_compat hc hQ v C)
  exact ⟨K, hK (), hq⟩

/-- The chart of `T` used to descend quotients. -/
abbrev chosenChart (T : AlgebraicSpaces B S hS) : SpaceChart T := (nonempty_spaceChart T).some

/-- **The pair over `T` determined by a transformation into the total presheaf**: the morphism
`T ⟶ Y` of the transformation together with the quotient over the chosen chart, descended to
`T`. -/
def fromMor : D.SpaceQuotient Qs T :=
  ⟨D.morBase hc hQ v,
    (D.exists_spaceQuotientRestrict_eq_chartQuotient hc hQ hQq v (chosenChart T)).choose,
    hdesc (chosenChart T) _ _
      (D.exists_spaceQuotientRestrict_eq_chartQuotient hc hQ hQq v (chosenChart T)).choose_spec.2
      (by
        rw [(D.exists_spaceQuotientRestrict_eq_chartQuotient hc hQ hQq v
          (chosenChart T)).choose_spec.1]
        exact TotalQuotient.kerAt_mem _ _)⟩

/-- The pair determined by a transformation restricts, at the chosen chart, to the value of the
transformation there. -/
theorem fromMor_chart :
    D.spaceQuotientTotal hres (D.fromMor hc hQ hQq hdesc v) (chosenChart T).α =
      v.app (op (chosenChart T).U) (ULift.up (chosenChart T).section) :=
  TotalQuotient.mk_eq _ (D.morBase_chart hc hQ v _) _
    (D.exists_spaceQuotientRestrict_eq_chartQuotient hc hQ hQq v (chosenChart T)).choose_spec.1

/-- **The transformation of the pair determined by a transformation is that transformation.** -/
theorem toMor_fromMor :
    (D.fromMor hc hQ hQq hdesc v).toMor D hres hc hQ = v := by
  ext W t
  obtain ⟨t⟩ := t
  change D.spaceQuotientTotal hres (D.fromMor hc hQ hQq hdesc v)
      (ObjectProperty.homMk (yonedaEquiv.symm t)) = v.app W (ULift.up t)
  obtain ⟨V', a, b, sqV, hae, has⟩ := (chosenChart T).exists_isPullback
    (ObjectProperty.homMk (yonedaEquiv.symm t) : (schemeSpaceFunctor B S hS).obj W.unop ⟶ T)
  refine D.totalQuotient_eq_of_map_eq hc hQ a hae has _ _ (D.morBase_spec hc hQ v t).symm ?_
  have hsec : T.obj.map b.op (chosenChart T).section = T.obj.map a.op t :=
    (map_yonedaEquiv_eq_of_comp_eq (x := (chosenChart T).α) sqV.w).trans
      (congrArg (T.obj.map a.op) (Equiv.apply_symm_apply yonedaEquiv t))
  exact (D.totalQuotientFunctor_map_spaceQuotientTotal hres hc hQ _ _ a).trans
    ((D.spaceQuotientTotal_congr hres _ sqV.w.symm).trans
      (((D.totalQuotientFunctor_map_spaceQuotientTotal hres hc hQ _ _ b).symm.trans
        (congrArg _ (D.fromMor_chart hres hc hQ hQq hdesc v))).trans
        (map_app_eq_of_map_eq (D := D) hc hQ v b a hsec)))

/-- **A pair over `T` is determined by its morphism to `Y` and its restriction to a chart.** -/
theorem SpaceQuotient.eq_of_chart (C : SpaceChart T) (q₁ q₂ : D.SpaceQuotient Qs T)
    (hh : q₁.hom = q₂.hom)
    (hk : D.spaceQuotientTotal hres q₁ C.α = D.spaceQuotientTotal hres q₂ C.α) : q₁ = q₂ := by
  obtain ⟨h₁, K₁, m₁⟩ := q₁
  obtain ⟨h₂, K₂, m₂⟩ := q₂
  dsimp only at hh
  subst hh
  change (⟨C.α ≫ h₁, D.spaceQuotientRestrict h₁ C.α K₁, hres h₁ C.α K₁ m₁⟩ :
      D.TotalQuotient Q C.U) =
    ⟨C.α ≫ h₁, D.spaceQuotientRestrict h₁ C.α K₂, hres h₁ C.α K₂ m₂⟩ at hk
  obtain rfl := D.spaceQuotientRestrict_injective h₁ C (eq_of_heq (TotalQuotient.mk.inj hk).2)
  rfl

/-- The morphism `T ⟶ Y` underlying the transformation of a pair is the morphism of the pair. -/
theorem morBase_toMor (q : D.SpaceQuotient Qs T) :
    D.morBase hc hQ (q.toMor D hres hc hQ) = q.hom := by
  apply ObjectProperty.hom_ext
  refine hom_ext_yoneda fun V p ↦ ?_
  apply yonedaEquiv.injective
  rw [yonedaEquiv_comp, yonedaEquiv_comp]
  change yonedaEquiv (yonedaEquiv.symm (yonedaEquiv p) ≫ q.hom.hom) = _
  rw [yonedaEquiv_comp, Equiv.apply_symm_apply]

/-- **The pair determined by the transformation of a pair is that pair.** -/
theorem fromMor_toMor (q : D.SpaceQuotient Qs T) :
    D.fromMor hc hQ hQq hdesc (q.toMor D hres hc hQ) = q :=
  SpaceQuotient.eq_of_chart D hres (chosenChart T) _ _ (D.morBase_toMor hres hc hQ q)
    ((D.fromMor_chart hres hc hQ hQq hdesc _).trans
      (D.spaceQuotientTotal_congr hres q
        (ObjectProperty.hom_ext _ (Equiv.symm_apply_apply yonedaEquiv (chosenChart T).α.hom))))

/-- For a condition `Q` on quotients which is stable under restriction to schemes and descends
along a chart, the transformations from the sheaf of an algebraic space `T` into the total presheaf
of `Q` are the pairs over `T` satisfying the corresponding condition `Qs`. -/
def morEquivSpaceQuotientOfDescends :
    (T.obj ⋙ uliftFunctor.{u + 1, u} ⟶ D.totalQuotientFunctor hc Q hQ) ≃ D.SpaceQuotient Qs T where
  toFun v := D.fromMor hc hQ hQq hdesc v
  invFun q := q.toMor D hres hc hQ
  left_inv v := D.toMor_fromMor hres hc hQ hQq hdesc v
  right_inv q := D.fromMor_toMor hres hc hQ hQq hdesc q

end Equivalence

/-! ### Descent of the conditions of the source along a chart -/

/-- A quasi-coherent quotient over `T` whose restriction to a surjective étale chart `U ⟶ T` is
flat over `U` is flat over `T`. -/
theorem isFlatOver_of_spaceQuotientRestrict (h : T ⟶ D.Y) (C : SpaceChart T)
    (K : Subobject (D.spaceBaseModule h)) (hqc : (cokernel K.arrow).IsQuasicoherentOnSite)
    (hK : IsFlatOver B S hS (D.space (D.testAt (C.α ≫ h))).2
      (D.projection (D.testAt (C.α ≫ h))).hom
      (cokernel (D.spaceQuotientRestrict h C.α K).arrow)) :
    IsFlatOver B S hS (D.spaceBaseChange h).2 (D.spaceBaseToSpace h).hom (cokernel K.arrow) := by
  have := hqc
  have hpb : ((modulePullback B S hS (D.spaceChartMap h C.α)).obj
      (cokernel K.arrow)).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS _ _ hqc
  refine (isFlatOver_modulePullback_iff_of_isSurjective_of_isFlat B S hS (D.spaceChartMap h C.α)
    (D.spaceBaseToSpace h) (cokernel K.arrow) (D.isSurjective_spaceChartMap h C)
    (isFlat_of_isEtale B S hS (D.isEtale_spaceChartMap h C))).2 ?_
  rw [D.spaceChartMap_comp_toSpace h C.α]
  have hK' := IsFlatOver.of_iso B S hS (D.space (D.testAt (C.α ≫ h))).2
    (D.spaceQuotientRestrictCokernelIso h C.α K) hK
  refine isFlatOver_of_forall_isFlatOverAtPoint B S hS _ _ hpb fun x => ?_
  exact isFlatOverAtPoint_comp_of_isEtale (D.projection (D.testAt (C.α ≫ h))) C.α C.etale
    _ ((isFlatOver_iff_forall_isFlatOverAtPoint B S hS _ _ hpb).1 hK' x)

/-- A quasi-coherent quotient over `T` whose restriction to a surjective étale chart `U ⟶ T` is
quasi-coherent and flat over `U` is quasi-coherent and flat over `T`. -/
theorem mem_spaceQuotients_of_spaceQuotientRestrict (C : SpaceChart T) (h : T ⟶ D.Y)
    (K : Subobject (D.spaceBaseModule h)) (hqc : (cokernel K.arrow).IsQuasicoherentOnSite)
    (hK : D.spaceQuotientRestrict h C.α K ∈ D.quotients (D.testAt (C.α ≫ h))) :
    K ∈ D.spaceQuotients h :=
  ⟨hqc, D.isFlatOver_of_spaceQuotientRestrict h C K hqc hK.2⟩

/-! ### Stacks 0D3U -/

/-- For an algebraic space `T` over `S`, the morphisms of sheaves on the big fppf site of `S`
from `T` into the functor of quotients `Q_{F/X/Y}` of Stacks 082P are in bijection with the pairs
`(h, F_T ⟶ Q)` consisting of a morphism `h : T ⟶ Y` of algebraic spaces and a quotient of the
pullback `F_T` of `F` to `X ×_{Y, h} T` which is quasi-coherent and flat over `T`.

The sheaf of `T` is lifted to the universe of the functor of quotients. The inverse sends a pair
to the transformation restricting it along the chart `t : V ⟶ T` of each section `t` of `T` over
a scheme `V` of the site (`AlgebraicGeometry.Space.QuotientSituation.SpaceQuotient.toMor`). -/
@[stacks 0D3U "the first displayed identification, for Q_{F/X/Y} and an arbitrary algebraic \
space T"]
def morEquivSpaceQuotientOfAlgebraicSpace (T : AlgebraicSpaces B S hS) :
    (T.obj ⋙ uliftFunctor.{u + 1, u} ⟶
        D.totalQuotientsFunctor (modulePushforwardCoherence B S hS)) ≃
      D.SpaceQuotients T :=
  D.morEquivSpaceQuotientOfDescends
    (fun h _ α K hK => D.spaceQuotientRestrict_mem_quotients h α K hK)
    (modulePushforwardCoherence B S hS) _ (fun _ _ hK => hK.1)
    (fun C h K hqc hK => D.mem_spaceQuotients_of_spaceQuotientRestrict C h K hqc hK)

/-- The inverse of the identification of Stacks 0D3U restricts a pair along the charts of the
sections of `T`. -/
theorem morEquivSpaceQuotientOfAlgebraicSpace_symm_app {T : AlgebraicSpaces B S hS}
    (q : D.SpaceQuotients T) {V : BigFppfOver B S hS} (t : T.obj.obj (op V)) :
    ((D.morEquivSpaceQuotientOfAlgebraicSpace T).symm q).app (op V) (ULift.up t) =
      ⟨ObjectProperty.homMk (yonedaEquiv.symm t) ≫ q.hom,
        D.spaceQuotientRestrict q.hom (ObjectProperty.homMk (yonedaEquiv.symm t)) q.ker,
        D.spaceQuotientRestrict_mem_quotients q.hom _ q.ker q.mem⟩ :=
  rfl

/-- A quasi-coherent quotient over `T` whose restriction to a surjective étale chart `U ⟶ T` is
flat over `U` and of finite presentation is flat over `T` and of finite presentation. -/
theorem mem_spaceFinitePresentationQuotients_of_spaceQuotientRestrict (C : SpaceChart T)
    (h : T ⟶ D.Y) (K : Subobject (D.spaceBaseModule h))
    (hqc : (cokernel K.arrow).IsQuasicoherentOnSite)
    (hK : D.spaceQuotientRestrict h C.α K ∈ D.finitePresentationQuotients (D.testAt (C.α ≫ h))) :
    K ∈ D.spaceFinitePresentationQuotients h :=
  ⟨D.mem_spaceQuotients_of_spaceQuotientRestrict C h K hqc hK.1,
    isFinitePresentationOnSite_of_modulePullback_of_isEtaleCovering B S hS (D.chartFamily h C)
      (D.chartFamilyMap h C) (fun _ => D.isEtale_spaceChartMap h C)
      (D.isEtaleCovering_chartFamily h C) (cokernel K.arrow) fun _ =>
        SheafOfModules.IsFinitePresentationOnSite.of_iso
          (D.spaceQuotientRestrictCokernelIso h C.α K) hK.2⟩

/-- For an algebraic space `T` over `S`, any proof `hc` of the pseudofunctoriality of inverse
images and any proof `hfp` that the base-change pullbacks preserve finite presentation, the
morphisms of sheaves on the big fppf site of `S` from `T` into the finite-presentation subfunctor
`Q^{fp}_{F/X/Y}` of Stacks 0CZL are in bijection with the pairs `(h, F_T ⟶ Q)` consisting of a
morphism `h : T ⟶ Y` and a quotient of `F_T` which is of finite presentation and flat over
`T`. -/
def morEquivSpaceFinitePresentationQuotientOfAlgebraicSpace
    (hc : ModulePushforwardCoherence B S hS) (hfp : D.PullbackPreservesFinitePresentation)
    (T : AlgebraicSpaces B S hS) :
    (T.obj ⋙ uliftFunctor.{u + 1, u} ⟶ D.totalFinitePresentationQuotientsFunctor hc hfp) ≃
      D.SpaceFinitePresentationQuotients T :=
  D.morEquivSpaceQuotientOfDescends
    (fun h _ α _ hK => D.spaceQuotientRestrict_mem_finitePresentationQuotients h α hK) hc
    (fun m K hK ↦ ⟨D.quotientPullback_mem_quotients' m K hK.1,
      SheafOfModules.IsFinitePresentationOnSite.of_iso (D.quotientPullbackCokernelIso m K).symm
        (hfp m (D.quotientModule _ K) hK.2)⟩)
    (fun _ _ hK => hK.1.1)
    (fun C h K hqc hK =>
      D.mem_spaceFinitePresentationQuotients_of_spaceQuotientRestrict C h K hqc hK)

/-- The inverse of the identification of Stacks 0D3U for `Q^{fp}_{F/X/Y}` restricts a pair along
the charts of the sections of `T`. -/
theorem morEquivSpaceFinitePresentationQuotientOfAlgebraicSpace_symm_app
    (hc : ModulePushforwardCoherence B S hS) (hfp : D.PullbackPreservesFinitePresentation)
    {T : AlgebraicSpaces B S hS} (p : D.SpaceFinitePresentationQuotients T)
    (V : BigFppfOver B S hS) (t : (T.obj ⋙ uliftFunctor.{u + 1, u}).obj (op V)) :
    ∃ hm, ((D.morEquivSpaceFinitePresentationQuotientOfAlgebraicSpace hc hfp T).symm p).app
        (op V) t =
      ⟨ObjectProperty.homMk (yonedaEquiv.symm t.down) ≫ p.hom,
        D.spaceQuotientRestrict p.hom (ObjectProperty.homMk (yonedaEquiv.symm t.down)) p.ker, hm⟩ :=
  ⟨_, rfl⟩

/-- For an algebraic space `T` over `S`, the morphisms of sheaves on the big fppf site of `S`
from `T` into the finite-presentation subfunctor `Q^{fp}_{F/X/Y}` of Stacks 0CZL are in bijection
with the pairs `(h, F_T ⟶ Q)` consisting of a morphism `h : T ⟶ Y` and a quotient of `F_T` which
is of finite presentation and flat over `T`.

The subfunctor is formed with the pseudofunctoriality of inverse images
`AlgebraicGeometry.Space.modulePushforwardCoherence` and the preservation of finite presentation
by the base-change pullbacks
`AlgebraicGeometry.Space.QuotientSituation.pullbackPreservesFinitePresentation`. -/
@[stacks 0D3U "the second displayed identification, for Q^{fp}_{F/X/Y} and an arbitrary \
algebraic space T"]
def morEquivSpaceFinitePresentationQuotientOfAlgebraicSpaceUnconditional
    (T : AlgebraicSpaces B S hS) :
    (T.obj ⋙ uliftFunctor.{u + 1, u} ⟶
        D.totalFinitePresentationQuotientsFunctor (modulePushforwardCoherence B S hS)
          D.pullbackPreservesFinitePresentation) ≃
      D.SpaceFinitePresentationQuotients T :=
  D.morEquivSpaceFinitePresentationQuotientOfAlgebraicSpace (modulePushforwardCoherence B S hS)
    D.pullbackPreservesFinitePresentation T

end QuotientSituation

end AlgebraicGeometry.Space

end
