module

public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackObstructionProducts
public import StacksFrontier.AlgebraicGeometry.Quot.PicardStackOpenImmersion
public import StacksFrontier.Deformation.Artin.Versality.Helpers.LiftDetectionFromObstruction

/-!
# Openness of versality for `Coh_{X/B}`: the second proof of Stacks 08WA

The second proof of Stacks 08WA applies Stacks 0CYF. Its conditions (1), (2), (3) are the
representability of the diagonal (Stacks 08W6), condition (RS*) (Stacks 08LQ) and limit
preservation (Stacks 08KD). Its obstruction theory at an object `x = (Spec A, ℱ)` is
`Ext²_{X_A}(ℱ, ℱ ⊗ f^*Ĩ)`, with the obstruction class of Stacks 08VW, functorial over a fixed
`A` (Stacks 0CYE, which is all the proof of Stacks 0CYF uses, by the footnote to its assumption
(4)), and its tangent spaces are `Ext¹_{X_A}(ℱ, ℱ ⊗ f^*M̃)` (Stacks 08VW). Both commute with
countable products by Stacks 08JR
(`AlgebraicGeometry.Space.CoherentSituation.bijective_extGroupMap_pi`).

This file assembles that argument from the deformation data of an object over a chart
(`AlgebraicGeometry.Space.CoherentSituation.ChartObstructionData`). The proof of Stacks 0CYF only
uses its assumptions (4), (5) at bases of finite type over `S`, which are Noetherian: that is the
form `Deformation.Artin.isOpenVersality_of_hasLiftOfCountableProductsOfFiniteType`.

## Main definitions

* `AlgebraicGeometry.Space.CoherentSituation.ChartObstructionData`: the tangent identification
  and the obstruction classes of an object over a chart.
* `Deformation.Artin.DeformationSituation.toSquareZeroThickening`: a deformation situation read
  as a square-zero thickening.

## Main results

* `AlgebraicGeometry.Space.CoherentSituation.isOpenVersality_coherentCFG_of_chartObstructionData`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Deformation.Artin

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace Deformation.Artin

variable {A : Type u} [CommRing A] {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {toS : Spec (.of A) ⟶ S} {hA : B.Contains (Spec (.of A))}

/-- A deformation situation of `A`, read as a square-zero thickening of `Spec A` over `S`. -/
def DeformationSituation.toSquareZeroThickening
    (t : DeformationSituation B S hS (AugmentedSiteRing.siteAlgebra A toS hA)) :
    SquareZeroThickening A B S hS toS hA t.top.carrier where
  q := t.hom.ringMap
  squareZeroSurjection := ⟨t.surjective, t.sq_eq_bot⟩
  hA' := t.top.mem
  toS' := t.top.toBase
  arrow := t.hom.specMap
  arrow_spec := t.hom.specMap_spec

/-- A deformation situation of `A`, read as an augmented ring of the site. -/
def DeformationSituation.toAugmentedSiteRing
    (t : DeformationSituation B S hS (AugmentedSiteRing.siteAlgebra A toS hA)) :
    AugmentedSiteRing A B S hS toS hA where
  ring := CommRingCat.of t.top.carrier
  contains := t.top.mem
  structureMap := t.top.toBase
  aug := t.hom.ringMap
  arrow := t.hom.specMap
  arrow_eq := t.hom.specMap_spec

variable {X : Type*} [Category X] {p : X ⥤ BigFppfOver B S hS}

/-- An object over `Spec A` lifts across a deformation situation exactly when the category of
its lifts across the corresponding square-zero thickening is nonempty. -/
theorem DeformationSituation.hasLift_iff_nonempty (hp : p.IsFiberedInGroupoids) (x : X)
    (hx : p.obj x = algebraOver A B S hS toS hA) (hU : MapsIntoAffineOpen S toS)
    (t : DeformationSituation B S hS (AugmentedSiteRing.siteAlgebra A toS hA)) :
    AffineObject.HasLift hp (AugmentedSiteRing.affineObject x hx hU) t ↔
      Nonempty ((Under.post p).Fiber (Under.mk (eqToHom hx ≫ t.toSquareZeroThickening.arrow))) :=
  (AugmentedSiteRing.hasLift_situation_iff hp x hx hU t.toAugmentedSiteRing t.surjective
    t.sq_eq_bot).trans (nonempty_quotient_iff _)

/-- A morphism of deformation situations over the identity of `(x, A)`, with a map of kernels
compatible with it, is a morphism of square-zero thickenings. -/
def DeformationSituation.Hom.toSquareZeroThickeningHom {x : X}
    {hx : p.obj x = algebraOver A B S hS toS hA} {hU : MapsIntoAffineOpen S toS}
    {t s : DeformationSituation B S hS (AugmentedSiteRing.siteAlgebra A toS hA)}
    (m : DeformationSituation.Hom B S hS p (P := AugmentedSiteRing.affineObject x hx hU)
      (Q := AugmentedSiteRing.affineObject x hx hU) t s)
    (hbase : m.base = AffineObject.Hom.id _) (fk : t.kernelObj ⟶ s.kernelObj)
    (hfk : ∀ z, s.kernelVal (fk z) = m.top.ringMap (t.kernelVal z)) :
    SquareZeroThickening.Hom t.toSquareZeroThickening s.toSquareZeroThickening where
  ringHom := m.top.ringMap
  overBase := by
    have h := m.comm
    rw [hbase] at h
    exact h
  overS := by
    have h := congrArg (fun g => B.inclusion.map g) (Over.w m.top.specMap)
    simp only [Functor.map_comp] at h
    change Spec.map (CommRingCat.ofHom m.top.ringMap) ≫ B.inclusion.map t.top.toBase =
      B.inclusion.map s.top.toBase
    rw [← m.top.specMap_spec]
    exact h
  kernelMap := fk
  kernelMap_spec i := hfk i

end Deformation.Artin

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance] HasDerivedCategory.standard

attribute [local instance] pointTopology

attribute [local instance] hasProductsOfShape_nat_modules_ringUniverse
  enoughInjectives_modules_ringUniverse isGrothendieckAbelian_modules_ringUniverse

namespace CoherentSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} (D : CoherentSituation B S hS)

/-- **The deformation theory of an object of `Coh_{X/B}` over a chart, read in Ext groups.** For
an object `x` of `Coh_{X/B}` over `Spec A`, given as the object `algebraOver` of the site, and
`(RS*)` for `Coh_{X/B}`: a bijection of the tangent functor with `Ext¹(ℱ, ℱ ⊗ f^*(-)~)`
natural along surjections of modules (Stacks 08VW), and obstruction classes in
`Ext²(ℱ, ℱ ⊗ f^*Ĩ)` vanishing exactly when `x` lifts (Stacks 08VW) and functorial along
surjections of square-zero thickenings of `Spec A` (Stacks 0CYE). -/
structure ChartObstructionData {A : Type u} [CommRing A] (toS : Spec (.of A) ⟶ S)
    (hA : B.Contains (Spec (.of A))) (x : CoherentObject D)
    (hx : (coherentCFG D).val.p.obj x = algebraOver A B S hS toS hA)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj x.T.left)]
    (hRS : SatisfiesRSStar B S hS (coherentCFG D).val.p (coherentCFG D).2) where
  /-- The identification of the tangent functor. -/
  τ : ∀ M : SiteModule A B,
    ((tangentFunctor A B S hS toS hA (coherentCFG D).val.p x hx (coherentCFG D).2
      hRS).functor.obj M : Type _) ≃ D.extGroup x (D.chartRingEquiv x hx) M.obj 1
  /-- It is natural along surjections of modules. -/
  τ_natural : ∀ {M N : SiteModule A B} (f : M ⟶ N), Function.Surjective f.hom →
    ∀ (t : (tangentFunctor A B S hS toS hA (coherentCFG D).val.p x hx (coherentCFG D).2
      hRS).functor.obj M),
    τ N ((tangentFunctor A B S hS toS hA (coherentCFG D).val.p x hx (coherentCFG D).2
      hRS).functor.map f t) = D.extGroupMap x (D.chartRingEquiv x hx) f.hom 1 (τ M t)
  /-- The obstruction class of a square-zero thickening. -/
  ob : ∀ (A' : Type u) [CommRing A'] (T : SquareZeroThickening A B S hS toS hA A'),
    D.extGroup x (D.chartRingEquiv x hx) T.kernel 2
  /-- It vanishes exactly when `x` lifts. -/
  ob_eq_zero_iff : ∀ (A' : Type u) [CommRing A'] (T : SquareZeroThickening A B S hS toS hA A'),
    Nonempty ((Under.post (coherentCFG D).val.p).Fiber (Under.mk (eqToHom hx ≫ T.arrow))) ↔
      ob A' T = 0
  /-- It is functorial along surjections of square-zero thickenings. -/
  ob_natural : ∀ (A₁ A₂ : Type u) [CommRing A₁] [CommRing A₂]
    (T₁ : SquareZeroThickening A B S hS toS hA A₁)
    (T₂ : SquareZeroThickening A B S hS toS hA A₂) (f : SquareZeroThickening.Hom T₁ T₂),
    Function.Surjective f.ringHom →
      D.extGroupMap x (D.chartRingEquiv x hx) f.kernelMap 2 (ob A₁ T₁) = ob A₂ T₂

/-- A ring with spectrum locally of finite type over a locally Noetherian scheme is Noetherian. -/
theorem isNoetherianRing_of_locallyOfFiniteType [_root_.AlgebraicGeometry.IsLocallyNoetherian S]
    {A : Type u} [CommRing A] (toS : Spec (.of A) ⟶ S)
    (h : _root_.AlgebraicGeometry.LocallyOfFiniteType toS) : IsNoetherianRing A := by
  have := h
  have := LocallyOfFiniteType.isLocallyNoetherian toS
  exact (isLocallyNoetherian_Spec (R := CommRingCat.of A)).mp this

section Tangent

variable {A : Type u} [CommRing A] {toS : Spec (.of A) ⟶ S} {hA : B.Contains (Spec (.of A))}
  {x : CoherentObject D} {hx : (coherentCFG D).val.p.obj x = algebraOver A B S hS toS hA}
  [IsAffine ((BigFppfOver.toScheme B S hS).obj x.T.left)]
  [IsNoetherianRing Γ((BigFppfOver.toScheme B S hS).obj x.T.left, ⊤)]
  {hRS : SatisfiesRSStar B S hS (coherentCFG D).val.p (coherentCFG D).2}

/-- **The tangent spaces of `Coh_{X/B}` over a Noetherian chart commute with countable
products.** -/
theorem bijective_tangent_pi (data : D.ChartObstructionData toS hA x hx hRS)
    (M : ℕ → SiteModule A B)
    (hM : IsSiteModule A B (ModuleCat.of A (∀ n, ((M n).obj : Type u)))) :
    Function.Bijective (fun t : (tangentFunctor A B S hS toS hA (coherentCFG D).val.p x hx
        (coherentCFG D).2 hRS).functor.obj ⟨ModuleCat.of A (∀ n, ((M n).obj : Type u)), hM⟩ =>
      fun n => (tangentFunctor A B S hS toS hA (coherentCFG D).val.p x hx (coherentCFG D).2
          hRS).functor.map
        (ObjectProperty.homMk (ModuleCat.ofHom (LinearMap.proj n)) :
          (⟨ModuleCat.of A (∀ n, ((M n).obj : Type u)), hM⟩ : SiteModule A B) ⟶ M n) t) := by
  have hfun : (fun t : (tangentFunctor A B S hS toS hA (coherentCFG D).val.p x hx
        (coherentCFG D).2 hRS).functor.obj ⟨ModuleCat.of A (∀ n, ((M n).obj : Type u)), hM⟩ =>
      fun n => (tangentFunctor A B S hS toS hA (coherentCFG D).val.p x hx (coherentCFG D).2
          hRS).functor.map
        (ObjectProperty.homMk (ModuleCat.ofHom (LinearMap.proj n)) :
          (⟨ModuleCat.of A (∀ n, ((M n).obj : Type u)), hM⟩ : SiteModule A B) ⟶ M n) t) =
      (fun c n => (data.τ (M n)).symm (c n)) ∘
        (fun c n => D.extGroupMap x (D.chartRingEquiv x hx)
          (ModuleCat.ofHom (LinearMap.proj n) :
            ModuleCat.of A (∀ n, ((M n).obj : Type u)) ⟶ (M n).obj) 1 c) ∘
        (data.τ ⟨ModuleCat.of A (∀ n, ((M n).obj : Type u)), hM⟩) := by
    funext t n
    exact (data.τ (M n)).eq_symm_apply.mpr
      (data.τ_natural (ObjectProperty.homMk (ModuleCat.ofHom (LinearMap.proj n)))
        (fun y => ⟨(Pi.single n y : ∀ m, ((M m).obj : Type u)),
          (Pi.single_eq_same (M := fun m => ((M m).obj : Type u)) n y : _)⟩) t)
  rw [hfun]
  exact (Equiv.piCongrRight fun n => (data.τ (M n)).symm).bijective.comp
    ((D.bijective_extGroupMap_pi x (D.chartRingEquiv x hx) (fun n => (M n).obj) 1).comp
      (data.τ _).bijective)

end Tangent

section Obstruction

variable {A : Type u} [CommRing A] {toS : Spec (.of A) ⟶ S} {hA : B.Contains (Spec (.of A))}
  {x : CoherentObject D} {hx : (coherentCFG D).val.p.obj x = algebraOver A B S hS toS hA}
  [IsAffine ((BigFppfOver.toScheme B S hS).obj x.T.left)]
  {hRS : SatisfiesRSStar B S hS (coherentCFG D).val.p (coherentCFG D).2}
  (L : DerivedCategory (ModuleCat.{u} (D.baseRing x)))
  (Ξ : ∀ (N : ModuleCat.{u} (D.baseRing x)) (i : ℤ),
      ShiftedHom L ((DerivedCategory.singleFunctor _ 0).obj N) i ≃+
        ShiftedHom (D.singleObject x) (tensorPullbackComplexDerived (D.baseProjection x)
          (D.singleComplex x)
          ((HomologicalComplex.single (SheafOfModules.{u}
            (ringedToposStructureRingSheaf B S hS (D.baseSpace x))) (ComplexShape.up ℤ) 0).obj
            ((representedAffineAssociated B S hS x.T.left).obj N))) i)

/-- The obstruction groups `Hom_{D(A)}(L, M[2]) = Ext²_{X_A}(ℱ, ℱ ⊗ f^*M̃)`, as a functor of the
`A`-module `M`. -/
abbrev obstructionGroups (e : A ≃+* D.baseRing x) : ModuleCat.{u} A ⥤ AddCommGrpCat :=
  (ModuleCat.restrictScalarsEquivalenceOfRingEquiv e.symm).functor ⋙
    DerivedCategory.singleFunctor _ 0 ⋙ shiftFunctor _ (2 : ℤ) ⋙
      preadditiveCoyoneda.obj (Opposite.op L)

/-- The obstruction element of a deformation situation, in the obstruction groups. -/
def obstructionElement (data : D.ChartObstructionData toS hA x hx hRS)
    (t : DeformationSituation B S hS (AugmentedSiteRing.siteAlgebra A toS hA)) :
    (D.obstructionGroups L (D.chartRingEquiv x hx)).obj t.kernelObj :=
  D.extShiftedHomEquiv x (D.chartRingEquiv x hx) L Ξ t.kernelObj 2
    (data.ob t.top.carrier t.toSquareZeroThickening)

variable {L Ξ}

/-- A deformation situation admits a lift of `x` exactly when its obstruction element vanishes. -/
theorem obstructionElement_eq_zero_iff (data : D.ChartObstructionData toS hA x hx hRS)
    (hU : MapsIntoAffineOpen S toS)
    (t : DeformationSituation B S hS (AugmentedSiteRing.siteAlgebra A toS hA)) :
    AffineObject.HasLift (coherentCFG D).2 (AugmentedSiteRing.affineObject x hx hU) t ↔
      D.obstructionElement L Ξ data t = 0 :=
  (DeformationSituation.hasLift_iff_nonempty (coherentCFG D).2 x hx hU t).trans
    ((data.ob_eq_zero_iff t.top.carrier t.toSquareZeroThickening).trans
      (map_eq_zero_iff (D.extShiftedHomEquiv x (D.chartRingEquiv x hx) L Ξ t.kernelObj 2)
        (D.extShiftedHomEquiv x (D.chartRingEquiv x hx) L Ξ t.kernelObj 2).injective).symm)

/-- The obstruction elements are functorial along a surjective morphism of deformation situations
over the identity of `(x, A)`, with a compatible map of kernels. -/
theorem obstructionElement_natural
    (hΞnat : ∀ {N N' : ModuleCat.{u} (D.baseRing x)}
      (g : N ⟶ N') (i : ℤ) (y : ShiftedHom L ((DerivedCategory.singleFunctor _ 0).obj N) i),
      Ξ N' i (y.comp (ShiftedHom.mk₀ (0 : ℤ) rfl
          ((DerivedCategory.singleFunctor _ 0).map g)) (zero_add i)) =
        Ξ N i y ≫ (DerivedCategory.Q.map ((tensorPullbackComplex (D.baseProjection x)
          (D.singleComplex x)).map ((HomologicalComplex.single (SheafOfModules.{u}
            (ringedToposStructureRingSheaf B S hS (D.baseSpace x))) (ComplexShape.up ℤ) 0).map
            ((representedAffineAssociated B S hS x.T.left).map g))))⟦i⟧')
    (data : D.ChartObstructionData toS hA x hx hRS) (hU : MapsIntoAffineOpen S toS)
    (t s : DeformationSituation B S hS (AugmentedSiteRing.siteAlgebra A toS hA))
    (m : DeformationSituation.Hom B S hS (coherentCFG D).val.p
      (P := AugmentedSiteRing.affineObject x hx hU) (Q := AugmentedSiteRing.affineObject x hx hU)
      t s)
    (hbase : m.base = AffineObject.Hom.id _) (hsurj : Function.Surjective m.top.ringMap)
    (fk : t.kernelObj ⟶ s.kernelObj)
    (hfk : ∀ z, s.kernelVal (fk z) = m.top.ringMap (t.kernelVal z)) :
    (D.obstructionGroups L (D.chartRingEquiv x hx)).map fk (D.obstructionElement L Ξ data t) =
      D.obstructionElement L Ξ data s := by
  have h := data.ob_natural t.top.carrier s.top.carrier t.toSquareZeroThickening
    s.toSquareZeroThickening (m.toSquareZeroThickeningHom hbase fk hfk) hsurj
  show _ = D.extShiftedHomEquiv x (D.chartRingEquiv x hx) L Ξ s.kernelObj 2
    (data.ob s.top.carrier s.toSquareZeroThickening)
  rw [← h]
  show _ = D.extShiftedHomEquiv x (D.chartRingEquiv x hx) L Ξ s.kernelObj 2
    (D.extGroupMap x (D.chartRingEquiv x hx) fk 2 (data.ob t.top.carrier t.toSquareZeroThickening))
  have key := D.extShiftedHomEquiv_extGroupMap x (D.chartRingEquiv x hx) hΞnat fk 2
    (data.ob t.top.carrier t.toSquareZeroThickening)
  refine Eq.trans ?_ key.symm
  exact (ShiftedHom.comp_mk₀ (show ShiftedHom L ((DerivedCategory.singleFunctor _ 0).obj
      (D.baseModule x (D.chartRingEquiv x hx) t.kernelObj)) (2 : ℤ) from
        D.obstructionElement L Ξ data t) (0 : ℤ) rfl
    ((DerivedCategory.singleFunctor _ 0).map
      ((ModuleCat.restrictScalarsEquivalenceOfRingEquiv (D.chartRingEquiv x hx).symm).functor.map
        fk))).symm

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj x.T.left)] in
/-- The obstruction groups are injective on countable products: an element of the group at `∏ₙ Mₙ`
is determined by its images under the projections to the `Mₙ`. -/
theorem injective_obstructionGroups_map_pi (M : ℕ → ModuleCat.{u} A) :
    Function.Injective (fun (z : (D.obstructionGroups L (D.chartRingEquiv x hx)).obj
        (ModuleCat.of A (∀ n, (M n : Type u)))) n =>
      (D.obstructionGroups L (D.chartRingEquiv x hx)).map
        (ModuleCat.ofHom (LinearMap.proj n) : ModuleCat.of A (∀ n, (M n : Type u)) ⟶ M n) z) := by
  let T := (ModuleCat.restrictScalarsEquivalenceOfRingEquiv (D.chartRingEquiv x hx).symm).functor
  have hc : IsLimit (Fan.mk (T.obj (ModuleCat.of A (∀ n, (M n : Type u))))
      (fun n => T.map (ModuleCat.ofHom (LinearMap.proj n) :
        ModuleCat.of A (∀ n, (M n : Type u)) ⟶ M n))) :=
    isLimitFanMkObjOfIsLimit T M _ (ModuleCat.HasLimit.productLimitCone M).isLimit
  have hb := (DerivedCategory.bijective_shiftedHom_single_comp_of_isLimit L 2 _ hc).1
  intro z z' h
  refine hb (a₁ := (show ShiftedHom L _ (2 : ℤ) from z))
    (a₂ := (show ShiftedHom L _ (2 : ℤ) from z')) (funext fun n => ?_)
  have e := fun w : ShiftedHom L ((DerivedCategory.singleFunctor _ 0).obj
      (T.obj (ModuleCat.of A (∀ n, (M n : Type u))))) (2 : ℤ) =>
    ShiftedHom.comp_mk₀ w (0 : ℤ) rfl
      ((DerivedCategory.singleFunctor _ 0).map (T.map (ModuleCat.ofHom (LinearMap.proj n) :
        ModuleCat.of A (∀ n, (M n : Type u)) ⟶ M n)))
  exact (e z).trans ((congrFun h n).trans (e z').symm)

end Obstruction

/-- **Openness of versality for `Coh_{X/B}` from the deformation data over charts** (the second
proof of Stacks 08WA, through Stacks 0CYF). Over a locally Noetherian `S`, if the diagonal of
`Coh_{X/B}` is representable by algebraic spaces, `Coh_{X/B}` satisfies (RS*) and is limit
preserving, and its objects over Noetherian affine charts carry the tangent identification and
obstruction classes of `AlgebraicGeometry.Space.CoherentSituation.ChartObstructionData`, then
`Coh_{X/B}` satisfies openness of versality. -/
theorem isOpenVersality_coherentCFG_of_chartObstructionData
    [_root_.AlgebraicGeometry.IsLocallyNoetherian S]
    (hΔ : Stack.HasRepresentableDiagonal B S hS (coherentCFG D))
    (hRS : SatisfiesRSStar B S hS (coherentCFG D).val.p (coherentCFG D).2)
    (hlim : IsLimitPreserving.{u, u, u, u + 1, u + 1} B S hS (coherentCFG D))
    (hdata : ∀ (A : Type u) [CommRing A] (toS : Spec (.of A) ⟶ S) (hA : B.Contains (Spec (.of A)))
      (x : CoherentObject D) (hx : (coherentCFG D).val.p.obj x = algebraOver A B S hS toS hA)
      [IsAffine ((BigFppfOver.toScheme B S hS).obj x.T.left)] [IsNoetherianRing (D.baseRing x)],
      Nonempty (D.ChartObstructionData toS hA x hx hRS)) :
    ∀ U : Over S, _root_.AlgebraicGeometry.LocallyOfFiniteType U.hom →
      ∀ (y : (coherentCFG D).val.obj)
        (hy : ((coherentCFG D).val.p ⋙ Over.post B.inclusion).obj y = U) (u : U.left),
        _root_.AlgebraicGeometry.IsFiniteTypePoint u →
        IsVersalAt U ((coherentCFG D).val.p ⋙ Over.post B.inclusion) u y hy →
        ∃ V : U.left.Opens, u ∈ V.1 ∧
          ∀ u' : U.left, u' ∈ V.1 → _root_.AlgebraicGeometry.IsFiniteTypePoint u' →
            IsVersalAt U ((coherentCFG D).val.p ⋙ Over.post B.inclusion) u' y hy := by
  have h := isOpenVersality_of_hasLiftOfCountableProductsOfFiniteType.{u, u + 1, u + 1}
    (coherentCFG D) hΔ hRS hlim ?_ ?_
  · intro U hU y hy u hu hver
    obtain ⟨V, huV, hV⟩ := h U hU y hy u hu hver
    exact ⟨V, huV, fun u' hu' hft => hV u' hu' hft⟩
  · intro A _ toS hA hlft x hx M hM
    have := D.isAffine_of_chart x hx
    have : IsNoetherianRing A := isNoetherianRing_of_locallyOfFiniteType toS hlft
    have := D.isNoetherianRing_of_chart x hx
    exact D.bijective_tangent_pi (hdata A toS hA x hx).some M hM
  · refine hasLiftOfCountableProductsOfFiniteType_of_obstruction B S hS _ _
      (fun A _ toS hA hU hlft x hx => ?_)
    have := D.isAffine_of_chart x hx
    have : IsNoetherianRing A := isNoetherianRing_of_locallyOfFiniteType toS hlft
    have := D.isNoetherianRing_of_chart x hx
    have hX := D.exists_isPseudoCoherentFrom_extEquiv x
    exact ⟨D.obstructionGroups hX.choose (D.chartRingEquiv x hx),
      D.obstructionElement hX.choose hX.choose_spec.2.choose (hdata A toS hA x hx).some,
      fun t => D.obstructionElement_eq_zero_iff (hdata A toS hA x hx).some hU t,
      fun t s m hb hsurj fk hfk => D.obstructionElement_natural hX.choose_spec.2.choose_spec.1
        (hdata A toS hA x hx).some hU t s m hb hsurj fk hfk,
      fun M => D.injective_obstructionGroups_map_pi M⟩

end CoherentSituation

end AlgebraicGeometry.Space

end
