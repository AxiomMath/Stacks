module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleRestrictHom
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.ZariskiTransitionExists
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.FpqcChartFullness
public import
  StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.RepresentedZariskiTransitionPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.FpqcSourceLocalityTransfer

/-!
# Fpqc descent of morphisms of quasi-coherent modules over a represented base

Let `B` be a big fppf site containing a scheme `S`, let `U` be an object of the big fppf category
over `S` and let `(g j : T j ⟶ U)` be a family of that category which is an fpqc covering of the
representable algebraic space `yoneda.obj U` in the sense of Stacks 03MQ.  A pairwise compatible
family of morphisms of the inverse images of Stacks 03LU of two **quasi-coherent** `𝒪`-modules on
`yoneda.obj U` along that covering is the family of the inverse images of a morphism of those
modules: the fullness half of Stacks 023T, read on represented algebraic spaces.  It follows
that the canonical descent functor of Stacks 04W5 of an arbitrary fpqc covering of algebraic
spaces is fully faithful, the full-faithfulness clause of Stacks 04W8.

## Main definitions

* `AlgebraicGeometry.Space.QuasiCoherentDescent.zariskiHomOn` is a morphism of the inverse images
  of Stacks 03LU along a morphism of representable algebraic spaces, read on the underlying
  schemes.

## Main results

* `AlgebraicGeometry.Space.QuasiCoherentDescent.restrictForm_representedSpaceMap`: the restricted
  reading of Stacks 04W3 at a composite of represented morphisms, through the contraction of the
  two inverse images.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.pullHom_zariskiHomOn`: **the reading on the
  schemes, restricted along a further morphism, is the reading of the restricted reading.**
* `AlgebraicGeometry.Space.QuasiCoherentDescent.exists_pairTestObject`: **the fibre product of
  two members of the family, taken in the big fppf category over `S`, is a test object for the
  pair** — every scheme mapping to the two members over `U` factors through it.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.pullHom_zariskiHomOn_eq_of_isPairwiseCompatible`:
  **the family read on the schemes is compatible.**
* `AlgebraicGeometry.Space.QuasiCoherentDescent.exists_modulePullback_map_eq_representedSpaceMap`
  and `reprFpqcHomSurjective`: **the fullness half of Stacks 023T on represented algebraic
  spaces.**
* `AlgebraicGeometry.Space.QuasiCoherentDescent.full_canonicalDescentFunctor_of_isFpqcCovering'`:
  **the canonical descent functor of Stacks 04W5 of an fpqc covering of algebraic spaces is
  full**, with no hypothesis.
* `nonempty_fullyFaithful_canonicalDescentFunctor_of_isFpqcCovering`: **that functor is fully
  faithful**, with no hypothesis.

## References

* [Stacks Project, Tag 04W8](https://stacks.math.columbia.edu/tag/04W8)
* [Stacks Project, Tag 04W5](https://stacks.math.columbia.edu/tag/04W5)
* [Stacks Project, Tag 04W3](https://stacks.math.columbia.edu/tag/04W3)
* [Stacks Project, Tag 023T](https://stacks.math.columbia.edu/tag/023T)
* [Stacks Project, Tag 03MQ](https://stacks.math.columbia.edu/tag/03MQ)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 021U](https://stacks.math.columbia.edu/tag/021U)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
  Pseudofunctor.LocallyDiscreteOpToCat

universe u v

namespace AlgebraicGeometry.Space.QuasiCoherentDescent

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Transport

variable {C₀ : Type*} [Category C₀]

/-- A transport along an equality of an object with itself cancels. -/
private theorem eqToIso_trans_of_eq_self {X Y : C₀} (p : X = X) (e : X ≅ Y) :
    eqToIso p ≪≫ e = e := by
  rw [show eqToIso p = Iso.refl X from rfl, Iso.refl_trans]

end Transport

/-! ### Morphisms on a representable algebraic space and on the underlying scheme -/

section Bijective

variable {U : BigFppfOver B S hS}

/-- **Reading a morphism of quasi-coherent `𝒪`-modules on a representable algebraic space on the
underlying scheme is bijective.** -/
theorem bijective_representedZariski_map
    (M N : SheafOfModules.{u} (representedStructureRingSheaf B S hS U))
    (hM : M.IsQuasicoherentOnSite) :
    Function.Bijective (fun ψ : M ⟶ N =>
      (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj U) U.left.property).map
        ((representedSmallEtaleModuleEquivalence B S hS U).inverse.map ψ)) :=
  (_root_.AlgebraicGeometry.SmallEtale.bijective_restrictModule_map (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj U) U.left.property
      ((representedSmallEtaleModuleEquivalence B S hS U).inverse.obj M)
      ((representedSmallEtaleModuleEquivalence B S hS U).inverse.obj N)
      (isQuasicoherentOnSite_representedSmallEtaleInverse B S hS U M hM)).comp
    ⟨fun _ _ h ↦ (representedSmallEtaleModuleEquivalence B S hS U).inverse.map_injective h,
      fun t ↦ ⟨(representedSmallEtaleModuleEquivalence B S hS U).inverse.preimage t,
        (representedSmallEtaleModuleEquivalence B S hS U).inverse.map_preimage t⟩⟩

end Bijective

/-! ### The comparison of Stacks 03LU at a composite of represented morphisms -/

section Comparison

variable {U V W : BigFppfOver B S hS}

attribute [local implicit_reducible] AlgebraicGeometry.Space.smallEtaleRingedSite

/-- **The comparison of Stacks 03LU at a composite of represented morphisms is the contraction
of the two inverse images.** -/
theorem pullbackComparison_representedSpaceMap_comp (p : W ⟶ V) (k : V ⟶ U)
    (hr : representedSpaceMap B S hS p ≫ representedSpaceMap B S hS k =
      representedSpaceMap B S hS (p ≫ k))
    (M : SheafOfModules.{u} (representedStructureRingSheaf B S hS U)) :
    pullbackComparison B S hS (representedSpaceMap B S hS p) (representedSpaceMap B S hS k)
        (representedSpaceMap B S hS (p ≫ k)) hr M =
      ((representedModulePullbackCompIso B S hS p k).app M).symm := by
  rw [pullbackComparison_eq_eqToIso_trans, representedModulePullbackCompIso_eq]
  exact eqToIso_trans_of_eq_self _ _

/-- **The restricted reading of Stacks 04W3 at a composite of represented morphisms, written
through the contraction of the two inverse images.** -/
theorem restrictForm_representedSpaceMap (p : W ⟶ V) (k : V ⟶ U)
    (hr : representedSpaceMap B S hS p ≫ representedSpaceMap B S hS k =
      representedSpaceMap B S hS (p ≫ k))
    {M N : SheafOfModules.{u} (representedStructureRingSheaf B S hS U)}
    (w : (modulePullback B S hS (representedSpaceMap B S hS k)).obj M ⟶
      (modulePullback B S hS (representedSpaceMap B S hS k)).obj N) :
    restrictForm B S hS (representedSpaceMap B S hS p) (representedSpaceMap B S hS k)
        (representedSpaceMap B S hS (p ≫ k)) hr w =
      ((representedModulePullbackCompIso B S hS p k).app M).inv ≫
        (modulePullback B S hS (representedSpaceMap B S hS p)).map w ≫
        ((representedModulePullbackCompIso B S hS p k).app N).hom := by
  rw [restrictForm_eq, factorForm_eq, pullbackComparison_representedSpaceMap_comp,
    pullbackComparison_representedSpaceMap_comp, Iso.symm_hom, Iso.symm_inv]

end Comparison

/-! ### One step taken in an arbitrary category -/

section Abstract

variable {C₀ D₀ : Type*} [Category C₀] [Category D₀]

/-- **A conjugation carried by a functor, re-expressed through a second pair of
isomorphisms.**  The morphism `s` is `Rw` conjugated by `aM` and `aN`; the four hypotheses then
move the conjugation of its image under `F` by `cM`, `cN` onto the morphism `t`, which is `RT`
conjugated by `apkM` and `apkN`. -/
theorem map_conj_eq_conj (F : C₀ ⥤ D₀) {X Y PM PN : C₀} {XD YD QM QN ZM ZN : D₀}
    (aM : X ≅ PM) (aN : Y ≅ PN) (cM : XD ≅ F.obj X) (cN : YD ≅ F.obj Y)
    (apkM : XD ≅ ZM) (apkN : YD ≅ ZN) (apM : F.obj PM ⟶ QM) (apN : F.obj PN ⟶ QN)
    (Cmh : QM ⟶ ZM) (Cnh : QN ⟶ ZN) (Rw : PM ⟶ PN) (Dw : QM ⟶ QN) (RT : ZM ⟶ ZN)
    (s : X ⟶ Y) (t : XD ⟶ YD) (h0 : s = aM.hom ≫ Rw ≫ aN.inv)
    (h5 : t = apkM.hom ≫ RT ≫ apkN.inv)
    (h1 : F.map aM.hom ≫ apM ≫ Cmh = cM.inv ≫ apkM.hom)
    (h2 : F.map aN.hom ≫ apN ≫ Cnh = cN.inv ≫ apkN.hom)
    (h3 : F.map Rw ≫ apN = apM ≫ Dw) (h4 : Cmh ≫ RT = Dw ≫ Cnh) :
    cM.hom ≫ F.map s ≫ cN.inv = t := by
  subst h0 h5
  have e2 : apN ≫ Cnh ≫ apkN.inv = F.map aN.inv ≫ cN.inv := by
    rw [← cancel_epi (F.map aN.hom), ← cancel_epi cN.hom, reassoc_of% h2,
      Iso.hom_inv_id_assoc, Iso.hom_inv_id, ← Functor.map_comp_assoc, Iso.hom_inv_id,
      F.map_id, Category.id_comp, Iso.hom_inv_id]
  simp only [Functor.map_comp, Category.assoc]
  rw [← e2, reassoc_of% h3, ← reassoc_of% h4, reassoc_of% h1, Iso.hom_inv_id_assoc]

/-- An endomorphism conjugated by the components of a natural isomorphism, prefixed by the
component at the source, is the endomorphism followed by the component at the target. -/
private theorem natIso_hom_app_conj {F G : C₀ ⥤ D₀} (α : F ≅ G) {M N : C₀}
    (u : F.obj M ⟶ F.obj N) :
    α.hom.app M ≫ ((α.app M).inv ≫ u ≫ (α.app N).hom) = u ≫ α.hom.app N := by
  rw [← Iso.app_hom, Iso.hom_inv_id_assoc, Iso.app_hom]

end Abstract

/-! ### The comparison of iterated pullbacks of modules on schemes, in the two spellings -/

section PullModComp

/-- A transport along an equality of a morphism with itself contributes nothing to the
comparison of iterated pullbacks. -/
private theorem pullbackCongr_hom_app_eq_id {X Y : Scheme.{u}} {f : X ⟶ Y} (h : f = f)
    (M : Y.Modules) : (Scheme.Modules.pullbackCongr h).hom.app M = 𝟙 _ := rfl

/-- **The comparison isomorphism of the pullback pseudofunctor at a factorization, inverted, is
the comparison of the two pullback functors of modules on schemes.** -/
theorem pullModComp_inv_eq {X Y Z : Scheme.{u}} (a : X ⟶ Y) (b : Y ⟶ Z) (ab : X ⟶ Z)
    (hab : a ≫ b = ab) (M : Z.Modules) :
    (pullModComp a b ab hab M).inv =
      (Scheme.Modules.pullbackComp a b).hom.app M ≫
        (Scheme.Modules.pullbackCongr hab).hom.app M := by
  rw [← Iso.symm_hom, pullModComp_symm_app]
  simp only [Iso.app_hom, Iso.trans_hom, NatTrans.comp_app]
  rfl

end PullModComp

/-! ### A morphism of inverse images, read on the underlying schemes -/

section Zariski

variable {U V W : BigFppfOver B S hS}

attribute [local implicit_reducible] AlgebraicGeometry.Space.smallEtaleRingedSite

/-- **A morphism of the inverse images of Stacks 03LU of two quasi-coherent `𝒪`-modules along a
morphism of representable algebraic spaces, read on the underlying schemes.**  It is the
morphism of the inverse images on the small étale sites restricted to the small Zariski sites,
conjugated by the comparison
`AlgebraicGeometry.Space.representedZariskiModulePullbackIso`. -/
def zariskiHomOn (g : V ⟶ U)
    {M N : SheafOfModules.{u} (representedStructureRingSheaf B S hS U)}
    (hM : M.IsQuasicoherentOnSite) (hN : N.IsQuasicoherentOnSite)
    (w : (modulePullback B S hS (representedSpaceMap B S hS g)).obj M ⟶
      (modulePullback B S hS (representedSpaceMap B S hS g)).obj N) :
    pullMod (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) g.left)
        (representedZariskiModule B S hS U M) ⟶
      pullMod (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) g.left)
        (representedZariskiModule B S hS U N) :=
  (representedZariskiModulePullbackIso B S hS g
      (relativelyRepresentable_yoneda_map B S hS g) M hM).hom ≫
    (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj V) V.left.property).map
      ((representedSmallEtaleModuleEquivalence B S hS V).inverse.map w) ≫
    (representedZariskiModulePullbackIso B S hS g
      (relativelyRepresentable_yoneda_map B S hS g) N hN).inv

/-- `AlgebraicGeometry.Space.QuasiCoherentDescent.zariskiHomOn` written out as the morphism of
the restrictions conjugated by the comparison of inverse images. -/
theorem zariskiHomOn_eq (g : V ⟶ U)
    {M N : SheafOfModules.{u} (representedStructureRingSheaf B S hS U)}
    (hM : M.IsQuasicoherentOnSite) (hN : N.IsQuasicoherentOnSite)
    (w : (modulePullback B S hS (representedSpaceMap B S hS g)).obj M ⟶
      (modulePullback B S hS (representedSpaceMap B S hS g)).obj N) :
    zariskiHomOn B S hS g hM hN w =
      (representedZariskiModulePullbackIso B S hS g
          (relativelyRepresentable_yoneda_map B S hS g) M hM).hom ≫
        (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj V) V.left.property).map
          ((representedSmallEtaleModuleEquivalence B S hS V).inverse.map w) ≫
        (representedZariskiModulePullbackIso B S hS g
          (relativelyRepresentable_yoneda_map B S hS g) N hN).inv := rfl

/-- The comparison of the iterated inverse images along the schemes underlying `p` and `k`,
inverted, is the comparison of the two pullback functors of modules on schemes. -/
private theorem pullModComp_inv_eq_pullbackComp (p : W ⟶ V) (k : V ⟶ U)
    (hc : _root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) p.left ≫
        _root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) k.left =
      _root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) (p ≫ k).left)
    (M : SheafOfModules.{u} (representedStructureRingSheaf B S hS U)) :
    (pullModComp
          (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) p.left)
          (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) k.left)
          (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) (p ≫ k).left)
          hc (representedZariskiModule B S hS U M)).inv =
      (Scheme.Modules.pullbackComp
          (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) p.left)
          (_root_.AlgebraicGeometry.SmallEtale.schemeHom
            (associatedBigEtaleSite B) k.left)).hom.app
        (representedZariskiModule B S hS U M) := by
  rw [pullModComp_inv_eq, pullbackCongr_hom_app_eq_id, Category.comp_id]

/-- The restricted reading of Stacks 04W3 at a composite of represented morphisms, read on the
schemes, commutes with the contraction
`AlgebraicGeometry.Space.representedModulePullbackCompIso` of the two inverse images. -/
private theorem map_restrictForm_representedSpaceMap_eq (p : W ⟶ V) (k : V ⟶ U)
    (hr : representedSpaceMap B S hS p ≫ representedSpaceMap B S hS k =
      representedSpaceMap B S hS (p ≫ k))
    {M N : SheafOfModules.{u} (representedStructureRingSheaf B S hS U)}
    (w : (modulePullback B S hS (representedSpaceMap B S hS k)).obj M ⟶
      (modulePullback B S hS (representedSpaceMap B S hS k)).obj N) :
    (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj W) W.left.property).map
        ((representedSmallEtaleModuleEquivalence B S hS W).inverse.map
          ((representedModulePullbackCompIso B S hS p k).hom.app M)) ≫
      (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj W) W.left.property).map
        ((representedSmallEtaleModuleEquivalence B S hS W).inverse.map
          (restrictForm B S hS (representedSpaceMap B S hS p) (representedSpaceMap B S hS k)
            (representedSpaceMap B S hS (p ≫ k)) hr w)) =
    (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj W) W.left.property).map
      ((representedSmallEtaleModuleEquivalence B S hS W).inverse.map
        ((modulePullback B S hS (representedSpaceMap B S hS p)).map w)) ≫
    (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj W) W.left.property).map
      ((representedSmallEtaleModuleEquivalence B S hS W).inverse.map
        ((representedModulePullbackCompIso B S hS p k).hom.app N)) := by
  rw [restrictForm_representedSpaceMap, ← Functor.map_comp, ← Functor.map_comp,
    natIso_hom_app_conj, Functor.map_comp, Functor.map_comp]

/-- **The reading on the schemes, restricted along a further morphism.**  Restricting
`AlgebraicGeometry.Space.QuasiCoherentDescent.zariskiHomOn` of `w` along the morphism of schemes
underlying `p` is the reading on the schemes of the restricted reading of `w` along `p`. -/
theorem pullHom_zariskiHomOn (p : W ⟶ V) (k : V ⟶ U) (ρ : W ⟶ U) (hρ : p ≫ k = ρ)
    (hr : representedSpaceMap B S hS p ≫ representedSpaceMap B S hS k =
      representedSpaceMap B S hS ρ)
    (hc : _root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) p.left ≫
        _root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) k.left =
      _root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) ρ.left)
    {M N : SheafOfModules.{u} (representedStructureRingSheaf B S hS U)}
    (hM : M.IsQuasicoherentOnSite) (hN : N.IsQuasicoherentOnSite)
    (w : (modulePullback B S hS (representedSpaceMap B S hS k)).obj M ⟶
      (modulePullback B S hS (representedSpaceMap B S hS k)).obj N) :
    pullHom (zariskiHomOn B S hS k hM hN w)
        (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) p.left)
        (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) ρ.left)
        (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) ρ.left)
        hc hc =
      zariskiHomOn B S hS ρ hM hN
        (restrictForm B S hS (representedSpaceMap B S hS p) (representedSpaceMap B S hS k)
          (representedSpaceMap B S hS ρ) hr w) := by
  subst hρ
  have hp := relativelyRepresentable_yoneda_map B S hS p
  have hk := relativelyRepresentable_yoneda_map B S hS k
  have h12 := fun (X : SheafOfModules.{u} (representedStructureRingSheaf B S hS U))
      (hX : X.IsQuasicoherentOnSite) ↦
    pullModComp_inv_eq_pullbackComp B S hS p k hc X ▸
      representedZariskiModulePullbackIso_comp B S hS p k hp hk
        (relativelyRepresentable_yoneda_map B S hS (p ≫ k)) X hX
  have h3 := representedZariskiModulePullbackIso_naturality B S hS p hp
    (isQuasicoherentOnSite_modulePullback_representedSpaceMap B S hS k hk M hM)
    (isQuasicoherentOnSite_modulePullback_representedSpaceMap B S hS k hk N hN) w
  have h4 := map_restrictForm_representedSpaceMap_eq B S hS p k hr w
  rw [pullHom_eq_conj (zariskiHomOn B S hS k hM hN w)
    (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) p.left)
    (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) (p ≫ k).left)
    (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) (p ≫ k).left)
    hc hc]
  exact map_conj_eq_conj
    (Scheme.Modules.pullback (_root_.AlgebraicGeometry.SmallEtale.schemeHom
      (associatedBigEtaleSite B) p.left)) _ _ _ _ _ _ _ _ _ _ _ _ _
    (zariskiHomOn B S hS k hM hN w) _ (zariskiHomOn_eq B S hS k hM hN w)
    (zariskiHomOn_eq B S hS (p ≫ k) hM hN _) (h12 M hM) (h12 N hN) h3 h4

end Zariski

/-! ### A test object for a pair of members of a family -/

section PairTest

variable {U T₁ T₂ : BigFppfOver B S hS}

/-- **The fibre product of two members of a family over `U`, taken in the big fppf category over
`S`, is a test object for the pair.**  It carries two projections agreeing over `U`, and every
pair of morphisms of schemes into the schemes underlying the two members agreeing over `U`
factors through the scheme underlying it. -/
theorem exists_pairTestObject (g₁ : T₁ ⟶ U) (g₂ : T₂ ⟶ U) :
    ∃ (W : BigFppfOver B S hS) (p : W ⟶ T₁) (q : W ⟶ T₂), p ≫ g₁ = q ≫ g₂ ∧
      ∀ (Y : Scheme.{u}) (d₁ : Y ⟶ (BigFppfOver.toScheme B S hS).obj T₁)
        (d₂ : Y ⟶ (BigFppfOver.toScheme B S hS).obj T₂),
        d₁ ≫ _root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) g₁.left =
            d₂ ≫ _root_.AlgebraicGeometry.SmallEtale.schemeHom
              (associatedBigEtaleSite B) g₂.left →
        ∃ ℓ : Y ⟶ (BigFppfOver.toScheme B S hS).obj W,
          ℓ ≫ _root_.AlgebraicGeometry.SmallEtale.schemeHom
              (associatedBigEtaleSite B) p.left = d₁ ∧
          ℓ ≫ _root_.AlgebraicGeometry.SmallEtale.schemeHom
              (associatedBigEtaleSite B) q.left = d₂ :=
  ⟨(BigFppfOver.siteFibreProduct B S hS g₁ g₂).pullback,
    (BigFppfOver.siteFibreProduct B S hS g₁ g₂).p₁,
    (BigFppfOver.siteFibreProduct B S hS g₁ g₂).p₂,
    (BigFppfOver.siteFibreProduct B S hS g₁ g₂).condition,
    fun _ d₁ d₂ hd ↦
      ⟨(BigFppfOver.isPullback_map_siteFibreProduct B S hS g₁ g₂).lift d₁ d₂ hd,
        (BigFppfOver.isPullback_map_siteFibreProduct B S hS g₁ g₂).lift_fst d₁ d₂ hd,
        (BigFppfOver.isPullback_map_siteFibreProduct B S hS g₁ g₂).lift_snd d₁ d₂ hd⟩⟩

end PairTest

/-! ### The fullness half of Stacks 023T over a represented base -/

section Main

variable {J : Type v} {U : BigFppfOver B S hS}

attribute [local implicit_reducible] AlgebraicGeometry.Space.smallEtaleRingedSite

/-- **The family of readings on the schemes of a pairwise compatible family is compatible.**  Two
of its members agree after restriction to an arbitrary scheme mapping to the two members of the
family. -/
theorem pullHom_zariskiHomOn_eq_of_isPairwiseCompatible (T : J → BigFppfOver B S hS)
    (g : ∀ j, T j ⟶ U) {M N : SheafOfModules.{u} (representedStructureRingSheaf B S hS U)}
    (hM : M.IsQuasicoherentOnSite) (hN : N.IsQuasicoherentOnSite)
    (w : ∀ j, (modulePullback B S hS (representedSpaceMap B S hS (g j))).obj M ⟶
      (modulePullback B S hS (representedSpaceMap B S hS (g j))).obj N)
    (hw : IsPairwiseCompatible B S hS (fun j => representedAlgebraicSpace B S hS (T j))
      (fun j => representedSpaceMap B S hS (g j)) w)
    (Y : Scheme.{u}) (y : Y ⟶ (BigFppfOver.toScheme B S hS).obj U) (j₁ j₂ : J)
    (d₁ : Y ⟶ (BigFppfOver.toScheme B S hS).obj (T j₁))
    (d₂ : Y ⟶ (BigFppfOver.toScheme B S hS).obj (T j₂))
    (hd₁ : d₁ ≫ _root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B)
      (g j₁).left = y)
    (hd₂ : d₂ ≫ _root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B)
      (g j₂).left = y) :
    pullHom (zariskiHomOn B S hS (g j₁) hM hN (w j₁)) d₁ y y hd₁ hd₁ =
      pullHom (zariskiHomOn B S hS (g j₂) hM hN (w j₂)) d₂ y y hd₂ hd₂ := by
  obtain ⟨W, p, q, hpq, hfac⟩ := exists_pairTestObject B S hS (g j₁) (g j₂)
  obtain ⟨ℓ, hl₁, hl₂⟩ := hfac Y d₁ d₂ (hd₁.trans hd₂.symm)
  subst hl₁ hl₂
  have hc₁ : _root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) p.left ≫
        _root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) (g j₁).left =
      _root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B)
        (p ≫ g j₁).left :=
    ((BigFppfOver.toScheme B S hS).map_comp p (g j₁)).symm
  have hc₂ : _root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) q.left ≫
        _root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) (g j₂).left =
      _root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B)
        (p ≫ g j₁).left :=
    ((BigFppfOver.toScheme B S hS).map_comp q (g j₂)).symm.trans
      (congrArg (BigFppfOver.toScheme B S hS).map hpq.symm)
  have hA : ℓ ≫ _root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B)
      (p ≫ g j₁).left = y := by
    rwa [← hc₁, ← Category.assoc]
  have hr₁ : representedSpaceMap B S hS p ≫ representedSpaceMap B S hS (g j₁) =
      representedSpaceMap B S hS (p ≫ g j₁) := representedSpaceMap_comp B S hS p (g j₁)
  have hr₂ : representedSpaceMap B S hS q ≫ representedSpaceMap B S hS (g j₂) =
      representedSpaceMap B S hS (p ≫ g j₁) :=
    (representedSpaceMap_comp B S hS q (g j₂)).trans
      (congrArg (fun z : W ⟶ U ↦ representedSpaceMap B S hS z) hpq.symm)
  have key : pullHom (zariskiHomOn B S hS (g j₁) hM hN (w j₁))
        (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) p.left)
        (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B)
          (p ≫ g j₁).left)
        (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B)
          (p ≫ g j₁).left) hc₁ hc₁ =
      pullHom (zariskiHomOn B S hS (g j₂) hM hN (w j₂))
        (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) q.left)
        (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B)
          (p ≫ g j₁).left)
        (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B)
          (p ≫ g j₁).left) hc₂ hc₂ := by
    rw [pullHom_zariskiHomOn B S hS p (g j₁) (p ≫ g j₁) rfl hr₁ hc₁ hM hN (w j₁),
      pullHom_zariskiHomOn B S hS q (g j₂) (p ≫ g j₁) hpq.symm hr₂ hc₂ hM hN (w j₂)]
    exact congrArg (zariskiHomOn B S hS (p ≫ g j₁) hM hN)
      (restrictForm_eq_of_isPairwiseCompatible B S hS
        (fun j ↦ representedAlgebraicSpace B S hS (T j))
        (fun j ↦ representedSpaceMap B S hS (g j)) w hw j₁ j₂
        (representedSpaceMap B S hS p) (representedSpaceMap B S hS q)
        (representedSpaceMap B S hS (p ≫ g j₁)) hr₁ hr₂)
  refine ((pullHom_pullHom (zariskiHomOn B S hS (g j₁) hM hN (w j₁)) _ _ _ ℓ y y
      hc₁ hc₁ hA hA).symm.trans ?_).trans
    (pullHom_pullHom (zariskiHomOn B S hS (g j₂) hM hN (w j₂)) _ _ _ ℓ y y hc₂ hc₂ hA hA)
  exact congrArg (fun z ↦ pullHom z ℓ y y hA hA) key

/-- **The two spellings of the morphism of representable algebraic spaces attached to a morphism
of the big fppf category over `S` act the same on morphisms of modules.**  The inverse images
of Stacks 03LU along `AlgebraicGeometry.Space.QuasiCoherentDescent.reprSpaceMap` and along
`AlgebraicGeometry.Space.representedSpaceMap` agree on morphisms. -/
theorem modulePullback_reprSpaceMap_map {V : BigFppfOver B S hS} (g : V ⟶ U)
    {M N : SheafOfModules.{u} (representedStructureRingSheaf B S hS U)} (χ : M ⟶ N) :
    (modulePullback B S hS (reprSpaceMap B S hS g)).map χ =
      (modulePullback B S hS (representedSpaceMap B S hS g)).map χ := by
  congr 1

/-- **A quasi-coherent `𝒪`-module on a representable algebraic space is quasi-coherent on the
underlying scheme.** -/
theorem isQuasicoherent_representedZariskiModule
    (M : SheafOfModules.{u} (representedStructureRingSheaf B S hS U))
    (hM : M.IsQuasicoherentOnSite) :
    SheafOfModules.IsQuasicoherent (representedZariskiModule B S hS U M) :=
  _root_.AlgebraicGeometry.SmallEtale.isQuasicoherent_restrictModule (associatedBigEtaleSite B)
    ((BigFppfOver.toScheme B S hS).obj U) U.left.property
    ((representedSmallEtaleModuleEquivalence B S hS U).inverse.obj M)
    (isQuasicoherentOnSite_representedSmallEtaleInverse B S hS U M hM)

/-- **An fpqc covering of a representable algebraic space by representable algebraic spaces is
an fpqc covering of the underlying schemes.** -/
theorem mem_fpqcPrecoverage_of_isFpqcCovering (T : J → BigFppfOver B S hS) (g : ∀ j, T j ⟶ U)
    (hcov : IsFpqcCovering B S hS fun j => yoneda.map (g j)) :
    Presieve.ofArrows (fun j => (BigFppfOver.toScheme B S hS).obj (T j))
        (fun j => (BigFppfOver.toScheme B S hS).map (g j)) ∈
      Scheme.fpqcPrecoverage.{u} ((BigFppfOver.toScheme B S hS).obj U) :=
  isFpqcCovering_yoneda_of_isCovering B S hS T U g
    ⟨AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U,
      fun j ↦ AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS (T j), hcov⟩

/-- **The family of readings on the schemes descends.**  The readings on the schemes of a
pairwise compatible family, along an fpqc covering, are the pullbacks of a single morphism
between the two quasi-coherent sheaves of modules on the scheme underlying `U`. -/
theorem exists_map_eq_zariskiHomOn (T : J → BigFppfOver B S hS) (g : ∀ j, T j ⟶ U)
    (hcov : IsFpqcCovering B S hS fun j => yoneda.map (g j))
    {M N : SheafOfModules.{u} (representedStructureRingSheaf B S hS U)}
    (hM : M.IsQuasicoherentOnSite) (hN : N.IsQuasicoherentOnSite)
    (w : ∀ j, (modulePullback B S hS (representedSpaceMap B S hS (g j))).obj M ⟶
      (modulePullback B S hS (representedSpaceMap B S hS (g j))).obj N)
    (hw : IsPairwiseCompatible B S hS (fun j => representedAlgebraicSpace B S hS (T j))
      (fun j => representedSpaceMap B S hS (g j)) w) :
    ∃ τ : representedZariskiModule B S hS U M ⟶ representedZariskiModule B S hS U N, ∀ j,
      (Scheme.Modules.pullback (_root_.AlgebraicGeometry.SmallEtale.schemeHom
          (associatedBigEtaleSite B) (g j).left)).map τ =
        zariskiHomOn B S hS (g j) hM hN (w j) :=
  QuasicoherentDescentData.exists_map_eq_of_pullHom_compatible
    (V := (BigFppfOver.toScheme B S hS).obj U)
    ⟨J, fun j ↦ (BigFppfOver.toScheme B S hS).obj (T j),
      fun j ↦ _root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B)
        (g j).left⟩
    (mem_fpqcPrecoverage_of_isFpqcCovering B S hS T g hcov)
    (representedZariskiModule B S hS U M) (representedZariskiModule B S hS U N)
    (isQuasicoherent_representedZariskiModule B S hS M hM)
    (isQuasicoherent_representedZariskiModule B S hS N hN)
    (fun j ↦ zariskiHomOn B S hS (g j) hM hN (w j))
    (fun {Y} y j₁ j₂ d₁ d₂ hd₁ hd₂ ↦ pullHom_zariskiHomOn_eq_of_isPairwiseCompatible
      B S hS T g hM hN w hw Y y j₁ j₂ d₁ d₂ hd₁ hd₂)

/-- **The inverse images of the descended morphism are the given family.**  A morphism `χ` of
`𝒪`-modules on the representable algebraic space whose reading on the underlying scheme is the
descended morphism has, along each member of the family, the given member as its inverse
image. -/
theorem modulePullback_map_eq_of_representedZariski_map_eq (T : J → BigFppfOver B S hS)
    (g : ∀ j, T j ⟶ U) {M N : SheafOfModules.{u} (representedStructureRingSheaf B S hS U)}
    (hM : M.IsQuasicoherentOnSite) (hN : N.IsQuasicoherentOnSite)
    (w : ∀ j, (modulePullback B S hS (representedSpaceMap B S hS (g j))).obj M ⟶
      (modulePullback B S hS (representedSpaceMap B S hS (g j))).obj N)
    (τ : representedZariskiModule B S hS U M ⟶ representedZariskiModule B S hS U N)
    (hτ : ∀ j, (Scheme.Modules.pullback (_root_.AlgebraicGeometry.SmallEtale.schemeHom
        (associatedBigEtaleSite B) (g j).left)).map τ = zariskiHomOn B S hS (g j) hM hN (w j))
    (χ : M ⟶ N)
    (hχ : (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj U) U.left.property).map
      ((representedSmallEtaleModuleEquivalence B S hS U).inverse.map χ) = τ) (j : J) :
    (modulePullback B S hS (representedSpaceMap B S hS (g j))).map χ = w j := by
  refine (bijective_representedZariski_map B S hS
    ((modulePullback B S hS (representedSpaceMap B S hS (g j))).obj M)
    ((modulePullback B S hS (representedSpaceMap B S hS (g j))).obj N)
    (isQuasicoherentOnSite_modulePullback_representedSpaceMap B S hS (g j)
      (relativelyRepresentable_yoneda_map B S hS (g j)) M hM)).1 ?_
  have hnat := representedZariskiModulePullbackIso_naturality B S hS (g j)
    (relativelyRepresentable_yoneda_map B S hS (g j)) hM hN χ
  rw [hχ, hτ j, zariskiHomOn_eq, Category.assoc, Category.assoc, Iso.inv_hom_id,
    Category.comp_id] at hnat
  exact ((Iso.cancel_iso_hom_left _ _ _).1 hnat).symm

/-- **A pairwise compatible family of morphisms of the inverse images of two quasi-coherent
`𝒪`-modules on a representable algebraic space, along an fpqc covering of it by representable
algebraic spaces, is the family of the inverse images of a morphism of those modules.** -/
theorem exists_modulePullback_map_eq_representedSpaceMap (T : J → BigFppfOver B S hS)
    (g : ∀ j, T j ⟶ U) (hcov : IsFpqcCovering B S hS fun j => yoneda.map (g j))
    {M N : SheafOfModules.{u} (representedStructureRingSheaf B S hS U)}
    (hM : M.IsQuasicoherentOnSite) (hN : N.IsQuasicoherentOnSite)
    (w : ∀ j, (modulePullback B S hS (representedSpaceMap B S hS (g j))).obj M ⟶
      (modulePullback B S hS (representedSpaceMap B S hS (g j))).obj N)
    (hw : IsPairwiseCompatible B S hS (fun j => representedAlgebraicSpace B S hS (T j))
      (fun j => representedSpaceMap B S hS (g j)) w) :
    ∃ χ : M ⟶ N,
      ∀ j, (modulePullback B S hS (representedSpaceMap B S hS (g j))).map χ = w j := by
  obtain ⟨τ, hτ⟩ := exists_map_eq_zariskiHomOn B S hS T g hcov hM hN w hw
  obtain ⟨χ, hχ⟩ := (bijective_representedZariski_map B S hS M N hM).2 τ
  exact ⟨χ, modulePullback_map_eq_of_representedZariski_map_eq B S hS T g hM hN w τ hτ χ hχ⟩

/-- **The fullness half of Stacks 023T, read on represented algebraic spaces and on
quasi-coherent modules**, in the form
`AlgebraicGeometry.Space.QuasiCoherentDescent.ReprFpqcHomSurjective`. -/
theorem reprFpqcHomSurjective : ReprFpqcHomSurjective.{u, v} B S hS := by
  intro J' U' T g hcov M N hM hN w hw
  obtain ⟨χ, hχ⟩ :=
    exists_modulePullback_map_eq_representedSpaceMap B S hS (U := U') T g hcov hM hN w hw
  exact ⟨χ, fun j ↦ (modulePullback_reprSpaceMap_map B S hS (g j) χ).trans (hχ j)⟩

/-- **The fullness half of the full-faithfulness clause of Stacks 04W8, with no hypothesis.**
The canonical descent functor of Stacks 04W5, from the quasi-coherent `𝒪_X`-modules of
Stacks 03G9 to the descent data of Stacks 04W3 relative to an fpqc covering
`(f i : X i ⟶ X)` of algebraic spaces in the sense of Stacks 03MQ, is full. -/
theorem full_canonicalDescentFunctor_of_isFpqcCovering' {I : Type v}
    {X : AlgebraicSpaces B S hS} (Xi : I → AlgebraicSpaces B S hS) (f : ∀ i, Xi i ⟶ X)
    (hf : IsFpqcCovering B S hS fun i => (f i).hom) :
    (canonicalDescentFunctor' B S hS Xi f).Full :=
  full_canonicalDescentFunctor_of_isFpqcCovering B S hS Xi f
    (reprFpqcHomSurjective.{u, v} B S hS) hf

/-- **The full-faithfulness clause of Stacks 04W8, with no hypothesis.**  The canonical descent
functor of Stacks 04W5 of an fpqc covering of algebraic spaces in the sense of Stacks 03MQ is
fully faithful. -/
theorem nonempty_fullyFaithful_canonicalDescentFunctor_of_isFpqcCovering {I : Type v}
    {X : AlgebraicSpaces B S hS} (Xi : I → AlgebraicSpaces B S hS) (f : ∀ i, Xi i ⟶ X)
    (hf : IsFpqcCovering B S hS fun i => (f i).hom) :
    Nonempty (canonicalDescentFunctor' B S hS Xi f).FullyFaithful :=
  have := full_canonicalDescentFunctor_of_isFpqcCovering'.{u, v} B S hS Xi f hf
  have := faithful_canonicalDescentFunctor_of_isFpqcCovering B S hS Xi f hf
  ⟨Functor.FullyFaithful.ofFullyFaithful _⟩

end Main

end AlgebraicGeometry.Space.QuasiCoherentDescent

end
