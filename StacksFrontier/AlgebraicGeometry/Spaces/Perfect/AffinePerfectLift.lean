module

public import StacksFrontier.AlgebraicGeometry.Duality.CompactGeneration.AffinePerfectLift
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.AffineKoszulGenerator
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.PerfectQuasicoherentCohomology
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RepresentedPerfectAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RepresentedPerfectConverseGeneral

/-!
# Lifting a perfect object from a quasi-compact open of an affine algebraic space

Let `V` be an affine algebraic space, `i : Y ⟶ V` an open immersion with `Y` quasi-compact and
`M` a perfect object of `D(𝒪_Y)`. There is a perfect object `B` of `D(𝒪_V)` with
`B|_Y ≅ M ⊕ M[1]`. This is the affine input of the proof of Stacks 09IX.

With `V = h_{Spec A}` and `Y = h_{T'}` for an open immersion of schemes `T' ⟶ Spec A`: `M` has
quasi-coherent cohomology (Stacks 08JL), so `M ≅ ε^*N` (Stacks 071Q); `N` is perfect (the converse
of Stacks 08HG,
`AlgebraicGeometry.Space.isPerfect_of_isPerfect_representedDerivedAssociatedModule_of_scheme`);
the scheme lift `Stacks.Duality.QcqsGeneration.exists_isPerfectComplex_pullback_iso_biprod_shift`
([Stacks, Tag 08EK]) gives `Q` on `Spec A` with `Q|_{T'} ≅ N ⊕ N[1]`, and `B = ε^*Q` (forward
Stacks 08HG). The general case is moved there along isomorphisms.

## Main results

* `AlgebraicGeometry.Space.exists_isPerfect_restrict_iso_biprod_shift_of_isAffineSpace`.

## References

* [Stacks Project, Tag 08EK](https://stacks.math.columbia.edu/tag/08EK)
* [Stacks Project, Tag 08HG](https://stacks.math.columbia.edu/tag/08HG)
* [Stacks Project, Tag 09IX](https://stacks.math.columbia.edu/tag/09IX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

attribute [local instance]
  _root_.AlgebraicGeometry.SmallEtale.preservesFiniteLimits_associatedModule
  etaleModulePullback_additive preservesFiniteLimits_etaleModulePullback
  preservesFiniteColimits_etaleModulePullback

attribute [local instance] preservesBinaryBiproducts_of_preservesBiproducts

attribute [local instance 10000] HasDerivedCategory.standard

/-- An additive functor commuting with shifts carries `X ⊕ X[1]` to `G X ⊕ (G X)[1]`. -/
def mapBiprodShiftOneIso {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    [HasBinaryBiproducts C] [HasBinaryBiproducts D] [HasShift C ℤ] [HasShift D ℤ]
    (G : C ⥤ D) [G.Additive] [G.CommShift ℤ] (X : C) :
    G.obj (X ⊞ X⟦(1 : ℤ)⟧) ≅ G.obj X ⊞ (G.obj X)⟦(1 : ℤ)⟧ :=
  G.mapBiprod _ _ ≪≫ biprod.mapIso (Iso.refl _) ((G.commShiftIso (1 : ℤ)).app X)

/-- `X ≅ Y` gives `X ⊕ X[1] ≅ Y ⊕ Y[1]`. -/
def biprodShiftOneMapIso {C : Type*} [Category C] [Preadditive C] [HasBinaryBiproducts C]
    [HasShift C ℤ] {X Y : C} (e : X ≅ Y) : X ⊞ X⟦(1 : ℤ)⟧ ≅ Y ⊞ Y⟦(1 : ℤ)⟧ :=
  biprod.mapIso e ((shiftFunctor C (1 : ℤ)).mapIso e)

variable {B S hS} in
/-- **The lift on a represented affine space.** Let `j : T' ⟶ Spec A` be a morphism of the big
fppf site whose scheme map is an open immersion with quasi-compact source, and `M` a perfect
object of `D(𝒪_{h_{T'}})`. There is a perfect object `B` of `D(𝒪_{h_{Spec A}})` whose pullback to
`h_{T'}` is `M ⊕ M[1]`. -/
theorem exists_isPerfect_representedDerivedPullback_iso_biprod_shift {A : Type u} [CommRing A]
    (hA : B.Contains (Spec (CommRingCat.of A))) (p : Spec (CommRingCat.of A) ⟶ S)
    {T' : BigFppfOver B S hS} (j : T' ⟶ BigFppfOver.mk B S hS hA p)
    [_root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map j)]
    [CompactSpace ((BigFppfOver.toScheme B S hS).obj T')]
    (hj : IsEtale B S hS (representedSpaceMap B S hS j).hom)
    (M : DerivedCategory
      (Modules.{u, u} B S hS (yoneda.obj T') (isAlgebraicSpace_yoneda B S hS T')))
    (hM : (smallEtaleRingedSite B S hS (yoneda.obj T')
      (isAlgebraicSpace_yoneda B S hS T')).IsPerfect M) :
    ∃ Bo : DerivedCategory (Modules.{u, u} B S hS (yoneda.obj (BigFppfOver.mk B S hS hA p))
        (isAlgebraicSpace_yoneda B S hS _)),
      (smallEtaleRingedSite B S hS (yoneda.obj (BigFppfOver.mk B S hS hA p))
        (isAlgebraicSpace_yoneda B S hS _)).IsPerfect Bo ∧
      Nonempty ((representedDerivedPullback B S hS j hj).obj Bo ≅ M ⊞ M⟦(1 : ℤ)⟧) := by
  have hMq := derivedCategoryB_isQuasicoherentOnSite_of_isPerfect_of_isAlgebraicSpace B S hS
    (yoneda.obj T') (isAlgebraicSpace_yoneda B S hS T') M hM
  obtain ⟨N, hNq, ⟨eN⟩⟩ := exists_representedDerivedAssociatedModule_iso B S hS T' M hMq
  have hN : Stacks.Cohomology.PerfectComplexes.IsPerfect
      (X := ((BigFppfOver.toScheme B S hS).obj T').toRingedSpace) N := by
    refine isPerfect_of_isPerfect_representedDerivedAssociatedModule_of_scheme B S hS T' N hNq ?_
    obtain ⟨E, hE, ⟨e⟩⟩ := hM
    exact ⟨E, hE, ⟨e ≪≫ eN.symm⟩⟩
  obtain ⟨N₀, hN₀, ⟨eN₀⟩⟩ : ∃ N₀ : CochainComplex ((BigFppfOver.toScheme B S hS).obj T').Modules ℤ,
      RingedSpace.IsPerfectComplex (X := ((BigFppfOver.toScheme B S hS).obj T').toRingedSpace) N₀ ∧
        Nonempty (DerivedCategory.Q.obj N₀ ≅ N) := hN
  let f : (BigFppfOver.toScheme B S hS).obj T' ⟶ Spec (CommRingCat.of A) :=
    (BigFppfOver.toScheme B S hS).map j
  have : _root_.AlgebraicGeometry.IsOpenImmersion f :=
    ‹_root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map j)›
  obtain ⟨Q₀, hQ₀, ⟨eQ⟩⟩ :=
    Stacks.Duality.QcqsGeneration.exists_isPerfectComplex_pullback_iso_biprod_shift (A := A) f N₀
      hN₀
  refine ⟨(representedDerivedAssociatedModule B S hS (BigFppfOver.mk B S hS hA p)).obj
    (DerivedCategory.Q.obj Q₀), ?_, ⟨?_⟩⟩
  · exact isPerfect_representedDerivedAssociatedModule_of_isPerfect B S hS hA p _
      (RingedSpace.IsPerfectComplex.isPerfect.{u, u + 1} hQ₀)
  · let ε' := representedAssociatedModule B S hS T' (isAlgebraicSpace_yoneda B S hS T')
    let c := ComplexShape.up ℤ
    exact (representedDerivedAssociatedModulePullbackIso B S hS j hj).app _ ≪≫
      ε'.mapDerivedCategory.mapIso
        ((Scheme.Modules.derivedPullbackIsoMapDerivedCategory f).app _ ≪≫
          (Scheme.Modules.pullback f).mapDerivedCategoryFactors.app Q₀ ≪≫ eQ) ≪≫
      ε'.mapDerivedCategoryFactors.app _ ≪≫
      DerivedCategory.Q.mapIso (mapBiprodShiftOneIso (ε'.mapHomologicalComplex c) N₀) ≪≫
      mapBiprodShiftOneIso DerivedCategory.Q _ ≪≫
      biprodShiftOneMapIso ((ε'.mapDerivedCategoryFactors.app N₀).symm ≪≫
        ε'.mapDerivedCategory.mapIso eN₀ ≪≫ eN)

variable {B S hS} in
/-- **The lift moves along isomorphisms of algebraic spaces.** Let `r : W ≅ V` and `s : Y' ≅ Y`
be isomorphisms and `i' : Y' ⟶ W`, `i : Y ⟶ V` étale with `s ≫ i = i' ≫ r`. If every perfect
object of `D(𝒪_{Y'})` is, up to `M ↦ M ⊕ M[1]`, the restriction of a perfect object of `D(𝒪_W)`,
the same holds for `Y ⟶ V`. -/
theorem exists_isPerfect_restrict_iso_biprod_shift_of_iso {W V Y' Y : AlgebraicSpaces B S hS}
    (r : W ≅ V) (s : Y' ≅ Y) (i' : Y' ⟶ W) (i : Y ⟶ V) (hi' : IsEtale B S hS i'.hom)
    (hi : IsEtale B S hS i.hom) (hsq : s.hom ≫ i = i' ≫ r.hom)
    (h : ∀ M' : DerivedCategory (Modules.{u, u} B S hS Y'.1 Y'.2),
      (smallEtaleRingedSite B S hS Y'.1 Y'.2).IsPerfect M' →
      ∃ Bo' : DerivedCategory (Modules.{u, u} B S hS W.1 W.2),
        (smallEtaleRingedSite B S hS W.1 W.2).IsPerfect Bo' ∧
        Nonempty ((etaleModulePullback.{u, u} B S hS i' hi').mapDerivedCategory.obj Bo' ≅
          M' ⊞ M'⟦(1 : ℤ)⟧))
    (M : DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2))
    (hM : (smallEtaleRingedSite B S hS Y.1 Y.2).IsPerfect M) :
    ∃ Bo : DerivedCategory (Modules.{u, u} B S hS V.1 V.2),
      (smallEtaleRingedSite B S hS V.1 V.2).IsPerfect Bo ∧
      Nonempty ((etaleModulePullback.{u, u} B S hS i hi).mapDerivedCategory.obj Bo ≅
        M ⊞ M⟦(1 : ℤ)⟧) := by
  have hr' := isEtale_hom_of_iso B S hS r.symm
  have hs := isEtale_hom_of_iso B S hS s
  have hs' := isEtale_hom_of_iso B S hS s.symm
  have : (etaleModulePullbackEquivalenceOfIso.{u, u} B S hS s).functor.Additive :=
    etaleModulePullback_additive B S hS s.hom hs
  have : PreservesFiniteLimits
      (etaleModulePullbackEquivalenceOfIso.{u, u} B S hS s).functor :=
    preservesFiniteLimits_etaleModulePullback B S hS s.hom hs
  have : PreservesFiniteColimits
      (etaleModulePullbackEquivalenceOfIso.{u, u} B S hS s).functor :=
    preservesFiniteColimits_etaleModulePullback B S hS s.hom hs
  let Φ := Stacks.DerivedQCoh.Equivalence.mapDerivedCategory
    (etaleModulePullbackEquivalenceOfIso.{u, u} B S hS s)
  have hsq' : i ≫ r.inv = s.inv ≫ i' := by
    rw [← cancel_epi s.hom, ← Category.assoc, hsq, Category.assoc, r.hom_inv_id,
      Category.comp_id, Iso.hom_inv_id_assoc]
  obtain ⟨Bo', hBo', ⟨e⟩⟩ :=
    h ((etaleModulePullback.{u, u} B S hS s.hom hs).mapDerivedCategory.obj M)
    (isPerfect_etaleModulePullback_standard B S hS s.hom hs M hM)
  refine ⟨(etaleModulePullback.{u, u} B S hS r.inv hr').mapDerivedCategory.obj Bo',
    isPerfect_etaleModulePullback_standard B S hS r.inv hr' Bo' hBo', ⟨?_⟩⟩
  let G := (etaleModulePullback.{u, u} B S hS s.inv hs').mapDerivedCategory
  exact (Functor.mapDerivedCategorySquareIso
      (etaleModulePullbackSquareIso B S hS hi hr' hs' hi' hsq')).app Bo' ≪≫ G.mapIso e ≪≫
    mapBiprodShiftOneIso G _ ≪≫ biprodShiftOneMapIso (Φ.unitIso.app M).symm

variable {B S hS} in
/-- **Lifting a perfect object from a quasi-compact open of an affine algebraic space.** Let `V`
be an affine algebraic space over `S`, `i : Y ⟶ V` an open immersion with `Y` quasi-compact and
`M` a perfect object of `D(𝒪_Y)`. There is a perfect object `B` of `D(𝒪_V)` with
`B|_Y ≅ M ⊕ M[1]`.

This is the affine input of the proof of Stacks 09IX (there drawn from Derived Categories of
Schemes, Lemma 36.13.4, Stacks 08EK): `V ≅ h_{Spec A}` and `Y ≅ h_{T'}` for an open immersion
`T' ⟶ Spec A`, and `exists_isPerfect_representedDerivedPullback_iso_biprod_shift` applies. -/
theorem exists_isPerfect_restrict_iso_biprod_shift_of_isAffineSpace {V Y : AlgebraicSpaces B S hS}
    (hV : IsAffineSpace B S hS V.1) (i : Y ⟶ V) (hi : IsOpenImmersion B S hS i.hom)
    (hY : IsQuasiCompactSpace B S hS Y.1) (M : DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2))
    (hM : (smallEtaleRingedSite B S hS Y.1 Y.2).IsPerfect M) :
    ∃ Bo : DerivedCategory (Modules.{u, u} B S hS V.1 V.2),
      (smallEtaleRingedSite B S hS V.1 V.2).IsPerfect Bo ∧
      Nonempty ((etaleModulePullback.{u, u} B S hS i
        (isEtale_of_isOpenImmersion B S hS hi)).mapDerivedCategory.obj Bo ≅ M ⊞ M⟦(1 : ℤ)⟧) := by
  obtain ⟨T, hT, ⟨eV⟩⟩ := hV
  obtain ⟨A, _, hA, p, ⟨eT⟩⟩ := exists_iso_mk_spec B S hS T hT
  let T₀ := BigFppfOver.mk B S hS hA p
  let W : AlgebraicSpaces B S hS := ⟨yoneda.obj T₀, isAlgebraicSpace_yoneda B S hS T₀⟩
  let r : W ≅ V := ObjectProperty.isoMk _ ((yoneda.mapIso eT).symm ≪≫ eV.symm)
  -- The open immersion `Y ⟶ V ≅ h_{T₀}` is represented by an open immersion `T' ⟶ T₀`.
  have hi₀ : IsOpenImmersion B S hS (i ≫ r.inv).hom :=
    isOpenImmersion_comp B S hS i.hom r.inv.hom hi (isOpenImmersion_of_isIso B S hS r.inv.hom)
  have hpb := hi₀.rep.isPullback (𝟙 (yoneda.obj T₀))
  have : IsIso (hi₀.rep.fst (𝟙 (yoneda.obj T₀))) := hpb.isIso_fst_of_isIso
  let g := asIso (hi₀.rep.fst (𝟙 (yoneda.obj T₀)))
  let T' := hi₀.rep.pullback (𝟙 (yoneda.obj T₀))
  let j : T' ⟶ T₀ := hi₀.rep.snd (𝟙 (yoneda.obj T₀))
  have hjo : _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map j) :=
    hi₀.property_snd (𝟙 (yoneda.obj T₀))
  let s : (⟨yoneda.obj T', isAlgebraicSpace_yoneda B S hS T'⟩ : AlgebraicSpaces B S hS) ≅ Y :=
    ObjectProperty.isoMk _ g
  have hsq : s.hom ≫ i = representedSpaceMap B S hS j ≫ r.hom := by
    apply ObjectProperty.hom_ext
    have hw := hpb.w
    simp only [Category.comp_id] at hw
    change hi₀.rep.fst (𝟙 (yoneda.obj T₀)) ≫ i.hom = yoneda.map j ≫ r.hom.hom
    rw [← hw]
    change hi₀.rep.fst (𝟙 (yoneda.obj T₀)) ≫ i.hom =
      hi₀.rep.fst (𝟙 (yoneda.obj T₀)) ≫ (i.hom ≫ r.inv.hom) ≫ r.hom.hom
    rw [Category.assoc, ← ObjectProperty.FullSubcategory.comp_hom, r.inv_hom_id]
    rfl
  have hj : IsEtale B S hS (representedSpaceMap B S hS j).hom :=
    isEtale_of_presheaf_etale B S hS
      ((BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS
        (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}) j).2 inferInstance)
  have : CompactSpace ((BigFppfOver.toScheme B S hS).obj T') :=
    compactSpace_of_isQuasiCompactSpace_yoneda_obj B S hS (IsQuasiCompactSpace.of_iso B S hS hY
      g.symm)
  exact exists_isPerfect_restrict_iso_biprod_shift_of_iso r s (representedSpaceMap B S hS j) i hj _
    hsq
    (fun M' hM' => exists_isPerfect_representedDerivedPullback_iso_biprod_shift hA p j hj M' hM')
    M hM

end AlgebraicGeometry.Space

end
