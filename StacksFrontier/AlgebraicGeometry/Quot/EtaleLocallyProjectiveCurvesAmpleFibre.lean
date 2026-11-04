module

public import StacksFrontier.AlgebraicGeometry.Quot.EtaleLocallyProjectiveCurvesSchemeChart
public import StacksFrontier.AlgebraicGeometry.Quot.EtaleSchemeChartOfAmpleFibre
public import StacksFrontier.AlgebraicGeometry.AmpleDegreeCriterion.SectionVanishingCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.PointSectionZeroScheme
public import StacksFrontier.AlgebraicGeometry.Spaces.AdmissibleBlowupDominating
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupIsomorphismOffCentre
public import StacksFrontier.AlgebraicGeometry.Spaces.EffectiveCartierDivisorSumEffective
public import StacksFrontier.AlgebraicGeometry.Spaces.ZeroSchemeOfCanonicalSection
public import StacksFrontier.AlgebraicGeometry.Spaces.ClopenLiftOverHenselianPair
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowBlowupDiagramReduction
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperClosedImmersion

/-!
# Families of curves are étale locally schemes (Stacks 0E6F)

Let `X ⟶ S` be a family of curves and `s ∈ S`. On every one-dimensional irreducible component of
the fibre `X_s` choose a point `x` with a local equation isolated at `x`; at its image in `X`
take an elementary étale chart, on which the equation defines a divisor finite over an étale
neighbourhood of `s`, effective Cartier on the base change of `X`. After putting the finitely many
neighbourhoods over one étale neighbourhood `T ⟶ S` (through a lift of `Spec κ(s)`), the sum `D`
of the divisors is an effective Cartier divisor of `X_T`, and the canonical section of `𝒪(D)`
read on the fibre `X_s` vanishes at the chosen points and at no generic point of a
one-dimensional component (the divisors are finite over `T`). So `𝒪(D)` is ample on the fibre,
and `X_T` is a scheme near the fibre.

## Main results

* `AlgebraicGeometry.CurveFamily.hasEtaleSchemeChartAt`: every family of curves has an étale
  scheme chart at every point of its base (the pointwise statement of Stacks 0E6F).
* `AlgebraicGeometry.Space.isEffectiveCartierDivisor_sumClosedSubspacesList`: a sum of effective
  Cartier divisors along a list is one.
* `AlgebraicGeometry.CurveFamily.notMem_range_pointsMap_of_isFinite`: a point of the fibre which
  is not closed does not lie on a divisor finite over the base.

## Implementation notes

The ampleness on the fibre is
`AlgebraicGeometry.isAmple_of_mem_nonvanishingLocus_genericPointsOne` (from Stacks 0B5Y and
0B40), applied to the reading of the canonical section of `𝒪(D)`; where that reading vanishes is
`AlgebraicGeometry.Space.notMem_nonvanishingLocus_pointGlobalSection_iff_mem_subspacePointSet`
(Stacks 0845). The scheme chart then comes from
`AlgebraicGeometry.CurveFamily.hasEtaleSchemeChartAt_of_isAmple_fibre_of_isAffine` (Stacks 0D3D,
0D32). Stacks 0E6F is not proved here, so nothing here is registered.

## References

* [Stacks Project, Tag 0E6F](https://stacks.math.columbia.edu/tag/0E6F)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- A sum of effective Cartier divisors along a list, on an effective Cartier seed, is an effective
Cartier divisor (Stacks 083V). -/
theorem isEffectiveCartierDivisor_sumClosedSubspacesList (X : AlgebraicSpaces B S hS) {ι : Type*}
    (Z : ι → ClosedSubspaces B S hS X.1) (Z₀ : ClosedSubspaces B S hS X.1)
    (h₀ : IsEffectiveCartierDivisor B S hS X Z₀) (l : List ι)
    (h : ∀ i ∈ l, IsEffectiveCartierDivisor B S hS X (Z i)) :
    IsEffectiveCartierDivisor B S hS X (sumClosedSubspacesList X Z Z₀ l) := by
  induction l with
  | nil => exact h₀
  | cons i l ih =>
    exact isEffectiveCartierDivisor_sumClosedSubspaces B S hS X (Z i) _
      (h i List.mem_cons_self) (ih fun i' hi' => h i' (List.mem_cons_of_mem _ hi'))

/-- The empty closed subspace is an effective Cartier divisor. -/
theorem isEffectiveCartierDivisor_emptyClosedSubspace (X : AlgebraicSpaces B S hS) :
    IsEffectiveCartierDivisor B S hS X (emptyClosedSubspace X) := by
  refine isEffectiveCartierDivisor_of_isEmpty_points B S hS X _ ⟨fun p => ?_⟩
  exact (Set.eq_empty_iff_forall_notMem.1 (subspacePointSet_emptyClosedSubspace X)) _ ⟨p, rfl⟩

/-- The points of a sum of closed subspaces along a list, on the empty seed, are the points of
the summands. -/
theorem mem_subspacePointSet_sumClosedSubspacesList_iff (X : AlgebraicSpaces B S hS) {ι : Type*}
    (Z : ι → ClosedSubspaces B S hS X.1) (l : List ι) (x : points B S hS X.1) :
    x ∈ subspacePointSet B S hS X.1 (sumClosedSubspacesList X Z (emptyClosedSubspace X) l).1 ↔
      ∃ i ∈ l, x ∈ subspacePointSet B S hS X.1 (Z i).1 := by
  induction l with
  | nil =>
    simp only [sumClosedSubspacesList, subspacePointSet_emptyClosedSubspace, List.not_mem_nil,
      false_and, exists_false, Set.mem_empty_iff_false]
  | cons i l ih =>
    simp only [sumClosedSubspacesList, subspacePointSet_sumClosedSubspaces, Set.mem_union, ih,
      List.mem_cons, exists_eq_or_imp]

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.CurveFamily

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

local notation "𝒯" => BigFppfOver.toScheme B integerBase hZ

/-- Every point of the space represented by a scheme of the site is the point of a point of the
scheme. -/
theorem presheafPoint_pointsToScheme_eq (U : BigFppfOver B integerBase hZ)
    (q : Space.points B integerBase hZ (yoneda.obj U)) :
    Space.presheafPoint B integerBase hZ U (Space.pointsToScheme B integerBase hZ U q)
      (B.residueField_spec_contains U.left.property _) = q :=
  Space.injective_pointsToScheme B integerBase hZ U
    (Space.pointsToScheme_presheafPoint B integerBase hZ U _ _)

/-- **A non-closed point of the fibre lies on no divisor finite over the base.** Let `V` present
the base change of `fT : X_T ⟶ T` along `σ : F ⟶ T` from a scheme `F` with one point, and
`π : P ⟶ X_T` a closed immersion with `P` finite over `T`. A point `ζ` of `V` which is not closed
does not map into the image of `π`: the points of `V` mapping there are those of the closed
subscheme `V ×_{X_T} P = F ×_T P`, finite over `F`, all of whose points are closed. -/
theorem notMem_range_pointsMap_of_isFinite {T F V P : BigFppfOver B integerBase hZ}
    {XT : (BigFppfOver B integerBase hZ)ᵒᵖ ⥤ Type u} (fT : XT ⟶ yoneda.obj T) (σ : F ⟶ T)
    (jT : yoneda.obj V ⟶ XT) (v : V ⟶ F) (hsqT : IsPullback jT (yoneda.map v) fT (yoneda.map σ))
    (π : yoneda.obj P ⟶ XT) (hπ : Space.IsClosedImmersion B integerBase hZ π) (p : P ⟶ T)
    (hπp : π ≫ fT = yoneda.map p) [IsFinite ((𝒯).map p)] [Subsingleton ((𝒯).obj F)]
    (ζ : (𝒯).obj V) (hζ : ¬ IsClosed ({ζ} : Set ((𝒯).obj V))) :
    Space.pointsMap B integerBase hZ _ jT (Space.presheafPoint B integerBase hZ V ζ
      (B.residueField_spec_contains V.left.property ζ)) ∉
        Set.range (Space.pointsMap B integerBase hZ _ π) := by
  intro hmem
  let rel := hπ.rep
  let Q := rel.pullback jT
  let fstQ : Q ⟶ P := rel.fst' jT
  let sndQ : Q ⟶ V := rel.snd jT
  have sqQ : IsPullback (yoneda.map fstQ) (yoneda.map sndQ) π jT := rel.isPullback' jT
  have hcl : IsClosedImmersion ((𝒯).map sndQ) := hπ.property_snd jT
  -- `Q` is finite over `F`
  have sq2 :
      IsPullback (yoneda.map fstQ) (yoneda.map (sndQ ≫ v)) (yoneda.map p) (yoneda.map σ) := by
    have := sqQ.paste_vert hsqT
    rwa [← Functor.map_comp, hπp] at this
  have sq3 : IsPullback fstQ (sndQ ≫ v) p σ :=
    IsPullback.of_map yoneda (Yoneda.fullyFaithful.map_injective (by
      simpa only [Functor.map_comp] using sq2.w)) sq2
  have : IsFinite ((𝒯).map (sndQ ≫ v)) :=
    MorphismProperty.of_isPullback (sq3.map (𝒯)) ‹IsFinite ((𝒯).map p)›
  -- every point of `Q` is closed
  have hdisc : DiscreteTopology ((𝒯).obj Q) := by
    have hd := ((𝒯).map (sndQ ≫ v)).isDiscrete_preimage_singleton ((𝒯).map v ζ)
    have huniv : ((𝒯).map (sndQ ≫ v)) ⁻¹' {(𝒯).map v ζ} = Set.univ :=
      Set.eq_univ_of_forall fun _ => Subsingleton.elim _ _
    rw [huniv] at hd
    exact isDiscrete_univ_iff.1 hd
  -- `ζ` is the image of a point of `Q`
  have hpre := Space.preimage_range_pointsMap_of_isPullback B integerBase hZ sqQ
  have hζQ : Space.presheafPoint B integerBase hZ V ζ
      (B.residueField_spec_contains V.left.property ζ) ∈
        Set.range (Space.pointsMap B integerBase hZ _ (yoneda.map sndQ)) := by
    rwa [← hpre]
  obtain ⟨q, hq⟩ := hζQ
  rw [← presheafPoint_pointsToScheme_eq Q q, Space.pointsMap_presheafPoint B integerBase hZ Q V
    sndQ _ _ (B.residueField_spec_contains V.left.property _)] at hq
  have hζq : (𝒯).map sndQ (Space.pointsToScheme B integerBase hZ Q q) = ζ := by
    have := congrArg (Space.pointsToScheme B integerBase hZ V) hq
    rwa [Space.pointsToScheme_presheafPoint, Space.pointsToScheme_presheafPoint] at this
  apply hζ
  have himg := ((𝒯).map sndQ).isClosedEmbedding.isClosedMap
    {Space.pointsToScheme B integerBase hZ Q q} (isClosed_discrete _)
  rwa [Set.image_singleton, hζq] at himg

/-- **Points of a base change over a field point come from the fibre.** Let `V` present the base
change of `fT : X_T ⟶ T` along `σ : F ⟶ T`, with `j_T : V ⟶ X_T`, and let `q_T : X_T ⟶ X` be such
that `j = j_T ≫ q_T` is a monomorphism. A point `z` of `X_T` over a point in the image of `σ`
whose image in `X` is that of a point `x` of `V` is the image of `x`. -/
theorem eq_pointsMap_of_isPullback_of_mono {T F V : BigFppfOver B integerBase hZ}
    {X XT : (BigFppfOver B integerBase hZ)ᵒᵖ ⥤ Type u} (fT : XT ⟶ yoneda.obj T) (σ : F ⟶ T)
    (jT : yoneda.obj V ⟶ XT) (v : V ⟶ F) (hsqT : IsPullback jT (yoneda.map v) fT (yoneda.map σ))
    (qT : XT ⟶ X) (j : yoneda.obj V ⟶ X) (hj : jT ≫ qT = j) [Mono j]
    (z : Space.points B integerBase hZ XT) (x : Space.points B integerBase hZ (yoneda.obj V))
    (hz₁ : Space.pointsMap B integerBase hZ _ qT z = Space.pointsMap B integerBase hZ _ j x)
    (hz₂ : Space.pointsMap B integerBase hZ _ fT z ∈
      Set.range (Space.pointsMap B integerBase hZ _ (yoneda.map σ))) :
    z = Space.pointsMap B integerBase hZ _ jT x := by
  have hpre := Space.preimage_range_pointsMap_of_isPullback B integerBase hZ hsqT.flip
  obtain ⟨x', rfl⟩ : z ∈ Set.range (Space.pointsMap B integerBase hZ _ jT) := by
    rwa [← hpre]
  exact congrArg _ (Space.pointsMap_injective_of_mono B integerBase hZ j
    (by rw [← hz₁, ← hj, Space.pointsMap_comp, Function.comp_apply]))

/-- The point `w` of an étale chart over the image of a point of the fibre over `s` lies over
`s`. -/
theorem toScheme_map_apply_eq_of_pointsMap_eq (X : CurveFamily B hZ) (s : (𝒯).obj X.base)
    {V : BigFppfOver B integerBase hZ}
    (v : V ⟶ integerSiteObject B hZ (B.residueField_spec_contains X.base.left.property s))
    (j : yoneda.obj V ⟶ X.total.obj)
    (hsq : IsPullback j (yoneda.map v) X.toBase.hom (yoneda.map (residueFieldIntegerMap X s)))
    (x : (𝒯).obj V) {W : BigFppfOver B integerBase hZ} (e : yoneda.obj W ⟶ X.total.obj)
    (w : W.left.1) (hw : B.Contains (Spec (.of (W.left.1.residueField w)))) (gW : W ⟶ X.base)
    (hgW : e ≫ X.toBase.hom = yoneda.map gW)
    (hpt : Space.pointsMap B integerBase hZ _ e (Space.presheafPoint B integerBase hZ W w hw) =
      Space.pointsMap B integerBase hZ _ j (Space.presheafPoint B integerBase hZ V x
        (B.residueField_spec_contains V.left.property x))) :
    (𝒯).map gW w = s := by
  let fX : X.total.obj ⟶ yoneda.obj X.base := X.toBase.hom
  let r := residueFieldIntegerMap X s
  have hsq' : IsPullback j (yoneda.map v) fX (yoneda.map r) := hsq
  have hgW' : e ≫ fX = yoneda.map gW := hgW
  have hpp : ∀ {T : BigFppfOver B integerBase hZ} (t t' : (𝒯).obj T),
      Space.presheafPoint B integerBase hZ T t (B.residueField_spec_contains T.left.property t) =
        Space.presheafPoint B integerBase hZ T t' (B.residueField_spec_contains T.left.property t')
        → t = t' := fun t t' h => by
    have := congrArg (Space.pointsToScheme B integerBase hZ _) h
    rwa [Space.pointsToScheme_presheafPoint, Space.pointsToScheme_presheafPoint] at this
  apply hpp
  have h1 := Space.pointsMap_presheafPoint B integerBase hZ W X.base gW w hw
    (B.residueField_spec_contains X.base.left.property _)
  have h2 := Space.pointsMap_presheafPoint B integerBase hZ V X.base (v ≫ r) x
    (B.residueField_spec_contains V.left.property x)
    (B.residueField_spec_contains X.base.left.property _)
  have hr : (𝒯).map (v ≫ r) x = s := by
    rw [Functor.map_comp, Scheme.Hom.comp_apply]
    exact Scheme.fromSpecResidueField_apply _ _
  rw [← hgW', Space.pointsMap_comp, Function.comp_apply, hpt, ← Function.comp_apply
    (f := Space.pointsMap B integerBase hZ _ fX), ← Space.pointsMap_comp, hsq'.w,
    ← Functor.map_comp] at h1
  exact h1.symm.trans (h2.trans (by rw [show (v ≫ r).left.hom x = s from hr]))

open Stacks.AlgebraicGeometry.ComponentDegrees in
/-- **A family of curves is étale locally on the base a scheme (Stacks 0E6F), pointwise.** For a
family of curves `X ⟶ S` and `s ∈ S` there are an étale morphism `U ⟶ S` of the site through `s`
and a scheme `Z` of the site with a cartesian square exhibiting `Z` as `X ×_S U`. -/
theorem hasEtaleSchemeChartAt (G : CurveFamily B hZ) (s : G.base.left.1) :
    G.HasEtaleSchemeChartAt s := by
  classical
  obtain ⟨V, v, j, hsq, hdim⟩ := exists_isPullback_residueField G s
  let F₁ := integerSiteObject B hZ (B.residueField_spec_contains G.base.left.property s)
  let r := residueFieldIntegerMap G s
  let fX : G.total.obj ⟶ yoneda.obj G.base := G.toBase.hom
  have hsq' : IsPullback j (yoneda.map v) fX (yoneda.map r) := hsq
  -- the fibre is a proper scheme of dimension at most one over `κ(s)`
  have hVp : IsProper ((𝒯).map v) :=
    Space.isProper_toScheme_map_of_isProper_yoneda_map B integerBase hZ v
      (Space.isProper_of_isPullback B integerBase hZ (isAlgebraicSpace_yoneda B integerBase hZ V)
        G.total.property (isAlgebraicSpace_yoneda B integerBase hZ _)
        (schemeSpace G.base).property hsq G.proper)
  let fV : (𝒯).obj V ⟶ Spec (.of (((𝒯).obj G.base).residueField s)) := (𝒯).map v
  have : IsProper fV := hVp
  have : IsLocallyNoetherian ((𝒯).obj V) := LocallyOfFiniteType.isLocallyNoetherian fV
  have : JacobsonSpace ((𝒯).obj V) := LocallyOfFiniteType.jacobsonSpace fV
  have : IsNoetherian ((𝒯).obj V) :=
    isNoetherian_of_isProper_over_field (((𝒯).obj G.base).residueField s) fV
  have : Subsingleton ((𝒯).obj F₁) := inferInstanceAs (Subsingleton (Spec (.of _)))
  have : Nonempty ((𝒯).obj F₁) := inferInstanceAs (Nonempty (Spec (.of _)))
  have hjmono : Mono j := by
    have : Mono ((𝒯).map r) := (inferInstance :
      Mono (((𝒯).obj G.base).fromSpecResidueField s))
    have : Mono r := (𝒯).mono_of_mono_map this
    have : Mono (yoneda.map r) := Functor.map_mono yoneda r
    exact hsq'.mono_fst_of_mono
  -- one chart divisor on each one-dimensional component of the fibre
  let ι := ↥(genericPointsOne ((𝒯).obj V))
  have : Finite ι := (finite_genericPointsOne ((𝒯).obj V)).to_subtype
  have : Fintype ι := Fintype.ofFinite ι
  have key : ∀ ζ : ι, ∃ (U : BigFppfOver B integerBase hZ) (φ : U ⟶ G.base) (u : (𝒯).obj U)
      (W : BigFppfOver B integerBase hZ) (e : yoneda.obj W ⟶ G.total.obj) (w : W.left.1)
      (hw : B.Contains (Spec (.of (W.left.1.residueField w)))) (x : (𝒯).obj V),
      x ∈ closure {ζ.1} ∧
      Space.pointsMap B integerBase hZ _ e (Space.presheafPoint B integerBase hZ W w hw) =
        Space.pointsMap B integerBase hZ _ j (Space.presheafPoint B integerBase hZ V x
          (B.residueField_spec_contains V.left.property x)) ∧
      Etale ((𝒯).map φ) ∧ (𝒯).map φ u = s ∧ IsIso (((𝒯).map φ).residueFieldMap u) ∧
      ∀ (T : BigFppfOver B integerBase hZ) (ψ : T ⟶ U), Etale ((𝒯).map ψ) →
      ∀ (XU : AlgebraicSpaces B integerBase hZ) (qU : XU.1 ⟶ G.total.obj)
        (fU : XU.1 ⟶ yoneda.obj T),
        IsPullback qU fU fX (yoneda.map (ψ ≫ φ)) →
        ∃ (P : BigFppfOver B integerBase hZ) (π : yoneda.obj P ⟶ XU.1) (p : P ⟶ T) (rr : P ⟶ W)
          (hπ : Space.IsClosedImmersion B integerBase hZ π),
          π ≫ fU = yoneda.map p ∧ π ≫ qU = yoneda.map rr ≫ e ∧
          _root_.AlgebraicGeometry.IsFinite ((𝒯).map p) ∧
          (∀ t, (𝒯).map ψ t = u → ∃ v', (𝒯).map p v' = t ∧ (𝒯).map rr v' = w) ∧
          Space.IsEffectiveCartierDivisor B integerBase hZ XU
            ⟨Subfunctor.range π, Space.isClosedSubspace_range_of_isClosedImmersion B integerBase hZ
              π (isAlgebraicSpace_yoneda B integerBase hZ P) hπ⟩ := by
    intro ζ
    obtain ⟨A, hA, f, x, hxA, hxζ, hf, hx, O, hxO, hiso⟩ :=
      exists_isRegular_isolated_of_mem_genericPointsOne hdim ζ.2
    obtain ⟨W, e, w, hw, gW, he, hmono, hgW, hWaff, hpt⟩ :=
      exists_elementaryEtaleChart_of_mem_fibre G s v j hsq x
    have : Flat ((𝒯).map gW) :=
      Space.prop_toScheme_map_of_holdsOnEveryEtaleChart B integerBase hZ G.flat e he hgW.symm
    have : LocallyOfFinitePresentation ((𝒯).map gW) :=
      Space.prop_toScheme_map_of_holdsOnEveryEtaleChart B integerBase hZ G.finitePresentation.1 e
        he hgW.symm
    have hws := toScheme_map_apply_eq_of_pointsMap_eq G s v j hsq x e w hw gW hgW hpt
    obtain ⟨Z, hwZ, hprin, hfib, z, hz, hqf⟩ :=
      exists_chartDivisor_of_fibre_equation G s v j hsq hA f hf hxA hx O hxO hiso e w hw gW he hgW
        hpt
    obtain ⟨U, φ, u, hφ, -, hu, hres, hpiece⟩ :=
      Space.exists_etale_isEffectiveCartierDivisor_range_of_chart fX G.proper.1 e he w hw hmono gW
        hgW Z hwZ hprin hfib z hz hqf
    refine ⟨U, φ, u, W, e, w, hw, x, hxζ, hpt, hφ, hu.trans hws, hres,
      fun T ψ hψ XU qU fU sqU => ?_⟩
    obtain ⟨P, π, p, rr, hπ, h1, h2, h3, -, -, h6, h7⟩ := hpiece T ψ hψ XU qU fU sqU
    exact ⟨P, π, p, rr, hπ, h1, h2, h3, h6, h7⟩
  choose U φ u W e w hw x hxζ hpt hφ hu hres hpiece using key
  -- lifts of `Spec κ(s)` through the neighbourhoods, and one common neighbourhood
  let ε : F₁ ⟶ Space.residueFieldObject B integerBase hZ G.base s
      (B.residueField_spec_contains G.base.left.property s) :=
    Over.homMk (𝟙 _) (by
      apply ObjectProperty.hom_ext
      exact specULiftZIsTerminal.hom_ext _ _)
  have hε : ε ≫ Space.residueFieldMap B integerBase hZ G.base s
      (B.residueField_spec_contains G.base.left.property s) = r := by
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    exact Category.id_comp _
  have hlift : ∀ ζ : ι, ∃ σ' : F₁ ⟶ U ζ, σ' ≫ φ ζ = r ∧ ∀ y, (𝒯).map σ' y = u ζ := by
    intro ζ
    obtain ⟨σ, hσ, hσu⟩ :=
      Space.exists_lift_residueFieldMap_of_isIso_residueFieldMap (φ ζ) (u ζ) s (hu ζ) (hres ζ)
    refine ⟨ε ≫ σ, by rw [Category.assoc, hσ, hε], fun y => ?_⟩
    rw [Functor.map_comp, Scheme.Hom.comp_apply, hσu]
  choose σ' hσ' hσu using hlift
  obtain ⟨T, φT, σT, hφT, hσT, hψ⟩ := Space.exists_etale_common_lift r U φ hφ σ' hσ' Finset.univ
  choose ψ hψet hψφ hψσ using fun ζ => hψ ζ (Finset.mem_univ ζ)
  -- the base change `X_T`
  let XT : AlgebraicSpaces B integerBase hZ :=
    ⟨pullback fX (yoneda.map φT), isAlgebraicSpace_pullback B integerBase hZ _ _
      G.total.property (isAlgebraicSpace_yoneda B integerBase hZ _)
      (isAlgebraicSpace_yoneda B integerBase hZ _)⟩
  let qT : XT.1 ⟶ G.total.obj := pullback.fst _ _
  let fT : XT.1 ⟶ yoneda.obj T := pullback.snd _ _
  have sqT : IsPullback qT fT fX (yoneda.map φT) := IsPullback.of_hasPullback _ _
  have hP : ∀ ζ : ι, _ := fun ζ => hpiece ζ T (ψ ζ) (hψet ζ) XT qT fT
    (by rw [hψφ ζ]; exact sqT)
  choose P π p rr hπ hπfT hπqT hfin hpts hcart using hP
  -- the divisor `D` and the module `𝒪(D)`
  let Dζ : ι → Space.ClosedSubspaces B integerBase hZ XT.1 := fun ζ =>
    ⟨Subfunctor.range (π ζ), Space.isClosedSubspace_range_of_isClosedImmersion B integerBase hZ
      (π ζ) (isAlgebraicSpace_yoneda B integerBase hZ (P ζ)) (hπ ζ)⟩
  let l := (Finset.univ : Finset ι).toList
  let D := Space.sumClosedSubspacesList XT Dζ (Space.emptyClosedSubspace XT) l
  have hD : Space.IsEffectiveCartierDivisor B integerBase hZ XT D :=
    Space.isEffectiveCartierDivisor_sumClosedSubspacesList XT Dζ _
      (Space.isEffectiveCartierDivisor_emptyClosedSubspace XT) l fun ζ _ => hcart ζ
  let L := Space.associatedInvertibleSheaf B integerBase hZ XT D hD
  have hLinv : Stacks.SheafOfModules.IsInvertible (Space.structurePresheaf B integerBase hZ XT.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (Space.smallEtaleRingedSite B integerBase hZ XT.1 XT.2).O)).property L :=
    Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _
      (Space.associatedInvertibleSheaf_isInvertible B integerBase hZ XT D hD)
  let σs := Space.canonicalSection B integerBase hZ XT D hD
  -- the fibre over `Spec κ(s) ⟶ T`
  let jT : yoneda.obj V ⟶ XT.1 := pullback.lift j (yoneda.map (v ≫ σT)) (by
    rw [hsq'.w, ← hσT]
    simp only [Functor.map_comp, Category.assoc])
  have hjT : jT ≫ qT = j := pullback.lift_fst _ _ _
  have hjT' : jT ≫ fT = yoneda.map (v ≫ σT) := pullback.lift_snd _ _ _
  have hsqT : IsPullback jT (yoneda.map v) fT (yoneda.map σT) := by
    refine IsPullback.of_right ?_ (by rw [hjT', Functor.map_comp]) sqT
    rwa [hjT, ← Functor.map_comp, hσT]
  obtain ⟨y₀⟩ : Nonempty ((𝒯).obj F₁) := inferInstance
  let t := (𝒯).map σT y₀
  have hr : ∀ y, (𝒯).map σT y = t := fun y => by rw [Subsingleton.elim y y₀]
  have ht : (𝒯).map φT t = s := by
    rw [← Scheme.Hom.comp_apply, ← Functor.map_comp, hσT]
    exact Scheme.fromSpecResidueField_apply _ _
  -- ampleness of the reading of `𝒪(D)` on the fibre
  let k : Space.representedAlgebraicSpace B integerBase hZ V ⟶ XT := ObjectProperty.homMk jT
  let M := Space.pointModule B integerBase hZ L V k
  let τ := Space.pointGlobalSection B integerBase hZ L V k σs
  have hMinv : Stacks.Ample.IsInvertibleModule ((𝒯).obj V) M :=
    Space.isInvertibleModule_pointModule B integerBase hZ L hLinv V k
  have hMinv' : SheafOfModules.IsInvertible ((𝒯).obj V).toRingedSpace.presheaf
      (structureSheafRing ((𝒯).obj V).toRingedSpace).property M :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).1 hMinv
  have hzeroD : ∀ y : (𝒯).obj V, y ∉ Stacks.Ample.nonvanishingLocus M τ ↔
      ∃ ζ ∈ l, Space.pointsMap B integerBase hZ _ jT (Space.presheafPoint B integerBase hZ V y
        (B.residueField_spec_contains V.left.property y)) ∈
          Set.range (Space.pointsMap B integerBase hZ _ (π ζ)) := by
    intro y
    rw [Space.notMem_nonvanishingLocus_pointGlobalSection_iff_mem_subspacePointSet B integerBase hZ
      L hLinv σs V k y, Space.zeroScheme_canonicalSection_eq,
      Space.mem_subspacePointSet_sumClosedSubspacesList_iff]
    refine exists_congr fun ζ => and_congr_right fun _ => ?_
    have : Mono (π ζ) := Space.mono_of_isClosedImmersion B integerBase hZ (π ζ) (hπ ζ)
    show _ ∈ Set.range (Space.pointsMap B integerBase hZ (Subfunctor.range (π ζ)).toFunctor
      (Subfunctor.range (π ζ)).ι) ↔ _
    rw [Space.range_pointsMap_ι_range_of_mono B integerBase hZ (π ζ)]
    rfl
  have hampM : Scheme.Modules.IsAmple ((𝒯).obj V) M := by
    refine isAmple_of_mem_nonvanishingLocus_genericPointsOne (((𝒯).obj G.base).residueField s)
      fV hdim M τ ?_ ?_
    · intro ζ hζ
      by_contra hnv
      obtain ⟨η, -, hη⟩ := (hzeroD ζ).1 hnv
      exact notMem_range_pointsMap_of_isFinite fT σT jT v hsqT (π η) (hπ η) (p η) (hπfT η) ζ
        (fun hcl => by
          have h0 := (mem_genericPointsOne_iff.1 hζ).2
          have : topologicalKrullDim ({ζ} : Set ((𝒯).obj V)) = 0 :=
            topologicalKrullDim_eq_zero_of_discreteTopology_nonempty
          rw [hcl.closure_eq, this] at h0
          exact zero_ne_one h0) hη
    · intro ζ hζ
      set η : ι := ⟨ζ, hζ⟩
      obtain ⟨v', hv't, hv'w⟩ := hpts η t (by
        rw [← Scheme.Hom.comp_apply, ← Functor.map_comp, hψσ η, hσu])
      refine ⟨x η, hxζ η, (hzeroD _).2 ⟨η, Finset.mem_toList.2 (Finset.mem_univ _), ?_⟩⟩
      refine ⟨Space.presheafPoint B integerBase hZ (P η) v'
        (B.residueField_spec_contains (P η).left.property v'), ?_⟩
      refine eq_pointsMap_of_isPullback_of_mono fT σT jT v hsqT qT j hjT _ _ ?_ ?_
      · rw [← Function.comp_apply (f := Space.pointsMap B integerBase hZ _ qT),
          ← Space.pointsMap_comp, hπqT, Space.pointsMap_comp, Function.comp_apply,
          Space.pointsMap_presheafPoint B integerBase hZ (P η) (W η) (rr η) v' _
            (B.residueField_spec_contains (W η).left.property _)]
        have hv'w' : (rr η).left.hom v' = w η := hv'w
        simp only [hv'w']
        exact hpt η
      · rw [← Function.comp_apply (f := Space.pointsMap B integerBase hZ _ fT),
          ← Space.pointsMap_comp, hπfT, Space.pointsMap_presheafPoint B integerBase hZ (P η) T
            (p η) v' _ (B.residueField_spec_contains T.left.property _)]
        refine ⟨Space.presheafPoint B integerBase hZ F₁ y₀
          (B.residueField_spec_contains F₁.left.property y₀), ?_⟩
        rw [Space.pointsMap_presheafPoint B integerBase hZ F₁ T σT y₀ _
          (B.residueField_spec_contains T.left.property _)]
        have hv't' : (p η).left.hom v' = (σT).left.hom y₀ := hv't
        simp only [hv't']
  -- the reading is the base change module
  let E : M ≅ Space.baseChangeModule B integerBase hZ L V jT :=
    (Space.restrictToChartSchemeIsoChartRestrictionSheaf B integerBase hZ
      (Space.representedAlgebraicSpace B integerBase hZ V)
      ((Space.modulePullback B integerBase hZ k).obj L)
      (Space.idEtaleChart B integerBase hZ V)).symm
  have hBinv : Stacks.Ample.IsInvertibleModule ((𝒯).obj V)
      (Space.baseChangeModule B integerBase hZ L V jT) :=
    Stacks.SheafOfModules.Invertible.isInvertible_of_iso _ _ E
  have hamp : ∃ hL : Stacks.Ample.IsInvertibleModule ((𝒯).obj V)
      (Space.baseChangeModule B integerBase hZ L V jT), @Stacks.Ample.IsAmple _ _ hL :=
    ⟨hBinv, (Stacks.RelativeVeryAmple.isAmple_congr M _ E).1
      ((Stacks.AmpleBridge.isAmple_iff_isAmple _ M).2 hampM)⟩
  have sqU := Space.isPullback_homMk B integerBase hZ G.total.property
    (isAlgebraicSpace_yoneda B integerBase hZ T) (isAlgebraicSpace_yoneda B integerBase hZ G.base)
    XT.property sqT
  have hchart := hasEtaleSchemeChartAt_of_isAmple_fibre_of_isAffine G φT hφT t _ _ sqU L hLinv
    jT v σT y₀ hr hsqT hamp
  rwa [ht] at hchart

end AlgebraicGeometry.CurveFamily

end
