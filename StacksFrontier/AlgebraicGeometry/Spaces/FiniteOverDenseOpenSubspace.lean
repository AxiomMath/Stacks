module

public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteOverDenseOpenSubspace.ZeroPointNeighbourhoods
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteOverDenseOpenSubspace.QuasiCompactAndSeparatedCases
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteOverDenseOpenSubspace.EtaleChartsAndAtlases

/-!
# Finiteness over a dense open subspace of the target

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` which is locally of finite
type, and write `X⁰ ⊂ |X|` and `Y⁰ ⊂ |Y|` for the sets of points of codimension zero. If `Y` is
decent, `X⁰` and `Y⁰` are finite with `f^{-1}(Y⁰) = X⁰`, and `f` is quasi-compact or separated,
then `f` is finite over a dense open subspace of `Y` (**Stacks 0BBC**). The auxiliary results are
in `ZeroPointNeighbourhoods`, `QuasiCompactAndSeparatedCases` and `EtaleChartsAndAtlases`. Here
points of a scheme are compared with the classes of their residue-field valued points, so that
the points of codimension zero of a representable algebraic space are the generic points of the
scheme, and with this the proof of **Stacks 0BBC** is completed.

## Main results

* `AlgebraicGeometry.Space.exists_isDenseOpenSubspace_isFinite_pullback_snd`: **Stacks 0BBC**.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u v w

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] pointTopology
attribute [local instance] CategoryTheory.MorphismProperty.relative_isStableUnderBaseChange

/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance (priority := high) hasPullback_presheaf_finiteOverDenseOpenSubspace
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

set_option synthInstance.maxHeartbeats 400000 in
/-- Discrete limits of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance (priority := high) hasLimitsOfShape_discrete_presheaf_finiteOverDenseOpenSubspace
    (J : Type) : HasLimitsOfShape (Discrete J) ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  inferInstance

open FiniteOverDense

private theorem residueFieldValuedPoint_schemePoint
    (U : BigFppfOver B S hS)
    (z : (BigFppfOver.toScheme B S hS).obj U) :
    schemePoint B S hS U (residueFieldValuedPoint B S hS U z) = z := by
  let T := (BigFppfOver.toScheme B S hS).obj U
  let kobj : B.Schemes := B.obj (B.residueField_spec_contains U.left.property z)
  show (B.inclusion.map (B.inclusion.preimage (X := kobj) (Y := U.left)
    (T.fromSpecResidueField z))) _ = z
  rw [B.inclusion.map_preimage]
  exact Scheme.fromSpecResidueField_apply z _

/-- The scheme point of a field valued point is carried along a morphism of the site. -/
private theorem schemePoint_fieldValuedPoint_map
    {U V : BigFppfOver B S hS} (f : U ⟶ V)
    (p : FieldValuedPoint B S hS (yoneda.obj U)) :
    schemePoint B S hS V (FieldValuedPoint.map B S hS (yoneda.obj U) (yoneda.map f) p) =
      (BigFppfOver.toScheme B S hS).map f (schemePoint B S hS U p) := by
  change (BigFppfOver.toScheme B S hS).map (p.value ≫ f) _ = _
  rw [Functor.map_comp]
  rfl

private theorem residueFieldValuedPoint_class_schemePoint
    (U : BigFppfOver B S hS)
    (p : FieldValuedPoint B S hS (yoneda.obj U)) :
    (residueFieldValuedPoint B S hS U (schemePoint B S hS U p)).class
      B S hS (yoneda.obj U) = p.class B S hS (yoneda.obj U) := by
  let F := BigFppfOver.toScheme B S hS
  let m : Spec (.of p.carrier) ⟶ F.obj U := F.map p.value
  have : IsLocalHom (Scheme.stalkClosedPointTo m).hom :=
    Scheme.isLocalHom_stalkClosedPointTo' m
  let z := schemePoint B S hS U p
  let q := residueFieldValuedPoint B S hS U z
  let a : Spec (.of p.carrier) ⟶ Spec ((F.obj U).residueField z) :=
    Spec.map (@Scheme.descResidueField p.carrier p.field (F.obj U)
      (m (IsLocalRing.closedPoint p.carrier)) (Scheme.stalkClosedPointTo m)
      (Scheme.isLocalHom_stalkClosedPointTo' m))
  have ha : a ≫ (F.obj U).fromSpecResidueField z = F.map p.value :=
    Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField p.carrier (F.obj U) m
  have hq : F.map q.value = (F.obj U).fromSpecResidueField z := by
    let K := B.obj (B.residueField_spec_contains U.left.property z)
    show B.inclusion.map (B.inclusion.preimage (X := K) (Y := U.left)
      ((F.obj U).fromSpecResidueField z)) = _
    exact B.inclusion.map_preimage _
  let a₀ : (p.siteObject B S hS (yoneda.obj U)).left ⟶
      (q.siteObject B S hS (yoneda.obj U)).left := B.inclusion.preimage a
  have ha₀ : B.inclusion.map a₀ = a :=
    B.inclusion.map_preimage (X := (p.siteObject B S hS (yoneda.obj U)).left)
      (Y := (q.siteObject B S hS (yoneda.obj U)).left) a
  have hleft : a₀ ≫ q.value.left = p.value.left := by
    apply B.inclusion.map_injective
    rw [Functor.map_comp]
    show B.inclusion.map a₀ ≫ F.map q.value = F.map p.value
    rw [hq]
    exact (congrArg (fun g => g ≫ (F.obj U).fromSpecResidueField z) ha₀).trans ha
  let a' : p.siteObject B S hS (yoneda.obj U) ⟶
      q.siteObject B S hS (yoneda.obj U) := Over.homMk a₀ (by
    calc
      a₀ ≫ (q.siteObject B S hS (yoneda.obj U)).hom =
          a₀ ≫ (q.value.left ≫ U.hom) := congrArg (fun j => a₀ ≫ j) q.value.w.symm
      _ = p.value.left ≫ U.hom := by rw [← Category.assoc, hleft]
      _ = _ := p.value.w)
  have hav : a' ≫ q.value = p.value := (Over.forget _).map_injective hleft
  apply FieldValuedPoint.class_eq_class_of_hasCommonExtension
  exact ⟨p, ⟨a', hav⟩, FieldValuedPoint.dominates_refl B S hS _ p⟩

private theorem pointsMap_residueFieldValuedPoint
    {U V : BigFppfOver B S hS} (f : U ⟶ V)
    (z : (BigFppfOver.toScheme B S hS).obj U) :
    pointsMap B S hS (yoneda.obj U) (yoneda.map f)
      ((residueFieldValuedPoint B S hS U z).class B S hS (yoneda.obj U)) =
    (residueFieldValuedPoint B S hS V
      ((BigFppfOver.toScheme B S hS).map f z)).class
        B S hS (yoneda.obj V) := by
  let p := FieldValuedPoint.map B S hS (yoneda.obj U)
    (yoneda.map f) (residueFieldValuedPoint B S hS U z)
  have hp : schemePoint B S hS V p =
      (BigFppfOver.toScheme B S hS).map f z := by
    exact (schemePoint_fieldValuedPoint_map B S hS f _).trans
      (congrArg _ (residueFieldValuedPoint_schemePoint B S hS U z))
  show p.class B S hS (yoneda.obj V) = _
  rw [← hp]
  exact (residueFieldValuedPoint_class_schemePoint B S hS V p).symm

private theorem residueFieldValuedPoint_class_surjective
    (U : BigFppfOver B S hS) :
    Function.Surjective (fun z : (BigFppfOver.toScheme B S hS).obj U =>
      (residueFieldValuedPoint B S hS U z).class B S hS (yoneda.obj U)) := by
  intro x
  obtain ⟨p, rfl⟩ := Quot.exists_rep x
  exact ⟨schemePoint B S hS U p,
    residueFieldValuedPoint_class_schemePoint B S hS U p⟩

private theorem residueFieldValuedPoint_class_injective
    (U : BigFppfOver B S hS) :
    Function.Injective (fun z : (BigFppfOver.toScheme B S hS).obj U =>
      (residueFieldValuedPoint B S hS U z).class B S hS (yoneda.obj U)) := by
  let X := (BigFppfOver.toScheme B S hS).obj U
  let pt := fun z : X =>
    (residueFieldValuedPoint B S hS U z).class B S hS (yoneda.obj U)
  let inv : points B S hS (yoneda.obj U) → X := fun z =>
    Quot.lift
      (fun p : FieldValuedPoint B S hS (yoneda.obj U) =>
        (AlgebraicGeometry.Space.toSchemeFieldValuedPoint B S hS U p).point)
      (by
        intro p q hpq
        obtain ⟨r, hpr, hqr⟩ := hpq
        obtain ⟨f, hf⟩ := hpr
        obtain ⟨g, hg⟩ := hqr
        have hf' : f ≫ p.value = r.value := by
          change (yoneda.obj U).map f.op p.value = r.value at hf
          exact hf
        have hg' : g ≫ q.value = r.value := by
          change (yoneda.obj U).map g.op q.value = r.value at hg
          exact hg
        have hdom (s : FieldValuedPoint B S hS (yoneda.obj U))
            (k : r.siteObject B S hS (yoneda.obj U) ⟶
              s.siteObject B S hS (yoneda.obj U)) (hk : k ≫ s.value = r.value) :
            (AlgebraicGeometry.Space.toSchemeFieldValuedPoint B S hS U r).Dominates
              (AlgebraicGeometry.Space.toSchemeFieldValuedPoint B S hS U s) := by
          refine ⟨B.inclusion.map k.left, ?_⟩
          exact congrArg (fun t => B.inclusion.map t.left) hk
        have hpq' : (AlgebraicGeometry.Space.toSchemeFieldValuedPoint B S hS U p).HasCommonExtension
            (AlgebraicGeometry.Space.toSchemeFieldValuedPoint B S hS U q) :=
          ⟨AlgebraicGeometry.Space.toSchemeFieldValuedPoint B S hS U r, hdom p f hf', hdom q g hg'⟩
        exact (AlgebraicGeometry.FieldValuedPoint.hasCommonExtension_iff_point_eq _ _).mp hpq') z
  have hinv (z : X) : inv (pt z) = z := by
    show (AlgebraicGeometry.Space.toSchemeFieldValuedPoint B S hS U
      (residueFieldValuedPoint B S hS U z)).point = z
    exact residueFieldValuedPoint_schemePoint B S hS U z
  intro x y h
  exact (hinv x).symm.trans ((congrArg inv h).trans (hinv y))

private theorem localRingDimension_zero_of_schemeGeneric
    (U : BigFppfOver B S hS)
    (z : (BigFppfOver.toScheme B S hS).obj U)
    (hz : z ∈ genericPoints ((BigFppfOver.toScheme B S hS).obj U)) :
    localRingDimension B S hS
      ((residueFieldValuedPoint B S hS U z).class B S hS (yoneda.obj U)) = 0 := by
  let p := residueFieldValuedPoint B S hS U z
  apply (localRingDimension_eq_zero_iff_exists_etale_genericPoint
    B S hS (isAlgebraicSpace_yoneda B S hS U)
    (p.class B S hS (yoneda.obj U))).2
  refine ⟨U, 𝟙 _, z, ?_, ?_, hz⟩
  · intro V φ hφ
    simpa only [Category.comp_id] using hφ
  · refine ⟨p, ?_, ?_⟩
    · exact residueFieldValuedPoint_schemePoint B S hS U z
    · simp only [pointsMap_id', id_eq]

private theorem schemeGeneric_of_localRingDimension_zero
    (U : BigFppfOver B S hS)
    (z : (BigFppfOver.toScheme B S hS).obj U)
    (hz : localRingDimension B S hS
      ((residueFieldValuedPoint B S hS U z).class B S hS (yoneda.obj U)) = 0) :
    z ∈ genericPoints ((BigFppfOver.toScheme B S hS).obj U) := by
  let p := residueFieldValuedPoint B S hS U z
  have hall := (localRingDimension_eq_zero_iff_all_etale_genericPoints
    B S hS (isAlgebraicSpace_yoneda B S hS U)
    (p.class B S hS (yoneda.obj U))).mp hz
  apply hall U (𝟙 _) z
  · intro V φ hφ
    simpa only [Category.comp_id] using hφ
  · refine ⟨p, ?_, ?_⟩
    · exact residueFieldValuedPoint_schemePoint B S hS U z
    · simp only [pointsMap_id', id_eq]

/-- **Stacks 0BBC.** Let `f : X ⟶ Y` be a morphism of algebraic spaces over `S` which is
locally of finite type, and write `X⁰` and `Y⁰` for the sets of points of `|X|` and `|Y|`
whose local rings have dimension zero. Assume that `Y` is decent, that `X⁰` and `Y⁰` are
finite with `f^{-1}(Y⁰) = X⁰`, and that `f` is either quasi-compact or separated. Then there
is an open subspace `V ⊂ Y` whose set of points is dense in `|Y|` and over which `f` becomes
finite.

The hypothesis `f^{-1}(Y⁰) = X⁰` makes the fibre of `f` over a point of codimension zero of
`Y` finite, so over a suitable neighbourhood of such a point `f` is finite: if `f` is
quasi-compact this is condition (3) of Stacks 0ACZ, and if `f` is separated it is condition
(3) of Stacks 0AD0 together with the vanishing of the complementary open, which carries no
point of codimension zero and is therefore empty by Stacks 0BAR. Since `Y⁰` is finite, finitely
many such neighbourhoods are glued, and the result is dense because it contains `Y⁰`. -/
@[stacks 0BBC]
theorem exists_isDenseOpenSubspace_isFinite_pullback_snd
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y)
    (f : X ⟶ Y)
    (hlft : IsLocallyOfFiniteType B S hS f)
    (hYdecent : IsDecentSpace B S hS Y)
    (hXzero : Set.Finite {x : points B S hS X |
      localRingDimension B S hS x = 0})
    (hYzero : Set.Finite {y : points B S hS Y |
      localRingDimension B S hS y = 0})
    (hpreimage :
      (pointsMap B S hS X f) ⁻¹'
        {y : points B S hS Y |
          localRingDimension B S hS y = 0} =
        {x : points B S hS X |
          localRingDimension B S hS x = 0})
    (hqc_or_sep : IsQuasiCompact B S hS f ∨
      IsSeparated B S hS f) :
    letI : TopologicalSpace (points B S hS Y) :=
      pointTopology B S hS Y
    ∃ V : Subfunctor Y,
      IsOpenSubspace B S hS V ∧
        Dense (Set.range (pointsMap B S hS V.toFunctor V.ι)) ∧
          IsFinite B S hS (pullback.snd f V.ι) := by
  classical
  have hfib := finite_fiber_over_zero_point B S hS f hXzero hpreimage
  by_cases hqcqs : IsQuasiCompact B S hS f ∧
      IsQuasiSeparated B S hS f
  · exact exists_dense_open_isFinite_of_quasiSeparated_finiteType
      B S hS hX hY f hqcqs.2 ⟨hlft, hqcqs.1⟩ hYdecent hYzero hfib
  rcases hqc_or_sep with hqc | hsep
  · have hnqs : ¬ IsQuasiSeparated B S hS f :=
      fun hqs => hqcqs ⟨hqc, hqs⟩
    apply exists_dense_open_isFinite_of_finite_open_neighborhoods
      B S hS hX hY f hYzero
    intro y hy
    obtain ⟨W, hW, hWqc, hWqs, hWrep, w, hw⟩ :=
      exists_quasiSeparated_open_neighborhood_of_zero
        B S hS hY hYdecent hYzero y hy
    let P := pullback f W.ι
    let p : P ⟶ X := pullback.fst f W.ι
    let q : P ⟶ W.toFunctor := pullback.snd f W.ι
    have hP := isAlgebraicSpace_pullback B S hS f W.ι hX hW.1 hY
    have hPqc : IsQuasiCompactSpace B S hS P :=
      isQuasiCompactSpace_of_iso B S hS (pullbackSymmetry W.ι f)
        (hqc W.toFunctor hW.1 hWqc W.ι)
    obtain ⟨U, a, hUaff, hasurj, haet⟩ :=
      (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover
        B S hS P hP).mp hPqc
    have hp : IsOpenImmersion B S hS p := by
      let X' : AlgebraicGeometry.AlgebraicSpaces B S hS := ⟨X, hX⟩
      let Y' : AlgebraicGeometry.AlgebraicSpaces B S hS := ⟨Y, hY⟩
      let W' : AlgebraicGeometry.AlgebraicSpaces B S hS := ⟨W.toFunctor, hW.1⟩
      have sq := AlgebraicGeometry.AlgebraicSpaces.isPullback_fiberProduct B S hS
        (ObjectProperty.homMk f : X' ⟶ Y')
        (ObjectProperty.homMk W.ι : W' ⟶ Y')
      exact isOpenImmersion_of_isPullback B S hS sq.flip hW.2
    have hWdecent := isDecentSpace_of_isEtale B S hS W.ι
      hW.1 hY (isEtale_of_openImmersion B S hS W.ι hW.2) hYdecent
    have hWzero := finite_codimensionZeroPoints_of_openImmersion B S hS
      hW.1 hY W.ι hW.2 hYzero
    have hpq (z : points B S hS P) :
        pointsMap B S hS X f (pointsMap B S hS P p z) =
          pointsMap B S hS W.toFunctor W.ι (pointsMap B S hS P q z) :=
      pointsMap_apply_comm B S hS pullback.condition z
    have hqzero (z : points B S hS P)
        (hz : localRingDimension B S hS
          (pointsMap B S hS P q z) = 0) :
        localRingDimension B S hS z = 0 := by
      apply (localRingDimension_zero_iff_of_openImmersion
        B S hS hP hX p hp z).2
      refine (Set.ext_iff.mp hpreimage (pointsMap B S hS P p z)).mp ?_
      rw [Set.mem_preimage, hpq]
      exact localRingDimension_zero_map_of_openSubspace
        B S hS hW.1 hY W.ι hW.2 _ hz
    obtain ⟨V, hV, hVdense, hVfinite⟩ :=
      exists_dense_open_isFinite_etale_chart B S hS hP hW.1 q
        (locallyOfFiniteType_pullback_snd B S hS hX hY hW.1 f W.ι hlft)
        hWqs hWdecent hWzero hqzero U hUaff a haet
    let R := (hP.diagonal_representable.of_diag a).pullback a
    let s : R ⟶ U := (hP.diagonal_representable.of_diag a).fst' a
    let t : R ⟶ U := (hP.diagonal_representable.of_diag a).snd a
    have hRpb : IsPullback (yoneda.map s) (yoneda.map t) a a :=
      (hP.diagonal_representable.of_diag a).isPullback' a
    have hUsep : Scheme.IsSeparated ((BigFppfOver.toScheme B S hS).obj U) := by
      let := hUaff
      infer_instance
    have hRsep : Scheme.IsSeparated
        ((BigFppfOver.toScheme B S hS).obj R) :=
      isSeparated_scheme_pullback B S hS P hP U hUsep a haet
    have ha : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf a := by
      simpa using haet U (𝟙 _) (presheaf_etale_id B S hS U)
    obtain ⟨T, hTaff, ⟨e⟩⟩ := hWrep
    let k : U ⟶ T := yoneda.preimage (a ≫ q ≫ e.inv)
    have hk : yoneda.map k = a ≫ q ≫ e.inv := yoneda.map_preimage _
    let l : R ⟶ T := t ≫ k
    have hsk : s ≫ k = l := by
      apply yoneda.map_injective
      simp only [Functor.map_comp, hk]
      dsimp [l]
      simp only [Functor.map_comp, hk]
      simpa only [Category.assoc] using
        congrArg (fun z => z ≫ q ≫ e.inv) hRpb.w
    let Tfun := BigFppfOver.toScheme B S hS
    have heEtale : (MorphismProperty.inverseImage (@Etale.{u}) Tfun).presheaf
        e.hom := by
      simpa using MorphismProperty.RespectsIso.postcomp _ e.hom (𝟙 _)
        (presheaf_etale_id B S hS T)
    have hTW := localRingDimension_zero_iff_of_isEtale B S hS
      (isAlgebraicSpace_yoneda B S hS T) hW.1 e.hom
      (isEtale_of_presheaf B S hS e.hom heEtale)
    have hkLft : LocallyOfFiniteType (Tfun.map k) := by
      apply (locallyOfFiniteType_pullback_snd
        B S hS hX hY hW.1 f W.ι hlft) U T a e.hom k ha heEtale
      simp [hk, Category.assoc]
      rfl
    have htEtale : Etale (Tfun.map t) := ha.2 a (yoneda.map s) t hRpb
    have hlLft : LocallyOfFiniteType (Tfun.map l) := by
      dsimp only [l]
      rw [Functor.map_comp]
      let := htEtale
      let := hkLft
      exact locallyOfFiniteType_comp
        (hf := locallyOfFiniteType_of_etale (Tfun.map t))
        (Tfun.map t) (Tfun.map k)
    have hlSep : AlgebraicGeometry.IsSeparated (Tfun.map l) := by
      let := hRsep
      infer_instance
    have hrelation : yoneda.map s ≫ yoneda.map k =
        yoneda.map t ≫ yoneda.map k := by
      rw [← Functor.map_comp, ← Functor.map_comp, hsk]
    let d : yoneda.obj R ⟶ pullback (yoneda.map k) (yoneda.map k) :=
      pullback.lift (yoneda.map s) (yoneda.map t) hrelation
    have hdmono : Mono d := by
      constructor
      intro Z m n hmn
      apply hRpb.hom_ext
      · have h := congrArg (fun z => z ≫ pullback.fst (yoneda.map k) (yoneda.map k)) hmn
        simpa only [Category.assoc, d, pullback.lift_fst] using h
      · have h := congrArg (fun z => z ≫ pullback.snd (yoneda.map k) (yoneda.map k)) hmn
        simpa only [Category.assoc, d, pullback.lift_snd] using h
    let : (MorphismProperty.inverseImage (@Etale.{u}) Tfun).IsStableUnderBaseChange :=
      inverseImage_stableUnderBaseChange B S hS _
    have htPresheaf : (MorphismProperty.inverseImage (@Etale.{u}) Tfun).presheaf
        (yoneda.map t) :=
      (MorphismProperty.relative_map_iff (F := yoneda)).mpr htEtale
    have htEtaleSpace : IsEtale B S hS (yoneda.map t) :=
      isEtale_of_presheaf B S hS (yoneda.map t) htPresheaf
    have hRgeneric_maps_Wzero
        (r : Tfun.obj R) (hr : r ∈ genericPoints (Tfun.obj R)) :
        localRingDimension B S hS
          (pointsMap B S hS (yoneda.obj R)
            (yoneda.map t ≫ a ≫ q)
            ((residueFieldValuedPoint B S hS R r).class B S hS (yoneda.obj R))) = 0 := by
      let z := (residueFieldValuedPoint B S hS R r).class B S hS (yoneda.obj R)
      have hz : localRingDimension B S hS z = 0 :=
        localRingDimension_zero_of_schemeGeneric B S hS R r hr
      have huz : localRingDimension B S hS
          (pointsMap B S hS (yoneda.obj R) (yoneda.map t) z) = 0 :=
        (localRingDimension_zero_iff_of_isEtale B S hS
          (isAlgebraicSpace_yoneda B S hS R)
          (isAlgebraicSpace_yoneda B S hS U)
          (yoneda.map t) htEtaleSpace z).1 hz
      have hpz : localRingDimension B S hS
          (pointsMap B S hS (yoneda.obj U) a
            (pointsMap B S hS (yoneda.obj R) (yoneda.map t) z)) = 0 :=
        (localRingDimension_zero_iff_of_isEtale B S hS
          (isAlgebraicSpace_yoneda B S hS U) hP a haet _).1 huz
      have hxz : localRingDimension B S hS
          (pointsMap B S hS P p
            (pointsMap B S hS (yoneda.obj U) a
              (pointsMap B S hS (yoneda.obj R) (yoneda.map t) z))) = 0 :=
        localRingDimension_zero_map_of_openSubspace B S hS hP hX p hp _ hpz
      let xz := pointsMap B S hS P p
        (pointsMap B S hS (yoneda.obj U) a
          (pointsMap B S hS (yoneda.obj R) (yoneda.map t) z))
      have hyz : localRingDimension B S hS
          (pointsMap B S hS X f xz) = 0 := (Set.ext_iff.mp hpreimage xz).mpr hxz
      apply (localRingDimension_zero_iff_of_openImmersion B S hS
        hW.1 hY W.ι hW.2 _).2
      change localRingDimension B S hS (pointsMap B S hS W.toFunctor W.ι
        (pointsMap B S hS P q (pointsMap B S hS (yoneda.obj U) a
          (pointsMap B S hS (yoneda.obj R) (yoneda.map t) z)))) = 0
      rw [← hpq]
      exact hyz
    have hmap : yoneda.map l ≫ e.hom = yoneda.map t ≫ a ≫ q := by
      dsimp only [l]
      rw [Functor.map_comp, hk]
      simp only [Category.assoc, e.inv_hom_id, Category.comp_id]
    have hRpoint (r : Tfun.obj R) : ∃ qr : FieldValuedPoint B S hS (yoneda.obj T),
        schemePoint B S hS T qr = Tfun.map l r ∧
          pointsMap B S hS (yoneda.obj T) e.hom (qr.class B S hS (yoneda.obj T)) =
            pointsMap B S hS (yoneda.obj R) (yoneda.map t ≫ a ≫ q)
              ((residueFieldValuedPoint B S hS R r).class B S hS (yoneda.obj R)) :=
      ⟨_, (schemePoint_fieldValuedPoint_map B S hS l _).trans
          (congrArg _ (residueFieldValuedPoint_schemePoint B S hS R r)),
        by rw [← hmap, pointsMap_comp_apply]; rfl⟩
    have hRgeneric_maps_Tgeneric
        (r : Tfun.obj R) (hr : r ∈ genericPoints (Tfun.obj R)) :
        Tfun.map l r ∈ genericPoints (Tfun.obj T) :=
      (localRingDimension_eq_zero_iff_all_etale_genericPoints
        B S hS hW.1 _).mp (hRgeneric_maps_Wzero r hr) T e.hom (Tfun.map l r)
        (isEtale_of_presheaf B S hS e.hom heEtale) (hRpoint r)
    have hRpreimage_generic
        (r : Tfun.obj R) (hr : Tfun.map l r ∈ genericPoints (Tfun.obj T)) :
        r ∈ genericPoints (Tfun.obj R) := by
      let pr := residueFieldValuedPoint B S hS R r
      let xr := pointsMap B S hS (yoneda.obj R)
        (yoneda.map t ≫ a ≫ q) (pr.class B S hS (yoneda.obj R))
      have hxr : localRingDimension B S hS xr = 0 :=
        (localRingDimension_eq_zero_iff_exists_etale_genericPoint
          B S hS hW.1 xr).2
          ⟨T, e.hom, Tfun.map l r,
            isEtale_of_presheaf B S hS e.hom heEtale, hRpoint r, hr⟩
      let zR := pr.class B S hS (yoneda.obj R)
      let zU := pointsMap B S hS (yoneda.obj R) (yoneda.map t) zR
      let zP := pointsMap B S hS (yoneda.obj U) a zU
      have hxr_eq : xr = pointsMap B S hS P q zP := by
        show pointsMap B S hS (yoneda.obj R)
          (yoneda.map t ≫ a ≫ q) zR =
          pointsMap B S hS P q
            (pointsMap B S hS (yoneda.obj U) a
              (pointsMap B S hS (yoneda.obj R) (yoneda.map t) zR))
        rw [pointsMap_comp, Function.comp_apply, pointsMap_comp, Function.comp_apply]
      have hzP : localRingDimension B S hS zP = 0 :=
        hqzero zP (hxr_eq ▸ hxr)
      have hzU : localRingDimension B S hS zU = 0 :=
        (localRingDimension_zero_iff_of_isEtale B S hS
          (isAlgebraicSpace_yoneda B S hS U) hP a haet zU).2 hzP
      have hzR : localRingDimension B S hS zR = 0 :=
        (localRingDimension_zero_iff_of_isEtale B S hS
          (isAlgebraicSpace_yoneda B S hS R)
          (isAlgebraicSpace_yoneda B S hS U)
          (yoneda.map t) htEtaleSpace zR).2 hzU
      exact schemeGeneric_of_localRingDimension_zero B S hS R r hzR
    have heinj : Function.Injective
        (pointsMap B S hS (yoneda.obj T) e.hom) := by
      intro x y hxy
      have h := congrArg (pointsMap B S hS W.toFunctor e.inv) hxy
      have hleft (z : points B S hS (yoneda.obj T)) :
          pointsMap B S hS W.toFunctor e.inv
            (pointsMap B S hS (yoneda.obj T) e.hom z) = z := by
        calc
          _ = pointsMap B S hS (yoneda.obj T) (e.hom ≫ e.inv) z :=
            (congrFun (pointsMap_comp B S hS _ e.hom e.inv) z).symm
          _ = z := by rw [e.hom_inv_id, pointsMap_id']; rfl
      exact (hleft x).symm.trans (h.trans (hleft y))
    let φ : Tfun.obj T → points B S hS W.toFunctor := fun z =>
      pointsMap B S hS (yoneda.obj T) e.hom
        ((residueFieldValuedPoint B S hS T z).class B S hS (yoneda.obj T))
    have hφinj : Function.Injective φ := by
      intro x y hxy
      exact residueFieldValuedPoint_class_injective B S hS T (heinj hxy)
    have hTgenericFinite : (genericPoints (Tfun.obj T)).Finite := by
      apply Set.Finite.of_finite_image (f := φ)
      · apply hWzero.subset
        rintro _ ⟨z, hz, rfl⟩
        exact (hTW _).1 (localRingDimension_zero_of_schemeGeneric B S hS T z hz)
      · exact hφinj.injOn
    have hkpreimage (z : Tfun.obj U)
        (hz : Tfun.map k z ∈ genericPoints (Tfun.obj T)) :
        z ∈ genericPoints (Tfun.obj U) := by
      let zu := (residueFieldValuedPoint B S hS U z).class B S hS (yoneda.obj U)
      have hzT := localRingDimension_zero_of_schemeGeneric B S hS T (Tfun.map k z) hz
      rw [← pointsMap_residueFieldValuedPoint B S hS k z] at hzT
      have hzW := (hTW _).1 hzT
      have heq : yoneda.map k ≫ e.hom = a ≫ q := by simp [hk]
      rw [← Function.comp_apply (f := pointsMap B S hS (yoneda.obj T) e.hom),
        ← pointsMap_comp, heq, pointsMap_comp, Function.comp_apply] at hzW
      have hzP := hqzero _ hzW
      exact schemeGeneric_of_localRingDimension_zero B S hS U z
        ((localRingDimension_zero_iff_of_isEtale B S hS
          (isAlgebraicSpace_yoneda B S hS U) hP a haet zu).2 hzP)
    let : IsAffine (Tfun.obj U) := hUaff
    let : IsAffine (Tfun.obj T) := hTaff
    let : LocallyOfFiniteType (Tfun.map k) := hkLft
    have hkfiber (η : Tfun.obj T) (hη : η ∈ genericPoints (Tfun.obj T)) :
        ((Tfun.map k) ⁻¹' {η}).Finite := by
      have hqf := ((AlgebraicGeometry.quasiFiniteAt_over_genericPoint_tfae
        (Tfun.map k) η hη).out 1 2).mp
          (fun z hz => hkpreimage z ((show Tfun.map k z = η from hz).symm ▸ hη))
      exact (AlgebraicGeometry.finite_setOf_mapsTo_and_quasiFiniteAt
        (Tfun.map k) η).subset (fun z hz => ⟨hz, hqf z hz⟩)
    have hRgeneric_eq : genericPoints (Tfun.obj R) =
        (Tfun.map l) ⁻¹' genericPoints (Tfun.obj T) := by
      ext r
      exact ⟨hRgeneric_maps_Tgeneric r, hRpreimage_generic r⟩
    let C := pullback k k
    let ds : R ⟶ C := pullback.lift s t hsk
    let sqCY := (IsPullback.of_hasPullback k k).map yoneda
    let sqCF := (IsPullback.of_hasPullback k k).map Tfun
    have hd : yoneda.map ds ≫ sqCY.isoPullback.hom = d := by
      apply pullback.hom_ext
      · rw [Category.assoc, sqCY.isoPullback_hom_fst, ← Functor.map_comp]
        simp only [ds, pullback.lift_fst, d]
      · rw [Category.assoc, sqCY.isoPullback_hom_snd, ← Functor.map_comp]
        simp only [ds, pullback.lift_snd, d]
    have hdsmono : Mono ds := by
      apply Functor.mono_of_mono_map (F := yoneda)
      have hm : Mono (yoneda.map ds ≫ sqCY.isoPullback.hom) := hd.symm ▸ hdmono
      exact mono_of_mono (yoneda.map ds) sqCY.isoPullback.hom
    let := hdsmono
    let δ : Tfun.obj R ⟶ pullback (Tfun.map k) (Tfun.map k) :=
      Tfun.map ds ≫ sqCF.isoPullback.hom
    have hδmono : Mono δ := by dsimp [δ]; infer_instance
    have hδl : δ ≫ pullback.snd (Tfun.map k) (Tfun.map k) ≫ Tfun.map k =
        Tfun.map l := by
      dsimp only [δ]
      rw [Category.assoc, ← Category.assoc sqCF.isoPullback.hom,
        sqCF.isoPullback_hom_snd, ← Functor.map_comp, ← Functor.map_comp]
      simp only [ds, pullback.lift_snd_assoc, l]
    have hRfiber (η : Tfun.obj T) (hη : η ∈ genericPoints (Tfun.obj T)) :
        ((Tfun.map l) ⁻¹' {η}).Finite := by
      obtain ⟨O, hηO, hfinO⟩ :=
        (AlgebraicGeometry.finite_preimage_singleton_iff_exists_affine_open_isFinite_restrict
          (Tfun.map k) η hη).mp (hkfiber η hη)
      have hprod := finite_selfPullback_fiber_of_isFinite_restrict
        (Tfun.map k) O.1 η hηO hfinO
      let := hδmono
      have hh := hprod.preimage δ.injective.injOn
      apply hh.subset
      intro r hr
      show (pullback.snd (Tfun.map k) (Tfun.map k) ≫ Tfun.map k) (δ r) = η
      rw [← Scheme.Hom.comp_apply, hδl]
      exact hr
    have hRgenericFinite : (genericPoints (Tfun.obj R)).Finite := by
      rw [hRgeneric_eq]
      exact hTgenericFinite.preimage' hRfiber
    let : LocallyOfFiniteType (Tfun.map l) := hlLft
    obtain ⟨D, hDdense, hDfinite⟩ := AlgebraicGeometry.exists_dense_open_isFinite
      (Tfun.map l) hRgenericFinite hTgenericFinite hRgeneric_eq.symm (Or.inr hlSep)
    have hwzero : localRingDimension B S hS w = 0 :=
      (localRingDimension_zero_iff_of_openImmersion B S hS hW.1 hY W.ι hW.2 w).2
        (hw.symm ▸ hy)
    obtain ⟨v, hv⟩ := zeroPoint_mem_dense_open B S hS hW.1 hWdecent hWzero
      V ⟨hV, hVdense⟩ w hwzero
    obtain ⟨VT, jv, iv, sqV⟩ := hV.2.1 e.hom
    let : IsIso iv := sqV.isIso_fst_of_isIso
    obtain ⟨z, hz⟩ := residueFieldValuedPoint_class_surjective B S hS VT
      (pointsMap B S hS V.toFunctor (inv iv) v)
    dsimp only at hz
    have hivz : pointsMap B S hS (yoneda.obj VT) iv
        ((residueFieldValuedPoint B S hS VT z).class B S hS (yoneda.obj VT)) = v := by
      rw [hz, ← Function.comp_apply (f := pointsMap B S hS (yoneda.obj VT) iv),
        ← pointsMap_comp]
      simp only [IsIso.inv_hom_id, pointsMap_id', id_eq]
    have hzW : pointsMap B S hS (yoneda.obj T) e.hom
        ((residueFieldValuedPoint B S hS T (Tfun.map jv z)).class B S hS (yoneda.obj T)) = w := by
      rw [← pointsMap_residueFieldValuedPoint B S hS jv z,
        ← Function.comp_apply (f := pointsMap B S hS (yoneda.obj T) e.hom),
        ← pointsMap_comp, ← sqV.w, pointsMap_comp, Function.comp_apply, hivz, hv]
    have hzgen : Tfun.map jv z ∈ genericPoints (Tfun.obj T) :=
      schemeGeneric_of_localRingDimension_zero B S hS T _
        ((hTW _).2 (hzW.symm ▸ hwzero))
    have hzD : Tfun.map jv z ∈ D :=
      genericPoint_mem_dense_open_of_finite hTgenericFinite hDdense D.isOpen hzgen
    obtain ⟨A, hAaff, hzA, hAD⟩ := exists_isAffineOpen_mem_and_subset
      (X := Tfun.obj VT) (U := (Tfun.map jv) ⁻¹ᵁ D) (x := z) hzD
    let AT := openSubschemeSiteObject B S hS VT A
    let ja : AT ⟶ VT := openSubschemeSiteι B S hS VT A
    have hja : Tfun.map ja = A.ι := map_openSubschemeSiteι B S hS VT A
    let c : AT ⟶ T := ja ≫ jv
    let j : yoneda.obj AT ⟶ V.toFunctor := yoneda.map ja ≫ iv
    let jw : yoneda.obj AT ⟶ W.toFunctor := j ≫ V.ι
    have hjw : jw = yoneda.map c ≫ e.hom := by
      simp only [jw, j, c, Functor.map_comp, Category.assoc]
      rw [sqV.w]
    let : (MorphismProperty.inverseImage (@AlgebraicGeometry.IsOpenImmersion.{u})
        Tfun).IsStableUnderBaseChange := inverseImage_stableUnderBaseChange B S hS _
    let : (MorphismProperty.inverseImage (@Surjective.{u})
        Tfun).IsStableUnderBaseChange := inverseImage_stableUnderBaseChange B S hS _
    have hjopen : IsOpenImmersion B S hS j := by
      have hj : (MorphismProperty.inverseImage (@AlgebraicGeometry.IsOpenImmersion.{u})
          Tfun).presheaf (yoneda.map ja) := by
        apply (MorphismProperty.relative_map_iff (F := yoneda)).mpr
        show AlgebraicGeometry.IsOpenImmersion (Tfun.map ja)
        rw [hja]
        exact (inferInstance : AlgebraicGeometry.IsOpenImmersion (X := A.toScheme)
          (Y := Tfun.obj VT) A.ι)
      exact MorphismProperty.RespectsIso.postcomp _ iv (yoneda.map ja) hj
    have hjwopen : IsOpenImmersion B S hS jw :=
      isOpenImmersion_comp B S hS j V.ι hjopen hV.2
    let zA : Tfun.obj AT := ⟨z, hzA⟩
    let az := (residueFieldValuedPoint B S hS AT zA).class B S hS (yoneda.obj AT)
    have haz : pointsMap B S hS (yoneda.obj AT) jw az = w := by
      dsimp only [az]
      rw [hjw, pointsMap_comp, Function.comp_apply,
        pointsMap_residueFieldValuedPoint]
      have hcz : Tfun.map c zA = Tfun.map jv z := by
        simp only [c, Functor.map_comp, hja]
        rfl
      rw [hcz]
      exact hzW
    have hcD : Set.range (Tfun.map c).base ⊆ Set.range D.ι.base := by
      rintro _ ⟨x, rfl⟩
      refine ⟨⟨Tfun.map c x, ?_⟩, rfl⟩
      show Tfun.map jv (Tfun.map ja x) ∈ D
      rw [hja]
      exact hAD x.property
    have hRbasefin : IsFinite B S hS
        (pullback.snd (yoneda.map l) (yoneda.map c)) :=
      finite_pullback_yoneda_of_scheme B S hS l c
        (finite_pullback_of_range_subset_open (Tfun.map l) (Tfun.map c) D hDfinite hcD)
    obtain ⟨U₀, k₀, i₀, hU₀, hk₀, sq₀⟩ := hVfinite AT hAaff j
    let i : yoneda.obj U₀ ⟶ yoneda.obj U := i₀ ≫ pullback.fst (a ≫ q) V.ι
    have sq : IsPullback i (yoneda.map k₀) (a ≫ q) jw :=
      sq₀.paste_horiz (IsPullback.of_hasPullback (a ≫ q) V.ι)
    let P₀ := pullback q jw
    let a₀ : yoneda.obj U₀ ⟶ P₀ :=
      pullback.lift (i ≫ a) (yoneda.map k₀) (by simpa only [Category.assoc] using sq.w)
    have ha₀fst : a₀ ≫ pullback.fst q jw = i ≫ a := pullback.lift_fst _ _ _
    have ha₀snd : a₀ ≫ pullback.snd q jw = yoneda.map k₀ := pullback.lift_snd _ _ _
    have sqA : IsPullback i a₀ a (pullback.fst q jw) := by
      have hs : IsPullback (a₀ ≫ pullback.snd q jw) i jw (a ≫ q) := by
        rw [ha₀snd]
        exact sq.flip
      exact (hs.of_right ha₀fst (IsPullback.of_hasPullback q jw).flip).flip
    have hP₀ := isAlgebraicSpace_pullback B S hS q jw hP
      (isAlgebraicSpace_yoneda B S hS AT) hW.1
    have ha₀surj : (MorphismProperty.inverseImage (@Surjective.{u}) Tfun).presheaf a₀ :=
      MorphismProperty.of_isPullback sqA hasurj
    have ha₀et : (MorphismProperty.inverseImage (@Etale.{u}) Tfun).presheaf a₀ :=
      MorphismProperty.of_isPullback sqA ha
    have hrelSq := (kernelPair_baseChange sqA).paste_vert sq
    let er := hRpb.isoPullback
    have her : er.hom ≫ (pullback.snd a a ≫ a ≫ q) = yoneda.map l ≫ e.hom := by
      rw [← Category.assoc, hRpb.isoPullback_hom_snd]
      simp only [l, Functor.map_comp, hk, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    have hrelSq' : IsPullback
        (pullback.map a₀ a₀ a a i i (pullback.fst q jw) sqA.w.symm sqA.w.symm ≫ er.inv)
        (pullback.snd a₀ a₀ ≫ yoneda.map k₀) (yoneda.map l) (yoneda.map c) := by
      apply hrelSq.of_iso (Iso.refl _) er.symm (Iso.refl _) e.symm
      · simp
      · simp
      · dsimp only [Iso.symm_hom]
        rw [← Iso.cancel_iso_hom_left er]
        simp only [Iso.hom_inv_id_assoc]
        rw [← Category.assoc er.hom (pullback.snd a a ≫ a ≫ q) e.inv, her]
        simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
      · simp only [Iso.symm_hom, Iso.refl_hom, Category.id_comp, hjw,
          Category.assoc, Iso.hom_inv_id, Category.comp_id]
    have hrelfinite : IsFinite B S hS
        (pullback.snd a₀ a₀ ≫ a₀ ≫ pullback.snd q jw) := by
      rw [ha₀snd]
      apply isFinite_of_arrowIso B S hS _ _ hrelSq'.isoPullback.symm (Iso.refl _)
        ?_ hRbasefin
      simpa only [Iso.symm_hom, Iso.refl_hom, Category.comp_id] using
        hrelSq'.isoPullback_inv_snd
    have hq₀finite : IsFinite B S hS (pullback.snd q jw) := by
      apply finite_of_finite_atlas_and_relation B S hS hP₀ U₀ AT hU₀ hAaff a₀
        (pullback.snd q jw) ha₀surj ha₀et
        (locallyOfFiniteType_pullback_snd B S hS hP hW.1
          (isAlgebraicSpace_yoneda B S hS AT) q jw
          (locallyOfFiniteType_pullback_snd B S hS hX hY hW.1 f W.ι hlft))
        ?_ hrelfinite
      rw [ha₀snd, Functor.preimage_map]
      exact hk₀
    let jy := jw ≫ W.ι
    let N := Subfunctor.range jy
    let : Mono jw := mono_of_isOpenImmersion B S hS jw hjwopen
    let en : yoneda.obj AT ≅ N.toFunctor := asIso (Subfunctor.toRange jy)
    have hN := isOpenSubspace_range_of_isAlgebraicSpace B S hS
      (isAlgebraicSpace_yoneda B S hS AT) jy
      (isOpenImmersion_comp B S hS jw W.ι hjwopen hW.2)
    have hen : en.hom ≫ N.ι = jy := Subfunctor.toRange_ι jy
    refine ⟨N, hN, ⟨pointsMap B S hS (yoneda.obj AT) en.hom az, ?_⟩, ?_⟩
    · rw [← Function.comp_apply (f := pointsMap B S hS N.toFunctor N.ι),
        ← pointsMap_comp, hen, pointsMap_comp, Function.comp_apply, haz, hw]
    · have hjyfin : IsFinite B S hS (pullback.snd f jy) := by
        apply isFinite_of_arrowIso B S hS _ _
          (pullbackLeftPullbackSndIso f W.ι jw) (Iso.refl _) ?_ hq₀finite
        simp [jy, q]
      let ep := pullback.map f jy f N.ι (𝟙 X) en.hom (𝟙 Y)
        (by simp) (by simpa using hen.symm)
      apply isFinite_of_arrowIso B S hS _ _ (asIso ep) en ?_ hjyfin
      dsimp only [ep, pullback.map]
      simpa only [asIso_hom] using pullback.lift_snd _ _ _
  · exact exists_dense_open_isFinite_of_separated B S hS hX hY f hlft hsep
      hYdecent hXzero hYzero hfib

end AlgebraicGeometry.Space

end
