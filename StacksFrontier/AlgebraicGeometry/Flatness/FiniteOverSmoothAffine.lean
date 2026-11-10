module

public import StacksFrontier.AlgebraicGeometry.Flatness.FiniteOverSmoothFactorization
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.GenericFibre.ShrinkingConsequences

/-!
# The affine form of the finite-over-smooth local structure theorem

Let `f : X ⟶ S` be locally of finite type and let `x` be a point of `X`. Stacks 057K produces
elementary étale neighbourhoods `U` of `(X, x)` and `V` of `(S, f x)`, a scheme `Y` smooth of
relative dimension `n` over `V` with geometrically integral fibres, and a finite morphism
`π : U ⟶ Y` over `V` whose fibre through the distinguished point is a single point and whose
image point has purely transcendental residue field over that of `V`. This module refines the
construction so that all three of `U`, `V` and `Y` are affine. That is Stacks 057L.

## Main results

* `AlgebraicGeometry.exists_finite_over_smooth_affine` is Stacks 057L.

## Implementation notes

The refinement is a triple shrinking. Starting from the output of
`AlgebraicGeometry.exists_finite_over_smooth`, one picks an affine open `A ⊆ V₀` around the
distinguished point, then an affine open `B` of `h₀⁻¹(A)` around the distinguished point of `Y₀`,
and finally an affine open `C ⊆ A` around the distinguished point which is contained in the
image of `B` — the image is open because `B ⟶ A` is smooth, hence flat and locally of finite
presentation, hence open. The new data are `V := C`, `Y := B ×_A C` realised as the open
`hB⁻¹(C) ⊆ B`, and `U := π₀⁻¹(Y) ⊆ U₀`.

Affineness of `Y` and of `U` is not inherited from an affine open basis but from the fact that
the preimage of an affine open under an affine morphism is affine: `hB` is a morphism of affine
schemes and `π₀` is finite.

The purely transcendental clause is the only part that does not restrict formally. Both residue
fields change along open immersions, which induce isomorphisms on residue fields, so the new
extension is isomorphic to the old one; this is
`AlgebraicGeometry.purelyTranscendental_residueField_of_isOpenImmersion`, which transports pure
transcendence by `Stacks.Flatness.purelyTranscendental_of_ringEquiv`.

Geometric integrality of the new smooth morphism is obtained from that of `hP : h₀⁻¹(A) ⟶ A` by
restricting to `C` and then observing that `Y ⟶ C` factors as an open immersion into
`hP⁻¹(C) ⟶ C` followed by that restriction, and is surjective; an open subscheme of an
integral scheme which surjects onto the base is again geometrically integral over it: this is
`AlgebraicGeometry.geometricallyIntegral_resLE_ι_comp`.

## References

* [Stacks Project, Tag 057L](https://stacks.math.columbia.edu/tag/057L)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- An open subscheme of a geometrically integral scheme over a base, which still surjects onto
that base, is itself geometrically integral over it: every base change of the open immersion is
an open immersion into an integral scheme, and nonemptiness is supplied by surjectivity. -/
lemma geometricallyIntegral_comp_of_isOpenImmersion {U X S : Scheme.{u}} (i : U ⟶ X)
    (g : X ⟶ S) [IsOpenImmersion i] [GeometricallyIntegral g] (hsurj : Surjective (i ≫ g)) :
    GeometricallyIntegral (i ≫ g) := by
  rw [GeometricallyIntegral.eq_geometrically]
  intro K _ y Z fst snd hpb
  let j : pullback (i ≫ g) y ⟶ pullback g y :=
    pullback.map _ _ _ _ i (𝟙 _) (𝟙 _) (by simp) (by simp)
  have : IsOpenImmersion j := by infer_instance
  have : MorphismProperty.IsStableUnderBaseChange @Surjective := inferInstance
  have : Surjective (pullback.snd (i ≫ g) y) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback (i ≫ g) y) hsurj
  have : Nonempty ((pullback (i ≫ g) y).carrier) := by
    obtain ⟨z, _⟩ := (pullback.snd (i ≫ g) y).surjective (IsLocalRing.closedPoint _)
    exact ⟨z⟩
  have : IsIntegral (pullback g y) :=
    GeometricallyIntegral.geometrically_isIntegral _ _ _ (IsPullback.of_hasPullback _ _)
  exact (isIntegral_of_isOpenImmersion j).of_isIso hpb.isoPullback.inv

private lemma resLE_apply_eq {X Y : Scheme.{u}} (f : X ⟶ Y) {U : Y.Opens} {V : X.Opens}
    (e : V ≤ f ⁻¹ᵁ U) {x : V.toScheme} {y : U.toScheme} (h : f (V.ι x) = U.ι y) :
    f.resLE U V e x = y := by
  apply U.ι.isOpenEmbedding.injective
  change (f.resLE U V e ≫ U.ι) x = U.ι y
  rw [Scheme.Hom.resLE_comp_ι]
  exact h

private lemma resLE_of_isStableUnderBaseChange {P : MorphismProperty Scheme.{u}}
    [P.IsStableUnderBaseChange] {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) (hf : P f) :
    P (f.resLE U (f ⁻¹ᵁ U) le_rfl) := by
  rw [Scheme.Hom.resLE_eq_morphismRestrict]
  exact P.of_isPullback (isPullback_morphismRestrict f U).flip hf

private lemma surjective_resLE_of_subset_range {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens)
    (hU : (U : Set Y) ⊆ Set.range f) : Surjective (f.resLE U (f ⁻¹ᵁ U) le_rfl) := by
  refine ⟨fun c ↦ ?_⟩
  obtain ⟨b, hb⟩ := hU c.property
  let q : (f ⁻¹ᵁ U).toScheme := ⟨b, by change f b ∈ U; rw [hb]; exact c.property⟩
  exact ⟨q, resLE_apply_eq f le_rfl hb⟩

private lemma finitePresentation_resLE {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens)
    (hf : FinitePresentation f) : FinitePresentation (f.resLE U (f ⁻¹ᵁ U) le_rfl) := by
  have : MorphismProperty.IsStableUnderBaseChange @LocallyOfFinitePresentation :=
    locallyOfFinitePresentation_isStableUnderBaseChange
  have : MorphismProperty.IsStableUnderBaseChange @QuasiCompact :=
    quasiCompact_isStableUnderBaseChange
  have : MorphismProperty.IsStableUnderBaseChange @QuasiSeparated :=
    quasiSeparated_isStableUnderBaseChange
  exact ⟨resLE_of_isStableUnderBaseChange (P := @LocallyOfFinitePresentation) f U hf.1,
    resLE_of_isStableUnderBaseChange (P := @QuasiCompact) f U hf.2.1,
    resLE_of_isStableUnderBaseChange (P := @QuasiSeparated) f U hf.2.2⟩

/-- If `g : X ⟶ S` is geometrically integral, `B` is an open of `X` and `C` an open of `S`, and the
restriction of `B ⟶ S` over `C` is surjective, then that restriction is geometrically integral. -/
theorem geometricallyIntegral_resLE_ι_comp {X S : Scheme.{u}} (g : X ⟶ S) [GeometricallyIntegral g]
    (B : X.Opens) (C : S.Opens)
    (hsurj : Surjective ((B.ι ≫ g).resLE C ((B.ι ≫ g) ⁻¹ᵁ C) le_rfl)) :
    GeometricallyIntegral ((B.ι ≫ g).resLE C ((B.ι ≫ g) ⁻¹ᵁ C) le_rfl) := by
  let T : B.toScheme.Opens := (B.ι ≫ g) ⁻¹ᵁ C
  let Sopen : X.Opens := g ⁻¹ᵁ C
  let gC : Sopen.toScheme ⟶ C.toScheme := g.resLE C Sopen le_rfl
  let jP : T.toScheme ⟶ X := T.ι ≫ B.ι
  let G : X.Opens := jP.opensRange
  let eP : T.toScheme ≅ G.toScheme := IsOpenImmersion.isoOfRangeEq jP G.ι (by simp [G])
  have hGS : G ≤ Sopen := by
    rintro _ ⟨t, rfl⟩
    exact t.property
  let iT : T.toScheme ⟶ Sopen.toScheme := eP.hom ≫ X.homOfLE hGS
  have hePfac : eP.hom ≫ G.ι = jP := IsOpenImmersion.isoOfRangeEq_hom_fac jP G.ι (by simp [G])
  have hGι : X.homOfLE hGS ≫ Sopen.ι = G.ι := Scheme.homOfLE_ι X hGS
  have hTfac : iT ≫ gC = (B.ι ≫ g).resLE C T le_rfl := by
    apply (cancel_mono C.ι).1
    calc
      iT ≫ gC ≫ C.ι = eP.hom ≫ X.homOfLE hGS ≫ Sopen.ι ≫ g := by
        simp [iT, gC, Category.assoc]
      _ = eP.hom ≫ G.ι ≫ g := by
        simpa only [Category.assoc] using congrArg (fun q => eP.hom ≫ q ≫ g) hGι
      _ = jP ≫ g := by
        simpa only [Category.assoc] using congrArg (fun q => q ≫ g) hePfac
      _ = T.ι ≫ B.ι ≫ g := by simp [jP, Category.assoc]
      _ = (B.ι ≫ g).resLE C T le_rfl ≫ C.ι :=
        (Scheme.Hom.resLE_comp_ι (B.ι ≫ g) (by simp [T])).symm
  have : GeometricallyIntegral gC :=
    resLE_of_isStableUnderBaseChange (P := @GeometricallyIntegral) g C ‹_›
  simpa only [hTfac] using
    geometricallyIntegral_comp_of_isOpenImmersion iT gC (by rw [hTfac]; exact hsurj)

/-- Restricting a morphism along open immersions of its source and target preserves pure
transcendence of the residue field extension at a point. -/
theorem purelyTranscendental_residueField_of_isOpenImmersion {Y₀ V₀ T C : Scheme.{u}}
    {h₀ : Y₀ ⟶ V₀} {h : T ⟶ C} {j : T ⟶ Y₀} {ι : C ⟶ V₀} [IsOpenImmersion j]
    [IsOpenImmersion ι] (hfac : h ≫ ι = j ≫ h₀) {y : Y₀} {v : V₀} (hy : h₀ y = v) {t : T}
    {c : C} (hc : h t = c) (hj : j t = y)
    (H : letI : Algebra (V₀.residueField v) (Y₀.residueField y) :=
        ((V₀.residueFieldCongr hy).inv ≫ h₀.residueFieldMap y).hom.toAlgebra
      PurelyTranscendental (V₀.residueField v) (Y₀.residueField y)) :
    letI : Algebra (C.residueField c) (T.residueField t) :=
      ((C.residueFieldCongr hc).inv ≫ h.residueFieldMap t).hom.toAlgebra
    PurelyTranscendental (C.residueField c) (T.residueField t) := by
  subst hc hj hy
  have hpt : ι (h t) = h₀ (j t) := congrArg (fun q => q t) hfac
  have hsq : ι.residueFieldMap (h t) ≫ h.residueFieldMap t =
      (V₀.residueFieldCongr hpt).hom ≫ h₀.residueFieldMap (j t) ≫ j.residueFieldMap t := by
    have := Scheme.Hom.residueFieldMap_congr hfac t
    simp only [Scheme.residueFieldMap_comp] at this
    exact this
  let e : C.residueField (h t) ≅ V₀.residueField (h₀ (j t)) :=
    (asIso (ι.residueFieldMap (h t))).symm ≪≫ V₀.residueFieldCongr hpt
  let E : Y₀.residueField (j t) ≅ T.residueField t := asIso (j.residueFieldMap t)
  let : Algebra (V₀.residueField (h₀ (j t))) (Y₀.residueField (j t)) :=
    ((V₀.residueFieldCongr rfl).inv ≫ h₀.residueFieldMap (j t)).hom.toAlgebra
  let : Algebra (C.residueField (h t)) (T.residueField t) :=
    ((C.residueFieldCongr rfl).inv ≫ h.residueFieldMap t).hom.toAlgebra
  have key : (C.residueFieldCongr rfl).inv ≫ h.residueFieldMap t =
      e.hom ≫ ((V₀.residueFieldCongr rfl).inv ≫ h₀.residueFieldMap (j t)) ≫ E.hom := by
    simp only [e, E, Scheme.residueFieldCongr_refl, Iso.refl_inv, Category.id_comp,
      Iso.trans_hom, Iso.symm_hom, asIso_inv, asIso_hom, Category.assoc, ← hsq,
      IsIso.inv_hom_id_assoc]
  exact Stacks.Flatness.purelyTranscendental_of_ringEquiv e.commRingCatIsoToRingEquiv
    E.commRingCatIsoToRingEquiv (fun a => congrArg (fun φ => φ.hom a) key) H

/-- **Stacks Project, Tag 057L.** The finite-over-smooth local structure of a locally
finite-type morphism can be obtained with all three new schemes affine. -/
@[stacks 057L]
theorem exists_finite_over_smooth_affine {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (x : X) :
    ∃ (n : ℕ) (_ : topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) = n)
      (U : EtaleNeighborhood X x) (V : EtaleNeighborhood S (f x))
      (Y : Scheme.{u}) (h : Y ⟶ V.scheme) (π : U.scheme ⟶ Y),
      U.IsElementary ∧ V.IsElementary ∧ (U.toBase ≫ f = π ≫ h ≫ V.toBase) ∧
        SmoothOfRelativeDimension n h ∧
        (∀ s' : V.scheme, GeometricallyIntegral (h.fiberToSpecResidueField s')) ∧
        IsFinite π ∧ (∀ z : U.scheme, π z = π U.point ↔ z = U.point) ∧
        (∃ heq : h (π U.point) = V.point,
          letI : Algebra (V.scheme.residueField V.point) (Y.residueField (π U.point)) :=
            ((V.scheme.residueFieldCongr heq).inv ≫ h.residueFieldMap (π U.point)).hom.toAlgebra
          PurelyTranscendental (V.scheme.residueField V.point)
            (Y.residueField (π U.point))) ∧
        (LocallyOfFinitePresentation f → FinitePresentation π) ∧
        IsAffine V.scheme ∧ IsAffine Y ∧ IsAffine U.scheme := by
  obtain ⟨n, hn, U₀, V₀, Y₀, h₀, π₀, hU₀, hV₀, hcomm₀, hsmooth₀,
      hfib₀, hfinite₀, huniq₀, hpt₀, hfp₀⟩ := exists_finite_over_smooth f x
  obtain ⟨heq₀, htrans₀⟩ := hpt₀
  let y₀ : Y₀ := π₀ U₀.point
  have hhy₀ : h₀ y₀ = V₀.point := heq₀
  obtain ⟨_, ⟨O, hO, rfl⟩, hsO, _⟩ :=
    V₀.scheme.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ V₀.point) isOpen_univ
  let A : V₀.scheme.affineOpens := ⟨O, hO⟩
  let a₀ : A.1.toScheme := ⟨V₀.point, hsO⟩
  let P : Y₀.Opens := h₀ ⁻¹ᵁ A.1
  have hyP : y₀ ∈ P := by
    change h₀ y₀ ∈ A.1
    simpa [hhy₀, a₀] using hsO
  let p₀ : P.toScheme := ⟨y₀, hyP⟩
  let hP : P.toScheme ⟶ A.1.toScheme := h₀.resLE A.1 P le_rfl
  have hPpoint : hP p₀ = a₀ := resLE_apply_eq h₀ le_rfl hhy₀
  obtain ⟨_, ⟨B₀, hB₀, rfl⟩, hpB, _⟩ :=
    P.toScheme.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ p₀) isOpen_univ
  let B : P.toScheme.affineOpens := ⟨B₀, hB₀⟩
  let b₀ : B.1.toScheme := ⟨p₀, hpB⟩
  let hB : B.1.toScheme ⟶ A.1.toScheme := B.1.ι ≫ hP
  have hBpoint : hB b₀ = a₀ := hPpoint
  have : MorphismProperty.IsStableUnderBaseChange (@SmoothOfRelativeDimension n) :=
    smoothOfRelativeDimension_isStableUnderBaseChange n
  have hsmP : SmoothOfRelativeDimension n hP :=
    resLE_of_isStableUnderBaseChange (P := @SmoothOfRelativeDimension n) h₀ A.1 hsmooth₀
  have hsmB : SmoothOfRelativeDimension n hB := by
    have : SmoothOfRelativeDimension 0 B.1.ι := inferInstance
    simpa [hB] using (inferInstance : SmoothOfRelativeDimension (0 + n) (B.1.ι ≫ hP))
  have hWopen : IsOpen (hB '' (Set.univ : Set B.1.toScheme)) := by
    have : Smooth hB := SmoothOfRelativeDimension.smooth n hB
    exact hB.isOpenMap _ isOpen_univ
  let W : A.1.toScheme.Opens := ⟨hB '' (Set.univ : Set B.1.toScheme), hWopen⟩
  have haW : a₀ ∈ W := ⟨b₀, Set.mem_univ _, hBpoint⟩
  obtain ⟨_, ⟨C₀, hC₀, rfl⟩, haC, hCW⟩ :=
    A.1.toScheme.isBasis_affineOpens.exists_subset_of_mem_open haW hWopen
  let C : A.1.toScheme.affineOpens := ⟨C₀, hC₀⟩
  let c₀ : C.1.toScheme := ⟨a₀, haC⟩
  let V : EtaleNeighborhood S (f x) :=
    { scheme := C.1.toScheme
      point := c₀
      toBase := C.1.ι ≫ A.1.ι ≫ V₀.toBase
      map_point := V₀.map_point }
  have hV : V.IsElementary := by
    rw [EtaleNeighborhood.isElementary_iff] at hV₀ ⊢
    change IsIso ((C.1.ι ≫ A.1.ι ≫ V₀.toBase).residueFieldMap c₀)
    rw [Scheme.residueFieldMap_comp, Scheme.residueFieldMap_comp]
    exact IsIso.comp_isIso' (IsIso.comp_isIso' hV₀ inferInstance) inferInstance
  let T : B.1.toScheme.Opens := hB ⁻¹ᵁ C.1
  have hTaff : IsAffine T.toScheme := by
    have : IsAffine B.1.toScheme := B.2
    have : IsAffine A.1.toScheme := A.2
    have : IsAffineHom hB := isAffineHom_of_isAffine hB
    exact IsAffineHom.isAffine_preimage C.1 C.2
  let q₀ : T.toScheme := ⟨b₀, by change hB b₀ ∈ C.1; simpa [hBpoint] using haC⟩
  let hT : T.toScheme ⟶ C.1.toScheme := hB.resLE C.1 T le_rfl
  have hTpoint : hT q₀ = c₀ := resLE_apply_eq hB le_rfl hBpoint
  let jY : T.toScheme ⟶ Y₀ := T.ι ≫ B.1.ι ≫ P.ι
  let F : Y₀.Opens := jY.opensRange
  let eY : T.toScheme ≅ F.toScheme := IsOpenImmersion.isoOfRangeEq jY F.ι (by simp [F])
  have heYfac : eY.inv ≫ jY = F.ι := IsOpenImmersion.isoOfRangeEq_inv_fac jY F.ι (by simp [F])
  have hYfac : eY.hom ≫ F.ι = jY := IsOpenImmersion.isoOfRangeEq_hom_fac jY F.ι (by simp [F])
  let Y : Scheme.{u} := T.toScheme
  have hYaff : IsAffine Y := hTaff
  let h : Y ⟶ C.1.toScheme := hT
  let UO : U₀.scheme.Opens := π₀ ⁻¹ᵁ F
  have hyF : y₀ ∈ F := ⟨q₀, rfl⟩
  have huO : U₀.point ∈ UO := hyF
  let u₀ : UO.toScheme := ⟨U₀.point, huO⟩
  let U : EtaleNeighborhood X x :=
    { scheme := UO.toScheme
      point := u₀
      toBase := UO.ι ≫ U₀.toBase
      map_point := U₀.map_point }
  let πF : U.scheme ⟶ F.toScheme := π₀.resLE F UO le_rfl
  have hπfac : πF ≫ F.ι = UO.ι ≫ π₀ := Scheme.Hom.resLE_comp_ι π₀ (by simp [UO])
  let π : U.scheme ⟶ Y := πF ≫ eY.inv
  have hUaff : IsAffine U.scheme := by
    have : IsAffineHom π₀ := hfinite₀.toIsAffineHom
    exact IsAffineHom.isAffine_preimage F (isAffineOpen_opensRange jY)
  have hU : U.IsElementary := by
    change IsIso ((X.residueFieldCongr U.map_point).inv ≫ U.toBase.residueFieldMap U.point)
    rw [Scheme.residueFieldMap_comp]
    change IsIso (((X.residueFieldCongr U₀.map_point).inv ≫
      U₀.toBase.residueFieldMap U₀.point) ≫ UO.ι.residueFieldMap u₀)
    exact IsIso.comp_isIso' hU₀ (inferInstance : IsIso (UO.ι.residueFieldMap u₀))
  have hfinite : IsFinite π := by
    have : IsFinite πF := resLE_of_isStableUnderBaseChange (P := @IsFinite) π₀ F hfinite₀
    change IsFinite (πF ≫ eY.inv)
    infer_instance
  have hhfac : hT ≫ C.1.ι ≫ A.1.ι = jY ≫ h₀ := by
    have ht₁ : hT ≫ C.1.ι = T.ι ≫ hB := Scheme.Hom.resLE_comp_ι hB (by simp [T])
    have hp₁ : hP ≫ A.1.ι = P.ι ≫ h₀ := Scheme.Hom.resLE_comp_ι h₀ (by simp [P])
    rw [← Category.assoc, ht₁]
    simp only [hB, jY, Category.assoc, hp₁]
  have hcomm : U.toBase ≫ f = π ≫ h ≫ V.toBase := by
    change UO.ι ≫ U₀.toBase ≫ f =
      πF ≫ eY.inv ≫ hT ≫ C.1.ι ≫ A.1.ι ≫ V₀.toBase
    rw [hcomm₀, reassoc_of% hhfac, reassoc_of% heYfac, reassoc_of% hπfac]
  have hdim : SmoothOfRelativeDimension n h :=
    resLE_of_isStableUnderBaseChange (P := @SmoothOfRelativeDimension n) hB C.1 hsmB
  have hGI₀ : GeometricallyIntegral h₀ :=
    (GeometricallyIntegral.iff_geometricallyIntegral_fiber h₀).2 hfib₀
  have hGIP : GeometricallyIntegral hP :=
    resLE_of_isStableUnderBaseChange (P := @GeometricallyIntegral) h₀ A.1 hGI₀
  have hsurjT : Surjective hT := surjective_resLE_of_subset_range hB C.1 fun c hc ↦ by
    obtain ⟨b, _, hb⟩ := hCW hc
    exact ⟨b, hb⟩
  have hGIh : GeometricallyIntegral hT := geometricallyIntegral_resLE_ι_comp hP B.1 C.1 hsurjT
  have hfib : ∀ s' : V.scheme, GeometricallyIntegral (h.fiberToSpecResidueField s') :=
    (GeometricallyIntegral.iff_geometricallyIntegral_fiber h).1 hGIh
  have huniq : ∀ z : U.scheme, π z = π U.point ↔ z = U.point := by
    refine fun z ↦ ⟨fun hz ↦ Subtype.ext ((huniq₀ z.1).mp ?_), fun hz ↦ by rw [hz]⟩
    have hz' : πF z = πF U.point := by
      have hz'' := congrArg eY.hom hz
      dsimp [π] at hz''
      simpa using hz''
    have hbase := congrArg F.ι hz'
    change (πF ≫ F.ι) z = (πF ≫ F.ι) U.point at hbase
    rwa [hπfac] at hbase
  have hπpoint : π U.point = q₀ := by
    apply eY.hom.injective
    change (eY.inv ≫ eY.hom) (πF U.point) = eY.hom q₀
    rw [CategoryTheory.Iso.inv_hom_id]
    apply F.ι.isOpenEmbedding.injective
    change (πF ≫ F.ι) U.point = (eY.hom ≫ F.ι) q₀
    rw [hπfac, hYfac]
    rfl
  have heq : h (π U.point) = V.point := by
    rw [hπpoint]
    exact hTpoint
  have htrans : ∃ heq : h (π U.point) = V.point,
      let : Algebra (V.scheme.residueField V.point) (Y.residueField (π U.point)) :=
        ((V.scheme.residueFieldCongr heq).inv ≫ h.residueFieldMap (π U.point)).hom.toAlgebra
      PurelyTranscendental (V.scheme.residueField V.point) (Y.residueField (π U.point)) :=
    ⟨heq, purelyTranscendental_residueField_of_isOpenImmersion hhfac heq₀ heq
      (by rw [hπpoint]; rfl) htrans₀⟩
  have hfp : LocallyOfFinitePresentation f → FinitePresentation π := fun hf ↦ by
    obtain ⟨_, _, _⟩ : FinitePresentation πF := finitePresentation_resLE π₀ F (hfp₀ hf)
    exact ⟨inferInstance, inferInstance, inferInstance⟩
  exact ⟨n, hn, U, V, Y, h, π, hU, hV, hcomm, hdim, hfib, hfinite, huniq,
    htrans, hfp, C.2, hYaff, hUaff⟩

end AlgebraicGeometry

end
