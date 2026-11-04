module

public import StacksFrontier.AlgebraicGeometry.Descent.FpqcDescentProperties.NoetherianNormalDecomposition
public import StacksFrontier.AlgebraicGeometry.FibreDimensionBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FiniteOverSmooth.Main
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FiniteOverSmooth.FibreDimension
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FiniteOverSmooth.ConditionalStatements
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FiniteOverSmooth.NormalFibre
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FiniteOverSmooth.PurelyTranscendental
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FiniteOverSmooth.ResidueFieldMap
public import StacksFrontier.AlgebraicGeometry.Morphisms.Smooth.Normal
public import StacksFrontier.AlgebraicGeometry.Properties.Regular
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.ConnectedPoint
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.Regular
public import StacksFrontier.Topology.Noetherian.LocallyConnected

/-!
# Finite-type morphisms near a point, with geometrically integral fibres

A locally finite-type morphism `f : X ⟶ S` becomes, after elementary étale neighbourhoods of a
point `x` of the source and of its image, a finite morphism onto a family which is smooth of
relative dimension the local dimension of the fibre `X_{f x}` at `x`, and all of whose fibres are
geometrically integral. The fibre of the finite morphism over the image of the distinguished
point is that point alone, and the residue field there is purely transcendental over the residue
field of the base point.

This is Stacks Tag 057K. It is Stacks 052E, which gives the same conclusion without the
geometrically-integral clause, followed by Stacks 057J twice: 052E's smooth family has a fibre
component through the relevant point which is geometrically irreducible, because it is connected
and the residue field extension 052E produces is purely transcendental, and 057J spreads that
component out to a neighbourhood with geometrically integral fibres.

## Main results

* `AlgebraicGeometry.exists_finite_over_smooth_geometricallyIntegral_of_statement057J` is Tag
  057K, with the statement of Tag 057J as an explicit hypothesis.

## Implementation notes

Tag 057J is not yet available, so it is carried as the hypothesis
`AlgebraicGeometry.Statement057J` and the theorem is left untagged. Everything else in the proof
is discharged.

Geometric irreducibility of the chosen fibre component is obtained from connectedness together
with `AlgebraicGeometry.IsAlgClosedIn.of_purelyTranscendental` and Tag 04KV, and from normality
of the base changes of the component, which here comes from smoothness directly (Tags 056S and
0569) rather than from Tags 06DG and 038O: inside this proof the morphism in question is smooth
over the residue field, so its base changes are regular and hence normal.

Transporting the purely transcendental residue field extension produced by 052E across the
identifications made by the étale neighbourhoods is
`AlgebraicGeometry.PurelyTranscendental.of_ringEquiv_square`; the two squares of residue fields
that make it applicable are instances of `AlgebraicGeometry.residueFieldMap_square`.

## References

* [Stacks Project, Tag 057K](https://stacks.math.columbia.edu/tag/057K)
* [Stacks Project, Tag 052E](https://stacks.math.columbia.edu/tag/052E)
* [Stacks Project, Tag 057J](https://stacks.math.columbia.edu/tag/057J)
* [Stacks Project, Tag 02FY](https://stacks.math.columbia.edu/tag/02FY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IntermediateField TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- A connected, quasi-compact scheme smooth over a field, whose structure morphism is
geometrically connected, is geometrically irreducible: each base change is normal because it is
smooth over a field hence regular, and a connected Noetherian normal scheme is irreducible. -/
theorem geometricallyIrreducible_of_geometricallyConnected_of_smooth {X Y : Scheme.{u}}
    (f : X ⟶ Y) [Smooth f] [LocallyOfFiniteType f] [QuasiCompact f]
    (hconn : GeometricallyConnected f) : GeometricallyIrreducible f := by
  rw [GeometricallyIrreducible.eq_geometrically]
  intro K hK q Z fst snd hpull
  have : IsLocallyNoetherian (pullback f q : Scheme.{u}) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd f q)
  have : CompactSpace (pullback f q : Scheme.{u}) :=
    (quasiCompact_iff_compactSpace (pullback.snd f q)).mp inferInstance
  have : IsNoetherian (pullback f q : Scheme.{u}) := ⟨⟩
  have hnormalQ : IsNormal (pullback f q : Scheme.{u}) :=
    isNormal_of_isRegular _ (isRegular_of_smooth_over_field (pullback.snd f q))
  have : ConnectedSpace (pullback f q : Scheme.{u}) :=
    hconn.geometrically_connectedSpace q (pullback.fst f q) (pullback.snd f q)
      (IsPullback.of_hasPullback f q)
  have : IrreducibleSpace (pullback f q : Scheme.{u}) :=
    irreducibleSpace_of_isNormal_of_connectedSpace _ hnormalQ
  exact (Scheme.homeoOfIso hpull.isoPullback).irreducibleSpace_iff.mpr inferInstance

/-- **Stacks Project, Tag 057K**, conditional on Tag 057J. Étale-locally near a point, a locally
finite-type morphism is finite over a smooth family of the fibre's local dimension, with
geometrically integral fibres. The finite map can be chosen finitely presented when the original
morphism is locally finitely presented. -/
theorem exists_finite_over_smooth_geometricallyIntegral_of_statement057J
    (h057J : Statement057J.{u}) {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] (x : X) :
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
        (LocallyOfFinitePresentation f → FinitePresentation π) := by
  classical
  obtain ⟨n, hn⟩ := exists_topologicalKrullDimAt_fiber_eq_nat f x
  obtain ⟨-, ⟨O, hO, rfl⟩, hsO, -⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
  set A : S.affineOpens := ⟨O, hO⟩
  set XO : X.Opens := f ⁻¹ᵁ A.1
  set xO : XO.toScheme := ⟨x, show f x ∈ A.1 from hsO⟩
  set fO : XO.toScheme ⟶ A.1.toScheme := f ∣_ A.1 with hfO
  set a : A.1.toScheme := fO xO
  have hpullO : IsPullback XO.ι fO f A.1.ι := (isPullback_morphismRestrict f A.1).flip
  have hdimO : topologicalKrullDimAt (fO.fiber (fO xO)) (fO.asFiber xO) = n :=
    (topologicalKrullDimAt_fiber_eq_of_isPullback hpullO xO).trans hn
  obtain ⟨Y₀, h₀, U₀, π₀, hsmooth₀, hU₀, hfinite₀, huniq₀, hcomm₀, ⟨hy₀, hpt₀⟩, hfp₀⟩ :=
    exists_finite_over_smooth_of_locallyOfFiniteType fO xO n hdimO
  set y₀ : Y₀ := π₀ U₀.point
  obtain ⟨-, ⟨O', hO', rfl⟩, hyB, -⟩ :=
    Y₀.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y₀) isOpen_univ
  set B : Y₀.affineOpens := ⟨O', hO'⟩
  set b : B.1.toScheme := ⟨y₀, hyB⟩
  set h : B.1.toScheme ⟶ A.1.toScheme := B.1.ι ≫ h₀ with hhdef
  have hb : h b = a := hy₀
  set UO : U₀.scheme.Opens := π₀ ⁻¹ᵁ B.1
  set u : UO.toScheme := ⟨U₀.point, show π₀ U₀.point ∈ B.1 from hyB⟩
  set U₁ : EtaleNeighborhood XO.toScheme xO :=
    { scheme := UO.toScheme
      point := u
      toBase := UO.ι ≫ U₀.toBase
      map_point := U₀.map_point }
  set π₁ : U₁.scheme ⟶ B.1.toScheme := π₀.resLE B.1 UO le_rfl with hπ₁def
  have hU₁ : U₁.IsElementary := by
    rw [EtaleNeighborhood.isElementary_iff]
    exact isIso_residueFieldMap_comp UO.ι U₀.toBase u inferInstance (U₀.isElementary_iff.mp hU₀)
  have hsm : SmoothOfRelativeDimension n h := by
    have : SmoothOfRelativeDimension n h₀ := hsmooth₀
    simpa [hhdef] using
      (inferInstance : SmoothOfRelativeDimension (0 + n) (B.1.ι ≫ h₀))
  have : Smooth h := SmoothOfRelativeDimension.smooth n h
  have : IsAffine B.1.toScheme := B.2
  have : IsAffine A.1.toScheme := A.2
  have : IsAffineHom h := isAffineHom_of_isAffine h
  have hfinite₁ : IsFinite π₁ := by
    have : IsFinite π₀ := hfinite₀
    rw [hπ₁def, Scheme.Hom.resLE_eq_morphismRestrict]
    infer_instance
  have hfp : FinitePresentation h := ⟨inferInstance, inferInstance, inferInstance⟩
  have hnormal : Scheme.Hom.IsNormal h := h.isNormal_of_smooth
  -- The fibre of `h` over `a`, and the connected component of the chosen point in it.
  set qa : Spec (A.1.toScheme.residueField a) := default
  set p : h.fiber a := hb ▸ h.asFiber b
  have hpf : h.fiberι a p = b := Scheme.Hom.fiberι_cast_asFiber h b hb
  have hfibSmooth : Smooth (h.fiberToSpecResidueField a) :=
    inferInstanceAs (Smooth (pullback.snd h (A.1.toScheme.fromSpecResidueField a)))
  have hfibLFT : LocallyOfFiniteType (h.fiberToSpecResidueField a) :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd h (A.1.toScheme.fromSpecResidueField a)))
  have hfibQC : QuasiCompact (h.fiberToSpecResidueField a) :=
    inferInstanceAs (QuasiCompact (pullback.snd h (A.1.toScheme.fromSpecResidueField a)))
  have : IsLocallyNoetherian (h.fiber a : Scheme.{u}) :=
    LocallyOfFiniteType.isLocallyNoetherian (h.fiberToSpecResidueField a)
  have : CompactSpace (h.fiber a : Scheme.{u}) :=
    (quasiCompact_iff_compactSpace (h.fiberToSpecResidueField a)).mp hfibQC
  have : IsNoetherian (h.fiber a : Scheme.{u}) := ⟨⟩
  have : Finite (_root_.ConnectedComponents (h.fiber a : Scheme.{u})) :=
    NoetherianSpace.finite_connectedComponents _
  have hclopen : IsClopen (connectedComponent p) :=
    isClopen_connectedComponent_of_finite_connectedComponents p
  set T : (h.fiber a).Opens := ⟨connectedComponent p, hclopen.2⟩
  set pT : T.toScheme := ⟨p, mem_connectedComponent⟩
  have hTp : T.ι pT = p := rfl
  have hconn : GeometricallyConnected (T.ι ≫ h.fiberToSpecResidueField a) := by
    have : ConnectedSpace T.toScheme :=
      isConnected_iff_connectedSpace.mp isConnected_connectedComponent
    let k : Type u := A.1.toScheme.residueField a
    let K₀ : Type u := Y₀.residueField y₀
    let KT : Type u := T.toScheme.residueField pT
    set φold : CommRingCat.of k ⟶ CommRingCat.of K₀ :=
      (A.1.toScheme.residueFieldCongr hy₀).inv ≫ h₀.residueFieldMap y₀ with hφold
    let : Algebra k K₀ := φold.hom.toAlgebra
    have hPTold : PurelyTranscendental k K₀ := hpt₀
    set m : T.toScheme ⟶ Y₀ := T.ι ≫ h.fiberι a ≫ B.1.ι with hm
    have hmpt : m pT = y₀ := by
      show B.1.ι (h.fiberι a (T.ι pT)) = y₀
      rw [hTp, hpf]
      rfl
    have : IsPreimmersion m := by
      rw [hm]
      exact IsPreimmersion.comp T.ι (h.fiberι a ≫ B.1.ι)
    have hmres : IsIso (m.residueFieldMap pT) := isIso_residueFieldMap_of_isPreimmersion m pT
    set eTopIso : CommRingCat.of K₀ ≅ CommRingCat.of KT :=
      (Y₀.residueFieldCongr hmpt).symm ≪≫ asIso (m.residueFieldMap pT) with heTopIso
    set gT := T.ι ≫ h.fiberToSpecResidueField a with hgT
    set q := gT pT
    have hqa : A.1.toScheme.fromSpecResidueField a q = a := by
      rw [show q = qa from Subsingleton.elim _ _]
      exact Scheme.fromSpecResidueField_apply a qa
    have : q.asIdeal.IsPrime := q.isPrime
    set φnew : CommRingCat.of k ⟶ CommRingCat.of KT :=
      CommRingCat.ofHom (algebraMap k q.asIdeal.ResidueField) ≫
        (Scheme.Spec.residueFieldIso (.of k) q).inv ≫ gT.residueFieldMap pT with hφnew
    have hfield : φnew = φold ≫ eTopIso.hom := by
      have hbase := algebraMap_residueField_comp_specResidueFieldIso_inv A.1.toScheme a q hqa
      have hcomm : m ≫ h₀ = gT ≫ A.1.toScheme.fromSpecResidueField a := by
        calc m ≫ h₀ = T.ι ≫ h.fiberι a ≫ (B.1.ι ≫ h₀) := by
              rw [hm]
              simp only [Category.assoc]
          _ = T.ι ≫ h.fiberToSpecResidueField a ≫
              A.1.toScheme.fromSpecResidueField a := by rw [← hhdef, h.fiber_fac a]
          _ = gT ≫ A.1.toScheme.fromSpecResidueField a := by
              rw [hgT]
              simp only [Category.assoc]
      calc
        φnew = (A.1.toScheme.residueFieldCongr hqa).inv ≫
            (A.1.toScheme.fromSpecResidueField a).residueFieldMap q ≫
              gT.residueFieldMap pT := by
          simpa only [hφnew, Category.assoc] using
            congrArg (fun j ↦ j ≫ gT.residueFieldMap pT) hbase
        _ = φold ≫ eTopIso.hom := by
          simpa only [hφold, heTopIso, Iso.trans_hom, Iso.symm_hom, asIso_hom,
            Category.assoc] using (residueFieldMap_square_of_eq h₀ gT m
              (A.1.toScheme.fromSpecResidueField a) hcomm pT y₀ a hmpt hqa hy₀).symm
    let : Algebra k KT := φnew.hom.toAlgebra
    set eTop : K₀ ≃+* KT := eTopIso.commRingCatIsoToRingEquiv
    have he : ∀ c : k, algebraMap k KT c = eTop (algebraMap k K₀ c) := fun c ↦
      congrArg (fun j : CommRingCat.of k ⟶ CommRingCat.of KT ↦ j.hom c) hfield
    let : PurelyTranscendental k KT :=
      (AlgEquiv.ofRingEquiv (f := eTop) fun z ↦ (he z).symm).purelyTranscendental
    exact geometricallyConnected_of_connectedSpace_of_algebraicClosure_eq_bot gT pT
      (IsAlgClosedIn.of_purelyTranscendental k KT)
  have hGI : GeometricallyIrreducible (T.ι ≫ h.fiberToSpecResidueField a) := by
    have : CompactSpace T.toScheme := isCompact_iff_compactSpace.mp hclopen.1.isCompact
    exact geometricallyIrreducible_of_geometricallyConnected_of_smooth _ hconn
  obtain ⟨V₀, hV₀, hVaff, W, hWqc, hWGI, hWfiber⟩ := h057J h a T hfp hnormal
  -- Assemble the two neighbourhoods and the finite morphism.
  obtain ⟨wq, hwY, hwV⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := h) (g := V₀.toBase) b V₀.point (hb.trans V₀.map_point.symm)
  have hwW : wq ∈ W := by
    obtain ⟨wf, hwf⟩ : wq ∈ Set.range ((pullback.snd h V₀.toBase).fiberι V₀.point) := by
      rw [Scheme.Hom.range_fiberι]
      exact hwV
    have hmem := (hWfiber wf).mpr ⟨p, mem_connectedComponent, by
      rw [hwf]
      exact hpf.trans hwY.symm⟩
    change (pullback.snd h V₀.toBase).fiberι V₀.point wf ∈ W at hmem
    rwa [hwf] at hmem
  set w : W.toScheme := ⟨wq, hwW⟩
  set wY : W.toScheme ⟶ B.1.toScheme := W.ι ≫ pullback.fst h V₀.toBase with hwYdef
  set h' : W.toScheme ⟶ V₀.scheme := W.ι ≫ pullback.snd h V₀.toBase with hh'def
  have hwY' : wY w = b := hwY
  have hwV' : h' w = V₀.point := hwV
  have hwComm : wY ≫ h = h' ≫ V₀.toBase := by
    rw [hwYdef, hh'def, Category.assoc, Category.assoc, pullback.condition]
  have : Etale wY := by
    rw [hwYdef]
    infer_instance
  have hιπ₁ (t : U₁.scheme) : B.1.ι (π₁ t) = π₀ t.val := by
    rw [← Scheme.Hom.comp_apply, hπ₁def, Scheme.Hom.resLE_comp_ι]
    rfl
  have hπ₁ : π₁ u = b := B.1.ι.isEmbedding.injective ((hιπ₁ u).trans rfl)
  have hcomm₁ : U₁.toBase ≫ fO = π₁ ≫ h := by
    show (UO.ι ≫ U₀.toBase) ≫ fO = π₀.resLE B.1 UO le_rfl ≫ B.1.ι ≫ h₀
    rw [Scheme.Hom.resLE_comp_ι_assoc, Category.assoc, hcomm₀]
  have huniq₁ (z : U₁.scheme) (hz : π₁ z = b) : z = u := by
    refine Subtype.ext ?_
    have hz₀ : π₀ z.val = y₀ := by
      rw [← hιπ₁, hz]
      rfl
    have hmem : z.val ∈ {z' : U₀.scheme | π₀ z' = y₀} := hz₀
    rwa [huniq₀] at hmem
  set pU : (pullback π₁ wY : Scheme.{u}) ⟶ U₁.scheme := pullback.fst π₁ wY with hpU
  set π' : (pullback π₁ wY : Scheme.{u}) ⟶ W.toScheme := pullback.snd π₁ wY with hπ'
  obtain ⟨z, hzU, hzW⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := π₁) (g := wY) u w (hπ₁.trans hwY'.symm)
  set U : EtaleNeighborhood X x :=
    { scheme := (pullback π₁ wY : Scheme.{u})
      point := z
      toBase := pU ≫ U₁.toBase ≫ XO.ι
      map_point := by
        show XO.ι (U₁.toBase (pU z)) = x
        rw [hzU]
        exact congrArg XO.ι U₁.map_point }
  set V : EtaleNeighborhood S (f x) :=
    { scheme := V₀.scheme
      point := V₀.point
      toBase := V₀.toBase ≫ A.1.ι
      map_point := by
        show A.1.ι (V₀.toBase V₀.point) = f x
        rw [V₀.map_point]
        show (fO ≫ A.1.ι) xO = f x
        rw [← hpullO.w]
        rfl }
  have hVres : IsIso (V₀.toBase.residueFieldMap V₀.point) := V₀.isElementary_iff.mp hV₀
  have hwqres : IsIso ((pullback.fst h V₀.toBase).residueFieldMap wq) :=
    isIso_residueFieldMap_pullback_fst_of_right h V₀.toBase wq
      ((V₀.toBase.isIso_residueFieldMap_congr hwV).mpr hVres)
  have hwres : IsIso (wY.residueFieldMap w) :=
    isIso_residueFieldMap_comp W.ι _ w inferInstance hwqres
  have hzres : IsIso (pU.residueFieldMap z) := by
    rw [hpU]
    exact isIso_residueFieldMap_pullback_fst_of_right π₁ wY z
      ((wY.isIso_residueFieldMap_congr hzW).mpr hwres)
  have hUres : IsIso (U₁.toBase.residueFieldMap u) := U₁.isElementary_iff.mp hU₁
  have hU : U.IsElementary := by
    rw [EtaleNeighborhood.isElementary_iff]
    exact isIso_residueFieldMap_comp pU _ z hzres
      (isIso_residueFieldMap_comp U₁.toBase XO.ι _ ((U₁.toBase.isIso_residueFieldMap_congr hzU).mpr
        hUres) (isIso_residueFieldMap_of_isPreimmersion XO.ι _))
  have hV : V.IsElementary := by
    rw [EtaleNeighborhood.isElementary_iff]
    exact isIso_residueFieldMap_comp V₀.toBase A.1.ι _ hVres
      (isIso_residueFieldMap_of_isPreimmersion A.1.ι _)
  have hcom : U.toBase ≫ f = π' ≫ h' ≫ V.toBase := by
    show (pU ≫ U₁.toBase ≫ XO.ι) ≫ f = π' ≫ h' ≫ V₀.toBase ≫ A.1.ι
    calc
      (pU ≫ U₁.toBase ≫ XO.ι) ≫ f = pU ≫ U₁.toBase ≫ fO ≫ A.1.ι := by
        simp only [Category.assoc, ← hpullO.w]
      _ = pU ≫ π₁ ≫ h ≫ A.1.ι := by
        rw [← Category.assoc U₁.toBase, hcomm₁]
        simp
      _ = π' ≫ wY ≫ h ≫ A.1.ι := by
        rw [← Category.assoc pU π₁, hpU, hπ', pullback.condition]
        simp only [Category.assoc]
      _ = π' ≫ h' ≫ V₀.toBase ≫ A.1.ι := by
        rw [← Category.assoc wY h, hwComm]
        simp
  have hsm' : SmoothOfRelativeDimension n h' := by
    have : SmoothOfRelativeDimension n (pullback.snd h V₀.toBase) :=
      (smoothOfRelativeDimension_isStableUnderBaseChange n).of_isPullback
        (IsPullback.of_hasPullback h V₀.toBase) hsm
    simpa [hh'def] using (inferInstance :
      SmoothOfRelativeDimension (0 + n) (W.ι ≫ pullback.snd h V₀.toBase))
  have : IsFinite π' := by
    rw [hπ']
    infer_instance
  have huniq (t : (pullback π₁ wY : Scheme.{u})) : π' t = π' z ↔ t = z := by
    refine ⟨fun ht ↦ ?_, fun ht ↦ congrArg π' ht⟩
    have htW : π' t = w := ht.trans hzW
    have htπ : π₁ (pU t) = b := by
      rw [← Scheme.Hom.comp_apply,
        show pU ≫ π₁ = π' ≫ wY from by rw [hpU, hπ']; exact pullback.condition,
        Scheme.Hom.comp_apply, htW, hwY']
    rw [hpU, hπ'] at *
    exact pullback_point_ext_of_isIso_residueFieldMap π₁ wY t z
      ((huniq₁ (pullback.fst π₁ wY t) htπ).trans hzU.symm) ht
      ((wY.isIso_residueFieldMap_congr hzW).mpr hwres)
  have hPT : ∃ heq : h' (π' z) = V₀.point,
      let : Algebra (V₀.scheme.residueField V₀.point) (W.toScheme.residueField (π' z)) :=
        ((V₀.scheme.residueFieldCongr heq).inv ≫ h'.residueFieldMap (π' z)).hom.toAlgebra
      PurelyTranscendental (V₀.scheme.residueField V₀.point)
        (W.toScheme.residueField (π' z)) := by
    have heq : h' (π' z) = V₀.point := (congrArg h' hzW).trans hwV'
    refine ⟨heq, ?_⟩
    let : Algebra (V₀.scheme.residueField V₀.point) (W.toScheme.residueField (π' z)) :=
      ((V₀.scheme.residueFieldCongr heq).inv ≫ h'.residueFieldMap (π' z)).hom.toAlgebra
    show PurelyTranscendental (V₀.scheme.residueField V₀.point)
      (W.toScheme.residueField (π' z))
    set tY := wY ≫ B.1.ι with htY
    have hty : tY (π' z) = y₀ := by
      show B.1.ι (wY (π' z)) = y₀
      rw [hzW, hwY']
      rfl
    have htComm : tY ≫ h₀ = h' ≫ V₀.toBase := by
      rw [htY, Category.assoc]
      exact hwComm
    have htres : IsIso (tY.residueFieldMap (π' z)) :=
      isIso_residueFieldMap_comp wY B.1.ι _ ((wY.isIso_residueFieldMap_congr hzW).mpr hwres)
        (isIso_residueFieldMap_of_isPreimmersion B.1.ι _)
    have : IsIso V₀.residueFieldMap := hV₀
    let : Algebra (A.1.toScheme.residueField a) (Y₀.residueField y₀) :=
      ((A.1.toScheme.residueFieldCongr hy₀).inv ≫ h₀.residueFieldMap y₀).hom.toAlgebra
    let : PurelyTranscendental (A.1.toScheme.residueField a) (Y₀.residueField y₀) := hpt₀
    refine PurelyTranscendental.of_ringEquiv_square
      (asIso V₀.residueFieldMap).commRingCatIsoToRingEquiv
      (((Y₀.residueFieldCongr hty).symm ≪≫
        asIso (tY.residueFieldMap (π' z))).commRingCatIsoToRingEquiv) ?_
    exact congrArg CommRingCat.Hom.hom
      (residueFieldMap_square h₀ h' tY V₀.toBase htComm (π' z) y₀ V₀.point a hty
        V₀.map_point hy₀ heq).symm
  refine ⟨n, hn, U, V, W.toScheme, h', π', hU, hV, hcom, hsm', ?_, inferInstance, huniq,
    hPT, ?_⟩
  · have : GeometricallyIntegral h' := hWGI
    exact fun s' ↦ inferInstance
  · intro hflp
    have hfOfp : LocallyOfFinitePresentation fO := by
      rw [hfO]
      infer_instance
    have : LocallyOfFinitePresentation π₀ := (hfp₀ hfOfp).1
    have : LocallyOfFinitePresentation π₁ := by
      rw [hπ₁def, Scheme.Hom.resLE_eq_morphismRestrict]
      infer_instance
    have : LocallyOfFinitePresentation π' := by
      rw [hπ']
      infer_instance
    exact ⟨inferInstance, inferInstance, inferInstance⟩

end AlgebraicGeometry

end
