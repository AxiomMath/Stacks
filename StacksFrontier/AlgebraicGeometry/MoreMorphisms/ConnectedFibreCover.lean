module

public import Mathlib.AlgebraicGeometry.Cover.MorphismProperty
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
public import Mathlib.FieldTheory.IsSepClosed
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ConnectedComponentSection.FibreComparison
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.GenericFibre.ShrinkingConsequences
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.ResidueField
public import StacksFrontier.AlgebraicGeometry.Properties.Noetherian
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.ConnectedSeparableClosure
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.QuasiCompactOpen
public import StacksFrontier.Topology.Noetherian.LocallyConnected

/-!
# Étale covering by morphisms with geometrically connected fibres

A flat morphism locally of finite presentation with geometrically reduced fibres admits an
étale covering of its source each member of which factors through an étale morphism to the
base, so that the first factor is flat of finite presentation with geometrically connected
and geometrically reduced fibres.

## Main results

* `AlgebraicGeometry.exists_etaleCover_factors_geometricallyConnected` (Tag 0EY5) produces the
  covering together with the factorization of each member.

## Implementation notes

The covering of the source is a `Scheme.Cover` for the étale precoverage, and the
factorization is recorded as an equality of the two composites to the base. "Of finite
presentation" is `AlgebraicGeometry.FinitePresentation`, which includes quasi-compactness and
quasi-separatedness, not merely local finite presentation.

The argument is local at a point `x` of the source: a connected quasi-compact open
neighbourhood of a point above `x` in the fibre over a separable closure of the residue field
descends to a finite separable subextension (Tag 04KU), is geometrically connected there
(Tag 0387), the subextension is realized by an étale neighbourhood of the base point
(Tag 02LF), and the resulting geometrically connected open in a fibre spreads out over an
affine elementary étale neighbourhood (Tag 055W).

## References

* [Stacks Project, Tag 0EY5](https://stacks.math.columbia.edu/tag/0EY5)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

section ProofImplementation

open CategoryTheory.Limits
open TopologicalSpace

/-- A point of a locally Noetherian, locally connected space has a quasi-compact connected
open neighbourhood. -/
private lemma exists_compact_connected_open_neighborhood
    {α : Type*} [TopologicalSpace α]
    (hα : TopologicalSpace.IsLocallyNoetherianSpace α)
    [LocallyConnectedSpace α] (x : α) :
    ∃ V : Opens α, IsCompact (V : Set α) ∧ x ∈ V ∧ _root_.IsConnected (V : Set α) := by
  obtain ⟨W, hWopen, hxW, hWnoeth⟩ := hα x
  let : NoetherianSpace W := hWnoeth
  let : LocallyConnectedSpace W := hWopen.locallyConnectedSpace
  let x' : W := ⟨x, hxW⟩
  exact ⟨⟨_, (isOpen_connectedComponent (x := x')).trans hWopen⟩,
    (NoetherianSpace.isCompact _).image continuous_subtype_val,
    ⟨x', mem_connectedComponent, rfl⟩,
    ⟨⟨x, x', mem_connectedComponent, rfl⟩, (isConnected_connectedComponent (x := x')).2.image _
      continuous_subtype_val.continuousOn⟩⟩

/-- A point of a scheme locally of finite presentation over a field has, in the base change to
the separable closure, a preimage with a quasi-compact connected open neighbourhood. -/
private theorem exists_compact_connected_open_after_separable_closure
    {k : Type u} [Field k] (X : Scheme.{u})
    (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFinitePresentation f] (x : X) :
    ∃ (V : (pullback f (spectrumMap k (SeparableClosure k))).Opens)
      (xbar : ↥(pullback f (spectrumMap k (SeparableClosure k)))),
      (pullback.fst f (spectrumMap k (SeparableClosure k))) xbar = x ∧
        xbar ∈ V ∧
          IsCompact (V : Set ↥(pullback f (spectrumMap k (SeparableClosure k)))) ∧
            _root_.IsConnected
              (V : Set ↥(pullback f (spectrumMap k (SeparableClosure k)))) := by
  let K := SeparableClosure k
  let : Algebra.IsAlgebraic k K := IsSepClosure.separable.isAlgebraic
  have : Surjective (spectrumMap k (SeparableClosure k)) := by
    rw [surjective_iff]
    show Function.Surjective (PrimeSpectrum.comap (algebraMap k K))
    exact Algebra.IsIntegral.comap_surjective k K
  obtain ⟨xbar, hxbar⟩ :=
    (inferInstance : Surjective (pullback.fst f (spectrumMap k (SeparableClosure k)))).surj x
  let P : Scheme.{u} := pullback f (spectrumMap k (SeparableClosure k))
  let : LocallyOfFinitePresentation
      (pullback.snd f (spectrumMap k (SeparableClosure k))) := inferInstance
  let : LocallyOfFiniteType
      (pullback.snd f (spectrumMap k (SeparableClosure k))) := inferInstance
  let : IsLocallyNoetherian P :=
    LocallyOfFiniteType.isLocallyNoetherian
      (pullback.snd f (spectrumMap k (SeparableClosure k)))
  have hP : TopologicalSpace.IsLocallyNoetherianSpace P :=
    AlgebraicGeometry.isLocallyNoetherianSpace_of_isLocallyNoetherian P
  let : LocallyConnectedSpace P := hP.locallyConnectedSpace P
  obtain ⟨V, hcompact, hxV, hconnected⟩ :=
    exists_compact_connected_open_neighborhood hP xbar
  exact ⟨V, xbar, hxbar, hxV, hcompact, hconnected⟩

/-- The connected quasi-compact open neighbourhood produced over the separable closure
descends to a quasi-compact open over a finite subextension, together with the comparison
morphism of the two base changes. -/
private theorem exists_finite_intermediate_open_neighborhood
    {k : Type u} [Field k] (X : Scheme.{u})
    (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFinitePresentation f] (x : X) :
    ∃ (E : IntermediateField k (SeparableClosure k)) (_ : FiniteDimensional k E)
      (V : (pullback f (spectrumMap k E)).Opens)
      (y : ↥(pullback f (spectrumMap k E)))
      (Vbar : (pullback f (spectrumMap k (SeparableClosure k))).Opens)
      (p : pullback f (spectrumMap k (SeparableClosure k)) ⟶
        pullback f (spectrumMap k E))
      (_ : p ≫ pullback.fst f (spectrumMap k E) =
        pullback.fst f (spectrumMap k (SeparableClosure k)))
      (_ : p ≫ pullback.snd f (spectrumMap k E) =
        pullback.snd f (spectrumMap k (SeparableClosure k)) ≫
          Spec.map (CommRingCat.ofHom (algebraMap E (SeparableClosure k))))
      (_ : Vbar = p ⁻¹ᵁ V)
      (_ : _root_.IsConnected (Vbar : Set ↥(pullback f
        (spectrumMap k (SeparableClosure k))))) ,
      IsCompact (V : Set ↥(pullback f (spectrumMap k E))) ∧
        y ∈ V ∧ (pullback.fst f (spectrumMap k E)) y = x := by
  let : Algebra.IsAlgebraic k (SeparableClosure k) := IsSepClosure.separable.isAlgebraic
  obtain ⟨Vbar, xbar, hxbar, hxVbar, hcompact, hconnected⟩ :=
    exists_compact_connected_open_after_separable_closure X f x
  obtain ⟨E, hE, V, hV, p, hfst, hsnd, hpreimage⟩ :=
    AlgebraicGeometry.exists_finite_subextension_descending_isCompact_open X f Vbar hcompact
  let y : ↥(pullback f (spectrumMap k E)) := p xbar
  have hyV : y ∈ V := by
    show xbar ∈ p ⁻¹ᵁ V
    rw [← hpreimage]
    exact hxVbar
  have hyx : (pullback.fst f (spectrumMap k E)) y = x := by
    show (p ≫ pullback.fst f (spectrumMap k E)) xbar = x
    rw [hfst]
    exact hxbar
  exact ⟨E, hE, V, y, Vbar, p, hfst, hsnd, hpreimage, hconnected,
    hV, hyV, hyx⟩

/-- The separable closure of a field is a separable closure of any intermediate field of it. -/
private theorem separableClosure_over_intermediate_is_separableClosure
    {k : Type u} [Field k] (E : IntermediateField k (SeparableClosure k)) :
    IsSepClosure E (SeparableClosure k) :=
  isSepClosure_iff.2 ⟨IsSepClosure.sep_closed k, E.isSeparable_tower_top⟩

/-- Restricting the top left corner of a pullback square along an open of the corner above it
gives a pullback square. -/
private theorem isPullback_restrict_comp {P Q S T : Scheme.{u}} {p : P ⟶ Q} {r : P ⟶ S}
    {q : Q ⟶ T} {i : S ⟶ T} (H : IsPullback p r q i) (V : Q.Opens) :
    IsPullback (p ∣_ V) ((p ⁻¹ᵁ V).ι ≫ r) (V.ι ≫ q) i :=
  ((isPullback_morphismRestrict p V).flip.paste_horiz H.flip).flip

/-- An open of a base change to a finite subextension whose preimage over the separable
closure is connected is geometrically connected over that subextension. -/
private theorem descended_open_geometricallyConnected
    {k : Type u} [Field k] (X : Scheme.{u})
    (f : X ⟶ Spec (CommRingCat.of k))
    (E : IntermediateField k (SeparableClosure k))
    (Vbar : (pullback f (spectrumMap k (SeparableClosure k))).Opens)
    (V : (pullback f (spectrumMap k E)).Opens)
    (p : pullback f (spectrumMap k (SeparableClosure k)) ⟶
      pullback f (spectrumMap k E))
    (hp₁ : p ≫ pullback.fst f (spectrumMap k E) =
      pullback.fst f (spectrumMap k (SeparableClosure k)))
    (hp₂ : p ≫ pullback.snd f (spectrumMap k E) =
      pullback.snd f (spectrumMap k (SeparableClosure k)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap E (SeparableClosure k))))
    (hpre : Vbar = p ⁻¹ᵁ V)
    (hconn : _root_.IsConnected (Vbar : Set ↥(pullback f
      (spectrumMap k (SeparableClosure k))))) :
    GeometricallyConnected (V.ι ≫ pullback.snd f (spectrumMap k E)) := by
  let K := SeparableClosure k
  let : Algebra.IsAlgebraic k K := IsSepClosure.separable.isAlgebraic
  let : IsSepClosure E K :=
    separableClosure_over_intermediate_is_separableClosure E
  have hcomp : spectrumMap E K ≫ spectrumMap k E = spectrumMap k K := by
    rw [← Spec.map_comp, Spec.map_inj]
    rw [← CommRingCat.ofHom_comp]
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    rw [CommRingCat.ofHom_apply, CommRingCat.ofHom_apply, RingHom.comp_apply]
    exact (IsScalarTower.algebraMap_apply k E K x).symm
  have H : IsPullback p (pullback.snd f (spectrumMap k K))
      (pullback.snd f (spectrumMap k E)) (spectrumMap E K) := by
    refine IsPullback.of_right ?_ hp₂ (IsPullback.of_hasPullback f (spectrumMap k E))
    rw [hp₁, hcomp]
    exact IsPullback.of_hasPullback f (spectrumMap k K)
  subst hpre
  exact (geometricallyConnected_iff_connectedSpace_baseChange E K _).2
    ((Scheme.Hom.homeomorph (isPullback_restrict_comp H V).isoPullback.hom).connectedSpace_iff.mp
      (isConnected_iff_connectedSpace.mp hconn))

/-- Geometric connectedness of an open of the target, as a scheme over the base, transfers
along an isomorphism of total spaces compatible with an isomorphism of bases. -/
private theorem geometricallyConnected_preimage_of_iso
    {P Q S T : Scheme.{u}} (p : P ⟶ S) (q : Q ⟶ T) (i : S ⟶ T)
    [IsIso i] (e : P ≅ Q) (he : e.hom ≫ q = p ≫ i)
    (V : Q.Opens) (hV : GeometricallyConnected (V.ι ≫ q)) :
    GeometricallyConnected ((e.hom ⁻¹ᵁ V).ι ≫ p) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (isPullback_restrict_comp (IsPullback.of_horiz_isIso (CommSq.mk he)) V) hV

/-- A geometrically connected open of a fibre containing the image of a point spreads out,
over an étale neighbourhood of the base point, to a quasi-compact open with geometrically
connected fibres containing a point above that point. -/
private theorem exists_open_piece_after_fiber_open
    {X S : Scheme.{u}} (f : X ⟶ S) [Flat f] [GeometricallyReduced f]
    (hfp : FinitePresentation f) (s : S) (T : (f.fiber s).Opens)
    [GeometricallyConnected (T.ι ≫ f.fiberToSpecResidueField s)]
    (y : f.fiber s) (hy : y ∈ T) (x : X) (hx : f.fiberι s y = x) :
    ∃ (U : AlgebraicGeometry.EtaleNeighborhood S s)
      (V : (pullback f U.toBase).Opens),
      QuasiCompact V.ι ∧
        GeometricallyConnected (V.ι ≫ pullback.snd f U.toBase) ∧
          ∃ z : ↥(pullback f U.toBase), z ∈ V ∧
            pullback.fst f U.toBase z = x := by
  obtain ⟨U, hElementary, hAffine, V, hVqc, hVconn, hViff⟩ :=
    AlgebraicGeometry.exists_etaleNeighborhood_geometricallyConnected
      f s T hfp
  have : IsIso U.residueFieldMap := hElementary
  let fU := pullback.snd f U.toBase
  let e := ConnectedComponentSection.elementaryFiberIso f U
  let z : fU.fiber U.point := e.inv y
  have hz : e.hom z = y := by simp [z]
  have hproject : pullback.fst f U.toBase (fU.fiberι U.point z) = f.fiberι s y := by
    have h : (e.hom ≫ f.fiberι s) z =
        (fU.fiberι U.point ≫ pullback.fst f U.toBase) z :=
      congrArg (fun g => g z) (ConnectedComponentSection.elementaryFiberIso_hom_fiberι f U)
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hz] at h
    exact h.symm
  exact ⟨U, V, hVqc, hVconn, _, (hViff z).2 ⟨y, hy, hproject.symm⟩, hproject.trans hx⟩

/-- Restricting a morphism with geometrically reduced fibres to an open of its source leaves
the fibres geometrically reduced. -/
private theorem geometricallyReduced_comp_of_isOpenImmersion
    {W Y S : Scheme.{u}} (i : W ⟶ Y) [IsOpenImmersion i] (q : Y ⟶ S)
    [GeometricallyReduced q] : GeometricallyReduced (i ≫ q) := by
  rw [GeometricallyReduced.eq_geometrically]
  intro K hK y Z fst snd h
  let r := pullback.map (i ≫ q) y q y i (𝟙 _) (𝟙 _)
    (by simp) (by simp)
  have : IsReduced (pullback q y) :=
    GeometricallyReduced.geometrically_isReduced (f := q) y
      (pullback.fst q y) (pullback.snd q y) (.of_hasPullback q y)
  exact ObjectProperty.prop_of_iso IsReduced h.isoPullback.symm (isReduced_of_isOpenImmersion r)

/-- A morphism locally of finite presentation restricted to affine opens of source and target
is of finite presentation. -/
private theorem finitePresentation_resLE_of_affine_opens
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFinitePresentation f]
    (U : S.Opens) (hU : IsAffineOpen U) (V : X.Opens) (hV : IsAffineOpen V)
    (e : V ≤ f ⁻¹ᵁ U) : FinitePresentation (f.resLE U V e) := by
  let : IsAffine V := hV
  let : IsAffine U := hU
  exact ⟨inferInstance, inferInstance, inferInstance⟩

/-- The local datum produced at a point `x` of the source: an étale morphism to the source
whose image contains `x`, factoring through an étale morphism to the base so that the first
factor is flat of finite presentation with geometrically connected and reduced fibres. -/
private structure LocalGoodPiece {X S : Scheme.{u}} (f : X ⟶ S) (x : X) where
  /-- The intermediate base, étale over `S`. -/
  base : Scheme.{u}
  /-- The étale structure morphism of the intermediate base. -/
  toBase : base ⟶ S
  /-- The member of the covering. -/
  source : Scheme.{u}
  /-- The étale morphism from the member of the covering to the source. -/
  toSource : source ⟶ X
  /-- The factoring morphism to the intermediate base. -/
  toBaseScheme : source ⟶ base
  /-- The intermediate base is étale over `S`. -/
  etaleBase : Etale toBase
  /-- The member of the covering is étale over the source. -/
  etaleSource : Etale toSource
  /-- The factoring morphism is flat. -/
  flat : Flat toBaseScheme
  /-- The factoring morphism is of finite presentation. -/
  finitePresentation : FinitePresentation toBaseScheme
  /-- The factoring morphism has geometrically connected fibres. -/
  geometricallyConnected : GeometricallyConnected toBaseScheme
  /-- The factoring morphism has geometrically reduced fibres. -/
  geometricallyReduced : GeometricallyReduced toBaseScheme
  /-- The two composites to `S` agree. -/
  factors : toSource ≫ f = toBaseScheme ≫ toBase
  /-- The member of the covering hits the given point. -/
  coversPoint : ∃ y : source, toSource y = x

/-- After an étale base change there is a geometrically connected open of the fibre over the
distinguished point containing a point above `x`. -/
private theorem exists_geometricallyConnected_open_after_etale
    {X S : Scheme.{u}} (f : X ⟶ S) (hfp : FinitePresentation f) (x : X) :
    ∃ (U : AlgebraicGeometry.EtaleNeighborhood S (f x))
      (T : ((pullback.snd f U.toBase).fiber U.point).Opens),
    (∃ y : (pullback.snd f U.toBase).fiber U.point,
        y ∈ T ∧ pullback.fst f U.toBase
          ((pullback.snd f U.toBase).fiberι U.point y) = x) ∧
        GeometricallyConnected
          (T.ι ≫ (pullback.snd f U.toBase).fiberToSpecResidueField U.point) := by
  let k := S.residueField (f x)
  let p := f.fiberToSpecResidueField (f x)
  let z : f.fiber (f x) := f.asFiber x
  let : Field k := inferInstance
  let : LocallyOfFinitePresentation f :=
    FinitePresentation.locallyOfFinitePresentation hfp
  let : LocallyOfFinitePresentation p := by
    dsimp [p, Scheme.Hom.fiberToSpecResidueField, Scheme.Hom.fiber]
    infer_instance
  obtain ⟨E, hE, V, y, Vbar, pbar, hfst, hsnd, hpre, hconnected,
      hVcompact, hyV, hyx⟩ :=
    @exists_finite_intermediate_open_neighborhood k inferInstance
      (f.fiber (f x)) p (by
        dsimp [p, Scheme.Hom.fiberToSpecResidueField, Scheme.Hom.fiber]
        infer_instance) z
  have hVconn : GeometricallyConnected (V.ι ≫
      pullback.snd p (spectrumMap k E)) :=
    @descended_open_geometricallyConnected k inferInstance (f.fiber (f x)) p
      E Vbar V pbar hfst hsnd hpre hconnected
  let : Field E := inferInstance
  let : Algebra k E := inferInstance
  let : FiniteDimensional k E := hE
  let : Module.Finite k E := inferInstance
  let : Algebra.IsSeparable k E := inferInstance
  obtain ⟨U, hAlg⟩ :=
    AlgebraicGeometry.exists_etaleNeighborhood_residueField_algEquiv S (f x) E
  let : Algebra k (U.scheme.residueField U.point) := U.residueFieldMap.hom.toAlgebra
  obtain ⟨e⟩ := hAlg
  let s₁ := U.toBase U.point
  let k₁ := S.residueField s₁
  let c := S.residueFieldCongr U.map_point.symm
  let raw := U.toBase.residueFieldMap U.point
  let : Field k₁ := inferInstance
  let : Algebra k₁ (U.scheme.residueField U.point) := raw.hom.toAlgebra
  let : Algebra k₁ E := (algebraMap k E).comp c.inv.hom |>.toAlgebra
  have hres : U.residueFieldMap.hom = raw.hom.comp c.hom.hom := by
    rfl
  let e' : U.scheme.residueField U.point ≃ₐ[k₁] E :=
    AlgEquiv.ofRingEquiv (f := e.toRingEquiv) (by
      intro a
      show e (raw.hom a) = (algebraMap k E) (c.inv.hom a)
      calc
        e (raw.hom a) = e (U.residueFieldMap.hom (c.inv.hom a)) := by
          congr 1
          rw [hres]
          simp
        _ = (algebraMap k E) (c.inv.hom a) := e.commutes (c.inv.hom a))
  let iField : Spec (CommRingCat.of (U.scheme.residueField U.point)) ⟶
      Spec (CommRingCat.of E) :=
    Spec.map e'.symm.toRingEquiv.toCommRingCatIso.hom
  let iBase : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of k₁) :=
    Spec.map c.inv
  let pE0 := spectrumMap k E
  let pE1 := spectrumMap k₁ E
  have hiField : Spec.map raw = iField ≫ pE1 := by
    dsimp [iField, pE1, spectrumMap]
    rw [← Spec.map_comp]
    congr 1
    ext a
    show raw.hom a = e'.symm ((algebraMap k₁ E) a)
    exact (e'.symm.commutes a).symm
  let fU := pullback.snd f U.toBase
  let q0 := p
  let q1 := f.fiberToSpecResidueField s₁
  let eEq : f.fiber (f x) ≅ f.fiber s₁ := fiberIsoOfEq f U.map_point.symm
  have heqBase : q0 ≫ iBase = eEq.hom ≫ q1 :=
    (ConnectedComponentSection.fiberIsoOfEq_hom_fiberToSpecResidueField f
      U.map_point.symm).symm
  have heqField : pE0 ≫ iBase = pE1 := by
    dsimp [pE0, pE1, iBase, spectrumMap]
    rw [← Spec.map_comp]
    congr 1
  let : IsIso eEq.hom := by infer_instance
  let : IsIso iBase := by dsimp [iBase]; infer_instance
  let qE0 := pullback q0 pE0
  let qE1 := pullback q1 pE1
  let mChange := pullback.map q0 pE0 q1 pE1 eEq.hom (𝟙 _) iBase heqBase heqField
  have : IsIso mChange := by
    dsimp [mChange]
    apply pullback.map_isIso
  let eChange : qE0 ≅ qE1 := asIso
    mChange
  have heChange : eChange.symm.hom ≫ pullback.snd q0 pE0 =
      pullback.snd q1 pE1 := by
    have hSnd : mChange ≫ pullback.snd q1 pE1 = pullback.snd q0 pE0 := by
      show pullback.map q0 pE0 q1 pE1 eEq.hom (𝟙 _) iBase heqBase heqField ≫
        pullback.snd q1 pE1 = _
      exact pullback.lift_snd _ _ _
    show inv mChange ≫ pullback.snd q0 pE0 = pullback.snd q1 pE1
    calc
      inv mChange ≫ pullback.snd q0 pE0 =
          inv mChange ≫ (mChange ≫ pullback.snd q1 pE1) := by rw [hSnd]
      _ = pullback.snd q1 pE1 := by simp
  let V₁ : qE1.Opens := eChange.inv ⁻¹ᵁ V
  have hV₁ : GeometricallyConnected (V₁.ι ≫ pullback.snd q1 pE1) :=
    geometricallyConnected_preimage_of_iso (pullback.snd q1 pE1)
      (pullback.snd q0 pE0) (𝟙 _) eChange.symm
      (by simpa using heChange) V hVconn
  let pU := Spec.map raw
  let qU := pullback q1 pU
  let eFib : fU.fiber U.point ≅ qU :=
    (isPullback_fiberToSpecResidueField_of_isPullback
      (IsPullback.of_hasPullback f U.toBase) U.point).flip.isoIsPullback _ _
      (IsPullback.of_hasPullback q1 pU).flip
  let eField : qU ≅ qE1 := asIso
    (pullback.map q1 pU q1 pE1 (𝟙 _) iField (𝟙 _) (by simp)
      (by simpa using hiField))
  let eTotal := eFib.trans eField
  have heTotal : eTotal.hom ≫ pullback.snd q1 pE1 =
      fU.fiberToSpecResidueField U.point ≫ iField := by
    have hFibPB := isPullback_fiberToSpecResidueField_of_isPullback
      (IsPullback.of_hasPullback f U.toBase) U.point
    have hFibSnd : eFib.hom ≫ pullback.snd q1 pU =
        fU.fiberToSpecResidueField U.point :=
      hFibPB.flip.isoIsPullback_hom_fst _ _ (IsPullback.of_hasPullback q1 pU).flip
    have hFieldSnd : eField.hom ≫ pullback.snd q1 pE1 =
        pullback.snd q1 pU ≫ iField := by
      show pullback.map q1 pU q1 pE1 (𝟙 _) iField (𝟙 _)
        (by simp) (by simpa using hiField) ≫ pullback.snd q1 pE1 = _
      exact pullback.lift_snd _ _ _
    calc
      eTotal.hom ≫ pullback.snd q1 pE1 =
          eFib.hom ≫ eField.hom ≫ pullback.snd q1 pE1 := by
            simp [eTotal, Category.assoc]
      _ = eFib.hom ≫ pullback.snd q1 pU ≫ iField :=
            congrArg (fun t => eFib.hom ≫ t) hFieldSnd
      _ = fU.fiberToSpecResidueField U.point ≫ iField :=
            congrArg (fun t => t ≫ iField) hFibSnd
  let T : (fU.fiber U.point).Opens := eTotal.hom ⁻¹ᵁ V₁
  have hTconn : GeometricallyConnected (T.ι ≫ fU.fiberToSpecResidueField U.point) :=
    geometricallyConnected_preimage_of_iso
      (fU.fiberToSpecResidueField U.point) (pullback.snd q1 pE1)
      iField eTotal heTotal V₁ hV₁
  let y₁ : qE1 := eChange.hom y
  let yU : fU.fiber U.point := eTotal.inv y₁
  have hy₁ : y₁ ∈ V₁ := by
    show eChange.inv (eChange.hom y) ∈ V
    simpa using hyV
  have hyU : yU ∈ T := by
    show eTotal.hom (eTotal.inv y₁) ∈ V₁
    simpa using hy₁
  have hchangeFst : eChange.hom ≫ pullback.fst q1 pE1 =
      pullback.fst q0 pE0 ≫ eEq.hom := by
    show mChange ≫ pullback.fst q1 pE1 = _
    calc
      mChange ≫ pullback.fst q1 pE1 = pullback.fst q0 pE0 ≫ eEq.hom := by
        show pullback.map q0 pE0 q1 pE1 eEq.hom (𝟙 _) iBase heqBase heqField ≫
          pullback.fst q1 pE1 = _
        exact pullback.lift_fst _ _ _
      _ = pullback.fst q0 pE0 ≫ eEq.hom := rfl
  have hField : eField.hom ≫ pullback.fst q1 pE1 = pullback.fst q1 pU := by
    show pullback.map q1 pU q1 pE1 (𝟙 _) iField (𝟙 _)
      (by simp) (by simpa using hiField) ≫ pullback.fst q1 pE1 = _
    exact pullback.lift_fst _ _ _
  have hfirst : fU.fiberι U.point ≫ pullback.fst f U.toBase =
      eTotal.hom ≫ pullback.fst q1 pE1 ≫ f.fiberι s₁ := by
    have hFib : eFib.hom ≫ pullback.fst q1 pU =
        baseChangeFiberMap f U.toBase U.point := by
      have hFibPB := isPullback_fiberToSpecResidueField_of_isPullback
        (IsPullback.of_hasPullback f U.toBase) U.point
      exact hFibPB.flip.isoIsPullback_hom_snd _ _
        (IsPullback.of_hasPullback q1 pU).flip
    calc
      fU.fiberι U.point ≫ pullback.fst f U.toBase =
          baseChangeFiberMap f U.toBase U.point ≫ f.fiberι s₁ :=
            (baseChangeFiberMap_comp_fiberι f U.toBase U.point).symm
      _ = eFib.hom ≫ pullback.fst q1 pU ≫ f.fiberι s₁ :=
            (congrArg (fun t => t ≫ f.fiberι s₁) hFib).symm
      _ = eFib.hom ≫ eField.hom ≫ pullback.fst q1 pE1 ≫ f.fiberι s₁ :=
            congrArg (fun t => eFib.hom ≫ t ≫ f.fiberι s₁) hField.symm
      _ = eTotal.hom ≫ pullback.fst q1 pE1 ≫ f.fiberι s₁ := by
            simp [eTotal, Category.assoc]
  have hpoint : pullback.fst f U.toBase (fU.fiberι U.point yU) = x := by
    calc
      pullback.fst f U.toBase (fU.fiberι U.point yU) =
          (eTotal.hom ≫ pullback.fst q1 pE1 ≫ f.fiberι s₁) yU :=
            congrArg (fun g => g yU) hfirst
      _ = (pullback.fst q1 pE1 ≫ f.fiberι s₁) y₁ := by simp [yU]
      _ = (pullback.fst q0 pE0 ≫ eEq.hom ≫ f.fiberι s₁) y := by
            show (pullback.fst q1 pE1 ≫ f.fiberι s₁) (eChange.hom y) = _
            have hh := congrArg (fun t => t ≫ f.fiberι s₁) hchangeFst
            simpa [Category.assoc] using congrArg (fun g => g y) hh
      _ = (pullback.fst q0 pE0 ≫ f.fiberι (f x)) y := by
            rw [fiberIsoOfEq_hom_fiberι f U.map_point.symm]
      _ = x := by
            show f.fiberι (f x) ((pullback.fst q0 pE0) y) = x
            rw [hyx]
            simp [z, Scheme.Hom.fiberι_asFiber]
  exact ⟨U, T, ⟨yU, hyU, hpoint⟩, hTconn⟩

/-- Every point of the source admits a local datum as in `LocalGoodPiece`. -/
private theorem exists_localGoodPiece
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFinitePresentation f] [Flat f]
    [GeometricallyReduced f] (x : X) : Nonempty (LocalGoodPiece f x) := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hsU, -⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hsU (f ⁻¹ᵁ U).isOpen
  have hVU' : V ≤ f ⁻¹ᵁ U := by
    intro y hy
    exact hVU hy
  let f₀ := f.resLE U V hVU'
  let x₀ : ↥(V : Set X) := ⟨x, hxV⟩
  have : LocallyOfFinitePresentation f₀ := by
    show LocallyOfFinitePresentation (f.resLE U V hVU')
    infer_instance
  have : Flat f₀ := by
    show Flat (f.resLE U V hVU')
    infer_instance
  have : GeometricallyReduced f₀ :=
    geometricallyReduced_comp_of_isOpenImmersion
      (X.homOfLE hVU') (f ∣_ U)
  have hfp₀ : FinitePresentation f₀ :=
    finitePresentation_resLE_of_affine_opens f U hU V hV hVU'
  obtain ⟨U₁, T, ⟨y, hyT, hyx⟩, hTconn⟩ :=
    exists_geometricallyConnected_open_after_etale f₀ hfp₀ x₀
  have : QuasiCompact f₀ := hfp₀.quasiCompact
  have : QuasiSeparated f₀ := hfp₀.quasiSeparated
  let f₁ := pullback.snd f₀ U₁.toBase
  have : LocallyOfFinitePresentation f₁ := inferInstance
  have : Flat f₁ := inferInstance
  have : GeometricallyReduced f₁ := inferInstance
  have hfp₁ : FinitePresentation f₁ := ⟨inferInstance, inferInstance, inferInstance⟩
  have : QuasiCompact f₁ := hfp₁.quasiCompact
  have : QuasiSeparated f₁ := hfp₁.quasiSeparated
  let : GeometricallyConnected (T.ι ≫ f₁.fiberToSpecResidueField U₁.point) := hTconn
  obtain ⟨U₂, W, hWqc, hWconn, z, hzW, hzx⟩ :=
    exists_open_piece_after_fiber_open f₁ hfp₁ U₁.point T y hyT
      (f₁.fiberι U₁.point y) rfl
  let g := W.ι ≫ pullback.snd f₁ U₂.toBase
  let j := W.ι ≫ pullback.fst f₁ U₂.toBase ≫
    pullback.fst f₀ U₁.toBase ≫ Scheme.Opens.ι V
  let h := U₂.toBase ≫ U₁.toBase ≫ Scheme.Opens.ι U
  have hEtaleBase : Etale h := by
    dsimp [h]
    infer_instance
  have hEtaleSource : Etale j := by
    dsimp [j]
    infer_instance
  have : Flat g := by
    dsimp [g]
    infer_instance
  have hfpW : FinitePresentation W.ι := ⟨inferInstance, hWqc, inferInstance⟩
  have : LocallyOfFinitePresentation W.ι := hfpW.locallyOfFinitePresentation
  have : QuasiCompact W.ι := hfpW.quasiCompact
  have : QuasiSeparated W.ι := hfpW.quasiSeparated
  have hfpPullback : FinitePresentation (pullback.snd f₁ U₂.toBase) :=
    ⟨inferInstance, inferInstance, inferInstance⟩
  have : LocallyOfFinitePresentation (pullback.snd f₁ U₂.toBase) :=
    hfpPullback.locallyOfFinitePresentation
  have : QuasiCompact (pullback.snd f₁ U₂.toBase) := hfpPullback.quasiCompact
  have : QuasiSeparated (pullback.snd f₁ U₂.toBase) := hfpPullback.quasiSeparated
  have hfpG : FinitePresentation g := by
    dsimp [g]
    exact ⟨inferInstance, inferInstance, inferInstance⟩
  have hGR : GeometricallyReduced g := by
    dsimp [g]
    exact geometricallyReduced_comp_of_isOpenImmersion W.ι
      (pullback.snd f₁ U₂.toBase)
  have hfactor : j ≫ f = g ≫ h := by
    have hres : f₀ ≫ Scheme.Opens.ι U = Scheme.Opens.ι V ≫ f :=
      Scheme.Hom.resLE_comp_ι f hVU'
    have hpb₁ : pullback.fst f₀ U₁.toBase ≫ f₀ =
        pullback.snd f₀ U₁.toBase ≫ U₁.toBase := pullback.condition
    have hpb₂ : pullback.fst f₁ U₂.toBase ≫ f₁ =
        pullback.snd f₁ U₂.toBase ≫ U₂.toBase := pullback.condition
    calc
      j ≫ f = W.ι ≫ pullback.fst f₁ U₂.toBase ≫
          pullback.fst f₀ U₁.toBase ≫ (Scheme.Opens.ι V ≫ f) := by
            simp only [j, Category.assoc]
      _ = W.ι ≫ pullback.fst f₁ U₂.toBase ≫
          pullback.fst f₀ U₁.toBase ≫ f₀ ≫ Scheme.Opens.ι U := by
            rw [hres]
      _ = W.ι ≫ pullback.fst f₁ U₂.toBase ≫
          (pullback.fst f₀ U₁.toBase ≫ f₀) ≫ Scheme.Opens.ι U := by
            simp only [Category.assoc]
      _ = W.ι ≫ pullback.fst f₁ U₂.toBase ≫
          (pullback.snd f₀ U₁.toBase ≫ U₁.toBase) ≫ Scheme.Opens.ι U := by
            rw [hpb₁]
      _ = W.ι ≫ (pullback.fst f₁ U₂.toBase ≫ f₁) ≫
          U₁.toBase ≫ Scheme.Opens.ι U := by
            dsimp only [f₁]
            simp only [Category.assoc]
      _ = W.ι ≫ (pullback.snd f₁ U₂.toBase ≫ U₂.toBase) ≫
          U₁.toBase ≫ Scheme.Opens.ι U := by
            rw [hpb₂]
      _ = W.ι ≫ pullback.snd f₁ U₂.toBase ≫ U₂.toBase ≫
          U₁.toBase ≫ Scheme.Opens.ι U := by
            simp only [Category.assoc]
      _ = g ≫ h := rfl
  have hPoint : ∃ w : W, j w = x := by
    refine ⟨⟨z, hzW⟩, ?_⟩
    show Scheme.Opens.ι V ((pullback.fst f₀ U₁.toBase)
      ((pullback.fst f₁ U₂.toBase) z)) = x
    calc
      _ = Scheme.Opens.ι V ((pullback.fst f₀ U₁.toBase)
          (f₁.fiberι U₁.point y)) := by rw [hzx]
      _ = Scheme.Opens.ι V x₀ := by rw [hyx]
      _ = x := rfl
  exact ⟨⟨U₂.scheme, h, W, j, g, hEtaleBase, hEtaleSource,
    ‹Flat g›, hfpG, hWconn, hGR, hfactor, hPoint⟩⟩

end ProofImplementation

/-- **Stacks Project, Tag 0EY5.** A flat morphism locally of finite presentation with
geometrically reduced fibres admits an étale covering of its source each member of which
factors through an étale morphism to the base, the first factor being flat of finite
presentation with geometrically connected and geometrically reduced fibres. -/
@[stacks 0EY5]
theorem exists_etaleCover_factors_geometricallyConnected
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFinitePresentation f] [Flat f]
    [GeometricallyReduced f] :
    ∃ 𝒰 : X.Cover.{u} Scheme.etalePrecoverage, ∀ i : 𝒰.I₀,
      ∃ (Sᵢ : Scheme.{u}) (h : Sᵢ ⟶ S) (g : 𝒰.X i ⟶ Sᵢ),
        Etale h ∧ Flat g ∧ FinitePresentation g ∧
          GeometricallyConnected g ∧ GeometricallyReduced g ∧
            g ≫ h = 𝒰.f i ≫ f := by
  let P : (x : X) → LocalGoodPiece f x :=
    fun x => Classical.choice (exists_localGoodPiece f x)
  let 𝒰 : X.Cover Scheme.etalePrecoverage :=
    Scheme.Cover.mkOfCovers (P := @Etale) X
      (fun x => (P x).source)
      (fun x => (P x).toSource)
      (fun x => by
        obtain ⟨y, hy⟩ := (P x).coversPoint
        exact ⟨x, y, hy⟩)
      (fun x => (P x).etaleSource)
  exact ⟨𝒰, fun i => ⟨(P i).base, (P i).toBase, (P i).toBaseScheme, (P i).etaleBase,
    (P i).flat, (P i).finitePresentation, (P i).geometricallyConnected,
    (P i).geometricallyReduced, (P i).factors.symm⟩⟩

end AlgebraicGeometry

end
