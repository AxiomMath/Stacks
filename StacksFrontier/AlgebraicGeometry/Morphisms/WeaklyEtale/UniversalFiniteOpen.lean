module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.AlgebraicGeometry.Restrict
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.Approximation
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.QuasiFinite
public import StacksFrontier.AlgebraicGeometry.Morphisms.WeaklyEtale.IdempotentUniversalAlgebra
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Fibre
public import StacksFrontier.RingTheory.ZariskisMainTheorem

/-!
# The universal finite open subscheme of a quasi-finite morphism

Let `f : X ⟶ Y` be a quasi-finite morphism of finite presentation between affine schemes. The
open subschemes of a base change `Y' ×_Y X` that are finite over `Y'` are classified by a single
morphism `Y_univ ⟶ Y` of finite presentation carrying one such open subscheme
`U_univ ⊆ Y_univ ×_Y X`: every finite open subscheme of `Y' ×_Y X`, for `Y'` affine, is the
inverse image of `U_univ` along some morphism `Y' ⟶ Y_univ` over `Y`.

## Main results

* `AlgebraicGeometry.exists_universal_finite_open_subscheme` constructs the universal base change
  and its finite open subscheme. This is **Stacks Tag 0F3N**.

## Implementation notes

An open subscheme of the base change is recorded as an element of
`(pullback f g).Opens`, and the operation of taking inverse images is the inverse image of opens
along the canonical morphism of fibre products. Unlike the source statement, the universal base
`Y_univ` is not asked to be affine; it is an open subscheme of an affine scheme.

Quasi-finiteness enters only through the identification of quasi-finite morphisms with the
morphisms of relative dimension zero, which lets Tag 05FJ reduce the statement to a Noetherian
base. The substance of the proof is then a universal idempotent: by Zariski's main theorem the
source embeds as an open subscheme of a scheme finite over the base, a finite open subscheme of a
base change becomes open and closed there, hence is cut out by an idempotent of the coordinate
algebra, and Tag 0F3M provides a finitely presented algebra carrying a universal such idempotent.
Deleting the closed image of the part of the universal open subscheme falling outside the original
source yields `Y_univ`.

## References

* [Stacks Project, Tag 0F3N](https://stacks.math.columbia.edu/tag/0F3N)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TensorProduct Algebra.TensorProduct

universe u

namespace AlgebraicGeometry

/-- An open subscheme that is finite over a separated morphism is also closed. This is the
bridge from an open subset of a fibre product to an idempotent of its coordinate algebra. -/
private lemma isClopen_of_isFinite_opens {Z T : Scheme.{u}} (p : Z ⟶ T)
    [IsSeparated p] (U : Z.Opens) (hU : IsFinite (U.ι ≫ p)) : IsClopen (U : Set Z) := by
  refine ⟨?_, U.2⟩
  let : IsFinite (U.ι ≫ p) := hU
  let : IsFinite U.ι := IsFinite.of_comp U.ι p
  let : IsClosedImmersion U.ι :=
    (IsClosedImmersion.iff_isFinite_and_mono U.ι).2 ⟨inferInstance, inferInstance⟩
  rw [← Scheme.Opens.range_ι U]
  exact U.ι.isClosedMap.isClosed_range

/-- Finiteness over `T` of an open immersion with range `V`, composed with `q`, can be tested on
the inclusion of `V`. -/
private lemma isFinite_opens_ι_comp_iff {U Z T : Scheme.{u}} (f : U ⟶ Z) [IsOpenImmersion f]
    (V : Z.Opens) (hV : f.opensRange = V) (q : Z ⟶ T) :
    IsFinite (V.ι ≫ q) ↔ IsFinite (f ≫ q) := by
  subst hV
  have h : f ≫ q = f.isoOpensRange.hom ≫ f.opensRange.ι ≫ q := by simp
  have : MorphismProperty.RespectsIso (@IsFinite : MorphismProperty Scheme.{u}) :=
    MorphismProperty.RespectsIso.mk _ (by intros; infer_instance) (by intros; infer_instance)
  rw [h]
  exact (MorphismProperty.cancel_left_of_respectsIso (P := @IsFinite) _ _).symm

/-- A ring map whose comap is an open embedding and which becomes bijective after inverting any
element whose basic open lies in the image induces an open immersion on spectra. -/
private lemma isOpenImmersion_specMap_of_isOpenEmbedding_comap
    {A B : CommRingCat.{u}} (f : A ⟶ B)
    (hOpen : Topology.IsOpenEmbedding (PrimeSpectrum.comap f.hom))
    (hAway : ∀ g : A,
      (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum A)) ⊆
        Set.range (PrimeSpectrum.comap f.hom) →
          Function.Bijective (Localization.awayMap f.hom g)) :
    IsOpenImmersion (Spec.map f) := by
  apply IsOpenImmersion.of_forall_source_exists (Spec.map f) hOpen.injective
  intro q
  let p := PrimeSpectrum.comap f.hom q
  have hpRange : p ∈ Set.range (PrimeSpectrum.comap f.hom) := ⟨q, rfl⟩
  have hpOpen : IsOpen (Set.range (PrimeSpectrum.comap f.hom)) := hOpen.isOpen_range
  obtain ⟨_, ⟨g, rfl⟩, hpg, hsub⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.isOpen_iff.mp hpOpen p hpRange
  let U : (Spec B).Opens := PrimeSpectrum.basicOpen (f.hom g)
  let V : (Spec A).Opens := PrimeSpectrum.basicOpen g
  let iU : U.toScheme ⟶ Spec B := U.ι
  let iV : V.toScheme ⟶ Spec A := V.ι
  have hqU : q ∈ U := by
    change g ∉ Ideal.comap f.hom q.asIdeal
    exact (PrimeSpectrum.mem_basicOpen g p).mp hpg
  have hrange : Set.range (iU ≫ Spec.map f) ⊆ Set.range iV := by
    intro x hx
    obtain ⟨y, rfl⟩ := hx
    refine ⟨⟨(Spec.map f).base (iU.base y), ?_⟩, rfl⟩
    change iU.base y ∈ (Spec.map f) ⁻¹ᵁ V
    rw [SpecMap_preimage_basicOpen]
    exact y.2
  let j : U.toScheme ⟶ V.toScheme := IsOpenImmersion.lift iV (iU ≫ Spec.map f) hrange
  let ρ : CommRingCat.of (Localization.Away g) ⟶
      CommRingCat.of (Localization.Away (f.hom g)) :=
    CommRingCat.ofHom (Localization.awayMap f.hom g)
  let eRing : Localization.Away g ≃+* Localization.Away (f.hom g) :=
    RingEquiv.ofBijective ρ.hom (hAway g hsub)
  let eAway : CommRingCat.of (Localization.Away g) ≅
      CommRingCat.of (Localization.Away (f.hom g)) :=
    RingEquiv.toCommRingCatIso eRing
  let k : U.toScheme ⟶ V.toScheme :=
    (basicOpenIsoSpecAway (f.hom g)).hom ≫
      (Scheme.Spec.mapIso eAway.op).hom ≫
        (basicOpenIsoSpecAway g).inv
  have hki : k ≫ iV = iU ≫ Spec.map f := by
    change
      (basicOpenIsoSpecAway (f.hom g)).hom ≫
        (Scheme.Spec.mapIso eAway.op).hom ≫
          (basicOpenIsoSpecAway g).inv ≫
            Scheme.Opens.ι (X := Spec A) (PrimeSpectrum.basicOpen g) =
        Scheme.Opens.ι (X := Spec B) (PrimeSpectrum.basicOpen (f.hom g)) ≫ Spec.map f
    rw [← basicOpenIsoSpecAway_hom_SpecMap g]
    rw [Iso.inv_hom_id_assoc]
    rw [← basicOpenIsoSpecAway_hom_SpecMap (f.hom g)]
    change
      (basicOpenIsoSpecAway (f.hom g)).hom ≫
          ((Scheme.Spec.mapIso eAway.op).hom ≫
            Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away g)))) =
      (basicOpenIsoSpecAway (f.hom g)).hom ≫
          (Spec.map (CommRingCat.ofHom
            (algebraMap B (Localization.Away (f.hom g)))) ≫ Spec.map f)
    have htail :
        (Scheme.Spec.mapIso eAway.op).hom ≫
            Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away g))) =
          Spec.map (CommRingCat.ofHom
            (algebraMap B (Localization.Away (f.hom g)))) ≫ Spec.map f := by
      change Spec.map eAway.op.hom.unop ≫
          Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away g))) =
        Spec.map (CommRingCat.ofHom
          (algebraMap B (Localization.Away (f.hom g)))) ≫ Spec.map f
      rw [← Spec.map_comp, ← Spec.map_comp]
      apply congrArg Spec.map
      apply CommRingCat.hom_ext
      ext a
      change Localization.awayMap f.hom g (algebraMap A (Localization.Away g) a) =
        algebraMap B (Localization.Away (f.hom g)) (f.hom a)
      rw [Localization.awayMap, IsLocalization.Away.map, IsLocalization.map_eq]
    exact congrArg (fun t => (basicOpenIsoSpecAway (f.hom g)).hom ≫ t) htail
  have hjk : j = k := by
    apply (cancel_mono iV).1
    rw [IsOpenImmersion.lift_fac]
    exact hki.symm
  have hkIso : IsIso k := by dsimp [k]; infer_instance
  have hjIso : IsIso j := hjk ▸ hkIso
  refine ⟨U.toScheme, iU, inferInstance, ?_, ?_⟩
  · simpa only [iU, Scheme.Opens.opensRange_ι] using hqU
  · rw [← IsOpenImmersion.lift_fac iV (iU ≫ Spec.map f) hrange]
    infer_instance

/-- A quasi-compact locally quasi-finite morphism has fibres of dimension at most zero, the
empty fibres included. -/
private lemma fiberDimension_le_zero_of_locallyQuasiFinite {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyQuasiFinite f] [QuasiCompact f] (y : Y) :
    f.fiberDimension y ≤ (0 : WithBot ℕ∞) := by
  let : IsArtinianScheme (f.fiber y) := inferInstance
  let : DiscreteTopology (f.fiber y) :=
    (IsArtinianScheme.iff_isNoetherian_and_discreteTopology).mp ‹_› |>.2
  exact topologicalKrullDim_zero_of_discreteTopology _

/-- The fibres of a morphism locally of finite type are locally Noetherian, being of finite type
over a field. -/
private alias fiber_isLocallyNoetherian := isLocallyNoetherian_fiber_of_locallyOfFiniteType

/-- A morphism locally of finite type whose fibres all have dimension at most zero is locally
quasi-finite. This is the converse direction of Tag 0397 in the form needed here, where the
empty fibres are allowed. -/
private lemma locallyQuasiFinite_of_fiberDimension_le_zero {X Y : Scheme.{u}}
    (f : X ⟶ Y) [LocallyOfFiniteType f]
    (h : ∀ y, f.fiberDimension y ≤ (0 : WithBot ℕ∞)) :
    LocallyQuasiFinite f := by
  rw [locallyQuasiFinite_iff_isDiscrete_preimage_singleton]
  intro y
  let : IsLocallyNoetherian (f.fiber y) := fiber_isLocallyNoetherian f y
  let : IsLocallyArtinian (f.fiber y) :=
    IsLocallyArtinian.of_topologicalKrullDim_le_zero (h y)
  exact _root_.isDiscrete_iff_discreteTopology.mpr <|
    (f.fiberHomeo y).discreteTopology_iff.mp inferInstance

/-- The coordinate ring of the base of an affine finite-type model is Noetherian, being of finite
type over `ℤ`. -/
private lemma isNoetherianRing_base_of_finiteTypeAffineModel
    {P : MorphismProperty Scheme.{u}} {X S : Scheme.{u}} {f : X ⟶ S}
    (m : FiniteTypeAffineModel P f) : IsNoetherianRing Γ(m.S₀, ⊤) := by
  let : IsAffine m.S₀ := m.base_affine
  let : LocallyOfFiniteType (terminal.from m.S₀) := m.base_locallyOfFiniteType
  let e : Spec (.of (ULift.{u} ℤ)) ≅ ⊤_ Scheme.{u} :=
    specULiftZIsTerminal.uniqueUpToIso terminalIsTerminal
  let g : m.S₀ ⟶ Spec (.of (ULift.{u} ℤ)) := terminal.from m.S₀ ≫ e.inv
  let : LocallyOfFiniteType g := by dsimp [g]; infer_instance
  let : IsNoetherianRing (ULift.{u} ℤ) :=
    isNoetherianRing_of_ringEquiv ℤ (ULift.ringEquiv (R := ℤ)).symm
  let : IsLocallyNoetherian m.S₀ := LocallyOfFiniteType.isLocallyNoetherian g
  exact IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top _⟩

/-- Zariski's main theorem for a quasi-finite algebra over a Noetherian ring, in the form of a
finite and finitely presented subalgebra whose spectrum receives the spectrum of the given algebra
as an open subscheme. -/
@[ega "IV 8.12.6" "special case"]
private theorem exists_finite_finitePresentation_subalgebra
    (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    [IsNoetherianRing A] [Algebra.FiniteType A B] [Algebra.QuasiFinite A B] :
    ∃ (C : Subalgebra A B), Module.Finite A C ∧
      Algebra.FinitePresentation A C ∧
      Topology.IsOpenEmbedding (PrimeSpectrum.comap C.val.toRingHom) ∧
      ∀ g : C,
        (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum C)) ⊆
          Set.range (PrimeSpectrum.comap C.val.toRingHom) →
            Function.Bijective (Localization.awayMap C.val.toRingHom g) := by
  obtain ⟨C, _, hCfin, hopen, haway⟩ :=
    quasiFinite_exists_finite_subalgebra (R := A) (S := B)
  let : Algebra A C := inferInstance
  let : Module.Finite A C := hCfin
  have hCfp : Module.FinitePresentation A C := Module.finitePresentation_of_finite A C
  exact ⟨C, hCfin,
    (Module.FinitePresentation.iff_finitePresentation_of_finite A C).mp hCfp, hopen, haway⟩

/-- **Stacks Project, Tag 0F3N.** A quasi-finite morphism of finite presentation between affine
schemes admits a base change of finite presentation carrying a universal finite open subscheme:
every open subscheme of a base change along a morphism of affine schemes that is finite over the
new base is the inverse image of this one. -/
@[stacks 0F3N]
theorem exists_universal_finite_open_subscheme
    {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (f : X ⟶ Y)
    [LocallyQuasiFinite f] (hfp : FinitePresentation f) :
    ∃ (Yuniv : Scheme.{u}) (g : Yuniv ⟶ Y)
      (Uuniv : (pullback f g).Opens),
      FinitePresentation g ∧
        IsFinite (Uuniv.ι ≫ pullback.snd f g) ∧
      ∀ (Y' : Scheme.{u}) [IsAffine Y'] (g' : Y' ⟶ Y)
          (U' : (pullback f g').Opens),
          IsFinite (U'.ι ≫ pullback.snd f g') →
            ∃ (h : Y' ⟶ Yuniv) (hh : h ≫ g = g'),
              (pullback.lift (pullback.fst f g')
                (pullback.snd f g' ≫ h)
                (by rw [Category.assoc, hh]; exact pullback.condition)) ⁻¹ᵁ Uuniv = U' := by
  classical
  let : LocallyOfFinitePresentation f := hfp.locallyOfFinitePresentation
  let : QuasiCompact f := hfp.quasiCompact
  have hdim : ∀ y : Y, f.fiberDimension y ≤ (0 : WithBot ℕ∞) :=
    fiberDimension_le_zero_of_locallyQuasiFinite f
  obtain ⟨m, hm⟩ := exists_finiteTypeAffineModel_fiberDimension_le f hfp 0 hdim
  let : LocallyOfFiniteType m.f₀ := m.locallyOfFiniteType
  let : QuasiCompact m.f₀ := m.quasiCompact
  have hlqf : LocallyQuasiFinite m.f₀ :=
    locallyQuasiFinite_of_fiberDimension_le_zero m.f₀ hm
  let : IsAffine m.S₀ := m.base_affine
  let : IsAffine m.X₀ := m.source_affine
  let A := Γ(m.S₀, ⊤)
  let B := Γ(m.X₀, ⊤)
  let : Algebra A B := m.f₀.appTop.hom.toAlgebra
  let : IsNoetherianRing A := isNoetherianRing_base_of_finiteTypeAffineModel m
  have hftRing : (algebraMap A B).FiniteType := by
    change (m.f₀.appTop).hom.FiniteType
    exact HasRingHomProperty.appTop (P := @LocallyOfFiniteType) m.f₀ inferInstance
  let : Algebra.FiniteType A B := (RingHom.finiteType_algebraMap).mp hftRing
  have hqfRing : RingHom.QuasiFinite (algebraMap A B) := by
    change RingHom.QuasiFinite (m.f₀.appTop).hom
    exact (HasRingHomProperty.iff_of_isAffine
      (P := @LocallyQuasiFinite) (f := m.f₀)).mp hlqf
  let : Algebra.QuasiFinite A B :=
    (RingHom.quasiFinite_algebraMap (R := A) (S := B)).mp hqfRing
  obtain ⟨C, hCfinite, hCfp, hCopen, hCaway⟩ :=
    exists_finite_finitePresentation_subalgebra A B
  let : Algebra A C := inferInstance
  let : Module.Finite A C := hCfinite
  let : Algebra.FinitePresentation A C := hCfp
  obtain ⟨Auniv, _, _, hAunivFp, eUniv, hUnivIdem, hRepresent⟩ :=
    Algebra.exists_finitePresentation_algebra_universal_for_idempotents.{u, u, u} A C
  let : Algebra.FiniteType A Auniv := inferInstance
  let : IsNoetherianRing Auniv := Algebra.FiniteType.isNoetherianRing A Auniv
  let ιCB : CommRingCat.of C ⟶ CommRingCat.of B := CommRingCat.ofHom C.val.toRingHom
  have hιCB : IsOpenImmersion (Spec.map ιCB) :=
    isOpenImmersion_specMap_of_isOpenEmbedding_comap ιCB hCopen hCaway
  let SA : Scheme.{u} := Spec (CommRingCat.of A)
  let SC : Scheme.{u} := Spec (CommRingCat.of C)
  let SB : Scheme.{u} := Spec (CommRingCat.of B)
  let fCA : SC ⟶ SA := Spec.map (CommRingCat.ofHom (algebraMap A C))
  let fBA : SB ⟶ SA := Spec.map (CommRingCat.ofHom (algebraMap A B))
  have hCBcomp : Spec.map ιCB ≫ fCA = fBA := by
    rw [← Spec.map_comp]
    change Spec.map (CommRingCat.ofHom (algebraMap A C) ≫ ιCB) =
      Spec.map (CommRingCat.ofHom (algebraMap A B))
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    ext b
    rfl
  let fUA : Spec (CommRingCat.of Auniv) ⟶ SA :=
    Spec.map (CommRingCat.ofHom (algebraMap A Auniv))
  let Zbar := pullback fCA fUA
  let Qbar := pullback (Spec.map ιCB) (pullback.fst fCA fUA)
  let iCBbar : Qbar ⟶ Zbar := pullback.snd (Spec.map ιCB) (pullback.fst fCA fUA)
  let : IsOpenImmersion (Spec.map ιCB) := hιCB
  have hCBbar : IsOpenImmersion iCBbar := by infer_instance
  let eZbar : Zbar ≅ Spec (CommRingCat.of (C ⊗[A] Auniv)) :=
    pullbackSpecIso A C Auniv
  let Vbar : Zbar.Opens := eZbar.hom ⁻¹ᵁ PrimeSpectrum.basicOpen eUniv
  have hVbarClopen : IsClopen (Vbar : Set Zbar) := by
    have hBasic : IsClopen
        (PrimeSpectrum.basicOpen eUniv).1 :=
      PrimeSpectrum.isClopen_iff.mpr ⟨eUniv, hUnivIdem, rfl⟩
    exact hBasic.preimage (Scheme.homeoOfIso eZbar).continuous
  let fZbar : Zbar ⟶ Spec (CommRingCat.of Auniv) := pullback.snd fCA fUA
  let : IsFinite fCA :=
    (IsFinite.SpecMap_iff (CommRingCat.ofHom (algebraMap A C))).2
      (RingHom.finite_algebraMap.mpr hCfinite)
  let badZ : Set Zbar :=
    (Vbar : Set Zbar) ∩ (iCBbar.opensRange : Set Zbar)ᶜ
  have hbadZ : IsClosed badZ :=
    hVbarClopen.1.inter iCBbar.opensRange.2.isClosed_compl
  let bad : Set (Spec (CommRingCat.of Auniv)) := fZbar.base '' badZ
  have hbad : IsClosed bad := fZbar.isClosedMap badZ hbadZ
  let W : (Spec (CommRingCat.of Auniv)).Opens := ⟨badᶜ, hbad.isOpen_compl⟩
  let gW : W.toScheme ⟶ SA := W.ι ≫ fUA
  let : TopologicalSpace.NoetherianSpace W.toScheme :=
    Topology.IsInducing.subtypeVal.noetherianSpace
  have hfpUniv : (algebraMap A Auniv).FinitePresentation :=
    (RingHom.finitePresentation_algebraMap).mpr hAunivFp
  let : LocallyOfFinitePresentation fUA :=
    (LocallyOfFinitePresentation.SpecMap_iff (CommRingCat.ofHom (algebraMap A Auniv))).2
      hfpUniv
  let : LocallyOfFinitePresentation W.ι := inferInstance
  let : QuasiCompact W.ι := inferInstance
  let : QuasiSeparated W.ι := inferInstance
  let : QuasiCompact fUA := inferInstance
  let : QuasiSeparated fUA := inferInstance
  have hfpW : FinitePresentation gW := ⟨inferInstance, inferInstance, inferInstance⟩
  let ZW := pullback fCA gW
  let baseZW : ZW ⟶ Zbar :=
    pullback.map fCA gW fCA fUA (𝟙 _) W.ι (𝟙 _) (by simp) (by simp [gW])
  let QW := pullback (Spec.map ιCB) (pullback.fst fCA gW)
  let jW : QW ⟶ ZW := pullback.snd (Spec.map ιCB) (pullback.fst fCA gW)
  let pZW : ZW ⟶ W.toScheme := pullback.snd fCA gW
  have hBaseZWFst : baseZW ≫ pullback.fst fCA fUA = pullback.fst fCA gW := by
    dsimp [baseZW, pullback.map]
    rw [pullback.lift_fst]
    simp
  have hBaseZWSnd : baseZW ≫ fZbar = pZW ≫ W.ι := by
    dsimp [baseZW, fZbar, pZW, pullback.map]
    rw [pullback.lift_snd]
  let VbarW : ZW.Opens := baseZW ⁻¹ᵁ Vbar
  let Uuniv : QW.Opens := jW ⁻¹ᵁ VbarW
  have hVbarW_le : VbarW ≤ jW.opensRange := by
    change (VbarW : Set ZW) ⊆ jW.opensRange
    intro z hz
    change baseZW z ∈ Vbar at hz
    have hzModel : z ∈ jW.opensRange := by
      by_contra hznotModel
      rw [Scheme.Hom.opensRange_pullbackSnd] at hznotModel
      change (pullback.fst fCA gW) z ∉ (Spec.map ιCB).opensRange at hznotModel
      have hzoutBar : baseZW z ∉ iCBbar.opensRange := by
        rw [Scheme.Hom.opensRange_pullbackSnd]
        intro hzInBar
        change (pullback.fst fCA fUA) (baseZW z) ∈
          (Spec.map ιCB).opensRange at hzInBar
        have hproj : (pullback.fst fCA fUA) (baseZW z) =
            (pullback.fst fCA gW) z :=
          congrArg (fun h => h z) hBaseZWFst
        rw [hproj] at hzInBar
        exact hznotModel hzInBar
      have hzbad : baseZW z ∈ badZ := ⟨hz, hzoutBar⟩
      have hbadMem : fZbar (baseZW z) ∈ bad := ⟨baseZW z, hzbad, rfl⟩
      let w := (pullback.snd fCA gW) z
      have hw : W.ι w ∈ W := by
        simpa only [Scheme.Opens.opensRange_ι] using
          (show W.ι w ∈ W.ι.opensRange from ⟨w, rfl⟩)
      have hproj : fZbar (baseZW z) = W.ι w := by
        simpa [w, pZW] using congrArg (fun h => h z) hBaseZWSnd
      rw [hproj] at hbadMem
      exact hw hbadMem
    exact hzModel
  have hVbarWClopen : IsClopen (VbarW : Set ZW) :=
    hVbarClopen.preimage baseZW.continuous
  have hVbarWClosedRange : IsClosed (Set.range VbarW.ι) := by
    rw [Scheme.Opens.range_ι]
    exact hVbarWClopen.1
  let : IsClosedImmersion VbarW.ι :=
    IsClosedImmersion.of_isPreimmersion VbarW.ι hVbarWClosedRange
  have hRangeOpen : (Uuniv.ι ≫ jW).opensRange = VbarW := by
    rw [Scheme.Hom.opensRange_comp, Scheme.Opens.opensRange_ι,
      Scheme.Hom.image_preimage_eq_opensRange_inf, inf_eq_right.mpr hVbarW_le]
  have hUfiniteOverW : IsFinite (Uuniv.ι ≫ jW ≫ pZW) := by
    rw [← Category.assoc]
    exact (isFinite_opens_ι_comp_iff _ VbarW hRangeOpen pZW).1 inferInstance
  let eS0 : m.S₀ ≅ SA := Scheme.isoSpec m.S₀
  let wS0 : W.toScheme ⟶ m.S₀ := gW ≫ eS0.inv
  let Yuniv := pullback wS0 m.toBase
  let g : Yuniv ⟶ Y := pullback.snd wS0 m.toBase
  have hwS0fp : FinitePresentation wS0 := by
    let : LocallyOfFinitePresentation gW := hfpW.1
    let : QuasiCompact gW := hfpW.2.1
    let : QuasiSeparated gW := hfpW.2.2
    let : LocallyOfFinitePresentation eS0.inv := inferInstance
    let : QuasiCompact eS0.inv := inferInstance
    let : QuasiSeparated eS0.inv := inferInstance
    dsimp [wS0]
    exact ⟨inferInstance, inferInstance, inferInstance⟩
  have hgfp : FinitePresentation g := by
    let : LocallyOfFinitePresentation wS0 := hwS0fp.1
    let : QuasiCompact wS0 := hwS0fp.2.1
    let : QuasiSeparated wS0 := hwS0fp.2.2
    refine ⟨?_, ?_, ?_⟩
    · let : MorphismProperty.IsStableUnderBaseChangeAlong
          (P := @LocallyOfFinitePresentation) m.toBase :=
        ⟨fun pb h => locallyOfFinitePresentation_isStableUnderBaseChange.of_isPullback pb h⟩
      exact MorphismProperty.pullback_snd wS0 m.toBase inferInstance
    · infer_instance
    · infer_instance
  let xToX0 : pullback f g ⟶ m.X₀ := pullback.fst f g ≫ m.toSource
  let yToS0 : Yuniv ⟶ m.S₀ := g ≫ m.toBase
  have hactualModel : IsPullback xToX0 (pullback.snd f g) m.f₀ yToS0 :=
    (IsPullback.of_hasPullback f g).paste_horiz m.isPullback
  let eX0 : m.X₀ ≅ SB := Scheme.isoSpec m.X₀
  have hmodelComm : eX0.hom ≫ fBA = m.f₀ ≫ eS0.hom := by
    rw [← Scheme.isoSpec_hom_naturality m.f₀]
    rfl
  let yW : Yuniv ⟶ W.toScheme := pullback.fst wS0 m.toBase
  let gY : Yuniv ⟶ SA := yW ≫ gW
  have hyW : yToS0 ≫ eS0.hom = gY := by
    calc
      yToS0 ≫ eS0.hom = g ≫ m.toBase ≫ eS0.hom := rfl
      _ = yW ≫ wS0 ≫ eS0.hom := by
        change pullback.snd wS0 m.toBase ≫ m.toBase ≫ eS0.hom = _
        rw [← pullback.condition_assoc]
      _ = gY := by simp [gY, wS0, yW, Category.assoc]
  let fCBA : SB ⟶ SA := Spec.map ιCB ≫ fCA
  have hmodelComm' : m.f₀ ≫ eS0.hom = eX0.hom ≫ fCBA := by
    rw [← hmodelComm, ← hCBcomp]
  have hactualC : IsPullback (xToX0 ≫ eX0.hom) (pullback.snd f g)
      fCBA gY := by
    apply hactualModel.of_iso (Iso.refl _) eX0 (Iso.refl _) eS0
    · simp
    · simp
    · exact hmodelComm'
    · exact hyW
  let ZBW := pullback fCBA gW
  let pBW : ZBW ⟶ W.toScheme := pullback.snd fCBA gW
  let eQW : QW ≅ ZBW :=
    pullbackRightPullbackFstIso fCA gW (Spec.map ιCB)
  let eAssoc : pullback pBW yW ≅ pullback fCBA gY :=
    pullbackLeftPullbackSndIso fCBA gW yW
  let eActual : pullback f g ≅ pullback pBW yW :=
    hactualC.isoPullback ≪≫ eAssoc.symm
  let qWtoW : QW ⟶ W.toScheme := jW ≫ pZW
  let PBQW := pullback qWtoW yW
  let PBopen := pullback Uuniv.ι (pullback.fst qWtoW yW)
  let iPBopen : PBopen ⟶ PBQW :=
    pullback.snd Uuniv.ι (pullback.fst qWtoW yW)
  let UQbase : PBQW.Opens := iPBopen.opensRange
  let uToW : Uuniv.toScheme ⟶ W.toScheme := Uuniv.ι ≫ qWtoW
  let eAssocU : PBopen ≅ pullback uToW yW :=
    pullbackRightPullbackFstIso qWtoW yW Uuniv.ι
  have hOpenToY : iPBopen ≫ pullback.snd qWtoW yW =
      eAssocU.hom ≫ pullback.snd uToW yW := by
    simp [eAssocU, uToW, PBopen, iPBopen]
  have hfinitePull : IsFinite (pullback.snd uToW yW) := by
    let : IsFinite uToW := by
      change IsFinite (Uuniv.ι ≫ jW ≫ pZW)
      exact hUfiniteOverW
    let : MorphismProperty.IsStableUnderBaseChangeAlong
        (P := @IsFinite) yW :=
      ⟨fun pb h =>
        (inferInstance : MorphismProperty.IsStableUnderBaseChange @IsFinite)
          |>.of_isPullback pb h⟩
    exact MorphismProperty.pullback_snd uToW yW inferInstance
  have hfiniteUQbase : IsFinite (UQbase.ι ≫ pullback.snd qWtoW yW) := by
    refine (isFinite_opens_ι_comp_iff iPBopen UQbase rfl _).2 ?_
    rw [hOpenToY]
    infer_instance
  have hQWoverW : qWtoW = eQW.hom ≫ pBW := by
    change jW ≫ pZW =
      (pullbackRightPullbackFstIso fCA gW (Spec.map ιCB)).hom ≫
        pullback.snd fCBA gW
    exact (pullbackRightPullbackFstIso_hom_snd fCA gW (Spec.map ιCB)).symm
  let eQBaseHom : PBQW ⟶ pullback pBW yW :=
    pullback.map qWtoW yW pBW yW eQW.hom (𝟙 Yuniv) (𝟙 W.toScheme)
      hQWoverW (by simp)
  let : IsIso eQW.hom := by dsimp [eQW]; infer_instance
  let : IsIso (𝟙 Yuniv) := inferInstance
  let : IsIso (𝟙 W.toScheme) := inferInstance
  have : IsIso eQBaseHom := by
    apply pullback.map_isIso
  let eQBase : PBQW ≅ pullback pBW yW := asIso eQBaseHom
  let eActualToQ : pullback f g ≅ PBQW := eActual ≪≫ eQBase.symm
  let Uactual : (pullback f g).Opens := eActualToQ.hom ⁻¹ᵁ UQbase
  have hQBaseSnd : eQBaseHom ≫ pullback.snd pBW yW =
      pullback.snd qWtoW yW := by
    change pullback.lift (pullback.fst qWtoW yW ≫ eQW.hom)
      (pullback.snd qWtoW yW ≫ 𝟙 Yuniv) _ ≫ pullback.snd pBW yW = _
    rw [pullback.lift_snd]
    simp
  have hQBaseSnd' : eQBase.symm.hom ≫ pullback.snd qWtoW yW =
      pullback.snd pBW yW := by
    calc
      eQBase.symm.hom ≫ pullback.snd qWtoW yW =
          eQBase.symm.hom ≫ (eQBaseHom ≫ pullback.snd pBW yW) := by rw [hQBaseSnd]
      _ = pullback.snd pBW yW := by simp [eQBase]
  have hActualOver : eActualToQ.hom ≫ pullback.snd qWtoW yW =
      pullback.snd f g := by
    calc
      eActualToQ.hom ≫ pullback.snd qWtoW yW =
          eActual.hom ≫ pullback.snd pBW yW := by
        dsimp [eActualToQ]
        exact congrArg (fun k => eActual.hom ≫ k) hQBaseSnd'
      _ = hactualC.isoPullback.hom ≫ pullback.snd fCBA gY := by
        dsimp [eActual]
        rw [Category.assoc, pullbackLeftPullbackSndIso_inv_snd_snd]
      _ = pullback.snd f g := IsPullback.isoPullback_hom_snd hactualC
  have hRangeOpenActual : (Uactual.ι ≫ eActualToQ.hom).opensRange = UQbase := by
    rw [Scheme.Hom.opensRange_comp, Scheme.Opens.opensRange_ι,
      Scheme.Hom.image_preimage_eq_opensRange_inf]
    rw [Scheme.Hom.opensRange_of_isIso, top_inf_eq]
  have hUactualFinite : IsFinite (Uactual.ι ≫ pullback.snd f g) := by
    rw [← hActualOver, ← Category.assoc]
    exact (isFinite_opens_ι_comp_iff _ UQbase hRangeOpenActual _).1 hfiniteUQbase
  refine ⟨Yuniv, g, Uactual, hgfp, hUactualFinite, ?_⟩
  intro Y' _ g' U' hU'finite
  let gS0' : Y' ⟶ m.S₀ := g' ≫ m.toBase
  let xToX0' : pullback f g' ⟶ m.X₀ := pullback.fst f g' ≫ m.toSource
  have hModelP' : IsPullback xToX0' (pullback.snd f g') m.f₀ gS0' :=
    (IsPullback.of_hasPullback f g').paste_horiz m.isPullback
  let A' := Γ(Y', ⊤)
  let : Algebra (↑A) A' := (gS0'.appTop).hom.toAlgebra
  let gA' : Spec (CommRingCat.of A') ⟶ SA :=
    Spec.map (CommRingCat.ofHom (algebraMap (↑A) A'))
  let eY' : Y' ≅ Spec (CommRingCat.of A') := Scheme.isoSpec Y'
  have hBaseComm : eY'.hom ≫ gA' = gS0' ≫ eS0.hom := by
    rw [← Scheme.isoSpec_hom_naturality gS0']
    rfl
  have hModelPSpec : IsPullback (xToX0' ≫ eX0.hom)
      (pullback.snd f g' ≫ eY'.hom) fCBA gA' := by
    apply hModelP'.of_iso (Iso.refl _) eX0 eY' eS0
    · simp
    · rfl
    · exact hmodelComm'
    · exact hBaseComm.symm
  let ePmodel' : pullback f g' ≅ pullback fCBA gA' := hModelPSpec.isoPullback
  let ZB' := pullback fCBA gA'
  let ZC' := pullback fCA gA'
  let Q' := pullback (Spec.map ιCB) (pullback.fst fCA gA')
  let j' : Q' ⟶ ZC' := pullback.snd (Spec.map ιCB) (pullback.fst fCA gA')
  have hj' : IsOpenImmersion j' := by infer_instance
  let eQB : Q' ≅ pullback fCBA gA' :=
    pullbackRightPullbackFstIso fCA gA' (Spec.map ιCB)
  let kBtoC : pullback fCBA gA' ⟶ ZC' := eQB.inv ≫ j'
  have hkBtoC : IsOpenImmersion kBtoC := by infer_instance
  let Umodel' : (pullback fCBA gA').Opens := ePmodel'.hom ''ᵁ U'
  let UC' : ZC'.Opens := kBtoC ''ᵁ Umodel'
  let qB' : pullback fCBA gA' ⟶ Spec (CommRingCat.of A') :=
    pullback.snd fCBA gA'
  let qC' : ZC' ⟶ Spec (CommRingCat.of A') := pullback.snd fCA gA'
  have hBtoCbase : kBtoC ≫ qC' = qB' := by
    calc
      kBtoC ≫ qC' = eQB.inv ≫ (j' ≫ qC') := rfl
      _ = eQB.inv ≫ (eQB.hom ≫ qB') := by
        rw [← pullbackRightPullbackFstIso_hom_snd fCA gA' (Spec.map ιCB)]
      _ = pullback.snd fCBA gA' := by simp [qB']
  have hRangeOpenModel' : (U'.ι ≫ ePmodel'.hom).opensRange = Umodel' := by
    rw [Scheme.Hom.opensRange_comp, Scheme.Opens.opensRange_ι]
  have hQMap' : ePmodel'.hom ≫ qB' =
      pullback.snd f g' ≫ eY'.hom :=
    IsPullback.isoPullback_hom_snd hModelPSpec
  have hUmodelFinite : IsFinite (Umodel'.ι ≫ qB') := by
    refine (isFinite_opens_ι_comp_iff (U'.ι ≫ ePmodel'.hom) Umodel' hRangeOpenModel' qB').2 ?_
    rw [Category.assoc, hQMap', ← Category.assoc]
    let : IsFinite (U'.ι ≫ pullback.snd f g') := hU'finite
    infer_instance
  have hUCfinite : IsFinite (UC'.ι ≫ qC') := by
    refine (isFinite_opens_ι_comp_iff (Umodel'.ι ≫ kBtoC) UC' ?_ qC').2 ?_
    · rw [Scheme.Hom.opensRange_comp, Scheme.Opens.opensRange_ι]
    · rw [Category.assoc, hBtoCbase]
      exact hUmodelFinite
  let : IsSeparated qC' := inferInstance
  have hUCclopen : IsClopen (UC' : Set ZC') :=
    isClopen_of_isFinite_opens qC' UC' hUCfinite
  let eZ' : ZC' ≅ Spec (CommRingCat.of (C ⊗[A] A')) :=
    pullbackSpecIso A C A'
  let V' : (Spec (CommRingCat.of (C ⊗[A] A'))).Opens := eZ'.inv ⁻¹ᵁ UC'
  have hV'clopen : IsClopen (V' : Set (Spec (CommRingCat.of (C ⊗[A] A')))) :=
    hUCclopen.preimage (Scheme.homeoOfIso eZ').symm.continuous
  obtain ⟨e', he', hEq'⟩ := PrimeSpectrum.isClopen_iff.mp hV'clopen
  obtain ⟨φAlg, hRepresentIdem⟩ := hRepresent (↑A') e' he'
  let φ : Spec (CommRingCat.of (↑A')) ⟶ Spec (CommRingCat.of Auniv) :=
    Spec.map (CommRingCat.ofHom φAlg.toRingHom)
  have hφbase : φ ≫ fUA = gA' := by
    rw [← Spec.map_comp]
    apply congrArg Spec.map
    ext a
    exact φAlg.commutes a
  let tAlg : C ⊗[A] Auniv →ₐ[A] C ⊗[A] (↑A') :=
    Algebra.TensorProduct.map (AlgHom.id A C) φAlg
  let tRing : CommRingCat.of (C ⊗[A] Auniv) ⟶
      CommRingCat.of (C ⊗[A] (↑A')) := CommRingCat.ofHom tAlg.toRingHom
  let incU : CommRingCat.of Auniv ⟶ CommRingCat.of (C ⊗[A] Auniv) :=
    CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom
  let incA' : CommRingCat.of (↑A') ⟶ CommRingCat.of (C ⊗[A] (↑A')) :=
    CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom
  have hInc : incU ≫ tRing = CommRingCat.ofHom φAlg.toRingHom ≫ incA' := by
    apply CommRingCat.hom_ext
    ext a
    simp [incU, incA', tRing, tAlg, Algebra.TensorProduct.includeRight_apply]
  let qScheme : ZC' ⟶ Zbar := eZ'.hom ≫ Spec.map tRing ≫ eZbar.inv
  have hqSchemeBase : qScheme ≫ fZbar = qC' ≫ φ := by
    dsimp [qScheme, fZbar, qC', eZ', eZbar]
    rw [Category.assoc, Category.assoc, pullbackSpecIso_inv_snd, ← Spec.map_comp]
    change eZ'.hom ≫ Spec.map (incU ≫ tRing) = qC' ≫ φ
    rw [hInc, Spec.map_comp]
    change eZ'.hom ≫ (Spec.map incA' ≫ φ) = qC' ≫ φ
    rw [← Category.assoc]
    change ((pullbackSpecIso A C A').hom ≫
      Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom)) ≫ φ = _
    exact congrArg (fun morphism => morphism ≫ φ) (pullbackSpecIso_hom_snd A C A')
  have hOpenQ : qScheme ⁻¹ᵁ Vbar = UC' := by
    have hBasic : (Spec.map tRing) ⁻¹ᵁ
        (PrimeSpectrum.basicOpen eUniv) = PrimeSpectrum.basicOpen (tAlg eUniv) := by
      rw [SpecMap_preimage_basicOpen]
      rfl
    have hRepOpen : PrimeSpectrum.basicOpen (tAlg eUniv) =
        PrimeSpectrum.basicOpen e' := by rw [hRepresentIdem]
    have hV'open : V' = PrimeSpectrum.basicOpen e' :=
      TopologicalSpace.Opens.ext hEq'
    have hUCopen : UC' = eZ'.hom ⁻¹ᵁ PrimeSpectrum.basicOpen e' := by
      have hhV := congrArg (fun U => eZ'.hom ⁻¹ᵁ U) hV'open
      rw [show V' = eZ'.inv ⁻¹ᵁ UC' from rfl,
        ← Scheme.Hom.comp_preimage, Iso.hom_inv_id,
        Scheme.Hom.id_preimage] at hhV
      exact hhV
    rw [hUCopen]
    ext z
    change eZbar.hom (eZbar.inv ((Spec.map tRing) (eZ'.hom z))) ∈
      PrimeSpectrum.basicOpen eUniv ↔ eZ'.hom z ∈ PrimeSpectrum.basicOpen e'
    rw [Scheme.inv_hom_apply]
    exact SetLike.ext_iff.mp (hBasic.trans hRepOpen) (eZ'.hom z)
  let incCU : CommRingCat.of C ⟶ CommRingCat.of (C ⊗[A] Auniv) :=
    CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom
  let incC' : CommRingCat.of C ⟶ CommRingCat.of (C ⊗[A] (↑A')) :=
    CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom
  have hIncC : incCU ≫ tRing = incC' := by
    apply CommRingCat.hom_ext
    ext c
    simp [incCU, incC', tRing, tAlg, Algebra.TensorProduct.includeLeftRingHom]
  have hqSchemeFst : qScheme ≫ pullback.fst fCA fUA = pullback.fst fCA gA' := by
    dsimp [qScheme, eZ', eZbar]
    rw [Category.assoc, Category.assoc, pullbackSpecIso_inv_fst,
      ← Spec.map_comp, hIncC, pullbackSpecIso_hom_fst]
  have hqPullback : IsPullback qScheme qC' fZbar φ := by
    have hWhole : IsPullback (qScheme ≫ pullback.fst fCA fUA) qC'
        fCA (φ ≫ fUA) := by
      rw [hqSchemeFst, hφbase]
      exact IsPullback.of_hasPullback fCA gA'
    exact hWhole.of_right hqSchemeBase (IsPullback.of_hasPullback fCA fUA)
  have hkRange : kBtoC.opensRange =
      (pullback.fst fCA gA') ⁻¹ᵁ (Spec.map ιCB).opensRange := by
    dsimp [kBtoC, j']
    rw [Scheme.Hom.opensRange_comp, Scheme.Hom.opensRange_of_isIso]
    rw [Scheme.Hom.image_top_eq_opensRange, Scheme.Hom.opensRange_pullbackSnd]
  have hRangeQ : qScheme ⁻¹ᵁ iCBbar.opensRange = kBtoC.opensRange := by
    rw [hkRange]
    dsimp [iCBbar]
    rw [Scheme.Hom.opensRange_pullbackSnd, ← Scheme.Hom.comp_preimage, hqSchemeFst]
  have hbadPreimage : qScheme.base ⁻¹' badZ = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro z hz
    have hzU : z ∈ UC' := by
      rw [← hOpenQ]
      exact hz.1
    have hzRange : z ∈ kBtoC.opensRange :=
      Scheme.Hom.image_le_opensRange kBtoC Umodel' hzU
    have hzRangeQ : qScheme z ∈ iCBbar.opensRange := by
      change z ∈ qScheme ⁻¹ᵁ iCBbar.opensRange
      rw [hRangeQ]
      exact hzRange
    exact hz.2 hzRangeQ
  have hφRange : Set.range φ ⊆ Set.range W.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨y, rfl⟩
    change φ y ∉ bad
    have himage := Scheme.image_preimage_eq_of_isPullback hqPullback badZ
    rw [hbadPreimage, Set.image_empty] at himage
    have hy : y ∉ φ.base ⁻¹' bad := by
      rw [← himage]
      exact Set.notMem_empty y
    exact hy
  let φW : Spec (CommRingCat.of (↑A')) ⟶ W.toScheme :=
    IsOpenImmersion.lift W.ι φ hφRange
  have hφW : φW ≫ W.ι = φ := IsOpenImmersion.lift_fac W.ι φ hφRange
  let hW : Y' ⟶ W.toScheme := eY'.hom ≫ φW
  have hhW : hW ≫ wS0 = g' ≫ m.toBase := by
    apply (cancel_mono eS0.hom).mp
    simp only [hW, wS0, gW, Category.assoc, Iso.inv_hom_id,
      Category.comp_id]
    rw [← Category.assoc φW W.ι fUA, hφW, hφbase]
    exact hBaseComm
  let h : Y' ⟶ Yuniv := pullback.lift hW g' hhW
  have hh : h ≫ g = g' := pullback.lift_snd _ _ _
  refine ⟨h, hh, ?_⟩
  let liftActual : pullback f g' ⟶ pullback f g :=
    pullback.lift (pullback.fst f g') (pullback.snd f g' ≫ h)
      (by rw [Category.assoc, hh]; exact pullback.condition)
  have hUQbase : UQbase = (pullback.fst qWtoW yW) ⁻¹ᵁ Uuniv := by
    dsimp [UQbase, iPBopen]
    rw [Scheme.Hom.opensRange_pullbackSnd, Scheme.Opens.opensRange_ι]
  let universalEnvelopeMap : pullback f g ⟶ Zbar :=
    eActualToQ.hom ≫ pullback.fst qWtoW yW ≫ jW ≫ baseZW
  have hUactualOpen : Uactual = universalEnvelopeMap ⁻¹ᵁ Vbar := by
    dsimp [Uactual, universalEnvelopeMap]
    rw [hUQbase]
  have hQBaseFst : eQBaseHom ≫ pullback.fst pBW yW =
      pullback.fst qWtoW yW ≫ eQW.hom := by
    dsimp [eQBaseHom, pullback.map]
    rw [pullback.lift_fst]
  have hQBaseInvFst : eQBase.inv ≫ pullback.fst qWtoW yW ≫ eQW.hom =
      pullback.fst pBW yW := by
    rw [← hQBaseFst]
    change eQBase.inv ≫ eQBase.hom ≫ pullback.fst pBW yW = _
    simp
  have hQWfst : jW ≫ pullback.fst fCA gW =
      eQW.hom ≫ pullback.fst fCBA gW ≫ Spec.map ιCB := by
    dsimp [jW, eQW]
    rw [pullbackRightPullbackFstIso_hom_fst_assoc]
    exact (pullback.condition (f := Spec.map ιCB) (g := pullback.fst fCA gW)).symm
  have hUniversalFst : universalEnvelopeMap ≫ pullback.fst fCA fUA =
      xToX0 ≫ eX0.hom ≫ Spec.map ιCB := by
    dsimp [universalEnvelopeMap]
    simp only [Category.assoc]
    rw [hBaseZWFst, hQWfst]
    change eActual.hom ≫ eQBase.inv ≫ pullback.fst qWtoW yW ≫
      eQW.hom ≫ pullback.fst fCBA gW ≫ Spec.map ιCB = _
    rw [reassoc_of% hQBaseInvFst]
    dsimp [eActual, eAssoc]
    simp only [Category.assoc]
    rw [pullbackLeftPullbackSndIso_inv_fst_assoc,
      IsPullback.isoPullback_hom_fst_assoc]
    exact Category.assoc _ _ _
  have hUniversalSnd : universalEnvelopeMap ≫ fZbar =
      pullback.snd f g ≫ yW ≫ W.ι := by
    dsimp [universalEnvelopeMap]
    simp only [Category.assoc]
    rw [hBaseZWSnd]
    change eActualToQ.hom ≫ pullback.fst qWtoW yW ≫ qWtoW ≫ W.ι = _
    rw [pullback.condition_assoc, ← Category.assoc eActualToQ.hom,
      hActualOver]
  have hModelEnvelopeFst : kBtoC ≫ pullback.fst fCA gA' =
      pullback.fst fCBA gA' ≫ Spec.map ιCB := by
    dsimp [kBtoC, j', eQB]
    exact pullbackRightPullbackFstIso_inv_snd_fst fCA gA' (Spec.map ιCB)
  have hLiftEnvelope : liftActual ≫ universalEnvelopeMap =
      ePmodel'.hom ≫ kBtoC ≫ qScheme := by
    apply pullback.hom_ext
    · simp only [Category.assoc]
      rw [hUniversalFst, hqSchemeFst,
        hModelEnvelopeFst]
      dsimp [xToX0, xToX0', ePmodel']
      rw [IsPullback.isoPullback_hom_fst_assoc]
      dsimp [liftActual]
      simp only [← Category.assoc, pullback.lift_fst]
    · change (liftActual ≫ universalEnvelopeMap) ≫ fZbar =
        (ePmodel'.hom ≫ kBtoC ≫ qScheme) ≫ fZbar
      simp only [Category.assoc]
      rw [hUniversalSnd, hqSchemeBase, reassoc_of% hBtoCbase,
        reassoc_of% hQMap']
      dsimp [liftActual]
      rw [pullback.lift_snd_assoc]
      change pullback.snd f g' ≫ h ≫ yW ≫ W.ι =
        (pullback.snd f g' ≫ eY'.hom) ≫ φ
      dsimp [h, yW]
      rw [pullback.lift_fst_assoc]
      dsimp [hW]
      simp only [Category.assoc]
      rw [hφW]
  change liftActual ⁻¹ᵁ Uactual = U'
  rw [hUactualOpen, ← Scheme.Hom.comp_preimage, hLiftEnvelope]
  rw [Scheme.Hom.comp_preimage, Scheme.Hom.comp_preimage, hOpenQ]
  change ePmodel'.hom ⁻¹ᵁ kBtoC ⁻¹ᵁ (kBtoC ''ᵁ Umodel') = U'
  rw [Scheme.Hom.preimage_image_eq]
  change ePmodel'.hom ⁻¹ᵁ (ePmodel'.hom ''ᵁ U') = U'
  exact Scheme.Hom.preimage_image_eq _ _

end AlgebraicGeometry

end
