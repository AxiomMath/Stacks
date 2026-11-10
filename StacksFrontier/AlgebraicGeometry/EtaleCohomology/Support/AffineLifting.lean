module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Sites.MorphismProperty
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.TensorProduct.Quotient
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.Comp
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.Defs
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.OpenImmersion
public import StacksFrontier.RingTheory.Smooth.Syntomic
public import StacksFrontier.RingTheory.Syntomic.Morphisms
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Reducing a covering statement along a closed immersion to affine liftings

Let `i : X ⟶ Y` be a closed immersion and let `p : U ⟶ X` be syntomic, smooth or étale. A
local lifting theorem at the level of commutative rings — every such map out of a quotient
`A ⧸ I` lifts, after localizing at a family of elements generating the unit ideal, to a map out
of `A` — yields the corresponding global statement: `U` is covered by base changes along
morphisms `V j ⟶ Y` of the same class.

## Main definitions

* `AlgebraicGeometry.AffineLifting.Topology` selects one of the three classes of morphisms.
* `AlgebraicGeometry.RingMapHasTopology` and `AlgebraicGeometry.SchemeMapHasTopology` express
  the selected property of a ring homomorphism, respectively of a morphism of schemes.

## Main results

* `AlgebraicGeometry.exists_zariskiCover_baseChange_of_affine_lifting` reduces the covering
  assertion for schemes to the ring-level local liftings.

## Implementation notes

The affine lifting hypothesis includes the compatibility of each localization isomorphism with
the original map out of the quotient ring; it makes the resulting morphisms of pullbacks lie
over the closed subscheme. A Zariski covering is expressed as membership in Mathlib's
`AlgebraicGeometry.Scheme.zariskiPrecoverage`.

The selector is nested as `AffineLifting.Topology` rather than declared as `Topology` directly
in `AlgebraicGeometry`, since the latter would shadow Mathlib's `Topology` namespace in every
file that opens `AlgebraicGeometry`.

## References

* [Stacks Project, Tag 04E3](https://stacks.math.columbia.edu/tag/04E3)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

/-- Lift a single localized piece of an affine chart: a ring-level lifting of `b` after
inverting `r` produces an open immersion into the relevant pullback of spectra, with prescribed
image and compatible with `b`. -/
private theorem affine_lift_piece
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (I : Ideal A) (b : A ⧸ I →+* B) (q : A →+* C) (r : B)
    (e : Localization.Away r ≃+* C ⧸ Ideal.map q I)
    (he : ∀ a : A,
    e (algebraMap B (Localization.Away r) (b (Ideal.Quotient.mk I a))) =
      Ideal.Quotient.mk (Ideal.map q I) (q a)) :
    ∃ (g : pullback
        (Spec.map (CommRingCat.ofHom q))
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) ⟶ Spec (.of B)
        ) (_hg : IsOpenImmersion g),
        g.opensRange = PrimeSpectrum.basicOpen r ∧
        g ≫ Spec.map (CommRingCat.ofHom b) =
          pullback.snd (Spec.map (CommRingCat.ofHom q))
            (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) := by
  classical
  let : Algebra A C := q.toAlgebra
  let : Algebra A (A ⧸ I) := inferInstance
  let qb : A ⧸ I →+* C ⧸ Ideal.map q I :=
    Ideal.Quotient.lift I
      ((Ideal.Quotient.mk (Ideal.map q I)).comp q) (by
      intro a ha
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem q ha))
  let bSpec := Spec.map (CommRingCat.ofHom b)
  let jSpec := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
  let qSpec := Spec.map (CommRingCat.ofHom q)
  let locMap := Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away r)))
  let : Semiring (TensorProduct A (A ⧸ I) C) :=
    @Algebra.TensorProduct.instSemiring A (A ⧸ I) C
      inferInstance inferInstance inferInstance inferInstance inferInstance
  let : CommRing (TensorProduct A (A ⧸ I) C) :=
    @Algebra.TensorProduct.instCommRing A (A ⧸ I) C
      inferInstance inferInstance inferInstance inferInstance inferInstance
  let : Algebra (A ⧸ I) (TensorProduct A (A ⧸ I) C) :=
    Algebra.TensorProduct.leftAlgebra
  let G := Algebra.TensorProduct.quotIdealMapEquivQuotTensor (A := A) C I
  let Ghom := G.toRingHom
  let GRing := RingEquiv.ofBijective Ghom G.bijective
  let gIso := GRing.toCommRingCatIso
  let P := pullbackSymmetry qSpec jSpec ≪≫ pullbackSpecIso A (A ⧸ I) C ≪≫
    Scheme.Spec.mapIso gIso.op
  let eSpec := Scheme.Spec.mapIso (.op e.toCommRingCatIso)
  refine ⟨P.hom ≫ eSpec.hom ≫ locMap, inferInstance, ?_, ?_⟩
  · change Scheme.Hom.opensRange ((P.hom ≫ eSpec.hom) ≫ locMap) = _
    rw [Scheme.Hom.opensRange_comp_of_isIso (P.hom ≫ eSpec.hom) locMap]
    simpa [locMap] using
      (Scheme.Hom.opensRange_localizationAway (R := CommRingCat.of B) r)
  · have hcomp : e.toRingHom.comp ((algebraMap B (Localization.Away r)).comp b) = qb := by
      apply RingHom.ext
      intro x
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
      exact he a
    have hmaps : eSpec.hom ≫ locMap ≫ bSpec = Spec.map (CommRingCat.ofHom qb) := by
      dsimp [eSpec, locMap, bSpec]
      rw [← Spec.map_comp, ← Spec.map_comp]
      change Scheme.Spec.map
          (((CommRingCat.ofHom b ≫ CommRingCat.ofHom
              (algebraMap B (Localization.Away r))) ≫
            e.toCommRingCatIso.op.hom.unop).op) =
        Scheme.Spec.map (CommRingCat.ofHom qb).op
      exact congrArg Scheme.Spec.map
        (congrArg Quiver.Hom.op (congrArg CommRingCat.ofHom hcomp))
    have hqb : (GRing.toRingHom).comp qb = Algebra.TensorProduct.includeLeftRingHom := by
      apply RingHom.ext
      intro x
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
      change G (Ideal.Quotient.mk (Ideal.map (algebraMap A C) I)
        (algebraMap A C a)) =
        Algebra.TensorProduct.includeLeftRingHom (Ideal.Quotient.mk I a)
      rw [Algebra.TensorProduct.quotIdealMapEquivQuotTensor_mk,
        Algebra.TensorProduct.includeLeftRingHom_apply]
      rw [← Ideal.Quotient.algebraMap_eq I,
        ← Algebra.TensorProduct.tmul_one_eq_one_tmul]
    have hproj : P.hom ≫ Spec.map (CommRingCat.ofHom qb) =
        pullback.snd qSpec jSpec := by
      have hcat : CommRingCat.ofHom qb ≫ gIso.hom =
          CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom := by
        calc
          CommRingCat.ofHom qb ≫ gIso.hom =
              CommRingCat.ofHom qb ≫ CommRingCat.ofHom GRing.toRingHom := rfl
          _ = CommRingCat.ofHom ((GRing.toRingHom).comp qb) := by
            rw [CommRingCat.ofHom_comp]
          _ = CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom :=
            congrArg CommRingCat.ofHom hqb
      have htensor : (Scheme.Spec.mapIso gIso.op).hom ≫
          Spec.map (CommRingCat.ofHom qb) =
          Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom) := by
        simp only [Functor.mapIso_hom, Iso.op_hom, Scheme.Spec_map]
        rw [← Spec.map_comp]
        exact congrArg Scheme.Spec.map (congrArg Quiver.Hom.op hcat)
      simp only [P, Iso.trans_hom, Category.assoc, htensor, pullbackSpecIso_hom_fst,
        jSpec, qSpec, Ideal.Quotient.algebraMap_eq,
        pullbackSymmetry_hom_comp_fst]
    calc
      (P.hom ≫ eSpec.hom ≫ locMap) ≫ bSpec =
          P.hom ≫ (eSpec.hom ≫ locMap ≫ bSpec) := by
            simp [Category.assoc]
      _ = P.hom ≫ Spec.map (CommRingCat.ofHom qb) := by rw [hmaps]
      _ = pullback.snd qSpec jSpec := hproj

/-- Syntomicity of a ring homomorphism, as a property of the bare homomorphism. -/
private def syntomicRingHom {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) : Prop :=
  letI := f.toAlgebra
  Algebra.Syntomic A B

private lemma syntomicRingHom_iff {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) :
    syntomicRingHom f ↔ letI := f.toAlgebra; Algebra.Syntomic A B := Iff.rfl

/-- A ring isomorphism is syntomic. -/
private theorem syntomic_of_ringEquiv {A B : Type u} [CommRing A] [CommRing B]
    (e : A ≃+* B) : letI := e.toRingHom.toAlgebra; Algebra.Syntomic A B := by
  let : Algebra A B := e.toRingHom.toAlgebra
  have : Algebra.Smooth A A := by infer_instance
  have : Algebra.Smooth A B := Algebra.Smooth.of_equiv (R := A)
    (show A ≃ₐ[A] B from { e with commutes' := fun _ => rfl })
  exact Algebra.Smooth.syntomic A B

private theorem syntomicRingHom_respectsIso :
    RingHom.RespectsIso (@syntomicRingHom.{u}) := by
  constructor
  · intro A B C _ _ _ f e hf
    let : Algebra A B := f.toAlgebra
    let : Algebra B C := e.toRingHom.toAlgebra
    let : Algebra A C := (e.toRingHom.comp f).toAlgebra
    have : IsScalarTower A B C := .of_algebraMap_eq fun _ => rfl
    have : Algebra.Syntomic A B := (syntomicRingHom_iff f).mp hf
    have : Algebra.Syntomic B C := syntomic_of_ringEquiv e
    exact (syntomicRingHom_iff _).mpr (Algebra.Syntomic.comp A B C)
  · intro A B C _ _ _ f e hf
    let : Algebra A B := e.toRingHom.toAlgebra
    let : Algebra B C := f.toAlgebra
    let : Algebra A C := (f.comp e.toRingHom).toAlgebra
    have : IsScalarTower A B C := .of_algebraMap_eq fun _ => rfl
    have : Algebra.Syntomic A B := syntomic_of_ringEquiv e
    have : Algebra.Syntomic B C := (syntomicRingHom_iff f).mp hf
    exact (syntomicRingHom_iff _).mpr (Algebra.Syntomic.comp A B C)

/-- The three classes of morphisms to which the affine reduction applies. -/
public inductive AffineLifting.Topology where
  | syntomic
  | smooth
  | etale

/-- The selected property of a homomorphism of commutative rings. -/
public def RingMapHasTopology (τ : AffineLifting.Topology) {A B : Type u}
    [CommRing A] [CommRing B] (f : A →+* B) : Prop :=
  letI := f.toAlgebra
  match τ with
  | .syntomic => Algebra.Syntomic A B
  | .smooth => Algebra.Smooth A B
  | .etale => Algebra.Etale A B

/-- The selected property of a morphism of schemes. -/
public def SchemeMapHasTopology (τ : AffineLifting.Topology) {X Y : Scheme.{u}}
    (f : X ⟶ Y) : Prop :=
  match τ with
  | .syntomic => Syntomic f
  | .smooth => Smooth f
  | .etale => Etale f

private theorem specMap_hasTopology (τ : AffineLifting.Topology) {A C : Type u}
    [CommRing A] [CommRing C] (q : A →+* C)
    (hq : RingMapHasTopology τ q) :
    SchemeMapHasTopology τ (Spec.map (CommRingCat.ofHom q)) := by
  cases τ with
  | syntomic =>
      let : Algebra A C := q.toAlgebra
      change Algebra.Syntomic A C at hq
      have hs : syntomicRingHom
          (((Spec.map (CommRingCat.ofHom q)).appTop).hom) :=
        (syntomicRingHom_respectsIso.arrow_mk_iso_iff
          (arrowIsoΓSpecOfIsAffine (CommRingCat.ofHom q))).mp hq
      intro x
      let f := Spec.map (CommRingCat.ofHom q)
      have hpre : (⊤ : (Spec (CommRingCat.of C)).Opens) =
          f ⁻¹ᵁ (⊤ : (Spec (CommRingCat.of A)).Opens) := by
        ext y
        simp
      cases hpre
      have hs' : syntomicRingHom f.appTop.hom := hs
      refine ⟨⟨⊤, isAffineOpen_top _⟩, by simp,
        ⟨⊤, isAffineOpen_top _⟩, by simp, ?_⟩
      exact (syntomicRingHom_iff _).mp hs'
  | smooth =>
      let : Algebra A C := q.toAlgebra
      change Algebra.Smooth A C at hq
      have hr : RingHom.Smooth
          (((Spec.map (CommRingCat.ofHom q)).appTop).hom) :=
        (RingHom.Smooth.respectsIso.arrow_mk_iso_iff
          (arrowIsoΓSpecOfIsAffine (CommRingCat.ofHom q))).mp hq
      exact (HasRingHomProperty.iff_of_isAffine (P := @Smooth)).2 hr
  | etale =>
      let : Algebra A C := q.toAlgebra
      change Algebra.Etale A C at hq
      have hr : RingHom.Etale
          (((Spec.map (CommRingCat.ofHom q)).appTop).hom) :=
        (RingHom.Etale.respectsIso.arrow_mk_iso_iff
          (arrowIsoΓSpecOfIsAffine (CommRingCat.ofHom q))).mp hq
      exact (HasRingHomProperty.iff_of_isAffine (P := @Etale)).2 hr

/-- Transport one lifted affine piece to a morphism into `U` over the closed subscheme. -/
private theorem transport_affine_piece
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (I : Ideal A) (b : A ⧸ I →+* B) (q : A →+* C) (r : B)
    (eLoc : Localization.Away r ≃+* C ⧸ Ideal.map q I)
    (heLoc : ∀ a : A,
      eLoc (algebraMap B (Localization.Away r)
        (b (Ideal.Quotient.mk I a))) =
          Ideal.Quotient.mk (Ideal.map q I) (q a))
    {X Y U : Scheme.{u}} (i : X ⟶ Y) [IsClosedImmersion i]
    (p : U ⟶ X) (w : Spec (.of A) ⟶ Y)
    (v : Spec (.of B) ⟶ U) [IsOpenImmersion v]
    (e : pullback w i ≅ Spec (.of (A ⧸ I)))
    (he : e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) =
      pullback.fst w i)
    (z : Spec (.of B) ⟶ pullback w i)
    (hz : Spec.map (CommRingCat.ofHom b) = z ≫ e.hom)
    (hv : z ≫ pullback.snd w i = v ≫ p) :
    ∃ (g : pullback (Spec.map (CommRingCat.ofHom q) ≫ w) i ⟶ U),
      IsOpenImmersion g ∧
        g ≫ p = pullback.snd (Spec.map (CommRingCat.ofHom q) ≫ w) i ∧
        ∀ x : Spec (.of B), x ∈ PrimeSpectrum.basicOpen r → ∃ t, g t = v x := by
  classical
  obtain ⟨gl, hgl, hglrange, hcomp⟩ := affine_lift_piece I b q r eLoc heLoc
  let qS := Spec.map (CommRingCat.ofHom q)
  let mS := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
  let d0 := pullback qS mS
  let d1 := pullback qS (pullback.fst w i)
  let d2 := pullback (qS ≫ w) i
  let hm := pullback.map qS (pullback.fst w i) qS mS (𝟙 _) e.hom (𝟙 _)
    (by simp) (by simpa [mS] using he.symm)
  have : IsIso hm := inferInstance
  let e₁ : d1 ≅ d0 := asIso hm
  let e₂ : d1 ≅ d2 := pullbackRightPullbackFstIso w i qS
  let ed : d0 ≅ d2 := e₁.symm ≪≫ e₂
  refine ⟨ed.inv ≫ gl ≫ v, ?_, ?_, ?_⟩
  · infer_instance
  · apply (cancel_epi ed.hom).1
    change ed.hom ≫ (ed.inv ≫ gl ≫ v ≫ p) =
      ed.hom ≫ pullback.snd (qS ≫ w) i
    rw [Iso.hom_inv_id_assoc]
    calc
      gl ≫ v ≫ p = gl ≫ z ≫ pullback.snd w i := by rw [← hv]
      _ = gl ≫ z ≫ e.hom ≫ e.inv ≫ pullback.snd w i := by
        simp
      _ = gl ≫ Spec.map (CommRingCat.ofHom b) ≫ e.inv ≫ pullback.snd w i := by
        simpa only [Category.assoc] using congrArg
          (fun f : Spec (.of B) ⟶ Spec (.of (A ⧸ I)) =>
            gl ≫ f ≫ e.inv ≫ pullback.snd w i) hz.symm
      _ = pullback.snd qS mS ≫ e.inv ≫ pullback.snd w i := by
        rw [← Category.assoc, hcomp]
      _ = ed.hom ≫ pullback.snd (qS ≫ w) i := by
        have hproj : e₁.inv ≫ pullback.snd qS (pullback.fst w i) =
            pullback.snd qS mS ≫ e.inv := by
          have hh : hm ≫ pullback.snd qS mS =
              pullback.snd qS (pullback.fst w i) ≫ e.hom := by
            simp [hm, pullback.map]
          apply (cancel_mono e.hom).1
          calc
            (e₁.inv ≫ pullback.snd qS (pullback.fst w i)) ≫ e.hom =
                e₁.inv ≫ hm ≫ pullback.snd qS mS := by
                  simpa only [Category.assoc] using
                    congrArg (fun f => e₁.inv ≫ f) hh.symm
            _ = pullback.snd qS mS := by simp [e₁]
            _ = (pullback.snd qS mS ≫ e.inv) ≫ e.hom := by simp
        rw [← Category.assoc, ← hproj]
        simp [ed, e₂, Category.assoc, pullbackRightPullbackFstIso_hom_snd]
  · intro x hx
    have hx' : x ∈ gl.opensRange := by rwa [hglrange]
    obtain ⟨t, ht⟩ := Scheme.Hom.mem_opensRange.mp hx'
    refine ⟨ed.hom t, ?_⟩
    simp [ht]

private theorem ringMapHasTopology_of_specMap (τ : AffineLifting.Topology) {A B : Type u}
    [CommRing A] [CommRing B] (b : A →+* B)
    (hb : SchemeMapHasTopology τ (Spec.map (CommRingCat.ofHom b))) :
    RingMapHasTopology τ b := by
  cases τ with
  | syntomic =>
      let f := Spec.map (CommRingCat.ofHom b)
      change Syntomic f at hb
      let : Algebra Γ(Spec (.of A), ⊤) Γ(Spec (.of B), ⊤) :=
        (f.appLE ⊤ ⊤ (by simp)).hom.toAlgebra
      have hfAffine := ((syntomic_tfae f).out 1 2
        (a := Syntomic f)
        (b := ∀ (U : (Spec (.of B)).Opens) (_ : IsAffineOpen U)
          (V : (Spec (.of A)).Opens) (_ : IsAffineOpen V)
          (hUV : U ≤ f ⁻¹ᵁ V),
          let : Algebra Γ(Spec (.of A), V) Γ(Spec (.of B), U) :=
            (f.appLE V U hUV).hom.toAlgebra
          Algebra.Syntomic Γ(Spec (.of A), V) Γ(Spec (.of B), U))
        rfl rfl (by decide) (by decide)).mp hb
      have htop : Algebra.Syntomic Γ(Spec (.of A), ⊤) Γ(Spec (.of B), ⊤) := by
        simpa only [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE] using
          hfAffine ⊤ (isAffineOpen_top _) ⊤ (isAffineOpen_top _) (by simp)
      exact (syntomicRingHom_respectsIso.arrow_mk_iso_iff
        (arrowIsoΓSpecOfIsAffine (CommRingCat.ofHom b))).mpr
          ((syntomicRingHom_iff f.appTop.hom).mpr htop)
  | smooth =>
      let f := Spec.map (CommRingCat.ofHom b)
      have hr : RingHom.Smooth f.appTop.hom :=
        (HasRingHomProperty.iff_of_isAffine (P := @Smooth)).1 hb
      exact (RingHom.Smooth.respectsIso.arrow_mk_iso_iff
        (arrowIsoΓSpecOfIsAffine (CommRingCat.ofHom b))).mpr hr
  | etale =>
      let f := Spec.map (CommRingCat.ofHom b)
      have hr : RingHom.Etale f.appTop.hom :=
        (HasRingHomProperty.iff_of_isAffine (P := @Etale)).1 hb
      exact (RingHom.Etale.respectsIso.arrow_mk_iso_iff
        (arrowIsoΓSpecOfIsAffine (CommRingCat.ofHom b))).mpr hr

@[ega "IV 17.3.3"]
private theorem schemeMapHasTopology_of_openImmersion (τ : AffineLifting.Topology)
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    SchemeMapHasTopology τ f := by
  cases τ with
  | syntomic => exact syntomic_of_isOpenImmersion f
  | smooth => exact inferInstanceAs (Smooth f)
  | etale => exact inferInstanceAs (Etale f)

private theorem schemeMapHasTopology_comp (τ : AffineLifting.Topology) {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : SchemeMapHasTopology τ f) (hg : SchemeMapHasTopology τ g) :
    SchemeMapHasTopology τ (f ≫ g) := by
  cases τ with
  | syntomic =>
      have := syntomic_isStableUnderComposition.{u}
      exact MorphismProperty.comp_mem @Syntomic f g hf hg
  | smooth => exact MorphismProperty.comp_mem @Smooth f g hf hg
  | etale =>
      have : Etale f := hf
      have : Etale g := hg
      exact inferInstanceAs (Etale (f ≫ g))

/-- Around any point of `U` choose an affine chart of `Y`, an affine chart of `U` above it, and
the induced presentation of the pullback along the closed immersion. -/
private theorem exists_affine_chart_data (τ : AffineLifting.Topology)
    {X Y U : Scheme.{u}} (i : X ⟶ Y) [IsClosedImmersion i]
    (p : U ⟶ X) (hp : SchemeMapHasTopology τ p) (x : U) :
    ∃ (A B : CommRingCat.{u}) (w : Spec A ⟶ Y) (v : Spec B ⟶ U)
      (_hw : IsOpenImmersion w) (_hv : IsOpenImmersion v)
      (I : Ideal A) (e : pullback w i ≅ Spec (.of (A ⧸ I)))
      (_he : e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) =
        pullback.fst w i)
      (z : Spec B ⟶ pullback w i) (b : A ⧸ I →+* B),
      Spec.map (CommRingCat.ofHom b) = z ≫ e.hom ∧
      z ≫ pullback.snd w i = v ≫ p ∧
      x ∈ Set.range v.base ∧
        SchemeMapHasTopology τ (Spec.map (CommRingCat.ofHom b)) := by
  classical
  let f₀ := p ≫ i
  obtain ⟨A, w, hw, hxy, -⟩ := Scheme.exists_affine_mem_range_and_range_subset
    (X := Y) (x := f₀ x) (U := ⊤) (by simp)
  obtain ⟨a, ha⟩ := Set.mem_range.mp hxy
  let O := f₀ ⁻¹ᵁ w.opensRange
  have hxO : x ∈ O := ⟨a, ha⟩
  obtain ⟨B, v, hv, hxv, hvsub⟩ :=
    Scheme.exists_affine_mem_range_and_range_subset (X := U) (x := x) (U := O) hxO
  let f := v ≫ p
  let T := pullback w i
  let t₁ := pullback.fst w i
  let t₂ := pullback.snd w i
  let W := t₂.opensRange
  have hfW : Set.range f.base ⊆ W := by
    intro y hy
    obtain ⟨s, rfl⟩ := hy
    have hvpt : v s ∈ v.opensRange := ⟨s, rfl⟩
    have hmem := hvsub hvpt
    change (p ≫ i) (v s) ∈ w.opensRange at hmem
    change (v ≫ p) s ∈ Scheme.Hom.opensRange (pullback.snd w i)
    rw [Scheme.Hom.opensRange_pullbackSnd]
    exact hmem
  have hpre : f ⁻¹ᵁ W = ⊤ := eq_top_iff.2 fun s _ => hfW ⟨s, rfl⟩
  have hrange : Set.range t₂.base = Set.range W.ι.base := by
    ext y
    simp [W]
  let eOpen := IsOpenImmersion.isoOfRangeEq t₂ W.ι hrange
  let fRes := f.resLE W ⊤ (by rw [hpre])
  let z := (Spec B).topIso.inv ≫ fRes ≫ eOpen.inv
  have hz₂ : z ≫ t₂ = f := by
    calc
      z ≫ t₂ = ((Spec B).topIso.inv ≫ fRes) ≫ (eOpen.inv ≫ t₂) := by
        dsimp [z]
        simp only [Category.assoc]
      _ = ((Spec B).topIso.inv ≫ fRes) ≫ W.ι := by
        rw [show eOpen.inv ≫ t₂ = W.ι from
          IsOpenImmersion.isoOfRangeEq_inv_fac t₂ W.ι hrange]
      _ = (Spec B).topIso.inv ≫ (⊤ : (Spec B).Opens).ι ≫ f := by
        dsimp [fRes]
        rw [Category.assoc, Scheme.Hom.resLE_comp_ι]
      _ = f := by
        change ((Spec B).topIso.inv ≫ (⊤ : (Spec B).Opens).ι) ≫ f = f
        rw [Scheme.toIso_inv_ι]
        simp
  have : IsClosedImmersion t₁ := inferInstance
  obtain ⟨I, e, he₀⟩ := (IsClosedImmersion.Spec_iff (f := t₁)).mp inferInstance
  have he : e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) =
      pullback.fst w i := by
    simpa [t₁] using he₀.symm
  let b : A ⧸ I →+* B := (Scheme.Spec.preimage (z ≫ e.hom)).unop.hom
  have hb : Spec.map (CommRingCat.ofHom b) = z ≫ e.hom := Scheme.Spec.map_preimage _
  have hfp : SchemeMapHasTopology τ f :=
    schemeMapHasTopology_comp τ v p (schemeMapHasTopology_of_openImmersion τ v) hp
  have hres : SchemeMapHasTopology τ fRes := by
    cases τ with
    | syntomic =>
        change Syntomic f at hfp
        exact syntomic_resLE hfp ⊤ W (by rw [hpre])
    | smooth =>
        have : Smooth f := hfp
        exact inferInstanceAs (Smooth fRes)
    | etale =>
        have : Etale f := hfp
        exact inferInstanceAs (Etale fRes)
  have htopIso : SchemeMapHasTopology τ (Spec B).topIso.inv :=
    schemeMapHasTopology_of_openImmersion τ _
  have hOpenIso : SchemeMapHasTopology τ eOpen.inv :=
    schemeMapHasTopology_of_openImmersion τ _
  have hz : SchemeMapHasTopology τ z :=
    schemeMapHasTopology_comp τ _ _
      htopIso (schemeMapHasTopology_comp τ _ _ hres hOpenIso)
  have heIso : SchemeMapHasTopology τ e.hom :=
    schemeMapHasTopology_of_openImmersion τ _
  have hzq : SchemeMapHasTopology τ (z ≫ e.hom) :=
    schemeMapHasTopology_comp τ z e.hom hz heIso
  have hspec : SchemeMapHasTopology τ (Spec.map (CommRingCat.ofHom b)) := by
    simpa only [hb] using hzq
  refine ⟨A, B, w, v, hw, hv, I, e, he, z, b, hb, hz₂, hxv, hspec⟩

/-- A ring-level local lifting result for a topology yields a covering of a scheme
over a closed subscheme by base changes of schemes over the ambient scheme. -/
public theorem exists_zariskiCover_baseChange_of_affine_lifting (τ : AffineLifting.Topology)
    (hLift : ∀ (A : Type u) [CommRing A] (I : Ideal A)
      (B : Type u) [CommRing B] (b : A ⧸ I →+* B),
      RingMapHasTopology τ b →
        ∃ (J : Type u) (g : J → B), Ideal.span (Set.range g) = ⊤ ∧
          ∀ j, ∃ (C : Type u) (hC : CommRing C),
            letI : CommRing C := hC
            ∃ (q : A →+* C), RingMapHasTopology τ q ∧
              ∃ (e : Localization.Away (g j) ≃+* C ⧸ Ideal.map q I),
                ∀ a : A,
                  e (algebraMap B (Localization.Away (g j))
                    (b (Ideal.Quotient.mk I a))) =
                    Ideal.Quotient.mk (Ideal.map q I) (q a))
    {X Y U : Scheme.{u}} (i : X ⟶ Y) [IsClosedImmersion i]
    (p : U ⟶ X) (hp : SchemeMapHasTopology τ p) :
    ∃ (J : Type u) (V : J → Scheme.{u}) (q : ∀ j, V j ⟶ Y)
      (g : ∀ j, pullback (q j) i ⟶ U),
      (∀ j, SchemeMapHasTopology τ (q j)) ∧
        (∀ j, g j ≫ p = pullback.snd (q j) i) ∧
          Presieve.ofArrows (fun j ↦ pullback (q j) i) g ∈
            Scheme.zariskiPrecoverage U := by
  classical
  let chartData (x : U) := exists_affine_chart_data τ i p hp x
  choose A B w v hw hv I e he z b hb hz₂ hxv hspec using chartData
  let liftData (x : U) := hLift (A x) (I x) (B x) (b x)
    (ringMapHasTopology_of_specMap τ (b x) (hspec x))
  choose J gen hspan hlocal using liftData
  have localLiftData (x : U) (j : J x) :
      ∃ (C : Type u) (hC : CommRing C) (q : A x →+* C),
        RingMapHasTopology τ q ∧
          ∃ (e : Localization.Away (gen x j) ≃+* C ⧸ Ideal.map q (I x)),
            ∀ a : A x,
              e (algebraMap (B x) (Localization.Away (gen x j))
                (b x (Ideal.Quotient.mk (I x) a))) =
                  Ideal.Quotient.mk (Ideal.map q (I x)) (q a) :=
    hlocal x j
  choose C hC q hdata using localLiftData
  have hq (x : U) (j : J x) : RingMapHasTopology τ (q x j) :=
    (hdata x j).1
  choose eloc hcompat using fun x j => (hdata x j).2
  have vOpen (x : U) : IsOpenImmersion (v x) := hv x
  have localPieces (x : U) (j : J x) :=
    transport_affine_piece (I x) (b x) (q x j) (gen x j)
      (eloc x j) (hcompat x j) i p (w x) (v x) (e x) (he x) (z x)
      (hb x) (hz₂ x)
  choose g hg hgp hcoverLocal using localPieces
  let Index := Σ x : U, J x
  let V : Index → Scheme.{u} := fun k => Spec (.of (C k.1 k.2))
  let qScheme : ∀ k : Index, V k ⟶ Y := fun k =>
    Spec.map (CommRingCat.ofHom (q k.1 k.2)) ≫ w k.1
  let gScheme : ∀ k : Index, pullback (qScheme k) i ⟶ U := fun k =>
    g k.1 k.2
  have hqScheme (k : Index) : SchemeMapHasTopology τ (qScheme k) := by
    let : IsOpenImmersion (w k.1) := hw k.1
    exact schemeMapHasTopology_comp τ _ _
      (specMap_hasTopology τ (q k.1 k.2) (hq k.1 k.2))
      (schemeMapHasTopology_of_openImmersion τ (w k.1))
  refine ⟨Index, V, qScheme, gScheme, hqScheme, fun k => hgp k.1 k.2, ?_⟩
  change Presieve.ofArrows (fun k : Index ↦ pullback (qScheme k) i) gScheme ∈
    Scheme.precoverage @IsOpenImmersion U
  rw [Scheme.ofArrows_mem_precoverage_iff]
  refine ⟨fun x => ?_, fun k => hg k.1 k.2⟩
  obtain ⟨y, hy⟩ := hxv x
  have hbasicTop : (⨆ j : J x, PrimeSpectrum.basicOpen (gen x j)) = ⊤ :=
    PrimeSpectrum.iSup_basicOpen_eq_top_iff.mpr (hspan x)
  have hyBasic : y ∈ ⨆ j : J x, PrimeSpectrum.basicOpen (gen x j) := by
    rw [hbasicTop]
    trivial
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp hyBasic
  obtain ⟨t, ht⟩ := hcoverLocal x j y hj
  refine ⟨⟨x, j⟩, t, ?_⟩
  change g x j t = x
  rw [ht, hy]

end AlgebraicGeometry
