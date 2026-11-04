module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Sites.MorphismProperty
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Support.AffineLifting
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.Defs
public import StacksFrontier.RingTheory.Etale.Lifting
public import StacksFrontier.RingTheory.Smooth.LocalStructure
public import StacksFrontier.RingTheory.Syntomic.RelativeGlobalCompleteIntersection

/-!
# Lifting étale, smooth and syntomic schemes along a closed immersion

Let `i : X ⟶ Y` be a closed immersion. A scheme étale, smooth, or syntomic over the closed
subscheme `X` is covered in the Zariski topology by base changes along `i` of schemes with the
same property over the ambient scheme `Y`.

## Main results

* `AlgebraicGeometry.exists_etale_zariskiCover_baseChange_of_isClosedImmersion`,
  `AlgebraicGeometry.exists_smooth_zariskiCover_baseChange_of_isClosedImmersion` and
  `AlgebraicGeometry.exists_syntomic_zariskiCover_baseChange_of_isClosedImmersion` are the
  three cases.

## Implementation notes

The Zariski covering is expressed by membership in `Scheme.zariskiPrecoverage`, and the
displayed equations record that the covering maps are morphisms over the closed subscheme.

## References

* [Stacks Project, Tag 04E3](https://stacks.math.columbia.edu/tag/04E3)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- If `C` has the property `τ` as an `A`-algebra, then `algebraMap A C` has it as a ring map. -/
private theorem ringMapHasTopology_algebraMap {A C : Type u} [CommRing A] [CommRing C]
    [Algebra A C] (τ : AffineLifting.Topology)
    (h : match τ with
      | .syntomic => Algebra.Syntomic A C
      | .smooth => Algebra.Smooth A C
      | .etale => Algebra.Etale A C) :
    RingMapHasTopology τ (algebraMap A C) := by
  cases τ <;> rwa [RingMapHasTopology, toAlgebra_algebraMap]

private theorem etale_affine_lifting
    (A : Type u) [CommRing A] (I : Ideal A) (B : Type u) [CommRing B]
    (b : A ⧸ I →+* B)
    (hb : AlgebraicGeometry.RingMapHasTopology .etale b) :
    ∃ (J : Type u) (g : J → B), Ideal.span (Set.range g) = ⊤ ∧
      ∀ j, ∃ (C : Type u) (hC' : CommRing C),
        letI : CommRing C := hC'
        ∃ (q : A →+* C), AlgebraicGeometry.RingMapHasTopology .etale q ∧
          ∃ (e : Localization.Away (g j) ≃+* C ⧸ Ideal.map q I),
            ∀ a : A,
              e (algebraMap B (Localization.Away (g j))
                (b (Ideal.Quotient.mk I a))) = Ideal.Quotient.mk (Ideal.map q I) (q a) := by
  let : Algebra (A ⧸ I) B := b.toAlgebra
  change Algebra.Etale (A ⧸ I) B at hb
  refine ⟨B, fun x => x, by simp, ?_⟩
  intro x
  let S := Localization.Away x
  let : IsLocalization.Away x S :=
    Localization.isLocalization (R := B) (M := Submonoid.powers x)
  let : Algebra (A ⧸ I) S := ((algebraMap B S).comp b).toAlgebra
  let : Algebra A S := ((algebraMap (A ⧸ I) S).comp (Ideal.Quotient.mk I)).toAlgebra
  let : SMul (A ⧸ I) B := (inferInstance : Algebra (A ⧸ I) B).toSMul
  let : SMul B S := (inferInstance : Algebra B S).toSMul
  let : SMul (A ⧸ I) S := (inferInstance : Algebra (A ⧸ I) S).toSMul
  let : SMul A (A ⧸ I) := (inferInstance : Algebra A (A ⧸ I)).toSMul
  let : SMul A S := (inferInstance : Algebra A S).toSMul
  let : IsScalarTower (A ⧸ I) B S := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower A (A ⧸ I) S := IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra.Etale B S := Algebra.Etale.of_isLocalizationAway x
  let : Algebra.Etale (A ⧸ I) S := Algebra.Etale.comp (A ⧸ I) B S
  obtain ⟨C, instC, instAC, hC, ψ, hψ, hker⟩ :=
    etale_lift_along_surjection A (A ⧸ I) S Ideal.Quotient.mk_surjective
  let : CommRing C := instC
  let : Algebra A C := instAC
  let q : A →+* C := algebraMap A C
  let e₀ : C ⧸ Ideal.map q I ≃+* S :=
    (Ideal.quotEquivOfEq (by simpa [q] using hker.symm)).trans
      (RingHom.quotientKerEquivOfSurjective hψ)
  refine ⟨C, instC, q, ?_, e₀.symm, ?_⟩
  · exact ringMapHasTopology_algebraMap .etale hC
  · intro a
    apply e₀.injective
    simp only [RingEquiv.apply_symm_apply, e₀, RingEquiv.trans_apply,
      Ideal.quotEquivOfEq_mk, RingHom.quotientKerEquivOfSurjective_apply_mk]
    symm
    show ψ (algebraMap A C a) = algebraMap B S (b (Ideal.Quotient.mk I a))
    rw [AlgHom.commutes]
    rfl

/-- An étale scheme over a closed subscheme has a Zariski covering by base changes of étale
schemes over the ambient scheme. -/
@[stacks 04E3 "etale_cover", ega "IV 18.1.1" "étale case"]
public theorem exists_etale_zariskiCover_baseChange_of_isClosedImmersion
    {X Y U : Scheme.{u}} (i : X ⟶ Y) [IsClosedImmersion i]
    (p : U ⟶ X) [Etale p] :
    ∃ (I : Type u) (V : I → Scheme.{u}) (q : ∀ j, V j ⟶ Y)
      (g : ∀ j, pullback (q j) i ⟶ U),
      (∀ j, Etale (q j)) ∧
        (∀ j, g j ≫ p = pullback.snd (q j) i) ∧
          Presieve.ofArrows (fun j ↦ pullback (q j) i) g ∈ Scheme.zariskiPrecoverage U := by
  simpa only [AlgebraicGeometry.SchemeMapHasTopology] using
    (AlgebraicGeometry.exists_zariskiCover_baseChange_of_affine_lifting
      .etale etale_affine_lifting i p (inferInstanceAs (Etale p)))

private theorem smooth_affine_lifting :
    ∀ (A : Type u) [CommRing A] (I : Ideal A)
      (B : Type u) [CommRing B] (b : A ⧸ I →+* B),
      AlgebraicGeometry.RingMapHasTopology .smooth b →
        ∃ (J : Type u) (g : J → B), Ideal.span (Set.range g) = ⊤ ∧
          ∀ j, ∃ (C : Type u) (hC : CommRing C),
            letI : CommRing C := hC
            ∃ (q : A →+* C), AlgebraicGeometry.RingMapHasTopology .smooth q ∧
              ∃ (e : Localization.Away (g j) ≃+* C ⧸ Ideal.map q I),
                ∀ a : A,
                  e (algebraMap B (Localization.Away (g j))
                    (b (Ideal.Quotient.mk I a))) =
                    Ideal.Quotient.mk (Ideal.map q I) (q a) := by
  intro A _ I B _ b hb
  let : Algebra (A ⧸ I) B := b.toAlgebra
  have : Algebra.Smooth (A ⧸ I) B := hb
  obtain ⟨s, hs, hs'⟩ :=
    Algebra.Smooth.exists_span_eq_top_isStandardSmooth_algEquiv_tensorProduct
      A (A ⧸ I) Ideal.Quotient.mk_surjective B
  refine ⟨s, Subtype.val, by simpa using hs, ?_⟩
  intro j
  obtain ⟨C, hC, hAlg, hStd, ⟨F⟩⟩ := hs' j.1 j.2
  let : CommRing C := hC
  let : Algebra A C := hAlg
  let : Algebra.IsStandardSmooth A C := hStd
  let q : A →+* C := algebraMap A C
  let G := Algebra.TensorProduct.quotIdealMapEquivQuotTensor (A := A) C I
  let e : Localization.Away j.1 ≃+* C ⧸ Ideal.map q I :=
    F.toRingEquiv.trans G.symm.toRingEquiv
  refine ⟨C, hC, q, ?_, e, ?_⟩
  · exact ringMapHasTopology_algebraMap .smooth inferInstance
  · intro a
    apply G.injective
    simp only [e, RingEquiv.trans_apply]
    show G (G.symm (F (algebraMap B (Localization.Away j.1)
        (algebraMap (A ⧸ I) B (Ideal.Quotient.mk I a))))) = G _
    rw [AlgEquiv.apply_symm_apply]
    calc
      F (algebraMap B (Localization.Away j.1)
          (algebraMap (A ⧸ I) B (Ideal.Quotient.mk I a))) =
          algebraMap (A ⧸ I) (TensorProduct A (A ⧸ I) C)
            (Ideal.Quotient.mk I a) := by
        rw [← IsScalarTower.algebraMap_apply (A ⧸ I) B (Localization.Away j.1)]
        exact F.commutes _
      _ = G (Ideal.Quotient.mk (Ideal.map q I) (q a)) := by
        have hq : Ideal.Quotient.mk (Ideal.map q I) (q a) =
            algebraMap (A ⧸ I) (C ⧸ Ideal.map q I) (Ideal.Quotient.mk I a) := by
          rw [show q a = algebraMap A C a by rfl, Ideal.Quotient.mk_algebraMap,
            ← Ideal.Quotient.algebraMap_eq I]
          exact IsScalarTower.algebraMap_apply A (A ⧸ I)
            (C ⧸ Ideal.map q I) a
        rw [hq]
        exact (G.commutes _).symm

/-- If `X ⟶ Y` is a closed immersion and `U ⟶ X` is smooth, then `U` has a Zariski covering
by schemes obtained by base change from smooth schemes over `Y`. -/
@[stacks 04E3 "smooth_cover", ega "IV 18.1.1" "smooth case"]
public theorem exists_smooth_zariskiCover_baseChange_of_isClosedImmersion
    {X Y U : Scheme.{u}} (i : X ⟶ Y) [IsClosedImmersion i]
    (p : U ⟶ X) [Smooth p] :
    ∃ (I : Type u) (V : I → Scheme.{u}) (q : ∀ j, V j ⟶ Y)
      (g : ∀ j, pullback (q j) i ⟶ U),
      (∀ j, Smooth (q j)) ∧
        (∀ j, g j ≫ p = pullback.snd (q j) i) ∧
          Presieve.ofArrows (fun j ↦ pullback (q j) i) g ∈ Scheme.zariskiPrecoverage U := by
  simpa only [AlgebraicGeometry.SchemeMapHasTopology] using
    AlgebraicGeometry.exists_zariskiCover_baseChange_of_affine_lifting
      .smooth smooth_affine_lifting i p (inferInstanceAs (Smooth p))

/-- If `X ⟶ Y` is a closed immersion and `U ⟶ X` is syntomic, then `U` has a Zariski
covering by schemes obtained by base change from syntomic schemes over `Y`. -/
@[stacks 04E3 "syntomic_cover"]
public theorem exists_syntomic_zariskiCover_baseChange_of_isClosedImmersion
    {X Y U : Scheme.{u}} (i : X ⟶ Y) [IsClosedImmersion i]
    (p : U ⟶ X) (hp : AlgebraicGeometry.Syntomic p) :
    ∃ (I : Type u) (V : I → Scheme.{u}) (q : ∀ j, V j ⟶ Y)
      (g : ∀ j, pullback (q j) i ⟶ U),
      (∀ j, AlgebraicGeometry.Syntomic (q j)) ∧
        (∀ j, g j ≫ p = pullback.snd (q j) i) ∧
          Presieve.ofArrows (fun j ↦ pullback (q j) i) g ∈ Scheme.zariskiPrecoverage U := by
  apply AlgebraicGeometry.exists_zariskiCover_baseChange_of_affine_lifting
    AffineLifting.Topology.syntomic ?_ i p hp
  intro A _ I B _ b hb
  let : Algebra (A ⧸ I) B := b.toAlgebra
  let : Algebra A B := (b.comp (Ideal.Quotient.mk I)).toAlgebra
  let : IsScalarTower A (A ⧸ I) B := .of_algebraMap_eq fun a => rfl
  let : Algebra.Syntomic (A ⧸ I) B := hb
  obtain ⟨s, hs, hloc⟩ :=
    Algebra.Syntomic.exists_span_eq_top_algEquiv_quotient (R := A) (S := B) I
  refine ⟨{g // g ∈ s}, (·.1), by simpa using hs, ?_⟩
  intro g
  obtain ⟨T, hT, hAlg, hrgci, ⟨e⟩⟩ := hloc g.1 g.2
  let : CommRing T := hT
  let : Algebra A T := hAlg
  let q : A →+* T := algebraMap A T
  refine ⟨T, hT, ⟨q, ?_, ⟨e.symm, ?_⟩⟩⟩
  · exact ringMapHasTopology_algebraMap .syntomic
      (Algebra.Syntomic.of_isRelativeGlobalCompleteIntersection A T)
  · intro a
    apply e.injective
    calc
      e (e.symm (algebraMap B (Localization.Away g.1)
        (b (Ideal.Quotient.mk I a)))) =
          algebraMap B (Localization.Away g.1) (b (Ideal.Quotient.mk I a)) := e.apply_symm_apply _
      _ = algebraMap B (Localization.Away g.1) (algebraMap A B a) := rfl
      _ = algebraMap A (Localization.Away g.1) a :=
        (IsScalarTower.algebraMap_apply A B (Localization.Away g.1) a).symm
      _ = e (Ideal.Quotient.mk (Ideal.map q I) (q a)) := by
        symm
        simp [q]

end AlgebraicGeometry
