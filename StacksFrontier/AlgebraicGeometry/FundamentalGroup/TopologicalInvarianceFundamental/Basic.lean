module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import StacksFrontier.RingTheory.Henselian.AbsolutelyIntegrallyClosed
public import StacksFrontier.RingTheory.Henselian.Pair
public import StacksFrontier.RingTheory.Henselian.Pair.FiniteEtale
public import StacksFrontier.RingTheory.Idempotents.Lifting
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleProper

/-!
# Finite étale covers of a henselian pair

For a henselian pair `(A, I)`, pullback along the closed immersion
`Spec (A ⧸ I) ⟶ Spec A` induces an equivalence between the categories of finite étale schemes
over the two spectra.

## Main results

* `AlgebraicGeometry.finiteEtaleBaseChange_isEquivalence_of_henselianPair` states Gabber's
  equivalence for a henselian pair.

## Implementation notes

Finite étale schemes over a base are represented by `MorphismProperty.Over` for the intersection
of the finite and étale morphism properties, and their restriction is the canonical pullback
functor. The theorem records that this pullback functor itself is an equivalence, rather than
asserting only an abstract equivalence of its source and target categories. The affine case is
reduced to finite étale algebras through `finiteEtaleSpec`, and the quotient map is converted
contravariantly to the morphism `Spec (A ⧸ I) ⟶ Spec A`.

## References

* [Stacks Project, Tag 09ZS](https://stacks.math.columbia.edu/tag/09ZS)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

section

/-- The spectrum of an algebra is finite étale over the base iff the algebra is finite étale. -/
private lemma finiteEtale_specMap_algebraMap_iff (R S : Type u) [CommRing R] [CommRing S]
    [Algebra R S] :
    finiteEtale.{u} (Spec.map (CommRingCat.ofHom (algebraMap R S))) ↔
      Module.Finite R S ∧ Algebra.Etale R S := by
  change IsFinite _ ∧ Etale _ ↔ _
  rw [IsFinite.SpecMap_iff, HasRingHomProperty.Spec_iff (P := @Etale),
    CommRingCat.hom_ofHom, RingHom.finite_algebraMap, RingHom.etale_algebraMap]

/-- The spectrum of an algebra map is a morphism of schemes over the base. -/
private lemma specMap_comp_algebraMap (R : Type u) [CommRing R]
    {B C : (CommAlgCat.FiniteEtale.{u} R)ᵒᵖ} (f : B ⟶ C) :
    Spec.map (CommRingCat.ofHom f.unop.hom.hom.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R ↑(C.unop.obj))) =
      Spec.map (CommRingCat.ofHom (algebraMap R ↑(B.unop.obj))) := by
  rw [← Spec.map_comp]
  apply Spec.map_inj.mpr
  apply CommRingCat.hom_ext
  ext r
  exact f.unop.hom.hom.commutes r

/-- The affine spectrum construction, restricted to finite étale algebras. -/
private noncomputable def finiteEtaleSpec (R : Type u) [CommRing R] :
    (CommAlgCat.FiniteEtale.{u} R)ᵒᵖ ⥤ FiniteEtaleOver (Spec (.of R)) where
  obj B := MorphismProperty.Over.mk ⊤
    (Spec.map (CommRingCat.ofHom (algebraMap R B.unop.obj)))
    ((finiteEtale_specMap_algebraMap_iff R B.unop.obj).mpr ⟨inferInstance, inferInstance⟩)
  map {B C} f := MorphismProperty.Over.homMk
      (Spec.map (CommRingCat.ofHom f.unop.hom.hom)) (specMap_comp_algebraMap R f)
  map_id B := by
    apply MorphismProperty.Over.Hom.ext
    change Spec.map (CommRingCat.ofHom (𝟙 B).unop.hom.hom.toRingHom) = 𝟙 _
    simp
  map_comp f g := by
    apply MorphismProperty.Over.Hom.ext
    change Spec.map (CommRingCat.ofHom (f ≫ g).unop.hom.hom.toRingHom) =
      Spec.map (CommRingCat.ofHom f.unop.hom.hom.toRingHom) ≫
        Spec.map (CommRingCat.ofHom g.unop.hom.hom.toRingHom)
    simp [← Spec.map_comp, ← CommRingCat.ofHom_comp, AlgHom.comp_toRingHom]

private lemma finiteEtaleSpec_faithful (R : Type u) [CommRing R] :
    (finiteEtaleSpec R).Faithful where
  map_injective {X Y} {f g} h := by
    apply Quiver.Hom.unop_inj
    apply ObjectProperty.hom_ext
    apply CommAlgCat.hom_ext
    have hh : Spec.map (CommRingCat.ofHom f.unop.hom.hom.toRingHom) =
        Spec.map (CommRingCat.ofHom g.unop.hom.hom.toRingHom) :=
      congrArg (fun k => k.left) h
    apply AlgHom.coe_ringHom_injective
    exact congrArg CommRingCat.Hom.hom (Spec.map_inj.mp hh)

private lemma finiteEtaleSpec_full (R : Type u) [CommRing R] :
    (finiteEtaleSpec R).Full where
  map_surjective {X Y} f := by
    let fl : Spec (CommRingCat.of ↑(X.unop.obj)) ⟶ Spec (CommRingCat.of ↑(Y.unop.obj)) := f.left
    have hfl : CommRingCat.ofHom (algebraMap R Y.unop.obj) ≫ Spec.preimage fl =
        CommRingCat.ofHom (algebraMap R X.unop.obj) := by
      apply Spec.map_inj.mp
      rw [Spec.map_comp, Spec.map_preimage]
      exact MorphismProperty.Over.w f
    let g : Y.unop.obj →+* X.unop.obj := (Spec.preimage fl).hom
    let ga : Y.unop.obj →ₐ[R] X.unop.obj :=
      ⟨g, RingHom.congr_fun (congrArg CommRingCat.Hom.hom hfl)⟩
    exact ⟨(ObjectProperty.homMk (CommAlgCat.ofHom ga)).op,
      MorphismProperty.Over.Hom.ext (Spec.map_preimage fl)⟩

private lemma finiteEtaleSpec_essSurj (R : Type u) [CommRing R] :
    (finiteEtaleSpec R).EssSurj := by
  refine ⟨fun X => ?_⟩
  have : IsFinite X.hom := X.prop.1
  have : Etale X.hom := X.prop.2
  have : IsAffine ((Functor.fromPUnit (Spec (CommRingCat.of R))).obj X.right) := by
    show IsAffine (Spec (CommRingCat.of R))
    infer_instance
  have : IsAffine X.left := isAffine_of_isAffineHom X.hom
  let φ : CommRingCat.of R ⟶ CommRingCat.of Γ(X.left, ⊤) :=
    Spec.preimage (X.left.isoSpec.inv ≫ X.hom)
  let : Algebra R Γ(X.left, ⊤) := φ.hom.toAlgebra
  obtain ⟨hfin, heta⟩ := (finiteEtale_specMap_algebraMap_iff R Γ(X.left, ⊤)).mp
    (by
      change finiteEtale (Spec.map φ)
      rw [Spec.map_preimage]
      exact ⟨inferInstance, inferInstance⟩)
  let B := CommAlgCat.FiniteEtale.of R Γ(X.left, ⊤)
  refine ⟨Opposite.op B, ⟨MorphismProperty.Over.isoMk X.left.isoSpec.symm ?_⟩⟩
  show X.left.isoSpec.inv ≫ X.hom = Spec.map φ
  rw [Spec.map_preimage]

private lemma finiteEtaleSpec_isEquivalence (R : Type u) [CommRing R] :
    (finiteEtaleSpec R).IsEquivalence := by
  have := finiteEtaleSpec_faithful R
  have := finiteEtaleSpec_full R
  have := finiteEtaleSpec_essSurj R
  exact Functor.IsEquivalence.mk

/-- The comparison isomorphisms between the two base-change constructions are natural. -/
private lemma specBaseChange_naturality (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    {B C : (CommAlgCat.FiniteEtale.{u} R)ᵒᵖ} (f : B ⟶ C) :
    Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.map (.id S S) f.unop.hom.hom).toRingHom) ≫
        ((pullbackSpecIso R S ↑(C.unop.obj)).symm ≪≫
          pullbackSymmetry (Spec.map (CommRingCat.ofHom (algebraMap R S)))
            (Spec.map (CommRingCat.ofHom (algebraMap R ↑(C.unop.obj))))).hom =
      ((pullbackSpecIso R S ↑(B.unop.obj)).symm ≪≫
          pullbackSymmetry (Spec.map (CommRingCat.ofHom (algebraMap R S)))
            (Spec.map (CommRingCat.ofHom (algebraMap R ↑(B.unop.obj))))).hom ≫
        pullback.lift
          (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R ↑(B.unop.obj))))
              (Spec.map (CommRingCat.ofHom (algebraMap R S))) ≫
            Spec.map (CommRingCat.ofHom f.unop.hom.hom.toRingHom))
          (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R ↑(B.unop.obj))))
            (Spec.map (CommRingCat.ofHom (algebraMap R S))))
          (by rw [Category.assoc, specMap_comp_algebraMap]; exact pullback.condition) := by
  apply pullback.hom_ext
  · simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, pullback.lift_fst,
      pullbackSymmetry_hom_comp_fst, pullbackSpecIso_inv_snd,
      pullbackSymmetry_hom_comp_fst_assoc, pullbackSpecIso_inv_snd_assoc]
    rw [← Spec.map_comp, ← Spec.map_comp]
    apply Spec.map_inj.mpr
    ext x
    simp
  · simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, pullback.lift_snd,
      pullbackSymmetry_hom_comp_snd, pullbackSpecIso_inv_fst]
    rw [← Spec.map_comp]
    apply Spec.map_inj.mpr
    ext x
    simp

/-- Spectrum carries extension of scalars to the canonical scheme pullback. -/
private noncomputable def finiteEtaleSpecBaseChangeIso
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] :
    (CommAlgCat.FiniteEtale.baseChange R S).op ⋙ finiteEtaleSpec S ≅
      finiteEtaleSpec R ⋙ MorphismProperty.Over.pullback finiteEtale.{u} ⊤
        (Spec.map (CommRingCat.ofHom (algebraMap R S))) :=
  NatIso.ofComponents (fun B => MorphismProperty.Over.isoMk
    ((pullbackSpecIso R S B.unop.obj).symm ≪≫ pullbackSymmetry _ _) (by
      change ((pullbackSpecIso R S ↑(B.unop.obj)).symm ≪≫
            pullbackSymmetry (Spec.map (CommRingCat.ofHom (algebraMap R S)))
              (Spec.map (CommRingCat.ofHom (algebraMap R ↑(B.unop.obj))))).hom ≫
          pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R ↑(B.unop.obj))))
            (Spec.map (CommRingCat.ofHom (algebraMap R S))) =
        Spec.map (CommRingCat.ofHom (algebraMap S (TensorProduct R S ↑(B.unop.obj))))
      simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc,
        pullbackSymmetry_hom_comp_snd, pullbackSpecIso_inv_fst'])) <|
    fun f => MorphismProperty.Over.Hom.ext (specBaseChange_naturality R S f)

private theorem isEquivalence_pullback_finiteEtaleProperty
    (A : Type u) [CommRing A] (I : Ideal A) (hI : HenselianPair A I) :
    (MorphismProperty.Over.pullback finiteEtale.{u} ⊤
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))).IsEquivalence := by
  have := finiteEtaleSpec_isEquivalence A
  have := finiteEtaleSpec_isEquivalence (A ⧸ I)
  have := isEquivalence_baseChange_quotient A I hI
  have := Functor.isEquivalence_of_iso (finiteEtaleSpecBaseChangeIso A (A ⧸ I))
  exact Functor.isEquivalence_of_comp_left (finiteEtaleSpec A) _

/-- For a henselian pair `(A, I)`, base change from `Spec A` to `Spec (A ⨸ I)` is an
equivalence on finite étale schemes. -/
@[stacks 09ZS,
  ega "IV 18.5.15" "more general",
  sga "7 XIII 1.2.1" "FÉt equivalence",
  sga "3 X 4.0" "ÉtCov(S)≃ÉtCov(S₀)", sga "4 XII 5.9bis" "X = S affine"]
public theorem finiteEtaleBaseChange_isEquivalence_of_henselianPair
    (A : Type u) [CommRing A] (I : Ideal A) (hI : HenselianPair A I) :
    (MorphismProperty.Over.pullback
      ((@IsFinite : MorphismProperty Scheme.{u}) ⊓ @Etale) ⊤
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))).IsEquivalence :=
  isEquivalence_pullback_finiteEtaleProperty A I hI

end

end AlgebraicGeometry
