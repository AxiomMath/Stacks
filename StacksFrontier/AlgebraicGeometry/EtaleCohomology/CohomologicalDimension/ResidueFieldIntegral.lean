module

public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import StacksFrontier.AlgebraicGeometry.Etale.FiniteEtaleIrreducibleCover0551c
public import StacksFrontier.AlgebraicGeometry.Scheme.BaseChange.Points
public import StacksFrontier.AlgebraicGeometry.Scheme.ResidueFieldMapFromSpec
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.QuasiFiniteAdjoinField
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Morphisms of schemes with integral residue field extensions

A morphism of schemes `f : X ⟶ Y` *has integral residue field extensions* when, for every point
`x` of `X`, the field extension `κ(f x) → κ(x)` is integral, equivalently algebraic. This file
proves the permanence properties the proof of [Stacks, Tag 0F0X] uses:

* the spectrum of a ring map whose residue field extensions at primes are integral has the
  property (`AlgebraicGeometry.isIntegral_residueFieldMap_Spec_map`);
* the property is stable under composition and holds for isomorphisms;
* it is stable under base change (`AlgebraicGeometry.isIntegral_residueFieldMap_pullback_snd`):
  a point of `X ×_S Y` comes from a prime of `κ(x) ⊗_{κ(s)} κ(y)`, which is integral over `κ(y)`
  when `κ(x)` is integral over `κ(s)`;
* along it the transcendence degree of residue fields over a base field does not grow
  (`AlgebraicGeometry.trdeg_residueField_le_of_isIntegral`).

## References

* [Stacks Project, Tag 0F0X](https://stacks.math.columbia.edu/tag/0F0X)
* [Stacks Project, Tag 01JT](https://stacks.math.columbia.edu/tag/01JT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TensorProduct

universe u v w

namespace AlgebraicGeometry

/-- If `g ∘ f` is integral and `g` is injective, then `f` is integral. -/
theorem RingHom.isIntegral_of_isIntegral_comp_of_injective {R : Type u} {S : Type v}
    {T : Type w} [CommRing R] [CommRing S] [CommRing T] (f : R →+* S) (g : S →+* T)
    (h : (g.comp f).IsIntegral) (hg : Function.Injective g) : f.IsIntegral := by
  let := f.toAlgebra
  let := g.toAlgebra
  let := (g.comp f).toAlgebra
  have : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact fun x => IsIntegral.tower_bot hg (h (g x))

/-- **A residue field map is integral as soon as the images of the ring are.** -/
theorem isIntegral_residueFieldMap_of_forall {R : Type u} {S : Type v} [CommRing R]
    [CommRing S] (φ : R →+* S) (P : Ideal S) [P.IsPrime]
    (h : ∀ s : S, (Ideal.ResidueField.map (P.comap φ) P φ rfl).IsIntegralElem
      (algebraMap S P.ResidueField s)) :
    (Ideal.ResidueField.map (P.comap φ) P φ rfl).IsIntegral := by
  let := (Ideal.ResidueField.map (P.comap φ) P φ rfl).toAlgebra
  intro z
  obtain ⟨a, s, -, rfl⟩ := IsFractionRing.div_surjective (A := S ⧸ P) z
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective s
  have ha : _root_.IsIntegral (P.comap φ).ResidueField (algebraMap S P.ResidueField a) := h a
  have hs : _root_.IsIntegral (P.comap φ).ResidueField (algebraMap S P.ResidueField s) := h s
  rw [IsScalarTower.algebraMap_apply S (S ⧸ P) P.ResidueField] at ha hs
  show _root_.IsIntegral _ _
  rw [div_eq_mul_inv]
  exact ha.mul hs.inv

/-- **An integral ring map has integral residue field extensions.** -/
theorem isIntegral_residueFieldMap_of_isIntegral {R : Type u} {S : Type v} [CommRing R]
    [CommRing S] (φ : R →+* S) (hφ : φ.IsIntegral) (P : Ideal S) [P.IsPrime] :
    (Ideal.ResidueField.map (P.comap φ) P φ rfl).IsIntegral := by
  refine isIntegral_residueFieldMap_of_forall φ P fun s => ?_
  obtain ⟨p, hmon, hp⟩ := hφ s
  refine ⟨p.map (algebraMap R (P.comap φ).ResidueField), hmon.map _, ?_⟩
  rw [Polynomial.eval₂_map]
  have hc : (Ideal.ResidueField.map (P.comap φ) P φ rfl).comp
      (algebraMap R (P.comap φ).ResidueField) = (algebraMap S P.ResidueField).comp φ := by
    ext r
    simp
  rw [hc, ← Polynomial.hom_eval₂, hp, map_zero]

/-- An isomorphism of commutative rings is integral. -/
private theorem isIntegral_hom_of_isIso {A B : CommRingCat.{u}} (e : A ⟶ B) [IsIso e] :
    e.hom.IsIntegral :=
  RingHom.isIntegral_of_surjective _ (ConcreteCategory.bijective_of_isIso e).2

/-- Composing an integral map of rings with isomorphisms on both sides gives an integral map. -/
theorem isIntegral_hom_iso_comp_comp_iso {A B C D : CommRingCat.{u}} (e₁ : A ≅ B) (g : B ⟶ C)
    (e₂ : C ≅ D) (hg : g.hom.IsIntegral) : (e₁.hom ≫ g ≫ e₂.hom).hom.IsIntegral := by
  simp only [CommRingCat.hom_comp]
  exact RingHom.IsIntegral.trans _ _ (isIntegral_hom_of_isIso e₁.hom)
    (RingHom.IsIntegral.trans _ _ hg (isIntegral_hom_of_isIso e₂.hom))

variable {X Y Z : Scheme.{u}}

/-- **The spectrum of a ring map with integral residue field extensions has integral residue
field extensions.** The residue field map of `Spec.map φ` at a prime `q` is, up to the
identifications `AlgebraicGeometry.Scheme.Spec.residueFieldIso`, the residue field map of `φ`
(`AlgebraicGeometry.algebraMap_Spec_map_residueFieldMap`). -/
theorem isIntegral_residueFieldMap_Spec_map {R S : CommRingCat.{u}} (φ : R ⟶ S)
    (h : ∀ (P : Ideal S) [P.IsPrime],
      (Ideal.ResidueField.map (P.comap φ.hom) P φ.hom rfl).IsIntegral)
    (q : PrimeSpectrum S) : ((Spec.map φ).residueFieldMap q).hom.IsIntegral := by
  set z : PrimeSpectrum R := (Spec.map φ) q with hz
  have hcomp := algebraMap_Spec_map_residueFieldMap φ q z hz.symm
  let g : CommRingCat.of z.asIdeal.ResidueField ⟶ CommRingCat.of q.asIdeal.ResidueField :=
    (Scheme.Spec.residueFieldIso R z).inv ≫ ((Spec R).residueFieldCongr hz.symm).inv ≫
      (Spec.map φ).residueFieldMap q ≫ (Scheme.Spec.residueFieldIso S q).hom
  have hzq : z.asIdeal = q.asIdeal.comap φ.hom := by
    rw [hz]
    rfl
  have hg : g.hom = Ideal.ResidueField.map z.asIdeal q.asIdeal φ.hom hzq := by
    apply Ideal.ResidueField.ringHom_ext
    have := congrArg CommRingCat.Hom.hom hcomp
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom] at this
    rw [Ideal.ResidueField.map]
    ext r
    have h1 := congrArg (fun F => F r) this
    simp only [RingHom.comp_apply] at h1
    simp only [RingHom.comp_apply, g, CommRingCat.hom_comp]
    rw [h1]
    simp [Ideal.ResidueField.map_algebraMap]
  have hgint : g.hom.IsIntegral := by
    rw [hg]
    have key : ∀ (I : Ideal R) [I.IsPrime] (hI : I = q.asIdeal.comap φ.hom),
        (Ideal.ResidueField.map I q.asIdeal φ.hom hI).IsIntegral := by
      intro I _ hI
      subst hI
      exact h _
    exact key _ hzq
  -- `(Spec.map φ).residueFieldMap q` is `g` up to isomorphisms
  have heq : (Spec.map φ).residueFieldMap q =
      ((Spec R).residueFieldCongr hz.symm).hom ≫ (Scheme.Spec.residueFieldIso R z).hom ≫ g ≫
        (Scheme.Spec.residueFieldIso S q).inv := by
    simp [g]
    rfl
  rw [heq]
  simpa using isIntegral_hom_iso_comp_comp_iso
    (((Spec R).residueFieldCongr hz.symm) ≪≫ Scheme.Spec.residueFieldIso R z) g
    (Scheme.Spec.residueFieldIso S q).symm hgint

/-- **Integral residue field extensions compose.** -/
theorem isIntegral_residueFieldMap_comp (f : X ⟶ Y) (g : Y ⟶ Z) (x : X)
    (hf : (f.residueFieldMap x).hom.IsIntegral) (hg : (g.residueFieldMap (f x)).hom.IsIntegral) :
    ((f ≫ g).residueFieldMap x).hom.IsIntegral := by
  rw [Scheme.residueFieldMap_comp]
  exact RingHom.IsIntegral.trans _ _ hg hf

/-- **An isomorphism of residue fields is integral.** -/
theorem isIntegral_residueFieldMap_of_isIso (f : X ⟶ Y) (x : X) [IsIso (f.residueFieldMap x)] :
    (f.residueFieldMap x).hom.IsIntegral :=
  isIntegral_hom_of_isIso _

/-- **In a pushout of rings, the cobase change of an integral map is integral.** The pushout is
the tensor product, which is integral over the factor it is a base change of
(`Algebra.IsIntegral.tensorProduct`). -/
@[ega "II 6.3.3" "First step of the proof"]
theorem isIntegral_inr_of_isPushout {A B C P : CommRingCat.{u}} {f : A ⟶ B} {g : A ⟶ C}
    {inl : B ⟶ P} {inr : C ⟶ P} (h : IsPushout f g inl inr) (hf : f.hom.IsIntegral) :
    inr.hom.IsIntegral := by
  let := f.hom.toAlgebra
  let := g.hom.toAlgebra
  have : Algebra.IsIntegral A B := ⟨hf⟩
  have ht := CommRingCat.isPushout_tensorProduct A C B
  let e := ht.isoIsPushout _ _ h.flip
  rw [← ht.inl_isoIsPushout_hom _ _ h.flip, CommRingCat.hom_comp, CommRingCat.hom_ofHom]
  refine RingHom.IsIntegral.trans _ _ ?_ (isIntegral_hom_of_isIso e.hom)
  exact fun x => Algebra.IsIntegral.isIntegral (R := C) x

/-- The residue field extensions of the second projection at the points coming from the
spectrum of `κ(x) ⊗_{κ(s)} κ(y)`. -/
private theorem isIntegral_residueFieldMap_pullback_snd_specTensorTo {S : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S) (T : Scheme.Pullback.Triplet f g)
    (hT : (f.residueFieldMap T.x).hom.IsIntegral) (p : Spec T.tensor) :
    ((pullback.snd f g).residueFieldMap (T.SpecTensorTo p)).hom.IsIntegral := by
  -- `κ(y) → T.tensor` is integral
  have hinr : T.tensorInr.hom.IsIntegral := by
    refine isIntegral_inr_of_isPushout (IsPushout.of_hasPushout _ _) ?_
    rw [CommRingCat.hom_comp]
    exact RingHom.IsIntegral.trans _ _ (isIntegral_hom_of_isIso _) hT
  -- the composite `κ(y) → κ(q p) → κ_{Spec T.tensor}(p)` is integral
  have hcomp : ((T.SpecTensorTo ≫ pullback.snd f g).residueFieldMap p).hom.IsIntegral := by
    rw [Scheme.Hom.residueFieldMap_congr T.specTensorTo_snd p, CommRingCat.hom_comp]
    refine RingHom.IsIntegral.trans _ _ (isIntegral_hom_of_isIso _) ?_
    have := isIso_residueFieldMap_fromSpecResidueField Y T.y (Spec.map T.tensorInr p)
    refine isIntegral_residueFieldMap_comp _ _ p ?_
      (isIntegral_residueFieldMap_of_isIso _ _)
    exact isIntegral_residueFieldMap_Spec_map T.tensorInr
      (fun P _ => isIntegral_residueFieldMap_of_isIntegral _ hinr P) p
  rw [Scheme.residueFieldMap_comp] at hcomp
  exact RingHom.isIntegral_of_isIntegral_comp_of_injective
    ((pullback.snd f g).residueFieldMap (T.SpecTensorTo p)).hom
    (T.SpecTensorTo.residueFieldMap p).hom hcomp
    (RingHom.injective _)

/-- **Integral residue field extensions are stable under base change.** If `f : X ⟶ S` has
integral residue field extensions, so does the second projection `X ×_S Y ⟶ Y`: a point of the
fibre product comes from a prime of `κ(x) ⊗_{κ(s)} κ(y)`, whose residue field it maps into
isomorphically (Stacks 01JT), and that tensor product is integral over `κ(y)`. -/
theorem isIntegral_residueFieldMap_pullback_snd {S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (hf : ∀ x, (f.residueFieldMap x).hom.IsIntegral) (w : ↑(pullback f g)) :
    ((pullback.snd f g).residueFieldMap w).hom.IsIntegral := by
  have h := isIntegral_residueFieldMap_pullback_snd_specTensorTo f g
    (Scheme.Pullback.Triplet.ofPoint w) (hf _) (Scheme.Pullback.SpecOfPoint w)
  rwa [Scheme.Pullback.SpecTensorTo_SpecOfPoint] at h

/-- **Along a morphism with integral residue field extension at a point, the transcendence
degree over a base field does not grow.** For `i : W ⟶ X` over a field `K` and a point `w` with
`κ(i w) → κ(w)` integral, `trdeg_K κ(w) ≤ trdeg_K κ(i w)`. -/
theorem trdeg_residueField_le_of_isIntegral (K : Type u) [Field K] {W : Scheme.{u}}
    (gX : X ⟶ Spec (.of K)) (i : W ⟶ X) (w : W) (hw : (i.residueFieldMap w).hom.IsIntegral) :
    letI : Algebra K (X.residueField (i w)) :=
      ((Scheme.ΓSpecIso (.of K)).inv ≫ gX.appTop ≫ X.Γevaluation (i w)).hom.toAlgebra
    letI : Algebra K (W.residueField w) :=
      ((Scheme.ΓSpecIso (.of K)).inv ≫ (i ≫ gX).appTop ≫ W.Γevaluation w).hom.toAlgebra
    Algebra.trdeg K (W.residueField w) ≤ Algebra.trdeg K (X.residueField (i w)) := by
  let : Algebra K (X.residueField (i w)) :=
    ((Scheme.ΓSpecIso (.of K)).inv ≫ gX.appTop ≫ X.Γevaluation (i w)).hom.toAlgebra
  let : Algebra K (W.residueField w) :=
    ((Scheme.ΓSpecIso (.of K)).inv ≫ (i ≫ gX).appTop ≫ W.Γevaluation w).hom.toAlgebra
  let : Algebra (X.residueField (i w)) (W.residueField w) := (i.residueFieldMap w).hom.toAlgebra
  have : IsScalarTower K (X.residueField (i w)) (W.residueField w) := by
    apply IsScalarTower.of_algebraMap_eq'
    show ((Scheme.ΓSpecIso (.of K)).inv ≫ (i ≫ gX).appTop ≫ W.Γevaluation w).hom =
      (i.residueFieldMap w).hom.comp
        ((Scheme.ΓSpecIso (.of K)).inv ≫ gX.appTop ≫ X.Γevaluation (i w)).hom
    have hcat : (Scheme.ΓSpecIso (.of K)).inv ≫ (i ≫ gX).appTop ≫ W.Γevaluation w =
        (Scheme.ΓSpecIso (.of K)).inv ≫ gX.appTop ≫ X.Γevaluation (i w) ≫
          i.residueFieldMap w := by
      rw [Scheme.Hom.comp_appTop, Category.assoc, Scheme.Γevaluation_naturality i w]
    simpa [CommRingCat.hom_comp, RingHom.comp_assoc] using congrArg CommRingCat.Hom.hom hcat
  have : Algebra.IsIntegral (X.residueField (i w)) (W.residueField w) := ⟨hw⟩
  have h := trdeg_add_eq (R := K) (S := X.residueField (i w)) (A := W.residueField w)
  rw [trdeg_eq_zero (R := X.residueField (i w)) (A := W.residueField w), add_zero] at h
  exact h.symm.le

end AlgebraicGeometry

end
