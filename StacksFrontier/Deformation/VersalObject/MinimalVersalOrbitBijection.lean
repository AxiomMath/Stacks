module

public import StacksFrontier.Deformation.BaseCategory.DerivationSplitting
public import StacksFrontier.Deformation.TangentSpace.DerivationsDescend
public import StacksFrontier.Deformation.VersalObject.MinimalVersalDerivationOrbits
public import StacksFrontier.Deformation.VersalObject.MinimalVersalDescent

/-!
# A minimal versal formal object has bijective differential on orbits

Let `ξ` be a minimal versal formal object of a predeformation category satisfying Schlessinger's
condition (S2). Its differential, presented as the relation
`Deformation.derivationDifferentialGraph`, is a well-defined map, is surjective, is equivariant
for the translation action of `Der_Λ(k, k)`, and induces a bijection on `Der_Λ(k, k)`-orbits.

## Main results

* `Deformation.minimalVersal_hasBijectiveDifferentialOnDerivationOrbits`: the differential of a
  minimal versal formal object induces a bijection on `Der_Λ(k, k)`-orbits.
* `Deformation.eq_zero_on_maximalIdeal_of_derivationToTangent_eq`: a derivation killed by the
  differential of a minimal versal formal object vanishes on the maximal ideal.
* `Deformation.exists_eq_add_of_eq_action`: two derivations of the base of a minimal versal
  formal object whose tangent vectors differ by a translation differ by a residue-field
  derivation.
* `Deformation.exists_derivationSplittingPullback`: the splitting of a square-zero object of
  `𝒞_Λ` along a derivation, as a pullback square.
* `Deformation.isPullback_of_jointly_bijective`: a square of `𝒞_Λ` is a pullback as soon as its
  two maps out of the apex separate points and realise every compatible pair.

## References

* [Stacks Project, Tag 06T8](https://stacks.math.columbia.edu/tag/06T8)
* [Stacks Project, Tag 06T6](https://stacks.math.columbia.edu/tag/06T6)
* [Stacks Project, Tag 06T2](https://stacks.math.columbia.edu/tag/06T2)
* [Stacks Project, Tag 06IS](https://stacks.math.columbia.edu/tag/06IS)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor IsLocalRing

namespace Deformation

section Augmentation

universe u v w

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

/-- The augmentation of an object of `𝒞_Λ` onto the fixed residue field. -/
public noncomputable def aug (A : ArtinianLocalAlgCat.{u, max v w, w} Λ k) : A →ₐ[Λ] k :=
  (residueFieldCoordinates.{u, v, w} (Λ := Λ) (k := k)).toAlgHom.comp
    (residueMorphism.{u, v, w} A).hom

/-- The augmentation computes the chosen residue-field identification. -/
public theorem aug_spec (A : ArtinianLocalAlgCat.{u, max v w, w} Λ k) (a : A) :
    A.residueEquiv (residue A a) = aug.{u, v, w} A a :=
  ((residueMorphism.{u, v, w} A).residue_comm a).symm.trans
    (residueFieldCoordinates_residue.{u, v, w} _)

/-- An element of an object of `𝒞_Λ` is a unit exactly when its augmentation is nonzero. -/
public theorem aug_eq_zero_iff_not_isUnit (A : ArtinianLocalAlgCat.{u, max v w, w} Λ k) (a : A) :
    aug.{u, v, w} A a = 0 ↔ ¬ IsUnit a := by
  rw [← aug_spec, ← residue_ne_zero_iff_isUnit]
  exact ⟨fun h hne => hne (A.residueEquiv.injective (by rw [h, map_zero])),
    fun h => by rw [not_not] at h; rw [h, map_zero]⟩

/-- The augmentation is surjective. -/
public theorem aug_surjective (A : ArtinianLocalAlgCat.{u, max v w, w} Λ k) :
    Function.Surjective (aug.{u, v, w} A) := by
  intro c
  obtain ⟨a, ha⟩ := residue_surjective (A.residueEquiv.symm c)
  exact ⟨a, by rw [← aug_spec, ha, A.residueEquiv.apply_symm_apply]⟩

/-- A `Λ`-algebra map compatible with the augmentations is local. -/
public theorem isLocalHom_of_aug_comm {A B : ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    (f : A →ₐ[Λ] B) (hf : ∀ a : A, aug.{u, v, w} B (f a) = aug.{u, v, w} A a) :
    IsLocalHom f.toRingHom := by
  refine ⟨fun a ha => ?_⟩
  by_contra hcon
  exact (aug_eq_zero_iff_not_isUnit B (f a)).mp
    ((hf a).trans ((aug_eq_zero_iff_not_isUnit A a).mpr hcon)) ha

/-- A `Λ`-algebra map compatible with the augmentations is a morphism of `𝒞_Λ`. -/
public noncomputable def homOfAugComm {A B : ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    (f : A →ₐ[Λ] B) (hf : ∀ a : A, aug.{u, v, w} B (f a) = aug.{u, v, w} A a) : A ⟶ B where
  hom := f
  isLocal := isLocalHom_of_aug_comm f hf
  residue_comm := fun a => by rw [aug_spec, aug_spec, hf a]

/-- A morphism of `𝒞_Λ` respects the augmentations. -/
public theorem aug_hom {A B : ArtinianLocalAlgCat.{u, max v w, w} Λ k} (f : A ⟶ B) (a : A) :
    aug.{u, v, w} B (f.hom a) = aug.{u, v, w} A a := by
  rw [← aug_spec, ← aug_spec, f.residue_comm]

/-- The augmentation of the dual-number object is the first coordinate. -/
public theorem aug_dualNumbers (z : artinianDualNumbers.{u, w, v} Λ k) :
    aug.{u, v, w} (artinianDualNumbers.{u, w, v} Λ k) z = TrivSqZeroExt.fst z := by
  rw [← aug_spec]
  exact squareZeroExtensionArtinian_residue Λ k _ z

/-- The residue morphism reads the augmentation. -/
public theorem residueMorphism_hom_down (A : ArtinianLocalAlgCat.{u, max v w, w} Λ k) (a : A) :
    ULift.down ((residueMorphism.{u, v, w} A).hom a) = aug.{u, v, w} A a := rfl

/-- The residue morphism is surjective. -/
public theorem residueMorphism_surjective (A : ArtinianLocalAlgCat.{u, max v w, w} Λ k) :
    Function.Surjective (residueMorphism.{u, v, w} A).hom := by
  intro y
  obtain ⟨a, ha⟩ := aug_surjective.{u, v, w} A (ULift.down y)
  exact ⟨a, ULift.down_injective (by rw [residueMorphism_hom_down, ha])⟩

/-- The quotient map onto the `n`-th positive adic truncation. -/
public noncomputable def truncationHom (R : CompleteLocalAlgCat.{u, v, w} Λ k) (n : ℕ) :
    R →ₐ[Λ] AdicTruncation.obj R n :=
  Ideal.Quotient.mkₐ Λ (AdicTruncation.ideal R n)

/-- The quotient map onto a truncation is surjective. -/
public theorem truncationHom_surjective (R : CompleteLocalAlgCat.{u, v, w} Λ k) (n : ℕ) :
    Function.Surjective (truncationHom R n) :=
  Ideal.Quotient.mk_surjective

/-- The kernel of the quotient map onto a truncation is the defining ideal. -/
public theorem truncationHom_eq_zero_iff (R : CompleteLocalAlgCat.{u, v, w} Λ k) (n : ℕ) (r : R) :
    truncationHom R n r = 0 ↔ r ∈ AdicTruncation.ideal R n :=
  Ideal.Quotient.eq_zero_iff_mem

/-- The augmentation of a complete local algebra is its residue map. -/
public theorem residueHom_apply (R : CompleteLocalAlgCat.{u, v, w} Λ k) (r : R) :
    residueHom R r = R.residueEquiv (residue R r) := rfl

/-- The residue map kills the maximal ideal. -/
private theorem residueHom_eq_zero_of_mem_maximalIdeal (R : CompleteLocalAlgCat.{u, v, w} Λ k)
    {r : R} (hr : r ∈ maximalIdeal (R : Type _)) : residueHom R r = 0 := by
  rw [residueHom_apply, (residue_eq_zero_iff r).mpr hr, map_zero]

/-- Truncating does not change augmentations. -/
public theorem aug_truncationHom (R : CompleteLocalAlgCat.{u, max v w, w} Λ k) (n : ℕ) (r : R) :
    aug.{u, v, w} (AdicTruncation.obj R n) (truncationHom R n r) = residueHom R r := by
  rw [← aug_spec, residueHom_apply]
  exact AdicTruncation.residueEquiv_residue_mk R n r

/-- Level one of a complete local algebra has square-zero maximal ideal. -/
public theorem maximalIdeal_sq_truncation (R : CompleteLocalAlgCat.{u, v, w} Λ k) :
    maximalIdeal (AdicTruncation.obj R 1) ^ 2 = ⊥ := by
  refine le_antisymm ?_ bot_le
  rw [pow_two]
  refine Ideal.mul_le.mpr ?_
  intro x hx y hy
  obtain ⟨a, rfl⟩ := truncationHom_surjective R 1 x
  obtain ⟨b, rfl⟩ := truncationHom_surjective R 1 y
  have hmem : ∀ {c : R}, truncationHom R 1 c ∈ maximalIdeal (AdicTruncation.obj R 1) →
      c ∈ maximalIdeal (R : Type _) := fun {c} hc => by
    rw [mem_maximalIdeal] at hc ⊢
    exact fun hu => hc (hu.map (truncationHom R 1))
  have ha := hmem hx
  have hb := hmem hy
  have hab : a * b ∈ AdicTruncation.ideal R 1 := by
    show a * b ∈ maximalIdeal (R : Type _) ^ (1 + 1)
    rw [show (1 : ℕ) + 1 = 2 from rfl, pow_two]
    exact Ideal.mul_mem_mul ha hb
  have h0 : truncationHom R 1 (a * b) = 0 := (truncationHom_eq_zero_iff R 1 _).mpr hab
  rw [map_mul] at h0
  simpa using h0

/-- A dual-number point of `R` whose algebra map kills `m_R²` descends to level one. -/
public theorem exists_descend_dualNumberPoint
    (R : CompleteLocalAlgCat.{u, max v w, w} Λ k)
    (α : (restrictedCoyoneda R).obj (artinianDualNumbers.{u, w, v} Λ k))
    (hker : ∀ z : R, z ∈ AdicTruncation.ideal R 1 → α.hom z = 0) :
    ∃ χ : (AdicTruncation.obj R 1 : ArtinianLocalAlgCat.{u, max v w, w} Λ k) ⟶
        artinianDualNumbers.{u, w, v} Λ k,
      ∀ r : R, χ.hom (truncationHom R 1 r) = α.hom r := by
  let χ₀ : (AdicTruncation.obj R 1 : ArtinianLocalAlgCat.{u, max v w, w} Λ k) →ₐ[Λ]
      artinianDualNumbers.{u, w, v} Λ k :=
    Ideal.Quotient.liftₐ (AdicTruncation.ideal R 1) α.hom hker
  have hfac : ∀ r : R, χ₀ (truncationHom R 1 r) = α.hom r := fun _ => rfl
  have hf : ∀ a, aug.{u, v, w} (artinianDualNumbers.{u, w, v} Λ k) (χ₀ a) =
      aug.{u, v, w} (AdicTruncation.obj R 1) a := by
    intro a
    obtain ⟨r, rfl⟩ := truncationHom_surjective R 1 a
    rw [hfac r, aug_truncationHom]
    exact (aug_spec _ _).symm.trans (α.residue_comm r)
  exact ⟨homOfAugComm χ₀ hf, hfac⟩

/-- The square-zero component of a dual-number point of an Artinian object is a derivation
over the augmentation. -/
public theorem exists_pointDerivation (A : ArtinianLocalAlgCat.{u, max v w, w} Λ k)
    (χ : A ⟶ artinianDualNumbers.{u, w, v} Λ k) :
    ∃ D : A →ₗ[Λ] k,
      (∀ a b : A, D (a * b) = aug.{u, v, w} A a * D b + aug.{u, v, w} A b * D a) ∧
        (∀ a : A, D a = ULift.down (TrivSqZeroExt.snd (χ.hom a))) := by
  let S : CompleteLocalAlgCat.{u, max v w, w} Λ k := artinianToComplete.obj A
  let : Algebra S k := (residueHom S).toRingHom.toAlgebra
  let d : Derivation Λ S k :=
    tangentSpaceDerivationsLinearEquiv.{u, v, w} S (artinianToComplete.map χ)
  have hd : ∀ a : S, d a = ULift.down (TrivSqZeroExt.snd (χ.hom a)) := fun a =>
    tangentSpaceDerivationsLinearEquiv_apply.{u, v, w} S (artinianToComplete.map χ) a
  refine ⟨d.toLinearMap, ?_, hd⟩
  intro a b
  have h := d.leibniz a b
  rw [Algebra.smul_def, Algebra.smul_def] at h
  show d (a * b) = _ * d b + _ * d a
  rw [h]
  congr 1

/-- A commuting square of `𝒞_Λ` whose two maps out of the apex jointly separate its points
and realise every compatible pair is a pullback square. -/
public theorem isPullback_of_jointly_bijective
    {W X Y Z : ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    (u : W ⟶ X) (v' : W ⟶ Y) (f : X ⟶ Z) (g : Y ⟶ Z)
    (hf : Function.Surjective f.hom)
    (hcomm : u ≫ f = v' ≫ g)
    (hinj : ∀ a b : W, u.hom a = u.hom b → v'.hom a = v'.hom b → a = b)
    (hsurj : ∀ (x : X) (y : Y), f.hom x = g.hom y → ∃ a : W, u.hom a = x ∧ v'.hom a = y) :
    CategoryTheory.IsPullback u v' f g := by
  classical
  have hpb := ArtinianLocalAlgCat.isPullback_of_surjective f g (Or.inl hf)
  set F := ArtinianLocalAlgCat.pullbackFst_of_surjective f g (Or.inl hf) with hF
  set S := ArtinianLocalAlgCat.pullbackSnd_of_surjective f g (Or.inl hf) with hS
  set ι := hpb.lift u v' hcomm with hι
  have hu : ∀ x : W, F.hom (ι.hom x) = u.hom x :=
    fun x => congrArg (fun q : W ⟶ X => q.hom x) (hpb.lift_fst u v' hcomm)
  have hv : ∀ x : W, S.hom (ι.hom x) = v'.hom x :=
    fun x => congrArg (fun q : W ⟶ Y => q.hom x) (hpb.lift_snd u v' hcomm)
  have hw : ∀ z : ArtinianLocalAlgCat.pullbackObj_of_surjective f g (Or.inl hf),
      f.hom (F.hom z) = g.hom (S.hom z) :=
    fun z => congrArg (fun q : _ ⟶ Z => q.hom z) hpb.w
  have hext : ∀ z z' : ArtinianLocalAlgCat.pullbackObj_of_surjective f g (Or.inl hf),
      F.hom z = F.hom z' → S.hom z = S.hom z' → z = z' := by
    intro z z' h1 h2
    rw [hF, ArtinianLocalAlgCat.pullbackFst_of_surjective_hom] at h1
    rw [hS, ArtinianLocalAlgCat.pullbackSnd_of_surjective_hom] at h2
    exact Subtype.ext (Prod.ext h1 h2)
  have hinjι : Function.Injective ι.hom := fun a b hab =>
    hinj a b (by rw [← hu a, ← hu b, hab]) (by rw [← hv a, ← hv b, hab])
  have hsurjι : Function.Surjective ι.hom := by
    intro z
    obtain ⟨a, ha1, ha2⟩ := hsurj (F.hom z) (S.hom z) (hw z)
    exact ⟨a, hext _ _ (by rw [hu a, ha1]) (by rw [hv a, ha2])⟩
  have hiso : IsIso ι := ArtinianLocalAlgCat.isIso_of_bijective_hom ι ⟨hinjι, hsurjι⟩
  refine hpb.of_iso' (asIso ι) (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · simp only [Iso.refl_hom, Category.comp_id]
    exact hpb.lift_fst u v' hcomm
  · simp only [Iso.refl_hom, Category.comp_id]
    exact hpb.lift_snd u v' hcomm
  · simp
  · simp

/-- The splitting of a square-zero object of `𝒞_Λ` along a derivation presents it as the
fibre product of the kernel subobject with the dual numbers over the residue-field object. -/
public theorem exists_derivationSplittingPullback
    (A : ArtinianLocalAlgCat.{u, max v w, w} Λ k)
    (hA : maximalIdeal (A : Type _) ^ 2 = ⊥)
    (χ : A ⟶ artinianDualNumbers.{u, w, v} Λ k)
    (D : A →ₗ[Λ] k)
    (hD : ∀ a b : A, D (a * b) = aug.{u, v, w} A a * D b + aug.{u, v, w} A b * D a)
    (hDχ : ∀ a : A, D a = ULift.down (TrivSqZeroExt.snd (χ.hom a)))
    {t : A} (ht : t ∈ maximalIdeal (A : Type _)) (hDt : D t = 1) :
    ∃ (A' : ArtinianLocalAlgCat.{u, max v w, w} Λ k) (ψ : A ⟶ A'),
      CategoryTheory.IsPullback χ ψ
          (residueMorphism.{u, v, w} (artinianDualNumbers.{u, w, v} Λ k))
          (residueMorphism.{u, v, w} A') ∧
        ∀ σ : A' ⟶ A, σ ≫ ψ = 𝟙 A' → ¬ Function.Surjective σ.hom := by
  classical
  obtain ⟨A', ψ, j, hjψ, hψsurj, hjinj, hjker, hunique, hnosec⟩ :=
    exists_derivationSplitting A hA (aug.{u, v, w} A) (aug_spec.{u, v, w} A) D hD ht hDt
  refine ⟨A', ψ, ?_, hnosec⟩
  refine isPullback_of_jointly_bijective χ ψ
    (residueMorphism.{u, v, w} (artinianDualNumbers.{u, w, v} Λ k))
    (residueMorphism.{u, v, w} A')
    (residueMorphism_surjective.{u, v, w} _)
    (hom_residueFieldObject_ext.{u, v, w} _ _) ?_ ?_
  · intro a b hu hv
    obtain ⟨c, -, hc⟩ := hunique (ψ.hom a) (D a)
    rw [hc a ⟨rfl, rfl⟩, hc b ⟨hv.symm, by rw [hDχ a, hDχ b, hu]⟩]
  · intro x y hxy
    obtain ⟨a, ⟨ha1, ha2⟩, -⟩ := hunique y (ULift.down (TrivSqZeroExt.snd x))
    refine ⟨a, ?_, ha1⟩
    have hd1 : aug.{u, v, w} (artinianDualNumbers.{u, w, v} Λ k) x =
        aug.{u, v, w} A' y := by
      have h := congrArg ULift.down hxy
      rwa [residueMorphism_hom_down, residueMorphism_hom_down] at h
    refine @TrivSqZeroExt.ext k ↑(FGModuleCat.of k (ULift.{v, w} k)) (χ.hom a) x ?_ ?_
    · rw [← aug_dualNumbers.{u, v, w}, ← aug_dualNumbers.{u, v, w},
        aug_hom χ a, hd1, ← ha1, aug_hom ψ a]
    · exact ULift.down_injective ((hDχ a).symm.trans ha2)

/-- The dual numbers over `k`, lifted into the carrier universe of `𝒞_Λ`. -/
public noncomputable def dualNumbersUp :
    DualNumber k →ₐ[Λ] (artinianDualNumbers.{u, w, v} Λ k) where
  toFun x := ⟨TrivSqZeroExt.fst x, ⟨TrivSqZeroExt.snd x⟩⟩
  map_zero' := by
    apply TrivSqZeroExt.ext
    · rfl
    · apply ULift.ext; rfl
  map_one' := by
    apply TrivSqZeroExt.ext
    · rfl
    · apply ULift.ext; rfl
  map_add' x y := by
    apply TrivSqZeroExt.ext
    · rfl
    · apply ULift.ext
      rfl
  map_mul' x y := by
    apply TrivSqZeroExt.ext
    · change TrivSqZeroExt.fst x * TrivSqZeroExt.fst y = _
      rfl
    · apply ULift.ext
      change TrivSqZeroExt.fst x * TrivSqZeroExt.snd y
          + TrivSqZeroExt.snd x * TrivSqZeroExt.fst y =
        TrivSqZeroExt.fst x * TrivSqZeroExt.snd y
          + TrivSqZeroExt.fst y * TrivSqZeroExt.snd x
      ring
  commutes' r := by
    apply TrivSqZeroExt.ext
    · rfl
    · apply ULift.ext; rfl

/-- Lifting the dual numbers does not change the first coordinate. -/
public theorem dualNumbersUp_fst (x : DualNumber k) :
    TrivSqZeroExt.fst (dualNumbersUp.{u, v, w} (Λ := Λ) (k := k) x) = TrivSqZeroExt.fst x := rfl

/-- Lifting the dual numbers is bijective. -/
public theorem dualNumbersUp_bijective :
    Function.Bijective (dualNumbersUp.{u, v, w} (Λ := Λ) (k := k)) := by
  constructor
  · intro x y hxy
    refine TrivSqZeroExt.ext ?_ ?_
    · exact congrArg
        (fun z : artinianDualNumbers.{u, w, v} Λ k => TrivSqZeroExt.fst z) hxy
    · exact congrArg (fun z => ULift.down (TrivSqZeroExt.snd z)) hxy
  · intro z
    exact ⟨⟨TrivSqZeroExt.fst z, ULift.down (TrivSqZeroExt.snd z)⟩, by
      refine TrivSqZeroExt.ext rfl ?_
      exact ULift.ext rfl⟩

/-- The dual-number object of `𝒞_Λ` is `Λ`-algebra isomorphic to the dual numbers. -/
public noncomputable def dualNumbersEquiv :
    (artinianDualNumbers.{u, w, v} Λ k) ≃ₐ[Λ] DualNumber k :=
  (AlgEquiv.ofBijective (dualNumbersUp.{u, v, w} (Λ := Λ) (k := k))
    dualNumbersUp_bijective.{u, v, w}).symm

/-- The identification with the dual numbers preserves the first coordinate. -/
public theorem dualNumbersEquiv_fst (z : artinianDualNumbers.{u, w, v} Λ k) :
    TrivSqZeroExt.fst (dualNumbersEquiv z) = TrivSqZeroExt.fst z := by
  have h := (AlgEquiv.ofBijective (dualNumbersUp.{u, v, w} (Λ := Λ) (k := k))
    dualNumbersUp_bijective.{u, v, w}).apply_symm_apply z
  exact (dualNumbersUp_fst _).symm.trans (congrArg
    (fun y : artinianDualNumbers.{u, w, v} Λ k => TrivSqZeroExt.fst y) h)

/-- The residue morphism of the dual-number object is the dual-number projection. -/
public theorem isDualNumberProjection_residueMorphism_dualNumbers :
    IsDualNumberProjection
      (residueMorphism.{u, v, w} (artinianDualNumbers.{u, w, v} Λ k)) := by
  refine ⟨residueFieldCoordinates.{u, v, w} (Λ := Λ) (k := k), dualNumbersEquiv, ?_⟩
  ext z
  show aug.{u, v, w} (artinianDualNumbers.{u, w, v} Λ k) z =
    TrivSqZeroExt.fst (dualNumbersEquiv z)
  rw [dualNumbersEquiv_fst]
  exact aug_dualNumbers.{u, v, w} z

/-- The inclusion of the residue-field object into the dual-number object. -/
public noncomputable def dualNumbersInclusion :
    residueFieldObject.{u, v, w} Λ k ⟶ artinianDualNumbers.{u, w, v} Λ k :=
  homOfAugComm
    { toFun := fun c => ⟨ULift.down c, 0⟩
      map_one' := rfl
      map_mul' := fun x y => by
        refine TrivSqZeroExt.ext rfl ?_
        apply ULift.ext
        change (0 : k) = ULift.down x * 0 + ULift.down y * 0
        ring
      map_zero' := rfl
      map_add' := fun x y => by
        refine TrivSqZeroExt.ext rfl ?_
        apply ULift.ext
        change (0 : k) = 0 + 0
        ring
      commutes' := fun _ => rfl }
    (fun c => by
      rw [aug_dualNumbers]
      exact (residueFieldCoordinates_residue.{u, v, w} c).symm.trans
        (aug_spec (residueFieldObject.{u, v, w} Λ k) c))

end Augmentation

section SpecialFibre

universe u v w uF vF

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
variable {F : Type uF} [Category.{vF} F]

/-- Every object of a predeformation category admits a morphism to the object of its
special fibre. -/
public theorem nonempty_hom_to_specialFiber
    (p : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k)
    (hp : IsPredeformationCategory p)
    (x₀ : p.Fiber (residueFieldObject.{u, v, w} Λ k)) (x : F) :
    Nonempty (x ⟶ x₀.1) := by
  classical
  obtain ⟨z, φ, hφ⟩ :=
    exists_pushforward hp.cofibered (residueMorphism.{u, v, w} (p.obj x)) x rfl
  have hz : p.obj z = residueFieldObject.{u, v, w} Λ k := by
    let := hφ
    exact IsHomLift.codomain_eq p (residueMorphism.{u, v, w} (p.obj x)) φ
  let zF : p.Fiber (residueFieldObject.{u, v, w} Λ k) := ⟨z, hz⟩
  let e : p.Fiber (residueFieldObject.{u, v, w} Λ k) ≌ Discrete PUnit.{uF + 1} :=
    Classical.choice hp.specialFiber
  let g : zF ⟶ x₀ := e.fullyFaithfulFunctor.preimage ⟨Subsingleton.elim _ _⟩
  exact ⟨φ ≫ Functor.Fiber.fiberInclusion.map g⟩

end SpecialFibre

section StepB

universe u v w uF vF

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
variable {F : Type uF} [Category.{vF} F]

/-- The residue map of a complete local algebra is surjective. -/
public theorem residueHom_surjective (R : CompleteLocalAlgCat.{u, v, w} Λ k) :
    Function.Surjective (residueHom R) := by
  intro c
  obtain ⟨r, hr⟩ := residue_surjective (R.residueEquiv.symm c)
  exact ⟨r, by rw [residueHom_apply, hr, R.residueEquiv.apply_symm_apply]⟩

/-- The Leibniz rule for a derivation of `R` into its residue field, with the scalar action
written through `residueHom`. -/
public theorem derivation_leibniz_residueHom (R : CompleteLocalAlgCat.{u, v, w} Λ k)
    (D : (letI : Algebra R k := (residueHom R).toRingHom.toAlgebra
      Derivation Λ R k)) (a b : R) :
    D (a * b) = residueHom R a * D b + residueHom R b * D a := by
  let : Algebra R k := (residueHom R).toRingHom.toAlgebra
  rw [D.leibniz, Algebra.smul_def, Algebra.smul_def]
  rfl

/-- A derivation of `R` into its residue field kills the square of the maximal ideal. -/
public theorem derivation_eq_zero_of_mem_maximalIdeal_sq (R : CompleteLocalAlgCat.{u, v, w} Λ k)
    (D : (letI : Algebra R k := (residueHom R).toRingHom.toAlgebra
      Derivation Λ R k)) {z : R} (hz : z ∈ maximalIdeal (R : Type _) ^ 2) : D z = 0 := by
  let : Algebra R k := (residueHom R).toRingHom.toAlgebra
  rw [pow_two] at hz
  refine Submodule.mul_induction_on hz ?_ ?_
  · intro a ha b hb
    rw [derivation_leibniz_residueHom, residueHom_eq_zero_of_mem_maximalIdeal R ha,
      residueHom_eq_zero_of_mem_maximalIdeal R hb]
    ring
  · intro x y hx hy
    rw [_root_.map_add, hx, hy, add_zero]

/-- Objects of a fibre with the same isomorphism class are isomorphic. -/
public theorem nonempty_iso_of_classOf_eq {C : Type u} [Category.{v} C]
    {𝓕 : BasedCategory.{vF, uF} C} (h𝓕 : IsCofiberedInGroupoids 𝓕.p) {A : C}
    (x y : 𝓕.p.Fiber A) (h : classOf 𝓕 h𝓕 x = classOf 𝓕 h𝓕 y) : Nonempty (x ≅ y) := by
  have hx := classOf_eq 𝓕 h𝓕 x
  have hy := classOf_eq 𝓕 h𝓕 y
  have hq : Quotient.mk (isIsomorphicSetoid (𝓕.p.Fiber A)) x =
      Quotient.mk (isIsomorphicSetoid (𝓕.p.Fiber A)) y := by
    rw [← hx, ← hy, h]
  exact Quotient.exact hq

/-- The underlying map of a transport along an equality of objects is surjective. -/
public theorem eqToHom_hom_surjective {A B : ArtinianLocalAlgCat.{u, max v w, w} Λ k} (h : A = B) :
    Function.Surjective (eqToHom h).hom := by
  cases h
  intro y
  exact ⟨y, by simp⟩

/-- If the differential of a *minimal* versal formal object takes the same value at a derivation
`d` as at the zero derivation, then `d` vanishes on the maximal ideal of `ξ.base`. -/
public theorem eq_zero_on_maximalIdeal_of_derivationToTangent_eq
    [IsNoetherianRing Λ] [Module.Finite Λ k]
    {p : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    (hp : IsPredeformationCategory p) (hS2 : SchlessingerConditionS2 p)
    (ξ : FormalObject p) (hξ : IsMinimalVersal hp.cofibered ξ)
    (P : ChosenPushforwards p)
    (d : (letI : Algebra ξ.base k := (residueHom ξ.base).toRingHom.toAlgebra
      Derivation Λ ξ.base k))
    (hzero : derivationToTangent.{u, v, w} hp.cofibered ξ P d =
      derivationToTangent.{u, v, w} hp.cofibered ξ P 0)
    (r : ξ.base) (hr : r ∈ maximalIdeal (ξ.base : Type _)) : d r = 0 := by
  classical
  let : Algebra ξ.base k := (residueHom ξ.base).toRingHom.toAlgebra
  by_contra hne
  obtain ⟨c, hc⟩ := residueHom_surjective ξ.base (d r)⁻¹
  have hrq := residueHom_eq_zero_of_mem_maximalIdeal ξ.base hr
  have ht : c * r ∈ maximalIdeal (ξ.base : Type _) := Ideal.mul_mem_left _ _ hr
  have hdt : d (c * r) = 1 := by
    rw [derivation_leibniz_residueHom, hc, hrq, zero_mul, add_zero, inv_mul_cancel₀ hne]
  let α := (tangentSpaceDerivationsLinearEquiv.{u, v, w} ξ.base).symm d
  have hαsnd : ∀ s : ξ.base, ULift.down (TrivSqZeroExt.snd (α.hom s)) = d s := by
    intro s
    have h := tangentSpaceDerivationsLinearEquiv_apply.{u, v, w} ξ.base α s
    rw [LinearEquiv.apply_symm_apply] at h
    exact h.symm
  have hαfst : ∀ s : ξ.base, TrivSqZeroExt.fst (α.hom s) = residueHom ξ.base s := by
    intro s
    rw [← aug_dualNumbers.{u, v, w}]
    exact (aug_spec _ _).symm.trans (α.residue_comm s)
  have hker : ∀ z : ξ.base, z ∈ AdicTruncation.ideal ξ.base 1 → α.hom z = 0 := by
    intro z hz
    have hz2 : z ∈ maximalIdeal (ξ.base : Type _) ^ 2 := by
      change z ∈ maximalIdeal (ξ.base : Type _) ^ (1 + 1) at hz
      rwa [show (1 : ℕ) + 1 = 2 from rfl] at hz
    have hzm : z ∈ maximalIdeal (ξ.base : Type _) := Ideal.pow_le_self two_ne_zero hz2
    refine @TrivSqZeroExt.ext k ↑(FGModuleCat.of k (ULift.{v, w} k)) (α.hom z) 0 ?_ ?_
    · rw [hαfst, residueHom_eq_zero_of_mem_maximalIdeal _ hzm]
      rfl
    · apply ULift.down_injective
      show ULift.down (TrivSqZeroExt.snd (α.hom z)) = (0 : k)
      rw [hαsnd z, derivation_eq_zero_of_mem_maximalIdeal_sq ξ.base d hz2]
  obtain ⟨χ, hχ⟩ := exists_descend_dualNumberPoint.{u, v, w} ξ.base α hker
  obtain ⟨D, hD, hDχ⟩ := exists_pointDerivation.{u, v, w} (AdicTruncation.obj ξ.base 1) χ
  have hDt : D (truncationHom ξ.base 1 (c * r)) = 1 := by
    rw [hDχ, hχ (c * r), hαsnd (c * r), hdt]
  have htbar : truncationHom ξ.base 1 (c * r) ∈
      maximalIdeal ((AdicTruncation.obj ξ.base 1 : ArtinianLocalAlgCat.{u, max v w, w} Λ k)
        : Type _) := by
    rw [mem_maximalIdeal]
    refine (aug_eq_zero_iff_not_isUnit.{u, v, w} _ _).mp ?_
    rw [aug_truncationHom, map_mul, hrq, mul_zero]
  obtain ⟨A', ψ, hPB, hnosec⟩ := exists_derivationSplittingPullback.{u, v, w}
    (AdicTruncation.obj ξ.base 1) (maximalIdeal_sq_truncation ξ.base) χ D hD hDχ htbar hDt
  let yF : p.Fiber (AdicTruncation.obj ξ.base 1) := ⟨ξ.level 1, ξ.level_eq 1⟩
  let xF : p.Fiber A' := (P ψ).obj yF
  let xεF : p.Fiber (artinianDualNumbers.{u, w, v} Λ k) := (P χ).obj yF
  let a : ξ.level 1 ⟶ xF.1 := (P ψ).inclusion yF
  let b : ξ.level 1 ⟶ xεF.1 := (P χ).inclusion yF
  have hlb : p.IsHomLift χ b := ((P χ).cocartesian yF).toIsHomLift
  let x₀ : p.Fiber (residueFieldObject.{u, v, w} Λ k) := specialFiberObject p hp
  obtain ⟨e⟩ := nonempty_hom_to_specialFiber.{u, v, w} p hp x₀ xεF.1
  obtain ⟨dd⟩ := nonempty_hom_to_specialFiber.{u, v, w} p hp x₀ xF.1
  have hcomm : b ≫ e = a ≫ dd := maps_to_special_fiber_eq p hp x₀ _ _
  have hfac : ∀ {B : ArtinianLocalAlgCat.{u, max v w, w} Λ k} (y : p.Fiber B)
      (f : ξ.level 1 ⟶ y.1) (g : AdicTruncation.obj ξ.base 1 ⟶ B), p.IsHomLift g f →
      p.map f = eqToHom (ξ.level_eq 1) ≫ g ≫ eqToHom y.2.symm := fun y f g h => by
    let := h
    rw [IsHomLift.fac' p g f]
  have hfa := hfac xF a ψ ((P ψ).cocartesian yF).toIsHomLift
  have hfb := hfac xεF b χ hlb
  have hfe : eqToHom xεF.2.symm ≫ p.map e ≫ eqToHom x₀.2 =
      residueMorphism.{u, v, w} (artinianDualNumbers.{u, w, v} Λ k) :=
    hom_residueFieldObject_ext.{u, v, w} _ _
  have hfd : eqToHom xF.2.symm ≫ p.map dd ≫ eqToHom x₀.2 =
      residueMorphism.{u, v, w} A' :=
    hom_residueFieldObject_ext.{u, v, w} _ _
  have hdual : IsDualNumberProjection (p.map e) := by
    have hrw : p.map e = eqToHom xεF.2 ≫
        residueMorphism.{u, v, w} (artinianDualNumbers.{u, w, v} Λ k) ≫ eqToHom x₀.2.symm := by
      rw [← hfe]
      simp
    rw [hrw]
    exact isDualNumberProjection_eqToHom.{u, v, w} xεF.2 x₀.2.symm _
      isDualNumberProjection_residueMorphism_dualNumbers.{u, v, w}
  have hPB' : CategoryTheory.IsPullback (p.map b) (p.map a) (p.map e) (p.map dd) := by
    refine hPB.of_iso (eqToIso (ξ.level_eq 1).symm) (eqToIso xεF.2.symm)
      (eqToIso xF.2.symm) (eqToIso x₀.2.symm) ?_ ?_ ?_ ?_
    · rw [hfb]; simp
    · rw [hfa]; simp
    · rw [← hfe]; simp
    · rw [← hfd]; simp
  have hpt : α = truncationPoint ξ.base 1 ≫ artinianToComplete.map χ :=
    tangentPoint_ext.{u, v, w} ξ.base
      (fun s => congrArg (fun z => ULift.down (TrivSqZeroExt.snd z)) (hχ s).symm)
  have hclass1 : derivationToTangent.{u, v, w} hp.cofibered ξ P d =
      classOf (BasedCategory.ofFunctor p) hp.cofibered ⟨xεF.1, xεF.2⟩ := by
    rw [derivationToTangent_eq_pointClass hp.cofibered ξ P d]
    show pointClass hp.cofibered ξ P _ α = _
    rw [hpt]
    exact pointClass_of_lift hp.cofibered ξ P 1 χ xεF.2 b hlb
  let χ0 : (AdicTruncation.obj ξ.base 1 : ArtinianLocalAlgCat.{u, max v w, w} Λ k) ⟶
      artinianDualNumbers.{u, w, v} Λ k :=
    residueMorphism.{u, v, w} (AdicTruncation.obj ξ.base 1) ≫ dualNumbersInclusion.{u, v, w}
  let wF : p.Fiber (artinianDualNumbers.{u, w, v} Λ k) := (P dualNumbersInclusion.{u, v, w}).obj x₀
  let j0 : x₀.1 ⟶ wF.1 := (P dualNumbersInclusion.{u, v, w}).inclusion x₀
  have hlj0 : p.IsHomLift dualNumbersInclusion.{u, v, w} j0 :=
    ((P dualNumbersInclusion.{u, v, w}).cocartesian x₀).toIsHomLift
  obtain ⟨m⟩ := nonempty_hom_to_specialFiber.{u, v, w} p hp x₀ (ξ.level 1)
  have hfm : eqToHom (ξ.level_eq 1).symm ≫ p.map m ≫ eqToHom x₀.2 =
      residueMorphism.{u, v, w} (AdicTruncation.obj ξ.base 1) :=
    hom_residueFieldObject_ext.{u, v, w} _ _
  have hlm : p.IsHomLift (residueMorphism.{u, v, w} (AdicTruncation.obj ξ.base 1)) m := by
    refine IsHomLift.of_fac p _ m (ξ.level_eq 1) x₀.2 ?_
    rw [← hfm]
  have hli : p.IsHomLift χ0 (m ≫ j0) := by
    let := hlm
    let := hlj0
    exact IsHomLift.comp p _ _ _ _
  have hpt0 : (tangentSpaceDerivationsLinearEquiv.{u, v, w} ξ.base).symm 0 =
      truncationPoint ξ.base 1 ≫ artinianToComplete.map χ0 := by
    refine tangentPoint_ext.{u, v, w} ξ.base ?_
    intro s
    have h := tangentSpaceDerivationsLinearEquiv_apply.{u, v, w} ξ.base
      ((tangentSpaceDerivationsLinearEquiv.{u, v, w} ξ.base).symm 0) s
    rw [LinearEquiv.apply_symm_apply] at h
    rw [← h]
    rfl
  have hclass0 : derivationToTangent.{u, v, w} hp.cofibered ξ P 0 =
      classOf (BasedCategory.ofFunctor p) hp.cofibered ⟨wF.1, wF.2⟩ := by
    rw [derivationToTangent_eq_pointClass hp.cofibered ξ P 0]
    rw [hpt0]
    exact pointClass_of_lift hp.cofibered ξ P 1 χ0 wF.2 (m ≫ j0) hli
  obtain ⟨iso⟩ := nonempty_iso_of_classOf_eq hp.cofibered
    (⟨xεF.1, xεF.2⟩ : (BasedCategory.ofFunctor p).p.Fiber _)
    (⟨wF.1, wF.2⟩ : (BasedCategory.ofFunctor p).p.Fiber _)
    (by rw [← hclass1, ← hclass0, hzero])
  let sε : xF.1 ⟶ xεF.1 := dd ≫ j0 ≫ Functor.Fiber.fiberInclusion.map iso.inv
  have hsε : sε ≫ e = dd := maps_to_special_fiber_eq p hp x₀ _ _
  obtain ⟨s, hs⟩ := (exists_section_iff_exists_dualNumberLift p hp.cofibered hS2 b a e dd
    hcomm hdual hPB').mpr ⟨sε, hsε⟩
  have hmap : p.map s ≫ p.map a = 𝟙 (p.obj xF.1) := by
    rw [← p.map_comp, hs, p.map_id]
  have hid : ∀ z, (p.map a).hom ((p.map s).hom z) = z := fun z =>
    congrArg (fun q : p.obj xF.1 ⟶ p.obj xF.1 => q.hom z) hmap
  have hinjs : Function.Injective (p.map s).hom := fun z z' h => by
    rw [← hid z, ← hid z', h]
  have hsurjs := surjective_of_injective_to_minimalVersal_level p hp ξ hξ 1 s hinjs
  refine hnosec (eqToHom xF.2.symm ≫ p.map s ≫ eqToHom (ξ.level_eq 1)) ?_ ?_
  · have h1 : eqToHom (ξ.level_eq 1) ≫ ψ = p.map a ≫ eqToHom xF.2 := by
      rw [hfa]; simp
    calc
      (eqToHom xF.2.symm ≫ p.map s ≫ eqToHom (ξ.level_eq 1)) ≫ ψ
          = eqToHom xF.2.symm ≫ p.map s ≫ (eqToHom (ξ.level_eq 1) ≫ ψ) := by
            simp [Category.assoc]
      _ = eqToHom xF.2.symm ≫ p.map s ≫ p.map a ≫ eqToHom xF.2 := by rw [h1]
      _ = eqToHom xF.2.symm ≫ (p.map s ≫ p.map a) ≫ eqToHom xF.2 := by
            simp [Category.assoc]
      _ = 𝟙 A' := by rw [hmap]; simp
  · intro z
    obtain ⟨z1, hz1⟩ := eqToHom_hom_surjective.{u, v, w} (ξ.level_eq 1) z
    obtain ⟨z2, hz2⟩ := hsurjs z1
    obtain ⟨z3, hz3⟩ := eqToHom_hom_surjective.{u, v, w} xF.2.symm z2
    refine ⟨z3, ?_⟩
    show (eqToHom (ξ.level_eq 1)).hom ((p.map s).hom ((eqToHom xF.2.symm).hom z3)) = z
    rw [hz3, hz2, hz1]

end StepB

section Orbits

universe u v w uF vF

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
variable {F : Type uF} [Category.{vF} F]

/-- If the tangent vectors named by two derivations of the base of a minimal versal formal object
`ξ` differ by a translation, then the derivations themselves differ by a residue-field
derivation. -/
public theorem exists_eq_add_of_eq_action
    [IsNoetherianRing Λ] [Module.Finite Λ k]
    {p : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    (hp : IsPredeformationCategory p) (hS2 : SchlessingerConditionS2 p)
    (ξ : FormalObject p) (hξ : IsMinimalVersal hp.cofibered ξ)
    (D E : Derivations ξ.base k)
    (y z : predeformationTangentSpace.{u, v, w} p hp)
    (hy : derivationDifferentialGraph.{u, v, w} p hp ξ D y)
    (hz : derivationDifferentialGraph.{u, v, w} p hp ξ E z)
    (hδ : ∃ δ : Derivation Λ k k, z = (derivationAction.{u, v, w} p hp).action (δ, y)) :
    ∃ δ : Derivation Λ k k, ∀ r : ξ.base, E r = D r + δ (residueHom ξ.base r) := by
  classical
  obtain ⟨δ, hδ⟩ := hδ
  obtain ⟨E', hE', hgraph⟩ :=
    exists_derivationDifferentialGraph_action.{u, v, w} hp ξ D δ y hy
  let P : ChosenPushforwards p := chosenPushforwardsOfCofibered p hp.cofibered
  have hzE : z = derivationToTangent.{u, v, w} hp.cofibered ξ P (derivationToStandard ξ E) :=
    derivationDifferentialGraph_eq_derivationToTangent hp ξ P E z hz
  have hzE' : z = derivationToTangent.{u, v, w} hp.cofibered ξ P (derivationToStandard ξ E') :=
    derivationDifferentialGraph_eq_derivationToTangent hp ξ P E' z (hδ ▸ hgraph)
  let : Algebra ξ.base k := (residueHom ξ.base).toRingHom.toAlgebra
  have hsub : derivationToTangent.{u, v, w} hp.cofibered ξ P
      (derivationToStandard ξ E - derivationToStandard ξ E') =
      derivationToTangent.{u, v, w} hp.cofibered ξ P 0 :=
    derivationToTangent_sub_eq_zero_of_eq.{u, v, w} hp hS2 ξ P _ _ (hzE.symm.trans hzE')
  have hvanish : ∀ r : ξ.base, r ∈ maximalIdeal (ξ.base : Type _) →
      standardToDerivation ξ (derivationToStandard ξ E - derivationToStandard ξ E') r = 0 := by
    intro r hr
    rw [standardToDerivation_apply]
    exact eq_zero_on_maximalIdeal_of_derivationToTangent_eq.{u, v, w} hp hS2 ξ hξ P _ hsub r hr
  obtain ⟨δ', hδ'⟩ := exists_residueDerivation_of_eq_zero_on_maximalIdeal
    ξ.base (standardToDerivation ξ (derivationToStandard ξ E - derivationToStandard ξ E'))
    hvanish
  refine ⟨δ + δ', fun r => ?_⟩
  have hval : E r - E' r = δ' (residueHom ξ.base r) := by
    have h := hδ' r
    rw [standardToDerivation_apply] at h
    rw [← h]
    simp only [Derivation.sub_apply, derivationToStandard_apply]
  have : E r = E' r + δ' (residueHom ξ.base r) := by
    rw [← hval]
    ring
  rw [this, hE' r, Derivation.add_apply]
  ring

/-- The differential of a minimal versal formal object of a predeformation category satisfying
Schlessinger's condition (S2) is well defined, surjective and equivariant, and induces a
bijection on `Der_Λ(k, k)`-orbits. -/
@[stacks 06T8,
  stacks 06T6 "the condition holds for a minimal versal formal object"]
public theorem minimalVersal_hasBijectiveDifferentialOnDerivationOrbits
    [IsNoetherianRing Λ] [Module.Finite Λ k]
    (p : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k)
    (hp : IsPredeformationCategory p)
    (hS2 : SchlessingerConditionS2 p)
    (ξ : FormalObject p)
    (hξ : IsMinimalVersal hp.cofibered ξ) :
    HasBijectiveDifferentialOnDerivationOrbits.{u, v, w} p hp ξ := by
  refine ⟨fun D => existsUnique_derivationDifferentialGraph hp ξ D,
    fun y => exists_derivationDifferentialGraph_of_isVersal.{u, v, w} hp hS2 ξ hξ.1 y,
    fun D δ y hy => exists_derivationDifferentialGraph_action.{u, v, w} hp ξ D δ y hy,
    fun D E y z hy hz => ⟨exists_eq_add_of_eq_action.{u, v, w} hp hS2 ξ hξ D E y z hy hz,
      eq_action_of_eq_add.{u, v, w} hp ξ D E y z hy hz⟩⟩

end Orbits

end Deformation

end
