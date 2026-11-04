module

public import Mathlib.AlgebraicGeometry.Cover.Open
public import Mathlib.AlgebraicGeometry.Gluing
public import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Morphisms out of an affine scheme glued along basic opens

Let `B` be a commutative ring and `s : ι → B` a family of elements generating the unit ideal, so
that the basic opens `D(s i) = Spec B_{s i}` cover `Spec B`. A family of morphisms
`g i : Spec B_{s i} ⟶ Y` glues to a morphism `Spec B ⟶ Y` as soon as the members are compatible on
the overlaps. The compatibility is stated on test rings: for every ring `C` and every pair of
ring maps `B_{s i} ⟶ C`, `B_{s j} ⟶ C` agreeing on `B`, the two induced morphisms
`Spec C ⟶ Y` agree. This is the form in which it is verified in practice, and it contains the
condition on the overlap `D(s i) ∩ D(s j)` as the case `C = (B_{s j})_{s i}`.

## Main definitions

* `AlgebraicGeometry.Spec.glueAway`: the glued morphism `Spec B ⟶ Y`.

## Main results

* `AlgebraicGeometry.Spec.map_algebraMap_comp_glueAway`: the glued morphism restricts to `g i` on
  `D(s i)`.
* `AlgebraicGeometry.Spec.map_comp_glueAway_of_isUnit`: for every ring map `φ : B ⟶ C` which
  inverts `s i`, the composite `Spec C ⟶ Spec B ⟶ Y` is `g i` precomposed with the induced map
  `Spec C ⟶ Spec B_{s i}`.
* `AlgebraicGeometry.Spec.hom_ext_away`: morphisms out of `Spec B` agreeing on every `D(s i)` are
  equal.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Spec

variable {B : Type u} [CommRing B] {ι : Type*} (s : ι → B) (hs : Ideal.span (Set.range s) = ⊤)

/-- The overlap `D(s i) ∩ D(s j)` of two basic opens, read as the spectrum of the localization
of `B_{s j}` at the image of `s i`: the fibre product of the two members of the cover. -/
theorem isPullback_away (i j : ι) :
    IsPullback
      (Spec.map (CommRingCat.ofHom (IsLocalization.Away.lift (s i)
        (S := Localization.Away (s i))
        (g := (algebraMap (Localization.Away (s j))
          (Localization.Away (algebraMap B (Localization.Away (s j)) (s i)))).comp
            (algebraMap B (Localization.Away (s j))))
        (IsLocalization.Away.algebraMap_isUnit
          (algebraMap B (Localization.Away (s j)) (s i))))))
      (Spec.map (CommRingCat.ofHom (algebraMap (Localization.Away (s j))
        (Localization.Away (algebraMap B (Localization.Away (s j)) (s i))))))
      (Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away (s i)))))
      (Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away (s j))))) := by
  have : IsLocalization ((Submonoid.powers (s i)).map (algebraMap B (Localization.Away (s j))))
      (Localization.Away (algebraMap B (Localization.Away (s j)) (s i))) := by
    rw [Submonoid.map_powers]
    infer_instance
  exact (isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_of_isLocalization (algebraMap B (Localization.Away (s j)))
      _ (IsLocalization.Away.lift_comp _ _) (Submonoid.powers (s i)))).flip

variable {Y : Scheme.{u}} (g : ∀ i, Spec (.of (Localization.Away (s i))) ⟶ Y)

/-- The compatibility of a family of morphisms out of the basic opens `D(s i)`: any two ring maps
out of `B_{s i}` and `B_{s j}` which agree on `B` induce the same morphism after composing with
the corresponding members. -/
def AwayCompatible : Prop :=
  ∀ (i j : ι) {C : Type u} [CommRing C] (φ : Localization.Away (s i) →+* C)
    (ψ : Localization.Away (s j) →+* C),
    φ.comp (algebraMap B _) = ψ.comp (algebraMap B _) →
      Spec.map (CommRingCat.ofHom φ) ≫ g i = Spec.map (CommRingCat.ofHom ψ) ≫ g j

variable {s g}

/-- The compatibility on the fibre product of two members of the cover. -/
theorem pullback_fst_comp_eq_snd_comp (hg : AwayCompatible s g) (i j : ι) :
    pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away (s i)))))
        (Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away (s j))))) ≫ g i =
      pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away (s i)))))
        (Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away (s j))))) ≫ g j := by
  have hpb := isPullback_away s i j
  rw [← cancel_epi hpb.isoPullback.hom, hpb.isoPullback_hom_fst_assoc,
    hpb.isoPullback_hom_snd_assoc]
  exact hg i j _ _ (IsLocalization.Away.lift_comp _ _)

/-- **Morphisms out of `Spec B` glue along a cover by basic opens.** -/
def glueAway (hg : AwayCompatible s g) : Spec (.of B) ⟶ Y :=
  (Scheme.affineOpenCoverOfSpanRangeEqTop (R := .of B) s hs).openCover.glueMorphisms g
    (pullback_fst_comp_eq_snd_comp hg)

/-- The glued morphism restricts to `g i` on the basic open `D(s i)`. -/
@[reassoc (attr := simp)]
theorem map_algebraMap_comp_glueAway (hg : AwayCompatible s g) (i : ι) :
    Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away (s i)))) ≫ glueAway hs hg =
      g i :=
  (Scheme.affineOpenCoverOfSpanRangeEqTop (R := .of B) s hs).openCover.ι_glueMorphisms _ _ i

/-- Composing the glued morphism with the spectrum of a ring map inverting `s i` factors through
`D(s i)`. -/
theorem map_comp_glueAway_of_isUnit (hg : AwayCompatible s g) {C : Type u} [CommRing C]
    (φ : B →+* C) (i : ι) (hφ : IsUnit (φ (s i))) :
    Spec.map (CommRingCat.ofHom φ) ≫ glueAway hs hg =
      Spec.map (CommRingCat.ofHom (IsLocalization.Away.lift (s i) hφ
        (S := Localization.Away (s i)))) ≫ g i := by
  conv_lhs => rw [← IsLocalization.Away.lift_comp (s i) hφ (S := Localization.Away (s i))]
  rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, map_algebraMap_comp_glueAway]

include hs in
/-- **Morphisms out of `Spec B` agreeing on every basic open of a cover are equal.** -/
theorem hom_ext_away {f₁ f₂ : Spec (.of B) ⟶ Y}
    (h : ∀ i, Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away (s i)))) ≫ f₁ =
      Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away (s i)))) ≫ f₂) :
    f₁ = f₂ :=
  (Scheme.affineOpenCoverOfSpanRangeEqTop (R := .of B) s hs).openCover.hom_ext _ _ h

include hs in
/-- Morphisms out of `Spec B` agreeing after every ring map inverting some `s i` are equal. -/
theorem hom_ext_of_isUnit {f₁ f₂ : Spec (.of B) ⟶ Y}
    (h : ∀ i {C : Type u} [CommRing C] (φ : B →+* C), IsUnit (φ (s i)) →
      Spec.map (CommRingCat.ofHom φ) ≫ f₁ = Spec.map (CommRingCat.ofHom φ) ≫ f₂) :
    f₁ = f₂ :=
  hom_ext_away hs fun i ↦ h i _ (IsLocalization.Away.algebraMap_isUnit (s i))

end AlgebraicGeometry.Spec
