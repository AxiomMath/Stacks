module

public import StacksFrontier.AlgebraicGeometry.Blowup.AffineModelTwistBridge
public import StacksFrontier.AlgebraicGeometry.Blowup.RegularSurfaceExceptionalCurve
public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.FlatBaseChangeExceptionalDivisor
public import StacksFrontier.AlgebraicGeometry.F6Rank89.IdealSheafStalk
public import StacksFrontier.AlgebraicGeometry.Surfaces.ExceptionalCurveComap

/-!
# The exceptional divisor of the blowup at a regular closed point of dimension two

Let `A` be a scheme and `a ∈ A` a closed point whose local ring is regular of Krull dimension two.
The exceptional divisor `E` of the blowup of `A` in the reduced point `{a}` is an exceptional curve
of the first kind over the residue field `κ(a)`: it is an effective Cartier divisor, and there is
an isomorphism `𝐏¹_{κ(a)} ≅ E` along which the normal sheaf of `E` pulls back to `𝒪(-1)`.

This extends `Stacks.Blowup.exists_isExceptionalCurveOfFirstKind_exceptionalIdealData`, the same
statement for `Spec` of a regular two-dimensional local ring, to an arbitrary scheme with such a
point.

## Main results

* `Stacks.Blowup.exists_isExceptionalCurveOfFirstKind_exceptionalIdeal_vanishingIdeal`: the
  statement above.
* `Stacks.Blowup.exists_isExceptionalCurveOfFirstKind_exceptionalIdeal_specIdealSheaf`: the same
  for the blowup of `Spec R` in the ideal sheaf that the maximal ideal of a regular
  two-dimensional local ring `R` defines.
* `Stacks.Blowup.exists_isExceptionalCurveOfFirstKind_exceptionalIdeal_of_isPullback`: an
  exceptional curve of the first kind descends along the base change of a blowup by a flat
  preimmersion, for a centre supported at one point of its image.
* `Stacks.Blowup.exceptionalIdealData_eq_comap`: the exceptional divisor of the blowup
  `Proj (⨁ₙ mⁿ)` of `Spec R` in an ideal `m` is the inverse image of the exceptional divisor of the
  blowup of `Spec R` in the ideal sheaf of `m`, along any morphism over `Spec R`.
* `Stacks.Blowup.vanishingIdeal_comap_fromSpecStalk_eq_specIdealSheaf`: the inverse image along
  `Spec 𝒪_{X,z} ⟶ X` of the ideal sheaf of a reduced closed point `z` is the ideal sheaf of the
  maximal ideal of `𝒪_{X,z}`.

## References

* [Stacks Project, Tag 0AGQ](https://stacks.math.columbia.edu/tag/0AGQ)
* [Stacks Project, Tag 0805](https://stacks.math.columbia.edu/tag/0805)
* [Stacks Project, Tag 0B3P](https://stacks.math.columbia.edu/tag/0B3P)
-/


@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing TopologicalSpace Topology

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace Stacks.Blowup

/-! ### Identifications of ideal sheaves -/

/-- The image of an ideal of `R` under the inverse of `Γ(Spec R, ⊤) ≅ R` is its preimage under the
isomorphism itself. -/
private theorem ideal_map_inv_eq_comap_hom {R : Type u} [CommRing R] (m : Ideal R) :
    Ideal.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom m =
      Ideal.comap (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom m := by
  have hφψ : (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom.comp
      (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom = RingHom.id R :=
    congrArg CommRingCat.Hom.hom (Scheme.ΓSpecIso (CommRingCat.of R)).inv_hom_id
  have hψφ : (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom.comp
      (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom = RingHom.id _ :=
    congrArg CommRingCat.Hom.hom (Scheme.ΓSpecIso (CommRingCat.of R)).hom_inv_id
  refine le_antisymm (Ideal.map_le_iff_le_comap.2 fun y hy => ?_) fun x hx => ?_
  · change (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom y) ∈ m
    rw [← RingHom.comp_apply, hφψ]
    simpa using hy
  · have hxx : x = (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
        ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom x) := by
      rw [← RingHom.comp_apply, hψφ]
      simp
    rw [hxx]
    exact Ideal.mem_map_of_mem _ hx

/-- **The exceptional divisor of the affine model is the inverse image of the exceptional divisor
of the ideal-sheaf blowup**, along any morphism `d` between the two blowups compatible with the two
structure morphisms. -/
theorem exceptionalIdealData_eq_comap {R : Type u} [CommRing R] (m : Ideal R)
    (d : blowUpSpec m ⟶ AlgebraicGeometry.blowUp (AffineModel.specIdealSheaf m))
    (hd : d ≫ AlgebraicGeometry.blowUpToBase (AffineModel.specIdealSheaf m) = toSpec m) :
    exceptionalIdealData m =
      (AlgebraicGeometry.exceptionalIdeal (AffineModel.specIdealSheaf m)).comap d := by
  have h1 : (AlgebraicGeometry.exceptionalIdeal (AffineModel.specIdealSheaf m)).comap d =
      (AffineModel.specIdealSheaf m).comap
        (d ≫ AlgebraicGeometry.blowUpToBase (AffineModel.specIdealSheaf m)) :=
    (Scheme.IdealSheafData.comap_comp _ _ _).symm
  rw [h1, hd]
  change (Scheme.IdealSheafData.ofIdealTop
      (Ideal.comap (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom m)).comap (toSpec m) = _
  rw [AffineModel.specIdealSheaf, ideal_map_inv_eq_comap_hom]

/-- The inverse image along `Spec 𝒪_{X,z} ⟶ X` of the ideal sheaf of a reduced closed point is
the ideal sheaf that the maximal ideal of `𝒪_{X,z}` defines on `Spec 𝒪_{X,z}`. -/
theorem vanishingIdeal_comap_fromSpecStalk_eq_specIdealSheaf {X : Scheme.{u}} (z : X)
    (hz : IsClosed ({z} : Set X)) :
    (Scheme.IdealSheafData.vanishingIdeal (⟨{z}, hz⟩ : Closeds X)).comap (X.fromSpecStalk z) =
      AffineModel.specIdealSheaf (maximalIdeal (X.presheaf.stalk z)) := by
  rw [vanishingIdeal_singleton_comap_fromSpecStalk z hz, Scheme.ker_SpecMap]
  change Scheme.IdealSheafData.ofIdealTop
    (Ideal.map _ (RingHom.ker (IsLocalRing.residue (X.presheaf.stalk z)))) = _
  rw [IsLocalRing.ker_residue]
  rfl

/-! ### Criteria for isomorphisms -/

/-- The closed subscheme of the inverse image of an ideal sheaf `D` is the pullback of the closed
subscheme of `D`. -/
private theorem isPullback_comapSubschemeMap' {X Y : Scheme.{u}} (f : X ⟶ Y)
    (D : Y.IdealSheafData) : IsPullback (D.comap f).subschemeι
      (Stacks.Divisors.comapSubschemeMap' f D) f D.subschemeι :=
  isPullback_of_isClosedImmersion _ _ _ _ (by simp)
    (by simp [Scheme.IdealSheafData.ker_subschemeι])

/-- The induced morphism of closed subschemes along an isomorphism of the ambient schemes is an
isomorphism. -/
private theorem isIso_comapSubschemeMap_of_iso {X Y : Scheme.{u}} (φ : X ≅ Y)
    (D : Y.IdealSheafData) : IsIso (Stacks.Divisors.comapSubschemeMap' φ.hom D) :=
  MorphismProperty.of_isPullback (P := MorphismProperty.isomorphisms Scheme)
    (isPullback_comapSubschemeMap' φ.hom D) inferInstance

/-- A flat preimmersion which is surjective is an isomorphism. -/
private theorem isIso_of_flat_preimmersion_surjective {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsPreimmersion f] [Flat f] (hs : Function.Surjective f.base) : IsIso f := by
  have hoe : IsOpenEmbedding f.base :=
    ⟨IsPreimmersion.isEmbedding f, by rw [hs.range_eq]; exact isOpen_univ⟩
  have _hst : ∀ z : X, IsIso (f.stalkMap z) := fun z => isIso_stalkMap_of_flat_preimmersion f z
  have _hoi : IsOpenImmersion f := IsOpenImmersion.of_isIso_stalkMap f hoe
  have _hsj : Surjective f := ⟨hs⟩
  rw [isIso_iff_isOpenImmersion_and_surjective]
  exact ⟨inferInstance, inferInstance⟩

/-! ### The exceptional curve at the affine local model -/

/-- **The exceptional divisor of the blowup of `Spec R` in the ideal sheaf that the maximal ideal
of a regular two-dimensional local ring `R` defines is an exceptional curve of the first kind over
the residue field.** Here the centre is any ideal sheaf `K` equal to that one. -/
theorem exists_isExceptionalCurveOfFirstKind_exceptionalIdeal_specIdealSheaf (R : Type u)
    [CommRing R] [IsRegularLocalRing R] (hdim : ringKrullDim R = 2)
    (K : (Spec (CommRingCat.of R)).IdealSheafData)
    (hK : K = AffineModel.specIdealSheaf (maximalIdeal R)) :
    ∃ e : projectiveLineProj (ResidueField R) ≅
        (AlgebraicGeometry.exceptionalIdeal K).subscheme,
      (AlgebraicGeometry.exceptionalIdeal K).IsExceptionalCurveOfFirstKind
        (ResidueField R) e := by
  subst hK
  obtain ⟨ε, hε⟩ := exists_isExceptionalCurveOfFirstKind_exceptionalIdealData R hdim
  obtain ⟨d, hdbase, -⟩ := AffineModel.exists_iso_blowUpTwist (maximalIdeal R)
  exact AlgebraicGeometry.exists_isExceptionalCurveOfFirstKind_of_comap d.hom
    (AlgebraicGeometry.exceptionalIdeal (AffineModel.specIdealSheaf (maximalIdeal R)))
    (Stacks.Divisors.isPullbackDefined_of_flat _ _ inferInstance)
    (isIso_comapSubschemeMap_of_iso d _) (exceptionalIdealData (maximalIdeal R))
    (exceptionalIdealData_eq_comap (maximalIdeal R) d.hom hdbase) _ ε hε

/-! ### Flat base change of exceptional curves -/

/-- **An exceptional curve of the first kind descends along the base change of a blowup by a flat
preimmersion `g : S ⟶ A`**, when the centre is supported at a single point of the image of `g`. -/
theorem exists_isExceptionalCurveOfFirstKind_exceptionalIdeal_of_isPullback {A S : Scheme.{u}}
    (g : S ⟶ A) [Flat g] [IsPreimmersion g] (a : A) (s : S) (hs : g s = a)
    (I : A.IdealSheafData) (hIsupp : (I.support : Set A) = {a})
    {h : AlgebraicGeometry.blowUp (I.comap g) ⟶ AlgebraicGeometry.blowUp I}
    (hpb : IsPullback (AlgebraicGeometry.blowUpToBase (I.comap g)) h g
      (AlgebraicGeometry.blowUpToBase I))
    (k : Type u) [Field k]
    (e₀ : projectiveLineProj k ≅ (AlgebraicGeometry.exceptionalIdeal (I.comap g)).subscheme)
    (hE₀ : (AlgebraicGeometry.exceptionalIdeal (I.comap g)).IsExceptionalCurveOfFirstKind k e₀) :
    ∃ e : projectiveLineProj k ≅ (AlgebraicGeometry.exceptionalIdeal I).subscheme,
      (AlgebraicGeometry.exceptionalIdeal I).IsExceptionalCurveOfFirstKind k e := by
  have hflath : Flat h := MorphismProperty.of_isPullback (P := @Flat) hpb inferInstance
  have hpreh : IsPreimmersion h :=
    MorphismProperty.of_isPullback (P := @IsPreimmersion) hpb inferInstance
  have hpb2 := isPullback_comapSubschemeMap' h (AlgebraicGeometry.exceptionalIdeal I)
  have : Flat (Stacks.Divisors.comapSubschemeMap' h (AlgebraicGeometry.exceptionalIdeal I)) :=
    MorphismProperty.of_isPullback (P := @Flat) hpb2 hflath
  have : IsPreimmersion
      (Stacks.Divisors.comapSubschemeMap' h (AlgebraicGeometry.exceptionalIdeal I)) :=
    MorphismProperty.of_isPullback (P := @IsPreimmersion) hpb2 hpreh
  have hsurj : Function.Surjective
      (Stacks.Divisors.comapSubschemeMap' h (AlgebraicGeometry.exceptionalIdeal I)).base := by
    intro y
    have hmem : (AlgebraicGeometry.exceptionalIdeal I).subschemeι y ∈
        ((AlgebraicGeometry.exceptionalIdeal I).support :
          Set (AlgebraicGeometry.blowUp I)) := by
      rw [← Scheme.IdealSheafData.range_subschemeι]
      exact ⟨y, rfl⟩
    have hba : AlgebraicGeometry.blowUpToBase I
        ((AlgebraicGeometry.exceptionalIdeal I).subschemeι y) = a := by
      have h0 : (AlgebraicGeometry.exceptionalIdeal I).subschemeι y ∈
          ((I.comap (AlgebraicGeometry.blowUpToBase I)).support :
            Set (AlgebraicGeometry.blowUp I)) := hmem
      rw [Scheme.IdealSheafData.support_comap, TopologicalSpace.Closeds.coe_preimage,
        hIsupp] at h0
      exact h0
    obtain ⟨v, -, hv⟩ := Scheme.exists_preimage_of_isPullback hpb s
      ((AlgebraicGeometry.exceptionalIdeal I).subschemeι y) (hs.trans hba.symm)
    obtain ⟨w, -, hw⟩ := Scheme.exists_preimage_of_isPullback hpb2 v y hv
    exact ⟨w, hw⟩
  have : IsIso (Stacks.Divisors.comapSubschemeMap' h (AlgebraicGeometry.exceptionalIdeal I)) :=
    isIso_of_flat_preimmersion_surjective _ hsurj
  exact AlgebraicGeometry.exists_isExceptionalCurveOfFirstKind_of_comap h
    (AlgebraicGeometry.exceptionalIdeal I)
    (Stacks.Divisors.isPullbackDefined_of_flat _ _ inferInstance) inferInstance
    (AlgebraicGeometry.exceptionalIdeal (I.comap g))
    (AlgebraicGeometry.comap_exceptionalIdeal_of_isPullback I g hpb).symm k e₀ hE₀

/-! ### The blowup at a regular closed point of dimension two -/

/-- **The exceptional divisor of the blowup at a closed point whose local ring is regular of
dimension two is an exceptional curve of the first kind over the residue field.** The exceptional
divisor `E` of the blowup of `A` in the reduced point `{a}` is an effective Cartier divisor, and
there is an isomorphism `𝐏¹_{κ(a)} ≅ E` under which the normal sheaf of `E` pulls back to
`𝒪(-1)`. -/
theorem exists_isExceptionalCurveOfFirstKind_exceptionalIdeal_vanishingIdeal {A : Scheme.{u}}
    (a : A) (ha : IsClosed ({a} : Set A)) (hreg : IsRegularLocalRing (A.presheaf.stalk a))
    (hdim : ringKrullDim (A.presheaf.stalk a) = 2) :
    ∃ e : projectiveLineProj (ResidueField (A.presheaf.stalk a)) ≅
        (AlgebraicGeometry.exceptionalIdeal
          (Scheme.IdealSheafData.vanishingIdeal (⟨{a}, ha⟩ : Closeds A))).subscheme,
      Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind
        (AlgebraicGeometry.exceptionalIdeal
          (Scheme.IdealSheafData.vanishingIdeal (⟨{a}, ha⟩ : Closeds A)))
        (ResidueField (A.presheaf.stalk a)) e := by
  have _hreg : IsRegularLocalRing (A.presheaf.stalk a) := hreg
  have : Flat (A.fromSpecStalk a) := flat_fromSpecStalk A a
  obtain ⟨h, hpb⟩ := AlgebraicGeometry.exists_isPullback_blowUpToBase_comap (A.fromSpecStalk a)
    (Scheme.IdealSheafData.vanishingIdeal (⟨{a}, ha⟩ : Closeds A))
  obtain ⟨e₀, hE₀⟩ := exists_isExceptionalCurveOfFirstKind_exceptionalIdeal_specIdealSheaf
    (A.presheaf.stalk a) hdim _
    (vanishingIdeal_comap_fromSpecStalk_eq_specIdealSheaf a ha)
  exact exists_isExceptionalCurveOfFirstKind_exceptionalIdeal_of_isPullback
    (A.fromSpecStalk a) a (IsLocalRing.closedPoint (A.presheaf.stalk a))
    Scheme.fromSpecStalk_closedPoint _
    (Scheme.IdealSheafData.coe_support_vanishingIdeal _) hpb _ e₀ hE₀

end Stacks.Blowup

end
