module

public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.EtaleChartNeighborhood
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PrimeDivisorFunctionFieldChartIndependence
public import StacksFrontier.AlgebraicGeometry.Spaces.OrderOfVanishingChartComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.OrderOfVanishingRationalFunction

/-!
# The order of vanishing of a rational function read on an elementary étale chart

Let `X` be a locally Noetherian integral algebraic space over a scheme `S`, let `Z ⊂ X` be a
prime divisor with generic point `ξ`, and let `(U, u)` be an elementary étale neighbourhood of
`ξ` whose scheme is affine, reduced and locally Noetherian — but not necessarily integral. If
the pullback of an invertible rational function `f` of `X` to the total ring of fractions of
`Γ(U, 𝒪_U)` is a global section `a`, then the order of vanishing `ord_Z(f)` of Stacks 0ENL is
the length of `𝒪_{U, u} / a 𝒪_{U, u}`.

Indeed, the canonical map `R(X) → Q(𝒪^h_{X, ξ})` of Stacks 0ENK can be computed on any affine
elementary étale neighbourhood of `ξ`, so it sends `f` to the image of the germ of `a`, and the
structure map `𝒪_{U, u} → 𝒪^h_{X, ξ}` of a henselization leaves the length of the quotient by a
principal ideal unchanged.

The second half of the file supplies elementary étale neighbourhoods. The condition that makes
an étale chart `(U, u)` of `X` *elementary* is that the residue-field point
`Spec κ(u) → U → X` is a monomorphism; this holds automatically when the structure morphism
`Spec κ(u) → S` is a monomorphism, for instance at a point of a scheme over a field `k` whose
residue field is `k`, and also when the chart itself is a monomorphism.

## Main results

* `AlgebraicGeometry.Space.PrimeDivisor.ordRationalFunction_eq_ord_germ`: on an affine, reduced,
  locally Noetherian elementary étale neighbourhood of the generic point of `Z`, the order of
  vanishing of `f` along `Z` is `Ring.ord` of the germ of its pullback.
* `AlgebraicGeometry.Space.PrimeDivisor.ordRationalFunction_eq_ord_henselian`: the same, read in
  the henselian local ring at the generic point.
* `AlgebraicGeometry.Space.mono_yoneda_map_residueFieldMap_comp_of_mono_structure` and
  `AlgebraicGeometry.Space.mono_yoneda_map_residueFieldMap_comp_of_mono`: the residue-field
  point of an étale chart is a monomorphism into the space when the structure morphism of the
  residue field is a monomorphism, or when the chart is.
* `AlgebraicGeometry.Space.mono_fromSpecResidueField_comp_of_section`: at a rational point, the
  image of a section, the structure morphism of the residue field is a monomorphism.
* `AlgebraicGeometry.Space.elementaryEtaleNeighborhoodOfMonoChart` and
  `AlgebraicGeometry.Space.elementaryEtaleNeighborhoodOfMonoStructure`: the resulting elementary
  étale neighbourhoods.

## References

* [Stacks Project, Tag 0BGU](https://stacks.math.columbia.edu/tag/0BGU)
* [Stacks Project, Tag 0ENK](https://stacks.math.columbia.edu/tag/0ENK)
* [Stacks Project, Tag 0ENL](https://stacks.math.columbia.edu/tag/0ENL)
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped nonZeroDivisors

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hInt : IsIntegralSpace B S hS X)
    (hN : HasEtaleLocalProperty B S hS X (fun Y : Scheme.{u} => IsLocallyNoetherian Y))

/-! ### The order of vanishing on an elementary étale chart -/

/-- **The order of vanishing along a prime divisor, read in the henselian local ring through an
elementary étale chart.** Let `(U, u)` be an elementary étale neighbourhood of the generic point
of a prime divisor `Z` of a locally Noetherian integral algebraic space `X`, with `U` affine,
reduced and locally Noetherian. If the pullback of an invertible rational function `f` to
`Q(Γ(U, 𝒪_U))` is a global section `a`, then `ord_Z(f)` is the length of the quotient of the
henselian local ring `𝒪^h_{X, ξ}` by the image of `a`. -/
theorem PrimeDivisor.ordRationalFunction_eq_ord_henselian (Z : PrimeDivisor B S hS X)
    (U : ElementaryEtaleNeighborhood B S hS X hX (Z.genericPoint B S hS X))
    [IsAffine U.scheme.left.1] [IsReduced U.scheme.left.1]
    [IsLocallyNoetherian U.scheme.left.1]
    (f : (rationalFunctions B S hS hX)ˣ) (a : Γ(U.scheme.left.1, ⊤))
    (ha : rationalFunctionsToTotalFractionRing B S hS hX U.scheme U.toSpace U.etale_toSpace
        (f : rationalFunctions B S hS hX) =
      algebraMap Γ(U.scheme.left.1, ⊤) (FractionRing Γ(U.scheme.left.1, ⊤)) a) :
    ordRationalFunction B S hS hX hInt hN f Z =
      ((Ring.ord ↥(Z.genericHenselianLocalRing B S hS hX (hInt.isDecentSpace B S hS X))
        (Z.neighborhoodSectionsToGenericHenselianLocalRing B S hS hX
          (hInt.isDecentSpace B S hS X) U a)).toNat : ℤ) := by
  set hdec := hInt.isDecentSpace B S hS X
  have : IsLocalRing ↥(Z.genericHenselianLocalRing B S hS hX hdec) :=
    henselianLocalRing_isLocalRing B S hS X hX (Z.genericPoint B S hS X) hdec
  have hemb : Z.rationalFunctionsToGenericTotalFractionRing B S hS hX hdec hInt hN
        (f : rationalFunctions B S hS hX) =
      algebraMap _ (Z.genericTotalFractionRing B S hS hX hdec)
        (Z.neighborhoodSectionsToGenericHenselianLocalRing B S hS hX hdec U a) := by
    rw [← Z.neighborhoodTotalFractionRingToGeneric_pullback_eq B S hS hX hdec hInt hN U, ha]
    exact IsLocalization.map_eq _ _
  have hunit : IsUnit (algebraMap _ (Z.genericTotalFractionRing B S hS hX hdec)
      (Z.neighborhoodSectionsToGenericHenselianLocalRing B S hS hX hdec U a)) :=
    hemb ▸ f.isUnit.map _
  have hnzd : Z.neighborhoodSectionsToGenericHenselianLocalRing B S hS hX hdec U a ∈
      (↥(Z.genericHenselianLocalRing B S hS hX hdec))⁰ :=
    mem_nonZeroDivisors_of_injective (IsFractionRing.injective _ _) hunit.mem_nonZeroDivisors
  rw [ordRationalFunction_eq_length_sub_length B S hS hX hInt hN f Z ⟨_, hnzd⟩ 1
    (by rw [hemb, IsLocalization.mk'_one]), OneMemClass.coe_one, Ring.ord_one]
  simp only [ENat.toNat_zero, Nat.cast_zero, sub_zero]

/-- **The order of vanishing along a prime divisor, read on an elementary étale chart.** Let
`(U, u)` be an elementary étale neighbourhood of the generic point of a prime divisor `Z` of a
locally Noetherian integral algebraic space `X`, with `U` affine, reduced and locally Noetherian.
If the pullback of an invertible rational function `f` to `Q(Γ(U, 𝒪_U))` is a global section
`a`, then `ord_Z(f)` is the length of `𝒪_{U, u} / a 𝒪_{U, u}`.

The scheme `U` need not be integral, and its local ring at `u` need not be a domain. -/
theorem PrimeDivisor.ordRationalFunction_eq_ord_germ (Z : PrimeDivisor B S hS X)
    (U : ElementaryEtaleNeighborhood B S hS X hX (Z.genericPoint B S hS X))
    [IsAffine U.scheme.left.1] [IsReduced U.scheme.left.1]
    [IsLocallyNoetherian U.scheme.left.1]
    (f : (rationalFunctions B S hS hX)ˣ) (a : Γ(U.scheme.left.1, ⊤))
    (ha : rationalFunctionsToTotalFractionRing B S hS hX U.scheme U.toSpace U.etale_toSpace
        (f : rationalFunctions B S hS hX) =
      algebraMap Γ(U.scheme.left.1, ⊤) (FractionRing Γ(U.scheme.left.1, ⊤)) a) :
    ordRationalFunction B S hS hX hInt hN f Z =
      ((Ring.ord (U.scheme.left.1.presheaf.stalk U.point)
        (U.scheme.left.1.presheaf.germ ⊤ U.point trivial a)).toNat : ℤ) := by
  set hdec := hInt.isDecentSpace B S hS X
  have : IsLocalRing ↥(Z.genericHenselianLocalRing B S hS hX hdec) :=
    henselianLocalRing_isLocalRing B S hS X hX (Z.genericPoint B S hS X) hdec
  rw [Z.ordRationalFunction_eq_ord_henselian B S hS hX hInt hN U f a ha]
  exact congrArg (fun n : ℕ∞ => ((n.toNat : ℕ) : ℤ))
    (ord_stalkToHenselianLocalRing B S hS hX hdec Z U
      (U.scheme.left.1.presheaf.germ ⊤ U.point trivial a))

/-! ### Elementary étale charts -/

/-- If the structure morphism `Spec κ(u) → S` of the residue-field point of a point `u` of an
object of the big fppf site is a monomorphism of schemes, then every morphism out of the
presheaf that residue-field point represents is a monomorphism: that presheaf takes at most one
value at every object, two morphisms into `Spec κ(u)` over `S` being equal. -/
theorem mono_yoneda_map_residueFieldMap_comp_of_mono_structure (U : BigFppfOver B S hS)
    (u : U.left.1) (hu : B.Contains (Spec (.of (U.left.1.residueField u))))
    (hmono : Mono (U.left.1.fromSpecResidueField u ≫ U.hom.1))
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (c : yoneda.obj U ⟶ F) :
    Mono (yoneda.map (residueFieldMap B S hS U u hu) ≫ c) := by
  have (T : (BigFppfOver B S hS)ᵒᵖ) :
      Mono ((yoneda.map (residueFieldMap B S hS U u hu) ≫ c).app T) := by
    rw [mono_iff_injective]
    intro f g _
    refine Over.OverMorphism.ext (ObjectProperty.hom_ext _ ?_)
    have hf := congrArg (fun m => m.1) (Over.w f)
    have hg := congrArg (fun m => m.1) (Over.w g)
    exact (cancel_mono (U.left.1.fromSpecResidueField u ≫ U.hom.1)).1 (hf.trans hg.symm)
  exact NatTrans.mono_of_mono_app _

/-- A morphism of spectra of fields which admits a section is an isomorphism: the ring map
`L → K` of the section is a field embedding which is surjective, being a retraction. -/
theorem isIso_of_comp_eq_id_spec_field {K L : Type u} [Field K] [Field L]
    (g : Spec (.of L) ⟶ Spec (.of K)) (s : Spec (.of K) ⟶ Spec (.of L)) (h : s ≫ g = 𝟙 _) :
    IsIso g := by
  obtain ⟨φ, rfl⟩ := Spec.map_surjective g
  obtain ⟨ψ, rfl⟩ := Spec.map_surjective s
  rw [← Spec.map_comp, Spec.map_eq_id] at h
  have hψ : Function.Bijective ψ.hom := by
    refine ⟨ψ.hom.injective, fun x => ⟨φ x, ?_⟩⟩
    rw [← CommRingCat.comp_apply, h]
    rfl
  have : IsIso ψ := (RingEquiv.ofBijective ψ.hom hψ).toCommRingCatIso.isIso_hom
  have hφ : φ = inv ψ := IsIso.eq_inv_of_inv_hom_id h
  rw [hφ]
  infer_instance

/-- At a point which is the image of a section of a scheme `Y` over a field `K`, the structure
morphism `Spec κ(y) → Spec K` of the residue field is a monomorphism, being an isomorphism: the
residue field at a rational point is `K`. -/
theorem mono_fromSpecResidueField_comp_of_section {Y : Scheme.{u}} {K : Type u} [Field K]
    (p : Y ⟶ Spec (.of K)) (σ : Spec (.of K) ⟶ Y) (hσ : σ ≫ p = 𝟙 _) :
    Mono (Y.fromSpecResidueField (σ (IsLocalRing.closedPoint K)) ≫ p) := by
  have h := Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K Y σ
  have := isIso_of_comp_eq_id_spec_field
    (Y.fromSpecResidueField (σ (IsLocalRing.closedPoint K)) ≫ p)
    (Spec.map (Scheme.descResidueField (Scheme.stalkClosedPointTo σ)))
    ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ p) h).trans hσ))
  exact @IsIso.mono_of_iso _ _ _ _ _ this

/-- If an étale chart is a monomorphism, so is its residue-field point at every point. -/
theorem mono_yoneda_map_residueFieldMap_comp_of_mono (U : BigFppfOver B S hS)
    (u : U.left.1) (hu : B.Contains (Spec (.of (U.left.1.residueField u))))
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (c : yoneda.obj U ⟶ F) [Mono c] :
    Mono (yoneda.map (residueFieldMap B S hS U u hu) ≫ c) :=
  have := mono_yoneda_map_residueFieldMap B S hS U u hu
  mono_comp _ _

/-- The point of a represented presheaf attached to the scheme point underlying a point of it is
that point. -/
theorem presheafPoint_pointsToScheme_eq (U : BigFppfOver B S hS)
    (p : points B S hS (yoneda.obj U))
    (hu : B.Contains (Spec (.of (U.left.1.residueField (pointsToScheme B S hS U p))))) :
    presheafPoint B S hS U (pointsToScheme B S hS U p) hu = p :=
  injective_pointsToScheme B S hS U (pointsToScheme_presheafPoint B S hS U _ hu)

/-- **An étale monomorphic chart is an elementary étale neighbourhood of each of its points.** -/
def elementaryEtaleNeighborhoodOfMonoChart (U : BigFppfOver B S hS)
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    (c : yoneda.obj U ⟶ F) (hc : IsEtale B S hS c) (hmono : Mono c)
    (p : points B S hS (yoneda.obj U)) (x : points B S hS F)
    (hx : pointsMap B S hS (yoneda.obj U) c p = x) :
    ElementaryEtaleNeighborhood B S hS F hF x where
  scheme := U
  point := pointsToScheme B S hS U p
  residueField_contained := B.residueField_spec_contains U.left.property _
  toSpace := c
  etale_toSpace := hc
  map_point := by rw [presheafPoint_pointsToScheme_eq]; exact hx
  mono_residueField := mono_yoneda_map_residueFieldMap_comp_of_mono B S hS U _ _ c

/-- **An étale chart is an elementary étale neighbourhood of the image of a point whose residue
field is that of the base**, in the sense that the structure morphism `Spec κ(u) → S` is a
monomorphism. -/
def elementaryEtaleNeighborhoodOfMonoStructure (U : BigFppfOver B S hS)
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    (c : yoneda.obj U ⟶ F) (hc : IsEtale B S hS c) (u : U.left.1)
    (hmono : Mono (U.left.1.fromSpecResidueField u ≫ U.hom.1)) (x : points B S hS F)
    (hx : pointsMap B S hS (yoneda.obj U) c
      (presheafPoint B S hS U u (B.residueField_spec_contains U.left.property u)) = x) :
    ElementaryEtaleNeighborhood B S hS F hF x where
  scheme := U
  point := u
  residueField_contained := B.residueField_spec_contains U.left.property u
  toSpace := c
  etale_toSpace := hc
  map_point := hx
  mono_residueField := mono_yoneda_map_residueFieldMap_comp_of_mono_structure B S hS U u _ hmono c

end AlgebraicGeometry.Space

end
