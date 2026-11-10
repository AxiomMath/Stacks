module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Birational.IrreducibleCriterion
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.IntegralBirational
public import StacksFrontier.AlgebraicGeometry.Pushout.Dominant
public import StacksFrontier.AlgebraicGeometry.Pushout.FiniteType
public import StacksFrontier.AlgebraicGeometry.Pushout.Separation
public import StacksFrontier.AlgebraicGeometry.Pushout.SquareSections
public import StacksFrontier.AlgebraicGeometry.Scheme.Affine.PuncturedPlaneSections
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Basic
public import StacksFrontier.Examples.Scheme.PinchedPlane.ClosedImmersion

/-!
# A variety whose normalization is quasi-affine but which is not quasi-affine

Over any field there is a variety that is not quasi-affine although its normalization is. The
example is the punctured plane `A²_k ∖ {0}` with its two punctured coordinate axes glued to one
another along the parametrizations `(0, t)` and `(t⁻¹, 0)`: the pushout of the closed immersion
of the two axes into the punctured plane along the morphism folding them onto a single axis.

That pushout is a variety: it is reduced and irreducible because the punctured plane dominates
it, separated and of finite type because both schemes being glued are. The map from the
punctured plane to it is integral and surjective, and an isomorphism away from the glued axis,
so it is birational; therefore normalizing the pushout cannot distinguish it from the punctured
plane, and the punctured plane is quasi-affine.

The pushout is not quasi-affine, however, because its global functions cannot separate the two
points of the axis that were glued: a function on the pushout restricts to one function on the
punctured plane whose two restrictions to the axes agree, and such a function is constant along
the axis. The map to the spectrum of the global functions therefore collapses the whole axis,
so it is not injective, whereas for a quasi-affine scheme it is an open immersion.

## Main definitions

* `Stacks.Examples.PinchedPlane.pinchingSituation`: the pushout datum of Tag 0ECI used here.
* `Stacks.Examples.PinchedPlane.pinchedPlane`: the resulting variety, and
  `Stacks.Examples.PinchedPlane.pinchedPlaneToBase` its structure morphism.

## Main results

* `Stacks.Examples.PinchedPlane.pinchedPlane_isVariety`: the pinched plane is a variety.
* `Stacks.Examples.PinchedPlane.normalization_isQuasiAffine`: its normalization is quasi-affine.
* `Stacks.Examples.PinchedPlane.not_isQuasiAffine`: it is not itself quasi-affine.
* `Stacks.Examples.exists_isVariety_normalization_isQuasiAffine_not_isQuasiAffine`: Tag 0272.

## References

* [Stacks Project, Tag 0272](https://stacks.math.columbia.edu/tag/0272)
* [Stacks Project, Section 110.17 (Tag 0271)](https://stacks.math.columbia.edu/tag/0271)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Examples.PinchedPlane

variable (k : Type u) [Field k]

section Structure

/-- The structure morphism of the punctured plane over `k`. -/
def puncturedPlaneStructure : puncturedPlane k ⟶ Spec (.of k) :=
  (puncturedPlaneOpen k).ι ≫
    Spec.map (CommRingCat.ofHom (algebraMap k (affinePlaneRing k)))

/-- The structure morphism of the punctured axis over `k`. -/
def axisStructure : Spec (.of (LaurentPolynomial k)) ⟶ Spec (.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k (LaurentPolynomial k)))

/-- The structure morphism of the disjoint union of the two punctured axes over `k`. -/
def axesStructure :
    Spec (.of (LaurentPolynomial k × LaurentPolynomial k)) ⟶ Spec (.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k (LaurentPolynomial k × LaurentPolynomial k)))

/-- The closed immersion of the two axes is a morphism over `k`. -/
theorem axesToPuncturedPlane_structure :
    axesToPuncturedPlane k ≫ puncturedPlaneStructure k = axesStructure k := by
  rw [puncturedPlaneStructure, ← Category.assoc, axesToPuncturedPlane_ι, axesStructure,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun g => Spec.map (CommRingCat.ofHom g))
    (axisRestrictions k).comp_algebraMap

/-- The folding morphism is a morphism over `k`. -/
theorem axesToAxis_structure : axesToAxis k ≫ axisStructure k = axesStructure k := by
  rw [axesToAxis, axisStructure, axesStructure, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 1

/-- The punctured plane is of finite type over `k`. -/
instance puncturedPlaneStructure_locallyOfFiniteType :
    LocallyOfFiniteType (puncturedPlaneStructure k) := by
  have : LocallyOfFiniteType
      (Spec.map (CommRingCat.ofHom (algebraMap k (affinePlaneRing k)))) :=
    HasRingHomProperty.Spec_iff.mpr (RingHom.finiteType_algebraMap.mpr inferInstance)
  unfold puncturedPlaneStructure
  infer_instance

/-- The punctured axis is of finite type over `k`. -/
instance axisStructure_locallyOfFiniteType : LocallyOfFiniteType (axisStructure k) :=
  HasRingHomProperty.Spec_iff.mpr (RingHom.finiteType_algebraMap.mpr inferInstance)

/-- The disjoint union of the two axes is of finite type over `k`. -/
instance axesStructure_locallyOfFiniteType : LocallyOfFiniteType (axesStructure k) :=
  HasRingHomProperty.Spec_iff.mpr (RingHom.finiteType_algebraMap.mpr inferInstance)

end Structure

section Situation

/-- **The pinching datum.** The punctured plane, the two punctured axes inside it as a closed
subscheme, and the morphism folding those axes onto a single copy of `Spec k[t, 1/t]`: a
situation of [Stacks Project, Tag 0ECI], because both axes lie in one affine chart. -/
abbrev pinchingSituation : PushoutAlongClosedImmersionAndIntegralSituation.{u} where
  S := Spec (.of k)
  X := puncturedPlane k
  Y := Spec (.of (LaurentPolynomial k))
  Z := Spec (.of (LaurentPolynomial k × LaurentPolynomial k))
  pX := puncturedPlaneStructure k
  pY := axisStructure k
  pZ := axesStructure k
  i := axesToPuncturedPlane k
  j := axesToAxis k
  i_over := axesToPuncturedPlane_structure k
  j_over := axesToAxis_structure k
  fiber_preimage_subset_affine _ :=
    ⟨pinchingChartOpen k, isAffineOpen_pinchingChartOpen k,
      fun z _ => axesToPuncturedPlane_mem_pinchingChartOpen k z⟩

/-- The folding morphism is scheme-theoretically dominant, being
surjective onto a reduced scheme. -/
instance axesToAxis_isSchemeTheoreticallyDominant :
    IsSchemeTheoreticallyDominant (axesToAxis k) :=
  IsSchemeTheoreticallyDominant.of_isDominant _

/-- The plane pinched along the identification of its two punctured axes. -/
abbrev pinchedPlane : Scheme.{u} := pushoutScheme (pinchingSituation k)

/-- The structure morphism of the pinched plane over `k`. -/
abbrev pinchedPlaneToBase : pinchedPlane k ⟶ Spec (.of k) :=
  pushoutToBase (pinchingSituation k)

/-- The pinched plane is integral. -/
instance pinchedPlane_isIntegral : IsIntegral (pinchedPlane k) :=
  isIntegral_of_irreducibleSpace_of_isReduced _

/-- The pinched plane is quasi-compact over `k`. -/
instance pinchedPlaneToBase_quasiCompact : QuasiCompact (pinchedPlaneToBase k) :=
  quasiCompact_of_compactSpace _

/-- **The pinched plane is a variety.** -/
theorem pinchedPlane_isVariety : IsVariety k (pinchedPlaneToBase k) := IsVariety.mk

/-- The pinched plane is Noetherian, being quasi-compact and of
finite type over a field. -/
instance pinchedPlane_isNoetherian : IsNoetherian (pinchedPlane k) := by
  have := LocallyOfFiniteType.isLocallyNoetherian (pinchedPlaneToBase k)
  exact ⟨⟩

/-- The punctured plane is Noetherian, being quasi-compact and of
finite type over a field. -/
instance puncturedPlane_isNoetherian : IsNoetherian (puncturedPlane k) := by
  have := LocallyOfFiniteType.isLocallyNoetherian (puncturedPlaneStructure k)
  exact ⟨⟩

/-- Every quasi-compact open of the pinched plane has finitely many irreducible components:
the pinched plane is a Noetherian space. -/
theorem pinchedPlane_finite_irreducibleComponents
    (U : (pinchedPlane k).Opens) (_ : IsCompact (U : Set (pinchedPlane k))) :
    (irreducibleComponents U).Finite :=
  @NoetherianSpace.finite_irreducibleComponents (U : Set (pinchedPlane k)) _ inferInstance

end Situation

section Birational

/-- The locus of the pinched plane away from the glued axis. -/
abbrev offAxis : (pinchedPlane k).Opens :=
  ⟨(Set.range (pushoutInr (pinchingSituation k)))ᶜ,
    (pushoutInr (pinchingSituation k)).isClosedEmbedding.isClosed_range.isOpen_compl⟩

/-- The glued axis is disjoint from the locus away from it. -/
theorem pushoutInr_preimage_offAxis :
    pushoutInr (pinchingSituation k) ⁻¹ᵁ offAxis k = ⊥ := by
  ext y
  simp [offAxis]

/-- The generic point of the punctured plane does not lie on the glued axis: the axes are
contained in the zero locus of `xy`, which misses the generic point. -/
theorem genericPoint_mem_offAxis :
    pushoutInl (pinchingSituation k) (genericPoint (puncturedPlane k)) ∈ offAxis k := by
  rintro ⟨y, hy⟩
  obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback
    (genericPoint (puncturedPlane k)) y hy.symm
  have hzero := axesToPuncturedPlane_mem_zeroLocus k
    ((pushoutSquare_isPullback (pinchingSituation k)).isoPullback.inv z)
  have hz' : axesToPuncturedPlane k
      ((pushoutSquare_isPullback (pinchingSituation k)).isoPullback.inv z) =
      genericPoint (puncturedPlane k) := by
    rw [← Scheme.Hom.comp_apply]
    exact (congrArg (fun f => f z)
      (pushoutSquare_isPullback (pinchingSituation k)).isoPullback_inv_fst).trans hz
  rw [hz', genericPoint_eq_of_isOpenImmersion (puncturedPlaneOpen k).ι,
    genericPoint_eq_bot_of_affine] at hzero
  change (MvPolynomial.X 0 * MvPolynomial.X 1 : affinePlaneRing k) = 0 at hzero
  exact mul_ne_zero (MvPolynomial.X_ne_zero 0) (MvPolynomial.X_ne_zero 1) hzero

/-- The map from the punctured plane to the pinched plane is an isomorphism on the local ring
at the generic point: it is already an isomorphism over the whole locus away from the glued
axis, which contains the generic point. -/
theorem isIso_stalkMap_genericPoint :
    IsIso ((pushoutInl (pinchingSituation k)).stalkMap
      (genericPoint (puncturedPlane k))) := by
  have hiso : IsIso (pushoutInl (pinchingSituation k) ∣_ offAxis k) :=
    pushoutInl_isIso_morphismRestrict (pinchingSituation k) (offAxis k)
      (pushoutInr_preimage_offAxis k)
  have hoi : IsOpenImmersion (pushoutInl (pinchingSituation k) ∣_ offAxis k) := by
    have := hiso
    infer_instance
  have hstalk : IsIso ((pushoutInl (pinchingSituation k) ∣_ offAxis k).stalkMap
      ⟨genericPoint (puncturedPlane k), genericPoint_mem_offAxis k⟩) :=
    @IsOpenImmersion.instIsIsoCommRingCatStalkMap _ _ _ hoi _
  have harr := (pushoutInl (pinchingSituation k)).resLEStalkMap
    (U := offAxis k) (V := pushoutInl (pinchingSituation k) ⁻¹ᵁ offAxis k) (e := le_rfl)
    ⟨genericPoint (puncturedPlane k), genericPoint_mem_offAxis k⟩
  refine (Arrow.isIso_iff_isIso_of_isIso harr.hom).mp ?_
  rw [(pushoutInl (pinchingSituation k)).resLE_eq_morphismRestrict]
  exact hstalk

/-- **The pinched plane is dominated birationally by the punctured plane.** -/
theorem pushoutInl_isBirational : IsBirational (pushoutInl (pinchingSituation k)) := by
  have := isIso_stalkMap_genericPoint k
  exact isBirational_of_isIso_stalkMap_genericPoint _

/-- **The normalization of the pinched plane is quasi-affine.** The normalization of the
pinched plane is also a normalization of the punctured plane, and the latter is quasi-affine, so
the normalization is affine over a quasi-affine scheme. -/
theorem normalization_isQuasiAffine :
    Scheme.IsQuasiAffine (Scheme.normalizationScheme (pinchedPlane k)
      (pinchedPlane_finite_irreducibleComponents k)) := by
  obtain ⟨-, g, -, hg, -⟩ :=
    exists_normalizationFactorization_of_isIntegralHom_of_isBirational
      (pinchedPlane_finite_irreducibleComponents k) (pushoutInl (pinchingSituation k))
      (fun U _ => @NoetherianSpace.finite_irreducibleComponents
        (pushoutInl (pinchingSituation k) ⁻¹ᵁ U : Set (puncturedPlane k)) _ inferInstance)
      (pushoutInl_isBirational k)
  have hcomp : IsIntegralHom (g ≫ pushoutInl (pinchingSituation k)) := by
    rw [hg]
    dsimp [Scheme.normalization]
    infer_instance
  have : IsIntegralHom g := IsIntegralHom.of_comp g (pushoutInl (pinchingSituation k))
  exact Scheme.IsQuasiAffine.of_isAffineHom g

end Birational

section GlobalSections

/-- The coordinate ring of the plane, as the ring of global functions on the punctured plane.
This is Tag 01IL. -/
def planeToGlobalSections :
    CommRingCat.of (affinePlaneRing k) ⟶ Γ(puncturedPlane k, ⊤) :=
  (Scheme.ΓSpecIso (.of (affinePlaneRing k))).inv ≫ (puncturedPlaneOpen k).ι.appTop

/-- The global functions on the punctured plane are the polynomials
on the plane. -/
instance planeToGlobalSections_isIso : IsIso (planeToGlobalSections k) :=
  isIso_coordinateRingToGlobalSections (puncturedAffinePlaneOf k)

/-- A morphism from an affine scheme into the punctured plane acts on global functions by the
ring map it comes from. -/
theorem planeToGlobalSections_comp
    (j : Spec (.of (LaurentPolynomial k)) ⟶ puncturedPlane k)
    (r : affinePlaneRing k →+* LaurentPolynomial k)
    (hj : j ≫ (puncturedPlaneOpen k).ι = Spec.map (CommRingCat.ofHom r)) :
    planeToGlobalSections k ≫ j.appTop ≫
        (Scheme.ΓSpecIso (.of (LaurentPolynomial k))).hom = CommRingCat.ofHom r := by
  calc
    _ = (Scheme.ΓSpecIso (.of (affinePlaneRing k))).inv ≫
        (j ≫ (puncturedPlaneOpen k).ι).appTop ≫
          (Scheme.ΓSpecIso (.of (LaurentPolynomial k))).hom := by
      rw [planeToGlobalSections, Scheme.Hom.comp_appTop]
      simp only [Category.assoc]
    _ = _ := by rw [hj, Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]

/-- A section of the folding morphism, viewed in the punctured plane, lands on the glued axis. -/
private theorem section_comp_pushoutInl (s : Spec (.of (LaurentPolynomial k)) ⟶
      Spec (.of (LaurentPolynomial k × LaurentPolynomial k)))
    (hs : s ≫ axesToAxis k = 𝟙 _) :
    (s ≫ axesToPuncturedPlane k) ≫ pushoutInl (pinchingSituation k) =
      pushoutInr (pinchingSituation k) := by
  rw [Category.assoc, (pushoutAlongClosedImmersionAndIntegral (pinchingSituation k)).isPushout.w,
    ← Category.assoc, hs, Category.id_comp]

/-- The first axis and the glued axis agree in the pinched plane. -/
theorem firstAxisToPuncturedPlane_pushoutInl :
    firstAxisToPuncturedPlane k ≫ pushoutInl (pinchingSituation k) =
      pushoutInr (pinchingSituation k) :=
  section_comp_pushoutInl k _ (firstAxisToAxes_axesToAxis k)

/-- The second axis and the glued axis agree in the pinched plane. -/
theorem secondAxisToPuncturedPlane_pushoutInl :
    secondAxisToPuncturedPlane k ≫ pushoutInl (pinchingSituation k) =
      pushoutInr (pinchingSituation k) :=
  section_comp_pushoutInl k _ (secondAxisToAxes_axesToAxis k)

/-- If a polynomial on the plane gives the same global function as `t` on the punctured plane,
then restricting `t` to the glued axis agrees with restricting the polynomial to an axis. -/
private theorem appTop_pushoutInr_eq_of_axis
    (a : Spec (.of (LaurentPolynomial k)) ⟶ puncturedPlane k)
    (r : affinePlaneRing k →+* LaurentPolynomial k)
    (hr : a ≫ (puncturedPlaneOpen k).ι = Spec.map (CommRingCat.ofHom r))
    (ha : a ≫ pushoutInl (pinchingSituation k) = pushoutInr (pinchingSituation k))
    (p : affinePlaneRing k) (t : Γ(pinchedPlane k, ⊤))
    (hp : planeToGlobalSections k p = (pushoutInl (pinchingSituation k)).appTop t) :
    ((pushoutInr (pinchingSituation k)).appTop ≫
      (Scheme.ΓSpecIso (.of (LaurentPolynomial k))).hom) t = r p := by
  have h := congrArg (fun v => (a.appTop ≫ (Scheme.ΓSpecIso (.of (LaurentPolynomial k))).hom).hom v)
    hp
  change (planeToGlobalSections k ≫ a.appTop ≫
      (Scheme.ΓSpecIso (.of (LaurentPolynomial k))).hom) p =
    ((pushoutInl (pinchingSituation k)).appTop ≫ a.appTop ≫
      (Scheme.ΓSpecIso (.of (LaurentPolynomial k))).hom) t at h
  rw [planeToGlobalSections_comp k a r hr, ← Category.assoc, ← Scheme.Hom.comp_appTop, ha] at h
  exact h.symm

/-- **The global functions on the pinched plane are constant along the glued axis.** A global
function on the pinched plane comes from a polynomial on the plane whose restrictions to the two
axes agree, and such a polynomial restricts to a constant. -/
theorem exists_algebraMap_eq_appTop (t : Γ(pinchedPlane k, ⊤)) :
    ∃ c : k, ((pushoutInr (pinchingSituation k)).appTop ≫
        (Scheme.ΓSpecIso (.of (LaurentPolynomial k))).hom) t =
      algebraMap k (LaurentPolynomial k) c := by
  obtain ⟨p, hp⟩ := (ConcreteCategory.bijective_of_isIso (planeToGlobalSections k)).2
    ((pushoutInl (pinchingSituation k)).appTop t)
  have hfirst := appTop_pushoutInr_eq_of_axis k _ _ (firstAxisToPuncturedPlane_ι k)
    (firstAxisToPuncturedPlane_pushoutInl k) p t hp
  have hsecond := appTop_pushoutInr_eq_of_axis k _ _ (secondAxisToPuncturedPlane_ι k)
    (secondAxisToPuncturedPlane_pushoutInl k) p t hp
  obtain ⟨c, hc⟩ :=
    exists_algebraMap_eq_of_restrictions_eq k p (hfirst.symm.trans hsecond)
  exact ⟨c, hfirst.trans hc⟩

end GlobalSections

section NotQuasiAffine

/-- Evaluation of a Laurent polynomial at the point `t = 1`. -/
def axisEvalOne : LaurentPolynomial k →+* k :=
  LaurentPolynomial.eval₂ (RingHom.id k) (1 : kˣ)

/-- Evaluation at `t = 1` is a retraction of the ground field. -/
@[simp]
theorem axisEvalOne_algebraMap (c : k) :
    axisEvalOne k (algebraMap k (LaurentPolynomial k) c) = c := by
  rw [← LaurentPolynomial.C_eq_algebraMap, axisEvalOne, LaurentPolynomial.eval₂_C]
  rfl

/-- Every power of the coordinate evaluates to `1` at `t = 1`. -/
@[simp]
theorem axisEvalOne_T (n : ℤ) : axisEvalOne k (LaurentPolynomial.T n) = 1 := by
  rw [axisEvalOne, LaurentPolynomial.eval₂_T]
  simp

/-- The coordinate of the axis is not the constant `1`: comparing
coefficients in degree one, one side is `1` and the other `0`. -/
theorem T_one_sub_one_ne_zero :
    (LaurentPolynomial.T 1 : LaurentPolynomial k) - 1 ≠ 0 := by
  intro h
  have hc := congrArg (fun z : LaurentPolynomial k => z.coeff 1) h
  simp only [AddMonoidAlgebra.coeff_sub, Finsupp.coe_sub, Pi.sub_apply,
    LaurentPolynomial.T_apply, AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero,
    Pi.zero_apply] at hc
  rw [← LaurentPolynomial.T_zero, LaurentPolynomial.T_apply] at hc
  norm_num at hc

/-- A ring map into `k[t, 1/t]` whose image consists of constants cannot induce an injection of
spectra: the zero ideal and the ideal of functions vanishing at `t = 1` have the same
preimage. -/
theorem not_injective_specMap_of_range_constants {R : Type u} [CommRing R]
    (f : R →+* LaurentPolynomial k)
    (hf : ∀ r, ∃ c : k, f r = algebraMap k (LaurentPolynomial k) c) :
    ¬ Function.Injective (Spec.map (CommRingCat.ofHom f)) := by
  intro hinj
  have hne : (⊥ : PrimeSpectrum (LaurentPolynomial k)) ≠
      PrimeSpectrum.comap (axisEvalOne k) (⊥ : PrimeSpectrum k) := by
    intro h
    have hp : (LaurentPolynomial.T 1 : LaurentPolynomial k) - 1 ∈
        (PrimeSpectrum.comap (axisEvalOne k) (⊥ : PrimeSpectrum k)).asIdeal := by
      change axisEvalOne k (LaurentPolynomial.T 1 - 1) = 0
      simp
    rw [← h, PrimeSpectrum.asIdeal_bot, Ideal.mem_bot] at hp
    exact T_one_sub_one_ne_zero k hp
  refine hne (hinj ?_)
  change PrimeSpectrum.comap f _ = PrimeSpectrum.comap f _
  refine PrimeSpectrum.ext (Ideal.ext fun r => ?_)
  change f r = 0 ↔ axisEvalOne k (f r) = 0
  obtain ⟨c, hc⟩ := hf r
  have hiff : algebraMap k (LaurentPolynomial k) c = 0 ↔ c = 0 := by
    rw [← map_zero (algebraMap k (LaurentPolynomial k))]
    exact (RingHom.injective (algebraMap k (LaurentPolynomial k))).eq_iff
  rw [hc, axisEvalOne_algebraMap]
  exact hiff

/-- **The pinched plane is not quasi-affine.** Its global functions are constant along the
glued axis, so the canonical map to the spectrum of the global functions collapses that axis;
for a quasi-affine scheme that map is an open immersion, hence injective. -/
theorem not_isQuasiAffine : ¬ Scheme.IsQuasiAffine (pinchedPlane k) := by
  intro h
  refine not_injective_specMap_of_range_constants k
    ((pushoutInr (pinchingSituation k)).appTop ≫
      (Scheme.ΓSpecIso (.of (LaurentPolynomial k))).hom).hom
    (exists_algebraMap_eq_appTop k) ?_
  change Function.Injective (Spec.map ((pushoutInr (pinchingSituation k)).appTop ≫
    (Scheme.ΓSpecIso (.of (LaurentPolynomial k))).hom))
  rw [Spec.map_comp, SpecMap_ΓSpecIso_hom, ← Scheme.toSpecΓ_naturality]
  exact (pinchedPlane k).toSpecΓ.isOpenEmbedding.injective.comp
    (pushoutInr (pinchingSituation k)).isClosedEmbedding.injective

end NotQuasiAffine

end Stacks.Examples.PinchedPlane

namespace Stacks.Examples

/-- **Stacks Project, Tag 0272.** Over any field there is a variety whose normalization is
quasi-affine but which is itself not quasi-affine: the punctured plane with its two punctured
coordinate axes glued to one another. -/
@[stacks 0272]
theorem exists_isVariety_normalization_isQuasiAffine_not_isQuasiAffine
    (k : Type u) [Field k] :
    ∃ (X : Scheme.{u}) (f : X ⟶ Spec (.of k))
      (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite),
      AlgebraicGeometry.IsVariety k f ∧
        Scheme.IsQuasiAffine (Scheme.normalizationScheme X hX) ∧
        ¬ Scheme.IsQuasiAffine X :=
  ⟨PinchedPlane.pinchedPlane k, PinchedPlane.pinchedPlaneToBase k,
    PinchedPlane.pinchedPlane_finite_irreducibleComponents k,
    PinchedPlane.pinchedPlane_isVariety k,
    PinchedPlane.normalization_isQuasiAffine k, PinchedPlane.not_isQuasiAffine k⟩

end Stacks.Examples

end
