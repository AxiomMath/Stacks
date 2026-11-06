module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.FormalCurve.Algebraization
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.InfinitesimalNeighbourhood.Flatness
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.FppfLocalTarget
public import StacksFrontier.Deformation.Examples.Geometric.SchemesUnobstructed
public import StacksFrontier.Deformation.Examples.Geometric.SmoothingCriterion
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.Zero
public import StacksFrontier.AlgebraicGeometry.QuasiProjective.HProjective
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.ProjectiveSchemes
public import StacksFrontier.AlgebraicGeometry.AmpleWire.Basic
public import StacksFrontier.Deformation.Examples.Geometric.SmoothingZeroDimensional
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.InfinitesimalNeighbourhood.FlatnessKernelPowers

/-!
# Smoothing a proper curve with isolated complete intersection singularities

Let `k` be a field and `S = Spec k⟦t⟧` the formal disc, with thickenings
`Sₙ = Spec (k⟦t⟧ ⧸ (t) ^ (n + 1))`. This file carries out the second half of the proof of
[Stacks, Tag 0E7Y]: a cartesian tower of flat schemes `Xₙ ⟶ Sₙ`, whose bottom `X₀` is proper over
`k`, Cohen–Macaulay and equidimensional of dimension one, and which satisfies the source's
Fitting-ideal clause at some level, is the formal completion of a flat projective `Y ⟶ S` with
smooth generic fibre and special fibre `X₀`.

The steps are the source's.

* The tower algebraizes to an H-projective `Y ⟶ S` by [Stacks, Tag 0E7R]
  (`Stacks.FormalCurve.exists_isProjectiveMorphism_of_topologicalKrullDim_le_one`).
* `Y ⟶ S` is flat by [Stacks, Tag 0D4G]: at a point over the closed point of `S` this is
  `AlgebraicGeometry.flat_stalkMap_of_flat_pullbacks_spec_quotient_pow`, and at a point over the
  generic point the local ring of `S` is a field
  (`Deformation.Examples.Smoothing.flat_of_flat_pullback_adicThickeningι`).
* The generic fibre is smooth by [Stacks, Tag 0E7T]
  (`Deformation.Examples.SmoothingCriterion.smooth_genericFibre_of_pow_mem_fittingIdeal`), once
  the fibre over the closed point is identified with `X₀`
  (`Deformation.Examples.Smoothing.exists_iso_comp_ι_eq_fromSpecResidueField`).

## Main results

* `flat_of_flat_pullback_adicThickeningι`: flatness over the formal disc is detected on the
  thickenings.
* `exists_flat_isProjective_smoothing_of_tower`: the tower algebraizes to a smoothing.
* `exists_flat_finite_projective_smoothing_of_topologicalKrullDim_le_zero`: the dimension-zero
  piece of the source's decomposition, as a scheme over `k`.

## References

* [The Stacks Project, Tag 0E7Y](https://stacks.math.columbia.edu/tag/0E7Y)
* [The Stacks Project, Tag 0E7R](https://stacks.math.columbia.edu/tag/0E7R)
* [The Stacks Project, Tag 0D4G](https://stacks.math.columbia.edu/tag/0D4G)
* [The Stacks Project, Tag 0E7T](https://stacks.math.columbia.edu/tag/0E7T)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Deformation.Examples.Smoothing

open Deformation.Examples.SmoothingCriterion

variable (k : Type u) [Field k]

/-- The ideal `(t)` of the formal disc `k⟦t⟧`. -/
abbrev discIdeal : Ideal (PowerSeries k) := Ideal.span {(PowerSeries.X : PowerSeries k)}

/-- The ideal `(t)` is the maximal ideal of `k⟦t⟧`. -/
theorem discIdeal_eq_maximalIdeal :
    discIdeal k = IsLocalRing.maximalIdeal (PowerSeries k) :=
  (PowerSeries.maximalIdeal_eq_span_X).symm

/-- The ideal `(t)` of `k⟦t⟧` is maximal. -/
instance : (discIdeal k).IsMaximal := by
  rw [discIdeal_eq_maximalIdeal]
  infer_instance

/-- A prime of `k⟦t⟧` is either zero or `(t)`. -/
theorem eq_bot_or_discIdeal_le (p : Ideal (PowerSeries k)) [p.IsPrime] :
    p = ⊥ ∨ discIdeal k ≤ p := by
  rcases eq_or_ne p ⊥ with h | h
  · exact Or.inl h
  · right
    rw [discIdeal_eq_maximalIdeal,
      IsLocalRing.eq_maximalIdeal (Ideal.IsPrime.isMaximal ‹_› h)]

/-- The constant coefficient, read on `k⟦t⟧ ⧸ (t) ^ (0 + 1)`. -/
def quotientConstantCoeff : PowerSeries k ⧸ discIdeal k ^ (0 + 1) →+* k :=
  Ideal.Quotient.lift _ PowerSeries.constantCoeff (fun a ha => by
    rw [zero_add, pow_one] at ha
    exact RingHom.mem_ker.mp (by rwa [PowerSeries.ker_coeff_eq_max_ideal,
      ← discIdeal_eq_maximalIdeal]))

/-- `quotientConstantCoeff` sends the image of `a : k` in `k⟦t⟧ ⧸ (t) ^ (0 + 1)` to `a`. -/
theorem quotientConstantCoeff_algebraMap (a : k) :
    quotientConstantCoeff k (algebraMap k (PowerSeries k ⧸ discIdeal k ^ (0 + 1)) a) = a := by
  rw [← Ideal.Quotient.mk_algebraMap]
  simp [quotientConstantCoeff, PowerSeries.algebraMap_eq]

/-- Every element of `k⟦t⟧ ⧸ (t) ^ (0 + 1)` is the image of its constant coefficient. -/
theorem algebraMap_quotientConstantCoeff (b : PowerSeries k ⧸ discIdeal k ^ (0 + 1)) :
    algebraMap k _ (quotientConstantCoeff k b) = b := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective b
  rw [← Ideal.Quotient.mk_algebraMap, Eq.comm, Ideal.Quotient.eq]
  rw [show quotientConstantCoeff k (Ideal.Quotient.mk (discIdeal k ^ (0 + 1)) a) =
      PowerSeries.constantCoeff a from rfl, pow_one]
  apply Ideal.mem_span_singleton.mpr
  rw [PowerSeries.X_dvd_iff]
  simp [PowerSeries.algebraMap_eq]

/-- `Spec k` is the bottom thickening `Spec (k⟦t⟧ ⧸ (t))`, as schemes over `Spec k⟦t⟧`. -/
def specBottomIso :
    Spec (.of k) ≅ adicThickening (PowerSeries k) (discIdeal k) 0 :=
  Scheme.Spec.mapIso (RingEquiv.toCommRingCatIso
    { quotientConstantCoeff k with
      invFun := algebraMap k _
      left_inv := algebraMap_quotientConstantCoeff k
      right_inv := quotientConstantCoeff_algebraMap k }).op

/-- The inverse of `specBottomIso` is the morphism induced by the structure map
`k → k⟦t⟧ ⧸ (t) ^ (0 + 1)`. -/
theorem specBottomIso_inv :
    (specBottomIso k).inv =
      Spec.map (CommRingCat.ofHom (algebraMap k (PowerSeries k ⧸ discIdeal k ^ (0 + 1)))) :=
  rfl

/-- Composed with the closed immersion of the bottom thickening into `Spec k⟦t⟧`, `specBottomIso`
is the morphism induced by the constant coefficient `k⟦t⟧ → k`. -/
theorem specBottomIso_hom_comp_ι :
    (specBottomIso k).hom ≫ adicThickeningι (PowerSeries k) (discIdeal k) 0 =
      Spec.map (CommRingCat.ofHom (PowerSeries.constantCoeff (R := k))) := by
  rw [specBottomIso, adicThickeningι]
  show Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp]
  rfl

/-- The prime ideal of the closed point of `Spec k⟦t⟧` is maximal. -/
instance : (IsLocalRing.closedPoint (PowerSeries k)).asIdeal.IsMaximal :=
  IsLocalRing.maximalIdeal.isMaximal _

/-- The residue field of `k⟦t⟧` at `(t)` is the bottom quotient `k⟦t⟧ ⧸ (t) ^ (0 + 1)`. -/
def quotientResidueFieldEquiv :
    PowerSeries k ⧸ discIdeal k ^ (0 + 1) ≃+*
      (IsLocalRing.closedPoint (PowerSeries k)).asIdeal.ResidueField :=
  (Ideal.quotEquivOfEq (by
      rw [zero_add, pow_one, discIdeal_eq_maximalIdeal]
      rfl)).trans
    (RingEquiv.ofBijective _
      (IsLocalRing.closedPoint (PowerSeries k)).asIdeal.bijective_algebraMap_quotient_residueField)

/-- `quotientResidueFieldEquiv` sends the class of `a : k⟦t⟧` to the image of `a` in the residue
field. -/
theorem quotientResidueFieldEquiv_mk (a : PowerSeries k) :
    quotientResidueFieldEquiv k (Ideal.Quotient.mk _ a) =
      algebraMap (PowerSeries k)
        (IsLocalRing.closedPoint (PowerSeries k)).asIdeal.ResidueField a := by
  rw [IsScalarTower.algebraMap_apply (PowerSeries k)
    (PowerSeries k ⧸ (IsLocalRing.closedPoint (PowerSeries k)).asIdeal)]
  simp [quotientResidueFieldEquiv, Ideal.quotEquivOfEq_mk]

/-- The closed point of the formal disc, as the spectrum of its residue field, is the bottom
thickening `Spec (k⟦t⟧ ⧸ (t))`, over `Spec k⟦t⟧`. -/
theorem exists_iso_comp_ι_eq_fromSpecResidueField :
    ∃ E : Spec ((Spec (.of (PowerSeries k))).residueField
        (IsLocalRing.closedPoint (PowerSeries k))) ≅
        adicThickening (PowerSeries k) (discIdeal k) 0,
      E.hom ≫ adicThickeningι (PowerSeries k) (discIdeal k) 0 =
        (Spec (.of (PowerSeries k))).fromSpecResidueField
          (IsLocalRing.closedPoint (PowerSeries k)) := by
  let x : Spec (.of (PowerSeries k)) := IsLocalRing.closedPoint (PowerSeries k)
  let E' := Scheme.Spec.mapIso (quotientResidueFieldEquiv k).toCommRingCatIso.op
  refine ⟨asIso (Spec.map (Scheme.Spec.residueFieldIso (.of (PowerSeries k)) x).inv) ≪≫ E', ?_⟩
  rw [← Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField (.of (PowerSeries k)) x]
  show Spec.map _ ≫ Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp]
  congr 2

/-- **Flatness over the formal disc from flatness over its thickenings.** A morphism
`g : Y ⟶ Spec k⟦t⟧` from a locally Noetherian scheme is flat as soon as its base change to every
thickening `Spec (k⟦t⟧ ⧸ (t ^ (n + 1)))` is flat. Over the closed point this is
[Stacks, Tag 0D4G]; over the generic point the local ring of the base is a field. -/
theorem flat_of_flat_pullback_adicThickeningι {Y : Scheme.{u}} [IsLocallyNoetherian Y]
    (g : Y ⟶ Spec (.of (PowerSeries k)))
    (hflat : ∀ n, Flat (pullback.snd g (adicThickeningι (PowerSeries k) (discIdeal k) n))) :
    Flat g := by
  rw [Flat.iff_flat_stalkMap]
  intro y
  let p : PrimeSpectrum (PowerSeries k) := g y
  rcases eq_bot_or_discIdeal_le k p.asIdeal with hp | hp
  · have hgen : g y = genericPoint (Spec (.of (PowerSeries k))) := by
      rw [genericPoint_eq_bot_of_affine]
      exact PrimeSpectrum.ext hp
    have hfield : IsField ((Spec (.of (PowerSeries k))).presheaf.stalk (g y)) := by
      rw [hgen]
      exact Field.toIsField _
    let := hfield.toField
    show @Module.Flat _ _ _ _ (g.stalkMap y).hom.toAlgebra.toModule
    infer_instance
  · exact AlgebraicGeometry.flat_stalkMap_of_flat_pullbacks_spec_quotient_pow (discIdeal k) g
      hflat y hp

/-- The generic fibre of a proper flat `g : Y ⟶ Spec k⟦t⟧` with Cohen–Macaulay equidimensional
special fibre of dimension `1` is smooth once the image of `t ^ m` lies in the first Fitting ideal
of the base change of `g` to `Spec (k⟦t⟧ ⧸ (t ^ (m + 1)))`. -/
private theorem smooth_genericFibre_of_isPullback_quotient_span_X_pow {Y Z : Scheme.{u}}
    (g : Y ⟶ Spec (.of (PowerSeries k))) [IsProper g] [Flat g]
    (hCM : IsCohenMacaulay (g.fiber (IsLocalRing.closedPoint (PowerSeries k))))
    (hequi : TopologicalSpace.Equidimensional (g.fiber (IsLocalRing.closedPoint (PowerSeries k))))
    (hdim : topologicalKrullDim (g.fiber (IsLocalRing.closedPoint (PowerSeries k))) =
      ((1 : ℕ) : WithBot ℕ∞))
    (m : ℕ) {J : Ideal (PowerSeries k)}
    (hJ : J = Ideal.span {(PowerSeries.X : PowerSeries k) ^ (m + 1)})
    {pr : Z ⟶ Y} {Q : Z ⟶ Spec (.of (PowerSeries k ⧸ J))}
    (hQ : IsPullback pr Q g (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))))
    (hQfit : ∀ U : Z.affineOpens,
      Q.appLE ⊤ U.1 (le_preimage_top Q U.1)
          ((Scheme.ΓSpecIso (.of (PowerSeries k ⧸ J))).inv
            (Ideal.Quotient.mk J (PowerSeries.X ^ m))) ∈
        (fittingIdeal (Scheme.Hom.relativeDifferentials Q) (1 : ℤ)).ideal U) :
    Smooth (g.fiberToSpecResidueField
      (⟨⊥, inferInstance⟩ : PrimeSpectrum (PowerSeries k))) := by
  subst hJ
  refine smooth_genericFibre_of_pow_mem_fittingIdeal k g 1 (m + 1) (by omega)
    hCM hequi hdim hQ fun U => ?_
  convert hQfit U using 1
  simp only [← map_pow]
  rw [Nat.add_sub_cancel, hQ.w, Scheme.Hom.comp_appLE]
  have hnat := congrArg (fun φ => φ.hom (PowerSeries.X ^ m))
    (Scheme.ΓSpecIso_inv_naturality
      (CommRingCat.ofHom (Ideal.Quotient.mk
        (Ideal.span {(PowerSeries.X : PowerSeries k) ^ (m + 1)}))))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at hnat
  rw [hnat, CommRingCat.comp_apply]
  rfl

/-- **A cartesian tower over the formal disc with a smoothing Fitting clause algebraizes to a
smoothing.** Let `Xₙ ⟶ Spec (k⟦t⟧ ⧸ (t) ^ (n + 1))` be a cartesian tower of flat morphisms with
`X₀` proper over `k`, Cohen–Macaulay and equidimensional of dimension `1`, and suppose that at
some level `n` the image of `t ^ n` lies in the first Fitting ideal of `Ω_{Xₙ/Sₙ}` over every
affine open. Then there is a flat projective `Y ⟶ Spec k⟦t⟧` with smooth generic fibre whose
special fibre is `X₀`, as a scheme over `Spec k`.

This is the second half of the proof of [Stacks, Tag 0E7Y]: the algebraization of
[Stacks, Tag 0E7R]
(`Stacks.FormalCurve.exists_isProjectiveMorphism_of_topologicalKrullDim_le_one`), flatness by
[Stacks, Tag 0D4G] (`flat_of_flat_pullback_adicThickeningι`) and the smoothing criterion
[Stacks, Tag 0E7T]
(`Deformation.Examples.SmoothingCriterion.smooth_genericFibre_of_pow_mem_fittingIdeal`). -/
theorem exists_flat_isProjective_smoothing_of_tower {Xn : ℕ → Scheme.{u}}
    (q : ∀ n, Xn n ⟶ adicThickening (PowerSeries k) (discIdeal k) n)
    (i : ∀ n, Xn n ⟶ Xn (n + 1))
    (hcart : ∀ n, IsPullback (i n) (q n) (q (n + 1))
      (adicThickeningSucc (PowerSeries k) (discIdeal k) n))
    (hflat : ∀ n, Flat (q n)) (hq : IsProper (q 0))
    (hCM : IsCohenMacaulay (Xn 0)) (hequi : TopologicalSpace.Equidimensional (Xn 0))
    (hdim : topologicalKrullDim (Xn 0) = 1)
    (hfit : ∃ n, ∀ U : (Xn n).affineOpens,
      (q n).appLE ⊤ U.1 (le_preimage_top (q n) U.1)
          ((Scheme.ΓSpecIso (.of (PowerSeries k ⧸ discIdeal k ^ (n + 1)))).inv
            (Ideal.Quotient.mk (discIdeal k ^ (n + 1)) (PowerSeries.X ^ n))) ∈
        (fittingIdeal (Scheme.Hom.relativeDifferentials (q n)) (1 : ℤ)).ideal U) :
    ∃ (Y : Scheme.{u}) (g : Y ⟶ Spec (.of (PowerSeries k))),
      Flat g ∧ AlgebraicGeometry.IsProjective g ∧
      Smooth (g.fiberToSpecResidueField
        (⟨⊥, inferInstance⟩ : PrimeSpectrum (PowerSeries k))) ∧
      ∃ e : Xn 0 ≅ pullback g
          (Spec.map (CommRingCat.ofHom (PowerSeries.constantCoeff (R := k)))),
        e.hom ≫ pullback.snd g
            (Spec.map (CommRingCat.ofHom (PowerSeries.constantCoeff (R := k)))) =
          q 0 ≫ Spec.map (CommRingCat.ofHom
            (algebraMap k (PowerSeries k ⧸ discIdeal k ^ (0 + 1)))) := by
  obtain ⟨Y, g, hproj, kk, -, hk⟩ :=
    Stacks.FormalCurve.exists_isProjectiveMorphism_of_topologicalKrullDim_le_one
      (PowerSeries k) (discIdeal k) q i hcart hq hdim.le
  have : IsProper g := isProper_of_isProjectiveMorphism g hproj
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian g
  have hflatg : Flat g := by
    refine flat_of_flat_pullback_adicThickeningι k g fun n => ?_
    rw [← (hk n).isoPullback_inv_snd]
    have := hflat n
    infer_instance
  -- the fibres over the closed point, for any identification with the bottom thickening
  have hfib : ∀ {T : Scheme.{u}} (E : T ≅ adicThickening (PowerSeries k) (discIdeal k) 0)
      (h : T ⟶ Spec (.of (PowerSeries k))),
      E.hom ≫ adicThickeningι (PowerSeries k) (discIdeal k) 0 = h →
      IsPullback (kk 0) (q 0 ≫ E.inv) g h := fun E h hE =>
    (hk 0).of_iso (Iso.refl _) (Iso.refl _) E.symm (Iso.refl _)
      (by simp) (by simp) (by simp) (by rw [← hE]; simp)
  have h0 := hfib (specBottomIso k) _ (specBottomIso_hom_comp_ι k)
  obtain ⟨E, hE⟩ := exists_iso_comp_ι_eq_fromSpecResidueField k
  have hc := hfib E _ hE
  let F : Xn 0 ≅ g.fiber (IsLocalRing.closedPoint (PowerSeries k)) := hc.isoPullback
  have hCM' : IsCohenMacaulay (g.fiber (IsLocalRing.closedPoint (PowerSeries k))) :=
    (isCohenMacaulay_iff_of_iso F).mp hCM
  have hequi' : TopologicalSpace.Equidimensional
      (g.fiber (IsLocalRing.closedPoint (PowerSeries k))) :=
    TopologicalSpace.Equidimensional.of_homeomorph (Scheme.homeoOfIso F).symm hequi
  have hdim' : topologicalKrullDim (g.fiber (IsLocalRing.closedPoint (PowerSeries k))) =
      ((1 : ℕ) : WithBot ℕ∞) := by
    rw [← IsHomeomorph.topologicalKrullDim_eq _ (Scheme.homeoOfIso F).isHomeomorph, hdim]
    rfl
  obtain ⟨m, hm⟩ := hfit
  exact ⟨Y, g, hflatg, IsProjectiveMorphism.isProjective hproj,
    smooth_genericFibre_of_isPullback_quotient_span_X_pow k g hCM' hequi' hdim' m
      (Ideal.span_singleton_pow _ _) (hk m) hm,
    h0.isoPullback, by rw [IsPullback.isoPullback_hom_snd, specBottomIso_inv]⟩

/-- **The zero-dimensional case of [Stacks, Tag 0E7Y], for a scheme.** A scheme `X` of finite type
and of dimension at most zero over a field `k`, which is a local complete intersection over `k`,
is the special fibre of a flat, finite and projective family over `Spec k⟦t⟧` whose generic fibre
is smooth.

`X` is affine and finite over `k` by [Stacks, Tag 06LH], its ring of global sections is a local
complete intersection over `k` by [Stacks, Tag 01UD], and the family is the one of
`Deformation.Examples.Smoothing.exists_flat_finite_projective_smoothing_of_finiteDimensional`
([Stacks, Tag 0E7W]). The empty scheme is allowed. -/
theorem exists_flat_finite_projective_smoothing_of_topologicalKrullDim_le_zero
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] [QuasiCompact f]
    (hf : IsLocalCompleteIntersectionOverField f) (hdim : topologicalKrullDim X ≤ 0) :
    ∃ (Y : Scheme.{u}) (g : Y ⟶ Spec (.of (PowerSeries k))),
      Flat g ∧ IsFinite g ∧ AlgebraicGeometry.IsProjective g ∧
      Smooth (g.fiberToSpecResidueField
        (⟨⊥, inferInstance⟩ : PrimeSpectrum (PowerSeries k))) ∧
      ∃ e : X ≅ pullback g
          (Spec.map (CommRingCat.ofHom (PowerSeries.constantCoeff (R := k)))),
        e.hom ≫ pullback.snd g
            (Spec.map (CommRingCat.ofHom (PowerSeries.constantCoeff (R := k)))) = f := by
  have hfin : IsFinite f := by
    rcases isEmpty_or_nonempty X with _ | _
    · infer_instance
    · have : Nonempty (IrreducibleCloseds X) :=
        ⟨⟨closure {Classical.arbitrary X}, isIrreducible_singleton.closure, isClosed_closure⟩⟩
      exact isFinite_of_finiteType_of_dimension_zero k f
        (le_antisymm hdim Order.krullDim_nonneg)
  have : IsAffine X := isAffine_of_isAffineHom f
  let A : Type u := Γ(X, ⊤)
  let : Algebra k A := sectionsAlgebra f ⊤
  have : Module.Finite k A := by
    have h1 : (f.appLE ⊤ ⊤ (by simp)).hom.Finite := by
      rw [show f.appLE ⊤ ⊤ (by simp) = f.appLE ⊤ (f ⁻¹ᵁ ⊤) le_rfl from rfl,
        Scheme.Hom.appLE_eq_app]
      exact f.finite_appTop
    have h2 : (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom.Finite :=
      RingHom.Finite.of_surjective _
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of k)).inv).2
    exact RingHom.Finite.comp h1 h2
  obtain ⟨Y, g, hflat, hfinite, hproj, hsmooth, e, he⟩ :=
    exists_flat_finite_projective_smoothing_of_finiteDimensional k A
      (isLocalCompleteIntersection_sections_of_syntomic f hf (isAffineOpen_top X))
  refine ⟨Y, g, hflat, hfinite, hproj, hsmooth,
    (Scheme.topIso X).symm ≪≫ (isAffineOpen_top X).isoSpec ≪≫ e, ?_⟩
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, he]
  rw [isoSpec_hom_comp_specMap_algebraMap f (isAffineOpen_top X), ← Category.assoc,
    ← Scheme.topIso_hom, Iso.inv_hom_id, Category.id_comp]

/-- **Over an affine base, the disjoint union of two projective morphisms is projective.** This is
`AlgebraicGeometry.isProjective_coprod_desc`, whose hypothesis that the base carries an ample
invertible sheaf holds for an affine base: its structure sheaf is ample
(`Stacks.Ample.isAmple_unitModule_of_isAffine`). -/
theorem _root_.AlgebraicGeometry.isProjective_coprod_desc_of_isAffine {X Y S : Scheme.{u}}
    [IsAffine S] (f : X ⟶ S) (g : Y ⟶ S) (hf : AlgebraicGeometry.IsProjective f)
    (hg : AlgebraicGeometry.IsProjective g) :
    AlgebraicGeometry.IsProjective (coprod.desc f g) :=
  isProjective_coprod_desc f g ((hasAmpleInvertibleSheaf_iff S).mpr
    ⟨Stacks.Ample.unitModule S, inferInstance, Stacks.Ample.isAmple_unitModule_of_isAffine S⟩) hf hg

end Deformation.Examples.Smoothing
