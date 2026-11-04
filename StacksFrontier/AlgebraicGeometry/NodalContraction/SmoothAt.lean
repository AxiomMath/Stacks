module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Smooth.AtPoint
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.FiberDimension
public import StacksFrontier.AlgebraicGeometry.NumericalCriterion.Basic
public import StacksFrontier.AlgebraicGeometry.SmoothAtFiber.Locality
public import StacksFrontier.FieldTheory.Separable.TFAE
public import StacksFrontier.RingTheory.Smooth.RegularLocalRing
public import StacksFrontier.RingTheory.Smooth.StandardSmoothProperties
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Pointwise criteria for smoothness, and smooth neighbourhoods of constant fibre dimension

Criteria for a morphism of schemes to be smooth at a point, and the passage from smoothness at a
point to an open neighbourhood on which the morphism is smooth of the relative dimension of its
fibre at that point. Over a field, a point whose local ring is regular with geometrically reduced
residue field is a smooth point (Tags 00TV and 030W). Over a general base, a flat morphism locally
of finite presentation is smooth at a point at which its fibre is smooth (Tag 01V9).

## Main results

* `AlgebraicGeometry.smoothAt_of_isRegularLocalRing_of_isGeometricallyReduced_residueField`: a
  morphism to the spectrum of a field, locally of finite type, is smooth at a point whose local
  ring is regular with geometrically reduced residue field.
* `AlgebraicGeometry.smoothAt_of_flat_of_smoothAt_fiber`: a flat morphism locally of finite
  presentation is smooth at a point at which its scheme-theoretic fibre is smooth.
* `AlgebraicGeometry.exists_smoothOfRelativeDimension_neighborhood_of_smoothAt`: a morphism
  smooth at a point whose fibre has dimension `n` there is smooth of relative dimension `n` on an
  open neighbourhood of that point.

## References

* [Stacks Project, Tag 0CDF](https://stacks.math.columbia.edu/tag/0CDF)
* [Stacks Project, Tag 00TV](https://stacks.math.columbia.edu/tag/00TV)
* [Stacks Project, Tag 030W](https://stacks.math.columbia.edu/tag/030W)
* [Stacks Project, Tag 01V9](https://stacks.math.columbia.edu/tag/01V9)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- A localisation of a finite type algebra over a field at a prime is formally smooth as soon as
it is a regular local ring with geometrically reduced residue field (Tags 030W and 00TV). -/
@[ega "0 19.6.4" "special case",
  ega "IV 17.15.9" "a ⇒ b",
  sga "1 II 5.10" "partial",
  sga "1 III 1.2" "field base, special case"]
private lemma formallySmooth_of_isRegularLocalRing_of_isGeometricallyReduced
    (k B A : Type u) [Field k] [CommRing B] [CommRing A]
    [Algebra k B] [Algebra k A] [Algebra B A] [IsScalarTower k B A]
    [Algebra.FiniteType k B] (q : Ideal B) [q.IsPrime]
    [IsLocalization.AtPrime A q] [IsRegularLocalRing A]
    [Algebra.IsGeometricallyReduced k (IsLocalRing.ResidueField A)] :
    Algebra.FormallySmooth k A := by
  let e : Localization.AtPrime q ≃ₐ[k] A :=
    (IsLocalization.algEquiv q.primeCompl (Localization.AtPrime q) A).restrictScalars k
  let eκ : q.ResidueField ≃ₐ[k] IsLocalRing.ResidueField A :=
    IsLocalRing.ResidueField.mapAlgEquiv e
  have : Algebra.IsGeometricallyReduced k q.ResidueField :=
    Algebra.IsGeometricallyReduced.of_injective eκ.toAlgHom eκ.injective
  have : Algebra.IsSeparableExtension k q.ResidueField :=
    ((Algebra.isSeparableExtension_tfae k q.ResidueField (ringExpChar k)).out 4 1).mp
      (show Algebra.IsGeometricallyReduced k q.ResidueField from inferInstance)
  have hsm : Algebra.IsSmoothAt k q :=
    (Algebra.isSmoothAt_iff_isRegularLocalRing q A).mpr inferInstance
  exact Algebra.FormallySmooth.of_equiv e

/-- **Regularity with geometrically reduced residue field implies smoothness over a field.** A
morphism to the spectrum of a field `k`, locally of finite type, is smooth at a point `x` whose
local ring is a regular local ring and whose residue field is geometrically reduced over `k`. -/
@[ega "0 19.0.2" "IV", ega "IV 17.15.1" "sufficiency"]
public theorem smoothAt_of_isRegularLocalRing_of_isGeometricallyReduced_residueField
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType f] (x : X) [IsRegularLocalRing (X.presheaf.stalk x)]
    (hgeo : letI : Algebra k ((Spec (CommRingCat.of k)).presheaf.stalk (f x)) :=
        StructureSheaf.stalkAlgebra k (f x)
      letI : Algebra k (X.presheaf.stalk x) := ((f.stalkMap x).hom.comp
        (algebraMap k ((Spec (CommRingCat.of k)).presheaf.stalk (f x)))).toAlgebra
      Algebra.IsGeometricallyReduced k (IsLocalRing.ResidueField (X.presheaf.stalk x))) :
    InfinitesimalLifting.SmoothAt f x := by
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset
    (X := X) (U := ⊤) (x := x) trivial
  let A := Γ(X, U)
  let B := X.presheaf.stalk x
  let hpre : U ≤ f ⁻¹ᵁ (⊤ : (Spec (CommRingCat.of k)).Opens) := by simp
  let halg : k →+* (↑A) :=
    ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ f.appLE ⊤ U hpre).hom
  let : Algebra k (↑A) := halg.toAlgebra
  let : Algebra k ((Spec (CommRingCat.of k)).presheaf.stalk (f.base x)) :=
    StructureSheaf.stalkAlgebra k (f.base x)
  let baseGerm : CommRingCat.of k ⟶ (Spec (CommRingCat.of k)).presheaf.stalk (f.base x) :=
    (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
      (Spec (CommRingCat.of k)).presheaf.germ ⊤ (f.base x) (by simp)
  have hbase : algebraMap k ((Spec (CommRingCat.of k)).presheaf.stalk (f.base x)) =
      baseGerm.hom := by
    ext d; rfl
  let : Algebra k (↑B) := ((f.stalkMap x).hom.comp
    (algebraMap k ((Spec (CommRingCat.of k)).presheaf.stalk (f.base x)))).toAlgebra
  let : Algebra (↑A) (↑B) := X.presheaf.algebra_section_stalk ⟨x, hxU⟩
  let : IsScalarTower k (↑A) (↑B) := IsScalarTower.of_algebraMap_eq' (by
    ext c
    show (f.stalkMap x).hom
        (algebraMap k ((Spec (CommRingCat.of k)).presheaf.stalk (f.base x)) c) =
      X.presheaf.germ U x hxU (halg c)
    calc
      _ = X.presheaf.germ (f ⁻¹ᵁ (⊤ : (Spec (CommRingCat.of k)).Opens)) x (by simp)
          ((f.app ⊤) ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom c)) := by
        rw [hbase]
        show (f.stalkMap x).hom (baseGerm.hom c) = _
        dsimp [baseGerm]
        exact Scheme.Hom.germ_stalkMap_apply f ⊤ x (by simp)
          ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom c)
      _ = X.presheaf.germ U x hxU (halg c) := by
        rw [← X.presheaf.germ_res_apply (homOfLE hpre) x hxU]
        rfl)
  have : Algebra.FiniteType k A := by
    rw [← RingHom.finiteType_algebraMap]
    exact RingHom.FiniteType.comp (f.finiteType_appLE (isAffineOpen_top _) hU hpre)
      (RingHom.FiniteType.of_surjective _
        (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv.surjective)
  let q := (hU.primeIdealOf ⟨x, hxU⟩).asIdeal
  have : q.IsPrime := (hU.primeIdealOf ⟨x, hxU⟩).isPrime
  have : IsLocalization.AtPrime B q := hU.isLocalization_stalk ⟨x, hxU⟩
  have : Algebra.IsGeometricallyReduced k (IsLocalRing.ResidueField B) := hgeo
  have : Algebra.FormallySmooth k B :=
    formallySmooth_of_isRegularLocalRing_of_isGeometricallyReduced k A B q
  let R := (Spec (CommRingCat.of k)).presheaf.stalk (f x)
  let : Algebra R B := (f.stalkMap x).hom.toAlgebra
  have : IsScalarTower k R B := IsScalarTower.of_algebraMap_eq' rfl
  have : (f x).asIdeal.IsPrime := (f x).isPrime
  have : IsLocalization.AtPrime R (f x).asIdeal :=
    StructureSheaf.IsLocalization.to_stalk k (f x)
  have : Algebra.FormallyEtale k R :=
    Algebra.FormallyEtale.of_isLocalization (f x).asIdeal.primeCompl
  apply InfinitesimalLifting.formallySmooth_stalkMap_smoothAt f x
  show Algebra.FormallySmooth R B
  exact Algebra.FormallySmooth.of_restrictScalars k R B

/-- **Flatness together with a smooth fibre implies smoothness at a point.** A morphism locally of
finite presentation which is flat is smooth at a point as soon as its scheme-theoretic fibre
through that point is smooth there. This is the implication from condition (2) to condition (1)
of Tag 01V9. -/
@[sga "1 II 2.1" "sufficiency at a point",
  sga "1 II 2.2" "special case",
  sga "3 VIB 3.10" "(ii) ⇒ (i), special case",
  sga "3 VIB 4.4" "more general",
  sga "3 XV 1.1" "partial"]
public theorem smoothAt_of_flat_of_smoothAt_fiber
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFinitePresentation f]
    (hflat : Flat f) (x : X)
    (hfiber : InfinitesimalLifting.SmoothAt
      (f.fiberToSpecResidueField (f x)) (f.asFiber x)) :
    InfinitesimalLifting.SmoothAt f x := by
  refine ((Stacks.Tag01V9NumericalCriterion.smoothAt_tfae f x).out 1 2).mpr ?_
  exact ⟨(Flat.iff_flat_stalkMap f).mp hflat x, hfiber⟩

/-- A smooth morphism is smooth of relative dimension `n` on a neighbourhood of any point at
which its fibre has dimension `n`. -/
private lemma exists_smoothOfRelativeDimension_neighborhood_of_smooth
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Smooth f] (x : X) (n : ℕ)
    (hdim : topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) = n) :
    ∃ V : X.Opens, x ∈ V ∧ SmoothOfRelativeDimension n (V.ι ≫ f) := by
  obtain ⟨U, hU, V, hV, hxV, hVU, hstd⟩ := Smooth.exists_isStandardSmooth f x
  let : IsAffine V.toScheme := hV
  let : IsAffine U.toScheme := hU
  let A := ToType Γ(Y, U)
  let B := ToType Γ(X, V)
  let : Algebra A B := (f.appLE U V hVU).hom.toAlgebra
  let hs : Algebra.IsStandardSmooth A B := hstd.toAlgebra
  obtain ⟨ι, σ, _, _, ⟨P⟩⟩ := hs.out
  let : P.toPresentation.IsRelativeGlobalCompleteIntersection :=
    P.isRelativeGlobalCompleteIntersection
  let j : Spec Γ(X, V) ⟶ X := hV.fromSpec
  let i : Spec Γ(Y, U) ⟶ Y := hU.fromSpec
  let g : Spec Γ(X, V) ⟶ Spec Γ(Y, U) := Spec.map (f.appLE U V hVU)
  have hcomp : j ≫ f = g ≫ i := (IsAffineOpen.SpecMap_appLE_fromSpec f hU hV hVU).symm
  let q : Spec (CommRingCat.of B) := hV.primeIdealOf ⟨x, hxV⟩
  have hjq : j q = x := hV.fromSpec_primeIdealOf ⟨x, hxV⟩
  have hdimP : P.dimension = n := by
    have hdim' := AlgebraicGeometry.fiberDimensionAt_eq_card_sub_card P.toPresentation q
    have hdimP' : topologicalKrullDimAt (g.fiber (g q)) (g.asFiber q) =
        (P.dimension : WithBot ℕ∞) := by
      simpa [Algebra.Presentation.dimension, g, RingHom.algebraMap_toAlgebra] using hdim'
    rw [fiberDimensionAt_eq_of_open_square j f g i hcomp q, hjq, hdim] at hdimP'
    exact_mod_cast hdimP'.symm
  have hsd : RingHom.IsStandardSmoothOfRelativeDimension n (f.appLE U V hVU).hom :=
    P.isStandardSmoothOfRelativeDimension hdimP
  have : SmoothOfRelativeDimension n (f.resLE U V hVU) := by
    apply (HasRingHomProperty.iff_of_isAffine (P := @SmoothOfRelativeDimension n)).mpr
    apply (RingHom.locally_respectsIso
      (RingHom.isStandardSmoothOfRelativeDimension_respectsIso (n := n))).arrow_mk_iso_iff
        (arrowResLEAppIso f U V hVU) |>.mpr
    exact RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso
      (f.appLE U V hVU).hom hsd
  refine ⟨V, hxV, ?_⟩
  simpa only [Nat.add_zero, Scheme.Hom.resLE_comp_ι] using
    (inferInstance : SmoothOfRelativeDimension (n + 0) (f.resLE U V hVU ≫ U.ι))

/-- **A morphism smooth at a point is smooth of the fibre's relative dimension nearby.** If `f` is
smooth at `x` and its fibre through `x` has dimension `n` there, then `f` is smooth of relative
dimension `n` on an open neighbourhood of `x`. -/
public theorem exists_smoothOfRelativeDimension_neighborhood_of_smoothAt
    {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) (n : ℕ)
    (hf : InfinitesimalLifting.SmoothAt f x)
    (hdim : topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) = n) :
    ∃ V : X.Opens, x ∈ V ∧ SmoothOfRelativeDimension n (V.ι ≫ f) := by
  obtain ⟨U, hxU, hU⟩ := (InfinitesimalLifting.smoothAt_iff_exists_open_smooth_comp f x).mp hf
  let := hU
  have hd : topologicalKrullDimAt ((U.ι ≫ f).fiber ((U.ι ≫ f) ⟨x, hxU⟩))
      ((U.ι ≫ f).asFiber ⟨x, hxU⟩) = n :=
    (fiberDimensionAt_eq_of_open_square U.ι f (U.ι ≫ f) (𝟙 Y) (by simp) ⟨x, hxU⟩).trans hdim
  obtain ⟨V, hxV, hV⟩ := exists_smoothOfRelativeDimension_neighborhood_of_smooth
    (U.ι ≫ f) ⟨x, hxU⟩ n hd
  let := hV
  refine ⟨U.ι ''ᵁ V, ⟨⟨x, hxU⟩, hxV, rfl⟩, ?_⟩
  have he : (U.ι.isoImage V).inv ≫ V.ι ≫ U.ι ≫ f = (U.ι ''ᵁ V).ι ≫ f := by
    rw [← Category.assoc _ U.ι, ← Category.assoc, Scheme.Hom.isoImage_inv_ι]
  rw [← he]
  have : SmoothOfRelativeDimension 0 (U.ι.isoImage V).inv := inferInstance
  simpa using (inferInstance : SmoothOfRelativeDimension (0 + n)
    ((U.ι.isoImage V).inv ≫ V.ι ≫ U.ι ≫ f))

end AlgebraicGeometry

end
