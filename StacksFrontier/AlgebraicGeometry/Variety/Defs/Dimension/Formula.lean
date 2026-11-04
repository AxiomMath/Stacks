module

public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.ResidueField
public import StacksFrontier.RingTheory.Spectrum.Prime.LocalDimension
public import StacksFrontier.Topology.Dimension.Krull

/-!
# The dimension formula for a scheme locally of finite type over a field

Let `X` be a scheme locally of finite type over a field `k`. At every point `x` of `X`, the
dimension of `X` at `x` is the sum of the transcendence degree over `k` of the residue field at
`x` and the Krull dimension of the local ring at `x`.

## Main results

* `AlgebraicGeometry.topologicalKrullDimAt_eq_trdeg_add_krullDim_stalk` is the dimension formula
  at a point of a scheme locally of finite type over a field.

## Implementation notes

The `k`-algebra structure on the residue field is induced canonically by the structure morphism
through global sections. Dimensions take values in `WithBot ℕ∞`; accordingly, the
cardinal-valued transcendence degree is sent to `ℕ∞` by `Cardinal.toENat` before it is added to
the dimension of the stalk.

The formula is reduced to the corresponding statement for a prime of a finitely generated
algebra over `k` on an affine open neighbourhood of `x`. Transporting the residue field along
that reduction needs the canonical identification of `κ(x)` with the residue field of the
corresponding prime, which is assembled from the residue-field maps of the open immersion and
of the affine identification; `appTop_ι_appTop` records the one compatibility of global sections
that identification rests on.

## References

* [Stacks Project, Tag 0A21](https://stacks.math.columbia.edu/tag/0A21)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- The dimension of `X` at a point of an affine open is the local dimension of the spectrum of
the section ring at the corresponding prime. -/
lemma topologicalKrullDimAt_eq_affine_open
    {X : Scheme} (x : X) (U : X.Opens) (hx : x ∈ U) (hU : IsAffineOpen U) :
    topologicalKrullDimAt X x =
      TopologicalSpace.localKrullDim (PrimeSpectrum Γ(X, U)) (hU.primeIdealOf ⟨x, hx⟩) := by
  rw [← TopologicalSpace.topologicalKrullDimAt_eq_localKrullDim]
  calc
    topologicalKrullDimAt X x = topologicalKrullDimAt U ⟨x, hx⟩ :=
      Topology.IsOpenEmbedding.topologicalKrullDimAt_eq
        (IsOpen.isOpenEmbedding_subtypeVal U.2) ⟨x, hx⟩
    _ = _ := topologicalKrullDimAt_eq_of_homeomorph (hU.isoSpec.hom.homeomorph) ⟨x, hx⟩

/-- Restriction to an open subscheme followed by the canonical identification of the sections of
`U` over its own top with the sections of `X` over `U` is restriction of sections along
`U ≤ ⊤`. -/
private lemma ι_appTop_topIso_hom {X : Scheme} (U : X.Opens) :
    U.ι.appTop ≫ U.topIso.hom =
      X.presheaf.map (homOfLE (show U ≤ (⊤ : X.Opens) from le_top)).op := by
  rw [Scheme.Opens.topIso_hom]
  change X.presheaf.map (homOfLE (x := U.ι ''ᵁ ⊤) le_top).op ≫
      X.presheaf.map (eqToHom U.ι_image_top.symm).op = _
  rw [← Functor.map_comp]
  congr 1

/-- Restricting a global section along the inclusion of an open subscheme is the same as taking
the corresponding `appLE` and then the inverse of the canonical identification of the sections
of `U` over its own top with the sections of `X` over `U`. -/
private lemma appTop_ι_appTop {X Y : Scheme} (f : X ⟶ Y) (U : X.Opens) :
    f.appTop ≫ U.ι.appTop = f.appLE ⊤ U (by simp) ≫ U.topIso.inv := by
  rw [Iso.eq_comp_inv, Category.assoc, ι_appTop_topIso_hom]
  rfl

/-- The residue field map of a morphism that is an isomorphism on the stalk at `x` is an
isomorphism. -/
private lemma isIso_residueFieldMap {X Y : Scheme} (f : X ⟶ Y) (x : X) [IsIso (f.stalkMap x)] :
    IsIso (f.residueFieldMap x) :=
  (IsLocalRing.ResidueField.mapEquiv
    (asIso (f.stalkMap x)).commRingCatIsoToRingEquiv).toCommRingCatIso.isIso_hom

/-- **Stacks Project, Tag 0A21.** The dimension at a point of a scheme locally of finite type
over a field is the transcendence degree of its residue field plus the dimension of its local
ring. -/
@[stacks 0A21 "dimension_formula",
  ega "IV 13.3.4" "special case",
  ega "IV 17.15.8",
  ega "IV 5.2.3",
  sga "1 II 5.8" "partial",
  sga "1 II 5.9" "n = trdeg_k κ(x) + p"]
theorem topologicalKrullDimAt_eq_trdeg_add_krullDim_stalk
    (k : Type u) [Field k] (X : Scheme.{u}) (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f]
    (x : X) :
    letI : Algebra k (X.residueField x) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation x).hom.toAlgebra
    topologicalKrullDimAt X x =
      (Cardinal.toENat (Algebra.trdeg k (X.residueField x)) : WithBot ℕ∞) +
        ringKrullDim (X.presheaf.stalk x) := by
  obtain ⟨U, hU, hxU, -⟩ :=
    exists_isAffineOpen_mem_and_subset (show x ∈ (⊤ : X.Opens) from trivial)
  have hft : (f.appLE ⊤ U (by simp)).hom.FiniteType :=
    f.finiteType_appLE (isAffineOpen_top _) hU _
  let : Algebra k Γ(X, U) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ U (by simp)).hom.toAlgebra
  let : Algebra.FiniteType k Γ(X, U) := by
    change (((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ U (by simp)).hom).FiniteType
    exact hft.comp (RingHom.FiniteType.of_surjective _
      (Scheme.ΓSpecIso (.of k)).symm.commRingCatIsoToRingEquiv.surjective)
  let : Algebra k (X.residueField x) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation x).hom.toAlgebra
  have hdim := PrimeSpectrum.localKrullDim_eq_height_add_trdeg_residueField k
    (hU.primeIdealOf ⟨x, hxU⟩)
  rw [topologicalKrullDimAt_eq_affine_open x U hxU hU,
    hU.ringKrullDim_stalk_eq_height x hxU, hdim]
  let : IsOpenImmersion U.ι := inferInstance
  let y : (↥U) := ⟨x, hxU⟩
  let : IsAffine U := hU
  let := U.toScheme.presheaf.algebra_section_stalk (U := (⊤ : U.toScheme.Opens)) ⟨y, trivial⟩
  let : IsLocalization.AtPrime (U.toScheme.presheaf.stalk y)
      ((isAffineOpen_top U.toScheme).primeIdealOf ⟨y, trivial⟩).asIdeal :=
    (isAffineOpen_top U.toScheme).isLocalization_stalk ⟨y, trivial⟩
  let : IsLocalRing (U.toScheme.presheaf.stalk y) :=
    IsLocalization.AtPrime.isLocalRing (R := Γ(U.toScheme, ⊤))
      (S := U.toScheme.presheaf.stalk y)
      (P := ((isAffineOpen_top U.toScheme).primeIdealOf ⟨y, trivial⟩).asIdeal)
  let : IsIso (U.ι.stalkMap y) :=
    (IsOpenImmersion.iff_isIso_stalkMap.mp (inferInstance : IsOpenImmersion U.ι)).2 y
  let : IsIso (hU.isoSpec.hom.stalkMap y) :=
    (isIso_iff_isIso_stalkMap hU.isoSpec.hom).mp (inferInstance : IsIso hU.isoSpec.hom) |>.2 y
  let : IsIso (U.ι.residueFieldMap y) := isIso_residueFieldMap U.ι y
  let : IsIso (hU.isoSpec.hom.residueFieldMap y) := isIso_residueFieldMap hU.isoSpec.hom y
  let e₁ : X.residueField x ≃+* (U.toScheme).residueField y :=
    (asIso (U.ι.residueFieldMap y)).commRingCatIsoToRingEquiv
  let e₂ : (U.toScheme).residueField y ≃+*
      (Spec Γ(X, U)).residueField (hU.primeIdealOf y) :=
    (asIso (hU.isoSpec.hom.residueFieldMap y)).commRingCatIsoToRingEquiv.symm
  let e₃ : (Spec Γ(X, U)).residueField (hU.primeIdealOf y) ≃+*
      (hU.primeIdealOf y).asIdeal.ResidueField :=
    (Scheme.Spec.residueFieldIso Γ(X, U) (hU.primeIdealOf y)).commRingCatIsoToRingEquiv
  let e : X.residueField x ≃+* (hU.primeIdealOf y).asIdeal.ResidueField :=
    e₁.trans (e₂.trans e₃)
  have htr : Algebra.trdeg k (X.residueField x) =
      Algebra.trdeg k (hU.primeIdealOf y).asIdeal.ResidueField := by
    rw [AlgEquiv.trdeg_eq (AlgEquiv.ofRingEquiv (f := e) (by
      intro z
      change e (((((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation x).hom) z)) =
        (algebraMap (Γ(X, U)) (hU.primeIdealOf y).asIdeal.ResidueField)
          ((algebraMap k (Γ(X, U))) z)
      change e₃ (e₂ (e₁ (((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫
        X.Γevaluation x).hom z))) = _
      have he₁ : e₁ (X.Γevaluation x
          (f.appTop.hom ((Scheme.ΓSpecIso (.of k)).inv.hom z))) =
          U.toScheme.Γevaluation y
            (U.ι.appTop (f.appTop.hom ((Scheme.ΓSpecIso (.of k)).inv.hom z))) := by
        change e₁.toRingHom _ = _
        rw [show e₁.toRingHom = (U.ι.residueFieldMap y).hom from rfl]
        have hn := Scheme.Γevaluation_naturality_apply U.ι y
          (f.appTop.hom ((Scheme.ΓSpecIso (.of k)).inv.hom z))
        dsimp [y] at hn
        exact hn
      have he₂ (a : Γ(Spec Γ(X, U), ⊤)) :
          e₂ (U.toScheme.Γevaluation y (hU.isoSpec.hom.appTop a)) =
            (Spec Γ(X, U)).Γevaluation (hU.primeIdealOf y) a := by
        have he₂map : e₂.symm.toRingHom = (hU.isoSpec.hom.residueFieldMap y).hom := rfl
        rw [show U.toScheme.Γevaluation y (hU.isoSpec.hom.appTop a) =
            e₂.symm ((Spec Γ(X, U)).Γevaluation (hU.primeIdealOf y) a) by
          change _ = e₂.symm.toRingHom _
          rw [he₂map]
          have hn := Scheme.Γevaluation_naturality_apply hU.isoSpec.hom y a
          change hU.isoSpec.hom.residueFieldMap y
            ((Spec Γ(X, U)).Γevaluation (hU.primeIdealOf y) a) = _ at hn
          exact hn.symm]
        exact e₂.apply_symm_apply _
      have happ :
          U.ι.appTop (f.appTop.hom ((Scheme.ΓSpecIso (.of k)).inv.hom z)) =
            hU.isoSpec.hom.appTop
              ((Scheme.ΓSpecIso Γ(X, U)).inv.hom ((algebraMap k Γ(X, U)) z)) := by
        rw [hU.isoSpec_hom_appTop]
        have halg : (algebraMap k Γ(X, U)) z =
            (((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ U (by simp)).hom z) := rfl
        simp only [CommRingCat.comp_apply]
        rw [(Scheme.ΓSpecIso Γ(X, U)).inv_hom_id_apply, halg]
        exact congrArg (fun q : Γ(Spec (.of k), ⊤) ⟶ Γ(U.toScheme, ⊤) =>
          q.hom ((Scheme.ΓSpecIso (.of k)).inv.hom z)) (appTop_ι_appTop f U)
      rw [← e₃.apply_symm_apply ((algebraMap (Γ(X, U))
        (hU.primeIdealOf y).asIdeal.ResidueField) ((algebraMap k (Γ(X, U))) z))]
      apply_fun e₃.symm
      simp only [e₃, RingEquiv.symm_apply_apply]
      have hs := Scheme.Spec.algebraMap_residueFieldIso_inv (Γ(X, U))
        (hU.primeIdealOf y : Spec Γ(X, U))
      have hs' := congrArg (fun q : Γ(X, U) ⟶
          .of ((Spec Γ(X, U)).residueField (hU.primeIdealOf y : Spec Γ(X, U))) =>
        q.hom ((algebraMap k (Γ(X, U))) z)) hs
      change _ = (Scheme.Spec.residueFieldIso Γ(X, U) (hU.primeIdealOf y)).inv.hom
          ((algebraMap (Γ(X, U)) (hU.primeIdealOf y).asIdeal.ResidueField)
            ((algebraMap k (Γ(X, U))) z))
      have hs'' :
          (Scheme.Spec.residueFieldIso Γ(X, U) (hU.primeIdealOf y)).inv.hom
              ((algebraMap (Γ(X, U)) (hU.primeIdealOf y).asIdeal.ResidueField)
                ((algebraMap k (Γ(X, U))) z)) =
            (CommRingCat.Hom.hom
              ((Scheme.ΓSpecIso Γ(X, U)).inv ≫
                (Spec Γ(X, U)).presheaf.germ ⊤ (hU.primeIdealOf y) trivial ≫
                (Spec Γ(X, U)).residue (hU.primeIdealOf y)))
              ((algebraMap k (Γ(X, U))) z) := by
        simpa using hs'
      rw [hs'']
      rw [show e₁ (((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫
          X.Γevaluation x).hom z) =
          U.toScheme.Γevaluation y
            (U.ι.appTop (f.appTop.hom ((Scheme.ΓSpecIso (.of k)).inv.hom z))) by
        simpa using he₁, happ, he₂]
      rfl))]
  rw [← htr]
  push_cast
  rw [add_comm]

end AlgebraicGeometry

end
