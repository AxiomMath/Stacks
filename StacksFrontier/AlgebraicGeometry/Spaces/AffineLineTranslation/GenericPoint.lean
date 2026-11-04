module

public import Mathlib.AlgebraicGeometry.Morphisms.Preimmersion
public import Mathlib.FieldTheory.Laurent
public import Mathlib.FieldTheory.RatFunc.AsPolynomial
public import StacksFrontier.AlgebraicGeometry.Limits.CoproductUniversal
public import StacksFrontier.CategoryTheory.Limits.CoproductPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineLineTranslation

/-!
# The generic point of the affine line and the integer translations

The generic point of the affine line over a field `k` is `Spec k(x)`, mapped to `𝔸¹_k` by
the morphism sending the standard coordinate to the indeterminate. It is a monomorphism,
and translating the indeterminate by an integer intertwines it with the corresponding
integer translation of `𝔸¹_k`.

Consequently the fibre of the graph relation of the translation action over the generic
point, taken on either side, is a disjoint union of one copy of `Spec k(x)` for every
integer.

## Main definitions

* `AlgebraicGeometry.AffineLineTranslation.genericPointOver` is `Spec k(x)` over `Spec k`,
  and `AlgebraicGeometry.AffineLineTranslation.genericPointMap` is its map to `𝔸¹_k`.
* `AlgebraicGeometry.AffineLineTranslation.ratFuncTranslationEquiv` is translation of the
  indeterminate of `k(x)`, and
  `AlgebraicGeometry.AffineLineTranslation.genericPointTranslationIso` is the automorphism
  of `Spec k(x)` it induces.
* `AlgebraicGeometry.AffineLineTranslation.genericPointCopies` is the disjoint union of one
  copy of `Spec k(x)` for every integer, identified by
  `AlgebraicGeometry.AffineLineTranslation.genericPointSourceFiberIso` and
  `AlgebraicGeometry.AffineLineTranslation.genericPointRelationFiberIso` with the two
  fibres of the graph relation over the generic point.

## Main results

* `AlgebraicGeometry.AffineLineTranslation.genericPointMap_translation`: the translation
  automorphism of `Spec k(x)` lies over the corresponding translation of `𝔸¹_k`.
* `AlgebraicGeometry.AffineLineTranslation.genericPointMap_mono`: the generic point map is
  a monomorphism, being the spectrum of a localization.

## Implementation notes

The generic point map is identified with `Spec` of the localization map
`k[X] ⟶ k(x)` through `AlgebraicGeometry.AffineSpace.SpecIso` and
`MvPolynomial.uniqueAlgEquiv`, which makes it a preimmersion, hence a monomorphism.

## References

* [Stacks Project, Tag 02Z7](https://stacks.math.columbia.edu/tag/02Z7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry

/-- Reading `AlgebraicGeometry.Scheme.ΓSpecIso_inv_naturality` on elements: the global
sections of `Spec f` carry the inverse of the canonical isomorphism at `x` to its value
at `f x`. -/
theorem Scheme.specMap_appTop_ΓSpecIso_inv {R S : CommRingCat.{u}} (f : R ⟶ S) (x : R) :
    (Spec.map f).appTop ((Scheme.ΓSpecIso R).inv x) = (Scheme.ΓSpecIso S).inv (f.hom x) := by
  have h := congrArg (fun q : CommRingCat.Hom _ _ => q.hom x)
    (Scheme.ΓSpecIso_inv_naturality f).symm
  exact h

namespace AffineLineTranslation

open AffineLineInvolution

variable (k : Type u) [Field k]

/-- The generic point of the affine line over `k`, the spectrum of the field of rational
functions, viewed over `Spec k`. -/
abbrev genericPointOver : Over (Spec (.of k)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k (RatFunc k))))

/-- The generic point of the affine line over `k`, as a morphism to `𝔸¹_k`: it sends the
standard coordinate to the indeterminate. -/
def genericPointMap : genericPointOver k ⟶ affineLine k :=
  Over.homMk
    (AffineSpace.homOfVector (genericPointOver k).hom
      (fun _ : PUnit.{u + 1} => (Scheme.ΓSpecIso (.of (RatFunc k))).inv RatFunc.X))

/-- Translation of the indeterminate of `k(x)` by an element of `k`, as an algebra
automorphism. -/
def ratFuncTranslationEquiv (r : k) : RatFunc k ≃ₐ[k] RatFunc k :=
  AlgEquiv.ofBijective (RatFunc.laurent r) ⟨RatFunc.laurent_injective r, fun y =>
    ⟨RatFunc.laurent (-r) y, by
      rw [RatFunc.laurent_laurent, add_neg_cancel, RatFunc.laurent_at_zero]⟩⟩

/-- The automorphism of the generic point of the affine line induced by translating the
indeterminate by an integer. -/
def genericPointTranslationIso (n : ℤ) : genericPointOver k ≅ genericPointOver k := by
  refine Over.isoMk (Scheme.Spec.mapIso
    (ratFuncTranslationEquiv k (n : k)).toRingEquiv.toCommRingCatIso.op) ?_
  change Spec.map (CommRingCat.ofHom (RatFunc.laurent (n : k)).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (RatFunc.C : k →+* RatFunc k)) = _
  rw [← Spec.map_comp (CommRingCat.ofHom (RatFunc.C : k →+* RatFunc k))
    (CommRingCat.ofHom (RatFunc.laurent (n : k)).toRingHom)]
  change Spec.map (CommRingCat.ofHom (RatFunc.C : k →+* RatFunc k) ≫
      CommRingCat.ofHom (RatFunc.laurent (n : k)).toRingHom) =
    Spec.map (CommRingCat.ofHom (RatFunc.C : k →+* RatFunc k))
  apply congrArg Spec.map
  ext x
  exact RatFunc.laurent (n : k) |>.commutes x

/-- The underlying morphism of the translation automorphism of the generic point is the
spectrum of the Laurent translation. -/
theorem genericPointTranslationIso_left (n : ℤ) :
    (genericPointTranslationIso k n).hom.left =
      Spec.map (CommRingCat.ofHom (RatFunc.laurent (n : k)).toRingHom) := by
  simp only [genericPointTranslationIso, Over.isoMk_hom_left, Functor.mapIso_hom]
  show Spec.map (CommRingCat.ofHom
      (ratFuncTranslationEquiv k (n : k)).toRingEquiv.toRingHom) = _
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  ext x
  rfl

/-- The Laurent translation by `n` carries the indeterminate to `x + n`. -/
theorem spec_laurent_appTop (n : ℤ) :
    (Spec.map (CommRingCat.ofHom (RatFunc.laurent (n : k)).toRingHom)).appTop
      ((Scheme.ΓSpecIso (.of (RatFunc k))).inv RatFunc.X) =
    (Scheme.ΓSpecIso (.of (RatFunc k))).inv (RatFunc.X + RatFunc.C (n : k)) := by
  simpa [RatFunc.laurent_X] using Scheme.specMap_appTop_ΓSpecIso_inv
    (CommRingCat.ofHom (RatFunc.laurent (n : k)).toRingHom) RatFunc.X

/-- The translation automorphism of the generic point lies over the corresponding
translation of the affine line. -/
theorem genericPointMap_translation (n : ℤ) :
    (genericPointTranslationIso k n).hom ≫ genericPointMap k =
      genericPointMap k ≫ (translationAction k (Multiplicative.ofAdd n)).hom := by
  ext
  apply AffineSpace.hom_ext
  · simp only [Over.comp_left]
    calc
      (Over.Hom.left (genericPointTranslationIso k n).hom ≫
          Over.Hom.left (genericPointMap k)) ≫ (affineLine k).hom =
        Over.Hom.left (genericPointTranslationIso k n).hom ≫ (genericPointOver k).hom := by
          rw [Category.assoc, (genericPointMap k).w]
      _ = (genericPointOver k).hom := (genericPointTranslationIso k n).hom.w
      _ = (Over.Hom.left (genericPointMap k) ≫
          Over.Hom.left ((translationAction k (Multiplicative.ofAdd n)).hom)) ≫
            (affineLine k).hom := by
          rw [Category.assoc, ((translationAction k (Multiplicative.ofAdd n)).hom).w,
            (genericPointMap k).w]
  · intro i
    obtain rfl : i = PUnit.unit := Subsingleton.elim _ _
    simp only [Over.comp_left]
    rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
      CommRingCat.comp_apply, genericPointTranslationIso_left]
    simp only [genericPointMap, Over.homMk_left, AffineSpace.homOfVector_appTop_coord]
    show (Spec.map (CommRingCat.ofHom (RatFunc.laurent (n : k)).toRingHom)).appTop
        ((Scheme.ΓSpecIso (.of (RatFunc k))).inv RatFunc.X) =
      (AffineSpace.homOfVector (genericPointOver k).hom
        (fun _ : PUnit.{u + 1} => (Scheme.ΓSpecIso (.of (RatFunc k))).inv RatFunc.X)).appTop
        (((translationAction k (Multiplicative.ofAdd n)).hom.left).appTop
          (AffineSpace.coord (Spec (.of k)) PUnit.unit))
    rw [spec_laurent_appTop, translationAction_apply]
    simp only [map_add, AffineSpace.homOfVector_appTop_coord, map_intCast]

/-- The generic point map is a monomorphism: it is the spectrum of the localization of
`k[X]` at its nonzero divisors, hence a preimmersion. -/
theorem genericPointMap_mono : Mono (genericPointMap k).left := by
  let α : MvPolynomial PUnit.{u + 1} k ≃ₐ[k] Polynomial k := MvPolynomial.uniqueAlgEquiv k PUnit
  let e := (AffineSpace.SpecIso PUnit.{u + 1} (.of k)).trans
    (Scheme.Spec.mapIso (α.toRingEquiv.toCommRingCatIso.op)).symm
  let φ : CommRingCat.of (Polynomial k) ⟶ CommRingCat.of (RatFunc k) :=
    CommRingCat.ofHom (algebraMap (Polynomial k) (RatFunc k))
  let q : Spec (.of (RatFunc k)) ⟶ (affineLine k).left := Spec.map φ ≫ e.inv
  have hpre : IsPreimmersion (Spec.map φ) :=
    IsPreimmersion.of_isLocalization (nonZeroDivisors (Polynomial k))
  have hbase : CommRingCat.ofHom (algebraMap k (RatFunc k)) =
      CommRingCat.ofHom (MvPolynomial.C : k →+* MvPolynomial PUnit.{u + 1} k) ≫
        CommRingCat.ofHom α.toRingEquiv.toRingHom ≫ φ := by
    apply CommRingCat.hom_ext
    ext c
    show algebraMap k (RatFunc k) c =
      (algebraMap (Polynomial k) (RatFunc k)) (α (MvPolynomial.C c))
    rw [show MvPolynomial.C c = algebraMap k (MvPolynomial PUnit.{u + 1} k) c from rfl,
      α.commutes]
    rfl
  have hq : (genericPointMap k).left = q := by
    apply AffineSpace.hom_ext
    · show (genericPointMap k).left ≫ (affineLine k).hom = q ≫ (affineLine k).hom
      simp only [q, e, Iso.trans_inv, Iso.symm_inv, Scheme.Spec.mapIso_hom]
      show (genericPointMap k).left ≫ (affineLine k).hom =
        Spec.map φ ≫ Spec.map (CommRingCat.ofHom α.toRingEquiv.toRingHom) ≫
          (AffineSpace.SpecIso PUnit.{u + 1} (.of k)).inv ≫ (affineLine k).hom
      calc
        _ = (genericPointOver k).hom := (genericPointMap k).w
        _ = Spec.map (CommRingCat.ofHom (algebraMap k (RatFunc k))) := rfl
        _ = Spec.map (CommRingCat.ofHom MvPolynomial.C ≫
            CommRingCat.ofHom α.toRingEquiv.toRingHom ≫ φ) := congrArg Spec.map hbase
        _ = Spec.map φ ≫ Spec.map (CommRingCat.ofHom α.toRingEquiv.toRingHom) ≫
            Spec.map (CommRingCat.ofHom MvPolynomial.C) := by
              rw [← Spec.map_comp, ← Spec.map_comp, Category.assoc]
        _ = q ≫ (affineLine k).hom := by
              have hline := AffineSpace.SpecIso_inv_over (n := PUnit.{u + 1}) (.of k)
              show Spec.map φ ≫ Spec.map (CommRingCat.ofHom α.toRingEquiv.toRingHom) ≫
                  Spec.map (CommRingCat.ofHom MvPolynomial.C) =
                Spec.map φ ≫ (Spec.map (CommRingCat.ofHom α.toRingEquiv.toRingHom) ≫
                  ((AffineSpace.SpecIso PUnit.{u + 1} (.of k)).inv ≫ (affineLine k).hom))
              rw [← hline]
              rfl
    · intro i
      obtain rfl : i = PUnit.unit := Subsingleton.elim _ _
      simp only [genericPointMap, Over.homMk_left, AffineSpace.homOfVector_appTop_coord]
      show (Scheme.ΓSpecIso (.of (RatFunc k))).inv RatFunc.X =
        (Spec.map φ ≫ Spec.map (CommRingCat.ofHom α.toRingEquiv.toRingHom) ≫
          (AffineSpace.SpecIso PUnit.{u + 1} (.of k)).inv).appTop
          (AffineSpace.coord (Spec (.of k)) PUnit.unit)
      have hecoord : (e.inv).appTop (AffineSpace.coord (Spec (.of k)) PUnit.unit) =
          (Scheme.ΓSpecIso (.of (Polynomial k))).inv Polynomial.X := by
        show ((Scheme.Spec.mapIso α.toRingEquiv.toCommRingCatIso.op).hom ≫
          (AffineSpace.SpecIso PUnit.{u + 1} (.of k)).inv).appTop
          (AffineSpace.coord (Spec (.of k)) PUnit.unit) = _
        rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, AffineSpace.SpecIso_inv_appTop_coord]
        show (Spec.map (CommRingCat.ofHom α.toRingEquiv.toRingHom)).appTop
            ((Scheme.ΓSpecIso (.of (MvPolynomial PUnit.{u + 1} k))).inv
              (MvPolynomial.X PUnit.unit)) = _
        rw [Scheme.specMap_appTop_ΓSpecIso_inv]
        congr 1
        simp [α]
      show (Scheme.ΓSpecIso (.of (RatFunc k))).inv RatFunc.X =
        (Spec.map φ).appTop ((e.inv).appTop (AffineSpace.coord (Spec (.of k)) PUnit.unit))
      rw [hecoord, Scheme.specMap_appTop_ΓSpecIso_inv]
      congr 1
  rw [hq]
  infer_instance

/-- The disjoint union of one copy of the generic point of the affine line over `k` for
every integer. -/
abbrev genericPointCopies : Over (Spec (.of k)) :=
  ∐ fun _ : Multiplicative ℤ => genericPointOver k

/-- The fibre product of the generic point map against its translate by `n` is the generic
point itself: the translation automorphism is a section of both projections. -/
def genericPointTranslationFiberIso (n : ℤ) :
    genericPointOver k ≅ pullback (genericPointMap k)
      (genericPointMap k ≫ (translationAction k (Multiplicative.ofAdd n)).hom) := by
  have : Mono (genericPointMap k).left := genericPointMap_mono k
  have : Mono (genericPointMap k) := Over.mono_of_mono_left _
  have hpb : IsPullback (𝟙 (genericPointOver k)) (genericPointTranslationIso k n).hom
      (genericPointMap k ≫ (translationAction k (Multiplicative.ofAdd n)).hom)
      (genericPointMap k) :=
    IsPullback.of_horiz_isIso_mono
      (show CommSq _ _ _ _ from ⟨(genericPointMap_translation k n).symm⟩)
  exact hpb.isoPullback ≪≫ pullbackSymmetry _ _

/-- The fibre of the source map of the graph relation of the translation action over the
generic point is one copy of the generic point for each integer. -/
def genericPointSourceFiberIso :
    genericPointCopies k ≅ pullback
      (Space.actionRelationSource (affineLine k) (Multiplicative ℤ)) (genericPointMap k) := by
  let X : Multiplicative ℤ → Over (Spec (.of k)) := fun _ ↦ affineLine k
  let f : ∀ n : Multiplicative ℤ, X n ⟶ affineLine k := fun _ ↦ 𝟙 (affineLine k)
  let c : Cofan X :=
    Cofan.mk (Space.actionRelationScheme (affineLine k) (Multiplicative ℤ)) (Sigma.ι X)
  have huι (n : Multiplicative ℤ) :
      c.inj n ≫ Space.actionRelationSource (affineLine k) (Multiplicative ℤ) = f n := by
    change Sigma.ι X n ≫ Space.actionRelationSource (affineLine k) (Multiplicative ℤ) = 𝟙 _
    rw [Space.actionRelationSource, Sigma.ι_desc]
  exact Sigma.mapIso (fun _ : Multiplicative ℤ => pullbackRightIdIso (genericPointMap k)) ≪≫
    coproductPullbackIso X f c (isUniversalColimit_sigmaCofanOver X)
      (Space.actionRelationSource (affineLine k) (Multiplicative ℤ)) huι (genericPointMap k) ≪≫
        (pullbackSymmetry _ _).symm

/-- The identification of the fibre of the source map carries the summand indexed by `n` to
the generic point of the summand indexed by `n`. -/
theorem genericPointSourceFiberIso_fst (n : Multiplicative ℤ) :
    Sigma.ι (fun _ : Multiplicative ℤ => genericPointOver k) n ≫
      (genericPointSourceFiberIso k).hom ≫
        pullback.fst (Space.actionRelationSource (affineLine k) (Multiplicative ℤ))
          (genericPointMap k) =
      genericPointMap k ≫ Sigma.ι (fun _ : Multiplicative ℤ => affineLine k) n := by
  simp [genericPointSourceFiberIso, coproductPullbackIso_ι_snd,
    pullbackSymmetry_inv_comp_fst, pullbackRightIdIso, Category.assoc]

/-- The self-fibre of the generic point along the graph relation of the translation action
is one copy of the generic point for each integer. -/
def genericPointRelationFiberIso :
    pullback (pullback.fst
        (Space.actionRelationSource (affineLine k) (Multiplicative ℤ)) (genericPointMap k) ≫
        Space.actionRelationTarget (affineLine k) (Multiplicative ℤ) (translationAction k))
      (genericPointMap k) ≅ genericPointCopies k := by
  let R₁ := pullback (Space.actionRelationSource (affineLine k) (Multiplicative ℤ))
    (genericPointMap k)
  let φ : R₁ ⟶ affineLine k := pullback.fst _ _ ≫
    Space.actionRelationTarget (affineLine k) (Multiplicative ℤ) (translationAction k)
  let c : Cofan (fun _ : Multiplicative ℤ => genericPointOver k) := Cofan.mk R₁
    fun n => Sigma.ι (fun _ : Multiplicative ℤ => genericPointOver k) n ≫
      (genericPointSourceFiberIso k).hom
  have ec : Cofan.mk (genericPointCopies k)
      (Sigma.ι fun _ : Multiplicative ℤ => genericPointOver k) ≅ c :=
    Cofan.ext (genericPointSourceFiberIso k) fun n => by simp [c]
  have hu : IsUniversalColimit c :=
    (isUniversalColimit_sigmaCofanOver fun _ : Multiplicative ℤ => genericPointOver k).of_iso ec
  let f : ∀ _ : Multiplicative ℤ, genericPointOver k ⟶ affineLine k :=
    fun n => genericPointMap k ≫ (translationAction k n).hom
  have huι (n : Multiplicative ℤ) : c.inj n ≫ φ = f n := by
    change (Sigma.ι (fun _ : Multiplicative ℤ => genericPointOver k) n ≫
      (genericPointSourceFiberIso k).hom ≫
      pullback.fst (Space.actionRelationSource (affineLine k) (Multiplicative ℤ))
        (genericPointMap k)) ≫
        Space.actionRelationTarget (affineLine k) (Multiplicative ℤ) (translationAction k) = _
    rw [genericPointSourceFiberIso_fst]
    change genericPointMap k ≫ Sigma.ι (fun _ : Multiplicative ℤ => affineLine k) n ≫
      Space.actionRelationTarget (affineLine k) (Multiplicative ℤ) (translationAction k) = _
    simp [f, Space.actionRelationTarget]
  exact (Sigma.mapIso (fun n : Multiplicative ℤ => genericPointTranslationFiberIso k n.toAdd) ≪≫
    coproductPullbackIso (fun _ : Multiplicative ℤ => genericPointOver k) f c hu φ huι
      (genericPointMap k) ≪≫ pullbackSymmetry _ _).symm

end AffineLineTranslation

end AlgebraicGeometry

end
