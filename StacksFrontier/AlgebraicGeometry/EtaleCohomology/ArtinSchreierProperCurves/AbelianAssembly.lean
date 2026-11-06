module
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSequence.AdditiveSheaf
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSequence.ConstantKernel
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSequence.Sequence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.GenericPointDirectImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleAbelianDerivedFunctors
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Existence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.TrivialityAndGlobalSections

public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierProperCurves.DirectImageSequence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BoundedBelowDerivedDirectImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionModules.CurveConstantCoefficients
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionModules.CurveConstantCoefficientsUnconditional
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.WeakSerreAbelian

/-!
# `Rᵠf_*(𝐙/p𝐙)` from the higher direct images of `𝐆_a`

Let `f : X ⟶ S` be a morphism of schemes over `𝐅_p` with `𝐆_{a,S} = f_*𝐆_{a,X}`. The long exact
sequence of `Rf_*` applied to the Artin–Schreier sequence identifies `Rᵠf_*(𝐙/p𝐙)`:

* in degree `0` with the kernel of `F - 1` on `𝐆_{a,S}`, which is the constant sheaf `𝐙/p𝐙`;
* in degree `1` with the kernel of `F - 1` on `R¹f_*𝐆_a`, provided `F - 1` is surjective on
  `𝐆_{a,S}`, which it is;
* in degrees `q ≥ 2` with zero, provided `Rᵠf_*𝐆_a = 0` for `q ≥ 2` and `F - 1` is surjective on
  `R¹f_*𝐆_a`.

This is the argument of case (b) of the proof of [Stacks, Tag 0GKV]; the inputs about `R¹f_*𝐆_a`
and `Rᵠf_*𝐆_a` are hypotheses of `Stacks.ArtinSchreier.isConstructibleEtaleAbelianSheaf_homology_
etaleAbelianDerivedDirectImage_constantZMod` and are discharged for proper smooth families of
curves elsewhere.

## Main results

* `Stacks.EtaleCohomology.isConstructibleEtaleAbelianSheaf_of_iso` and
  `Stacks.EtaleCohomology.isConstructibleEtaleAbelianSheaf_of_isZero`: constructibility on
  Mathlib's small étale site is invariant under isomorphism and holds for zero.
* `Stacks.ArtinSchreier.epi_homology_zero_map_artinSchreierMap`: `F - 1` is surjective on
  `H⁰(Rf_*𝐆_a) = f_*𝐆_a`.
* `Stacks.ArtinSchreier.
  isConstructibleEtaleAbelianSheaf_homology_etaleAbelianDerivedDirectImage_constantZMod`: the
  three degrees together.

## References

* [Stacks Project, Tag 0GKV](https://stacks.math.columbia.edu/tag/0GKV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open Stacks.EtaleCohomology

universe u

attribute [local instance] HasDerivedCategory.standard

namespace Stacks.EtaleCohomology

/-- `isRightAdjoint_sheafPushforwardContinuous_addCommGrpCat_containing` at coefficients
`AddCommGrpCat.{u + 1}`: there the universe `max (u + 1) ?r` of the general instance is not
solved by unification. -/
instance (priority := high) isRightAdjoint_sheafPushforwardContinuous_addCommGrpCat_abelianAssembly
    (X : Scheme.{u}) (S T : (BigEtaleSite.containing X).Scheme) (f : T ⟶ S) :
    (Functor.sheafPushforwardContinuous
      (AlgebraicGeometry.smallEtaleBaseChange (BigEtaleSite.containing X) f)
      AddCommGrpCat.{u + 1}
      (AlgebraicGeometry.SmallEtale.topology (BigEtaleSite.containing X) S.obj S.property)
      (AlgebraicGeometry.SmallEtale.topology (BigEtaleSite.containing X) T.obj
        T.property)).IsRightAdjoint :=
  isRightAdjoint_sheafPushforwardContinuous_addCommGrpCat_containing.{u, 0} X S T f

/-- **Constructibility on Mathlib's small étale site is invariant under isomorphism.** -/
theorem isConstructibleEtaleAbelianSheaf_of_iso {X : Scheme.{u}}
    {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} (e : F ≅ G)
    (hF : _root_.Stacks.EtaleCohomology.IsConstructibleSmallEtaleAbelianSheaf.{u, 0} F) :
    _root_.Stacks.EtaleCohomology.IsConstructibleSmallEtaleAbelianSheaf.{u, 0} G :=
  isConstructibleAbelianSheaf_congr _ _
    ((SmallEtale.sheafEquiv (BigEtaleSite.containing X) X (BigEtaleSite.contains_containing X)
      AddCommGrpCat.{u + 1}).inverse.mapIso e) hF

/-- **A zero abelian sheaf on Mathlib's small étale site is constructible.** -/
theorem isConstructibleEtaleAbelianSheaf_of_isZero {X : Scheme.{u}}
    {F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} (hF : IsZero F) :
    _root_.Stacks.EtaleCohomology.IsConstructibleSmallEtaleAbelianSheaf.{u, 0} F :=
  isConstructibleAbelianSheaf_congr _ _
    (((SmallEtale.sheafEquiv (BigEtaleSite.containing X) X (BigEtaleSite.contains_containing X)
      AddCommGrpCat.{u + 1}).inverse.map_isZero hF).isoZero.symm)
    (isConstructibleAbelianSheaf_zero _ _)

end Stacks.EtaleCohomology

namespace Stacks.ArtinSchreier

variable {X S : Scheme.{u}} (f : X ⟶ S) {p : ℕ} (hp : p.Prime) (hS : (p : Γ(S, ⊤)) = 0)
  (hX : (p : Γ(X, ⊤)) = 0)

/-- The functor `K ↦ Hⁿ(Rf_*(K[0]))` on abelian sheaves of `X_étale`. -/
abbrev homologyDerivedDirectImageSingle (n : ℤ) :
    Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⥤
      Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) 0 ⋙
    etaleAbelianDerivedDirectImage.{u, 0} f ⋙
      DerivedCategory.homologyFunctor (Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}) n

include hS in
/-- **`F - 1` is surjective on `H⁰(Rf_*𝐆_a)`** when `𝐆_{a,S} ⟶ f_*𝐆_{a,X}` is an isomorphism:
there `H⁰(Rf_*𝐆_a) = f_*𝐆_{a,X} = 𝐆_{a,S}`, on which `F - 1` is surjective. -/
theorem epi_homology_zero_map_artinSchreierMap
    [IsIso (additiveDirectImageComparisonGeneral.{u, 0} f)] :
    Epi ((homologyDerivedDirectImageSingle f 0).map (artinSchreierMap.{u, 0} X hp hX)) := by
  let e := etaleAbelianDerivedDirectImageSingleHomologyIso.{u, 0} f 0 ≪≫
    (etaleAbelianDirectImage.{u, 0} f).rightDerivedZeroIsoSelf
  have hnat := e.hom.naturality (artinSchreierMap.{u, 0} X hp hX)
  have hcmp := artinSchreierMap_comp_additiveDirectImageComparison_unconditional f hp hS hX
  have : Epi ((etaleAbelianDirectImage.{u, 0} f).map (artinSchreierMap.{u, 0} X hp hX)) := by
    have h : (etaleAbelianDirectImage.{u, 0} f).map (artinSchreierMap.{u, 0} X hp hX) =
        inv (additiveDirectImageComparisonGeneral.{u, 0} f) ≫ artinSchreierMap.{u, 0} S hp hS ≫
          additiveDirectImageComparisonGeneral.{u, 0} f := by
      rw [hcmp, IsIso.inv_hom_id_assoc]
    rw [h]
    have := epi_artinSchreierMap.{u, 0} S hp hS
    infer_instance
  have h : (homologyDerivedDirectImageSingle f 0).map (artinSchreierMap.{u, 0} X hp hX) =
      e.hom.app _ ≫ (etaleAbelianDirectImage.{u, 0} f).map (artinSchreierMap.{u, 0} X hp hX) ≫
        e.inv.app _ := by
    rw [← Category.assoc, ← hnat, Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
    rfl
  rw [h]
  infer_instance

/-- `Hⁿ(Rf_*(K[0])) ≅ Rⁿf_* K` for `n : ℕ`, read at the functor
`Stacks.ArtinSchreier.homologyDerivedDirectImageSingle`. -/
abbrev homologyDerivedDirectImageSingleIso (n : ℕ) :
    homologyDerivedDirectImageSingle f n ≅ (etaleAbelianDirectImage.{u, 0} f).rightDerived n :=
  etaleAbelianDerivedDirectImageSingleHomologyIso.{u, 0} f n

/-- Transport of an epimorphism along `homologyDerivedDirectImageSingleIso`. -/
theorem epi_homologyDerivedDirectImageSingle_map_iff {A B : Sheaf X.smallEtaleTopology
    AddCommGrpCat.{u + 1}} (g : A ⟶ B) (n : ℕ) :
    Epi ((homologyDerivedDirectImageSingle f n).map g) ↔
      Epi (((etaleAbelianDirectImage.{u, 0} f).rightDerived n).map g) := by
  rw [← MorphismProperty.epimorphisms.iff, ← MorphismProperty.epimorphisms.iff]
  exact (MorphismProperty.epimorphisms _).arrow_mk_iso_iff
    (Arrow.isoOfNatIso (homologyDerivedDirectImageSingleIso f n) (Arrow.mk g))

/-- The kernel of `Hⁿ(Rf_*(g[0]))` is the kernel of `Rⁿf_*(g)`. -/
def kernelHomologyDerivedDirectImageSingleIso {A B : Sheaf X.smallEtaleTopology
    AddCommGrpCat.{u + 1}} (g : A ⟶ B) (n : ℕ) :
    kernel ((homologyDerivedDirectImageSingle f n).map g) ≅
      kernel (((etaleAbelianDirectImage.{u, 0} f).rightDerived n).map g) :=
  kernel.mapIso _ _ ((homologyDerivedDirectImageSingleIso f n).app A)
    ((homologyDerivedDirectImageSingleIso f n).app B)
    ((homologyDerivedDirectImageSingleIso f n).hom.naturality g)

include hS in
/-- **`Rᵠf_*(𝐙/p𝐙)` is constructible**, from the higher direct images of `𝐆_a`. Let `f : X ⟶ S`
be a morphism of schemes over `𝐅_p` such that `𝐆_{a,S} ⟶ f_*𝐆_{a,X}` is an isomorphism,
`Rᵠf_*𝐆_a = 0` for `q ≥ 2`, and `F - 1` on `R¹f_*𝐆_a` is an epimorphism with constructible
kernel. Then every cohomology sheaf of `Rf_*(𝐙/p𝐙)` is constructible: in degree `0` it is the
kernel of `F - 1` on `𝐆_{a,S}`, the constant sheaf `𝐙/p𝐙`; in degree `1` the kernel of `F - 1`
on `R¹f_*𝐆_a`; in all other degrees it vanishes. This is the long exact sequence argument of
case (b) of the proof of [Stacks, Tag 0GKV]. -/
theorem isConstructibleEtaleAbelianSheaf_homology_etaleAbelianDerivedDirectImage_constantZMod
    [hcmp : IsIso (additiveDirectImageComparisonGeneral.{u, 0} f)]
    (hvan : ∀ n : ℕ, 2 ≤ n →
      IsZero (((etaleAbelianDirectImage.{u, 0} f).rightDerived n).obj (additiveSheaf.{u, 0} X)))
    (hepi : Epi (((etaleAbelianDirectImage.{u, 0} f).rightDerived 1).map
      (artinSchreierMap.{u, 0} X hp hX)))
    (hker : _root_.Stacks.EtaleCohomology.IsConstructibleSmallEtaleAbelianSheaf.{u, 0}
      (kernel (((etaleAbelianDirectImage.{u, 0} f).rightDerived 1).map
        (artinSchreierMap.{u, 0} X hp hX))))
    (q : ℤ) :
    _root_.Stacks.EtaleCohomology.IsConstructibleSmallEtaleAbelianSheaf.{u, 0}
      ((homologyDerivedDirectImageSingle f q).obj
        ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
          (AddCommGrpCat.of (ULift.{u + 1} (ZMod p))))) := by
  have : NeZero p := ⟨hp.ne_zero⟩
  let AS := constantArtinSchreierSequence.{u, 0} X hp hX
  have hAS : AS.ShortExact := constantArtinSchreierSequence_shortExact.{u, 0} X hp hX
  let R := etaleAbelianDerivedDirectImage.{u, 0} f
  have hGE : ∀ K : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1},
      (R.obj ((DerivedCategory.singleFunctor _ 0).obj K)).IsGE 0 := fun K =>
    isGE_etaleAbelianDerivedDirectImage_obj.{u, 0} f _ 0 inferInstance
  have hneg : ∀ (K : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (i : ℤ), i < 0 →
      IsZero ((homologyDerivedDirectImageSingle f i).obj K) := fun K i hi => by
    have := hGE K
    exact DerivedCategory.isZero_of_isGE _ 0 i hi
  have hzeroG : ∀ n : ℕ, 2 ≤ n →
      IsZero ((homologyDerivedDirectImageSingle f n).obj (additiveSheaf.{u, 0} X)) :=
    fun n hn => (hvan n hn).of_iso ((homologyDerivedDirectImageSingleIso f n).app _)
  -- surjectivity of `F - 1` on `Hⁿ(Rf_*𝐆_a)` in every degree `n ≥ -1`
  have hepiAt : ∀ n : ℤ, n ≠ 0 → n ≠ 1 →
      Epi ((homologyDerivedDirectImageSingle f n).map AS.g) := by
    intro n h0 h1
    rcases lt_or_gt_of_ne h0 with hn | hn
    · exact IsZero.epi (hneg _ n hn) _
    · obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m := ⟨n.toNat, (Int.toNat_of_nonneg hn.le).symm⟩
      exact IsZero.epi (hzeroG m (by omega)) _
  have hepi0 : Epi ((homologyDerivedDirectImageSingle f 0).map AS.g) :=
    epi_homology_zero_map_artinSchreierMap f hp hS hX
  have hepi1 : Epi ((homologyDerivedDirectImageSingle f 1).map AS.g) :=
    (epi_homologyDerivedDirectImageSingle_map_iff f AS.g 1).2 hepi
  have hepiAll : ∀ n : ℤ, Epi ((homologyDerivedDirectImageSingle f n).map AS.g) := by
    intro n
    by_cases h0 : n = 0
    · subst h0; exact hepi0
    by_cases h1 : n = 1
    · subst h1; exact hepi1
    exact hepiAt n h0 h1
  -- `Hⁿ(Rf_*𝐆_a[0])`'s kernel of `F - 1` is `Hⁿ(Rf_*(𝐙/p𝐙)[0])` when `F - 1` is epi in degree
  -- `n - 1`
  have hkerIso : ∀ n : ℕ, Epi ((homologyDerivedDirectImageSingle f ((n : ℤ) - 1)).map AS.g) →
      ((homologyDerivedDirectImageSingle f n).obj AS.X₁ ≅
        kernel (((etaleAbelianDirectImage.{u, 0} f).rightDerived n).map AS.g)) := fun n h =>
    have hk := DerivedCategory.isIso_kernelLift_homologyMap_of_shortExact R hAS ((n : ℤ) - 1) n
      (by omega) h
    have w : (homologyDerivedDirectImageSingle f n).map AS.f ≫
        (homologyDerivedDirectImageSingle f n).map AS.g = 0 := by
      rw [← Functor.map_comp, AS.zero, Functor.map_zero]
    (@asIso _ _ _ _ (kernel.lift ((homologyDerivedDirectImageSingle f n).map AS.g)
      ((homologyDerivedDirectImageSingle f n).map AS.f) w) hk) ≪≫
        kernelHomologyDerivedDirectImageSingleIso f AS.g n
  rcases lt_trichotomy q 0 with hq | rfl | hq
  · exact isConstructibleEtaleAbelianSheaf_of_isZero (hneg _ q hq)
  · -- degree zero: the kernel of `F - 1` on `𝐆_{a,S}`
    let e₂ : kernel (((etaleAbelianDirectImage.{u, 0} f).rightDerived 0).map AS.g) ≅
        kernel ((etaleAbelianDirectImage.{u, 0} f).map AS.g) :=
      kernel.mapIso _ _ ((etaleAbelianDirectImage.{u, 0} f).rightDerivedZeroIsoSelf.app _)
        ((etaleAbelianDirectImage.{u, 0} f).rightDerivedZeroIsoSelf.app _)
        ((etaleAbelianDirectImage.{u, 0} f).rightDerivedZeroIsoSelf.hom.naturality AS.g)
    let e₃ : kernel (artinSchreierMap.{u, 0} S hp hS) ≅
        kernel ((etaleAbelianDirectImage.{u, 0} f).map AS.g) :=
      kernel.mapIso _ _ (@asIso _ _ _ _ (additiveDirectImageComparisonGeneral.{u, 0} f) hcmp)
        (@asIso _ _ _ _ (additiveDirectImageComparisonGeneral.{u, 0} f) hcmp)
        (artinSchreierMap_comp_additiveDirectImageComparison_unconditional f hp hS hX)
    let AS' := constantArtinSchreierSequence.{u, 0} S hp hS
    have hAS' : AS'.ShortExact := constantArtinSchreierSequence_shortExact.{u, 0} S hp hS
    have := hAS'.mono_f
    let e₄ : AS'.X₁ ≅ kernel AS'.g :=
      IsLimit.conePointUniqueUpToIso hAS'.exact.fIsKernel (limit.isLimit _)
    refine isConstructibleEtaleAbelianSheaf_of_iso
      (e₄ ≪≫ e₃ ≪≫ e₂.symm ≪≫ (hkerIso 0 (by simpa using hepiAll (-1))).symm) ?_
    exact isConstructibleEtaleAbelianSheaf_constantSheaf_general.{u, 0} S _
  · rcases eq_or_lt_of_le (show (1 : ℤ) ≤ q by omega) with rfl | hq2
    · -- degree one: the kernel of `F - 1` on `R¹f_*𝐆_a`
      exact isConstructibleEtaleAbelianSheaf_of_iso
        (hkerIso 1 (by simpa using hepi0)).symm hker
    · -- degrees at least two: zero
      obtain ⟨m, rfl⟩ : ∃ m : ℕ, q = m := ⟨q.toNat, (Int.toNat_of_nonneg (by omega)).symm⟩
      refine isConstructibleEtaleAbelianSheaf_of_isZero ?_
      exact DerivedCategory.isZero_homology_of_shortExact R hAS ((m : ℤ) - 1) m (by omega)
        (hepiAll _) (hzeroG m (by omega))

end Stacks.ArtinSchreier
