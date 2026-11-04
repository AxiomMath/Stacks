module

public import StacksFrontier.AlgebraicGeometry.Divisors.EtaPullbackLocalModel
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.QuasiIsoLocalOnPullbacks
public import StacksFrontier.AlgebraicGeometry.DivisorFlatPullback.Basic

/-!
# The comparison of décalages under a pullback is local on the source and on the target

Let `h : Y ⟶ X` be a morphism of schemes, `D ⊆ X` an effective Cartier divisor whose pullback
along `h` is defined, `P^•` a K-flat complex of flat `𝒪_X`-modules and `r : R^• ⟶ η_{ℐ_D} P^•` a
quasi-isomorphism out of a K-flat complex.  This file reduces the statement that the map of
complexes

`ψ_h : h^* R^• ⟶ h^*(η_{ℐ_D} P^•) ⟶ η_{ℐ_{h^{-1}D}}(h^* P^•)`

is a quasi-isomorphism to local statements: it suffices that every point of `Y` lies in the image
of an open immersion `j : V ⟶ Y` for which `j ≫ h` factors as `g ≫ ι` with `ι : U ⟶ X` an open
immersion, and for which the corresponding map for `g`, built from the restriction of `P^•` to
`U`, is a quasi-isomorphism.

The two reductions are the comparison of décalages for a composite of pullbacks
(`Stacks.IdealTorsion.Eta.quasiIso_transportedPullbackEtaMap_comp_iff`), applied to `j ≫ h` and
to `g ≫ ι`, together with the invertibility of the comparison along a flat morphism, and the
stalkwise nature of quasi-isomorphy
(`Stacks.IdealTorsion.Eta.quasiIso_of_forall_exists_quasiIso_pullbackComplexMap`).

## Main results

* `Stacks.Divisors.Eta.quasiIso_comp_flat_iff`: precomposing with a flat morphism.
* `Stacks.Divisors.Eta.quasiIso_flat_comp_iff`: postcomposing with a flat morphism.
* `Stacks.Divisors.Eta.quasiIso_divisorPullbackEtaMap_of_local`: the local criterion.
-/

@[expose] public noncomputable section

attribute [local instance_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf Stacks.SheafOfModules.TensorSheafification.structureSheaf

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

open Stacks.RingedSpace (pullbackFunctor)
open Stacks.IdealTorsion.Eta (etaObj pullbackComplex pullbackComplexMap pullbackIdealIncl)

universe u

namespace Stacks.Divisors.Eta

/-- The identification `k^*ℐ_D ≅ ℐ_{k^{-1}D}`, transported along an equality `k^{-1}D = D₂` of
ideal sheaf data. -/
def pullbackIdealSheafComapIsoOfEq {W Y : Scheme.{u}} (k : W ⟶ Y) (D : Y.IdealSheafData)
    [Stacks.Divisors.IsEffectiveCartierDivisor D] (hk : Stacks.Divisors.IsPullbackDefined k D)
    {D₂ : W.IdealSheafData} (hD : D.comap k = D₂) :
    Iso (C := SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf W.toRingedSpace.sheaf))
      ((pullbackFunctor k.toLRSHom.toShHom).obj (idealSheaf D)) (idealSheaf D₂) :=
  Stacks.Divisors.pullbackIdealSheafComapIso k D hk ≪≫ eqToIso (congrArg idealSheaf hD)

/-- The transported identification is compatible with the inclusions. -/
theorem pullbackIdealSheafComapIsoOfEq_hom_comp_idealSheafι {W Y : Scheme.{u}}
    (k : W ⟶ Y) (D : Y.IdealSheafData) [Stacks.Divisors.IsEffectiveCartierDivisor D]
    (hk : Stacks.Divisors.IsPullbackDefined k D) {D₂ : W.IdealSheafData}
    (hD : D.comap k = D₂) :
    (pullbackIdealSheafComapIsoOfEq k D hk hD).hom ≫ idealSheafι D₂ =
      pullbackIdealIncl k.toLRSHom.toShHom (idealSheaf D) (idealSheafι D) := by
  subst hD
  exact (Category.assoc _ _ _).trans <|
    (congrArg (fun t => (Stacks.Divisors.pullbackIdealSheafComapIso k D hk).hom ≫ t)
      (Category.id_comp (idealSheafι (D.comap k)))).trans
    (Stacks.Divisors.pullbackIdealSheafComapIso_hom_comp_idealSheafι k D hk)

/-- For the trivial equality the transported identification is the identification itself. -/
theorem pullbackIdealSheafComapIsoOfEq_rfl {W Y : Scheme.{u}}
    (k : W ⟶ Y) (D : Y.IdealSheafData) [Stacks.Divisors.IsEffectiveCartierDivisor D]
    (hk : Stacks.Divisors.IsPullbackDefined k D) :
    pullbackIdealSheafComapIsoOfEq k D hk rfl = Stacks.Divisors.pullbackIdealSheafComapIso k D hk :=
  Iso.trans_refl _

/-- **The comparison of décalages, with its target transported along an equality of ideal sheaf
data.** -/
theorem quasiIso_divisorPullbackEtaMap_iff_eqToIso {W Y : Scheme.{u}} (k : W ⟶ Y)
    (D : Y.IdealSheafData) [Stacks.Divisors.IsEffectiveCartierDivisor D]
    [hk : Stacks.Divisors.IsPullbackDefined k D] (D₂ : W.IdealSheafData)
    [Stacks.Divisors.IsEffectiveCartierDivisor D₂] (hD : D.comap k = D₂)
    (P : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.toRingedSpace.sheaf)) ℤ)
    (hP : ∀ n : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u}
      (O := Y.toRingedSpace.sheaf) (P.X n))
    {R : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.toRingedSpace.sheaf)) ℤ}
    (r : R ⟶ @etaObj Y.toRingedSpace (idealSheaf D) (idealSheafι D) (mono_idealSheafι D)
      (isInvertible_idealSheaf D) P (isIdealTorsionFree_X D P hP)) :
    QuasiIso (pullbackComplexMap k.toLRSHom.toShHom r ≫ divisorPullbackEtaMap k D P hP) ↔
      QuasiIso (pullbackComplexMap k.toLRSHom.toShHom r ≫
        @Stacks.IdealTorsion.Eta.transportedPullbackEtaMap _ _ k.toLRSHom.toShHom
          (idealSheaf D) (idealSheafι D) (isInvertible_idealSheaf D)
          (idealSheaf D₂) (idealSheafι D₂) (isInvertible_idealSheaf D₂)
          (pullbackIdealSheafComapIsoOfEq k D hk hD)
          (mono_idealSheafι D) (mono_pullbackIdealIncl_of_isPullbackDefined k D inferInstance)
          (mono_idealSheafι D₂)
          (pullbackIdealSheafComapIsoOfEq_hom_comp_idealSheafι k D hk hD) P
          (isIdealTorsionFree_X D P hP) (isIdealTorsionFree_pullbackComplex_X' k D P hP)
          (fun n => isIdealTorsionFree_of_isFlat D₂ _ (isFlat_pullbackComplex_X k P hP n))) := by
  subst hD
  have he := pullbackIdealSheafComapIsoOfEq_rfl k D hk
  rw [@Stacks.IdealTorsion.Eta.transportedPullbackEtaMap_congr_iso _ _ k.toLRSHom.toShHom
    (idealSheaf D) (idealSheafι D) (isInvertible_idealSheaf D)
    (idealSheaf (D.comap k)) (idealSheafι (D.comap k)) (isInvertible_idealSheaf (D.comap k))
    (mono_idealSheafι D) (mono_pullbackIdealIncl_of_isPullbackDefined k D inferInstance)
    (mono_idealSheafι (D.comap k)) P
    (isIdealTorsionFree_X D P hP) (isIdealTorsionFree_pullbackComplex_X' k D P hP)
    (fun n => isIdealTorsionFree_of_isFlat (D.comap k) _ (isFlat_pullbackComplex_X k P hP n))
    _ _ he]
  rfl

section Composite

variable {V Y X : Scheme.{u}} (j : V ⟶ Y) (h : Y ⟶ X) (D : X.IdealSheafData)
  [Stacks.Divisors.IsEffectiveCartierDivisor D] [hD : Stacks.Divisors.IsPullbackDefined h D]
  [hj : Stacks.Divisors.IsPullbackDefined j (D.comap h)]
  [hjh : Stacks.Divisors.IsPullbackDefined (j ≫ h) D]
  (P : CochainComplex
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.toRingedSpace.sheaf)) ℤ)
  (hP : ∀ n : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u}
    (O := X.toRingedSpace.sheaf) (P.X n))
  {R : CochainComplex
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.toRingedSpace.sheaf)) ℤ}
  (r : R ⟶ @etaObj X.toRingedSpace (idealSheaf D) (idealSheafι D) (mono_idealSheafι D)
    (isInvertible_idealSheaf D) P (isIdealTorsionFree_X D P hP))

/-- **The comparison for a composite is the composite of the comparisons, on
quasi-isomorphisms**: the comparison for `j ≫ h`, precomposed with the pullback of `r`, is a
quasi-isomorphism exactly when the comparison for `j` composed with the pullback along `j` of the
one for `h` is. -/
theorem quasiIso_divisorPullbackEtaMap_comp_iff :
    QuasiIso (pullbackComplexMap (j ≫ h).toLRSHom.toShHom r ≫
        divisorPullbackEtaMap (j ≫ h) D P hP) ↔
      QuasiIso (pullbackComplexMap j.toLRSHom.toShHom
          (pullbackComplexMap h.toLRSHom.toShHom r ≫ divisorPullbackEtaMap h D P hP) ≫
        divisorPullbackEtaMap j (D.comap h) (pullbackComplex h.toLRSHom.toShHom P)
          (isFlat_pullbackComplex_X h P hP)) := by
  have hcomp : D.comap (j ≫ h) = (D.comap h).comap j := Scheme.IdealSheafData.comap_comp D j h
  have hjh' : Stacks.Divisors.IsEffectiveCartierDivisor ((D.comap h).comap j) := hj
  rw [quasiIso_divisorPullbackEtaMap_iff_eqToIso (j ≫ h) D ((D.comap h).comap j) hcomp P hP r]
  have hk : j.toLRSHom.toShHom ≫ h.toLRSHom.toShHom = (j ≫ h).toLRSHom.toShHom := by
    rw [Scheme.Hom.comp_toLRSHom, LocallyRingedSpace.comp_toShHom]
  exact @Stacks.IdealTorsion.Eta.quasiIso_transportedPullbackEtaMap_comp_iff' _ _ _
    j.toLRSHom.toShHom h.toLRSHom.toShHom
    (idealSheaf D) (idealSheafι D) (isInvertible_idealSheaf D)
    (idealSheaf (D.comap h)) (idealSheafι (D.comap h)) (isInvertible_idealSheaf (D.comap h))
    (idealSheaf ((D.comap h).comap j)) (idealSheafι ((D.comap h).comap j))
    (isInvertible_idealSheaf ((D.comap h).comap j))
    (mono_idealSheafι D) (mono_idealSheafι (D.comap h)) (mono_idealSheafι ((D.comap h).comap j))
    (mono_pullbackIdealIncl_of_isPullbackDefined h D inferInstance)
    (mono_pullbackIdealIncl_of_isPullbackDefined j (D.comap h) inferInstance)
    (Stacks.Divisors.pullbackIdealSheafComapIso h D hD)
    (Stacks.Divisors.pullbackIdealSheafComapIso_hom_comp_idealSheafι h D hD)
    (Stacks.Divisors.pullbackIdealSheafComapIso j (D.comap h) hj)
    (Stacks.Divisors.pullbackIdealSheafComapIso_hom_comp_idealSheafι j (D.comap h) hj)
    P (isIdealTorsionFree_X D P hP) (isIdealTorsionFree_pullbackComplex_X' h D P hP)
    (isIdealTorsionFree_pullbackComplex_X h D P hP)
    (isIdealTorsionFree_pullbackComplex_X' j (D.comap h) _ (isFlat_pullbackComplex_X h P hP))
    (isIdealTorsionFree_pullbackComplex_X j (D.comap h) _ (isFlat_pullbackComplex_X h P hP))
    (j ≫ h).toLRSHom.toShHom hk
    (mono_pullbackIdealIncl_of_isPullbackDefined (j ≫ h) D inferInstance)
    (pullbackIdealSheafComapIsoOfEq (j ≫ h) D hjh hcomp)
    (pullbackIdealSheafComapIsoOfEq_hom_comp_idealSheafι (j ≫ h) D hjh hcomp)
    (isIdealTorsionFree_pullbackComplex_X' (j ≫ h) D P hP)
    (fun n => isIdealTorsionFree_of_isFlat ((D.comap h).comap j) _
      (isFlat_pullbackComplex_X (j ≫ h) P hP n)) R r

end Composite

/-! ### The local criterion -/

/-- If `a` is pullback defined for `b⁻¹D`, then `a ≫ b` is pullback defined for `D`. -/
private theorem isPullbackDefined_comp_of_comap {W Y X : Scheme.{u}} (a : W ⟶ Y) (b : Y ⟶ X)
    (D : X.IdealSheafData) [Stacks.Divisors.IsEffectiveCartierDivisor D]
    (ha : Stacks.Divisors.IsPullbackDefined a (D.comap b)) :
    Stacks.Divisors.IsPullbackDefined (a ≫ b) D := by
  change Stacks.Divisors.IsEffectiveCartierDivisor (D.comap (a ≫ b))
  rw [Scheme.IdealSheafData.comap_comp]; exact ha

section Local

variable {Y X : Scheme.{u}} (h : Y ⟶ X) (D : X.IdealSheafData)
  [Stacks.Divisors.IsEffectiveCartierDivisor D] [hD : Stacks.Divisors.IsPullbackDefined h D]
  (P : CochainComplex
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.toRingedSpace.sheaf)) ℤ)
  (hP : ∀ n : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u}
    (O := X.toRingedSpace.sheaf) (P.X n))
  {R : CochainComplex
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.toRingedSpace.sheaf)) ℤ}
  (r : R ⟶ @etaObj X.toRingedSpace (idealSheaf D) (idealSheafι D) (mono_idealSheafι D)
    (isInvertible_idealSheaf D) P (isIdealTorsionFree_X D P hP))

/-- The comparison of décalages along a flat morphism is an isomorphism of complexes. -/
theorem isIso_divisorPullbackEtaMap_of_flat [Flat h] :
    IsIso (divisorPullbackEtaMap h D P hP) := by
  have hflat : AlgebraicGeometry.IsFlat h.toLRSHom.toShHom := fun x => Flat.stalkMap h x
  have h1 := @Stacks.IdealTorsion.Eta.isIso_pullbackEtaMap _ _ h.toLRSHom.toShHom
    (idealSheaf D) (idealSheafι D) (mono_idealSheafι D) (isInvertible_idealSheaf D)
    (mono_pullbackIdealIncl_of_isPullbackDefined h D inferInstance) P (isIdealTorsionFree_X D P hP)
    (isIdealTorsionFree_pullbackComplex_X' h D P hP) hflat
  have h2 := (@Stacks.IdealTorsion.Eta.IdealCongr.etaIso Y.toRingedSpace
    ((pullbackFunctor h.toLRSHom.toShHom).obj (idealSheaf D)) (idealSheaf (D.comap h))
    (Stacks.IdealTorsion.Eta.isInvertible_pullbackIdeal h.toLRSHom.toShHom (idealSheaf D))
    (isInvertible_idealSheaf (D.comap h))
    (pullbackIdealIncl h.toLRSHom.toShHom (idealSheaf D) (idealSheafι D))
    (idealSheafι (D.comap h)) (Stacks.Divisors.pullbackIdealSheafComapIso h D hD)
    (Stacks.Divisors.pullbackIdealSheafComapIso_hom_comp_idealSheafι h D hD)
    (pullbackComplex h.toLRSHom.toShHom P)
    (mono_pullbackIdealIncl_of_isPullbackDefined h D inferInstance)
    (mono_idealSheafι (D.comap h)) (isIdealTorsionFree_pullbackComplex_X' h D P hP)
    (isIdealTorsionFree_pullbackComplex_X h D P hP)).isIso_hom
  exact IsIso.comp_isIso' h1 h2

omit hD in
/-- The comparison of décalages depends on the morphism only through its value. -/
theorem quasiIso_divisorPullbackEtaMap_congr {k₁ k₂ : Y ⟶ X} (hk : k₁ = k₂)
    [Stacks.Divisors.IsPullbackDefined k₁ D] [Stacks.Divisors.IsPullbackDefined k₂ D] :
    QuasiIso (pullbackComplexMap k₁.toLRSHom.toShHom r ≫ divisorPullbackEtaMap k₁ D P hP) ↔
      QuasiIso (pullbackComplexMap k₂.toLRSHom.toShHom r ≫ divisorPullbackEtaMap k₂ D P hP) := by
  subst hk; exact Iff.rfl

/-- **The local criterion.**  The map of complexes `h^* R^• ⟶ η_{ℐ_{h^{-1}D}}(h^* P^•)` is a
quasi-isomorphism as soon as every point of `Y` lies in the image of an open immersion
`j : V ⟶ Y` such that `j ≫ h = g ≫ ι` for an open immersion `ι : U ⟶ X`, and the corresponding
map for `g`, built from the restriction `ι^* P^•` and the resolution `ι^* r` of its décalage, is a
quasi-isomorphism. -/
theorem quasiIso_divisorPullbackEtaMap_of_local
    (hloc : ∀ y : Y, ∃ (V U : Scheme.{u}) (j : V ⟶ Y) (g : V ⟶ U) (ι : U ⟶ X) (x : V),
      IsOpenImmersion j ∧ j x = y ∧ ∃ (_ : j ≫ h = g ≫ ι)
        (_ : Stacks.Divisors.IsPullbackDefined ι D)
        (_ : Stacks.Divisors.IsPullbackDefined g (D.comap ι)),
        QuasiIso (pullbackComplexMap g.toLRSHom.toShHom
            (pullbackComplexMap ι.toLRSHom.toShHom r ≫ divisorPullbackEtaMap ι D P hP) ≫
          divisorPullbackEtaMap g (D.comap ι) (pullbackComplex ι.toLRSHom.toShHom P)
            (isFlat_pullbackComplex_X ι P hP))) :
    QuasiIso (pullbackComplexMap h.toLRSHom.toShHom r ≫ divisorPullbackEtaMap h D P hP) := by
  refine Stacks.IdealTorsion.Eta.quasiIso_of_forall_exists_quasiIso_pullbackComplexMap _
    (fun y => ?_)
  obtain ⟨V, U, j, g, ι, x, hj, rfl, hcomm, hιD, hg, hq⟩ := hloc y
  refine ⟨V.toRingedSpace, j.toLRSHom.toShHom, x, rfl, inferInstance, ?_⟩
  have hjD : Stacks.Divisors.IsPullbackDefined j (D.comap h) :=
    Stacks.Divisors.isPullbackDefined_of_flat j (D.comap h) hD
  have hjhD := isPullbackDefined_comp_of_comap j h D hjD
  have hgιD := isPullbackDefined_comp_of_comap g ι D hg
  have hiso := isIso_divisorPullbackEtaMap_of_flat j (D.comap h)
    (pullbackComplex h.toLRSHom.toShHom P)
    (isFlat_pullbackComplex_X h P hP)
  rw [← quasiIso_iff_comp_right _ (divisorPullbackEtaMap j (D.comap h)
    (pullbackComplex h.toLRSHom.toShHom P) (isFlat_pullbackComplex_X h P hP)),
    ← quasiIso_divisorPullbackEtaMap_comp_iff j h D P hP r,
    quasiIso_divisorPullbackEtaMap_congr D P hP r hcomm,
    quasiIso_divisorPullbackEtaMap_comp_iff g ι D P hP r]
  exact hq

end Local

end Stacks.Divisors.Eta

end
