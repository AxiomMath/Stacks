module

public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleQuotients.Basic
public import StacksFrontier.Deformation.Examples.Geometric.SchemesTangentSpaceLinear

/-!
# The ideal of the closed point of `Spec k[V]`

Let `V` be a finite-dimensional `k`-vector space and `k[V] = k ⊕ V` the square-zero extension, an
object of `𝒞_Λ`. The ideal of the closed point `Spec k ⊂ Spec k[V]` is `V`, so the module `f^* 𝒥`
of the deformation problem of [Stacks Project, Tag 08U7] attached to a deformation of a scheme `X`
over `k[V]` is `𝒪_X ⊗_k V`. This file builds those identifications; they are the coefficients of
the `k`-linear form of the second display of [Stacks Project, Tag 0DY9].

## Main definitions

* `Deformation.Examples.coordBase`: `k[V]` as an object of `𝒞_Λ`.
* `Deformation.Examples.kerTopLinearEquiv`: the ideal of the closed point on global sections is
  `Γ(Spec k, V^~)`.
* `Deformation.Examples.coordConormalIso`: the conormal sheaf of the closed point is `V^~`.
* `Deformation.Examples.coordPulledIdealIso`: `f^* 𝒥 ≅ 𝒪_X ⊗_k V`.

## References

* [Stacks Project, Tag 0DY9](https://stacks.math.columbia.edu/tag/0DY9)
* [Stacks Project, Tag 08U7](https://stacks.math.columbia.edu/tag/08U7)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Deformation.Examples

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k] (V : FGModuleCat.{u} k)

/-- `k[V]`. -/
noncomputable abbrev coordBase : ArtinianLocalAlgCat.{u, u, u} Λ k :=
  (squareZeroExtensionArtinian.{u, u, u} Λ k).obj V

/-- The residue map of `k[V]` is the first coordinate. -/
theorem residueMap_coordBase (z : (coordBase (Λ := Λ) V : Type u)) :
    Deformation.Artin.residueMap (coordBase (Λ := Λ) V) z = TrivSqZeroExt.fst z :=
  squareZeroExtensionArtinian_residue Λ k V z

/-- A global function in the ideal of the closed point has vanishing first coordinate. -/
theorem fst_ΓSpecIso_of_mem_ker
    (a : RingHom.ker (topComorphism (residueSpecMap (coordBase (Λ := Λ) V)).toLRSHom.toShHom)) :
    TrivSqZeroExt.fst ((Scheme.ΓSpecIso (CommRingCat.of (coordBase (Λ := Λ) V))).hom.hom a.1) =
      0 := by
  have h := specIso_topComorphism (coordBase (Λ := Λ) V) a.1
  have h0 : (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv
      (topComorphism (residueSpecMap (coordBase (Λ := Λ) V)).toLRSHom.toShHom a.1) = 0 :=
    (RingEquiv.map_eq_zero_iff _).2 a.2
  rw [← residueMap_coordBase]
  exact h.symm.trans h0


/-- `V^~` on `Spec k`, in the spelling of sheaves of modules over the structure sheaf. -/
noncomputable abbrev tildeCoeff :
    SheafOfModules.{u} (structureSheafRing (Spec (CommRingCat.of k)).toRingedSpace) :=
  (tilde.functor (CommRingCat.of k)).obj V.obj



/-- The ideal of the closed point of `Spec k[V]` on global sections is `V`. -/
noncomputable def kerTopEquivV :
    RingHom.ker (topComorphism (residueSpecMap (coordBase (Λ := Λ) V)).toLRSHom.toShHom) ≃+ V where
  toFun a :=
    TrivSqZeroExt.snd ((Scheme.ΓSpecIso (CommRingCat.of (coordBase (Λ := Λ) V))).hom.hom a.1)
  invFun v := ⟨(Scheme.ΓSpecIso (CommRingCat.of (coordBase (Λ := Λ) V))).inv.hom
      (TrivSqZeroExt.inr v), by
    have h := specIso_topComorphism (coordBase (Λ := Λ) V)
      ((Scheme.ΓSpecIso (CommRingCat.of (coordBase (Λ := Λ) V))).inv.hom (TrivSqZeroExt.inr v))
    have h2 : (Scheme.ΓSpecIso (CommRingCat.of (coordBase (Λ := Λ) V))).commRingCatIsoToRingEquiv
        ((Scheme.ΓSpecIso (CommRingCat.of (coordBase (Λ := Λ) V))).inv.hom (TrivSqZeroExt.inr v)) =
        TrivSqZeroExt.inr v :=
      congrArg (fun f => f.hom (TrivSqZeroExt.inr v))
        (Scheme.ΓSpecIso (CommRingCat.of (coordBase (Λ := Λ) V))).inv_hom_id
    rw [h2] at h
    have h3 : Deformation.Artin.residueMap (coordBase (Λ := Λ) V)
        (TrivSqZeroExt.inr v : (coordBase (Λ := Λ) V : Type u)) = 0 :=
      (residueMap_coordBase V _).trans (TrivSqZeroExt.fst_inr _ _)
    exact (RingEquiv.map_eq_zero_iff _).1 (h.trans h3)⟩
  left_inv a := by
    apply Subtype.ext
    change (Scheme.ΓSpecIso (CommRingCat.of (coordBase (Λ := Λ) V))).inv.hom
      (TrivSqZeroExt.inr (TrivSqZeroExt.snd
        ((Scheme.ΓSpecIso (CommRingCat.of (coordBase (Λ := Λ) V))).hom.hom a.1))) = a.1
    have hfst := fst_ΓSpecIso_of_mem_ker V a
    have e : TrivSqZeroExt.inr (TrivSqZeroExt.snd
        ((Scheme.ΓSpecIso (CommRingCat.of (coordBase (Λ := Λ) V))).hom.hom a.1)) =
        (Scheme.ΓSpecIso (CommRingCat.of (coordBase (Λ := Λ) V))).hom.hom a.1 :=
      TrivSqZeroExt.ext hfst.symm rfl
    rw [e]
    exact congrArg (fun f => f.hom a.1)
      (Scheme.ΓSpecIso (CommRingCat.of (coordBase (Λ := Λ) V))).hom_inv_id
  right_inv v := by
    change TrivSqZeroExt.snd ((Scheme.ΓSpecIso (CommRingCat.of (coordBase (Λ := Λ) V))).hom.hom
      ((Scheme.ΓSpecIso (CommRingCat.of (coordBase (Λ := Λ) V))).inv.hom
        (TrivSqZeroExt.inr v))) = v
    have h2 := congrArg (fun f => f.hom (TrivSqZeroExt.inr v))
      (Scheme.ΓSpecIso (CommRingCat.of (coordBase (Λ := Λ) V))).inv_hom_id
    exact (congrArg TrivSqZeroExt.snd h2).trans (TrivSqZeroExt.snd_inr _ _)
  map_add' a b := by
    change TrivSqZeroExt.snd ((Scheme.ΓSpecIso (CommRingCat.of (coordBase (Λ := Λ) V))).hom.hom
      (a.1 + b.1)) = _
    rw [map_add]
    rfl


/-- In `k[V]`, a product with an element of the maximal ideal is the scalar multiple by the
residue. -/
theorem snd_mul_of_fst_eq_zero (x y : (coordBase (Λ := Λ) V : Type u))
    (hy : TrivSqZeroExt.fst y = 0) :
    TrivSqZeroExt.snd (x * y) = TrivSqZeroExt.fst x • TrivSqZeroExt.snd y := by
  change (TrivSqZeroExt.fst x • TrivSqZeroExt.snd y + TrivSqZeroExt.fst y • TrivSqZeroExt.snd x :
    V) = _
  rw [hy, zero_smul, add_zero]

/-- The identification of the ideal of the closed point of `Spec k[V]` on global sections with
`Γ(Spec k, V^~)`, linear over `Γ(Spec k[V], ⊤)`. -/
noncomputable def kerTopLinearEquiv :
    RingHom.ker (topComorphism (residueSpecMap (coordBase (Λ := Λ) V)).toLRSHom.toShHom)
      ≃ₗ[(baseSpec (coordBase (Λ := Λ) V)).presheaf.obj (op ⊤)]
      ((SheafOfModules.evaluation
        (structureSheafRing (baseSpec (coordBase (Λ := Λ) V)).toRingedSpace) (op ⊤)).obj
        ((RingedSpaceModuleAdjunction.modulePushforward
          (residueSpecMap (coordBase (Λ := Λ) V)).toLRSHom.toShHom).obj (tildeCoeff V))) where
  __ := (kerTopEquivV V).trans (tilde.isoTop (R := CommRingCat.of k) V.obj).toLinearEquiv.toAddEquiv
  map_smul' r a := by
    set c : k :=
      TrivSqZeroExt.fst ((Scheme.ΓSpecIso (CommRingCat.of (coordBase (Λ := Λ) V))).hom.hom r)
    have hL : kerTopEquivV V (r • a) = c • kerTopEquivV V a := by
      change TrivSqZeroExt.snd ((Scheme.ΓSpecIso (CommRingCat.of (coordBase (Λ := Λ) V))).hom.hom
        (r * a.1)) = _
      rw [map_mul]
      exact snd_mul_of_fst_eq_zero V _ _ (fst_ΓSpecIso_of_mem_ker V a)
    have hc : topComorphism (residueSpecMap (coordBase (Λ := Λ) V)).toLRSHom.toShHom r =
        (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom c := by
      have h := specIso_topComorphism (coordBase (Λ := Λ) V) r
      rw [residueMap_coordBase] at h
      refine ((Scheme.ΓSpecIso
        (CommRingCat.of k)).commRingCatIsoToRingEquiv.symm_apply_apply _).symm.trans ?_
      exact congrArg (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.symm h
    refine ((congrArg (tilde.toOpen (R := CommRingCat.of k) V.obj ⊤).hom hL).trans
      (map_smul _ c _)).trans ?_
    refine (Scheme.Modules.smul_Spec_def (M := (tilde.functor (CommRingCat.of k)).obj V.obj)
      (U := ⊤) c _).trans ?_
    have hmap : (Spec (CommRingCat.of k)).presheaf.map
        (⊤ : (Spec (CommRingCat.of k)).Opens).leTop.op
        ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom c) =
        topComorphism (residueSpecMap (coordBase (Λ := Λ) V)).toLRSHom.toShHom r := by
      rw [hc, show (⊤ : (Spec (CommRingCat.of k)).Opens).leTop.op = 𝟙 _ from
        Quiver.Hom.unop_inj (Subsingleton.elim _ _), CategoryTheory.Functor.map_id]
      rfl
    rw [hmap]
    rfl


/-- **The ideal of the closed point of `Spec k[V]` is the pushforward of `V^~`.** -/
noncomputable def coordIdealSheafIso :
    Stacks.ClosedImmersion.idealSheaf (residueSpecMap (coordBase (Λ := Λ) V)).toLRSHom.toShHom ≅
      (RingedSpaceModuleAdjunction.modulePushforward
        (residueSpecMap (coordBase (Λ := Λ) V)).toLRSHom.toShHom).obj (tildeCoeff V) :=
  idealSheafIsoOfKerIsoTop _ _ (kerTopLinearEquiv V).toModuleIso

/-- **The conormal sheaf of the closed point of `Spec k[V]` is `V^~`.** -/
noncomputable def coordConormalIso :
    Stacks.Thickenings.schemeConormalSheaf (residueSpecMap (coordBase (Λ := Λ) V)) ≅ tildeCoeff V :=
  haveI := residueSpecMap_isClosedImmersion (coordBase (Λ := Λ) V)
  conormalIsoOfIdealSheafIso (residueSpecMap (coordBase (Λ := Λ) V))
    ((residueSpecMap (coordBase (Λ := Λ) V)).app_surjective ⊤ (isAffineOpen_top _))
    (coordIdealSheafIso V)

/-- **`f^* 𝒥 ≅ 𝒪_X ⊗_k V` for the closed point of `Spec k[V]`.** -/
noncomputable def coordPulledIdealIso (X : Over (Spec (CommRingCat.of k))) :
    SchemeDeformationCategory.pulledIdeal (coordBase (Λ := Λ) V) X ≅
      (coefficientSheafFunctor X.hom).obj V :=
  (RingedSpaceModuleAdjunction.modulePullback X.hom.toLRSHom.toShHom).mapIso (coordConormalIso V) ≪≫
    ((Stacks.ProjectiveBundleQuotients.pullbackIso X.hom).app _).symm

end Deformation.Examples

end
