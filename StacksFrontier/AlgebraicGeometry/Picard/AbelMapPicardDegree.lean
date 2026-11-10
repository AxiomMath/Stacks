module

public import StacksFrontier.AlgebraicGeometry.Picard.AbelMapSurjective
public import StacksFrontier.AlgebraicGeometry.PicardScheme.CurvePicard.DegreeComponents
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertFamilyPicardClass
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertSchemeCurveSupplement
public import StacksFrontier.AlgebraicGeometry.PicardScheme.Jacobian.RiemannRochEffective

/-!
# The degree components `Pic^d_{X/k}` as targets of `γ_d`

The degree-`d` subfunctor of the Picard functor of a smooth projective curve with a rational
point, `Stacks.PicardFunctor.degreeSubfunctor`, is cut out by the fibre degree
`deg(ℒ_t) = χ(X_t, ℒ_t) - χ(X_t, 𝒪_{X_t})`. Since `χ(X_t, 𝒪_{X_t}) = 1 - g` on every fibre of a
geometrically integral curve of genus `g`, this is the condition `χ(X_t, ℒ_t) = d + 1 - g`, so
the degree subfunctor is a degree component in the sense of `Stacks.AbelMap.IsDegreeComponent`,
the description of `Pic^d_{X/k}` in [Stacks, Tag 0BA0]. When the Picard functor is
representable, `Pic^d_{X/k}` (`Stacks.PicardFunctor.picardSchemeDegreeComponent`) represents it.

## Main results

* `Stacks.AbelMap.fibreCohomology_unit`: the fibres of `𝒪_{X_T}` have `h⁰ = 1` and `h¹ = g`.
* `Stacks.AbelMap.isDegreeComponent_degreeSubfunctor`.
* `Stacks.AbelMap.degreeComponentRepresentableBy`: `Pic^d_{X/k}` represents the degree
  subfunctor.

## References

* [Stacks Project, Tag 0BA0](https://stacks.math.columbia.edu/tag/0BA0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.FibreCohomology (fibreCohomology)
open Stacks.PicardFunctor (picardFunctor toPicardFunctor baseChange baseChangeMap picardAt
  picardMap picardSchemeOver picardHomEquiv)

universe u

namespace Stacks.AbelMap

section Fibre

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  [IsCurve k f] [GeometricallyIrreducible f] [Smooth f] [IsProper f]

omit [IsCurve k f] in
/-- **The fibres of the structure sheaf of a family of curves.** For a geometrically irreducible
smooth proper curve `X` of genus `g` over `k` and a `k`-scheme `T`, every fibre of `X_T ⟶ T` has
`dim H⁰(X_t, 𝒪) = 1` and `dim H¹(X_t, 𝒪) = g`. -/
theorem fibreCohomology_unit (T : Over (Spec (.of k))) (t : T.left) :
    Module.finrank (T.left.residueField t)
        (fibreCohomology ((Over.pullback T.hom).obj (Over.mk f)).hom
          (SheafOfModules.unit _) t 0) = 1 ∧
      Module.finrank (T.left.residueField t)
        (fibreCohomology ((Over.pullback T.hom).obj (Over.mk f)).hom
          (SheafOfModules.unit _) t 1) = genus f := by
  let g := residueFieldPointι t
  have : IsProper ((Over.pullback T.hom).obj (Over.mk f)).hom :=
    inferInstanceAs (IsProper (pullback.snd f T.hom))
  let := residueFieldAlgebra t
  have hsq : IsPullback (pullback.fst f (residueFieldPoint t).hom)
      ((Over.pullback (residueFieldPoint t).hom).obj (Over.mk f)).hom f
      (Spec.map (CommRingCat.ofHom (algebraMap k (T.left.residueField t)))) :=
    IsPullback.of_hasPullback _ _
  have hfib : IsPullback (Stacks.Hilbert.familyBaseChangeMap (Over.mk f) g)
      ((Over.pullback (residueFieldPoint t).hom).obj (Over.mk f)).hom
      ((Over.pullback T.hom).obj (Over.mk f)).hom
      (Spec.map (𝟙 (T.left.residueField t)) ≫ T.left.fromSpecResidueField t) := by
    rw [Spec.map_id]
    convert Stacks.Hilbert.isPullback_familyBaseChangeMap (Over.mk f) g using 1
    exact Category.id_comp _
  have := isProper_of_isPullback f _ _ hsq
  have := isIso_globalSections_of_isPullback f _ _ hsq
  let eM := (Scheme.Modules.pullbackUnitIso (Stacks.Hilbert.familyBaseChangeMap (Over.mk f) g)).symm
  let fZ : ((Over.pullback (residueFieldPoint t).hom).obj (Over.mk f)).left ⟶
      Spec (.of ↑(T.left.residueField t)) :=
    ((Over.pullback (residueFieldPoint t).hom).obj (Over.mk f)).hom
  have e := Stacks.FibreCohomology.finrank_eq_of_isPullback (K := ↑(T.left.residueField t))
    _ _ t (𝟙 _) _ fZ hfib _ eM
  exact ⟨(e 0).symm.trans (finrank_cohomologyOverField_unit_zero_eq_one fZ), (e 1).symm.trans
    ((genus_eq_finrank_cohomologyOverField_unit_one' (↑(T.left.residueField t)) fZ).symm.trans
      (genus_baseChange k _ _ fZ f hsq))⟩

end Fibre

section Site

open Stacks.PicardFunctor Stacks.PicardCurve

variable {k : Type u} [Field k] (B : BigFppfSite.{u}) {X : Scheme.{u}} (hX : B.Contains X)
  (hk : B.Contains (Spec (.of k))) (f : B.obj hX ⟶ B.obj hk)
  [IsCurve k (B.inclusion.map f)] [GeometricallyIrreducible (B.inclusion.map f)]
  [Smooth (B.inclusion.map f)] [IsProjectiveVariety k (B.inclusion.map f)]
  (σ : Spec (.of k) ⟶ X) (hσ : σ ≫ B.inclusion.map f = 𝟙 (Spec (.of k)))

omit [GeometricallyIrreducible (B.inclusion.map f)] in
/-- The fibre rank of the class of an invertible module on `X_T`. -/
theorem fibreRank_toPicardFunctor (T : BigFppfOver B (Spec (.of k)) hk)
    (L : (baseChange B hX hk f T).Modules)
    (hL : Stacks.SheafOfModules.IsInvertible (baseChange B hX hk f T).presheaf
      (Stacks.RingedSpace.structureIsSheaf (baseChange B hX hk f T).toRingedSpace) L)
    (t : B.inclusion.obj T.left) (n : ℕ) :
    fibreRank B hX hk f σ hσ (isIso_baseChangeProj_c_of_isCurve B hX hk f σ hσ) T
        ((toPicardFunctor B hX hk f).app (op T) (Stacks.SheafOfModules.picardClass _ _ L hL)) t n =
      Module.finrank ((B.inclusion.obj T.left).residueField t)
        (fibreCohomology (pullback.snd (B.inclusion.map f) (B.inclusion.map T.hom)) L t n) := by
  rw [← toPicardFunctorHom_apply, fibreRank_toPicardFunctorHom, classFibreRank_picardClass]
  rfl

/-- The fibre Euler characteristic of the trivial point is `1 - g`. -/
theorem fibreEuler_zero (T : BigFppfOver B (Spec (.of k)) hk) (t : B.inclusion.obj T.left) :
    fibreEuler B hX hk f σ hσ (isIso_baseChangeProj_c_of_isCurve B hX hk f σ hσ) T 0 t =
      1 - genus (B.inclusion.map f) := by
  let Y := baseChange B hX hk f T
  let O : Y.Modules := SheafOfModules.unit Y.ringCatSheaf
  have hO : Stacks.SheafOfModules.IsInvertible Y.presheaf
      (Stacks.RingedSpace.structureIsSheaf Y.toRingedSpace) O :=
    Stacks.SheafOfModules.isInvertible_unit _ _
  have hrank : ∀ n, fibreRank B hX hk f σ hσ (isIso_baseChangeProj_c_of_isCurve B hX hk f σ hσ)
      T 0 t n = Module.finrank ((B.inclusion.obj T.left).residueField t)
        (fibreCohomology (pullback.snd (B.inclusion.map f) (B.inclusion.map T.hom)) O t n) := by
    intro n
    have h := fibreRank_toPicardFunctor B hX hk f σ hσ T O hO t n
    have h0 : (toPicardFunctor B hX hk f).app (op T)
        (Stacks.SheafOfModules.picardClass _ _ O hO) = 0 := by
      rw [← toPicardFunctorHom_apply]
      convert map_zero (toPicardFunctorHom B hX hk f T)
      exact Stacks.SheafOfModules.picardClass_zero _ _
    rwa [h0] at h
  obtain ⟨e0, e1⟩ := fibreCohomology_unit (B.inclusion.map f) (Over.mk (B.inclusion.map T.hom)) t
  unfold fibreEuler
  rw [hrank, hrank]
  erw [e0, e1]
  push_cast
  ring

/-- **The degree-`d` subfunctor of the Picard functor is a degree component**: the class of an
invertible module on `X_T` has fibre degree `d` everywhere exactly when every fibre has Euler
characteristic `d + 1 - g`. -/
theorem isDegreeComponent_degreeSubfunctor (d : ℤ) :
    IsDegreeComponent B hX hk f d
      (degreeSubfunctor B hX hk f σ hσ (isIso_baseChangeProj_c_of_isCurve B hX hk f σ hσ) d) := by
  intro T L hL
  change (∀ t, fibreDegree B hX hk f σ hσ _ T _ t = d) ↔ _
  refine forall_congr' fun t => ?_
  unfold fibreDegree
  rw [fibreEuler_zero]
  unfold fibreEuler
  rw [fibreRank_toPicardFunctor, fibreRank_toPicardFunctor]
  constructor <;> intro h <;> linarith

section Representable

variable [(picardFunctor B hX hk f).IsRepresentable]

/-- The inclusion `Pic^d_{X/k} ⟶ Pic_{X/k}` of the degree-`d` component is a monomorphism. -/
instance mono_picardDegreeComponentι (d : ℤ) :
    Mono (picardSchemeDegreeComponentι B hX hk f σ hσ d) := by
  have : Mono (B.inclusion.map (picardSchemeDegreeComponentι B hX hk f σ hσ d).left) := by
    rw [inclusion_map_picardSchemeDegreeComponentι]
    change Mono (Scheme.Opens.ι (picardDegreeLocus B hX hk f σ hσ d))
    infer_instance
  have : Mono (picardSchemeDegreeComponentι B hX hk f σ hσ d).left :=
    B.inclusion.mono_of_mono_map this
  exact Over.mono_of_mono_left _

omit [GeometricallyIrreducible (B.inclusion.map f)] in
/-- The morphism `T ⟶ Pic_{X/k}` corresponding to a section of the degree-`d` subfunctor over
`T` factors through the inclusion `Pic^d_{X/k} ⟶ Pic_{X/k}`. -/
theorem exists_comp_picardDegreeComponentι_of_mem (d : ℤ) {T : BigFppfOver B (Spec (.of k)) hk}
    (ξ : (degreeSubfunctor B hX hk f σ hσ (isIso_baseChangeProj_c_of_isCurve B hX hk f σ hσ)
      d).toFunctor.obj (op T)) :
    ∃ ψ : T ⟶ picardSchemeDegreeComponent B hX hk f σ hσ d,
      ψ ≫ picardSchemeDegreeComponentι B hX hk f σ hσ d = (picardHomEquiv B hX hk f).symm ξ.1 :=
  (exists_comp_picardSchemeDegreeComponentι_iff B hX hk f σ hσ _ d).2 (by
    rw [Equiv.apply_symm_apply]
    exact ξ.2)

/-- **`Pic^d_{X/k}` represents the degree-`d` subfunctor of the Picard functor.** -/
def degreeComponentRepresentableBy (d : ℤ) :
    (degreeSubfunctor B hX hk f σ hσ (isIso_baseChangeProj_c_of_isCurve B hX hk f σ hσ)
      d).toFunctor.RepresentableBy (picardSchemeDegreeComponent B hX hk f σ hσ d) where
  homEquiv {T} :=
    { toFun := fun ψ =>
        ⟨picardHomEquiv B hX hk f (ψ ≫ picardSchemeDegreeComponentι B hX hk f σ hσ d),
         (exists_comp_picardSchemeDegreeComponentι_iff B hX hk f σ hσ _ d).1 ⟨ψ, rfl⟩⟩
      invFun := fun ξ => (exists_comp_picardDegreeComponentι_of_mem B hX hk f σ hσ d ξ).choose
      left_inv := fun ψ => by
        rw [← cancel_mono (picardSchemeDegreeComponentι B hX hk f σ hσ d)]
        exact (exists_comp_picardDegreeComponentι_of_mem B hX hk f σ hσ d _).choose_spec.trans
          ((picardHomEquiv B hX hk f).symm_apply_apply _)
      right_inv := fun ξ => by
        apply Subtype.ext
        change picardHomEquiv B hX hk f (_ ≫ _) = ξ.1
        rw [(exists_comp_picardDegreeComponentι_of_mem B hX hk f σ hσ d ξ).choose_spec,
          Equiv.apply_symm_apply] }
  homEquiv_comp {T T'} a ψ := by
    apply Subtype.ext
    change picardHomEquiv B hX hk f ((a ≫ ψ) ≫ _) =
      (picardFunctor B hX hk f).map a.op (picardHomEquiv B hX hk f (ψ ≫ _))
    rw [Category.assoc]
    exact (picardFunctor B hX hk f).representableBy.homEquiv_comp _ _

variable {d : ℕ} (H : BigFppfOver B (Spec (.of k)) hk)
  (hH : Stacks.Hilbert.RepresentsHilbertFunctorOfRank (Over.mk (B.inclusion.map f))
    (Over.mk (B.inclusion.map H.hom)) d)

/-- **Stacks Project, Tag 0BA0, clause (4): `γ_d : Hilb^d_{X/k} ⟶ Pic^d_{X/k}`** for a smooth
projective geometrically irreducible curve with a rational point, into the degree component
`Stacks.PicardFunctor.picardSchemeDegreeComponent` of the Picard scheme. -/
def curveAbelMap : H ⟶ picardSchemeDegreeComponent B hX hk f σ hσ d :=
  abelMap B hX hk f (isDegreeComponent_degreeSubfunctor B hX hk f σ hσ d) H hH
    (degreeComponentRepresentableBy B hX hk f σ hσ d)

/-- The point of `Pic^d_{X/k}` that `γ_d` assigns to a degree-`d` family `D` on `X_T` is the
class of `𝒪(D)`. -/
theorem picardHomEquiv_comp_curveAbelMap {T : BigFppfOver B (Spec (.of k)) hk} (t : T ⟶ H) :
    picardHomEquiv B hX hk f (t ≫ curveAbelMap B hX hk f σ hσ H hH ≫
        picardSchemeDegreeComponentι B hX hk f σ hσ d) =
      (toPicardFunctor B hX hk f).app (op T)
        (hH.family (Stacks.PicardFunctor.testMap B hk t)).picardClass := by
  rw [← Category.assoc]
  exact congrArg Subtype.val (homEquiv_comp_abelMap B hX hk f
    (isDegreeComponent_degreeSubfunctor B hX hk f σ hσ d) H hH
    (degreeComponentRepresentableBy B hX hk f σ hσ d) t)

/-- **Stacks Project, Tag 0BA0, clause (5): `γ_d` is surjective for `d ≥ g`.** -/
theorem surjective_curveAbelMap (hdg : genus (B.inclusion.map f) ≤ d) :
    Surjective (B.inclusion.map (curveAbelMap B hX hk f σ hσ H hH).left) :=
  surjective_abelMap B hX hk f σ hσ (isDegreeComponent_degreeSubfunctor B hX hk f σ hσ d) H hH
    (degreeComponentRepresentableBy B hX hk f σ hσ d) hdg

end Representable

end Site

end Stacks.AbelMap

end
