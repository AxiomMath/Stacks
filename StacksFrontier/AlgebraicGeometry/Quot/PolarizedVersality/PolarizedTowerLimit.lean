module

public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackFormalEffectiveness
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedFormalEffective
public import StacksFrontier.Deformation.Artin.Versality.OpennessTower

/-!
# Square-zero systems of polarized families are effective

Let `(Rₙ)` be an inverse system of rings with surjective transition maps whose kernels have square
zero, with limit `R`, and let `Xₙ` be polarized families (Stacks 0D1M) over schemes identified with
`Spec Rₙ`, with morphisms `Xₙ ⟶ Xₙ₊₁` over the transition maps. By Stacks 0D4T
(`Stacks.PolarizedAlgebraization.exists_algebraization`) the system comes from a polarized family
over `Spec R`: for every scheme `T` identified with `Spec R` compatibly with the `Xₙ`, there is a
polarized family over `T` receiving compatible morphisms from the `Xₙ` over the given maps.

## Main results

* `AlgebraicGeometry.PolarizedVersality.Polarized.exists_cocone_of_squareZeroTower`: the limit
  family.
* `AlgebraicGeometry.PolarizedVersality.Polarized.isSquareZeroEffective_polarizedSliceProjection`:
  square-zero systems in `𝒫olarized` over a terminal base are effective.

## References

* [Stacks Project, Tag 0D4T](https://stacks.math.columbia.edu/tag/0D4T)
* [Stacks Project, Tag 0CXU](https://stacks.math.columbia.edu/tag/0CXU)
* [Stacks Project, Tag 0D4V](https://stacks.math.columbia.edu/tag/0D4V)
-/

@[expose] public noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite Deformation.Artin Stacks.Ample

namespace AlgebraicGeometry.PolarizedVersality.Polarized

variable {B : BigFppfSite.{u}}

/-- **The limit of a square-zero system of polarized families.** Let `R` be an inverse system of
rings with surjective transition maps whose kernels have square zero, `cR` a limit cone of `R`,
and `st n : X n ⟶ X (n + 1)` morphisms of polarized families, with the base of `X n` identified
with `Spec (R n)` compatibly with the transition maps. Given maps `a n` from the bases of the
`X n` to a scheme `T` identified with `Spec cR.pt` compatibly with the projections, there are a
polarized family `x` over `T` and morphisms `ι n : X n ⟶ x` over the `a n` with
`st n ≫ ι (n + 1) = ι n`. -/
theorem exists_cocone_of_squareZeroTower (R : ℕᵒᵖ ⥤ CommRingCat.{u})
    (hsurj : ∀ n : ℕ, Function.Surjective (R.map (homOfLE (Nat.le_succ n)).op))
    (hsq : ∀ n : ℕ, RingHom.ker (R.map (homOfLE (Nat.le_succ n)).op).hom ^ 2 = ⊥)
    (cR : Cone R) (hcR : IsLimit cR) (X : ℕ → PolarizedFamily B) (st : ∀ n, X n ⟶ X (n + 1))
    (T : B.Schemes) (a : ∀ n, (X n).base ⟶ T) (ha : ∀ n, (st n).baseMap ≫ a (n + 1) = a n)
    (e : ∀ n, B.inclusion.obj (X n).base ≅ Spec (R.obj (op n)))
    (eT : B.inclusion.obj T ≅ Spec cR.pt)
    (he : ∀ n, B.inclusion.map (st n).baseMap ≫ (e (n + 1)).hom =
      (e n).hom ≫ Spec.map (R.map (homOfLE (Nat.le_succ n)).op))
    (heT : ∀ n, B.inclusion.map (a n) ≫ eT.hom = (e n).hom ≫ Spec.map (cR.π.app (op n))) :
    ∃ (x : PolarizedFamily B) (hx : x.base = T) (ι : ∀ n, X n ⟶ x),
      (∀ n, st n ≫ ι (n + 1) = ι n) ∧ ∀ n, (ι n).baseMap ≫ eqToHom hx = a n := by
  classical
  have hnil : ∀ n : ℕ, RingHom.ker (R.map (homOfLE (Nat.le_succ n)).op).hom ≤
      nilradical (R.obj (op (n + 1))) := fun n z hz =>
    mem_nilradical.mpr ⟨2, Ideal.mem_bot.mp (by rw [← hsq n]; exact Ideal.pow_mem_pow hz 2)⟩
  let f : ∀ n, (X n).total ⟶ Spec (R.obj (op n)) := fun n => (X n).toBase ≫ (e n).hom
  have hpb : ∀ n, IsPullback (st n).totalMap (f n) (f (n + 1))
      (Spec.map (R.map (homOfLE (Nat.le_succ n)).op)) := fun n =>
    (st n).cartesian.of_iso (Iso.refl _) (Iso.refl _) (e n) (e (n + 1)) (by simp) (by simp [f])
      (by simp [f]) (he n)
  have hproperT : ∀ n, IsProper (f n) := fun n => by
    have : IsProper (X n).toBase := (X n).proper
    exact inferInstanceAs (IsProper ((X n).toBase ≫ (e n).hom))
  have hflatT : ∀ n, Flat (f n) := fun n => by
    have : Flat (X n).toBase := (X n).flat
    exact inferInstanceAs (Flat ((X n).toBase ≫ (e n).hom))
  have hfpT : ∀ n, FinitePresentation (f n) := fun n => by
    obtain ⟨_, _, _⟩ := (X n).finitePresentation
    exact ⟨inferInstanceAs (LocallyOfFinitePresentation ((X n).toBase ≫ (e n).hom)),
      inferInstanceAs (QuasiCompact ((X n).toBase ≫ (e n).hom)),
      inferInstanceAs (QuasiSeparated ((X n).toBase ≫ (e n).hom))⟩
  have hample : let : IsInvertibleModule (X 0).total (X 0).lineBundle := (X 0).invertible
      IsAmple (X 0).total (X 0).lineBundle := by
    let : IsInvertibleModule (X 0).total (X 0).lineBundle := (X 0).invertible
    have : IsAffine (B.inclusion.obj (X 0).base) := IsAffine.of_isIso (e 0).hom
    exact (Stacks.RelativeAmpleAffineBase.isRelativelyAmple_iff_isAmple (X 0).toBase _).mp
      (X 0).relativelyAmple
  obtain ⟨Y, gY, ℒ, hℒ, j, hj, e', hproper, hflat, hfp, hampleY, hpbY, hiso, hcompat⟩ :=
    Stacks.PolarizedAlgebraization.exists_algebraization R hsurj hnil
      (fun n => (X n).total) f (fun n => (st n).totalMap) hpb (fun n => (X n).lineBundle)
      (hL := fun n => (X n).invertible) (fun n => (st n).lineBundleIso)
      (hproper := hproperT) (hflat := hflatT) hfpT hample
  let ψ : cR.pt ≅ limit R := hcR.conePointUniqueUpToIso (limit.isLimit R)
  have hψ : ∀ n, ψ.hom ≫ limit.π R (op n) = cR.π.app (op n) := fun n =>
    hcR.conePointUniqueUpToIso_hom_comp (limit.isLimit R) (op n)
  let E : Spec (limit R) ≅ B.inclusion.obj T := asIso (Spec.map ψ.hom) ≪≫ eT.symm
  have : IsAffine (B.inclusion.obj T) := IsAffine.of_isIso eT.hom
  have := hproper
  have := hflat
  have hfpx : FinitePresentation (gY ≫ E.hom) := by
    obtain ⟨_, _, _⟩ := hfp
    exact ⟨inferInstance, inferInstance, inferInstance⟩
  let x : PolarizedFamily B :=
    { base := T
      total := Y
      toBase := gY ≫ E.hom
      proper := inferInstance
      flat := inferInstance
      finitePresentation := hfpx
      lineBundle := ℒ
      invertible := hℒ
      relativelyAmple :=
        (Stacks.RelativeAmpleAffineBase.isRelativelyAmple_iff_isAmple (gY ≫ E.hom) ℒ).mpr
          hampleY }
  have hcart : ∀ n, IsPullback (j n) (X n).toBase (gY ≫ E.hom) (B.inclusion.map (a n)) := by
    intro n
    refine (hpbY n).of_iso (Iso.refl _) (Iso.refl _) (e n).symm E (by simp) (by simp [f])
      (by simp) ?_
    change Spec.map (limit.π R (op n)) ≫ Spec.map ψ.hom ≫ eT.inv =
      (e n).inv ≫ B.inclusion.map (a n)
    rw [← Spec.map_comp_assoc, hψ, Iso.eq_inv_comp, ← Category.assoc, ← heT n, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  let ι : ∀ n, X n ⟶ x := fun n =>
    { baseMap := a n
      totalMap := j n
      cartesian := hcart n
      lineBundleIso := @asIso _ _ _ _ (e' n) (hiso n) }
  refine ⟨x, rfl, ι, fun n => ?_, fun n => Category.comp_id _⟩
  refine PolarizedFamily.Hom.ext ((PolarizedFamily.comp_baseMap _ _).trans (ha n))
    ((PolarizedFamily.comp_totalMap _ _).trans (hj n)) ?_
  refine PolarizedFormal.heq_of_pullbackCongr_hom_app_comp (hj n) _ _ ?_
  change (Scheme.Modules.pullbackCongr (hj n)).hom.app ℒ ≫ e' n =
    (Scheme.Modules.pullbackComp _ _).inv.app ℒ ≫
      (Scheme.Modules.pullback (st n).totalMap).map (e' (n + 1)) ≫ (st n).lineBundleIso.hom
  rw [← hcompat n, ← Category.assoc, ← NatTrans.comp_app, Iso.inv_hom_id, NatTrans.id_app,
    Category.id_comp]

variable (B) in
/-- **Square-zero systems in `𝒫olarized` are effective** (condition (4) of Stacks 0CXU), over a
terminal base scheme, by Stacks 0D4T. -/
theorem isSquareZeroEffective_polarizedSliceProjection {S : Scheme.{u}} (hS : B.Contains S)
    (hT : IsTerminal (B.obj hS)) :
    IsSquareZeroEffective B S hS (polarizedSliceProjection B hS hT)
      (polarizedProjection_isFiberedInGroupoids_unconditional.sliceAtTerminal hT) := by
  rintro Λ _ _ _ R cR hcR hsurj hsq ξ ⟨⟨T, ⟨⟨⟩⟩, hTm⟩, cι⟩ e eLimit he heLimit -
  have := Space.ComplexesSituation.preservesLimitsOfShape_forget₂_commAlgCat Λ
  obtain ⟨x, hx, ι, hι, hιa⟩ := exists_cocone_of_squareZeroTower (R ⋙ forget₂ _ _)
    (fun _ => hsurj _) (fun _ => hsq _) ((forget₂ _ _).mapCone cR) (isLimitOfPreserves _ hcR)
    ξ.obj (fun n => ξ.map (homOfLE (Nat.le_succ n))) T (fun n => (cι.app n).left)
    (fun n => congrArg CommaMorphism.left
      (Cocone.w (⟨_, cι⟩ : Cocone (ξ ⋙ polarizedSliceProjection B hS hT))
        (homOfLE (Nat.le_succ n))))
    e eLimit
    (fun n => he (homOfLE (Nat.le_succ n))) heLimit
  subst hx
  obtain rfl : hTm = hT.from _ := hT.hom_ext _ _
  refine ⟨⟨x, NatTrans.ofSequence ι fun n => (hι n).trans (Category.comp_id _).symm⟩, ?_⟩
  refine Space.ComplexesSituation.coconeEq_of_pt_eq rfl fun n => Over.OverMorphism.ext ?_
  have h := hιa n
  rw [eqToHom_refl, Category.comp_id] at h
  exact (congrArg CommaMorphism.left (Category.comp_id _ : _ ≫ 𝟙 _ = _)).trans h

end AlgebraicGeometry.PolarizedVersality.Polarized

end
