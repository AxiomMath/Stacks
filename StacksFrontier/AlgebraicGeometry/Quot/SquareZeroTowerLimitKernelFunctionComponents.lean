module

public import StacksFrontier.AlgebraicGeometry.Quot.SquareZeroTowerLimitComparisonSections

/-!
# The components of the functions `c_m` on `Y = Spec(lim Rₙ)`

In the situation of `AlgebraicGeometry.ProperFlatFibre.towerProblem`, an element `m` of
`lim Iₙ` is the function `c_m ∈ Ker(Γ(Y) → Γ(Y₀))`
(`AlgebraicGeometry.ProperFlatFibre.towerLimitKernelFunction`). Its pullback along `Yₙ ⟶ Y` is the
`n`-th component `mₙ ∈ Iₙ ≅ Ker(Γ(Yₙ) → Γ(Y₀))`. This is the comparison of functions in the proof
of [Stacks Project, Tag 0D3X].

## Main results

* `AlgebraicGeometry.ProperFlatFibre.towerLimitΓIso_hom_comp_π`
* `AlgebraicGeometry.ProperFlatFibre.Γ_map_towerLimitKernelFunction`

## References

* [Stacks Project, Tag 0D3X](https://stacks.math.columbia.edu/tag/0D3X)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.ProperFlatFibre

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (ξ : ℕ ⥤ CartesianProperFlatSpaces B S hS)
  {Λ : Type u} [CommRing Λ] {R : ℕᵒᵖ ⥤ CommAlgCat.{u} Λ}
  (hsurj : ∀ {i j : ℕᵒᵖ} (f : i ⟶ j), Function.Surjective (R.map f).hom)
  (hsq : ∀ {i j : ℕᵒᵖ} (f : i ⟶ j), RingHom.ker (R.map f).hom.toRingHom ^ 2 = ⊥)
  (e : ∀ n : ℕ, (BigFppfOver.toScheme B S hS).obj (towerBase ξ n) ≅
    Spec (.of (R.obj (.op n))))
  (he : ∀ {i j : ℕ} (f : i ⟶ j),
    (BigFppfOver.toScheme B S hS).map ((ξ ⋙ cartesianProperFlatProjection B S hS).map f) ≫
      (e j).hom = (e i).hom ≫ Scheme.Spec.map (CommRingCat.ofHom (R.map f.op).hom.toRingHom).op)
  (cR : Cone R) (hcR : IsLimit cR) (c : Cocone (ξ ⋙ cartesianProperFlatProjection B S hS))
  (eLimit : (BigFppfOver.toScheme B S hS).obj c.pt ≅ Spec (.of cR.pt))
  (hc : ∀ n : ℕ, (BigFppfOver.toScheme B S hS).map (c.ι.app n) ≫ eLimit.hom =
    (e n).hom ≫ Scheme.Spec.map (CommRingCat.ofHom (cR.π.app (.op n)).hom.toRingHom).op)

include hc in
/-- Pullback of functions along `Yₙ ⟶ Y` is the projection `lim Rₙ ⟶ Rₙ` under `Γ(Y) ≅ lim Rₙ`,
`Γ(Yₙ) ≅ Rₙ`. -/
theorem towerLimitΓIso_hom_comp_π (n : ℕ) :
    (towerLimitΓIso ξ cR c eLimit).hom ≫ CommRingCat.ofHom (cR.π.app (op n)).hom.toRingHom =
      Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map (c.ι.app n)).op ≫
        (towerBaseΓIso ξ e n).hom := by
  have hf : (BigFppfOver.toScheme B S hS).map (c.ι.app n) =
      (e n).hom ≫ Spec.map (CommRingCat.ofHom (cR.π.app (op n)).hom.toRingHom) ≫
        eLimit.inv := by
    rw [← Category.assoc]
    exact (Iso.eq_comp_inv _).2 (hc n)
  have hc' : (e n).hom.appTop ≫ (e n).inv.appTop = 𝟙 _ := by
    rw [← Scheme.Hom.comp_appTop, Iso.inv_hom_id]
    rfl
  change eLimit.inv.appTop ≫ (Scheme.ΓSpecIso _).hom ≫ _ =
    ((BigFppfOver.toScheme B S hS).map (c.ι.app n)).appTop ≫ (e n).inv.appTop ≫
      (Scheme.ΓSpecIso _).hom
  rw [hf, Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop]
  simp only [Category.assoc]
  rw [reassoc_of% hc', Scheme.ΓSpecIso_naturality]
  rfl

include hc in
/-- `AlgebraicGeometry.ProperFlatFibre.towerLimitΓIso_hom_comp_π` on elements: the pullback along
`Yₙ ⟶ Y` of the function of `Y` given by `x ∈ lim Rₙ` is the function of `Yₙ` given by `xₙ`. -/
theorem Γ_map_towerLimitΓIso_inv_apply (n : ℕ) (x : cR.pt) :
    (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map (c.ι.app n)).op).hom
        ((towerLimitΓIso ξ cR c eLimit).inv.hom x) =
      (towerBaseΓIso ξ e n).inv.hom ((cR.π.app (op n)).hom x) := by
  have h := congrArg (fun φ => ((towerLimitΓIso ξ cR c eLimit).inv ≫ φ ≫
    (towerBaseΓIso ξ e n).inv).hom x) (towerLimitΓIso_hom_comp_π ξ e cR c eLimit hc n)
  simp only [Iso.inv_hom_id_assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id] at h
  exact h.symm

include hc in
/-- **The `n`-th component of `c_m`**: the pullback along `Yₙ ⟶ Y` of the function
`c_m ∈ Ker(Γ(Y) → Γ(Y₀))` of `m ∈ lim Iₙ` is the `n`-th component `mₙ`, read in
`Ker(Γ(Yₙ) → Γ(Y₀))` (`AlgebraicGeometry.ProperFlatFibre.towerBaseKernelSystemObjIso`). -/
theorem Γ_map_towerLimitKernelFunction (n : ℕ)
    (m : ↑(limit (towerBaseKernelSystem ξ hsurj hsq e))) :
    (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map (c.ι.app n)).op).hom
        (towerLimitKernelFunction ξ hsurj hsq e cR hcR c eLimit hc m).1 =
      ((towerBaseKernelSystemObjIso ξ hsurj hsq e he n).hom
        (limit.π (towerBaseKernelSystem ξ hsurj hsq e) (op n) m)).1 := by
  have h3 := ConcreteCategory.congr_hom ((CommAlgCat.isLimitTowerKernelCone hsurj hsq cR
      hcR).conePointUniqueUpToIso_inv_comp (limit.isLimit _) (op n))
    ((preservesLimitIso (ModuleCat.restrictScalars.{u} (towerBaseΓIso ξ e 0).hom.hom)
      (CommAlgCat.towerKernelSystem R hsurj hsq)).inv.hom m)
  have h4 := ConcreteCategory.congr_hom (preservesLimitIso_inv_π
      (ModuleCat.restrictScalars.{u} (towerBaseΓIso ξ e 0).hom.hom)
      (CommAlgCat.towerKernelSystem R hsurj hsq) (op n)) m
  refine (Γ_map_towerLimitΓIso_inv_apply ξ e cR c eLimit hc n _).trans ?_
  exact congrArg (towerBaseΓIso ξ e n).inv.hom ((congrArg Subtype.val h3).trans
    (congrArg Subtype.val h4))

end AlgebraicGeometry.ProperFlatFibre

end
