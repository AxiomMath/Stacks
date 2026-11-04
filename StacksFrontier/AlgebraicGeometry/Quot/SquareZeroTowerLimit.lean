module

public import StacksFrontier.AlgebraicGeometry.Quot.SquareZeroTowerExtensions

/-!
# The limit of the tower of structure sheaves of a square-zero tower

In the situation of `AlgebraicGeometry.ProperFlatFibre.towerSpace`, the body of the proof of
[Stacks Project, Tag 0D3X] sets `𝒜 = lim 𝒪_{Xₙ}` on the small étale site of `X₁`. This file
forms that limit of the tower `Aₙ = aₙ⁻¹𝒪_{Xₙ}`
(`AlgebraicGeometry.ProperFlatFibre.towerRingSystem`) together with its reduction `𝒜 ⟶ 𝒪_{X₀}`,
and shows that the kernel of the reduction has square zero on every object.

## Main definitions

* `AlgebraicGeometry.ProperFlatFibre.towerRingLimit`: `𝒜 = lim Aₙ`.
* `AlgebraicGeometry.ProperFlatFibre.towerRingLimitReduction`: its reduction `𝒜 ⟶ 𝒪_{X₀}`.

## Main results

* `AlgebraicGeometry.ProperFlatFibre.towerRingReduction_squareZero`: each `Aₙ ⟶ 𝒪_{X₀}` has
  square-zero kernel.
* `AlgebraicGeometry.ProperFlatFibre.towerRingLimitReduction_squareZero`: so does `𝒜 ⟶ 𝒪_{X₀}`.

## References

* [Stacks Project, Tag 0D3X](https://stacks.math.columbia.edu/tag/0D3X)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite

universe u

namespace CategoryTheory.Sheaf

variable {C : Type*} [Category C] {J : GrothendieckTopology C}
  [HasLimitsOfShape ℕᵒᵖ (Sheaf J CommRingCat.{u})]

/-- **The kernel of the reduction of a limit of square-zero thickenings has square zero.** Let
`ρ : F ⟶ const 𝒪` be a cone of maps of sheaves of rings out of an inverse system `F` indexed by
`ℕᵒᵖ`, each `ρₙ` with square-zero kernel on every object. Then on every object the kernel of the
induced map `lim F ⟶ 𝒪` has square zero: sections of `lim F` are compatible families. -/
theorem ker_limit_reduction_sq_eq_bot (F : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{u})
    (O : Sheaf J CommRingCat.{u}) (ρ : F ⟶ (Functor.const _).obj O)
    (hρ : ∀ (n : ℕᵒᵖ) (U : Cᵒᵖ), RingHom.ker ((ρ.app n).hom.app U).hom ^ 2 = ⊥) (U : Cᵒᵖ) :
    RingHom.ker ((limit.π F (op 0) ≫ ρ.app (op 0)).hom.app U).hom ^ 2 = ⊥ := by
  have hl : IsLimit (((evaluation Cᵒᵖ CommRingCat.{u}).obj U).mapCone
      ((sheafToPresheaf J CommRingCat.{u}).mapCone (limit.cone F))) :=
    isLimitOfPreserves _ (isLimitOfPreserves _ (limit.isLimit F))
  refine le_bot_iff.mp ?_
  rw [pow_two, Submodule.mul_le]
  intro a ha b hb
  rw [Ideal.mem_bot]
  refine Concrete.isLimit_ext ((F ⋙ sheafToPresheaf J CommRingCat.{u}) ⋙
    (evaluation Cᵒᵖ CommRingCat.{u}).obj U) hl (a * b) 0 fun n => ?_
  have hmem : ∀ c, c ∈ RingHom.ker ((limit.π F (op 0) ≫ ρ.app (op 0)).hom.app U).hom →
      ((limit.π F n).hom.app U) c ∈ RingHom.ker ((ρ.app n).hom.app U).hom := by
    intro c hc
    rw [RingHom.mem_ker] at hc ⊢
    have h1 : limit.π F n ≫ ρ.app n = limit.π F (op 0) ≫ ρ.app (op 0) := by
      rw [← limit.w F (homOfLE (Nat.zero_le n.unop)).op, Category.assoc, ρ.naturality]
      simp
    rw [← hc]
    exact congrArg (fun k : limit F ⟶ O => k.hom.app U c) h1
  have h := Ideal.mul_mem_mul (hmem a ha) (hmem b hb)
  rw [← pow_two, hρ, Ideal.mem_bot, ← map_mul] at h
  exact h.trans (map_zero _).symm

omit [HasLimitsOfShape ℕᵒᵖ (Sheaf J CommRingCat)] in
/-- **Square-zero kernels transport along isomorphisms over the target.** If `g : A ≅ E` carries
`r' : E ⟶ 𝒪` to `r : A ⟶ 𝒪` and `r'` has square-zero kernel on `U`, so has `r`. -/
theorem ker_sq_eq_bot_of_iso {A E O : Sheaf J CommRingCat.{u}} (g : A ≅ E) {r : A ⟶ O}
    {r' : E ⟶ O} (h : g.hom ≫ r' = r) (U : Cᵒᵖ)
    (hE : RingHom.ker (r'.hom.app U).hom ^ 2 = ⊥) : RingHom.ker (r.hom.app U).hom ^ 2 = ⊥ := by
  subst h
  refine le_bot_iff.mp ?_
  rw [pow_two, Submodule.mul_le]
  intro a ha b hb
  rw [Ideal.mem_bot]
  have hmem : ∀ c, c ∈ RingHom.ker ((g.hom ≫ r').hom.app U).hom →
      g.hom.hom.app U c ∈ RingHom.ker (r'.hom.app U).hom := fun c hc => hc
  have hx := Ideal.mul_mem_mul (hmem a ha) (hmem b hb)
  rw [← pow_two, hE, Ideal.mem_bot, ← map_mul] at hx
  have hinv : g.inv.hom.app U (g.hom.hom.app U (a * b)) = a * b :=
    congrArg (fun k : A ⟶ A => k.hom.app U (a * b)) g.hom_inv_id
  rw [← hinv, hx, map_zero]

end CategoryTheory.Sheaf

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

include hsurj hsq he in
/-- **Each reduction `Aₙ ⟶ 𝒪_{X₀}` has square-zero kernel**: it is the reduction of the extension
`0 → 𝒪_{X₀} ⊗ Iₙ → 𝒪_{Xₙ} → 𝒪_{X₀} → 0` (`towerExtension`). -/
theorem towerRingReduction_squareZero (n : ℕ)
    (U : (Space.SmallEtale B S hS (towerSpace ξ 0).1)ᵒᵖ) :
    RingHom.ker (((towerRingReduction ξ).app (op n)).hom.app U).hom ^ 2 = ⊥ :=
  Sheaf.ker_sq_eq_bot_of_iso (towerRingSystemExtensionIso ξ hsurj hsq e he n (𝟙 _))
    (towerRingSystemExtensionIso_hom_comp_reduction ξ hsurj hsq e he n (𝟙 _)) U
    ((towerExtension ξ hsurj hsq e he n (𝟙 _)).squareZero U)

/-- **`𝒜 = lim Aₙ`**, the limit of the tower of structure sheaves on the small étale site of
`X₀`. -/
abbrev towerRingLimit :
    Sheaf (Space.SmallEtale.topology B S hS (towerSpace ξ 0).1) CommRingCat.{u} :=
  limit (towerRingSystem ξ)

/-- **The reduction `𝒜 ⟶ 𝒪_{X₀}`**, the projection to `A₀` followed by `a₀^♯`. -/
abbrev towerRingLimitReduction :
    towerRingLimit ξ ⟶ (Space.smallEtaleRingedTopos B S hS (towerSpace ξ 0)).O :=
  limit.π (towerRingSystem ξ) (op 0) ≫ (towerRingReduction ξ).app (op 0)

include hsurj hsq he in
/-- **The kernel of `𝒜 ⟶ 𝒪_{X₀}` has square zero.** -/
theorem towerRingLimitReduction_squareZero
    (U : (Space.SmallEtale B S hS (towerSpace ξ 0).1)ᵒᵖ) :
    RingHom.ker ((towerRingLimitReduction ξ).hom.app U).hom ^ 2 = ⊥ :=
  Sheaf.ker_limit_reduction_sq_eq_bot _ _ (towerRingReduction ξ)
    (fun n => towerRingReduction_squareZero ξ hsurj hsq e he n.unop) U

end AlgebraicGeometry.ProperFlatFibre

end
