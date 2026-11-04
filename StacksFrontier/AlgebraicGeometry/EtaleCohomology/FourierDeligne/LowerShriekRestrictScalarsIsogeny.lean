module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.PadicIntegerRingLevelIsogeny
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.LowerShriekHomologyRestrictScalars
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.EtaleModulesCtfCentralIdempotent

/-!
# Transporting a level isogeny through `R¹f_!`, inverse image and restriction of scalars

Let `π : Λ₀ → Λ` be a homomorphism of commutative rings, `f : X → Y` with a compactification,
`j_V : V → Y`, `L` a sheaf of `Λ`-modules on `X` and `H ≅ R¹f_! L` on `Y`. An `ℓᵃ`-isogeny
`w, w'` of sheaves of `Λ₀`-modules between `res_π L` and a sheaf `W` gives an `ℓᵃ`-isogeny between
`res_π (j_V⁻¹ H)` and `j_V⁻¹ R¹f_! W`: through `res_π ∘ j_V⁻¹ = j_V⁻¹ ∘ res_π`
(`Stacks.EtaleCohomology.etaleModuleInverseImageRestrictScalars`) and
`res_π ∘ R¹f_! = R¹f_! ∘ res_π` (`Stacks.EtaleCohomology.lowerShriekHomologyRestrictScalarsIso`).
Multiplication by `c ∈ Λ` on `j_V⁻¹ H` corresponds to `j_V⁻¹ R¹f_!(s)` for every endomorphism `s`
of `W` which `w, w'` carry to multiplication by `c`
(`Stacks.EtaleCohomology.exists_isogeny_restrictScalars_inverseImage_lowerShriekHomology`). This
is the Fourier side of the level isogeny in piece L6 of
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH).

## Main results

* `Stacks.EtaleCohomology.etaleModuleInverseImage_map_etaleModuleSMul`.
* `Stacks.EtaleCohomology.lowerShriekHomology_map_nsmul_id`.
* `Stacks.EtaleCohomology.exists_isogeny_restrictScalars_inverseImage_lowerShriekHomology`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

section Comm

variable {C D : Type*} [Category C] [Category D] {A B B' : C}

/-- Commuting with two isomorphisms, one after the other. -/
theorem comm_iso_trans {sA : A ⟶ A} {sB : B ⟶ B} {sC : B' ⟶ B'} (e₁ : A ≅ B) (e₂ : B ≅ B')
    (h₁ : sA ≫ e₁.hom = e₁.hom ≫ sB) (h₂ : sB ≫ e₂.hom = e₂.hom ≫ sC) :
    sA ≫ (e₁ ≪≫ e₂).hom = (e₁ ≪≫ e₂).hom ≫ sC := by
  rw [Iso.trans_hom, reassoc_of% h₁, h₂, Category.assoc]

/-- Commuting with the inverse of an isomorphism. -/
theorem comm_iso_symm {sA : A ⟶ A} {sB : B ⟶ B} (e : A ≅ B) (h : sA ≫ e.hom = e.hom ≫ sB) :
    sB ≫ e.symm.hom = e.symm.hom ≫ sA := by
  rw [Iso.symm_hom, Iso.comp_inv_eq, Category.assoc, h, Iso.inv_hom_id_assoc]

/-- Commuting with the image of an isomorphism under a functor. -/
theorem comm_mapIso (F : C ⥤ D) {sA : A ⟶ A} {sB : B ⟶ B} (e : A ≅ B)
    (h : sA ≫ e.hom = e.hom ≫ sB) :
    F.map sA ≫ (F.mapIso e).hom = (F.mapIso e).hom ≫ F.map sB := by
  rw [Functor.mapIso_hom, ← F.map_comp, h, F.map_comp]

end Comm

section SMul

variable {A : Type} [CommRing A]

/-- **Inverse image commutes with multiplication by a scalar**: it is left adjoint to the direct
image, which does. -/
theorem etaleModuleInverseImage_map_etaleModuleSMul {X Y : Scheme.{u}} (f : X ⟶ Y) (a : A)
    (G : EtaleModules.{u, 0} A Y) :
    (etaleModuleInverseImage.{u, 0} A f).map ((etaleModuleSMul Y a).app G) =
      (etaleModuleSMul X a).app ((etaleModuleInverseImage.{u, 0} A f).obj G) :=
  CategoryTheory.map_app_of_adjunction (etaleModuleInverseImageAdj.{u, 0} A f)
    (etaleModuleSMul Y a) (etaleModuleSMul X a)
    (etaleModuleDirectImage_map_etaleModuleSMul f a) G

/-- Multiplication by `k ∈ ℕ` is multiplication by the scalar `k`. -/
theorem nsmul_id_eq_etaleModuleSMul (Z : Scheme.{u}) (k : ℕ) (G : EtaleModules.{u, 0} A Z) :
    k • 𝟙 G = (etaleModuleSMul Z (k : A)).app G := by
  rw [etaleModuleSMul_app_eq_smul_id, Nat.cast_smul_eq_nsmul]

/-- **`R^q f_!` preserves multiplication by `k ∈ ℕ`.** -/
theorem lowerShriekHomology_map_nsmul_id {X Y : Scheme.{u}} (f : X ⟶ Y)
    (j : CompactificationOf (Over.mk f)) (q : ℕ) (k : ℕ) (G : EtaleModules.{u, 0} A X) :
    (lowerShriekHomology A f j q).map (k • 𝟙 G) = k • 𝟙 _ := by
  rw [nsmul_id_eq_etaleModuleSMul, nsmul_id_eq_etaleModuleSMul,
    lowerShriekHomology_map_etaleModuleSMul]

end SMul

section Transport

variable {Λ₀ Λ : Type} [CommRing Λ₀] [CommRing Λ] (π : Λ₀ →+* Λ) {X Y V : Scheme.{u}}
  (f : X ⟶ Y) (jf : CompactificationOf (Over.mk f)) (jV : V ⟶ Y)

/-- Multiplication by a scalar commutes with an isomorphism onto `R^q f_! L`, as
`R^q f_!` of the multiplication on `L`. -/
theorem etaleModuleSMul_comp_iso_lowerShriekHomology (q : ℕ) {H : EtaleModules.{u, 0} Λ Y}
    {L : EtaleModules.{u, 0} Λ X} (β : H ≅ (lowerShriekHomology Λ f jf q).obj L) (c : Λ) :
    (etaleModuleSMul Y c).app H ≫ β.hom =
      β.hom ≫ (lowerShriekHomology Λ f jf q).map ((etaleModuleSMul X c).app L) :=
  ((etaleModuleSMul Y c).naturality β.hom).symm.trans
    (congrArg (β.hom ≫ ·) (lowerShriekHomology_map_etaleModuleSMul f jf q c L).symm)

/-- The inverse of `Stacks.EtaleCohomology.lowerShriekHomologyRestrictScalarsIso` is natural. -/
theorem lowerShriekHomologyRestrictScalarsIso_inv_comm (q : ℕ) {L : EtaleModules.{u, 0} Λ X}
    (φ : L ⟶ L) :
    (etaleModuleRestrictScalars π Y).map ((lowerShriekHomology Λ f jf q).map φ) ≫
        ((lowerShriekHomologyRestrictScalarsIso π f jf q).app L).symm.hom =
      ((lowerShriekHomologyRestrictScalarsIso π f jf q).app L).symm.hom ≫
        (lowerShriekHomology Λ₀ f jf q).map ((etaleModuleRestrictScalars π X).map φ) :=
  (lowerShriekHomologyRestrictScalarsIso π f jf q).inv.naturality φ

attribute [-instance] CategoryTheory.catToReflQuiver in
/-- **Transport of a level isogeny through `R^q f_!`, inverse image and restriction of scalars**:
an `k`-isogeny `w, w'` of sheaves of `Λ₀`-modules between `res_π L` and `W` gives a `k`-isogeny
between `res_π (j_V⁻¹ H)` and `j_V⁻¹ R^q f_! W` for `H ≅ R^q f_! L`, carrying multiplication by
`c ∈ Λ` to `j_V⁻¹ R^q f_!(s)` for every endomorphism `s` of `W` which `w, w'` carry to
multiplication by `c`. -/
theorem exists_isogeny_restrictScalars_inverseImage_lowerShriekHomology
    (q : ℕ) {H : EtaleModules.{u, 0} Λ Y} {L : EtaleModules.{u, 0} Λ X}
    (β : H ≅ (lowerShriekHomology Λ f jf q).obj L) {W : EtaleModules.{u, 0} Λ₀ X}
    (w : (etaleModuleRestrictScalars π X).obj L ⟶ W)
    (w' : W ⟶ (etaleModuleRestrictScalars π X).obj L) (k : ℕ) (hww' : w ≫ w' = k • 𝟙 _)
    (hw'w : w' ≫ w = k • 𝟙 _) :
    ∃ (h : (etaleModuleRestrictScalars π V).obj ((etaleModuleInverseImage.{u, 0} Λ jV).obj H) ⟶
        (etaleModuleInverseImage.{u, 0} Λ₀ jV).obj ((lowerShriekHomology Λ₀ f jf q).obj W))
      (h' : (etaleModuleInverseImage.{u, 0} Λ₀ jV).obj ((lowerShriekHomology Λ₀ f jf q).obj W) ⟶
        (etaleModuleRestrictScalars π V).obj ((etaleModuleInverseImage.{u, 0} Λ jV).obj H)),
      h ≫ h' = k • 𝟙 _ ∧ h' ≫ h = k • 𝟙 _ ∧
      ∀ (c : Λ) (s : W ⟶ W),
        (etaleModuleRestrictScalars π X).map ((etaleModuleSMul X c).app L) ≫ w = w ≫ s →
        s ≫ w' = w' ≫ (etaleModuleRestrictScalars π X).map ((etaleModuleSMul X c).app L) →
        (etaleModuleRestrictScalars π V).map ((etaleModuleSMul V c).app
            ((etaleModuleInverseImage.{u, 0} Λ jV).obj H)) ≫ h =
          h ≫ (etaleModuleInverseImage.{u, 0} Λ₀ jV).map ((lowerShriekHomology Λ₀ f jf q).map s) ∧
        (etaleModuleInverseImage.{u, 0} Λ₀ jV).map ((lowerShriekHomology Λ₀ f jf q).map s) ≫ h' =
          h' ≫ (etaleModuleRestrictScalars π V).map ((etaleModuleSMul V c).app
            ((etaleModuleInverseImage.{u, 0} Λ jV).obj H)) := by
  let R := lowerShriekHomology Λ₀ f jf q ⋙ etaleModuleInverseImage.{u, 0} Λ₀ jV
  let i := ((etaleModuleInverseImageRestrictScalars π jV).app H).symm ≪≫
    (etaleModuleInverseImage.{u, 0} Λ₀ jV).mapIso ((etaleModuleRestrictScalars π Y).mapIso β ≪≫
      ((lowerShriekHomologyRestrictScalarsIso π f jf q).app L).symm)
  have hR : ∀ G : EtaleModules.{u, 0} Λ₀ X, R.map (k • 𝟙 G) = k • 𝟙 (R.obj G) := fun G => by
    show (etaleModuleInverseImage.{u, 0} Λ₀ jV).map
      ((lowerShriekHomology Λ₀ f jf q).map (k • 𝟙 G)) = _
    rw [lowerShriekHomology_map_nsmul_id, CategoryTheory.Functor.map_nsmul,
      CategoryTheory.Functor.map_id]
    rfl
  have hiso := isogeny_conj_map R i w w' (Iso.refl _) k
    (by rw [← CategoryTheory.Functor.map_comp, hww', hR])
    (by rw [← CategoryTheory.Functor.map_comp, hw'w, hR])
  refine ⟨_, _, hiso.1, hiso.2, fun c s hs hs' => ?_⟩
  -- the scalar `c` commutes with each piece of `i`
  have hα := (etaleModuleInverseImageRestrictScalars π jV).inv.naturality
    ((etaleModuleSMul Y c).app H)
  have h₁ : (etaleModuleRestrictScalars π V).map ((etaleModuleSMul V c).app
        ((etaleModuleInverseImage.{u, 0} Λ jV).obj H)) ≫
        ((etaleModuleInverseImageRestrictScalars π jV).app H).symm.hom =
      ((etaleModuleInverseImageRestrictScalars π jV).app H).symm.hom ≫
        (etaleModuleInverseImage.{u, 0} Λ₀ jV).map
          ((etaleModuleRestrictScalars π Y).map ((etaleModuleSMul Y c).app H)) := by
    rw [← etaleModuleInverseImage_map_etaleModuleSMul]
    exact hα
  have h₂ := etaleModuleSMul_comp_iso_lowerShriekHomology f jf q β c
  have h₃ := lowerShriekHomologyRestrictScalarsIso_inv_comm π f jf q ((etaleModuleSMul X c).app L)
  have hi := comm_iso_trans _ _ h₁ (comm_mapIso (etaleModuleInverseImage.{u, 0} Λ₀ jV) _
    (comm_iso_trans _ _ (comm_mapIso (etaleModuleRestrictScalars π Y) β h₂) h₃))
  have hj : R.map s ≫ (Iso.refl (R.obj W)).inv = (Iso.refl (R.obj W)).inv ≫ R.map s := by
    rw [Iso.refl_inv, Category.comp_id, Category.id_comp]
  exact ⟨comm_conj_map R i w (Iso.refl _) hi hs hj, comm_conj_map' R i w' (Iso.refl _) hi hs' hj⟩

end Transport

end Stacks.EtaleCohomology

end
