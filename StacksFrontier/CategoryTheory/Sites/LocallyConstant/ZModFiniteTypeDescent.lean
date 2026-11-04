module

public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.ZModDescent
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyConstantWeakSerre

/-!
# Finite local constancy of the underlying abelian sheaf of a sheaf of `ℤ/m`-modules

A sheaf `L` of `ℤ/mℤ`-modules whose underlying abelian sheaf is constant with value `A`, on a site
with a terminal object, is the constant sheaf of `ℤ/mℤ`-modules on `A / mA`
(`Stacks.ConstantSheaf.nonempty_constantSheaf_zmodQuotient_iso`; this is the construction of
`Stacks.ConstantSheaf.isConstant_of_isConstant_forget₂_zmod`, which records only the conclusion
that `L` is constant). When `A` is finite, so is `A / mA`. Hence a sheaf of `ℤ/mℤ`-modules whose
underlying abelian sheaf is finite locally constant is locally constant of finite type
(`Stacks.ConstantSheaf.isFiniteTypeLocallyConstant_of_isFiniteLocallyConstant_forget₂_zmod`).

This is how the local constancy of the higher direct images `Rᵠ f̄_* ℤ/ℓ` of a smooth proper
curve, proved on the underlying abelian sheaves (Tags 0GKD, 0GJ7), is read on sheaves of
`ℤ/ℓ`-modules in the low-degree inputs of the fibration step of Poincaré duality, in the proof of
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH).

## Main results

* `Stacks.ConstantSheaf.nonempty_constantSheaf_zmodQuotient_iso`.
* `Stacks.ConstantSheaf.isFiniteTypeLocallyConstant_of_isFiniteLocallyConstant_forget₂_zmod`.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

namespace Stacks.ConstantSheaf

universe w v u

variable {C : Type u} [Category.{v} C] (m : ℕ)

section Constant

variable {K : GrothendieckTopology C}
  [HasWeakSheafify K (ModuleCat.{w} (ZMod m))] [HasWeakSheafify K AddCommGrpCat.{w}]
  [K.PreservesSheafification (forget₂ (ModuleCat.{w} (ZMod m)) AddCommGrpCat.{w})]
  [K.HasSheafCompose (forget₂ (ModuleCat.{w} (ZMod m)) AddCommGrpCat.{w})]

/-- **A sheaf of `ℤ/mℤ`-modules whose underlying abelian sheaf is the constant sheaf on `A` is the
constant sheaf on `A / mA`**, on a site with a terminal object: multiplication by `m` vanishes on
`A̲`, the constant sheaf functor preserves the cokernel of multiplication by `m`, and forgetting
the `ℤ/mℤ`-module structure is fully faithful and commutes with constant sheaves. -/
theorem nonempty_constantSheaf_zmodQuotient_iso {T : C} (hT : IsTerminal T)
    (L : Sheaf K (ModuleCat.{w} (ZMod m))) (A : AddCommGrpCat.{w})
    (e : (constantSheaf K AddCommGrpCat.{w}).obj A ≅
      (sheafCompose K (forget₂ (ModuleCat.{w} (ZMod m)) AddCommGrpCat.{w})).obj L) :
    Nonempty ((constantSheaf K (ModuleCat.{w} (ZMod m))).obj (zmodQuotient m A) ≅ L) := by
  let F := sheafCompose K (forget₂ (ModuleCat.{w} (ZMod m)) AddCommGrpCat.{w})
  let c := constantSheaf K AddCommGrpCat.{w}
  have hadj := constantSheafAdj K AddCommGrpCat.{w} hT
  have : PreservesColimitsOfSize.{0, 0} c := hadj.leftAdjoint_preservesColimits
  have : c.IsLeftAdjoint := hadj.isLeftAdjoint
  have : PreservesBinaryBiproducts c := preservesBinaryBiproducts_of_preservesBinaryCoproducts c
  have : c.Additive := Functor.additive_of_preservesBinaryBiproducts c
  -- multiplication by `m` vanishes on `L`, hence on `A̲`
  have hL : m • 𝟙 (F.obj L) = 0 := by
    apply (sheafToPresheaf K _).map_injective
    rw [Functor.map_nsmul, CategoryTheory.Functor.map_id, Functor.map_zero]
    ext U x
    show m • (show L.obj.obj U from x) = 0
    exact ZModModule.char_nsmul_eq_zero m _
  have hA : c.map (m • 𝟙 A) = 0 := by
    rw [Functor.map_nsmul, CategoryTheory.Functor.map_id, ← cancel_mono e.hom, ← cancel_epi e.inv]
    have he : e.inv ≫ (m • 𝟙 (c.obj A)) ≫ e.hom = m • 𝟙 _ := by
      rw [Preadditive.nsmul_comp, Category.id_comp, Preadditive.comp_nsmul, e.inv_hom_id]
    rw [he, hL, Limits.zero_comp, Limits.comp_zero]
  -- so `A̲ ⟶ (A / mA)̲` is an isomorphism, `c` preserving cokernels
  have hπ : IsIso (c.map (cokernel.π (m • 𝟙 A))) := by
    have e₁ : IsIso (cokernel.π (c.map (m • 𝟙 A))) := by
      have key : ∀ {X Y : Sheaf K AddCommGrpCat.{w}} (g : X ⟶ Y), g = 0 →
          IsIso (cokernel.π g) := by
        rintro _ _ g rfl
        infer_instance
      exact key _ hA
    have hcomp : c.map (cokernel.π (m • 𝟙 A)) =
        cokernel.π (c.map (m • 𝟙 A)) ≫ (PreservesCokernel.iso c (m • 𝟙 A)).inv := by
      rw [← PreservesCokernel.π_iso_hom c (m • 𝟙 A), Category.assoc, Iso.hom_inv_id,
        Category.comp_id]
    rw [hcomp]
    infer_instance
  let e' : c.obj (cokernel (m • 𝟙 A)) ≅ F.obj L := (asIso (c.map (cokernel.π _))).symm ≪≫ e
  let e'' : F.obj ((constantSheaf K (ModuleCat.{w} (ZMod m))).obj (zmodQuotient m A)) ≅ F.obj L :=
    (constantCommuteCompose K (forget₂ (ModuleCat.{w} (ZMod m)) AddCommGrpCat.{w})).app _ ≪≫
      c.mapIso (forget₂ZmodQuotientIso m A) ≪≫ e'
  exact ⟨(F ⋙ sheafToPresheaf K _).preimageIso ((sheafToPresheaf K _).mapIso e'')⟩

/-- `A / mA` is finite when `A` is. -/
theorem finite_zmodQuotient (A : AddCommGrpCat.{w}) [Finite A] : Finite (zmodQuotient m A) :=
  Finite.of_surjective _
    ((AddCommGrpCat.epi_iff_surjective (cokernel.π (m • 𝟙 A))).1 inferInstance)

end Constant

section Local

variable (J : GrothendieckTopology C)
  [∀ U : C, HasWeakSheafify (J.over U) (ModuleCat.{w} (ZMod m))]
  [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{w}]
  [∀ U : C, (J.over U).PreservesSheafification
    (forget₂ (ModuleCat.{w} (ZMod m)) AddCommGrpCat.{w})]
  [∀ U : C, (J.over U).HasSheafCompose (forget₂ (ModuleCat.{w} (ZMod m)) AddCommGrpCat.{w})]
  [J.HasSheafCompose (forget₂ (ModuleCat.{w} (ZMod m)) AddCommGrpCat.{w})]

/-- **A sheaf of `ℤ/mℤ`-modules is locally constant of finite type as soon as its underlying
abelian sheaf is finite locally constant**: on each member of a trivializing covering, the
restriction is the constant sheaf on `A / mA` for a finite abelian group `A`
(`Stacks.ConstantSheaf.nonempty_constantSheaf_zmodQuotient_iso`), a finite, hence finitely
generated, `ℤ/mℤ`-module. -/
theorem isFiniteTypeLocallyConstant_of_isFiniteLocallyConstant_forget₂_zmod
    (L : Sheaf J (ModuleCat.{w} (ZMod m)))
    (h : IsFiniteLocallyConstant J
      ((sheafCompose J (forget₂ (ModuleCat.{w} (ZMod m)) AddCommGrpCat.{w})).obj L)) :
    IsFiniteTypeLocallyConstant (ZMod m) J L := by
  intro U
  obtain ⟨I, X, f, hcov, hc⟩ := h.exists_finite_cover U
  refine ⟨I, X, f, hcov, fun i => ?_⟩
  obtain ⟨A, hA, ⟨e⟩⟩ := hc i
  have e₁ : (constantSheaf (J.over (X i)) AddCommGrpCat.{w}).obj A ≅
      (sheafCompose (J.over (X i)) (forget₂ (ModuleCat.{w} (ZMod m)) AddCommGrpCat.{w})).obj
        ((J.overPullback (ModuleCat.{w} (ZMod m)) (X i)).obj L) := e
  obtain ⟨e₂⟩ := nonempty_constantSheaf_zmodQuotient_iso m (Over.mkIdTerminal (X := X i)) _ A e₁
  have : Finite A := hA
  have : Finite (zmodQuotient m A) := finite_zmodQuotient m A
  exact ⟨zmodQuotient m A, (ModuleCat.isFG_iff _).2 Module.Finite.of_finite, ⟨e₂⟩⟩

end Local

end Stacks.ConstantSheaf

end
