module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.Defs
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.MethodeDeLa.ZModGeometricFibre

/-!
# Local constancy of a sheaf of `ℤ/m`-modules is that of its underlying abelian sheaf

A sheaf `L` of `ℤ/mℤ`-modules is constant on a site with a terminal object as soon as its
underlying sheaf of abelian groups is constant, and so `L` is locally constant as soon as its
underlying abelian sheaf is. The value of the constant sheaf is not automatically a `ℤ/mℤ`-module.
If `A̲ ≅ L` as abelian sheaves, then multiplication by `m` vanishes on `A̲`. The constant sheaf
functor is a left adjoint, so it carries the cokernel `A / mA` of multiplication by `m` to the
cokernel of the zero map, which is `A̲` itself. Hence `L` is the constant sheaf on the
`ℤ/mℤ`-module `A / mA`, because the forgetful functor from `ℤ/mℤ`-modules to abelian groups is
fully faithful (`Stacks.EtaleCohomology.full_forget₂_moduleCat_zmod`) and commutes with
constant sheaves.

## Main results

* `Stacks.ConstantSheaf.isConstant_of_isConstant_forget₂_zmod`: the statement over a site with a
  terminal object.
* `Stacks.ConstantSheaf.isLocallyConstant_of_isLocallyConstant_forget₂_zmod`: the local form.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

namespace Stacks.ConstantSheaf

universe w v u

variable {C : Type u} [Category.{v} C] (m : ℕ)

section Constant

variable (K : GrothendieckTopology C)
  [HasWeakSheafify K (ModuleCat.{w} (ZMod m))] [HasWeakSheafify K AddCommGrpCat.{w}]
  [K.PreservesSheafification (forget₂ (ModuleCat.{w} (ZMod m)) AddCommGrpCat.{w})]
  [K.HasSheafCompose (forget₂ (ModuleCat.{w} (ZMod m)) AddCommGrpCat.{w})]

/-- The value `A / mA` of a constant abelian sheaf on which multiplication by `m` vanishes, as a
`ℤ/mℤ`-module. -/
def zmodQuotient (A : AddCommGrpCat.{w}) : ModuleCat.{w} (ZMod m) :=
  letI : Module (ZMod m) (cokernel (m • 𝟙 A) : AddCommGrpCat.{w}) := AddCommGroup.zmodModule
    (by
      intro x
      obtain ⟨a, rfl⟩ := (AddCommGrpCat.epi_iff_surjective (cokernel.π (m • 𝟙 A))).1
        inferInstance x
      have h₁ : m • cokernel.π (m • 𝟙 A) = 0 := by
        have := cokernel.condition (m • 𝟙 A)
        rwa [Preadditive.nsmul_comp, Category.id_comp] at this
      have h₂ : (m • cokernel.π (m • 𝟙 A)) a = 0 := by
        rw [h₁]
        rfl
      exact h₂)
  ModuleCat.of (ZMod m) (cokernel (m • 𝟙 A) : AddCommGrpCat.{w})

/-- The underlying abelian group of `zmodQuotient m A` is the cokernel of multiplication by `m`. -/
def forget₂ZmodQuotientIso (A : AddCommGrpCat.{w}) :
    (forget₂ (ModuleCat.{w} (ZMod m)) AddCommGrpCat.{w}).obj (zmodQuotient m A) ≅
      cokernel (m • 𝟙 A) :=
  AddEquiv.toAddCommGrpIso (AddEquiv.refl _)

variable {K}

/-- **A sheaf of `ℤ/mℤ`-modules whose underlying abelian sheaf is constant is constant**, on a
site with a terminal object. -/
theorem isConstant_of_isConstant_forget₂_zmod {T : C} (hT : IsTerminal T)
    (L : Sheaf K (ModuleCat.{w} (ZMod m)))
    [h : ((sheafCompose K (forget₂ (ModuleCat.{w} (ZMod m)) AddCommGrpCat.{w})).obj L).IsConstant
      K] : L.IsConstant K := by
  obtain ⟨A, ⟨e⟩⟩ := h.mem_essImage
  let F := sheafCompose K (forget₂ (ModuleCat.{w} (ZMod m)) AddCommGrpCat.{w})
  let c := constantSheaf K AddCommGrpCat.{w}
  have hadj := constantSheafAdj K AddCommGrpCat.{w} hT
  have : PreservesColimitsOfSize.{0, 0} c := hadj.leftAdjoint_preservesColimits
  have : c.IsLeftAdjoint := hadj.isLeftAdjoint
  have : PreservesBinaryBiproducts c := preservesBinaryBiproducts_of_preservesBinaryCoproducts c
  have : c.Additive := Functor.additive_of_preservesBinaryBiproducts c
  -- multiplication by `m` vanishes on `L`, hence on `A̲`
  have hL : m • 𝟙 ((sheafCompose K (forget₂ (ModuleCat.{w} (ZMod m)) AddCommGrpCat.{w})).obj L) =
      0 := by
    apply (sheafToPresheaf K _).map_injective
    rw [Functor.map_nsmul, CategoryTheory.Functor.map_id, Functor.map_zero]
    ext U x
    show m • (show L.obj.obj U from x) = 0
    exact ZModModule.char_nsmul_eq_zero m _
  have hA : c.map (m • 𝟙 A) = 0 := by
    rw [Functor.map_nsmul, CategoryTheory.Functor.map_id, ← cancel_mono e.hom,
      ← cancel_epi e.inv]
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
  exact Sheaf.isConstant_of_iso K
    ((F ⋙ sheafToPresheaf K _).preimageIso ((sheafToPresheaf K _).mapIso e'')).symm

end Constant

section Local

variable (J : GrothendieckTopology C)
  [∀ U : C, HasWeakSheafify (J.over U) (ModuleCat.{w} (ZMod m))]
  [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{w}]
  [∀ U : C, (J.over U).PreservesSheafification
    (forget₂ (ModuleCat.{w} (ZMod m)) AddCommGrpCat.{w})]
  [∀ U : C, (J.over U).HasSheafCompose (forget₂ (ModuleCat.{w} (ZMod m)) AddCommGrpCat.{w})]
  [J.HasSheafCompose (forget₂ (ModuleCat.{w} (ZMod m)) AddCommGrpCat.{w})]

/-- **A sheaf of `ℤ/mℤ`-modules is locally constant as soon as its underlying abelian sheaf is.**
Restriction to a slice commutes with forgetting the module structure, and the slice `C/U` has the
terminal object `𝟙 U`. -/
theorem isLocallyConstant_of_isLocallyConstant_forget₂_zmod
    (L : Sheaf J (ModuleCat.{w} (ZMod m)))
    (h : IsLocallyConstant J
      ((sheafCompose J (forget₂ (ModuleCat.{w} (ZMod m)) AddCommGrpCat.{w})).obj L)) :
    IsLocallyConstant J L where
  exists_cover U := by
    obtain ⟨I, X, f, hcov, hc⟩ := h.exists_cover U
    refine ⟨I, X, f, hcov, fun i => ?_⟩
    have e : (J.overPullback AddCommGrpCat.{w} (X i)).obj
        ((sheafCompose J (forget₂ (ModuleCat.{w} (ZMod m)) AddCommGrpCat.{w})).obj L) ≅
        (sheafCompose (J.over (X i)) (forget₂ (ModuleCat.{w} (ZMod m)) AddCommGrpCat.{w})).obj
          ((J.overPullback (ModuleCat.{w} (ZMod m)) (X i)).obj L) := Iso.refl _
    have := hc i
    have : ((sheafCompose (J.over (X i)) (forget₂ (ModuleCat.{w} (ZMod m))
        AddCommGrpCat.{w})).obj ((J.overPullback (ModuleCat.{w} (ZMod m)) (X i)).obj L)).IsConstant
        (J.over (X i)) := Sheaf.isConstant_congr _ e
    exact isConstant_of_isConstant_forget₂_zmod m (Over.mkIdTerminal (X := X i)) _

end Local

end Stacks.ConstantSheaf
