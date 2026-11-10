module

public import StacksFrontier.AlgebraicGeometry.Curves.GenusOne.SectionOrder
public import StacksFrontier.AlgebraicGeometry.PullbackSections.Qcqs
public import StacksFrontier.AlgebraicGeometry.TensorPowerDivision.Basic

/-!
# Division by a section vanishing at one point, in the section ring

Let `L` be an invertible module on a scheme `X`, `x` a point whose local ring is a discrete
valuation ring, and `u` a homogeneous element of the section ring `Γ_*(X, L)` that does not vanish
anywhere off `x`. This file proves that a homogeneous element `t` whose order at `x` is at least
that of `u` is a multiple `u · b` in the section ring.

## Main results

* `Stacks.StalkOrder.exists_mul_eq_of_sectionOrd_le`: **if `ord_x u ≤ ord_x t` then `t = u · b`.**

## Implementation notes

Off `x`, multiplication by `u` is bijective on sections
(`Stacks.TensorPowerDivision.bijective_app_mulMap`), which gives `b` there. At `x`, the stalk map
of multiplication by `u` has image the multiples of the coefficient of the germ of `u`
(`Stacks.SectionProduct.stalkMulGE_mulMap`), so the germ of `t` is the image of a germ, which is
represented by a section on a neighbourhood of `x` whose product with `u` is `t` after shrinking.
The two local quotients agree on the overlap by injectivity off `x`, and glue.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry
open Stacks.ModuleStalk Stacks.SectionProduct
open Stacks.GradedSections (powSections mul mulMap)
open Stacks.TensorPowers (natTensorPow)
open Stacks.NonvanishingOpen (nonvanishingOpen)

universe u

namespace Stacks.StalkOrder

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

attribute [local implicit_reducible] Stacks.TensorPowers.natTensorPow

variable {X : Scheme.{u}} {x : X} [IsDomain (X.presheaf.stalk x)]
  [IsDiscreteValuationRing (X.presheaf.stalk x)]
  (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]

/-- The naturality of a morphism of modules on sections, applied to a section. -/
theorem app_map_apply {M N : X.Modules} (φ : M ⟶ N) {U V : X.Opens} (i : U ⟶ V) (b : Γ(M, V)) :
    φ.app U (M.presheaf.map i.op b) = N.presheaf.map i.op (φ.app V b) :=
  ConcreteCategory.congr_hom (φ.mapPresheaf.naturality i.op) b

/-- **Gluing a preimage along a cover by two opens.** If `φ` is injective on `V ⊓ W` and the
restrictions of `T` to `V` and to `W` lie in the image of `φ`, then so does `T`. -/
private theorem exists_app_top_eq_of_sup {M N : X.Modules} (φ : M ⟶ N) {V W : X.Opens}
    (hVW : ⊤ ≤ V ⊔ W) (hinj : Function.Injective (φ.app (V ⊓ W))) {T : Γ(N, ⊤)}
    {b₁ : Γ(M, V)} {b₂ : Γ(M, W)} (h₁ : φ.app V b₁ = N.presheaf.map (homOfLE le_top).op T)
    (h₂ : φ.app W b₂ = N.presheaf.map (homOfLE le_top).op T) :
    ∃ b : Γ(M, ⊤), φ.app ⊤ b = T := by
  have hagree : M.presheaf.map (homOfLE (inf_le_left : V ⊓ W ≤ V)).op b₁ =
      M.presheaf.map (homOfLE (inf_le_right : V ⊓ W ≤ W)).op b₂ := by
    refine hinj ?_
    rw [app_map_apply, app_map_apply, h₁, h₂, ← CategoryTheory.comp_apply,
      ← CategoryTheory.comp_apply, ← Functor.map_comp, ← Functor.map_comp]
    rfl
  obtain ⟨b, hbV, hbW⟩ := Stacks.AlgebraicGeometry.SectionsBaseChange.sheaf_glue_pair
    (⟨M.presheaf, M.isSheaf⟩ : TopCat.Sheaf Ab.{u} _) V W b₁ b₂ hagree
  have key : ∀ (U : X.Opens) (hU : U ≤ ⊤) (hUV : U ≤ V ⊔ W) (c : Γ(M, U)),
      M.presheaf.map (homOfLE hUV).op b = c → φ.app U c = N.presheaf.map (homOfLE hU).op T →
      N.presheaf.map (homOfLE hU).op (φ.app ⊤ (M.presheaf.map (homOfLE hVW).op b)) =
        N.presheaf.map (homOfLE hU).op T := fun U hU hUV c hc hφ => by
    rw [← app_map_apply, ← hφ, ← hc]
    congr 1
    rw [← CategoryTheory.comp_apply, ← Functor.map_comp]
    rfl
  exact ⟨M.presheaf.map (homOfLE hVW).op b, TopCat.Sheaf.eq_of_locally_eq₂
    (F := (⟨N.presheaf, N.isSheaf⟩ : TopCat.Sheaf Ab.{u} _))
    (homOfLE (le_top : V ≤ ⊤)) (homOfLE (le_top : W ≤ ⊤)) hVW _ _
    (key V le_top le_sup_left b₁ hbV h₁) (key W le_top le_sup_right b₂ hbW h₂)⟩

/-- A section of a tensor power has germ `r • g` for a generator `g`, with `r` computing its
order. -/
private theorem exists_generator_smul_sectionOrd {n : ℕ} (s : powSections L n) :
    ∃ (g : TopCat.Presheaf.stalk (C := Ab.{u}) (natTensorPow L n).presheaf x)
      (r : X.presheaf.stalk x), (∀ z, ∃ c : X.presheaf.stalk x, z = c • g) ∧
      ((natTensorPow L n).presheaf.Γgerm x).hom (globalSection X _ s) = r • g ∧
      sectionOrd x L s = IsDiscreteValuationRing.addVal (X.presheaf.stalk x) r := by
  have := Stacks.SectionProduct.isInvertibleModule_natTensorPow (X := X) L n
  obtain ⟨g, hg, hfree⟩ := exists_generator (natTensorPow L n) x
  obtain ⟨r, hr⟩ := hg (((natTensorPow L n).presheaf.Γgerm x).hom (globalSection X _ s))
  refine ⟨g, r, hg, hr, ?_⟩
  unfold sectionOrd sectionGerm
  rw [hr, stalkOrd_smul_generator hg hfree]

/-- **Division by a section vanishing only at `x`.** Let `u` be a homogeneous element of degree
`j` of `Γ_*(X, L)` that does not vanish at any point other than `x`, and `t` one of degree `j + m`
whose order at `x` is at least that of `u`. Then `t = u · b` for a homogeneous `b` of degree
`m`. -/
theorem exists_mul_eq_of_sectionOrd_le {j m : ℕ} (u : powSections L j)
    (hu : ∀ y : X, y ≠ x → y ∈ nonvanishingOpen X (natTensorPow L j) (globalSection X _ u))
    (t : powSections L (j + m)) (hut : sectionOrd x L u ≤ sectionOrd x L t) :
    ∃ b : powSections L m, mul u b = t := by
  have := Stacks.SectionProduct.isInvertibleModule_natTensorPow (X := X) L j
  have := Stacks.SectionProduct.isInvertibleModule_natTensorPow (X := X) L m
  have := Stacks.SectionProduct.isInvertibleModule_natTensorPow (X := X) L (j + m)
  set V := nonvanishingOpen X (natTensorPow L j) (globalSection X _ u)
  set φ := mulMap u m
  set T := globalSection X (natTensorPow L (j + m)) t with hT
  obtain ⟨b₁, hb₁⟩ := (Stacks.TensorPowerDivision.bijective_app_mulMap L u le_rfl m V le_rfl).2
    ((natTensorPow L (j + m)).presheaf.map (homOfLE le_top).op T)
  obtain ⟨g, r, hg, hr, h₁⟩ := exists_generator_smul_sectionOrd (x := x) L u
  have hge : StalkMulGE u x r := (stalkMulGE_unit_iff _ u x r).mpr fun z => by
    obtain ⟨c, rfl⟩ := hg z
    exact ⟨c, by rw [hr, smul_smul, smul_smul, mul_comm]⟩
  have hgeφ : StalkMulGE φ x r := stalkMulGE_mulMap L u hge m
  obtain ⟨h, r', -, hr', h₂⟩ := exists_generator_smul_sectionOrd (x := x) L t
  obtain ⟨q, rfl⟩ : r ∣ r' := by rwa [← IsDiscreteValuationRing.addVal_le_iff_dvd, ← h₁, ← h₂]
  obtain ⟨ζ, hζ⟩ := hgeφ (q • h)
  obtain ⟨W, hxW, b₂, rfl⟩ := TopCat.Presheaf.exists_germ_eq (natTensorPow L m).presheaf ζ
  have hgerm : ((natTensorPow L (j + m)).presheaf.germ W x hxW).hom (φ.app W b₂) =
      ((natTensorPow L (j + m)).presheaf.germ ⊤ x trivial).hom T := by
    rw [← mapFun_germ, hζ, smul_smul, ← hr']
    rfl
  obtain ⟨W', hxW', iW, iT, hW'⟩ :=
    TopCat.Presheaf.germ_eq (natTensorPow L (j + m)).presheaf x hxW
      (show x ∈ (⊤ : X.Opens) from trivial) _ _ hgerm
  have hb₂ : φ.app W' ((natTensorPow L m).presheaf.map iW.op b₂) =
      (natTensorPow L (j + m)).presheaf.map iT.op T := by
    rw [app_map_apply, hW']
  have hcover : (⊤ : X.Opens) ≤ V ⊔ W' := by
    intro y _
    by_cases hy : y = x
    · exact Or.inr (hy ▸ hxW')
    · exact Or.inl (hu y hy)
  obtain ⟨bt, hprod⟩ := exists_app_top_eq_of_sup φ hcover
    (Stacks.TensorPowerDivision.bijective_app_mulMap L u le_rfl m (V ⊓ W') inf_le_left).1 hb₁ hb₂
  refine ⟨Stacks.AlgebraicGeometry.ProjChartFromRatios.secOf L bt, ?_⟩
  apply (Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv X _).injective
  change globalSection X _ _ = T
  rwa [Stacks.SectionProduct.globalSection_mul,
    Stacks.AlgebraicGeometry.ProjChartFromRatios.globalSection_secOf]

end Stacks.StalkOrder

end
