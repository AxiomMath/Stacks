module

public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Products
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Limits
public import Mathlib.CategoryTheory.Triangulated.Yoneda
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Triangulated.HomotopyColimit
public import StacksFrontier.CategoryTheory.Triangulated.HomotopyLimit
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.RlimBasic

/-!
# Milnor sequences: maps into a derived limit and out of a derived colimit

Let `D` be a pretriangulated category and `(Fₙ)` a sequence in `D`.

If `K` is a derived limit of an inverse system `F : ℕᵒᵖ ⥤ D`, then for every object `L` the
group of maps `L ⟶ K` sits in a short exact sequence whose left term is the first derived
inverse limit of the groups `Hom(L, Fₙ[-1])` and whose right term is the inverse limit of the
groups `Hom(L, Fₙ)`. Dually, if `K` is a derived colimit of a sequence `F : ℕ ⥤ D`, then the
group of maps `K ⟶ L` sits in a short exact sequence with outer terms the first derived inverse
limit of `Hom(Fₙ, L[-1])` and the inverse limit of `Hom(Fₙ, L)`.

In both cases the first derived inverse limit is the cokernel of `Rlim.delta`, the map
`1 - shift` on the product of the Hom-system, so the sequences are the Milnor sequences in the
two-term product presentation of `R¹lim`.

## Main definitions

* `Rlim.Hom.systemProduct`, `Rlim.Hom.systemDelta`: the product of the terms of an inverse system
  in `D` and the specified difference map `1 - shift` on it.
* `Rlim.Hom.DerivedLimitTriangle`: a chosen defining triangle of a derived inverse limit.
* `Rlim.Hom.homSystem`, `Rlim.Hom.shiftedHomSystem`: the inverse systems of abelian groups of maps
  from a fixed object into the terms of the system, and into their shifts.
* `Rlim.Hom.homProductComparison`, `Rlim.Hom.homProductMap`,
  `Rlim.Hom.shiftedHomProductComparison`, `Rlim.Hom.shiftedHomProductMap`,
  `Rlim.Hom.homConnecting`: the comparison isomorphisms between a Hom group of a product and the
  product of Hom groups, the induced maps on those products, and the connecting map of the
  shifted Hom long exact sequence.
* `Rlim.Hom.MilnorSequence`: the two canonical arrows of the Milnor sequence, their
  characterizing equations, and its short exactness.

## Main results

* `Rlim.Hom.hom_into_isDerivedLimit_shortExact`: the Milnor short exact sequence for maps into a
  derived inverse limit, natural for morphisms of defining triangles (Tag 0919), with the bare
  short exact sequence extracted as `Rlim.Hom.hom_into_isDerivedLimit_shortExact_basic`.
* `Rlim.Hom.shortExact_map_from_isHomotopyColimit`: the Milnor short exact sequence for maps out
  of a derived colimit, with its arrows identified through a defining triangle: restriction along
  the coprojections and the connecting morphism (Tag 0CQX). The version for a chosen defining
  triangle is `Rlim.Hom.shortExact_map_from_homotopyColimit_triangle`, and the bare short exact
  sequence is `Rlim.Hom.exists_shortExact_map_from_isHomotopyColimit`.

## Implementation notes

The first derived inverse limit of a countable inverse system of abelian groups is written as the
cokernel of `Rlim.delta`, the presentation set up in
`StacksFrontier.Homology.DerivedCategory.InverseSystem.RlimBasic`; the ordinary inverse limit is
retained as the categorical limit of the Hom-system. An inverse system is a functor from
`ℕᵒᵖ`, a derived limit is `CategoryTheory.Pretriangulated.IsDerivedLimit` and a derived colimit
is `CategoryTheory.Pretriangulated.IsHomotopyColimit`. Both proofs run the long exact Hom
sequence of the defining triangle and cut the resulting four-term exact sequence into a
cokernel-to-kernel short exact sequence; the comparison between a Hom group of a product and the
product of Hom groups is the only place where preservation of countable products by
`preadditiveCoyoneda` is used.

## References

* [Stacks Project, Tag 0919](https://stacks.math.columbia.edu/tag/0919)
* [Stacks Project, Tag 0CQX](https://stacks.math.columbia.edu/tag/0CQX)
-/


section

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Pretriangulated Limits Opposite

universe v u

namespace Rlim.Hom

-- `Rlim.product` is a plain definition, so the identifications of `Rlim.product A` with the
-- chosen product `∏ᶜ` are only reducible-transparency defeq.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- The objectwise product of an inverse system in the ambient category. -/
public abbrev systemProduct (F : ℕᵒᵖ ⥤ D) [HasProduct fun n : ℕ => F.obj (op n)] : D :=
  ∏ᶜ fun n : ℕ ↦ F.obj (op n)

/-- The specified difference map in a derived limit triangle. -/
public noncomputable def systemDelta (F : ℕᵒᵖ ⥤ D)
    [HasProduct fun n : ℕ => F.obj (op n)] : systemProduct F ⟶ systemProduct F :=
  Pi.lift fun n : ℕ => Pi.π (fun n : ℕ => F.obj (op n)) n -
    Pi.π (fun n : ℕ => F.obj (op n)) (n + 1) ≫
      F.map (homOfLE (Nat.le_succ n)).op

/-- A chosen defining triangle of a derived inverse limit. -/
public structure DerivedLimitTriangle (F : ℕᵒᵖ ⥤ D)
    [HasProduct fun n : ℕ => F.obj (op n)] (K : D) where
  /-- The map from `K` to the objectwise product of `F`. -/
  inclusion : K ⟶ systemProduct F
  /-- The connecting map from the objectwise product of `F` to the shift `K⟦1⟧`. -/
  connecting : systemProduct F ⟶ K⟦(1 : ℤ)⟧
  /-- The triangle formed by `inclusion`, `systemDelta F` and `connecting` is distinguished. -/
  distinguished : Triangle.mk inclusion (systemDelta F) connecting ∈ distTriang D

/-- The triangle specified by a derived limit datum. -/
public abbrev DerivedLimitTriangle.triangle {F : ℕᵒᵖ ⥤ D}
    [HasProduct fun n : ℕ => F.obj (op n)] {K : D} (t : DerivedLimitTriangle F K) :
    Triangle D := Triangle.mk t.inclusion (systemDelta F) t.connecting

/-- The functor of maps from `L` into the inverse system `F`. -/
public abbrev homSystem (L : D) (F : ℕᵒᵖ ⥤ D) : ℕᵒᵖ ⥤ Ab.{v} :=
  F ⋙ preadditiveCoyoneda.obj (op L)

/-- The shifted functor of maps from `L` into the inverse system `F`. -/
public abbrev shiftedHomSystem (L : D) (F : ℕᵒᵖ ⥤ D) : ℕᵒᵖ ⥤ Ab.{v} :=
  F ⋙ shiftFunctor D (-1 : ℤ) ⋙ preadditiveCoyoneda.obj (op L)

/-- The canonical comparison from a Hom group of a product to the product of Hom groups. -/
public noncomputable def homProductComparison (L : D) (F : ℕᵒᵖ ⥤ D)
    [HasProduct fun n : ℕ => F.obj (op n)] :
    (preadditiveCoyoneda.obj (op L)).obj (systemProduct F) ⟶
      ∏ᶜ fun n : ℕ ↦ (homSystem L F).obj (op n) :=
  piComparison (preadditiveCoyoneda.obj (op L)) (fun n : ℕ ↦ F.obj (op n))

/-- The map on product Hom groups induced by an arrow between the ambient products. -/
public noncomputable def homProductMap (L : D) (F G : ℕᵒᵖ ⥤ D)
    [HasProduct fun n : ℕ => F.obj (op n)]
    [HasProduct fun n : ℕ => G.obj (op n)] (f : systemProduct F ⟶ systemProduct G) :
    (∏ᶜ fun n : ℕ ↦ (homSystem L F).obj (op n)) ⟶
      (∏ᶜ fun n : ℕ ↦ (homSystem L G).obj (op n)) :=
  letI : PreservesLimits (preadditiveCoyoneda.obj (op L)) := inferInstance
  letI : PreservesLimitsOfSize.{0, 0} (preadditiveCoyoneda.obj (op L)) :=
    preservesSmallestLimits_of_preservesLimits _
  haveI : IsIso (homProductComparison L F) := by
    dsimp [homProductComparison]
    infer_instance
  inv (homProductComparison L F) ≫
    (preadditiveCoyoneda.obj (op L)).map f ≫ homProductComparison L G

/-- The canonical comparison from the Hom group into the shifted product to the product of the
shifted Hom groups. -/
public noncomputable def shiftedHomProductComparison (L : D) (F : ℕᵒᵖ ⥤ D)
    [HasProduct fun n : ℕ => F.obj (op n)] :
    (preadditiveCoyoneda.obj (op L)).obj ((systemProduct F)⟦(-1 : ℤ)⟧) ⟶
      ∏ᶜ fun n : ℕ ↦ (shiftedHomSystem L F).obj (op n) :=
  piComparison (shiftFunctor D (-1 : ℤ) ⋙ preadditiveCoyoneda.obj (op L))
    (fun n : ℕ ↦ F.obj (op n))

/-- A product map after applying shifted Hom. -/
public noncomputable def shiftedHomProductMap (L : D) (F G : ℕᵒᵖ ⥤ D)
    [HasProduct fun n : ℕ => F.obj (op n)]
    [HasProduct fun n : ℕ => G.obj (op n)] (f : systemProduct F ⟶ systemProduct G) :
    (∏ᶜ fun n : ℕ ↦ (shiftedHomSystem L F).obj (op n)) ⟶
      (∏ᶜ fun n : ℕ ↦ (shiftedHomSystem L G).obj (op n)) :=
  let H := shiftFunctor D (-1 : ℤ) ⋙ preadditiveCoyoneda.obj (op L)
  letI : PreservesLimitsOfSize.{0, 0} H :=
    preservesSmallestLimits_of_preservesLimits H
  haveI : IsIso (shiftedHomProductComparison L F) := by
    dsimp [shiftedHomProductComparison]
    infer_instance
  inv (shiftedHomProductComparison L F) ≫
    (preadditiveCoyoneda.obj (op L)).map ((shiftFunctor D (-1 : ℤ)).map f) ≫
      shiftedHomProductComparison L G

/-- The connecting map of the shifted Hom long exact sequence, expressed on product Hom
groups. -/
public noncomputable def homConnecting (L : D) (F : ℕᵒᵖ ⥤ D)
    [HasProduct fun n : ℕ => F.obj (op n)] (K : D)
    (t : DerivedLimitTriangle F K) :
    (∏ᶜ fun n : ℕ ↦ (shiftedHomSystem L F).obj (op n)) ⟶
      (preadditiveCoyoneda.obj (op L)).obj K :=
  let H := preadditiveCoyoneda.obj (op L)
  let J := shiftFunctor D (-1 : ℤ) ⋙ H
  letI : PreservesLimitsOfSize.{0, 0} J :=
    preservesSmallestLimits_of_preservesLimits J
  haveI : IsIso (shiftedHomProductComparison L F) := by
    dsimp [shiftedHomProductComparison]
    infer_instance
  inv (shiftedHomProductComparison L F) ≫
    H.homologySequenceδ t.triangle (-1) 0 (by omega) ≫
      (H.isoShiftZero ℤ).hom.app K
/-- A Milnor sequence attached to a specified defining derived-limit triangle. The two
equations characterize its arrows by the connecting map and the triangle inclusion. -/
public structure MilnorSequence (L : D) (F : ℕᵒᵖ ⥤ D)
    [HasProduct fun n : ℕ => F.obj (op n)] (K : D)
    (t : DerivedLimitTriangle F K) where
  /-- The map from the cokernel of the difference map of `shiftedHomSystem L F` to the maps
  from `L` to `K`. -/
  inclusion : cokernel (Rlim.delta (shiftedHomSystem L F)) ⟶
    (preadditiveCoyoneda.obj (op L)).obj K
  /-- The map from the maps from `L` to `K` to the limit of `homSystem L F`. -/
  projection : (preadditiveCoyoneda.obj (op L)).obj K ⟶ limit (homSystem L F)
  inclusion_spec : cokernel.π (Rlim.delta (shiftedHomSystem L F)) ≫ inclusion =
    homConnecting L F K t
  projection_spec : projection ≫ Rlim.limitToProduct (homSystem L F) =
    (preadditiveCoyoneda.obj (op L)).map t.inclusion ≫ homProductComparison L F
  zero : inclusion ≫ projection = 0
  /-- The complex formed by `inclusion` and `projection` is short exact. -/
  shortExact : (ShortComplex.mk inclusion projection zero).ShortExact

end Rlim.Hom
end

end


section

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Pretriangulated Limits Opposite

universe v u

namespace Rlim.Hom

-- `Rlim.product` is a plain definition, so the identifications of `Rlim.product A` with the
-- chosen product `∏ᶜ` are only reducible-transparency defeq.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

omit [HasZeroObject D] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] in
omit [HasShift D ℤ] in
private lemma homProductComparison_isIso (L : D) (F : ℕᵒᵖ ⥤ D)
    [HasProduct fun n : ℕ => F.obj (op n)] : IsIso (homProductComparison L F) := by
  let : PreservesLimitsOfSize.{0, 0} (preadditiveCoyoneda.obj (op L)) :=
    preservesSmallestLimits_of_preservesLimits _
  dsimp [homProductComparison]
  infer_instance

omit [HasZeroObject D] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] in
private lemma shiftedHomProductComparison_isIso (L : D) (F : ℕᵒᵖ ⥤ D)
    [HasProduct fun n : ℕ => F.obj (op n)] : IsIso (shiftedHomProductComparison L F) := by
  let : PreservesLimitsOfSize.{0, 0} (shiftFunctor D (-1 : ℤ) ⋙
      preadditiveCoyoneda.obj (op L)) := preservesSmallestLimits_of_preservesLimits _
  dsimp [shiftedHomProductComparison]
  infer_instance

attribute [local instance] homProductComparison_isIso shiftedHomProductComparison_isIso

omit [HasZeroObject D] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] in
omit [HasShift D ℤ] in
private lemma map_systemDelta (J : D ⥤ Ab.{v}) [J.Additive] (F : ℕᵒᵖ ⥤ D)
    [HasProduct fun n : ℕ => F.obj (op n)] :
    J.map (systemDelta F) ≫ piComparison J (fun n : ℕ => F.obj (op n)) =
      piComparison J (fun n : ℕ => F.obj (op n)) ≫ Rlim.delta (F ⋙ J) := by
  rw [Rlim.delta_eq_lift]
  apply Pi.hom_ext
  intro n
  dsimp only [Functor.comp_obj, Functor.comp_map]
  simp only [Category.assoc, piComparison_comp_π, Pi.lift_comp_π,
    Preadditive.comp_sub, piComparison_comp_π_assoc, ← J.map_comp, systemDelta,
    Pi.lift_comp_π, J.map_sub]

private lemma exact_of_iso_components
    {C : Type*} [Category* C] [HasZeroMorphisms C]
    {S : ShortComplex C} (hS : S.Exact) {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    (e₁ : S.X₁ ≅ X) (e₂ : S.X₂ ≅ Y) (e₃ : S.X₃ ≅ Z)
    (hf : S.f ≫ e₂.hom = e₁.hom ≫ f)
    (hg : S.g ≫ e₃.hom = e₂.hom ≫ g) :
    ∃ w : f ≫ g = 0, (ShortComplex.mk f g w).Exact := by
  have w : f ≫ g = 0 := by
    rw [← cancel_epi e₁.hom, ← Category.assoc, ← hf, Category.assoc, ← hg,
      ← Category.assoc, S.zero, zero_comp, comp_zero]
  exact ⟨w, ShortComplex.exact_of_iso (ShortComplex.isoMk e₁ e₂ e₃ hf.symm hg.symm) hS⟩

private lemma shortExact_of_exact_four
    {C : Type*} [Category* C] [Abelian C]
    {A₀ A₁ A₂ A₃ A₄ : C} {f₀ : A₀ ⟶ A₁} {f₁ : A₁ ⟶ A₂}
    {f₂ : A₂ ⟶ A₃} {f₃ : A₃ ⟶ A₄}
    (w₀ : f₀ ≫ f₁ = 0) (w₁ : f₁ ≫ f₂ = 0) (w₂ : f₂ ≫ f₃ = 0)
    (h₁ : (ShortComplex.mk f₀ f₁ w₀).Exact)
    (h₂ : (ShortComplex.mk f₁ f₂ w₁).Exact)
    (h₃ : (ShortComplex.mk f₂ f₃ w₂).Exact) :
    let i := cokernel.desc f₀ f₁ w₀
    let q := kernel.lift f₃ f₂ w₂
    ∃ w : i ≫ q = 0, (ShortComplex.mk i q w).ShortExact := by
  dsimp
  have hi : Mono (cokernel.desc f₀ f₁ w₀) := h₁.mono_cokernelDesc
  have hq : Epi (kernel.lift f₃ f₂ w₂) := h₃.epi_kernelLift
  have wi : cokernel.desc f₀ f₁ w₀ ≫ f₂ = 0 := by
    rw [← cancel_epi (cokernel.π f₀), cokernel.π_desc_assoc, comp_zero, w₁]
  have hm : (ShortComplex.mk (cokernel.desc f₀ f₁ w₀) f₂ wi).Exact :=
    (ShortComplex.exact_iff_of_epi_of_isIso_of_mono
      (S₁ := ShortComplex.mk f₁ f₂ w₁)
      (S₂ := ShortComplex.mk (cokernel.desc f₀ f₁ w₀) f₂ wi)
      ⟨cokernel.π _, 𝟙 _, 𝟙 _, by simp, by simp⟩).1 h₂
  have w : cokernel.desc f₀ f₁ w₀ ≫ kernel.lift f₃ f₂ w₂ = 0 := by
    rw [← cancel_mono (kernel.ι f₃)]
    simp [wi]
  refine ⟨w, ShortComplex.ShortExact.mk' ?_ hi hq⟩
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono
    (S₁ := ShortComplex.mk (cokernel.desc f₀ f₁ w₀) (kernel.lift f₃ f₂ w₂) w)
    (S₂ := ShortComplex.mk (cokernel.desc f₀ f₁ w₀) f₂ wi)
    ⟨𝟙 _, 𝟙 _, kernel.ι _, by simp, by simp⟩).2 hm

attribute [local instance] Rlim.limitToProduct_mono

set_option backward.isDefEq.respectTransparency false in
private lemma exists_milnorSequence (L : D) (F : ℕᵒᵖ ⥤ D)
    [HasProduct fun n : ℕ => F.obj (op n)] (K : D) (t : DerivedLimitTriangle F K) :
    Nonempty (MilnorSequence L F K t) := by
  let H := preadditiveCoyoneda.obj (op L)
  let c := homProductComparison L F
  let s := shiftedHomProductComparison L F
  let ec := asIso (homProductComparison L F)
  let es := asIso (shiftedHomProductComparison L F)
  let z := H.isoShiftZero ℤ
  let p := H.map t.inclusion ≫ c
  have hd : H.map (systemDelta F) ≫ c = c ≫ Rlim.delta (homSystem L F) :=
    map_systemDelta H F
  have hs : (H.shift (-1 : ℤ)).map (systemDelta F) ≫ s =
      s ≫ Rlim.delta (shiftedHomSystem L F) :=
    map_systemDelta (shiftFunctor D (-1 : ℤ) ⋙ H) F
  obtain ⟨w₀, h₀⟩ := exact_of_iso_components
    (H.homologySequence_exact₃ t.triangle t.distinguished (-1) 0 (by omega))
    (Rlim.delta (shiftedHomSystem L F)) (homConnecting L F K t)
    es es (z.app K) hs (by simp [homConnecting, H, z, es])
  obtain ⟨w₁, h₁⟩ := exact_of_iso_components
    (H.homologySequence_exact₁ t.triangle t.distinguished (-1) 0 (by omega))
    (homConnecting L F K t) p
    es (z.app K) (z.app (systemProduct F) ≪≫ ec)
    (by simp [homConnecting, H, z, es])
    (by simp [p, ec, c])
  obtain ⟨w₂, h₂⟩ := exact_of_iso_components
    (H.homologySequence_exact₂ t.triangle t.distinguished 0)
    p (Rlim.delta (homSystem L F))
    (z.app K) (z.app (systemProduct F) ≪≫ ec) (z.app (systemProduct F) ≪≫ ec)
    (by simp [p, ec, c])
    (by
      change (H.shift (0 : ℤ)).map (systemDelta F) ≫ z.hom.app (systemProduct F) ≫ c =
        (z.hom.app (systemProduct F) ≫ c) ≫ Rlim.delta (homSystem L F)
      rw [← Category.assoc, z.hom.naturality, Category.assoc, hd, Category.assoc])
  obtain ⟨w, hw⟩ := shortExact_of_exact_four w₀ w₁ w₂ h₀ h₁ h₂
  obtain ⟨e, he'⟩ := Rlim.exists_limit_iso_kernel_delta (homSystem L F)
  let i := cokernel.desc (Rlim.delta (shiftedHomSystem L F)) (homConnecting L F K t) w₀
  let q := kernel.lift (Rlim.delta (homSystem L F)) p w₂ ≫ e.inv
  have wiq : i ≫ q = 0 := by
    dsimp [i, q]
    rw [← Category.assoc, w, zero_comp]
  refine ⟨⟨i, q, ?_, ?_, wiq, ?_⟩⟩
  · exact cokernel.π_desc _ _ _
  · dsimp [q]
    rw [← he', Category.assoc, Iso.inv_hom_id_assoc, kernel.lift_ι]
  · exact ShortComplex.shortExact_of_iso
      (ShortComplex.isoMk (S₁ := ShortComplex.mk _ _ w) (Iso.refl _) (Iso.refl _) e.symm
        (by simp [i]) (by simp [q])) hw

omit [HasZeroObject D] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] in
omit [HasShift D ℤ] in
private lemma delta_eq_conjugate (J : D ⥤ Ab.{v}) [J.Additive] (F : ℕᵒᵖ ⥤ D)
    [HasProduct fun n : ℕ => F.obj (op n)]
    [IsIso (piComparison J (fun n : ℕ => F.obj (op n)))] :
    Rlim.delta (F ⋙ J) = inv (piComparison J (fun n : ℕ => F.obj (op n))) ≫
      J.map (systemDelta F) ≫ piComparison J (fun n : ℕ => F.obj (op n)) := by
  rw [map_systemDelta, IsIso.inv_hom_id_assoc]

set_option backward.isDefEq.respectTransparency false in
omit [HasZeroObject D] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] in
private lemma shiftedHomProductMap_comm [(shiftFunctor D (-1 : ℤ)).Additive] (L : D) (F G : ℕᵒᵖ ⥤ D)
    [HasProduct fun n : ℕ => F.obj (op n)]
    [HasProduct fun n : ℕ => G.obj (op n)]
    (f g : systemProduct F ⟶ systemProduct G) (h : systemDelta F ≫ g = f ≫ systemDelta G) :
    Rlim.delta (shiftedHomSystem L F) ≫ shiftedHomProductMap L F G g =
      shiftedHomProductMap L F G f ≫ Rlim.delta (shiftedHomSystem L G) := by
  let J := shiftFunctor D (-1 : ℤ) ⋙ preadditiveCoyoneda.obj (op L)
  have : IsIso (piComparison J (fun n : ℕ => F.obj (op n))) :=
    shiftedHomProductComparison_isIso L F
  have : IsIso (piComparison J (fun n : ℕ => G.obj (op n))) :=
    shiftedHomProductComparison_isIso L G
  rw [delta_eq_conjugate J F, delta_eq_conjugate J G]
  dsimp only [shiftedHomProductMap, shiftedHomProductComparison, J]
  simp only [Category.assoc, IsIso.hom_inv_id_assoc]
  change inv (piComparison J _) ≫ J.map (systemDelta F) ≫ J.map g ≫ piComparison J _ =
    inv (piComparison J _) ≫ J.map f ≫ J.map (systemDelta G) ≫ piComparison J _
  rw [← J.map_comp_assoc, h, J.map_comp_assoc]

set_option backward.isDefEq.respectTransparency false in
private lemma homConnecting_naturality (L : D) (F G : ℕᵒᵖ ⥤ D)
    [HasProduct fun n : ℕ => F.obj (op n)]
    [HasProduct fun n : ℕ => G.obj (op n)] (K M : D)
    (t : DerivedLimitTriangle F K) (tG : DerivedLimitTriangle G M)
    (a : t.triangle ⟶ tG.triangle) :
    shiftedHomProductMap L F G a.hom₃ ≫ homConnecting L G M tG =
      homConnecting L F K t ≫ (preadditiveCoyoneda.obj (op L)).map a.hom₁ := by
  let H := preadditiveCoyoneda.obj (op L)
  dsimp only [shiftedHomProductMap, homConnecting]
  simp only [Category.assoc, IsIso.hom_inv_id_assoc]
  change inv (shiftedHomProductComparison L F) ≫ (H.shift (-1 : ℤ)).map a.hom₃ ≫
      H.homologySequenceδ tG.triangle (-1) 0 _ ≫ (H.isoShiftZero ℤ).hom.app M =
    inv (shiftedHomProductComparison L F) ≫ H.homologySequenceδ t.triangle (-1) 0 _ ≫
      (H.isoShiftZero ℤ).hom.app K ≫ H.map a.hom₁
  rw [H.homologySequenceδ_naturality_assoc]
  exact congrArg (fun f => inv (shiftedHomProductComparison L F) ≫
    H.homologySequenceδ t.triangle (-1) 0 (by omega) ≫ f)
    ((H.isoShiftZero ℤ).hom.naturality a.hom₁)

set_option backward.isDefEq.respectTransparency false in
/-- **Stacks 0919.** If `K` is a derived limit of an inverse system `F` in a triangulated
category, then for every object `L` there is a short exact sequence
`0 ⟶ R¹ lim Hom(L, Fₙ[-1]) ⟶ Hom(L, K) ⟶ lim Hom(L, Fₙ) ⟶ 0`.

Here `R¹ lim` is the cokernel of the `1 - shift` endomorphism of the product of the shifted
Hom-groups. The arrows are characterized by the connecting map and the triangle inclusion.
For a morphism of defining triangles, the resulting Milnor sequences form a commutative diagram
with the induced maps on the cokernel and inverse limit. -/
@[stacks 0919]
public theorem hom_into_isDerivedLimit_shortExact
    {D : Type u} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    (F : ℕᵒᵖ ⥤ D) [HasProduct fun n : ℕ => F.obj (op n)] (K L : D)
    (hK : Pretriangulated.IsDerivedLimit F K) :
    ∃ (t : DerivedLimitTriangle F K) (S : MilnorSequence L F K t),
      ∀ (G : ℕᵒᵖ ⥤ D) [HasProduct fun n : ℕ => G.obj (op n)] (M : D)
        (tG : DerivedLimitTriangle G M) (a : t.triangle ⟶ tG.triangle)
        (b : limit (homSystem L F) ⟶ limit (homSystem L G))
        (_hb : Rlim.limitToProduct (homSystem L F) ≫ homProductMap L F G a.hom₂ =
          b ≫ Rlim.limitToProduct (homSystem L G)),
        ∃ (SG : MilnorSequence L G M tG)
          (hδ : Rlim.delta (shiftedHomSystem L F) ≫
              shiftedHomProductMap L F G a.hom₃ =
            shiftedHomProductMap L F G a.hom₂ ≫ Rlim.delta (shiftedHomSystem L G)),
          (cokernel.map (Rlim.delta (shiftedHomSystem L F))
              (Rlim.delta (shiftedHomSystem L G))
              (shiftedHomProductMap L F G a.hom₂)
              (shiftedHomProductMap L F G a.hom₃) hδ) ≫ SG.inclusion =
            S.inclusion ≫ (preadditiveCoyoneda.obj (op L)).map a.hom₁ ∧
          S.projection ≫ b =
            (preadditiveCoyoneda.obj (op L)).map a.hom₁ ≫ SG.projection := by
  obtain ⟨p, δ, ht⟩ := hK
  let t : DerivedLimitTriangle F K := ⟨p, δ, ht⟩
  obtain ⟨S⟩ := exists_milnorSequence L F K t
  refine ⟨t, S, fun G _ M tG a b hb => ?_⟩
  obtain ⟨SG⟩ := exists_milnorSequence L G M tG
  refine ⟨SG, shiftedHomProductMap_comm L F G a.hom₂ a.hom₃ a.comm₂, ?_, ?_⟩
  · rw [← cancel_epi (cokernel.π (Rlim.delta (shiftedHomSystem L F))),
      cokernel.π_desc_assoc, Category.assoc, SG.inclusion_spec,
      ← Category.assoc, S.inclusion_spec]
    exact homConnecting_naturality L F G K M t tG a
  · rw [← cancel_mono (Rlim.limitToProduct (homSystem L G)), Category.assoc, ← hb,
      ← Category.assoc, S.projection_spec]
    simp only [Category.assoc]
    rw [SG.projection_spec]
    dsimp only [homProductMap]
    simp only [IsIso.hom_inv_id_assoc]
    rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc]
    exact congrArg (fun f => (preadditiveCoyoneda.obj (op L)).map f ≫
      homProductComparison L G) a.comm₁

end Rlim.Hom

end

end


section

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Pretriangulated Limits Opposite

universe v u

namespace Rlim.Hom

-- `Rlim.product` is a plain definition, so the identifications of `Rlim.product A` with the
-- chosen product `∏ᶜ` are only reducible-transparency defeq.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- The underlying short exact sequence, forgetting its canonical-map equations and
naturality. -/
public theorem hom_into_isDerivedLimit_shortExact_basic
    (F : ℕᵒᵖ ⥤ D) [HasProduct fun n : ℕ => F.obj (op n)] (K L : D)
    (hK : Pretriangulated.IsDerivedLimit F K) :
    ∃ (i : cokernel (Rlim.delta (shiftedHomSystem L F)) ⟶
        (preadditiveCoyoneda.obj (op L)).obj K)
      (q : (preadditiveCoyoneda.obj (op L)).obj K ⟶ limit (homSystem L F))
      (w : i ≫ q = 0),
      (ShortComplex.mk i q w).ShortExact := by
  obtain ⟨_, S, _⟩ := hom_into_isDerivedLimit_shortExact F K L hK
  exact ⟨S.inclusion, S.projection, S.zero, S.shortExact⟩

end Rlim.Hom

end

end


section

noncomputable section

open CategoryTheory Limits CategoryTheory.Pretriangulated
open CategoryTheory.Pretriangulated.Opposite

namespace Rlim.Hom

-- `Rlim.product` is a plain definition, so the identifications of `Rlim.product A` with the
-- chosen product `∏ᶜ` are only reducible-transparency defeq.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private lemma exists_shortExact_of_iso
    {C : Type*} [Category* C] [HasZeroMorphisms C]
    {S : ShortComplex C} (hS : S.ShortExact) {X₁ X₂ X₃ : C}
    (e₁ : S.X₁ ≅ X₁) (e₂ : S.X₂ ≅ X₂) (e₃ : S.X₃ ≅ X₃) :
    ∃ (i : X₁ ⟶ X₂) (p : X₂ ⟶ X₃) (z : i ≫ p = 0),
      (ShortComplex.mk i p z).ShortExact ∧ i = e₁.inv ≫ S.f ≫ e₂.hom ∧
        p = e₂.inv ≫ S.g ≫ e₃.hom := by
  let i := e₁.inv ≫ S.f ≫ e₂.hom
  let p := e₂.inv ≫ S.g ≫ e₃.hom
  have z : i ≫ p = 0 := by simp [i, p, S.zero_assoc]
  refine ⟨i, p, z, ShortComplex.shortExact_of_iso ?_ hS, rfl, rfl⟩
  exact ShortComplex.isoMk e₁ e₂ e₃ (by simp [i]) (by simp [p])

universe v u

private def yonedaCoproductIsoProduct
    {D : Type u} [Category.{v} D] [Preadditive D]
    {J : Type} (F : J → D) [HasCoproduct F] (L : D) :
    (preadditiveYoneda.obj L).obj (Opposite.op (∐ F)) ≅
      ∏ᶜ (fun n ↦ (preadditiveYoneda.obj L).obj (Opposite.op (F n))) := by
  letI : PreservesLimitsOfSize.{0, 0} (preadditiveYoneda.obj L) :=
    preservesLimitsOfSize_shrink _
  exact (preadditiveYoneda.obj L).mapIso (opCoproductIsoProduct F) ≪≫
    PreservesProduct.iso (preadditiveYoneda.obj L) (fun n ↦ Opposite.op (F n))

private lemma yonedaCoproductIsoProduct_hom_π
    {D : Type u} [Category.{v} D] [Preadditive D]
    {J : Type} (F : J → D) [HasCoproduct F] (L : D) (n : J) :
    (yonedaCoproductIsoProduct F L).hom ≫
      Pi.π (fun n ↦ (preadditiveYoneda.obj L).obj (Opposite.op (F n))) n =
        (preadditiveYoneda.obj L).map (Sigma.ι F n).op := by
  simp [yonedaCoproductIsoProduct, ← Functor.map_comp]

set_option backward.isDefEq.respectTransparency false in
private lemma yonedaCoproductIsoProduct_map_difference
    {D : Type u} [Category.{v} D] [Preadditive D]
    (F : ℕ ⥤ D) [HasCoproduct F.obj] (L : D) :
    (preadditiveYoneda.obj L).map
      (Sigma.desc fun n ↦ Sigma.ι F.obj n -
        F.map (homOfLE (Nat.le_succ n)) ≫ Sigma.ι F.obj (n + 1)).op ≫
          (yonedaCoproductIsoProduct F.obj L).hom =
      (yonedaCoproductIsoProduct F.obj L).hom ≫
        Rlim.delta (F.op ⋙ preadditiveYoneda.obj L) := by
  apply Pi.hom_ext
  intro n
  dsimp only [Rlim.delta, Rlim.shift, Rlim.product,
    Functor.comp_obj, Functor.op_obj]
  simp only [Category.assoc, yonedaCoproductIsoProduct_hom_π,
    Preadditive.comp_sub, Preadditive.sub_comp, Category.comp_id, Pi.lift_comp_π]
  rw [← Functor.map_comp, ← op_comp, Sigma.ι_comp_desc]
  simp only [op_sub, Functor.map_sub, op_comp, Functor.map_comp, Functor.comp_map,
    Functor.op_map, Quiver.Hom.unop_op]
  simp only [← Category.assoc, yonedaCoproductIsoProduct_hom_π]

set_option backward.isDefEq.respectTransparency false in
/-- **Stacks 0CQX**, for a chosen defining triangle. Let `F : ℕ ⥤ D` be a system in a
pretriangulated category and let `∐ Fₙ ⟶ ∐ Fₙ ⟶ K ⟶ (∐ Fₙ)[1]` be a distinguished triangle whose
first map is `1 - fₙ`, the defining triangle of a derived colimit `K` (Derived Categories,
Definition 090Z), with second map `j` and third map `c`. For every `L` there is a short exact
sequence `0 → R¹ lim Hom(Fₙ, L[-1]) → Hom(K, L) → lim Hom(Fₙ, L) → 0` whose arrows are the ones
of the long exact `Hom(-, L)` sequence of the triangle:

* the second arrow sends `f : K ⟶ L` to the compatible family `(ιₙ ≫ j ≫ f)ₙ` of its
  restrictions along the coprojections `ιₙ ≫ j : Fₙ ⟶ K`;
* the first arrow sends the class of the family `(ιₙ ≫ g)ₙ` of a map `g : ∐ Fₙ ⟶ L[-1]` to
  `c ≫ g[1] : K ⟶ L`, through the connecting morphism `c` of the triangle and the identification
  `L[-1][1] ≅ L`.

Here `R¹ lim` is written as the cokernel of `1 - shift` on the product of the inverse system
`Hom(Fₙ, L[-1])`, using the description of derived inverse limits from Tag 07KW. -/
public theorem shortExact_map_from_homotopyColimit_triangle
    {D : Type u} [Category.{v} D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    (F : ℕ ⥤ D) [HasCoproduct F.obj] (K L : D) (j : ∐ F.obj ⟶ K)
    (c : K ⟶ (∐ F.obj)⟦(1 : ℤ)⟧)
    (hT : Triangle.mk (Sigma.desc fun n ↦ Sigma.ι F.obj n -
      F.map (homOfLE (Nat.le_succ n)) ≫ Sigma.ι F.obj (n + 1)) j c ∈ distTriang D) :
    let A₀ : ℕᵒᵖ ⥤ AddCommGrpCat.{v} := F.op ⋙ preadditiveYoneda.obj L
    let A₁ : ℕᵒᵖ ⥤ AddCommGrpCat.{v} := F.op ⋙ preadditiveYoneda.obj (L⟦(-1 : ℤ)⟧)
    let P₁ : AddCommGrpCat.{v} := ∏ᶜ fun n : ℕ ↦ A₁.obj (Opposite.op n)
    let shift₁ : P₁ ⟶ P₁ := Pi.lift fun n ↦
      Pi.π (fun n : ℕ ↦ A₁.obj (Opposite.op n)) (n + 1) ≫
        A₁.map (homOfLE (Nat.le_succ n)).op
    let δ₁ : P₁ ⟶ P₁ := 𝟙 P₁ - shift₁
    let H : AddCommGrpCat.{v} := (preadditiveYoneda.obj L).obj (Opposite.op K)
    ∃ (i : cokernel δ₁ ⟶ H) (r : H ⟶ limit A₀) (z : i ≫ r = 0),
      (ShortComplex.mk i r z).ShortExact ∧
      (∀ (f : K ⟶ L) (n : ℕ),
        limit.π A₀ (Opposite.op n) (r f) = Sigma.ι F.obj n ≫ j ≫ f) ∧
      ∀ (g : ∐ F.obj ⟶ L⟦(-1 : ℤ)⟧) (x : P₁),
        (∀ n : ℕ, Pi.π (fun n : ℕ ↦ A₁.obj (Opposite.op n)) n x = Sigma.ι F.obj n ≫ g) →
          i (cokernel.π δ₁ x) =
            c ≫ g⟦(1 : ℤ)⟧' ≫ (shiftFunctorCompIsoId D (-1 : ℤ) 1 (by norm_num)).hom.app L := by
  classical
  dsimp only
  let a : ∐ F.obj ⟶ ∐ F.obj := Sigma.desc fun n ↦ Sigma.ι F.obj n -
    F.map (homOfLE (Nat.le_succ n)) ≫ Sigma.ι F.obj (n + 1)
  let T := (triangleOpEquivalence D).functor.obj (Opposite.op (Triangle.mk a j c))
  have hT' : T ∈ distTriang Dᵒᵖ := op_distinguished _ hT
  let Y := preadditiveYoneda.obj L
  obtain ⟨z, hS⟩ := shortExact_of_exact_four
    (Y.comp_homologySequenceδ T hT' (-1) 0 (by decide))
    (Y.homologySequenceδ_comp T hT' (-1) 0 (by decide))
    (Y.homologySequence_comp T hT' 0)
    (Y.homologySequence_exact₃ T hT' (-1) 0 (by decide))
    (Y.homologySequence_exact₁ T hT' (-1) 0 (by decide))
    (Y.homologySequence_exact₂ T hT' 0)
  let A₀ := F.op ⋙ preadditiveYoneda.obj L
  let A₁ := F.op ⋙ preadditiveYoneda.obj (L⟦(-1 : ℤ)⟧)
  let e₁ := yonedaCoproductIsoProduct F.obj (L⟦(-1 : ℤ)⟧)
  let e₀ := (Y.isoShiftZero ℤ).app (Opposite.op (∐ F.obj)) ≪≫
    yonedaCoproductIsoProduct F.obj L
  have w₁ : (Y.shift (-1 : ℤ)).map T.mor₂ ≫ e₁.hom =
      e₁.hom ≫ Rlim.delta A₁ :=
    yonedaCoproductIsoProduct_map_difference F (L⟦(-1 : ℤ)⟧)
  have w₀ : (Y.shift (0 : ℤ)).map T.mor₂ ≫ e₀.hom =
      e₀.hom ≫ Rlim.delta A₀ := by
    change (Y.shift 0).map a.op ≫ ((Y.isoShiftZero ℤ).hom.app _ ≫
      (yonedaCoproductIsoProduct F.obj L).hom) =
        ((Y.isoShiftZero ℤ).hom.app _ ≫ (yonedaCoproductIsoProduct F.obj L).hom) ≫ _
    rw [← Category.assoc, (Y.isoShiftZero ℤ).hom.naturality a.op, Category.assoc,
      yonedaCoproductIsoProduct_map_difference F L]
    simp only [A₀, Category.assoc]
  obtain ⟨eLim, heLim⟩ := Rlim.limit_kernel_iso A₀
  let E₁ := cokernel.mapIso _ (Rlim.delta A₁) e₁ e₁ w₁
  let E₂ := (Y.isoShiftZero ℤ).app (Opposite.op K)
  let E₃ := kernel.mapIso _ (Rlim.delta A₀) e₀ e₀ w₀ ≪≫ eLim.symm
  obtain ⟨i, r, zir, hir, hi, hr⟩ := exists_shortExact_of_iso hS E₁ E₂ E₃
  refine ⟨i, r, zir, hir, fun f n ↦ ?_, fun g x hx ↦ ?_⟩
  · have hπ : r ≫ limit.π A₀ (Opposite.op n) = Y.map (Sigma.ι F.obj n ≫ j).op := by
      rw [hr, ← heLim n]
      simp only [E₂, E₃, e₀, Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc,
        kernel.mapIso, kernel.lift_ι_assoc, Iso.app_hom, Iso.app_inv]
      rw [show (yonedaCoproductIsoProduct F.obj L).hom ≫
          Pi.π (fun n ↦ A₀.obj (Opposite.op n)) n = Y.map (Sigma.ι F.obj n).op from
        yonedaCoproductIsoProduct_hom_π F.obj L n]
      have hnat := (Y.isoShiftZero ℤ).hom.naturality j.op
      change (Y.isoShiftZero ℤ).inv.app (Opposite.op K) ≫ (Y.shift 0).map j.op ≫
        (Y.isoShiftZero ℤ).hom.app (Opposite.op (∐ F.obj)) ≫ Y.map (Sigma.ι F.obj n).op = _
      rw [reassoc_of% hnat, Iso.inv_hom_id_app_assoc, ← Functor.map_comp]
      rfl
    exact (ConcreteCategory.congr_hom hπ f).trans (Category.assoc _ _ _)
  · have hx' : x = e₁.hom g := by
      refine Concrete.limit_ext _ _ _ fun ⟨n⟩ ↦ (hx n).trans ?_
      exact (ConcreteCategory.congr_hom
        (yonedaCoproductIsoProduct_hom_π F.obj (L⟦(-1 : ℤ)⟧) n) g).symm
    have hπ : e₁.hom ≫ cokernel.π (Rlim.delta A₁) ≫ i =
        Y.homologySequenceδ T (-1) 0 (by decide) ≫ E₂.hom := by
      rw [hi]
      simp only [E₁, cokernel.mapIso, cokernel.map, cokernel.π_desc_assoc, Category.assoc,
        Iso.hom_inv_id_assoc]
    rw [hx']
    refine (ConcreteCategory.congr_hom hπ g).trans ?_
    have hδ := preadditiveYoneda_homologySequenceδ_apply (Triangle.mk a j c) (-1) 0
      (by decide) g
    refine (congrArg (fun y : K ⟶ L⟦(0 : ℤ)⟧ ↦ y ≫ (shiftFunctorZero D ℤ).hom.app L) hδ).trans ?_
    simp [shiftFunctorCompIsoId]

/-- **Stacks 0CQX.** Let `F : ℕ ⥤ D` be a system in a pretriangulated category and let `K` be a
derived colimit of `F`. For every `L` there is a short exact sequence
`0 → R¹ lim Hom(Fₙ, L[-1]) → Hom(K, L) → lim Hom(Fₙ, L) → 0` coming from a defining triangle
`∐ Fₙ ⟶ ∐ Fₙ ⟶ K ⟶ (∐ Fₙ)[1]` of `K`, with second map `j` and third map `c`: the second arrow is
restriction along the coprojections `ιₙ ≫ j : Fₙ ⟶ K`, and the first arrow sends the class of
the family `(ιₙ ≫ g)ₙ` of a map `g : ∐ Fₙ ⟶ L[-1]` to `c ≫ g[1]`, the image of `g` under the
connecting morphism of the triangle. See `shortExact_map_from_homotopyColimit_triangle` for the
same statement for any chosen defining triangle.

Here `R¹ lim` is written as the cokernel of `1 - shift` on the product of the inverse system
`Hom(Fₙ, L[-1])`, using the description of derived inverse limits from Tag 07KW. -/
@[stacks 0CQX]
public theorem shortExact_map_from_isHomotopyColimit
    {D : Type u} [Category.{v} D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    (F : ℕ ⥤ D) [HasCoproduct F.obj] (K L : D) (hK : IsHomotopyColimit F K) :
    let A₀ : ℕᵒᵖ ⥤ AddCommGrpCat.{v} := F.op ⋙ preadditiveYoneda.obj L
    let A₁ : ℕᵒᵖ ⥤ AddCommGrpCat.{v} := F.op ⋙ preadditiveYoneda.obj (L⟦(-1 : ℤ)⟧)
    let P₁ : AddCommGrpCat.{v} := ∏ᶜ fun n : ℕ ↦ A₁.obj (Opposite.op n)
    let shift₁ : P₁ ⟶ P₁ := Pi.lift fun n ↦
      Pi.π (fun n : ℕ ↦ A₁.obj (Opposite.op n)) (n + 1) ≫
        A₁.map (homOfLE (Nat.le_succ n)).op
    let δ₁ : P₁ ⟶ P₁ := 𝟙 P₁ - shift₁
    let H : AddCommGrpCat.{v} := (preadditiveYoneda.obj L).obj (Opposite.op K)
    ∃ (j : ∐ F.obj ⟶ K) (c : K ⟶ (∐ F.obj)⟦(1 : ℤ)⟧),
      Triangle.mk (Sigma.desc fun n ↦ Sigma.ι F.obj n -
        F.map (homOfLE (Nat.le_succ n)) ≫ Sigma.ι F.obj (n + 1)) j c ∈ distTriang D ∧
      ∃ (i : cokernel δ₁ ⟶ H) (r : H ⟶ limit A₀) (z : i ≫ r = 0),
        (ShortComplex.mk i r z).ShortExact ∧
        (∀ (f : K ⟶ L) (n : ℕ),
          limit.π A₀ (Opposite.op n) (r f) = Sigma.ι F.obj n ≫ j ≫ f) ∧
        ∀ (g : ∐ F.obj ⟶ L⟦(-1 : ℤ)⟧) (x : P₁),
          (∀ n : ℕ, Pi.π (fun n : ℕ ↦ A₁.obj (Opposite.op n)) n x = Sigma.ι F.obj n ≫ g) →
            i (cokernel.π δ₁ x) =
              c ≫ g⟦(1 : ℤ)⟧' ≫
                (shiftFunctorCompIsoId D (-1 : ℤ) 1 (by norm_num)).hom.app L := by
  obtain ⟨j, c, hT⟩ := hK
  exact ⟨j, c, hT, shortExact_map_from_homotopyColimit_triangle F K L j c hT⟩

/-- The bare short exact sequence `0 → R¹ lim Hom(Fₙ, L[-1]) → Hom(K, L) → lim Hom(Fₙ, L) → 0`
for a derived colimit `K` of a system `F`, forgetting which maps realize it. The statement with
the maps identified through a defining triangle is `shortExact_map_from_isHomotopyColimit`
(Tag 0CQX). -/
public theorem exists_shortExact_map_from_isHomotopyColimit
    {D : Type u} [Category.{v} D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    (F : ℕ ⥤ D) [HasCoproduct F.obj] (K L : D) (hK : IsHomotopyColimit F K) :
    let A₀ : ℕᵒᵖ ⥤ AddCommGrpCat.{v} := F.op ⋙ preadditiveYoneda.obj L
    let A₁ : ℕᵒᵖ ⥤ AddCommGrpCat.{v} := F.op ⋙ preadditiveYoneda.obj (L⟦(-1 : ℤ)⟧)
    let P₁ : AddCommGrpCat.{v} := ∏ᶜ fun n : ℕ ↦ A₁.obj (Opposite.op n)
    let shift₁ : P₁ ⟶ P₁ := Pi.lift fun n ↦
      Pi.π (fun n : ℕ ↦ A₁.obj (Opposite.op n)) (n + 1) ≫
        A₁.map (homOfLE (Nat.le_succ n)).op
    let δ₁ : P₁ ⟶ P₁ := 𝟙 P₁ - shift₁
    let H : AddCommGrpCat.{v} := (preadditiveYoneda.obj L).obj (Opposite.op K)
    ∃ (i : cokernel δ₁ ⟶ H) (p : H ⟶ limit A₀) (z : i ≫ p = 0),
      (ShortComplex.mk i p z).ShortExact := by
  obtain ⟨_, _, _, i, r, z, h, _⟩ := shortExact_map_from_isHomotopyColimit F K L hK
  exact ⟨i, r, z, h⟩

end Rlim.Hom

end

end
