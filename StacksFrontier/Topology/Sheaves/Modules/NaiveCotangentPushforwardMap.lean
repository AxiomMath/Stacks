module

public import StacksFrontier.Topology.Sheaves.Modules.NaiveCotangentInverseImage

/-!
# The maps of conormal sequences along a morphism into a pushforward

Let `f : Y ⟶ X` be a continuous map, let `φ₁ : A₁ ⟶ B` be a presentation of a sheaf of
commutative rings on `X` over `R` and let `φ₂ : A₂ ⟶ B₂` be a presentation of a sheaf of
commutative rings on `Y` over `R₂`. Morphisms `ψ : A₁ ⟶ f_*A₂`, `b : B ⟶ f_*B₂` and
`ρ : R ⟶ f_*R₂` compatible with the two presentations induce maps from the terms of the conormal
sequence of `φ₁` to the pushforwards of the terms of the conormal sequence of `φ₂`:

`I₁/I₁² ⟶ f_*(I₂/I₂²)` and `B ⊗[A₁] Ω[A₁/R] ⟶ f_*(B₂ ⊗[A₂] Ω[A₂/R₂])`,

linear over `b`. This is the construction of
`StacksFrontier/Topology/Sheaves/Modules/NaiveCotangentInverseImage.lean`, where `B₂` is the inverse
image `f⁻¹B` and `b` the unit, carried out for an arbitrary `b`: for a morphism of ringed spaces
`g : Y ⟶ X` the case `B = 𝒪_X`, `B₂ = 𝒪_Y`, `b = g^♯` produces the maps of naive cotangent
complexes `𝖭𝖫_{X/S} ⟶ g_*𝖭𝖫_{Y/S}` adjoint to the canonical `g^*𝖭𝖫_{X/S} ⟶ 𝖭𝖫_{Y/S}`.

## Main definitions

* `Stacks.Sites.Conormal.pushforwardRingHom`: `b : B ⟶ f_*B₂` as a morphism of sheaves of rings,
  the morphism `f_*` on sheaves of modules is taken along.
* `Stacks.Sites.Conormal.conormalSheafMapPush`: the map `I₁/I₁² ⟶ f_*(I₂/I₂²)`.
* `Stacks.Sites.Conormal.tensorSheafMapPush`: the map
  `B ⊗[A₁] Ω[A₁/R] ⟶ f_*(B₂ ⊗[A₂] Ω[A₂/R₂])`.

## Main results

* `Stacks.Sites.Conormal.conormalSheafMapPush_conormalClass` and
  `Stacks.Sites.Conormal.tensorSheafMapPush_tensorDifferential`: the conormal class of `s` goes
  to the conormal class of `ψ s`, and `1 ⊗ d s` to `1 ⊗ d (ψ s)`.
* `Stacks.Sites.Conormal.conormalSequence_f_naturality_push`: the two maps commute with the
  left-hand maps of the conormal sequences.

## References

* [Stacks Project, Tag 08TM](https://stacks.math.columbia.edu/tag/08TM)
* [Stacks Project, Tag 0E1Z](https://stacks.math.columbia.edu/tag/0E1Z)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite TensorProduct

universe u

namespace Stacks.Sites.Conormal

section ChangeOfPresentationPush

variable {X Y : TopCat.{u}} (f : Y ⟶ X)

/-- A morphism `b : B ⟶ f_*B₂` of sheaves of commutative rings, after forgetting commutativity: the
morphism of sheaves of rings that `f_*` on sheaves of modules is taken along. -/
noncomputable def pushforwardRingHom {B : TopCat.Sheaf CommRingCat.{u} X}
    {B₂ : TopCat.Sheaf CommRingCat.{u} Y}
    (b : B ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} f).obj B₂) :
    Stacks.SheafOfModules.Tensor.ringSheaf B ⟶
      ((Opens.map f).sheafPushforwardContinuous RingCat.{u}
        (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)).obj
        (Stacks.SheafOfModules.Tensor.ringSheaf B₂) :=
  ObjectProperty.homMk (Functor.whiskerRight b.hom (forget₂ CommRingCat.{u} RingCat.{u}))

variable (B : TopCat.Sheaf CommRingCat.{u} X) (B₂ : TopCat.Sheaf CommRingCat.{u} Y)
  (b : B ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} f).obj B₂)
  {A₁ : TopCat.Sheaf CommRingCat.{u} X} {A₂ : TopCat.Sheaf CommRingCat.{u} Y}
  (φ₁ : A₁ ⟶ B) (φ₂ : A₂ ⟶ B₂)
  (ψ : A₁ ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} f).obj A₂)

variable (hψ : ψ ≫ (TopCat.Sheaf.pushforward CommRingCat.{u} f).map φ₂ = φ₁ ≫ b)

include hψ in
/-- Compatibility of `ψ` with the two presentations, on sections: the image of a section `s` of
`A₁` under `φ₂ ∘ ψ` is the inverse-image section of `φ₁ s`. -/
theorem sectionsMapPush_comp_apply (U : (Opens X)ᵒᵖ) (s : A₁.obj.obj U) :
    (φ₂.hom.app ((Opens.map f).op.obj U)).hom ((sectionsMapAlong f ψ U).hom s) =
      (b.hom.app U).hom
        ((φ₁.hom.app U).hom s) :=
  congrArg (fun t : A₁ ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} f).obj
      B₂ ↦ ((t.hom.app U).hom s)) hψ

/-- **`ψ` carries the kernel ideal of `φ₁` into the kernel ideal of `φ₂`**, for presentations
`φ₁ : A₁ ⟶ B` and `φ₂ : A₂ ⟶ B₂` compatible with `ψ : A₁ ⟶ f_*A₂` over an arbitrary morphism
`b : B ⟶ f_*B₂`. The case `B₂ = f⁻¹B`, with `b` the unit of `f⁻¹ ⊣ f_*`, is
`Stacks.Sites.Conormal.kernelIdeal_le_comap_sectionsMapAlong`. -/
theorem kernelIdeal_le_comap_sectionsMapPush (B : TopCat.Sheaf CommRingCat.{u} X)
    (B₂ : TopCat.Sheaf CommRingCat.{u} Y)
    (b : B ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} f).obj B₂)
    {A₁ : TopCat.Sheaf CommRingCat.{u} X} {A₂ : TopCat.Sheaf CommRingCat.{u} Y} (φ₁ : A₁ ⟶ B)
    (φ₂ : A₂ ⟶ B₂) (ψ : A₁ ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} f).obj A₂)
    (hψ : ψ ≫ (TopCat.Sheaf.pushforward CommRingCat.{u} f).map φ₂ = φ₁ ≫ b) (U : (Opens X)ᵒᵖ) :
    kernelIdeal φ₁.hom U ≤
      (kernelIdeal φ₂.hom ((Opens.map f).op.obj U)).comap (sectionsMapAlong f ψ U).hom := by
  intro s hs
  refine (sectionsMapPush_comp_apply f B B₂ b φ₁ φ₂ ψ hψ U s).trans ?_
  exact (congrArg ((b.hom.app U).hom) hs).trans (map_zero _)

include hψ in
/-- The induced map on quotients is compatible with the inclusions into `B` and `f⁻¹B`. -/
theorem quotientToTarget_quotientMapPush (U : (Opens X)ᵒᵖ)
    (r : (quotientPresheaf φ₁.hom).obj U) :
    (quotientToTarget φ₂.hom).app ((Opens.map f).op.obj U)
        (Ideal.quotientMap (kernelIdeal φ₂.hom ((Opens.map f).op.obj U))
          (sectionsMapAlong f ψ U).hom
          (kernelIdeal_le_comap_sectionsMapPush f B B₂ b φ₁ φ₂ ψ hψ U) r) =
      ((pushforwardRingHom f b).hom.app U).hom ((quotientToTarget φ₁.hom).app U r) := by
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
  exact sectionsMapPush_comp_apply f B B₂ b φ₁ φ₂ ψ hψ U r

include hψ in
/-- The induced map `A₁(U)/I₁(U) → A₂(f⁻¹U)/I₂(f⁻¹U)`, semilinear over `ψ`. -/
noncomputable def quotientMapPushₛₗ (U : (Opens X)ᵒᵖ) :
    (A₁.obj.obj U ⧸ kernelIdeal φ₁.hom U) →ₛₗ[(sectionsMapAlong f ψ U).hom]
      (A₂.obj.obj ((Opens.map f).op.obj U) ⧸ kernelIdeal φ₂.hom ((Opens.map f).op.obj U)) where
  toFun := Ideal.quotientMap _ (sectionsMapAlong f ψ U).hom
    (kernelIdeal_le_comap_sectionsMapPush f B B₂ b φ₁ φ₂ ψ hψ U)
  map_add' := map_add (Ideal.quotientMap _ (sectionsMapAlong f ψ U).hom
    (kernelIdeal_le_comap_sectionsMapPush f B B₂ b φ₁ φ₂ ψ hψ U))
  map_smul' r x := by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    change Ideal.Quotient.mk _ ((sectionsMapAlong f ψ U).hom (r * x)) =
      Ideal.Quotient.mk _ ((sectionsMapAlong f ψ U).hom r * (sectionsMapAlong f ψ U).hom x)
    exact congrArg (Ideal.Quotient.mk (kernelIdeal φ₂.hom ((Opens.map f).op.obj U)))
      (map_mul (sectionsMapAlong f ψ U).hom r x)

include hψ in
/-- The induced map on quotients commutes with the restriction maps. -/
theorem quotientMapPushₛₗ_naturality {U V : (Opens X)ᵒᵖ} (i : U ⟶ V)
    (y : (quotientPresheaf φ₁.hom).obj U) :
    quotientMapPushₛₗ f B B₂ b φ₁ φ₂ ψ hψ V ((quotientPresheaf φ₁.hom).map i y) =
      (quotientPresheaf φ₂.hom).map ((Opens.map f).op.map i)
        (quotientMapPushₛₗ f B B₂ b φ₁ φ₂ ψ hψ U y) := by
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  show Ideal.Quotient.mk _ ((sectionsMapAlong f ψ V).hom ((A₁.obj.map i).hom y)) =
    Ideal.Quotient.mk _
      ((A₂.obj.map ((Opens.map f).op.map i)).hom ((sectionsMapAlong f ψ U).hom y))
  exact congrArg (Ideal.Quotient.mk (kernelIdeal φ₂.hom ((Opens.map f).op.obj V)))
    (sectionsMapAlong_naturality f ψ i y)

include hψ in
/-- The induced map on conormal modules commutes with the restriction maps. -/
theorem cotangentMapPush_naturality {U V : (Opens X)ᵒᵖ} (i : U ⟶ V)
    (c : (conormalPresheaf φ₁.hom).obj U) :
    cotangentMap (kernelIdeal φ₁.hom V) (kernelIdeal φ₂.hom ((Opens.map f).op.obj V))
        (sectionsMapAlong f ψ V).hom
        (kernelIdeal_le_comap_sectionsMapPush f B B₂ b φ₁ φ₂ ψ hψ V)
        ((conormalPresheaf φ₁.hom).map i c) =
      (conormalPresheaf φ₂.hom).map ((Opens.map f).op.map i)
        (cotangentMap (kernelIdeal φ₁.hom U) (kernelIdeal φ₂.hom ((Opens.map f).op.obj U))
          (sectionsMapAlong f ψ U).hom
          (kernelIdeal_le_comap_sectionsMapPush f B B₂ b φ₁ φ₂ ψ hψ U) c) := by
  obtain ⟨c, rfl⟩ := (kernelIdeal φ₁.hom U).toCotangent_surjective c
  show (kernelIdeal φ₂.hom _).toCotangent
      ⟨(sectionsMapAlong f ψ V).hom ((A₁.obj.map i).hom (c : A₁.obj.obj U)), _⟩ =
    (kernelIdeal φ₂.hom _).toCotangent
      ⟨(A₂.obj.map ((Opens.map f).op.map i)).hom
        ((sectionsMapAlong f ψ U).hom (c : A₁.obj.obj U)), _⟩
  congr 1
  ext
  exact sectionsMapAlong_naturality f ψ i (c : A₁.obj.obj U)

variable [Presheaf.IsLocallySurjective (Opens.grothendieckTopology X) φ₁.hom]
  [Presheaf.IsLocallySurjective (Opens.grothendieckTopology Y) φ₂.hom]

include hψ in
/-- **The comparison of conormal sheaves along `f`.** The map `I₁/I₁² ⟶ f_*(I₂/I₂²)` sending the
conormal class of a section `s` of `I₁` to the conormal class of `ψ s`. -/
noncomputable def conormalSheafMapPush :
    conormalSheaf.{u, u, u, u} (Opens.grothendieckTopology X) A₁ B φ₁ ⟶
      (_root_.SheafOfModules.pushforward.{u} (pushforwardRingHom f b)).obj
        (conormalSheaf.{u, u, u, u} (Opens.grothendieckTopology Y) A₂
          B₂ φ₂) := by
  refine sheafifyLiftDesc.{u, u, u, u} (Opens.grothendieckTopology X) A₁ B φ₁
    (conormalPresheaf φ₁.hom) _
    (fun U c ↦ toAssociatedModule.{u, u, u, u} (Opens.grothendieckTopology Y) A₂
      B₂ φ₂
      (conormalPresheaf φ₂.hom) ((Opens.map f).op.obj U)
      (cotangentMap (kernelIdeal φ₁.hom U) (kernelIdeal φ₂.hom ((Opens.map f).op.obj U))
        (sectionsMapAlong f ψ U).hom
        (kernelIdeal_le_comap_sectionsMapPush f B B₂ b φ₁ φ₂ ψ hψ U) c)) ?_ ?_ ?_
  · intro U c c'
    exact (congrArg (toAssociatedModule.{u, u, u, u} (Opens.grothendieckTopology Y) A₂ _ φ₂
        (conormalPresheaf φ₂.hom) ((Opens.map f).op.obj U))
      (map_add (cotangentMap (kernelIdeal φ₁.hom U)
        (kernelIdeal φ₂.hom ((Opens.map f).op.obj U)) (sectionsMapAlong f ψ U).hom
        (kernelIdeal_le_comap_sectionsMapPush f B B₂ b φ₁ φ₂ ψ hψ U)) c c')).trans
      (toAssociatedModule_add.{u, u, u, u} (Opens.grothendieckTopology Y) A₂ _ φ₂
        (conormalPresheaf φ₂.hom) _ _ _)
  · intro U r c
    refine (congrArg (toAssociatedModule.{u, u, u, u} (Opens.grothendieckTopology Y) A₂ _ φ₂
        (conormalPresheaf φ₂.hom) ((Opens.map f).op.obj U))
      (map_smulₛₗ (cotangentMap (kernelIdeal φ₁.hom U)
        (kernelIdeal φ₂.hom ((Opens.map f).op.obj U)) (sectionsMapAlong f ψ U).hom
        (kernelIdeal_le_comap_sectionsMapPush f B B₂ b φ₁ φ₂ ψ hψ U)) r c)).trans ?_
    refine (toAssociatedModule_smul.{u, u, u, u} (Opens.grothendieckTopology Y) A₂ _ φ₂
      (conormalPresheaf φ₂.hom) _ _ _).trans ?_
    exact congrArg (fun s : (Stacks.SheafOfModules.Tensor.ringSheaf
        B₂).obj.obj
        ((Opens.map f).op.obj U) ↦ s • toAssociatedModule.{u, u, u, u}
          (Opens.grothendieckTopology Y) A₂ _ φ₂ (conormalPresheaf φ₂.hom)
          ((Opens.map f).op.obj U)
          (cotangentMap (kernelIdeal φ₁.hom U) (kernelIdeal φ₂.hom ((Opens.map f).op.obj U))
            (sectionsMapAlong f ψ U).hom
            (kernelIdeal_le_comap_sectionsMapPush f B B₂ b φ₁ φ₂ ψ hψ U) c))
      (quotientToTarget_quotientMapPush f B B₂ b φ₁ φ₂ ψ hψ U r)
  · intro U V i c
    exact (congrArg (toAssociatedModule.{u, u, u, u} (Opens.grothendieckTopology Y) A₂ _ φ₂
        (conormalPresheaf φ₂.hom) ((Opens.map f).op.obj V))
      (cotangentMapPush_naturality f B B₂ b φ₁ φ₂ ψ hψ i c)).trans
      (toAssociatedModule_map.{u, u, u, u} (Opens.grothendieckTopology Y) A₂ _ φ₂
        (conormalPresheaf φ₂.hom) ((Opens.map f).op.map i) _)

include hψ in
/-- On presheaf sections the comparison of conormal sheaves is the induced map on conormal
modules. -/
theorem conormalSheafMapPush_toAssociatedModule (U : (Opens X)ᵒᵖ)
    (c : (conormalPresheaf φ₁.hom).obj U) :
    ((conormalSheafMapPush f B B₂ b φ₁ φ₂ ψ hψ).val.app U)
        (toAssociatedModule.{u, u, u, u} (Opens.grothendieckTopology X) A₁ B φ₁
          (conormalPresheaf φ₁.hom) U c) =
      toAssociatedModule.{u, u, u, u} (Opens.grothendieckTopology Y) A₂
        B₂ φ₂ (conormalPresheaf φ₂.hom)
        ((Opens.map f).op.obj U)
        (cotangentMap (kernelIdeal φ₁.hom U) (kernelIdeal φ₂.hom ((Opens.map f).op.obj U))
          (sectionsMapAlong f ψ U).hom
          (kernelIdeal_le_comap_sectionsMapPush f B B₂ b φ₁ φ₂ ψ hψ U) c) := by
  apply sheafifyLiftDesc_toAssociatedModule.{u, u, u, u}

variable (R : TopCat.Sheaf CommRingCat.{u} X) (R₂ : TopCat.Sheaf CommRingCat.{u} Y)
  (a₁ : R ⟶ A₁) (a₂ : R₂ ⟶ A₂)

include hψ in
/-- **The comparison of conormal sheaves carries conormal classes to conormal classes.** The
conormal class of a section `s` of `I₁` goes to the conormal class of `ψ s`. -/
theorem conormalSheafMapPush_conormalClass (U : (Opens X)ᵒᵖ) (s : kernelIdeal φ₁.hom U) :
    ((conormalSheafMapPush f B B₂ b φ₁ φ₂ ψ hψ).val.app U)
        (conormalClass.{u, u, u, u} (Opens.grothendieckTopology X) R A₁ B a₁ φ₁ U s) =
      conormalClass.{u, u, u, u} (Opens.grothendieckTopology Y)
        R₂ A₂
        B₂ a₂ φ₂ ((Opens.map f).op.obj U)
        ⟨(sectionsMapAlong f ψ U).hom s,
          kernelIdeal_le_comap_sectionsMapPush f B B₂ b φ₁ φ₂ ψ hψ U s.2⟩ :=
  conormalSheafMapPush_toAssociatedModule f B B₂ b φ₁ φ₂ ψ hψ U _

/-! #### The comparison on the scalar extension of the differentials -/

variable (ρ : R ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} f).obj R₂)
  (ha : a₁ ≫ ψ = ρ ≫ (TopCat.Sheaf.pushforward CommRingCat.{u} f).map a₂)

include ha in
/-- The commutative square of rings over an open `U` of `X` inducing the map on relative
differentials. -/
theorem differentialsSquarePush (U : (Opens X)ᵒᵖ) :
    ((ρ).hom.app U) ≫
        a₂.hom.app ((Opens.map f).op.obj U) =
      a₁.hom.app U ≫ sectionsMapAlong f ψ U :=
  (congrArg (fun t : R ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} f).obj A₂ ↦ t.hom.app U)
    ha).symm

include ha in
/-- The map `Ω[A₁(U)/R(U)] → Ω[A₂(f⁻¹U)/(f⁻¹R)(f⁻¹U)]` induced by `ψ`, semilinear over `ψ`. -/
noncomputable def differentialsMapPush (U : (Opens X)ᵒᵖ) :
    (differentialsPresheaf a₁.hom).obj U →ₛₗ[(sectionsMapAlong f ψ U).hom]
      (differentialsPresheaf a₂.hom).obj ((Opens.map f).op.obj U) where
  toFun := CommRingCat.KaehlerDifferential.map (g' := sectionsMapAlong f ψ U)
    (differentialsSquarePush f ψ R R₂ a₁ a₂ ρ ha U)
  map_add' := map_add _
  map_smul' := (CommRingCat.KaehlerDifferential.map (g' := sectionsMapAlong f ψ U)
    (differentialsSquarePush f ψ R R₂ a₁ a₂ ρ ha U)).hom.map_smul

include ha in
/-- The map on relative differentials sends `d s` to `d (ψ s)`. -/
@[simp]
theorem differentialsMapPush_d (U : (Opens X)ᵒᵖ) (s : A₁.obj.obj U) :
    differentialsMapPush f ψ R R₂ a₁ a₂ ρ ha U (CommRingCat.KaehlerDifferential.d s) =
      CommRingCat.KaehlerDifferential.d ((sectionsMapAlong f ψ U).hom s) :=
  CommRingCat.KaehlerDifferential.map_d (differentialsSquarePush f ψ R R₂ a₁ a₂ ρ ha U) s

include ha in
/-- The map on relative differentials commutes with the restriction maps. -/
theorem differentialsMapPush_naturality {U V : (Opens X)ᵒᵖ} (i : U ⟶ V)
    (ω : (differentialsPresheaf a₁.hom).obj U) :
    differentialsMapPush f ψ R R₂ a₁ a₂ ρ ha V ((differentialsPresheaf a₁.hom).map i ω) =
      (differentialsPresheaf a₂.hom).map ((Opens.map f).op.map i)
        (differentialsMapPush f ψ R R₂ a₁ a₂ ρ ha U ω) := by
  show differentialsMapPush f ψ R R₂ a₁ a₂ ρ ha V
      ((differentialsPresheaf a₁.hom).restrictₛₗ i ω) =
    (differentialsPresheaf a₂.hom).restrictₛₗ ((Opens.map f).op.map i)
      (differentialsMapPush f ψ R R₂ a₁ a₂ ρ ha U ω)
  let := (a₁.hom.app U).hom.toAlgebra
  have mem : ω ∈ Submodule.span (A₁.obj.obj U)
      (Set.range (KaehlerDifferential.D (R.obj.obj U) (A₁.obj.obj U))) := by
    rw [KaehlerDifferential.span_range_derivation]; trivial
  induction mem using Submodule.span_induction with
  | mem s hs =>
      obtain ⟨s, rfl⟩ := hs
      show differentialsMapPush f ψ R R₂ a₁ a₂ ρ ha V ((differentialsPresheaf a₁.hom).map i
          (CommRingCat.KaehlerDifferential.d (f := a₁.hom.app U) s)) =
        (differentialsPresheaf a₂.hom).map ((Opens.map f).op.map i)
          (differentialsMapPush f ψ R R₂ a₁ a₂ ρ ha U
            (CommRingCat.KaehlerDifferential.d (f := a₁.hom.app U) s))
      have h₁ : (differentialsPresheaf a₁.hom).map i (CommRingCat.KaehlerDifferential.d s) =
          CommRingCat.KaehlerDifferential.d (f := a₁.hom.app V) ((A₁.obj.map i).hom s) :=
        PresheafOfModules.DifferentialsConstruction.relativeDifferentials'_map_d a₁.hom i s
      have h₂ : (differentialsPresheaf a₂.hom).map ((Opens.map f).op.map i)
            (CommRingCat.KaehlerDifferential.d (f := a₂.hom.app ((Opens.map f).op.obj U))
              ((sectionsMapAlong f ψ U).hom s)) =
          CommRingCat.KaehlerDifferential.d (f := a₂.hom.app ((Opens.map f).op.obj V))
            ((A₂.obj.map ((Opens.map f).op.map i)).hom ((sectionsMapAlong f ψ U).hom s)) :=
        PresheafOfModules.DifferentialsConstruction.relativeDifferentials'_map_d a₂.hom
          ((Opens.map f).op.map i) _
      rw [h₁, differentialsMapPush_d, differentialsMapPush_d, h₂]
      exact congrArg CommRingCat.KaehlerDifferential.d (sectionsMapAlong_naturality f ψ i s)
  | zero => rw [map_zero, map_zero, map_zero, map_zero]
  | add x y hx hy ihx ihy => rw [map_add, map_add, map_add, map_add, ihx, ihy]
  | smul r ω hω ih =>
      rw [map_smulₛₗ, map_smulₛₗ, ih, map_smulₛₗ, map_smulₛₗ]
      exact congrArg (fun s : A₂.obj.obj ((Opens.map f).op.obj V) ↦ s •
        (differentialsPresheaf a₂.hom).restrictₛₗ ((Opens.map f).op.map i)
          (differentialsMapPush f ψ R R₂ a₁ a₂ ρ ha U ω))
        (sectionsMapAlong_naturality f ψ i r)

include hψ ha in
/-- The induced map `(A₁(U)/I₁(U)) ⊗[A₁(U)] Ω[A₁(U)/R(U)] →
(A₂(f⁻¹U)/I₂(f⁻¹U)) ⊗[A₂(f⁻¹U)] Ω[A₂(f⁻¹U)/(f⁻¹R)(f⁻¹U)]`, semilinear over `ψ`. -/
noncomputable def tensorMapPushₛₗ (U : (Opens X)ᵒᵖ) :
    ((A₁.obj.obj U ⧸ kernelIdeal φ₁.hom U) ⊗[A₁.obj.obj U]
        ((differentialsPresheaf a₁.hom).obj U)) →ₛₗ[(sectionsMapAlong f ψ U).hom]
      ((A₂.obj.obj ((Opens.map f).op.obj U) ⧸ kernelIdeal φ₂.hom ((Opens.map f).op.obj U))
        ⊗[A₂.obj.obj ((Opens.map f).op.obj U)]
        ((differentialsPresheaf a₂.hom).obj ((Opens.map f).op.obj U))) :=
  TensorProduct.map (quotientMapPushₛₗ f B B₂ b φ₁ φ₂ ψ hψ U)
    (differentialsMapPush f ψ R R₂ a₁ a₂ ρ ha U)

omit [Presheaf.IsLocallySurjective (Opens.grothendieckTopology X) φ₁.hom]
  [Presheaf.IsLocallySurjective (Opens.grothendieckTopology Y) φ₂.hom] in
include hψ ha in
/-- The induced map on the tensor product is semilinear over the induced map on `A₁/I₁`. -/
theorem tensorMapPushₛₗ_smul (U : (Opens X)ᵒᵖ) (r : A₁.obj.obj U ⧸ kernelIdeal φ₁.hom U)
    (x : (A₁.obj.obj U ⧸ kernelIdeal φ₁.hom U) ⊗[A₁.obj.obj U]
      ((differentialsPresheaf a₁.hom).obj U)) :
    tensorMapPushₛₗ f B B₂ b φ₁ φ₂ ψ hψ R R₂ a₁ a₂ ρ ha U (r • x) =
      quotientMapPushₛₗ f B B₂ b φ₁ φ₂ ψ hψ U r •
        tensorMapPushₛₗ f B B₂ b φ₁ φ₂ ψ hψ R R₂ a₁ a₂ ρ ha U x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul y ω =>
    show tensorMapPushₛₗ f B B₂ b φ₁ φ₂ ψ hψ R R₂ a₁ a₂ ρ ha U ((r * y) ⊗ₜ ω) =
      quotientMapPushₛₗ f B B₂ b φ₁ φ₂ ψ hψ U r •
        tensorMapPushₛₗ f B B₂ b φ₁ φ₂ ψ hψ R R₂ a₁ a₂ ρ ha U (y ⊗ₜ ω)
    simp only [tensorMapPushₛₗ, TensorProduct.map_tmul, TensorProduct.smul_tmul']
    congr 1
    exact map_mul (Ideal.quotientMap _ (sectionsMapAlong f ψ U).hom
      (kernelIdeal_le_comap_sectionsMapPush f B B₂ b φ₁ φ₂ ψ hψ U)) r y
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]

omit [Presheaf.IsLocallySurjective (Opens.grothendieckTopology X) φ₁.hom]
  [Presheaf.IsLocallySurjective (Opens.grothendieckTopology Y) φ₂.hom] in
include hψ ha in
/-- The induced map on the tensor product commutes with the restriction maps. -/
theorem tensorMapPushₛₗ_naturality {U V : (Opens X)ᵒᵖ} (i : U ⟶ V)
    (x : (A₁.obj.obj U ⧸ kernelIdeal φ₁.hom U) ⊗[A₁.obj.obj U]
      ((differentialsPresheaf a₁.hom).obj U)) :
    tensorMapPushₛₗ f B B₂ b φ₁ φ₂ ψ hψ R R₂ a₁ a₂ ρ ha V (tensorMapₛₗ φ₁.hom a₁.hom i x) =
      tensorMapₛₗ φ₂.hom a₂.hom ((Opens.map f).op.map i)
        (tensorMapPushₛₗ f B B₂ b φ₁ φ₂ ψ hψ R R₂ a₁ a₂ ρ ha U x) := by
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero, map_zero]
  | tmul y ω =>
    refine (congrArg (tensorMapPushₛₗ f B B₂ b φ₁ φ₂ ψ hψ R R₂ a₁ a₂ ρ ha V)
      (TensorProduct.map_tmul _ _ y ω)).trans ?_
    refine (TensorProduct.map_tmul _ _ _ _).trans ?_
    refine Eq.trans ?_ (congrArg (tensorMapₛₗ φ₂.hom a₂.hom ((Opens.map f).op.map i))
      (TensorProduct.map_tmul _ _ y ω)).symm
    refine Eq.trans ?_ (TensorProduct.map_tmul _ _ _ _).symm
    exact congrArg₂ (fun z (ω : (differentialsPresheaf a₂.hom).obj
        ((Opens.map f).op.obj V)) ↦ z ⊗ₜ[A₂.obj.obj ((Opens.map f).op.obj V)] ω)
      (quotientMapPushₛₗ_naturality f B B₂ b φ₁ φ₂ ψ hψ i y)
      (differentialsMapPush_naturality f ψ R R₂ a₁ a₂ ρ ha i ω)
  | add x y hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]

include hψ ha in
/-- **The comparison of the scalar extensions of the differentials along `f`.** The map
`B ⊗[A₁] Ω[A₁/R] ⟶ f_*(f⁻¹B ⊗[A₂] Ω[A₂/f⁻¹R])` sending `1 ⊗ d s` to `1 ⊗ d (ψ s)`. -/
noncomputable def tensorSheafMapPush :
    tensorDifferentialsSheaf.{u, u, u, u} (Opens.grothendieckTopology X) R A₁ B a₁ φ₁ ⟶
      (_root_.SheafOfModules.pushforward.{u} (pushforwardRingHom f b)).obj
        (tensorDifferentialsSheaf.{u, u, u, u} (Opens.grothendieckTopology Y)
          R₂ A₂
          B₂ a₂ φ₂) := by
  refine sheafifyLiftDesc.{u, u, u, u} (Opens.grothendieckTopology X) A₁ B φ₁
    (tensorPresheaf φ₁.hom a₁.hom) _
    (fun U t ↦ toAssociatedModule.{u, u, u, u} (Opens.grothendieckTopology Y) A₂
      B₂ φ₂
      (tensorPresheaf φ₂.hom a₂.hom) ((Opens.map f).op.obj U)
      (tensorMapPushₛₗ f B B₂ b φ₁ φ₂ ψ hψ R R₂ a₁ a₂ ρ ha U t)) ?_ ?_ ?_
  · intro U t t'
    exact (congrArg (toAssociatedModule.{u, u, u, u} (Opens.grothendieckTopology Y) A₂ _ φ₂
        (tensorPresheaf φ₂.hom a₂.hom) ((Opens.map f).op.obj U))
      (map_add (tensorMapPushₛₗ f B B₂ b φ₁ φ₂ ψ hψ R R₂ a₁ a₂ ρ ha U) t t')).trans
      (toAssociatedModule_add.{u, u, u, u} (Opens.grothendieckTopology Y) A₂ _ φ₂
        (tensorPresheaf φ₂.hom a₂.hom) _ _ _)
  · intro U r t
    refine (congrArg (toAssociatedModule.{u, u, u, u} (Opens.grothendieckTopology Y) A₂ _ φ₂
        (tensorPresheaf φ₂.hom a₂.hom) ((Opens.map f).op.obj U))
      (tensorMapPushₛₗ_smul f B B₂ b φ₁ φ₂ ψ hψ R R₂ a₁ a₂ ρ ha U r t)).trans ?_
    refine (toAssociatedModule_smul.{u, u, u, u} (Opens.grothendieckTopology Y) A₂ _ φ₂
      (tensorPresheaf φ₂.hom a₂.hom) _ _ _).trans ?_
    exact congrArg (fun s : (Stacks.SheafOfModules.Tensor.ringSheaf
        B₂).obj.obj
        ((Opens.map f).op.obj U) ↦ s • toAssociatedModule.{u, u, u, u}
          (Opens.grothendieckTopology Y) A₂ _ φ₂ (tensorPresheaf φ₂.hom a₂.hom)
          ((Opens.map f).op.obj U) (tensorMapPushₛₗ f B B₂ b φ₁ φ₂ ψ hψ R R₂ a₁ a₂ ρ ha U t))
      (quotientToTarget_quotientMapPush f B B₂ b φ₁ φ₂ ψ hψ U r)
  · intro U V i t
    exact (congrArg (toAssociatedModule.{u, u, u, u} (Opens.grothendieckTopology Y) A₂ _ φ₂
        (tensorPresheaf φ₂.hom a₂.hom) ((Opens.map f).op.obj V))
      (tensorMapPushₛₗ_naturality f B B₂ b φ₁ φ₂ ψ hψ R R₂ a₁ a₂ ρ ha i t)).trans
      (toAssociatedModule_map.{u, u, u, u} (Opens.grothendieckTopology Y) A₂ _ φ₂
        (tensorPresheaf φ₂.hom a₂.hom) ((Opens.map f).op.map i) _)

include hψ ha in
/-- On presheaf sections the comparison of the scalar extensions of the differentials is the
induced map on the tensor products. -/
theorem tensorSheafMapPush_toAssociatedModule (U : (Opens X)ᵒᵖ)
    (t : (tensorPresheaf φ₁.hom a₁.hom).obj U) :
    ((tensorSheafMapPush f B B₂ b φ₁ φ₂ ψ hψ R R₂ a₁ a₂ ρ ha).val.app U)
        (toAssociatedModule.{u, u, u, u} (Opens.grothendieckTopology X) A₁ B φ₁
          (tensorPresheaf φ₁.hom a₁.hom) U t) =
      toAssociatedModule.{u, u, u, u} (Opens.grothendieckTopology Y) A₂
        B₂ φ₂ (tensorPresheaf φ₂.hom a₂.hom)
        ((Opens.map f).op.obj U)
        (tensorMapPushₛₗ f B B₂ b φ₁ φ₂ ψ hψ R R₂ a₁ a₂ ρ ha U t) := by
  apply sheafifyLiftDesc_toAssociatedModule.{u, u, u, u}

include hψ ha in
/-- **The comparison of the scalar extensions carries `1 ⊗ d s` to `1 ⊗ d (ψ s)`.** -/
theorem tensorSheafMapPush_tensorDifferential (U : (Opens X)ᵒᵖ) (s : A₁.obj.obj U) :
    ((tensorSheafMapPush f B B₂ b φ₁ φ₂ ψ hψ R R₂ a₁ a₂ ρ ha).val.app U)
        (tensorDifferential.{u, u, u, u} (Opens.grothendieckTopology X) R A₁ B a₁ φ₁ U s) =
      tensorDifferential.{u, u, u, u} (Opens.grothendieckTopology Y)
        R₂ A₂
        B₂ a₂ φ₂ ((Opens.map f).op.obj U)
        ((sectionsMapAlong f ψ U).hom s) := by
  refine (tensorSheafMapPush_toAssociatedModule f B B₂ b φ₁ φ₂ ψ hψ R R₂ a₁ a₂ ρ ha U _).trans ?_
  refine congrArg (toAssociatedModule.{u, u, u, u} (Opens.grothendieckTopology Y) A₂
    B₂ φ₂
    (tensorPresheaf φ₂.hom a₂.hom) ((Opens.map f).op.obj U)) ?_
  refine (TensorProduct.map_tmul _ _ _ _).trans ?_
  exact congrArg₂ (fun z (ω : (differentialsPresheaf a₂.hom).obj ((Opens.map f).op.obj U)) ↦
      z ⊗ₜ[A₂.obj.obj ((Opens.map f).op.obj U)] ω)
    (map_one (Ideal.quotientMap _ (sectionsMapAlong f ψ U).hom
      (kernelIdeal_le_comap_sectionsMapPush f B B₂ b φ₁ φ₂ ψ hψ U)))
    (differentialsMapPush_d f ψ R R₂ a₁ a₂ ρ ha U s)

include hψ ha in
/-- **The comparison maps commute with the left-hand maps of the two conormal sequences.** -/
theorem conormalSequence_f_naturality_push :
    (conormalSequence.{u, u, u, u} (Opens.grothendieckTopology X) R A₁ B a₁ φ₁).f ≫
        tensorSheafMapPush f B B₂ b φ₁ φ₂ ψ hψ R R₂ a₁ a₂ ρ ha =
      conormalSheafMapPush f B B₂ b φ₁ φ₂ ψ hψ ≫
        (_root_.SheafOfModules.pushforward.{u} (pushforwardRingHom f b)).map
          (conormalSequence.{u, u, u, u} (Opens.grothendieckTopology Y)
            R₂ A₂
            B₂ a₂ φ₂).f := by
  apply sheafify_hom_ext.{u, u, u, u} (Opens.grothendieckTopology X) A₁ B φ₁
    (conormalPresheaf φ₁.hom)
  intro U c
  obtain ⟨c, rfl⟩ := (kernelIdeal φ₁.hom U).toCotangent_surjective c
  refine Eq.trans (congrArg ((tensorSheafMapPush f B B₂ b φ₁ φ₂ ψ hψ R R₂ a₁ a₂ ρ ha).val.app U)
    (conormalSequence_f_class.{u, u, u, u} (Opens.grothendieckTopology X) R A₁ B a₁ φ₁ U c)) ?_
  refine Eq.trans (tensorSheafMapPush_tensorDifferential f B B₂ b φ₁ φ₂ ψ hψ R R₂ a₁ a₂ ρ ha U c) ?_
  refine Eq.symm (Eq.trans (congrArg
    ((conormalSequence.{u, u, u, u} (Opens.grothendieckTopology Y)
      R₂ A₂
      B₂ a₂ φ₂).f.val.app
        ((Opens.map f).op.obj U))
    (conormalSheafMapPush_conormalClass f B B₂ b φ₁ φ₂ ψ hψ R R₂ a₁ a₂ U c)) ?_)
  exact conormalSequence_f_class.{u, u, u, u} (Opens.grothendieckTopology Y)
    R₂ A₂
    B₂ a₂ φ₂ ((Opens.map f).op.obj U) _

end ChangeOfPresentationPush

end Stacks.Sites.Conormal

end
