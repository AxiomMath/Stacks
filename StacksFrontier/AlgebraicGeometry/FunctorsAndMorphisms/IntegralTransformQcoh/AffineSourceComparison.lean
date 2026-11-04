module

public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.IntegralTransformQcoh.AffineOpenKernelCocycle
public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.IntegralTransformQcoh.GluedKernel

/-!
# Comparing a functor with an integral transform on direct images from affines

Let `R` be a commutative ring, let `X` and `Y` be schemes over `R` with `X` quasi-compact with
affine diagonal, let `F : QCoh(𝒪_X) ⥤ QCoh(𝒪_Y)` be a functor and let `K` be a quasi-coherent
kernel on `X ×_R Y`.  For a morphism `f : X₁ ⟶ X` with `X₁` affine, an identification `A` of
`F ∘ f_*` with the integral transform of a kernel `K₁` on `X₁ ×_R Y` and an identification `β` of
`(f × id_Y)^*K` with `K₁` give an isomorphism

`F ∘ f_* ≅ F_K ∘ f_*`

(`AlgebraicGeometry.kernelComparison`), through affine change of source of Tag 0FZF for the
quasi-compact and quasi-separated `X`. This file proves that along a further affine change of
source `g : X₂ ⟶ X₁`, the comparison at `g ≫ f` is the comparison at `f` evaluated on direct
images along `g`, as soon as the identifications are related by the identification of Tag 0FZF
(`AlgebraicGeometry.kernelComparison_comp_app'`).

## Main definitions

* `AlgebraicGeometry.itMap`: the morphism of integral transforms induced by a morphism of
  kernels, typed by `AlgebraicGeometry.quasicoherentIntegralTransform`.
* `AlgebraicGeometry.kernelComparison`: the comparison `F ∘ f_* ≅ F_K ∘ f_*`.

## Main results

* `AlgebraicGeometry.quasicoherentIntegralTransformSourceChangeIso'_comp`:
  **pseudo-functoriality of affine change of source of Tag 0FZF for a quasi-compact and
  quasi-separated `X`**.
* `AlgebraicGeometry.kernelComparison_comp_app'`: **the comparison is compatible with a further
  affine change of source.**
* `AlgebraicGeometry.sourceChangeIso_hom_comp_map_affineSourceKernelRestrictIso`: the
  identification of Tag 0FZF of the kernels with affine source, in triangle form.

## References

* [Stacks Project, Tag 0GPA](https://stacks.math.columbia.edu/tag/0GPA)
* [Stacks Project, Tag 0FZF](https://stacks.math.columbia.edu/tag/0FZF)
* [Stacks Project, Tag 0FZD](https://stacks.math.columbia.edu/tag/0FZD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

attribute [local instance] isOpenImmersion_over_comp_left

attribute [local implicit_reducible] TopCat.Sheaf
  AlgebraicGeometry.Scheme.Modules CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf structureSheafRing
  Stacks.SheafOfModules.TensorSheafification.structureSheaf
  AlgebraicGeometry.Scheme.Modules.instCategory AlgebraicGeometry.Scheme.Modules.Hom

/-! ### Morphisms of integral transforms induced by morphisms of kernels -/

section ItMap

attribute [local implicit_reducible] AlgebraicGeometry.integralTransformQcohFunctor
  AlgebraicGeometry.IntegralTransformQcoh.liftFunctorAlongFullyFaithful

variable (R : Type u) [CommRing R] (Z W : Over (Spec (.of R))) [CompactSpace Z.left]
  [QuasiSeparatedSpace Z.left]

/-- **The morphism of integral transforms induced by a morphism of kernels**, typed by
`AlgebraicGeometry.quasicoherentIntegralTransform`: the functor of Tag 0FZD on morphisms. -/
def itMap {K L : Scheme.QuasicoherentModules (pullback Z.hom W.hom)} (φ : K ⟶ L) :
    quasicoherentIntegralTransform R Z W K ⟶ quasicoherentIntegralTransform R Z W L :=
  (integralTransformQcohFunctor R Z W).map φ

/-- `AlgebraicGeometry.itMap` preserves composition. -/
theorem itMap_comp {K L N : Scheme.QuasicoherentModules (pullback Z.hom W.hom)} (φ : K ⟶ L)
    (ψ : L ⟶ N) : itMap R Z W (φ ≫ ψ) = itMap R Z W φ ≫ itMap R Z W ψ :=
  (integralTransformQcohFunctor R Z W).map_comp φ ψ

/-- A commutative square of morphisms of kernels gives, under `AlgebraicGeometry.itMap`, a
commutative square of components at a quasi-coherent module. -/
theorem itMap_app_comp_eq {k₁ k₂ k₃ k₄ : Scheme.QuasicoherentModules (pullback Z.hom W.hom)}
    {a : k₁ ⟶ k₂} {b : k₂ ⟶ k₃} {m : k₁ ⟶ k₄} {c : k₄ ⟶ k₃} (h : a ≫ b = m ≫ c)
    (H : Scheme.QuasicoherentModules Z.left) :
    (itMap R Z W a).app H ≫ (itMap R Z W b).app H =
      (itMap R Z W m).app H ≫ (itMap R Z W c).app H := by
  rw [← NatTrans.comp_app, ← itMap_comp, h, itMap_comp, NatTrans.comp_app]

/-- `AlgebraicGeometry.map_sourceChangeKernelMap` at a quasi-coherent module, with the morphisms
of integral transforms spelled by `AlgebraicGeometry.itMap`. -/
theorem itMap_sourceChangeKernelMap_app {Z' : Over (Spec (.of R))} [IsAffine Z.left]
    [IsAffine Z'.left] (h : Z' ⟶ Z) [IsAffineHom h.left]
    {K L : Scheme.QuasicoherentModules (pullback Z.hom W.hom)} (φ : K ⟶ L)
    (H : Scheme.QuasicoherentModules Z'.left) :
    (itMap R Z' W (sourceChangeKernelMap R Z Z' W h φ)).app H =
      (quasicoherentIntegralTransformSourceChangeIso R Z Z' W h K).inv.app H ≫
        (itMap R Z W φ).app ((quasicoherentPushforward h.left).obj H) ≫
          (quasicoherentIntegralTransformSourceChangeIso R Z Z' W h L).hom.app H := by
  have := congrArg (fun φ => NatTrans.app φ H) (map_sourceChangeKernelMap R Z Z' W h φ)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at this
  exact this

end ItMap

/-! ### Pseudo-functoriality of change of source for a non-affine `X` -/

section PrimedComp

attribute [local implicit_reducible] AlgebraicGeometry.integralTransformQcohFunctor
  AlgebraicGeometry.IntegralTransformQcoh.liftFunctorAlongFullyFaithful

attribute [local instance] isAffineHom_left_of_isAffine_left

variable (R : Type u) [CommRing R] (X X₁ X₂ Y : Over (Spec (.of R))) [CompactSpace X.left]
  [QuasiSeparatedSpace X.left] [IsAffineHom (pullback.diagonal (terminal.from X.left))]
  [IsAffine X₁.left] [IsAffine X₂.left] (f : X₁ ⟶ X) (g : X₂ ⟶ X₁)
  (K : Scheme.QuasicoherentModules (pullback X.hom Y.hom))

/-- **Affine change of source for a non-affine `X`, after forgetting quasi-coherence of the
values**, is affine change of source for the formula of Tag 0FZB, conjugated by the two
comparison isomorphisms. -/
theorem whiskerRight_quasicoherentIntegralTransformSourceChangeIso'_hom :
    Functor.whiskerRight (quasicoherentIntegralTransformSourceChangeIso' R X X₁ Y f K).hom
        (SheafOfModules.isQuasicoherent Y.left.ringCatSheaf).ι =
      Functor.whiskerLeft (quasicoherentPushforward f.left)
          (quasicoherentIntegralTransformData R X Y K).comparison.hom ≫
        (integralTransformFormulaSourceChangeIso R X X₁ Y f K).hom ≫
        (quasicoherentIntegralTransformData R X₁ Y
          (sourceChangeKernel R X X₁ Y f K)).comparison.inv :=
  ((SheafOfModules.isQuasicoherent Y.left.ringCatSheaf).fullyFaithfulι.whiskeringRight
    (Scheme.QuasicoherentModules X₁.left)).map_preimage _

/-- **Pseudo-functoriality of the source-change isomorphism of Tag 0FZF for a quasi-compact and
quasi-separated `X`**:  change of source along a composite `X₂ ⟶ X₁ ⟶ X` of affine morphisms is
the composite of the two changes of source, up to the identification of the two iterated inverse
images of the kernel. -/
theorem quasicoherentIntegralTransformSourceChangeIso'_comp :
    (quasicoherentIntegralTransformSourceChangeIso' R X X₂ Y (g ≫ f) K).hom =
      Functor.whiskerRight (eqToIso (quasicoherentPushforward_eq_comp f g rfl)).hom
          (quasicoherentIntegralTransform R X Y K) ≫
        ((quasicoherentPushforward (Over.Hom.left g)).associator
              (quasicoherentPushforward (Over.Hom.left f))
              (quasicoherentIntegralTransform R X Y K)).hom ≫
          (quasicoherentPushforward (Over.Hom.left g)).whiskerLeft
              (quasicoherentIntegralTransformSourceChangeIso' R X X₁ Y f K).hom ≫
            (quasicoherentIntegralTransformSourceChangeIso R X₁ X₂ Y g
                (sourceChangeKernel R X X₁ Y f K)).hom ≫
              (integralTransformQcohFunctor R X₂ Y).map
                (sourceChangeKernelCompIso R X X₁ X₂ Y f g K).inv := by
  refine whiskerRight_isQuasicoherentι_injective R Y X₂ ?_
  rw [Functor.whiskerRight_comp, Functor.whiskerRight_comp, Functor.whiskerRight_comp,
    Functor.whiskerRight_comp]
  have hL := whiskerRight_quasicoherentIntegralTransformSourceChangeIso'_hom R X X₂ Y (g ≫ f) K
  have h3' := whiskerRight_quasicoherentIntegralTransformSourceChangeIso'_hom R X X₁ Y f K
  have h3 := whiskerRight_whiskerLeft_comp₃ (quasicoherentPushforward g.left)
    (SheafOfModules.isQuasicoherent Y.left.ringCatSheaf).ι
    (quasicoherentIntegralTransformSourceChangeIso' R X X₁ Y f K).hom _ _ _ h3'
  have h4 := whiskerRight_quasicoherentIntegralTransformSourceChangeIso_hom R X₁ X₂ Y g
    (sourceChangeKernel R X X₁ Y f K)
  have h5 := whiskerRight_integralTransformQcohFunctor_map R Y X₂ _ _
    (sourceChangeKernelCompIso R X X₁ X₂ Y f g K).inv
  have hex := whisker_exchange_pair (quasicoherentPushforward g.left)
    (quasicoherentPushforward f.left)
    (eqToIso (quasicoherentPushforward_eq_comp f g rfl)).hom
    (quasicoherentIntegralTransform R X Y K)
    (SheafOfModules.isQuasicoherent Y.left.ringCatSheaf).ι
    (quasicoherentIntegralTransformData R X Y K).comparison.hom
  refine five_chain hL h3 h4 h5 ?_ ?_ hex
    (integralTransformFormulaSourceChangeIso_comp R X X₁ X₂ Y f g K)
  · rw [← Functor.whiskerLeft_comp, Iso.inv_hom_id]
    exact NatTrans.ext (funext fun _ => rfl)
  · exact Iso.inv_hom_id _

/-- `AlgebraicGeometry.quasicoherentIntegralTransformSourceChangeIso'_comp` with the last factor
spelled by `AlgebraicGeometry.itMap`. -/
theorem quasicoherentIntegralTransformSourceChangeIso'_comp_itMap :
    (quasicoherentIntegralTransformSourceChangeIso' R X X₂ Y (g ≫ f) K).hom =
      Functor.whiskerRight (eqToIso (quasicoherentPushforward_eq_comp f g rfl)).hom
          (quasicoherentIntegralTransform R X Y K) ≫
        ((quasicoherentPushforward (Over.Hom.left g)).associator
              (quasicoherentPushforward (Over.Hom.left f))
              (quasicoherentIntegralTransform R X Y K)).hom ≫
          (quasicoherentPushforward (Over.Hom.left g)).whiskerLeft
              (quasicoherentIntegralTransformSourceChangeIso' R X X₁ Y f K).hom ≫
            (quasicoherentIntegralTransformSourceChangeIso R X₁ X₂ Y g
                (sourceChangeKernel R X X₁ Y f K)).hom ≫
              itMap R X₂ Y (sourceChangeKernelCompIso R X X₁ X₂ Y f g K).inv :=
  quasicoherentIntegralTransformSourceChangeIso'_comp R X X₁ X₂ Y f g K

/-- `AlgebraicGeometry.quasicoherentIntegralTransformSourceChangeIso'_comp_itMap` with the
composite presented as a given morphism `f'`. -/
theorem quasicoherentIntegralTransformSourceChangeIso'_comp' {f' : X₂ ⟶ X} (hk : g ≫ f = f') :
    (quasicoherentIntegralTransformSourceChangeIso' R X X₂ Y f' K).hom =
      Functor.whiskerRight (eqToIso (quasicoherentPushforward_eq_comp f g hk)).hom
          (quasicoherentIntegralTransform R X Y K) ≫
        ((quasicoherentPushforward (Over.Hom.left g)).associator
              (quasicoherentPushforward (Over.Hom.left f))
              (quasicoherentIntegralTransform R X Y K)).hom ≫
          (quasicoherentPushforward (Over.Hom.left g)).whiskerLeft
              (quasicoherentIntegralTransformSourceChangeIso' R X X₁ Y f K).hom ≫
            (quasicoherentIntegralTransformSourceChangeIso R X₁ X₂ Y g
                (sourceChangeKernel R X X₁ Y f K)).hom ≫
              itMap R X₂ Y ((sourceChangeKernelCompIso R X X₁ X₂ Y f g K).inv ≫
                eqToHom (congrArg (fun q : X₂ ⟶ X ↦ sourceChangeKernel R X X₂ Y q K) hk)) := by
  subst hk
  simp only [eqToHom_refl, Category.comp_id]
  exact quasicoherentIntegralTransformSourceChangeIso'_comp_itMap R X X₁ X₂ Y f g K

/-- `AlgebraicGeometry.quasicoherentIntegralTransformSourceChangeIso'_comp'` at a quasi-coherent
module. -/
theorem quasicoherentIntegralTransformSourceChangeIso'_comp_app' {f' : X₂ ⟶ X}
    (hk : g ≫ f = f') (H : Scheme.QuasicoherentModules X₂.left) :
    (quasicoherentIntegralTransformSourceChangeIso' R X X₂ Y f' K).hom.app H =
      (Functor.whiskerRight (eqToIso (quasicoherentPushforward_eq_comp f g hk)).hom
          (quasicoherentIntegralTransform R X Y K)).app H ≫
        (quasicoherentIntegralTransformSourceChangeIso' R X X₁ Y f K).hom.app
            ((quasicoherentPushforward g.left).obj H) ≫
          (quasicoherentIntegralTransformSourceChangeIso R X₁ X₂ Y g
              (sourceChangeKernel R X X₁ Y f K)).hom.app H ≫
            (itMap R X₂ Y ((sourceChangeKernelCompIso R X X₁ X₂ Y f g K).inv ≫
                eqToHom (congrArg (fun q : X₂ ⟶ X ↦ sourceChangeKernel R X X₂ Y q K)
                  hk))).app H := by
  have h := congrArg (fun φ => φ.app H)
    (quasicoherentIntegralTransformSourceChangeIso'_comp' R X X₁ X₂ Y f g K hk)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, associator_hom_app] at h
  refine h.trans ?_
  congr 1

end PrimedComp


/-! ### The diagram chase behind the compatibility of the comparisons -/

/-- A diagram chase in a category: if `eF ≫ eF' = 𝟙`, `eK' ≫ eK = 𝟙` and the relations `ha`, `hβ`,
`hM` and `hS` hold, then `A₂ ≫ tb₂ ≫ S₂.inv = eF ≫ (A₁.hom ≫ tb₁ ≫ S₁.inv) ≫ eK'`. -/
theorem comparison_chase {C : Type*} [Category C]
    {P P' Q₁ Q₂ L M₁ M₂ M₂' N N' : C}
    (eF : P ⟶ P') (eF' : P' ⟶ P) (heF : eF ≫ eF' = 𝟙 P)
    (A₁ : P' ≅ Q₁) (A₂ : P ⟶ Q₂) (Cf : Q₁ ≅ L) (ta : L ⟶ Q₂)
    (ha : Cf.hom ≫ ta = A₁.inv ≫ eF' ≫ A₂)
    (tb₂ : Q₂ ⟶ M₂') (tm : L ⟶ M₂) (tc : M₂ ⟶ M₂') (hβ : ta ≫ tb₂ = tm ≫ tc)
    (tb₁ : Q₁ ⟶ M₁) (Cs : M₁ ⟶ M₂) (hM : tm = Cf.inv ≫ tb₁ ≫ Cs)
    (S₁ : N ≅ M₁) (S₂ : N' ≅ M₂') (eK : N' ⟶ N) (eK' : N ⟶ N') (heK : eK' ≫ eK = 𝟙 N)
    (hS : S₂.hom = eK ≫ S₁.hom ≫ Cs ≫ tc) :
    A₂ ≫ tb₂ ≫ S₂.inv = eF ≫ (A₁.hom ≫ tb₁ ≫ S₁.inv) ≫ eK' := by
  have h1 : A₂ = eF ≫ A₁.hom ≫ Cf.hom ≫ ta := by
    rw [ha, Iso.hom_inv_id_assoc, ← Category.assoc, heF, Category.id_comp]
  rw [← Category.assoc, Iso.comp_inv_eq, h1, hS]
  simp only [Category.assoc, hβ, hM, Iso.hom_inv_id_assoc, reassoc_of% heK,
    Iso.inv_hom_id_assoc]

/-- A commutative square of morphisms is carried by a functor into a functor category to a
commutative square of components. -/
theorem map_app_comp_eq {C D E : Type*} [Category C] [Category D] [Category E] (T : E ⥤ D ⥤ C)
    {k₁ k₂ k₃ k₄ : E} {a : k₁ ⟶ k₂} {b : k₂ ⟶ k₃} {m : k₁ ⟶ k₄} {c : k₄ ⟶ k₃}
    (h : a ≫ b = m ≫ c) (H : D) :
    (T.map a).app H ≫ (T.map b).app H = (T.map m).app H ≫ (T.map c).app H := by
  rw [← NatTrans.comp_app, ← T.map_comp, h, T.map_comp, NatTrans.comp_app]

/-! ### Inverse images of isomorphisms of kernels -/

section SourceChangeKernelMap

variable (R : Type u) [CommRing R] (Z Z' W : Over (Spec (.of R))) (a : Z' ⟶ Z)

/-- `AlgebraicGeometry.sourceChangeKernelMap` preserves composition. -/
theorem sourceChangeKernelMap_comp {K L N : Scheme.QuasicoherentModules (pullback Z.hom W.hom)}
    (φ : K ⟶ L) (ψ : L ⟶ N) :
    sourceChangeKernelMap R Z Z' W a φ ≫ sourceChangeKernelMap R Z Z' W a ψ =
      sourceChangeKernelMap R Z Z' W a (φ ≫ ψ) :=
  ((sourceChangeKernelFunctor R Z Z' W a).map_comp φ ψ).symm

/-- `AlgebraicGeometry.sourceChangeKernelMap` preserves identities. -/
theorem sourceChangeKernelMap_id (K : Scheme.QuasicoherentModules (pullback Z.hom W.hom)) :
    sourceChangeKernelMap R Z Z' W a (𝟙 K) = 𝟙 _ :=
  (sourceChangeKernelFunctor R Z Z' W a).map_id K

/-- `AlgebraicGeometry.sourceChangeKernelMap` of `e.inv` followed by that of `e.hom` is the
identity, for an isomorphism of kernels `e`. -/
theorem sourceChangeKernelMap_inv_hom {K L : Scheme.QuasicoherentModules (pullback Z.hom W.hom)}
    (e : K ≅ L) :
    sourceChangeKernelMap R Z Z' W a e.inv ≫ sourceChangeKernelMap R Z Z' W a e.hom = 𝟙 _ := by
  rw [sourceChangeKernelMap_comp, e.inv_hom_id, sourceChangeKernelMap_id]

end SourceChangeKernelMap

/-! ### The comparison of `F` with an integral transform on the direct images from an affine -/

section KernelComparison

attribute [local instance] isAffineHom_left_of_isAffine_left

attribute [local implicit_reducible] AlgebraicGeometry.integralTransformQcohFunctor
  AlgebraicGeometry.IntegralTransformQcoh.liftFunctorAlongFullyFaithful

variable (R : Type u) [CommRing R] (X Y : Over (Spec (.of R)))
  (F : Scheme.QuasicoherentModules X.left ⥤ Scheme.QuasicoherentModules Y.left)
  [CompactSpace X.left] [QuasiSeparatedSpace X.left]
  [IsAffineHom (pullback.diagonal (terminal.from X.left))]
  (K : Scheme.QuasicoherentModules (pullback X.hom Y.hom))

/-- **The comparison of `F` with the integral transform of `K` on direct images from an affine,
through a kernel.**  For `f : X₁ ⟶ X` with `X₁` affine, an identification `A` of `F ∘ f_*` with
the integral transform of a kernel `K₁` on `X₁ ×_R Y`, and an identification `β` of
`(f × id_Y)^*K` with `K₁`, the composite of `A`, of `β` and of affine change of source
`F_K ∘ f_* ≅ F_{(f × id_Y)^*K}` of Tag 0FZF. -/
def kernelComparison {X₁ : Over (Spec (.of R))} [IsAffine X₁.left] (f : X₁ ⟶ X)
    {K₁ : Scheme.QuasicoherentModules (pullback X₁.hom Y.hom)}
    (A : quasicoherentPushforward f.left ⋙ F ≅ quasicoherentIntegralTransform R X₁ Y K₁)
    (β : sourceChangeKernel R X X₁ Y f K ≅ K₁) :
    quasicoherentPushforward f.left ⋙ F ≅
      quasicoherentPushforward f.left ⋙ quasicoherentIntegralTransform R X Y K :=
  A ≪≫ (integralTransformQcohFunctor R X₁ Y).mapIso β.symm ≪≫
    (quasicoherentIntegralTransformSourceChangeIso' R X X₁ Y f K).symm

/-- The component of `AlgebraicGeometry.kernelComparison` at a quasi-coherent module is the
composite of the components of `A`, of `AlgebraicGeometry.itMap` of `β.inv` and of the inverse of
affine change of source. -/
theorem kernelComparison_hom_app {X₁ : Over (Spec (.of R))} [IsAffine X₁.left] (f : X₁ ⟶ X)
    {K₁ : Scheme.QuasicoherentModules (pullback X₁.hom Y.hom)}
    (A : quasicoherentPushforward f.left ⋙ F ≅ quasicoherentIntegralTransform R X₁ Y K₁)
    (β : sourceChangeKernel R X X₁ Y f K ≅ K₁) (H : Scheme.QuasicoherentModules X₁.left) :
    (kernelComparison R X Y F K f A β).hom.app H =
      A.hom.app H ≫ (itMap R X₁ Y β.inv).app H ≫
          (quasicoherentIntegralTransformSourceChangeIso' R X X₁ Y f K).inv.app H := rfl

/-- **The comparison is compatible with a further affine change of source**:  for
`f : X₁ ⟶ X`, `g : X₂ ⟶ X₁` and `f' = g ≫ f` with `X₁`, `X₂` affine, if the identifications
`A₁`, `A₂` of `F ∘ f_*`, `F ∘ f'_*` with integral transforms are related through an
identification `a` of kernels by affine change of source, and the identifications `β₁`, `β₂`
of kernels are related by `a`, then the comparison at `f'` is the comparison at `f` evaluated
on direct images along `g`. -/
theorem kernelComparison_comp_app' {X₁ X₂ : Over (Spec (.of R))} [IsAffine X₁.left]
    [IsAffine X₂.left] (f : X₁ ⟶ X) (g : X₂ ⟶ X₁) {f' : X₂ ⟶ X} (hk : g ≫ f = f')
    {K₁ : Scheme.QuasicoherentModules (pullback X₁.hom Y.hom)}
    {K₂ : Scheme.QuasicoherentModules (pullback X₂.hom Y.hom)}
    (A₁ : quasicoherentPushforward f.left ⋙ F ≅ quasicoherentIntegralTransform R X₁ Y K₁)
    (A₂ : quasicoherentPushforward f'.left ⋙ F ≅ quasicoherentIntegralTransform R X₂ Y K₂)
    (a : sourceChangeKernel R X₁ X₂ Y g K₁ ≅ K₂)
    (ha : (quasicoherentIntegralTransformSourceChangeIso R X₁ X₂ Y g K₁).hom ≫
        itMap R X₂ Y a.hom =
      Functor.whiskerLeft (quasicoherentPushforward g.left) A₁.inv ≫
        Functor.whiskerRight (eqToIso (quasicoherentPushforward_eq_comp f g hk)).inv F ≫ A₂.hom)
    (β₁ : sourceChangeKernel R X X₁ Y f K ≅ K₁) (β₂ : sourceChangeKernel R X X₂ Y f' K ≅ K₂)
    (hβ : β₂.hom = eqToHom (congrArg (fun q : X₂ ⟶ X ↦ sourceChangeKernel R X X₂ Y q K) hk.symm) ≫
      (sourceChangeKernelCompIso R X X₁ X₂ Y f g K).hom ≫
        sourceChangeKernelMap R X₁ X₂ Y g β₁.hom ≫ a.hom)
    (H : Scheme.QuasicoherentModules X₂.left) :
    (kernelComparison R X Y F K f' A₂ β₂).hom.app H =
      (Functor.whiskerRight (eqToIso (quasicoherentPushforward_eq_comp f g hk)).hom F).app H ≫
        (kernelComparison R X Y F K f A₁ β₁).hom.app ((quasicoherentPushforward g.left).obj H) ≫
          (Functor.whiskerRight (eqToIso (quasicoherentPushforward_eq_comp f g hk)).inv
            (quasicoherentIntegralTransform R X Y K)).app H := by
  have hS := quasicoherentIntegralTransformSourceChangeIso'_comp_app' R X X₁ X₂ Y f g K hk H
  have hA := congrArg (fun φ => φ.app H) ha
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at hA
  have hM := itMap_sourceChangeKernelMap_app R X₁ Y g β₁.inv H
  have hβ' : a.hom ≫ β₂.inv = sourceChangeKernelMap R X₁ X₂ Y g β₁.inv ≫
      (sourceChangeKernelCompIso R X X₁ X₂ Y f g K).inv ≫
        eqToHom (congrArg (fun q : X₂ ⟶ X ↦ sourceChangeKernel R X X₂ Y q K) hk) := by
    rw [Iso.comp_inv_eq, hβ]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
      Iso.inv_hom_id_assoc]
    rw [← Category.assoc (sourceChangeKernelMap R X₁ X₂ Y g β₁.inv),
      sourceChangeKernelMap_inv_hom, Category.id_comp]
  let e := eqToIso (quasicoherentPushforward_eq_comp f g hk)
  exact comparison_chase _ _ ((Functor.isoWhiskerRight e F).hom_inv_id_app H)
    (A₁.app ((quasicoherentPushforward g.left).obj H)) (A₂.hom.app H)
    ((quasicoherentIntegralTransformSourceChangeIso R X₁ X₂ Y g K₁).app H) _ hA _ _ _
    (itMap_app_comp_eq R X₂ Y hβ' H) _ _ hM
    ((quasicoherentIntegralTransformSourceChangeIso' R X X₁ Y f K).app
      ((quasicoherentPushforward g.left).obj H))
    ((quasicoherentIntegralTransformSourceChangeIso' R X X₂ Y f' K).app H) _ _
    ((Functor.isoWhiskerRight e.symm (quasicoherentIntegralTransform R X Y K)).hom_inv_id_app H)
    hS

end KernelComparison


/-! ### The triangle of the kernels with affine source, with the composite given -/

section AffineSourceTriangle

attribute [local instance] isAffineHom_left_of_isAffine_left

attribute [local implicit_reducible] AlgebraicGeometry.integralTransformQcohFunctor
  AlgebraicGeometry.IntegralTransformQcoh.liftFunctorAlongFullyFaithful

variable (R : Type u) [CommRing R] (X Y : Over (Spec (.of R)))
  (F : Scheme.QuasicoherentModules X.left ⥤ Scheme.QuasicoherentModules Y.left)
  [IsAffineHom (pullback.diagonal (terminal.from X.left))]
  (hF : affineOpenRightExactLinearCoproductFunctor R X Y F)

/-- **The identification of Tag 0FZF of the kernels with affine source, in triangle form, with
the composite presented as a given morphism.** -/
theorem sourceChangeIso_hom_comp_map_affineSourceKernelRestrictIso
    {X₁ X₂ : Over (Spec (.of R))} [IsAffine X₁.left] [IsAffine X₂.left] (f : X₁ ⟶ X)
    (g : X₂ ⟶ X₁) {f' : X₂ ⟶ X} [IsOpenImmersion f.left] [IsOpenImmersion g.left]
    [IsOpenImmersion f'.left] (hk : g ≫ f = f') :
    (quasicoherentIntegralTransformSourceChangeIso R X₁ X₂ Y g
          (affineSourceKernel R X Y F hF f)).hom ≫
        itMap R X₂ Y (affineSourceKernelRestrictIso R X Y F hF f g hk).hom =
      Functor.whiskerLeft (quasicoherentPushforward g.left)
          (affineSourceKernelIso R X Y F hF f).inv ≫
        Functor.whiskerRight (eqToIso (quasicoherentPushforward_eq_comp f g hk)).inv F ≫
          (affineSourceKernelIso R X Y F hF f').hom := by
  subst hk
  have h := sourceChangeIso_hom_comp_map_affineSourceKernelSourceChangeIso R X Y F hF f g
  rw [quasicoherentPushforwardComp_hom_eq_eqToIso_inv R X f g] at h
  refine Eq.trans ?_ h
  simp only [affineSourceKernelRestrictIso, Iso.trans_hom, eqToIso_refl, Iso.refl_hom,
    Category.comp_id]
  rfl

end AffineSourceTriangle

end AlgebraicGeometry

end
