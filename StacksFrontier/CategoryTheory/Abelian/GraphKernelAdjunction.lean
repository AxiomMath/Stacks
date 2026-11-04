module

public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Preadditive.Biproducts

/-!
# The graph kernel of a morphism along an adjunction

Let `adj : L ⊣ R` be an adjunction between abelian categories, with `L : A ⥤ B` thought of as a
restriction (inverse image) functor and `R : B ⥤ A` as the corresponding direct image. Given
`F : A` and a morphism `φ : G ⟶ L.obj F` with `G : B`, the *graph kernel* of `φ` is the kernel of
the difference of the adjunction unit `F ⟶ R.obj (L.obj F)` and `R.map φ`, taken on the direct
sum `F ⊞ R.obj G`. It is an object of `A` whose image under `L` is `G` and whose projection to
`F` is carried to `φ` by that identification, and it is a subobject of `F` whenever `φ` is a
monomorphism.

The name comes from the special case `R = 𝟭`: the kernel of `(𝟙, -f) : X ⊞ Y ⟶ X` is the graph
of `f : Y ⟶ X` inside `X ⊞ Y`, so the general construction glues `F` and `R.obj G` along the
graph of `R.map φ` twisted by the unit.

## Main definitions

* `Stacks.GraphKernel.standardGraphKernelIso`: the kernel of `(𝟙, -f) : X ⊞ Y ⟶ X` is `Y`,
  embedded as the graph of `f`.
* `Stacks.GraphKernel.graphKernelMap`: the unit of the adjunction at `F` minus `R.map φ`, out of
  the direct sum `F ⊞ R.obj G`.
* `Stacks.GraphKernel.graphKernel`: the kernel of that morphism, and
  `Stacks.GraphKernel.graphKernelProjection` its first projection to `F`.

## Main results

* `Stacks.GraphKernel.graphKernelPullbackIso` identifies `L.obj (graphKernel adj F φ)` with `G`,
  with `Stacks.GraphKernel.graphKernelPullbackIso_hom` describing the identification as the
  second projection followed by the adjunction counit.
* `Stacks.GraphKernel.graphKernelPullbackIso_hom_comp`: under that identification the image of
  the projection to `F` is `φ`.
* `Stacks.GraphKernel.graphKernelProjection_mono`: the projection is a monomorphism as soon as
  `φ` is.

## Implementation notes

The identification `L.obj (graphKernel adj F φ) ≅ G` needs `L` to preserve the kernel and the
binary biproduct defining the graph kernel, and needs the counit of the adjunction to be an
isomorphism. The first is the hypothesis `PreservesFiniteLimits L`; the second is automatic,
since a left adjoint preserves colimits, hence binary coproducts, hence — being additive —
binary biproducts; the third follows from `R` being fully faithful.

`graphKernelProjection_mono` needs `R.map φ` to be a monomorphism, which is derived here rather
than assumed: `R` is a right adjoint, so it preserves limits, in particular pullbacks, and a
functor preserving pullbacks preserves monomorphisms.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.GraphKernel

universe v₁ v₂ u₁ u₂

variable {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]

section Standard

variable [Abelian B]

/-- The kernel of `(𝟙, -f) : X ⊞ Y ⟶ X` is `Y`, embedded in `X ⊞ Y` as the graph `(f, 𝟙)` of
`f : Y ⟶ X`. -/
def standardGraphKernelIso {X Y : B} (f : Y ⟶ X) : kernel (biprod.desc (𝟙 X) (-f)) ≅ Y := by
  let d : X ⊞ Y ⟶ X := biprod.desc (𝟙 X) (-f)
  let s : Y ⟶ X ⊞ Y := biprod.lift f (𝟙 Y)
  have hs : s ≫ d = 0 := by
    simp [d, s, biprod.lift_desc]
  refine
    { hom := kernel.ι d ≫ biprod.snd
      inv := kernel.lift d s hs
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · apply (cancel_mono (kernel.ι d)).1
    simp only [Category.assoc, kernel.lift_ι]
    apply biprod.hom_ext
    · simp only [s, biprod.lift_fst, Category.assoc, Category.id_comp]
      have h : kernel.ι d ≫ biprod.fst + -(kernel.ι d ≫ biprod.snd ≫ f) = 0 := by
        simpa [d, biprod.desc_eq, Category.assoc] using kernel.condition d
      exact (add_neg_eq_zero.mp h).symm
    · simp [s, Category.assoc]
  · simp [s]

end Standard

variable [Abelian A] [Abelian B] {L : A ⥤ B} {R : B ⥤ A}
  (adj : L ⊣ R) (F : A) {G : B} (φ : G ⟶ L.obj F)

/-- The unit of the adjunction at `F` minus the image under `R` of `φ`, out of the direct sum of
`F` and `R.obj G`. -/
def graphKernelMap : F ⊞ R.obj G ⟶ R.obj (L.obj F) :=
  biprod.desc (adj.unit.app F) (-R.map φ)

/-- The graph kernel of `φ : G ⟶ L.obj F`: the object of `A` obtained by glueing `F` and
`R.obj G` along the graph of `R.map φ`. -/
def graphKernel : A :=
  kernel (graphKernelMap adj F φ)

/-- The first projection of the graph kernel of `φ` to `F`. -/
def graphKernelProjection : graphKernel adj F φ ⟶ F :=
  kernel.ι (graphKernelMap adj F φ) ≫ biprod.fst

/-- The kernel inclusion of `graphKernelMap` equalises the unit with `R.map φ`. -/
private theorem graphKernel_ι_comp_unit {C : Type u₂} [Category.{v₂} C] {L' : A ⥤ C} {R' : C ⥤ A}
    (adj' : L' ⊣ R') (F' : A) {G' : C} (φ' : G' ⟶ L'.obj F') :
    kernel.ι (graphKernelMap adj' F' φ') ≫ biprod.fst ≫ adj'.unit.app F' =
      kernel.ι (graphKernelMap adj' F' φ') ≫ biprod.snd ≫ R'.map φ' := by
  have h := kernel.condition (graphKernelMap adj' F' φ')
  simp only [graphKernelMap, biprod.desc_eq, Preadditive.comp_add, Preadditive.comp_neg] at h
  exact add_neg_eq_zero.mp h

section Pullback

variable [L.Additive] [R.Full] [R.Faithful] [PreservesFiniteLimits L]

/-- The image under `L` of the graph kernel of `φ : G ⟶ L.obj F` is `G`. -/
def graphKernelPullbackIso : L.obj (graphKernel adj F φ) ≅ G := by
  let eG : L.obj (R.obj G) ≅ G := asIso (adj.counit.app G)
  let eF : L.obj (R.obj (L.obj F)) ≅ L.obj F := asIso (adj.counit.app (L.obj F))
  let : PreservesColimitsOfShape (Discrete WalkingPair) L :=
    (adj.leftAdjoint_preservesColimits).preservesColimitsOfShape
  let : PreservesBinaryBiproducts L :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts L
  let sourceIso : L.obj (F ⊞ R.obj G) ≅ L.obj F ⊞ G :=
    L.mapBiprod F (R.obj G) ≪≫ biprod.mapIso (Iso.refl _) eG
  let f' : L.obj F ⊞ G ⟶ L.obj F := biprod.desc (𝟙 (L.obj F)) (-φ)
  have sourceIso_inl : biprod.inl ≫ sourceIso.inv = L.map biprod.inl := by
    dsimp [sourceIso, Iso.trans_inv, biprod.mapIso_inv, Functor.mapBiprod_inv]
    simp [biprod.inl_desc]
  have sourceIso_inr : biprod.inr ≫ sourceIso.inv = eG.inv ≫ L.map biprod.inr := by
    dsimp [sourceIso, Iso.trans_inv, biprod.mapIso_inv, Functor.mapBiprod_inv]
    simp [biprod.inr_desc]
  have h' : sourceIso.inv ≫ L.map (graphKernelMap adj F φ) ≫ eF.hom = f' := by
    apply biprod.hom_ext'
    · rw [← Category.assoc, sourceIso_inl]
      calc
        L.map biprod.inl ≫ L.map (graphKernelMap adj F φ) ≫ eF.hom =
            L.map (biprod.inl ≫ graphKernelMap adj F φ) ≫ eF.hom := by
              rw [← Category.assoc, ← Functor.map_comp]
        _ = L.map (adj.unit.app F) ≫ eF.hom := by
              rw [graphKernelMap, biprod.inl_desc]
        _ = 𝟙 (L.obj F) := Adjunction.left_triangle_components adj F
        _ = biprod.inl ≫ f' := by simp [f']
    · rw [← Category.assoc, sourceIso_inr]
      calc
        (eG.inv ≫ L.map biprod.inr) ≫ L.map (graphKernelMap adj F φ) ≫ eF.hom =
            eG.inv ≫ L.map (biprod.inr ≫ graphKernelMap adj F φ) ≫ eF.hom := by
              simp only [Functor.map_comp, Category.assoc]
        _ = eG.inv ≫ L.map (-R.map φ) ≫ eF.hom := by
              rw [graphKernelMap, biprod.inr_desc]
        _ = -φ := by
              simp [eG, eF, Functor.map_neg, Adjunction.counit_naturality,
                Preadditive.comp_neg]
        _ = biprod.inr ≫ f' := by simp [f']
  have h : L.map (graphKernelMap adj F φ) ≫ eF.hom = sourceIso.hom ≫ f' := by
    calc
      L.map (graphKernelMap adj F φ) ≫ eF.hom =
          sourceIso.hom ≫ (sourceIso.inv ≫ L.map (graphKernelMap adj F φ) ≫ eF.hom) := by
            simp
      _ = sourceIso.hom ≫ f' := by rw [h']
  exact PreservesKernel.iso L (graphKernelMap adj F φ) ≪≫
    kernel.mapIso (L.map (graphKernelMap adj F φ)) f' sourceIso eF h ≪≫
      standardGraphKernelIso φ

/-- The identification of `L.obj (graphKernel adj F φ)` with `G` is induced by the second
projection of the direct sum followed by the counit of the adjunction. -/
theorem graphKernelPullbackIso_hom :
    (graphKernelPullbackIso adj F φ).hom =
      L.map (kernel.ι (graphKernelMap adj F φ) ≫ biprod.snd) ≫ adj.counit.app G := by
  simp only [graphKernelPullbackIso, graphKernel, Iso.trans_hom, standardGraphKernelIso,
    kernel.mapIso_hom, kernel.map]
  simp only [← Category.assoc, kernel.lift_ι]
  rw [PreservesKernel.iso_hom, kernelComparison_comp_ι]
  simp only [Functor.map_comp, Functor.mapBiprod_hom, biprod.mapIso_hom, Category.assoc,
    biprod.map_snd]
  simp only [← Category.assoc, biprod.lift_snd, asIso_hom]

/-- Under the identification of `L.obj (graphKernel adj F φ)` with `G`, the image of the
projection to `F` is `φ`. -/
theorem graphKernelPullbackIso_hom_comp :
    (graphKernelPullbackIso adj F φ).hom ≫ φ = L.map (graphKernelProjection adj F φ) := by
  rw [graphKernelPullbackIso_hom, graphKernelProjection]
  have hk := graphKernel_ι_comp_unit adj F φ
  dsimp only [graphKernel]
  simp only [Category.assoc, ← adj.counit_naturality φ, ← Functor.map_comp_assoc, ← hk]
  simp

end Pullback

omit [Abelian B] in
/-- If `φ` is a monomorphism then so is the projection of the graph kernel of `φ` to `F`. -/
theorem graphKernelProjection_mono [Mono φ] : Mono (graphKernelProjection adj F φ) := by
  have : PreservesLimitsOfShape WalkingCospan R :=
    (adj.rightAdjoint_preservesLimits).preservesLimitsOfShape
  have : R.PreservesMonomorphisms := preservesMonomorphisms_of_preservesLimitsOfShape R
  have hk := graphKernel_ι_comp_unit adj F φ
  show Mono (kernel.ι (graphKernelMap adj F φ) ≫ biprod.fst)
  refine ⟨fun {Z} a b hab => ?_⟩
  refine (cancel_mono (kernel.ι (graphKernelMap adj F φ))).1
    (biprod.hom_ext _ _ (by simpa only [Category.assoc] using hab) ?_)
  rw [← cancel_mono (R.map φ)]
  simp only [Category.assoc, ← hk, reassoc_of% hab]

end Stacks.GraphKernel

end
