module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationClosedFibreGlueing

/-!
# Glueing algebraic spaces of finite presentation at a point outside a retrocompact open

Let `S` be a scheme, let `U ⊆ S` be a retrocompact open and let `s` be a point of the complement
of `U`. For an open neighbourhood `W` of `s` the open `U ∪ W` is covered by the two opens `U` and
`W`, so Stacks 0E8Z identifies the algebraic spaces of finite presentation over `U ∪ W` with the
`2`-fibre product `FP_U ×_{FP_{U ∩ W}} FP_W`. Stacks 0E91 passes to the limit over the affine
open neighbourhoods `W` of `s`: with `Spec 𝒪_{S,s}` the limit of those neighbourhoods and
`V = Spec 𝒪_{S,s} ∩ U` the limit of their intersections with `U` — each quasi-compact, because
`U` is retrocompact in `S` — the comparison functor

`colim_{s ∈ U' ⊇ U open} FP_{U'} ⟶ FP_U ×_{FP_V} FP_{Spec 𝒪_{S,s}}`

is an equivalence of categories. Unlike in Stacks 0E90, where the point is closed and `U` is its
complement, so that the only admissible `U'` is `S` itself, here the open `U'` genuinely varies
and the left-hand side is a filtered `2`-colimit of categories.

This file proves the formal combination, for a cofiltered system of stages `Z i` — the opens
`U ∪ W i` — each covered by `U` and by `W i`, an object `M` of the big fppf site under the
system `W` and an object `N` under the system `Wn` of the intersections `W i ∩ U`: base change
exhibits the `2`-fibre product `FP_U ×_{FP_N} FP_M` as the filtered `2`-colimit of the
categories `FP_{Z i}`, as soon as `FP_M` and `FP_N` are the `2`-colimits of the `FP_{W i}` and of
the `FP_{Wn i}` (in the form of `IsFinitePresentationColimit` of
`StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationClosedFibreGlueing`) and base
change is an equivalence at each stage. The specialisation to Stacks 0E91 itself, where these
inputs are proved, is in
`StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationLocalRingGlueingRealised`.

The conclusion of this file is stated the way an equivalence out of a filtered `2`-colimit means
concretely, which is the shape in which `IsFinitePresentationColimit` states the colimit
identifications it takes as input: every object of the `2`-fibre product is, up to isomorphism,
the image of an object over some stage; every morphism between the images of two objects of a
stage is the image of a morphism at a later stage; and two morphisms of a stage whose images
agree already agree at a later stage. A morphism of the `2`-fibre product is a pair of
morphisms, so the fullness condition is read on the two components. The `2`-colimit category
`AlgebraicGeometry.FinitePresentationSpacesOver.StageColimit` and the equivalence out of it are
built from these three conditions in
`StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationStageColimitEquivalence`.

## Main definitions

* `AlgebraicGeometry.FinitePresentationSpacesOver.glueingFunctorFactorIso`: the comparison
  between the comparison functors of a square over two bases, namely base change along the
  comparison of the bases; its two components are the comparisons of the factorisations of the
  two legs.
* `AlgebraicGeometry.FinitePresentationSpacesOver.IsGlueingColimitEquivalence`: the
  conclusion of Stacks 0E91, the three conditions above.

The comparison functor out of a stage is not a new definition: it is
`AlgebraicGeometry.FinitePresentationSpacesOver.glueingFunctor B S hS (w i)` of
`StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationSlice` for the square `w i` over the
stage `Z i`, which takes an algebraic space of finite presentation over `Z i` to its base
changes to `U` and to `M` together with the canonical identification of their further base
changes to `N`.

## Main results

* `CategoryTheory.Over.pullbackSquareObjIso_factor` and
  `AlgebraicGeometry.FinitePresentationSpacesOver.baseChangeSquareIso_factor`: the coherence
  identity between the comparison isomorphisms of a square read over two bases and the
  comparisons of the factorisations of its two legs.
* `AlgebraicGeometry.FinitePresentationSpacesOver.representsFactor_of_full`,
  `AlgebraicGeometry.FinitePresentationSpacesOver.representsFactor_trans` and
  `AlgebraicGeometry.FinitePresentationSpacesOver.representsFactor_descend`: a morphism found at
  a later stage of a factorisation base changes to the given morphism over the composite, this
  property transports to a longer factorisation, and it descends through the other
  factorisation.
* `AlgebraicGeometry.FinitePresentationSpacesOver.glueingSquare` and
  `AlgebraicGeometry.FinitePresentationSpacesOver.glueingCone`: the square over a stage, and the
  cone property of the structure morphisms of `M` to the stages; both are derived from the data
  of the situation and are the two proofs the conclusion refers to.
* `AlgebraicGeometry.FinitePresentationSpacesOver.essSurj_glueingColimit`,
  `AlgebraicGeometry.FinitePresentationSpacesOver.full_glueingColimit` and
  `AlgebraicGeometry.FinitePresentationSpacesOver.faithful_glueingColimit`: the three
  conditions.
* `AlgebraicGeometry.FinitePresentationSpacesOver.isGlueingColimitEquivalence_of_colimit`:
  **the `2`-fibre product is the filtered `2`-colimit of the categories over the stages**, for
  an abstract system of stages; it is the formal step of Stacks 0E91.

## The proof, and where its inputs come from

The arguments are the ones of Stacks 0E91. Essential surjectivity: the object over `M` comes
from a stage `W i`, the comparison over `N` descends to an isomorphism over some `Wn j`, and the
glueing datum so obtained over the stage `Z j` is the image of a space over `Z j`. Fullness: the
component over `M` comes from a stage, the square condition of the `2`-fibre product then holds
over a later `Wn k`, and at the stage `Z k` the comparison functor is full. Faithfulness: the two
morphisms agree after base change to some `W j`, hence their images at the stage `Z j` agree.

The theorem is stated for an abstract system of stages, and takes three inputs:

* `hloc : IsFinitePresentationColimit B S hS W M pM hpM`, that base change along the cone `pM`
  exhibits `FP_M` as the cofiltered `2`-colimit of the `FP_{W i}`;
* `hoverlap : IsFinitePresentationColimit B S hS Wn N pN hpN`, the same for `FP_N` and the
  `FP_{Wn i}`;
* `hstage : ∀ i, (glueingFunctor B S hS (hsqW i).w).IsEquivalence`, Stacks 0E8Z at the stage.

For the situation of Stacks 0E91 — `M = Spec 𝒪_{S,s}`, `W i` the affine open neighbourhoods of
`s` inside a fixed one, `Wn i = W i ∩ U`, `N = V` and `Z i = U ∪ W i` — all three are theorems of
this library: `hloc` is
`FinitePresentationSpacesOver.isFinitePresentationColimit_restrictedSpecStalkSiteCone`,
`hoverlap` is
`AlgebraicGeometry.FinitePresentationSpacesOver.isFinitePresentationColimit_opensSpecStalkSiteCone`
(which uses that `U` is retrocompact in `S`, so that the `W i ∩ U` are quasi-compact), and
`hstage` is
`AlgebraicGeometry.FinitePresentationSpacesOver.isEquivalence_glueingFunctor_glueingStage`, from
Stacks 0E8Z over a subterminal base
(`AlgebraicGeometry.FinitePresentationSpacesOver.isEquivalence_glueingFunctor_of_mono_hom`).
They are combined with the theorem of this file in
`AlgebraicGeometry.FinitePresentationSpacesOver.isGlueingColimitEquivalence_specStalk`, and the
equivalence of categories of Stacks 0E91 is
`AlgebraicGeometry.FinitePresentationSpacesOver.isEquivalence_specStalkStageColimitFunctor`, both
in `StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationLocalRingGlueingRealised`.

## Implementation notes

All the comparison isomorphisms are the pinned ones of
`StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationClosedFibreGlueing`: base change
along a composite is compared with the iterated base change by the uniqueness of a pullback, so
each comparison is determined by its composites with the projections. The one new coherence
identity needed here, `baseChangeSquareIso_factor`, is proved by that file's recipe: transport to
the slice of presheaves along the fully faithful inclusion and check the composites with the
chain of projections of the iterated pullback.

The three generic lemmas whose names begin with `representsFactor` replace the lemmas
`representsOverM_of_full` and `representsOverM_trans` of Stacks 0E90, which are stated for the
canonical morphisms to the terminal object of the site. Here the base of a stage varies, so the
factorisations are carried as explicit equations instead; apart from that the proofs are the
same. Stating the final descent step, `representsFactor_descend`, as a generic lemma rather than
inline is what makes it usable: in place, the morphisms are typed through the projections of the
comparison functor, and the rewriting of the associativity of composition does not fire.

## References

* [Stacks Project, Tag 0E91](https://stacks.math.columbia.edu/tag/0E91)
* [Stacks Project, Tag 0E90](https://stacks.math.columbia.edu/tag/0E90)
* [Stacks Project, Tag 0E8Z](https://stacks.math.columbia.edu/tag/0E8Z)
* [Stacks Project, Tag 07SK](https://stacks.math.columbia.edu/tag/07SK)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace CategoryTheory.Over

variable {C : Type*} [Category C] [HasPullbacks C]

/-- **The comparison isomorphisms of a square over two bases are compatible with the
comparisons of the factorisations of the two legs.** Let `wi` and `wj` be commutative squares
on the same pair of legs `iu` and `im`, over `Zi` and over `Zj` respectively, and let
`ez : Zj ⟶ Zi` factor both legs of the first square through the second. -/
theorem pullbackSquareObjIso_factor {Zi Zj U' M' N' : C} {jUi : U' ⟶ Zi} {jMi : M' ⟶ Zi}
    {jUj : U' ⟶ Zj} {jMj : M' ⟶ Zj} {ez : Zj ⟶ Zi} {iu : N' ⟶ U'} {im : N' ⟶ M'}
    (wi : iu ≫ jUi = im ≫ jMi) (wj : iu ≫ jUj = im ≫ jMj) (hU : jUj ≫ ez = jUi)
    (hM : jMj ≫ ez = jMi) (A : Over Zi) :
    (Over.pullback iu).map (pullbackFactorObjIso hU A).hom ≫
        (pullbackSquareObjIso wj ((Over.pullback ez).obj A)).hom =
      (pullbackSquareObjIso wi A).hom ≫ (Over.pullback im).map (pullbackFactorObjIso hM A).hom := by
  apply Over.OverMorphism.ext
  rw [Over.comp_left, Over.comp_left]
  apply (isPullback_pullback_snd_pullback_snd_pullback_of_comp (f := im) (g := jMj) (k := ez)
    rfl rfl A).hom_ext
  · simp
  · simp

end CategoryTheory.Over

namespace AlgebraicGeometry.FinitePresentationSpacesOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The comparison isomorphisms of a square over two bases are compatible with the
comparisons of the factorisations of its two legs**, read in the categories of algebraic spaces
of finite presentation. -/
theorem baseChangeSquareIso_factor {Zi Zj U' M' N' : BigFppfOver B S hS} {jUi : U' ⟶ Zi}
    {jMi : M' ⟶ Zi} {jUj : U' ⟶ Zj} {jMj : M' ⟶ Zj} {ez : Zj ⟶ Zi} {iu : N' ⟶ U'}
    {im : N' ⟶ M'} (wi : iu ≫ jUi = im ≫ jMi) (wj : iu ≫ jUj = im ≫ jMj)
    (hU : jUj ≫ ez = jUi) (hM : jMj ≫ ez = jMi)
    (A : FinitePresentationSpacesOver B S hS Zi) :
    (baseChange B S hS iu).map ((baseChangeFactorIso B S hS hU).hom.app A) ≫
        (baseChangeSquareIso B S hS wj).hom.app ((baseChange B S hS ez).obj A) =
      (baseChangeSquareIso B S hS wi).hom.app A ≫
        (baseChange B S hS im).map ((baseChangeFactorIso B S hS hM).hom.app A) := by
  refine (ObjectProperty.ι (IsFinitePresentationSpaceOver B S hS N')).map_injective ?_
  simp only [Functor.map_comp, baseChangeSquareIso_hom_app_left, ι_map_baseChange_map,
    baseChangeFactorIso_hom_app_left]
  exact Over.pullbackSquareObjIso_factor (by rw [← Functor.map_comp, ← Functor.map_comp, wi])
    (by rw [← Functor.map_comp, ← Functor.map_comp, wj]) (by rw [← Functor.map_comp, hU])
    (by rw [← Functor.map_comp, hM]) A.obj

/-- **The comparison functors attached to a square over two bases differ by base change along
the comparison of the bases.** The components of the isomorphism are the comparisons of the
factorisations of the two legs; that they form a morphism of the `2`-fibre product is
`AlgebraicGeometry.FinitePresentationSpacesOver.baseChangeSquareIso_factor`. -/
noncomputable def glueingFunctorFactorIso {Zi Zj U' M' N' : BigFppfOver B S hS}
    {jUi : U' ⟶ Zi} {jMi : M' ⟶ Zi} {jUj : U' ⟶ Zj} {jMj : M' ⟶ Zj} {ez : Zj ⟶ Zi}
    {iu : N' ⟶ U'} {im : N' ⟶ M'} (wi : iu ≫ jUi = im ≫ jMi) (wj : iu ≫ jUj = im ≫ jMj)
    (hU : jUj ≫ ez = jUi) (hM : jMj ≫ ez = jMi) :
    glueingFunctor B S hS wi ≅ baseChange B S hS ez ⋙ glueingFunctor B S hS wj :=
  NatIso.ofComponents
    (fun A ↦ ObjectProperty.isoMk _ (Comma.isoMk (Iso.app (baseChangeFactorIso B S hS hU) A)
      (Iso.app (baseChangeFactorIso B S hS hM) A)
      (baseChangeSquareIso_factor B S hS wi wj hU hM A)))
    (fun {_ _} f ↦ ObjectProperty.hom_ext _ (Comma.hom_ext _ _
      ((baseChangeFactorIso B S hS hU).hom.naturality f)
      ((baseChangeFactorIso B S hS hM).hom.naturality f)))

/-- The first component of the comparison of the two comparison functors is the comparison of
the factorisation of the first leg. -/
@[simp]
theorem glueingFunctorFactorIso_hom_app_hom_left {Zi Zj U' M' N' : BigFppfOver B S hS}
    {jUi : U' ⟶ Zi} {jMi : M' ⟶ Zi} {jUj : U' ⟶ Zj} {jMj : M' ⟶ Zj} {ez : Zj ⟶ Zi}
    {iu : N' ⟶ U'} {im : N' ⟶ M'} (wi : iu ≫ jUi = im ≫ jMi) (wj : iu ≫ jUj = im ≫ jMj)
    (hU : jUj ≫ ez = jUi) (hM : jMj ≫ ez = jMi)
    (A : FinitePresentationSpacesOver B S hS Zi) :
    ((glueingFunctorFactorIso B S hS wi wj hU hM).hom.app A).hom.left =
      (baseChangeFactorIso B S hS hU).hom.app A :=
  rfl

/-- The second component of the comparison of the two comparison functors is the comparison of
the factorisation of the second leg. -/
@[simp]
theorem glueingFunctorFactorIso_hom_app_hom_right {Zi Zj U' M' N' : BigFppfOver B S hS}
    {jUi : U' ⟶ Zi} {jMi : M' ⟶ Zi} {jUj : U' ⟶ Zj} {jMj : M' ⟶ Zj} {ez : Zj ⟶ Zi}
    {iu : N' ⟶ U'} {im : N' ⟶ M'} (wi : iu ≫ jUi = im ≫ jMi) (wj : iu ≫ jUj = im ≫ jMj)
    (hU : jUj ≫ ez = jUi) (hM : jMj ≫ ez = jMi)
    (A : FinitePresentationSpacesOver B S hS Zi) :
    ((glueingFunctorFactorIso B S hS wi wj hU hM).hom.app A).hom.right =
      (baseChangeFactorIso B S hS hM).hom.app A :=
  rfl

/-- **A morphism of the base changes along the second factor of a factorisation represents a
given morphism over the composite.** This is the step of fullness: a morphism `h'` found at a
later stage, compatible with a morphism `mR` over the vertex, transports to a morphism whose
base change along the cone is `mR`. -/
theorem representsFactor_of_full {P Q R T : BigFppfOver B S hS} {a : P ⟶ Q} {b : Q ⟶ R}
    {c : R ⟶ T} {ab : P ⟶ R} {bc : Q ⟶ T} {abc : P ⟶ T} (hab : a ≫ b = ab) (hbc : b ≫ c = bc)
    (h₁ : a ≫ bc = abc) (h₂ : ab ≫ c = abc)
    {X Y : FinitePresentationSpacesOver B S hS T}
    {mR : (baseChange B S hS abc).obj X ⟶ (baseChange B S hS abc).obj Y}
    {h' : (baseChange B S hS b).obj ((baseChange B S hS c).obj X) ⟶
      (baseChange B S hS b).obj ((baseChange B S hS c).obj Y)}
    (hcompat : (baseChangeFactorIso B S hS hab).hom.app ((baseChange B S hS c).obj X) ≫
        (baseChange B S hS a).map h' =
      ((baseChangeFactorIso B S hS h₂).inv.app X ≫ mR ≫
          (baseChangeFactorIso B S hS h₂).hom.app Y) ≫
        (baseChangeFactorIso B S hS hab).hom.app ((baseChange B S hS c).obj Y)) :
    (baseChangeFactorIso B S hS h₁).hom.app X ≫ (baseChange B S hS a).map
        ((baseChangeFactorIso B S hS hbc).hom.app X ≫ h' ≫
          (baseChangeFactorIso B S hS hbc).inv.app Y) =
      mR ≫ (baseChangeFactorIso B S hS h₁).hom.app Y := by
  have hY : (baseChangeFactorIso B S hS h₂).hom.app Y ≫
        (baseChangeFactorIso B S hS hab).hom.app ((baseChange B S hS c).obj Y) ≫
          (baseChange B S hS a).map ((baseChangeFactorIso B S hS hbc).inv.app Y) =
      (baseChangeFactorIso B S hS h₁).hom.app Y := by
    rw [← Category.assoc, ← baseChangeFactorIso_assoc B S hS hab hbc h₁ h₂ Y, Category.assoc,
      ← Functor.map_comp, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id]
    simp
  rw [Functor.map_comp, Functor.map_comp, ← Category.assoc,
    baseChangeFactorIso_assoc B S hS hab hbc h₁ h₂ X, Category.assoc,
    ← Category.assoc ((baseChangeFactorIso B S hS hab).hom.app _), hcompat, Category.assoc,
    Category.assoc, Iso.hom_inv_id_app_assoc, Category.assoc, hY]

/-- The property of base changing to a given morphism over the vertex transports along the
comparison of a longer factorisation. -/
theorem representsFactor_trans {P Q R T : BigFppfOver B S hS} {a : P ⟶ Q} {b : Q ⟶ R}
    {c : R ⟶ T} {ab : P ⟶ R} {bc : Q ⟶ T} {abc : P ⟶ T} (hab : a ≫ b = ab) (hbc : b ≫ c = bc)
    (h₁ : a ≫ bc = abc) (h₂ : ab ≫ c = abc)
    {X Y : FinitePresentationSpacesOver B S hS T}
    {mR : (baseChange B S hS abc).obj X ⟶ (baseChange B S hS abc).obj Y}
    {g : (baseChange B S hS c).obj X ⟶ (baseChange B S hS c).obj Y}
    (hg : (baseChangeFactorIso B S hS h₂).hom.app X ≫ (baseChange B S hS ab).map g =
      mR ≫ (baseChangeFactorIso B S hS h₂).hom.app Y) :
    (baseChangeFactorIso B S hS h₁).hom.app X ≫ (baseChange B S hS a).map
        ((baseChangeFactorIso B S hS hbc).hom.app X ≫ (baseChange B S hS b).map g ≫
          (baseChangeFactorIso B S hS hbc).inv.app Y) =
      mR ≫ (baseChangeFactorIso B S hS h₁).hom.app Y := by
  refine representsFactor_of_full B S hS hab hbc h₁ h₂ ?_
  have hg' : (baseChange B S hS ab).map g = (baseChangeFactorIso B S hS h₂).inv.app X ≫ mR ≫
      (baseChangeFactorIso B S hS h₂).hom.app Y := by
    rw [← hg, Iso.inv_hom_id_app_assoc]
  rw [← hg']
  exact ((baseChangeFactorIso B S hS hab).hom.naturality g).symm

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for the base changes and factorisation isomorphisms over the big fppf site
-- is heavy
/-- **A morphism found at a later stage of a factorisation represents a given morphism over the
composite, read through the other factorisation.** The hypotheses are that `hk'` represents `mR`
over the longer factorisation and that `f₀` base changes to `hk'`. -/
theorem representsFactor_descend {P Q R T : BigFppfOver B S hS} {a : P ⟶ Q} {b : Q ⟶ R}
    {c : R ⟶ T} {ab : P ⟶ R} {bc : Q ⟶ T} {abc : P ⟶ T} (hab : a ≫ b = ab) (hbc : b ≫ c = bc)
    (h₁ : a ≫ bc = abc) (h₂ : ab ≫ c = abc)
    {X Y : FinitePresentationSpacesOver B S hS T}
    {mR : (baseChange B S hS abc).obj X ⟶ (baseChange B S hS abc).obj Y}
    {f₀ : (baseChange B S hS c).obj X ⟶ (baseChange B S hS c).obj Y}
    {hk' : (baseChange B S hS bc).obj X ⟶ (baseChange B S hS bc).obj Y}
    (hrep : (baseChangeFactorIso B S hS h₁).hom.app X ≫ (baseChange B S hS a).map hk' =
      mR ≫ (baseChangeFactorIso B S hS h₁).hom.app Y)
    (hdesc : (baseChangeFactorIso B S hS hbc).hom.app X ≫ (baseChange B S hS b).map f₀ =
      hk' ≫ (baseChangeFactorIso B S hS hbc).hom.app Y) :
    mR ≫ (baseChangeFactorIso B S hS h₂).hom.app Y =
      (baseChangeFactorIso B S hS h₂).hom.app X ≫ (baseChange B S hS ab).map f₀ := by
  have hassocX := baseChangeFactorIso_assoc B S hS hab hbc h₁ h₂ X
  have hassocY := baseChangeFactorIso_assoc B S hS hab hbc h₁ h₂ Y
  refine (cancel_mono ((baseChangeFactorIso B S hS hab).hom.app
    ((baseChange B S hS c).obj Y))).mp ?_
  rw [Category.assoc, Category.assoc, (baseChangeFactorIso B S hS hab).hom.naturality f₀,
    ← hassocY, ← reassoc_of% hassocX, ← Category.assoc, ← hrep, Category.assoc]
  simp only [Functor.comp_map, ← Functor.map_comp]
  rw [hdesc]

/-! ### The situation of Stacks 0E91 -/

section Colimit

variable {U M N : BigFppfOver B S hS} {iU : N ⟶ U} {iM : N ⟶ M}
  {I : Type u} [Category.{u} I] [IsCofiltered I] {W Wn Z : I ⥤ BigFppfOver B S hS}
  {jU : (i : I) → (U ⟶ Z.obj i)} {jW : (i : I) → (W.obj i ⟶ Z.obj i)}
  {jM : (i : I) → (M ⟶ Z.obj i)} {iUn : (i : I) → (Wn.obj i ⟶ U)}
  {iWn : (i : I) → (Wn.obj i ⟶ W.obj i)} {pM : (i : I) → (M ⟶ W.obj i)}
  {pN : (i : I) → (N ⟶ Wn.obj i)}
  (hsqW : ∀ i, IsPullback (iUn i) (iWn i) (jU i) (jW i))
  (hjUZ : ∀ {i j : I} (e : j ⟶ i), jU j ≫ Z.map e = jU i)
  (hjWZ : ∀ {i j : I} (e : j ⟶ i), W.map e ≫ jW i = jW j ≫ Z.map e)
  (hjMZ : ∀ {i j : I} (e : j ⟶ i), jM j ≫ Z.map e = jM i)
  (hjMW : ∀ i, pM i ≫ jW i = jM i)
  (hpM : ∀ {i j : I} (e : j ⟶ i), pM j ≫ W.map e = pM i)
  (hpN : ∀ {i j : I} (e : j ⟶ i), pN j ≫ Wn.map e = pN i)
  (hpNU : ∀ i, pN i ≫ iUn i = iU) (hpNW : ∀ i, pN i ≫ iWn i = iM ≫ pM i)
  (hiUn : ∀ {i j : I} (e : j ⟶ i), Wn.map e ≫ iUn i = iUn j)
  (hiWn : ∀ {i j : I} (e : j ⟶ i), Wn.map e ≫ iWn i = iWn j ≫ W.map e)
  (w : ∀ i, iU ≫ jU i = iM ≫ jM i)
  (hloc : IsFinitePresentationColimit B S hS W M pM hpM)
  (hoverlap : IsFinitePresentationColimit B S hS Wn N pN hpN)
  (hstage : ∀ i, (glueingFunctor B S hS (hsqW i).w).IsEquivalence)

omit [IsCofiltered I] in
include hsqW hjMW hpNU hpNW in
/-- **The square over a stage.** The structure morphisms of `U` and of `M` to the stage
`Z i = U ∪ W i` and the two legs `iU` and `iM` of the vertex `N` form a commuting square: this
is the square whose comparison functor goes from the algebraic spaces of finite presentation
over the stage to the `2`-fibre product `FP_U ×_{FP_N} FP_M`. -/
theorem glueingSquare (i : I) : iU ≫ jU i = iM ≫ jM i := by
  rw [← hpNU i, Category.assoc, (hsqW i).w, ← Category.assoc, hpNW i, Category.assoc, hjMW i]

omit [IsCofiltered I] in
include hjWZ hjMW hpM in
/-- **The structure morphisms of `M` to the stages form a cone.** -/
theorem glueingCone {i j : I} (e : j ⟶ i) : jM j ≫ Z.map e = jM i := by
  rw [← hjMW j, Category.assoc, ← hjWZ e, ← Category.assoc, hpM e, hjMW i]

/-- **Base change exhibits the `2`-fibre product `FP_U ×_{FP_N} FP_M` as the filtered
`2`-colimit of the algebraic spaces of finite presentation over the stages `Z i`.** The three
conditions are essential surjectivity, fullness and faithfulness of the family of comparison
functors `glueingFunctor (w i)`, in the elementary form in which an equivalence out of a
filtered `2`-colimit of categories is expressed: every object of the `2`-fibre product is, up
to isomorphism, the image of an object over some stage; a morphism between the images of two
objects of a stage is the image of a morphism at a later stage; and two morphisms of a stage
whose images agree already agree at a later stage. The `2`-colimit category itself is
`AlgebraicGeometry.FinitePresentationSpacesOver.StageColimit`, and the equivalence out of it is
deduced from these three conditions in
`StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationStageColimitEquivalence`.

A morphism of the `2`-fibre product is a pair of morphisms, so the fullness condition is stated
on the two components: `f` is a morphism at the later stage `j` whose base changes to `U` and to
`M` are the two components of `m`, read through the comparisons of the factorisations of `jU i`
and of `jM i` through `Z.map e`. -/
structure IsGlueingColimitEquivalence {I : Type u} [Category.{u} I] [IsCofiltered I]
    {U M N : BigFppfOver B S hS} {iU : N ⟶ U} {iM : N ⟶ M} (Z : I ⥤ BigFppfOver B S hS)
    (jU : (i : I) → (U ⟶ Z.obj i)) (jM : (i : I) → (M ⟶ Z.obj i))
    (w : ∀ i, iU ≫ jU i = iM ≫ jM i)
    (hjU : ∀ {i j : I} (e : j ⟶ i), jU j ≫ Z.map e = jU i)
    (hjM : ∀ {i j : I} (e : j ⟶ i), jM j ≫ Z.map e = jM i) : Prop where
  /-- Every object of the `2`-fibre product is, up to isomorphism, the image of an algebraic
  space of finite presentation over a stage. -/
  essSurj : ∀ T : IsoComma (baseChange B S hS iU) (baseChange B S hS iM),
    ∃ (i : I) (X : FinitePresentationSpacesOver B S hS (Z.obj i)),
      Nonempty ((glueingFunctor B S hS (w i)).obj X ≅ T)
  /-- A morphism between the images of two algebraic spaces of finite presentation over a stage
  is the image of a morphism at a later stage. -/
  full : ∀ (i : I) (X Y : FinitePresentationSpacesOver B S hS (Z.obj i))
    (m : (glueingFunctor B S hS (w i)).obj X ⟶ (glueingFunctor B S hS (w i)).obj Y),
    ∃ (j : I) (e : j ⟶ i) (f : (baseChange B S hS (Z.map e)).obj X ⟶
      (baseChange B S hS (Z.map e)).obj Y),
      m.hom.left ≫ (baseChangeFactorIso B S hS (hjU e)).hom.app Y =
          (baseChangeFactorIso B S hS (hjU e)).hom.app X ≫
            (baseChange B S hS (jU j)).map f ∧
        m.hom.right ≫ (baseChangeFactorIso B S hS (hjM e)).hom.app Y =
          (baseChangeFactorIso B S hS (hjM e)).hom.app X ≫
            (baseChange B S hS (jM j)).map f
  /-- Two morphisms of algebraic spaces of finite presentation over a stage whose images agree
  already agree at a later stage. -/
  faithful : ∀ (i : I) (X Y : FinitePresentationSpacesOver B S hS (Z.obj i)) (f g : X ⟶ Y),
    (glueingFunctor B S hS (w i)).map f = (glueingFunctor B S hS (w i)).map g →
    ∃ (j : I) (e : j ⟶ i),
      (baseChange B S hS (Z.map e)).map f = (baseChange B S hS (Z.map e)).map g

include hsqW hjUZ hjWZ hjMW hpM hloc hstage in
/-- **Two morphisms over a stage with the same image in the `2`-fibre product agree at a later
stage.** Their base changes to `M` agree, so their base changes to a stage `W j` agree by
faithfulness of the colimit over the stages; together with the agreement of their base changes
to `U` this makes their images under the comparison functor of Stacks 0E8Z at the stage `j`
agree, and that functor is faithful. -/
theorem faithful_glueingColimit (i : I) (X Y : FinitePresentationSpacesOver B S hS (Z.obj i))
    (f g : X ⟶ Y) (hfg : (glueingFunctor B S hS (w i)).map f =
      (glueingFunctor B S hS (w i)).map g) :
    ∃ (j : I) (e : j ⟶ i),
      (baseChange B S hS (Z.map e)).map f = (baseChange B S hS (Z.map e)).map g := by
  have hL : (baseChange B S hS (jU i)).map f = (baseChange B S hS (jU i)).map g :=
    congrArg (fun m ↦ m.hom.left) hfg
  have hR : (baseChange B S hS (jM i)).map f = (baseChange B S hS (jM i)).map g :=
    congrArg (fun m ↦ m.hom.right) hfg
  have hRW : (baseChange B S hS (pM i)).map ((baseChange B S hS (jW i)).map f) =
      (baseChange B S hS (pM i)).map ((baseChange B S hS (jW i)).map g) :=
    AlgebraicGeometry.FinitePresentationSpacesOver.map_eq_of_natIso
      (baseChangeFactorIso B S hS (hjMW i)) hR
  obtain ⟨j, e, hje⟩ := hloc.faithful i ((baseChange B S hS (jW i)).obj X)
    ((baseChange B S hS (jW i)).obj Y) ((baseChange B S hS (jW i)).map f)
    ((baseChange B S hS (jW i)).map g) hRW
  refine ⟨j, e, ?_⟩
  have hUj : (baseChange B S hS (jU j)).map ((baseChange B S hS (Z.map e)).map f) =
      (baseChange B S hS (jU j)).map ((baseChange B S hS (Z.map e)).map g) :=
    AlgebraicGeometry.FinitePresentationSpacesOver.map_eq_of_natIso
      (baseChangeFactorIso B S hS (hjUZ e)) hL
  have hWj : (baseChange B S hS (jW j)).map ((baseChange B S hS (Z.map e)).map f) =
      (baseChange B S hS (jW j)).map ((baseChange B S hS (Z.map e)).map g) :=
    AlgebraicGeometry.FinitePresentationSpacesOver.map_eq_of_natIso
      (baseChangeSquareIso B S hS (hjWZ e)) hje
  have hequiv := hstage j
  exact (glueingFunctor B S hS (hsqW j).w).map_injective
    (ObjectProperty.hom_ext _ (Comma.hom_ext _ _ hUj hWj))

include hsqW hjUZ hjWZ hjMZ hjMW hpM hpNU hpNW hiUn hiWn hloc hoverlap hstage in
/-- **A morphism between the images of two algebraic spaces of finite presentation over a stage
comes from a later stage.** Its component over `M` comes from a stage `W j` by fullness of the
colimit over the stages; the square condition of the `2`-fibre product then holds over a later
`Wn k` by faithfulness of the colimit over the intersections with `U`; at the stage `Z k` the
comparison functor of Stacks 0E8Z is full, and the morphism it produces has the two components
of the given morphism, read through the comparisons of the factorisations. -/
theorem full_glueingColimit (i : I) (X Y : FinitePresentationSpacesOver B S hS (Z.obj i))
    (m : (glueingFunctor B S hS (w i)).obj X ⟶ (glueingFunctor B S hS (w i)).obj Y) :
    ∃ (j : I) (e : j ⟶ i) (f : (baseChange B S hS (Z.map e)).obj X ⟶
      (baseChange B S hS (Z.map e)).obj Y),
      m.hom.left ≫ (baseChangeFactorIso B S hS (hjUZ e)).hom.app Y =
          (baseChangeFactorIso B S hS (hjUZ e)).hom.app X ≫
            (baseChange B S hS (jU j)).map f ∧
        m.hom.right ≫ (baseChangeFactorIso B S hS (hjMZ e)).hom.app Y =
          (baseChangeFactorIso B S hS (hjMZ e)).hom.app X ≫
            (baseChange B S hS (jM j)).map f := by
  obtain ⟨j, e, h', hcompat⟩ := hloc.full i ((baseChange B S hS (jW i)).obj X)
    ((baseChange B S hS (jW i)).obj Y)
    ((baseChangeFactorIso B S hS (hjMW i)).inv.app X ≫ m.hom.right ≫
      (baseChangeFactorIso B S hS (hjMW i)).hom.app Y)
  have h₁ : pM j ≫ (W.map e ≫ jW i) = jM i := by rw [← Category.assoc, hpM e, hjMW i]
  have hrepj := representsFactor_of_full B S hS (hpM e)
    (rfl : W.map e ≫ jW i = W.map e ≫ jW i) h₁ (hjMW i) hcompat
  have hw : ∀ {a b : I} (f : b ⟶ a) (x : W.obj a ⟶ Z.obj i), iUn a ≫ jU i = iWn a ≫ x →
      iUn b ≫ jU i = iWn b ≫ (W.map f ≫ x) := fun f _ hx ↦ by
    rw [← Category.assoc, ← hiWn f, Category.assoc, ← hx, ← Category.assoc, hiUn f]
  have w₂ := hw e _ (hsqW i).w
  have hsqj := (squareCondition_iff B S hS (w i) w₂ (hpNU j) (hpNW j) h₁ hrepj).1 m.hom.w
  obtain ⟨k, e', hk⟩ := hoverlap.faithful j _ _ _ _ hsqj
  have h₁' : pM k ≫ (W.map e' ≫ W.map e ≫ jW i) = jM i := by
    rw [← Category.assoc, hpM e', h₁]
  have hrepk := representsFactor_trans B S hS (hpM e')
    (rfl : W.map e' ≫ W.map e ≫ jW i = W.map e' ≫ W.map e ≫ jW i) h₁' h₁ hrepj
  have hrep' : (baseChangeFactorIso B S hS
        (rfl : W.map e' ≫ W.map e ≫ jW i = W.map e' ≫ W.map e ≫ jW i)).hom.app X ≫
      (baseChange B S hS (W.map e')).map ((baseChangeFactorIso B S hS
        (rfl : W.map e ≫ jW i = W.map e ≫ jW i)).hom.app X ≫ h' ≫
        (baseChangeFactorIso B S hS
          (rfl : W.map e ≫ jW i = W.map e ≫ jW i)).inv.app Y) =
      ((baseChangeFactorIso B S hS
          (rfl : W.map e' ≫ W.map e ≫ jW i = W.map e' ≫ W.map e ≫ jW i)).hom.app X ≫
        (baseChange B S hS (W.map e')).map ((baseChangeFactorIso B S hS
          (rfl : W.map e ≫ jW i = W.map e ≫ jW i)).hom.app X ≫ h' ≫
          (baseChangeFactorIso B S hS
            (rfl : W.map e ≫ jW i = W.map e ≫ jW i)).inv.app Y) ≫
        (baseChangeFactorIso B S hS
          (rfl : W.map e' ≫ W.map e ≫ jW i =
            W.map e' ≫ W.map e ≫ jW i)).inv.app Y) ≫
        (baseChangeFactorIso B S hS
          (rfl : W.map e' ≫ W.map e ≫ jW i =
            W.map e' ≫ W.map e ≫ jW i)).hom.app Y := by
    simp
  have w₁' := hw e' _ w₂
  have hsqk := (squareCondition_iff B S hS w₁' w₂ (hiUn e') (hiWn e') rfl hrep').2 hk
  have hWk : jW k ≫ Z.map (e' ≫ e) = W.map e' ≫ W.map e ≫ jW i := by
    rw [Z.map_comp, ← Category.assoc, ← hjWZ e', Category.assoc, ← hjWZ e]
  have hequiv := hstage k
  let ι := glueingFunctorFactorIso B S hS w₁' (hsqW k).w (hjUZ (e' ≫ e)) hWk
  let μ : (glueingFunctor B S hS w₁').obj X ⟶ (glueingFunctor B S hS w₁').obj Y :=
    ObjectProperty.homMk (⟨m.hom.left, _, hsqk⟩ :
      ((glueingFunctor B S hS w₁').obj X).obj ⟶ ((glueingFunctor B S hS w₁').obj Y).obj)
  obtain ⟨f₀, hf₀⟩ := (glueingFunctor B S hS (hsqW k).w).map_surjective
    (ι.inv.app X ≫ μ ≫ ι.hom.app Y)
  have hkey : ι.hom.app X ≫ (glueingFunctor B S hS (hsqW k).w).map f₀ = μ ≫ ι.hom.app Y := by
    rw [hf₀, Iso.hom_inv_id_app_assoc]
  refine ⟨k, e' ≫ e, f₀, (congrArg (fun z ↦ z.hom.left) hkey).symm, ?_⟩
  have hright : (baseChangeFactorIso B S hS hWk).hom.app X ≫
      (baseChange B S hS (jW k)).map f₀ =
      _ ≫ (baseChangeFactorIso B S hS hWk).hom.app Y := congrArg (fun z ↦ z.hom.right) hkey
  exact representsFactor_descend B S hS (hjMW k) hWk h₁' (hjMZ (e' ≫ e)) hrepk hright

include hsqW hjMW hpNU hpNW hiUn hiWn hloc hoverlap hstage in
/-- **Every object of the `2`-fibre product comes from a stage.** The space over `M` comes from
a stage `W i`, and the comparison over `N` descends to an isomorphism over some `Wn j`, by the
two colimit identifications; the glueing datum so obtained over the stage `Z j` is the image of
an algebraic space of finite presentation over `Z j` by Stacks 0E8Z, and that space has the
given object as its image, because the comparison of the datum is the one induced by the
comparison at the stage. -/
theorem essSurj_glueingColimit (T : IsoComma (baseChange B S hS iU) (baseChange B S hS iM)) :
    ∃ (i : I) (X : FinitePresentationSpacesOver B S hS (Z.obj i)),
      Nonempty ((glueingFunctor B S hS (w i)).obj X ≅ T) := by
  have hT : IsIso T.obj.hom := T.property
  obtain ⟨i, Bi, ⟨ψ⟩⟩ := hloc.essSurj T.obj.right
  obtain ⟨j, e, θ', hθ'⟩ := hoverlap.essIso i ((baseChange B S hS (iUn i)).obj T.obj.left)
    ((baseChange B S hS (iWn i)).obj Bi)
    ((Iso.app (baseChangeFactorIso B S hS (hpNU i)) T.obj.left).symm ≪≫ asIso T.obj.hom ≪≫
      (baseChange B S hS iM).mapIso ψ.symm ≪≫
      (Iso.app (baseChangeSquareIso B S hS (hpNW i)) Bi).symm)
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_inv, asIso_hom,
    Functor.mapIso_hom, Category.assoc] at hθ'
  -- the comparison of the glueing datum at the stage `j`
  set φj := Iso.app (baseChangeFactorIso B S hS (hiUn e)) T.obj.left ≪≫ θ' ≪≫
    Iso.app (baseChangeSquareIso B S hS (hiWn e)) Bi with hφj
  -- the identification of the space over `M` with the base change of the stage object
  set χ := (Iso.app (baseChangeFactorIso B S hS (hpM e)) Bi).symm ≪≫ ψ with hχ
  have hrel : T.obj.hom = (baseChangeFactorIso B S hS (hpNU j)).hom.app T.obj.left ≫
      (baseChange B S hS (pN j)).map φj.hom ≫
        (baseChangeSquareIso B S hS (hpNW j)).hom.app ((baseChange B S hS (W.map e)).obj Bi) ≫
          (baseChange B S hS iM).map χ.hom := by
    rw [hφj, hχ]
    simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv, Functor.map_comp,
      Category.assoc]
    rw [reassoc_of% (baseChangeFactorIso_assoc B S hS (hpN e) (hiUn e) (hpNU j) (hpNU i)
      T.obj.left), reassoc_of% hθ']
    rw [reassoc_of% (baseChangeSquareIso_paste B S hS (hpN e) (hiWn e) (hpNW i) (hpNW j)
      (hpM e) Bi)]
    simp
  -- the glueing datum at the stage `j` and its preimage there
  have hequiv := hstage j
  obtain ⟨X, ⟨Ξ⟩⟩ := Functor.EssSurj.mem_essImage (F := glueingFunctor B S hS (hsqW j).w)
    (⟨⟨T.obj.left, (baseChange B S hS (W.map e)).obj Bi, φj.hom⟩, inferInstance⟩ :
      IsoComma (baseChange B S hS (iUn j)) (baseChange B S hS (iWn j)))
  refine ⟨j, X, ⟨ObjectProperty.isoMk _ (Comma.isoMk
    ((IsoComma.fst (baseChange B S hS (iUn j)) (baseChange B S hS (iWn j))).mapIso Ξ)
    (Iso.app (baseChangeFactorIso B S hS (hjMW j)) X ≪≫
      (baseChange B S hS (pM j)).mapIso
        ((IsoComma.snd (baseChange B S hS (iUn j)) (baseChange B S hS (iWn j))).mapIso Ξ) ≪≫ χ)
    ?_)⟩⟩
  simp only [Functor.mapIso_hom]
  exact squareCondition_of_stage B S hS (w j) (hsqW j).w (hpNU j) (hpNW j) (hjMW j) hrel
    Ξ.hom.hom.w

include hsqW hjUZ hjWZ hjMW hpM hpN hpNU hpNW hiUn hiWn hloc hoverlap hstage in
/-- **The algebraic spaces of finite presentation over the opens between `U` and `S` containing
the point `s` have the `2`-fibre product `FP_U ×_{FP_V} FP_{Spec 𝒪_{S,s}}` as their filtered
`2`-colimit**, when `M` is a cofiltered limit of the stages `W i` and `N` the corresponding
limit of the `Wn i = U ∩ W i`, and the stages `Z i = U ∪ W i` are covered by `U` and `W i`.

This is the formal step of Stacks 0E91, for an abstract system of stages: the comparison
functors `FP_{Z i} ⥤ FP_U ×_{FP_N} FP_M` are jointly essentially surjective, full and faithful
in the sense of an equivalence out of a filtered `2`-colimit, which is the content of
`AlgebraicGeometry.FinitePresentationSpacesOver.IsGlueingColimitEquivalence`. The inputs `hloc`,
`hoverlap` and `hstage` are proved for the stages of Stacks 0E91, and the tag itself is
`AlgebraicGeometry.FinitePresentationSpacesOver.isEquivalence_specStalkStageColimitFunctor`. -/
theorem isGlueingColimitEquivalence_of_colimit :
    IsGlueingColimitEquivalence B S hS Z jU jM
      (glueingSquare B S hS hsqW hjMW hpNU hpNW) hjUZ
      (glueingCone B S hS hjWZ hjMW hpM) where
  essSurj := essSurj_glueingColimit B S hS (hsqW := hsqW) (hjMW := hjMW) (hpM := hpM)
    (hpN := hpN) (hpNU := hpNU) (hpNW := hpNW) (hiUn := hiUn) (hiWn := hiWn)
    (w := glueingSquare B S hS hsqW hjMW hpNU hpNW) (hloc := hloc) (hoverlap := hoverlap)
    (hstage := hstage)
  full := full_glueingColimit B S hS (hsqW := hsqW) (hjUZ := hjUZ) (hjWZ := hjWZ)
    (hjMZ := glueingCone B S hS hjWZ hjMW hpM) (hjMW := hjMW) (hpM := hpM) (hpN := hpN)
    (hpNU := hpNU) (hpNW := hpNW) (hiUn := hiUn) (hiWn := hiWn)
    (w := glueingSquare B S hS hsqW hjMW hpNU hpNW) (hloc := hloc) (hoverlap := hoverlap)
    (hstage := hstage)
  faithful := faithful_glueingColimit B S hS (hsqW := hsqW) (hjUZ := hjUZ) (hjWZ := hjWZ)
    (hjMW := hjMW) (hpM := hpM) (w := glueingSquare B S hS hsqW hjMW hpNU hpNW) (hloc := hloc)
    (hstage := hstage)

end Colimit

end AlgebraicGeometry.FinitePresentationSpacesOver

end
