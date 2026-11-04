module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Smooth.IntegralClosureSheaf
public import StacksFrontier.AlgebraicGeometry.RelativeSpecEssSurj.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# Integral closure and smooth pullback, as an equality of subsheaves of the pullback

Let `g : Y ⟶ S` be a smooth morphism of schemes, let `𝒜` be a quasi-coherent sheaf of
`𝒪_S`-algebras and let `𝒜' ⊆ 𝒜` be the integral closure of `𝒪_S` in `𝒜`. Stacks 081K says that
`g^*𝒜'` is the integral closure of `𝒪_Y` in `g^*𝒜`. This file states and proves exactly that,
for the pullback `Stacks.AffineAlgebraEquivalence.algebraPullback` and the integral closure
`AlgebraicGeometry.Scheme.QuasicoherentAlgebra.integralClosureAlgebra` of the development: the
two subsheaves `integralClosureAlgebra (g^*𝒜)` and `g^*(integralClosureAlgebra 𝒜)` of `g^*𝒜`
have the same sections over every open of `Y`.

The mathematics is `range_integralClosureAlgebraι_app_pullback_eq` of
`StacksFrontier/AlgebraicGeometry/Morphisms/Smooth/IntegralClosureSheaf.lean`, which asserts the
same equality for `𝒜 = f_* 𝒪_X` with `f` affine, with the pullback presented as a direct image
from a fibre product and `𝒜'` presented as the direct image of the structure sheaf of the
relative normalization of `f`. The transport onto `algebraPullback` and `integralClosureAlgebra`
is invariance of the integral-closure subalgebra under an isomorphism of algebra sheaves.

## Main results

* `ringLift`, `subalgebraLift`: a morphism of algebra sheaves whose sections lie in the range of
  a second one with injective sections factors through it. With `mono_of_injective_app` this
  gives `subalgebraIsoOfRangeEq`: two subsheaves of an algebra sheaf with the same sections over
  every open are isomorphic over it.
* `image_range_integralClosureAlgebraι_app`: **the integral closure of the structure sheaf is
  invariant under an isomorphism of algebra sheaves.**
* `integralClosureAlgebraIso`: the resulting isomorphism `𝒜' ≅ ℬ'` over an isomorphism
  `𝒜 ≅ ℬ`.
* `normalizationAlgebraIso`: for `f` affine, `𝒜' ≅ (f.fromNormalization)_* 𝒪` over `f_* 𝒪_X`.
* `range_integralClosureAlgebraι_app_algebraPullback_eq`: **Stacks 081K**, for an arbitrary
  quasi-coherent `𝒪_S`-algebra and the pullback `algebraPullback g`.

## Implementation notes

The reduction to `IntegralClosureSheaf.lean` runs through three isomorphisms of algebra sheaves,
each of which the transport lemma carries the integral closure along:
`Stacks.AffineAlgebraEquivalence.pushforwardAlgebraIso`, presenting `𝒜` as `f_* 𝒪_X` for
`f = relativeSpecToBase 𝒜`; `normalizationAlgebraIso`, identifying `𝒜'` with the relative
normalization; and `Stacks.AffineAlgebraEquivalence.baseChangeAlgebraHom`, identifying the
pullback with the direct image from the fibre product. The comparison of the two presentations
of the pullback of the subalgebra is the naturality
`Stacks.AlgebraPullbackQcoh.baseChangeAlgebraHom_naturality` of the last one, together with
`pullback_map_normalizationOver` — the identification of the base change of
`Stacks.IntegralClosure.SheafLevel.normalizationOver` with
`Stacks.IntegralClosure.SheafLevel.toBaseChangeNormalizationOver`, which is Mathlib's
`AlgebraicGeometry.Scheme.Hom.toNormalization_normalizationPullback_fst`.

Subsheaves are recorded as morphisms with injective components and their equality as equality of
the ranges of those components, as in `IntegralClosureSheaf.lean`.

## References

* [Stacks Project, Tag 081K](https://stacks.math.columbia.edu/tag/081K)
* [Stacks Project, Tag 035F](https://stacks.math.columbia.edu/tag/035F)
* [Stacks Project, Tag 01LX](https://stacks.math.columbia.edu/tag/01LX)
* [Stacks Project, Tag 01SA](https://stacks.math.columbia.edu/tag/01SA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open Stacks.AffineAlgebraEquivalence AlgebraicGeometry.Scheme.QuasicoherentAlgebra

universe u

namespace Stacks.IntegralClosure.SheafLevel

/-! ### Factoring through a subsheaf -/

section Factor

/-- A morphism of commutative rings all of whose values lie in the range of an injective
morphism factors through it. -/
public def ringLift {A B C : CommRingCat.{u}} (a : A ⟶ C) (b : B ⟶ C)
    (hb : Function.Injective b) (hab : ∀ x, a x ∈ Set.range b) : A ⟶ B :=
  CommRingCat.ofHom
    { toFun := fun x => (hab x).choose
      map_one' := hb (by rw [map_one b.hom, (hab 1).choose_spec, map_one a.hom])
      map_mul' := fun x y => hb (by
        rw [map_mul b.hom, (hab x).choose_spec, (hab y).choose_spec,
          (hab (x * y)).choose_spec, map_mul a.hom])
      map_zero' := hb (by rw [map_zero b.hom, (hab 0).choose_spec, map_zero a.hom])
      map_add' := fun x y => hb (by
        rw [map_add b.hom, (hab x).choose_spec, (hab y).choose_spec,
          (hab (x + y)).choose_spec, map_add a.hom]) }

/-- The defining property of `ringLift`: it is a factorisation of `a` through `b`. -/
public theorem ringLift_apply {A B C : CommRingCat.{u}} (a : A ⟶ C) (b : B ⟶ C)
    (hb : Function.Injective b) (hab : ∀ x, a x ∈ Set.range b) (x : A) :
    b (ringLift a b hb hab x) = a x :=
  (hab x).choose_spec

variable {X : Scheme.{u}}

/-- The isomorphism of presheaves of rings underlying an isomorphism of algebra sheaves. -/
public def presheafIsoOfIso {A B : X.QuasicoherentAlgebra} (e : A ≅ B) :
    A.right.presheaf ≅ B.right.presheaf where
  hom := e.hom.right.hom
  inv := e.inv.right.hom
  hom_inv_id := congrArg (fun k : A ⟶ A => (Under.Hom.right k).hom) e.hom_inv_id
  inv_hom_id := congrArg (fun k : B ⟶ B => (Under.Hom.right k).hom) e.inv_hom_id

/-- An isomorphism of algebra sheaves is bijective on sections over every open. -/
public theorem bijective_app_of_iso {A B : X.QuasicoherentAlgebra} (e : A ≅ B) (W : Opens X) :
    Function.Bijective (e.hom.right.hom.app (op W)) :=
  ConcreteCategory.bijective_of_isIso ((presheafIsoOfIso e).app (op W)).hom

/-- An invertible morphism of algebra sheaves is injective on sections over every open. -/
public theorem injective_right_app_of_isIso {A B : X.QuasicoherentAlgebra} (h : A ⟶ B) [IsIso h]
    (W : Opens X) : Function.Injective (h.right.hom.app (op W)) :=
  (bijective_app_of_iso (asIso h) W).1

/-- An invertible morphism of algebra sheaves is surjective on sections over every open. -/
public theorem surjective_right_app_of_isIso {A B : X.QuasicoherentAlgebra} (h : A ⟶ B) [IsIso h]
    (W : Opens X) : Function.Surjective (h.right.hom.app (op W)) :=
  (bijective_app_of_iso (asIso h) W).2

/-- An isomorphism of algebra sheaves is bijective on every stalk. -/
public theorem bijective_stalkFunctor_map_of_iso {A B : X.QuasicoherentAlgebra} (e : A ≅ B)
    (x : X) :
    Function.Bijective ((TopCat.Presheaf.stalkFunctor CommRingCat x).map e.hom.right.hom) :=
  ConcreteCategory.bijective_of_isIso
    (((TopCat.Presheaf.stalkFunctor CommRingCat x).mapIso (presheafIsoOfIso e)).hom)

/-- The sections of a morphism of algebra sheaves commute with restriction. -/
public theorem right_app_map {A B : X.QuasicoherentAlgebra} (φ : A ⟶ B) {U V : (Opens X)ᵒᵖ}
    (i : U ⟶ V) (y : A.right.presheaf.obj U) :
    φ.right.hom.app V (A.right.presheaf.map i y) =
      B.right.presheaf.map i (φ.right.hom.app U y) := by
  rw [← ConcreteCategory.comp_apply, φ.right.hom.naturality i, ConcreteCategory.comp_apply]

/-- The morphism of sheaves of rings underlying `subalgebraLift`. -/
public def subalgebraLiftHom {F H G : X.QuasicoherentAlgebra} (ψ : F ⟶ G) (φ : H ⟶ G)
    (hφ : ∀ W : Opens X, Function.Injective (φ.right.hom.app (op W)))
    (hr : ∀ W : Opens X, Set.range (ψ.right.hom.app (op W)) ⊆
      Set.range (φ.right.hom.app (op W))) :
    F.right ⟶ H.right where
  hom :=
    { app := fun U => ringLift (ψ.right.hom.app U) (φ.right.hom.app U) (hφ U.unop)
        (fun x => hr U.unop ⟨x, rfl⟩)
      naturality := fun {U V} i => by
        apply CommRingCat.hom_ext
        apply RingHom.ext
        intro x
        refine hφ V.unop ?_
        rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, ringLift_apply,
          right_app_map φ i, ringLift_apply]
        exact right_app_map ψ i x }

/-- `subalgebraLiftHom` is a factorisation of `ψ` through `φ` on underlying sheaves of rings. -/
public theorem subalgebraLiftHom_comp {F H G : X.QuasicoherentAlgebra} (ψ : F ⟶ G) (φ : H ⟶ G)
    (hφ : ∀ W : Opens X, Function.Injective (φ.right.hom.app (op W)))
    (hr : ∀ W : Opens X, Set.range (ψ.right.hom.app (op W)) ⊆
      Set.range (φ.right.hom.app (op W))) :
    subalgebraLiftHom ψ φ hφ hr ≫ φ.right = ψ.right := by
  apply CategoryTheory.Sheaf.hom_ext
  apply NatTrans.ext
  refine funext fun U => ?_
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  exact ringLift_apply (ψ.right.hom.app U) (φ.right.hom.app U) (hφ U.unop)
    (fun y => hr U.unop ⟨y, rfl⟩) x

/-- A morphism of algebra sheaves injective on sections over every open is a monomorphism on
underlying sheaves of rings. -/
public theorem mono_right_of_injective_app {H G : X.QuasicoherentAlgebra} (φ : H ⟶ G)
    (hφ : ∀ W : Opens X, Function.Injective (φ.right.hom.app (op W))) : Mono φ.right := by
  refine (Sheaf.Hom.mono_iff_presheaf_mono _ _ _).mpr ?_
  refine (NatTrans.mono_iff_mono_app _).mpr fun U => ?_
  exact ConcreteCategory.mono_of_injective _ (hφ U.unop)

/-- A morphism of algebra sheaves injective on sections over every open is a monomorphism. -/
public theorem mono_of_injective_app {H G : X.QuasicoherentAlgebra} (φ : H ⟶ G)
    (hφ : ∀ W : Opens X, Function.Injective (φ.right.hom.app (op W))) : Mono φ :=
  have := mono_right_of_injective_app φ hφ
  Under.mono_of_mono_right _

/-- A morphism of algebra sheaves whose sections over every open lie in the range of the sections
of a morphism injective on sections factors through it. -/
public def subalgebraLift {F H G : X.QuasicoherentAlgebra} (ψ : F ⟶ G) (φ : H ⟶ G)
    (hφ : ∀ W : Opens X, Function.Injective (φ.right.hom.app (op W)))
    (hr : ∀ W : Opens X, Set.range (ψ.right.hom.app (op W)) ⊆
      Set.range (φ.right.hom.app (op W))) :
    F ⟶ H :=
  have := mono_right_of_injective_app φ hφ
  Under.homMk (subalgebraLiftHom ψ φ hφ hr) ((cancel_mono φ.right).mp (by
    rw [Category.assoc, subalgebraLiftHom_comp, Under.w ψ, Under.w φ]))

/-- `subalgebraLift` is a factorisation of `ψ` through `φ`. -/
public theorem subalgebraLift_comp {F H G : X.QuasicoherentAlgebra} (ψ : F ⟶ G) (φ : H ⟶ G)
    (hφ : ∀ W : Opens X, Function.Injective (φ.right.hom.app (op W)))
    (hr : ∀ W : Opens X, Set.range (ψ.right.hom.app (op W)) ⊆
      Set.range (φ.right.hom.app (op W))) :
    subalgebraLift ψ φ hφ hr ≫ φ = ψ :=
  Under.UnderMorphism.ext (subalgebraLiftHom_comp ψ φ hφ hr)

/-- Two subsheaves of an algebra sheaf — morphisms with injective sections — with the same
sections over every open are isomorphic over it. -/
public def subalgebraIsoOfRangeEq {F H G : X.QuasicoherentAlgebra} (ψ : F ⟶ G) (φ : H ⟶ G)
    (hψ : ∀ W : Opens X, Function.Injective (ψ.right.hom.app (op W)))
    (hφ : ∀ W : Opens X, Function.Injective (φ.right.hom.app (op W)))
    (hr : ∀ W : Opens X, Set.range (ψ.right.hom.app (op W)) =
      Set.range (φ.right.hom.app (op W))) :
    F ≅ H where
  hom := subalgebraLift ψ φ hφ fun W => (hr W).le
  inv := subalgebraLift φ ψ hψ fun W => (hr W).ge
  hom_inv_id := by
    have := mono_of_injective_app ψ hψ
    refine (cancel_mono ψ).mp ?_
    rw [Category.assoc, subalgebraLift_comp, subalgebraLift_comp, Category.id_comp]
  inv_hom_id := by
    have := mono_of_injective_app φ hφ
    refine (cancel_mono φ).mp ?_
    rw [Category.assoc, subalgebraLift_comp, subalgebraLift_comp, Category.id_comp]

/-- The forward half of `subalgebraIsoOfRangeEq` is the factorisation of `ψ` through `φ`. -/
public theorem subalgebraIsoOfRangeEq_hom_comp {F H G : X.QuasicoherentAlgebra} (ψ : F ⟶ G)
    (φ : H ⟶ G) (hψ : ∀ W : Opens X, Function.Injective (ψ.right.hom.app (op W)))
    (hφ : ∀ W : Opens X, Function.Injective (φ.right.hom.app (op W)))
    (hr : ∀ W : Opens X, Set.range (ψ.right.hom.app (op W)) =
      Set.range (φ.right.hom.app (op W))) :
    (subalgebraIsoOfRangeEq ψ φ hψ hφ hr).hom ≫ φ = ψ :=
  subalgebraLift_comp ψ φ hφ fun W => (hr W).le

end Factor

/-! ### Invariance of the integral closure under an isomorphism -/

section Transport

/-- Integrality of an element over a ring is unchanged by an injective extension of the
ambient ring. -/
public theorem isIntegralElem_comp_iff {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    (α : R →+* S) (ε : S →+* T) (hε : Function.Injective ε) (y : S) :
    (ε.comp α).IsIntegralElem (ε y) ↔ α.IsIntegralElem y := by
  constructor
  · rintro ⟨p, hp, hpe⟩
    exact ⟨p, hp, hε (by rw [Polynomial.hom_eval₂, hpe, map_zero])⟩
  · rintro ⟨p, hp, hpe⟩
    exact ⟨p, hp, by rw [← Polynomial.hom_eval₂, hpe, map_zero]⟩

variable {X : Scheme.{u}}

/-- **The integral closure of the structure sheaf is invariant under an isomorphism of algebra
sheaves.** For an isomorphism `e : 𝒜 ≅ ℬ` of sheaves of `𝒪_X`-algebras, the sections of `𝒜` over
`W` that are integral over `𝒪_X` are carried by `e` exactly onto the sections of `ℬ` over `W`
that are integral over `𝒪_X`. -/
public theorem image_range_integralClosureAlgebraι_app {A B : X.QuasicoherentAlgebra} (e : A ≅ B)
    (W : Opens X) :
    e.hom.right.hom.app (op W) '' Set.range ((integralClosureAlgebraι A).right.hom.app (op W)) =
      Set.range ((integralClosureAlgebraι B).right.hom.app (op W)) := by
  have hstruct : A.hom.hom ≫ e.hom.right.hom = B.hom.hom :=
    congrArg (fun k : X.sheaf ⟶ B.right => k.hom) (Under.w e.hom)
  have key : ∀ s : A.right.presheaf.obj (op W),
      e.hom.right.hom.app (op W) s ∈
          Set.range ((integralClosureAlgebraι B).right.hom.app (op W)) ↔
        s ∈ Set.range ((integralClosureAlgebraι A).right.hom.app (op W)) := by
    intro s
    rw [mem_range_integralClosureAlgebraι_app_iff, mem_range_integralClosureAlgebraι_app_iff]
    refine forall_congr' fun x => forall_congr' fun hx => ?_
    rw [← TopCat.Presheaf.stalkFunctor_map_germ_apply W x hx e.hom.right.hom s]
    have hcomp : ((TopCat.Presheaf.stalkFunctor CommRingCat x).map B.hom.hom).hom =
        ((TopCat.Presheaf.stalkFunctor CommRingCat x).map e.hom.right.hom).hom.comp
          ((TopCat.Presheaf.stalkFunctor CommRingCat x).map A.hom.hom).hom := by
      rw [← hstruct, (TopCat.Presheaf.stalkFunctor CommRingCat x).map_comp,
        CommRingCat.hom_comp]
    rw [hcomp]
    exact isIntegralElem_comp_iff _ _ (bijective_stalkFunctor_map_of_iso e x).1 _
  refine Set.eq_of_subset_of_subset ?_ ?_
  · rintro _ ⟨s, hs, rfl⟩
    exact (key s).2 hs
  · intro y hy
    obtain ⟨s, rfl⟩ := (bijective_app_of_iso e W).2 y
    exact ⟨s, (key s).1 hy, rfl⟩

/-- The isomorphism of integral closures induced by an isomorphism of algebra sheaves. -/
public def integralClosureAlgebraIso {A B : X.QuasicoherentAlgebra} (e : A ≅ B) :
    integralClosureAlgebra A ≅ integralClosureAlgebra B :=
  subalgebraIsoOfRangeEq (integralClosureAlgebraι A ≫ e.hom) (integralClosureAlgebraι B)
    (fun W => (bijective_app_of_iso e W).1.comp (injective_integralClosureAlgebraι_app A W))
    (fun W => injective_integralClosureAlgebraι_app B W)
    (fun W => by
      rw [← image_range_integralClosureAlgebraι_app e W, ← Set.range_comp]
      rfl)

/-- `integralClosureAlgebraIso` is compatible with the two inclusions. -/
public theorem integralClosureAlgebraIso_hom_comp {A B : X.QuasicoherentAlgebra} (e : A ≅ B) :
    (integralClosureAlgebraIso e).hom ≫ integralClosureAlgebraι B =
      integralClosureAlgebraι A ≫ e.hom :=
  subalgebraIsoOfRangeEq_hom_comp _ _ _ _ _

/-- The integral closure of the structure sheaf is invariant under an invertible morphism of
algebra sheaves. -/
public theorem image_range_integralClosureAlgebraι_app_of_isIso
    {A B : X.QuasicoherentAlgebra} (h : A ⟶ B) [IsIso h] (W : Opens X) :
    h.right.hom.app (op W) '' Set.range ((integralClosureAlgebraι A).right.hom.app (op W)) =
      Set.range ((integralClosureAlgebraι B).right.hom.app (op W)) :=
  image_range_integralClosureAlgebraι_app (asIso h) W

end Transport

/-! ### The relative normalization as the integral-closure subalgebra -/

section Normalization

variable {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f] [IsAffineHom f]

/-- **Stacks Project, Tag 035F, for `f_* 𝒪_X`, as an isomorphism of algebra sheaves.** For `f`
affine the integral closure of `𝒪_S` in `f_* 𝒪_X` *is* the direct image of the structure sheaf
of the relative normalization of `f`, compatibly with the two inclusions into `f_* 𝒪_X`. This
upgrades the equality of ranges
`range_integralClosureAlgebraι_app_eq_range_normalizationAlgebraι_app` to an isomorphism. -/
public def normalizationAlgebraIso :
    pushforwardAlgebra f.fromNormalization ≅ integralClosureAlgebra (pushforwardAlgebra f) :=
  subalgebraIsoOfRangeEq (normalizationAlgebraι f)
    (integralClosureAlgebraι (pushforwardAlgebra f))
    (injective_normalizationAlgebraι_app f)
    (injective_integralClosureAlgebraι_app (pushforwardAlgebra f))
    fun W => (range_integralClosureAlgebraι_app_eq_range_normalizationAlgebraι_app f W).symm

/-- `normalizationAlgebraIso` is compatible with the two inclusions into `f_* 𝒪_X`. -/
public theorem normalizationAlgebraIso_hom_comp :
    (normalizationAlgebraIso f).hom ≫ integralClosureAlgebraι (pushforwardAlgebra f) =
      normalizationAlgebraι f :=
  subalgebraIsoOfRangeEq_hom_comp _ _ _ _ _

end Normalization

/-! ### Stacks 081K -/

section BaseChange

/-- Precomposition with a morphism surjective on sections over `W` does not change the range on
sections over `W`, written as an image. -/
public theorem range_comp_right_app_image {S : Scheme.{u}} {A B C : Under S.sheaf} (φ : A ⟶ B)
    (ψ : B ⟶ C) (W : S.Opens) :
    Set.range ((φ ≫ ψ).right.hom.app (op W)) =
      ψ.right.hom.app (op W) '' Set.range (φ.right.hom.app (op W)) := by
  rw [← Set.range_comp]
  rfl

variable {X S Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
  [QuasiCompact f] [QuasiSeparated f] [Smooth g]

/-- The base change along `g` of the factorisation `X ⟶ f.normalization` of `f` is the canonical
morphism `X ×_S Y ⟶ f.normalization ×_S Y` of `IntegralClosureSheaf.lean`. This is Mathlib's
`AlgebraicGeometry.Scheme.Hom.toNormalization_normalizationPullback_fst`. -/
public theorem pullback_map_normalizationOver :
    (Over.pullback g).map (normalizationOver f) = toBaseChangeNormalizationOver f g := by
  apply Over.OverMorphism.ext
  refine pullback.hom_ext ?_ ?_
  · simp only [Over.pullback_map_left, pullback.lift_fst, Over.homMk_left, Over.mk_hom,
      toBaseChangeNormalizationOver, normalizationOver, Category.assoc,
      Scheme.Hom.toNormalization_normalizationPullback_fst]
  · simp only [Over.pullback_map_left, pullback.lift_snd, Over.homMk_left, Over.mk_hom,
      toBaseChangeNormalizationOver, normalizationOver, Category.assoc,
      Scheme.Hom.normalizationPullback_snd, Scheme.Hom.toNormalization_fromNormalization]

/-- The pullback of the relative normalization of `f`, compared inside `(X ×_S Y)_* 𝒪` through
the base-change morphism, is the base-changed normalization of `IntegralClosureSheaf.lean`. -/
public theorem range_algebraPullback_normalizationAlgebraι_comp_app (W : Y.Opens) :
    Set.range (((algebraPullback g).map (normalizationAlgebraι f) ≫
        baseChangeAlgebraHom g (Over.mk f)).right.hom.app (op W)) =
      Set.range ((baseChangeNormalizationAlgebraι f g).right.hom.app (op W)) := by
  have := isIso_baseChangeAlgebraHom_fromNormalization f g
  have hnat : (algebraPullback g).map (normalizationAlgebraι f) ≫
      baseChangeAlgebraHom g (Over.mk f) =
        baseChangeAlgebraHom g (Over.mk f.fromNormalization) ≫
          baseChangeNormalizationAlgebraι f g :=
    (Stacks.AlgebraPullbackQcoh.baseChangeAlgebraHom_naturality g (normalizationOver f)).trans
      (congrArg (fun k => baseChangeAlgebraHom g (Over.mk f.fromNormalization) ≫
        pushforwardAlgebraMap k) (pullback_map_normalizationOver f g))
  rw [hnat]
  exact range_comp_right_app _ _ W (surjective_right_app_of_isIso _ W)

/-- **Stacks Project, Tag 081K, for `𝒜 = f_* 𝒪_X` with `f` affine.** Inside the pullback
`g^*(f_* 𝒪_X)`, the integral closure of `𝒪_Y` and the pullback of the integral closure of `𝒪_S`
in `f_* 𝒪_X` have the same sections over every open `W` of `Y`. -/
public theorem range_integralClosureAlgebraι_app_algebraPullback_pushforward_eq [IsAffineHom f]
    (W : Y.Opens) :
    Set.range ((integralClosureAlgebraι
        ((algebraPullback g).obj (pushforwardAlgebra f))).right.hom.app (op W)) =
      Set.range (((algebraPullback g).map
        (integralClosureAlgebraι (pushforwardAlgebra f))).right.hom.app (op W)) := by
  have := isIso_baseChangeAlgebraHom_self f g
  have hL : (baseChangeAlgebraHom g (Over.mk f)).right.hom.app (op W) ''
      Set.range ((integralClosureAlgebraι
        ((algebraPullback g).obj (pushforwardAlgebra f))).right.hom.app (op W)) =
      Set.range ((integralClosureAlgebraι
        (pushforwardAlgebra (pullback.snd f g))).right.hom.app (op W)) :=
    image_range_integralClosureAlgebraι_app_of_isIso (baseChangeAlgebraHom g (Over.mk f)) W
  have hR : (baseChangeAlgebraHom g (Over.mk f)).right.hom.app (op W) ''
      Set.range (((algebraPullback g).map
        (integralClosureAlgebraι (pushforwardAlgebra f))).right.hom.app (op W)) =
      Set.range ((baseChangeNormalizationAlgebraι f g).right.hom.app (op W)) := by
    rw [← range_comp_right_app_image _ (baseChangeAlgebraHom g (Over.mk f)) W,
      ← range_comp_right_app ((algebraPullback g).map (normalizationAlgebraIso f).hom) _ W
        (surjective_right_app_of_isIso _ W),
      ← Category.assoc, ← Functor.map_comp, normalizationAlgebraIso_hom_comp]
    exact range_algebraPullback_normalizationAlgebraι_comp_app f g W
  refine (Set.image_eq_image
    (injective_right_app_of_isIso (baseChangeAlgebraHom g (Over.mk f)) W)).mp ?_
  rw [hL, hR]
  exact range_integralClosureAlgebraι_app_pullback_eq f g W

end BaseChange

section Main

variable {S Y : Scheme.{u}} (A : Stacks.RelativeSpec.AlgebraSheaf S)
  [Stacks.RelativeSpec.AlgebraSheaf.IsQuasicoherent A] (g : Y ⟶ S) [Smooth g]

/-- **Stacks Project, Tag 081K.** Let `g : Y ⟶ S` be a smooth morphism of schemes, let `𝒜` be a
quasi-coherent sheaf of commutative `𝒪_S`-algebras and let `𝒜' = integralClosureAlgebra 𝒜` be
the integral closure of `𝒪_S` in `𝒜`. Then the integral closure of `𝒪_Y` in `g^*𝒜` is `g^*𝒜'`:
the two subsheaves `integralClosureAlgebra (g^*𝒜)` and `g^*𝒜'` of `g^*𝒜` have the same sections
over every open `W` of `Y`. No hypothesis is placed on `𝒜` beyond quasi-coherence, and none on
`g` beyond smoothness. -/
@[stacks 081K "the whole statement, in the development's own terms: the integral closure
`integralClosureAlgebra` of the structure sheaf, the pullback `algebraPullback` of algebra
sheaves, an arbitrary quasi-coherent `𝒜`, an arbitrary open of `Y`, and no hypothesis beyond
`g` smooth. The two subsheaves of `g^*𝒜` are compared by the ranges of their sections, which is
how the development writes an inclusion of algebra sheaves. The mathematics is
`range_integralClosureAlgebraι_app_pullback_eq`, where Stacks 03GG and 03GV are consumed; what
is added here is the transport `image_range_integralClosureAlgebraι_app` of the integral closure
along an isomorphism of algebra sheaves, together with `normalizationAlgebraIso` and
`Stacks.AlgebraPullbackQcoh.baseChangeAlgebraHom_naturality`.", ega "IV 18.12.15"]
public theorem range_integralClosureAlgebraι_app_algebraPullback_eq (W : Y.Opens) :
    Set.range ((integralClosureAlgebraι ((algebraPullback g).obj A)).right.hom.app (op W)) =
      Set.range (((algebraPullback g).map (integralClosureAlgebraι A)).right.hom.app (op W)) := by
  have : IsSeparated (relativeSpecToBase A) := IsSeparated.of_isAffineHom _
  have hL : ((algebraPullback g).map (pushforwardAlgebraIso A).hom).right.hom.app (op W) ''
      Set.range ((integralClosureAlgebraι ((algebraPullback g).obj
        (pushforwardAlgebra (relativeSpecToBase A)))).right.hom.app (op W)) =
      Set.range ((integralClosureAlgebraι ((algebraPullback g).obj A)).right.hom.app (op W)) :=
    image_range_integralClosureAlgebraι_app_of_isIso _ W
  have hR : ((algebraPullback g).map (pushforwardAlgebraIso A).hom).right.hom.app (op W) ''
      Set.range (((algebraPullback g).map (integralClosureAlgebraι
        (pushforwardAlgebra (relativeSpecToBase A)))).right.hom.app (op W)) =
      Set.range (((algebraPullback g).map
        (integralClosureAlgebraι A)).right.hom.app (op W)) := by
    rw [← range_comp_right_app_image _ _ W, ← Functor.map_comp,
      ← integralClosureAlgebraIso_hom_comp (pushforwardAlgebraIso A), Functor.map_comp]
    exact range_comp_right_app _ _ W (surjective_right_app_of_isIso _ W)
  rw [← hL, ← hR]
  exact congrArg
    (fun s => ((algebraPullback g).map (pushforwardAlgebraIso A).hom).right.hom.app (op W) '' s)
    (range_integralClosureAlgebraι_app_algebraPullback_pushforward_eq (relativeSpecToBase A) g W)

end Main

end Stacks.IntegralClosure.SheafLevel

end
