module

public import StacksFrontier.AlgebraicGeometry.Artin.ContractionClosedImmersionGlue
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionAffineMcQuillan
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionSubspaceAffineChart
public import StacksFrontier.AlgebraicGeometry.FormalSpace.InfinitesimalNeighbourhood.ReductionIdeal

/-!
# Morphisms out of the completion of an affine scheme along an ideal

Let `X = Spec A` be an affine object of the big fppf site over `S`, with `A` Noetherian, let
`I ⊆ A` be an ideal and let `W` be an fppf sheaf. A compatible family of sections
`x_n ∈ W(Spec(A/I^(n+1)))` defines a morphism `x̂ : X_{/V(I)} ⟶ W` out of the completion of `X`
along `V(I)`: a section of the completion over an affine object `U` is a morphism `U ⟶ Spec A`
all of whose points lie in `V(I)`, hence it kills a power `I^(n+1)` and factors through
`Spec(A/I^(n+1))`, and `x̂` sends it to the restriction of `x_n`. The construction is the one of
the proof of Stacks 0GI8, which assembles `x̂ = (ξ'_n)` from the morphisms
`ξ'_n : Spec(R/I^n) ⟶ W`.

## Main definitions

* `AlgebraicGeometry.FormalSpace.zeroLocusCompletionLift`: the morphism `x̂`.

## Main results

* `AlgebraicGeometry.FormalSpace.zeroLocusCompletionLift_apply`: its value on a section of the
  completion factoring through `Spec(A/I^(n+1))`.

## References

* [Stacks Project, Tag 0GI8](https://stacks.math.columbia.edu/tag/0GI8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.FormalSpace

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {A : Type u} [CommRing A] [IsNoetherianRing A] {hA : B.Contains (Spec (.of A))}
  {f : Spec (.of A) ⟶ S} (I : Ideal A)

/-- The `n`-th infinitesimal neighbourhood `Spec(A/I^(n+1))` of `V(I)` in `Spec A`, as an
object of the site. -/
abbrev idealNeighbourhood (n : ℕ) : BigFppfOver B S hS :=
  (BigAffineFppf.inclusion B S hS).obj (quotientOver B S hS f hA (I ^ (n + 1)))

/-- The closed immersion `Spec(A/I^(n+1)) ⟶ Spec A`. -/
abbrev idealNeighbourhoodι (n : ℕ) :
    idealNeighbourhood (hS := hS) (hA := hA) (f := f) I n ⟶ affineOver B S hS hA f :=
  Space.quotientToAffineOver B S hS f hA (I ^ (n + 1))

/-- The closed immersion `Spec(A/I^(n+1)) ⟶ Spec(A/I^(m+1))` for `n ≤ m`. -/
abbrev idealNeighbourhoodTransition {n m : ℕ} (h : n ≤ m) :
    idealNeighbourhood (hS := hS) (hA := hA) (f := f) I n ⟶
      idealNeighbourhood (hS := hS) (hA := hA) (f := f) I m :=
  (BigAffineFppf.inclusion B S hS).map (quotientOverTransition B S hS f hA
    (Ideal.pow_le_pow_right (Nat.succ_le_succ h)))

omit [IsNoetherianRing A] in
/-- The transition `Spec(A/I^(n+1)) ⟶ Spec(A/I^(m+1))` followed by the closed immersion into
`Spec A` is the closed immersion `Spec(A/I^(n+1)) ⟶ Spec A`. -/
theorem idealNeighbourhoodTransition_comp_ι {n m : ℕ} (h : n ≤ m) :
    idealNeighbourhoodTransition (hS := hS) (hA := hA) (f := f) I h ≫
        idealNeighbourhoodι I m = idealNeighbourhoodι I n :=
  Space.quotientOverTransition_comp_quotientToAffineOver B S hS f hA _

/-- The infinitesimal neighbourhood `Spec(A/I^(n+1))` is an affine scheme. -/
instance isAffine_toScheme_idealNeighbourhood (n : ℕ) :
    IsAffine ((BigFppfOver.toScheme B S hS).obj
      (idealNeighbourhood (hS := hS) (hA := hA) (f := f) I n)) :=
  (quotientOver B S hS f hA (I ^ (n + 1))).2

variable {I} {W : FppfSheaf B S hS}
  (x : ∀ n, W.obj.obj (op (idealNeighbourhood (hS := hS) (hA := hA) (f := f) I n)))
  (hx : ∀ ⦃n m : ℕ⦄ (h : n ≤ m),
    W.obj.map (idealNeighbourhoodTransition I h).op (x m) = x n)

omit [IsNoetherianRing A] in
include hx in
/-- Two factorizations of a morphism through infinitesimal neighbourhoods give the same
restriction of the compatible family. -/
theorem map_eq_map_of_comp_ι_eq {U : BigFppfOver B S hS} {n₁ n₂ : ℕ}
    (l₁ : U ⟶ idealNeighbourhood I n₁) (l₂ : U ⟶ idealNeighbourhood I n₂)
    (h : l₁ ≫ idealNeighbourhoodι I n₁ = l₂ ≫ idealNeighbourhoodι I n₂) :
    W.obj.map l₁.op (x n₁) = W.obj.map l₂.op (x n₂) := by
  have := Space.mono_quotientToAffineOver B S hS f hA (I ^ (max n₁ n₂ + 1))
  have h₁ := le_max_left n₁ n₂
  have h₂ := le_max_right n₁ n₂
  have e : l₁ ≫ idealNeighbourhoodTransition I h₁ = l₂ ≫ idealNeighbourhoodTransition I h₂ := by
    apply (cancel_mono (idealNeighbourhoodι I (max n₁ n₂))).1
    rw [Category.assoc, Category.assoc, idealNeighbourhoodTransition_comp_ι,
      idealNeighbourhoodTransition_comp_ι, h]
  rw [← hx h₁, ← hx h₂, ← Functor.map_comp_apply, ← Functor.map_comp_apply,
    ← op_comp, ← op_comp, e]

omit [IsNoetherianRing A] in
/-- A morphism `U ⟶ Spec A` killing `I^(n+1)` factors through `Spec(A/I^(n+1))`. -/
theorem exists_factor_idealNeighbourhoodι {U : BigFppfOver B S hS}
    (φ : U ⟶ affineOver B S hS hA f) {n : ℕ} (hn : I ^ (n + 1) ≤ RingHom.ker (chartRing φ)) :
    ∃ l : U ⟶ idealNeighbourhood I n, l ≫ idealNeighbourhoodι I n = φ := by
  set ι := (BigFppfOver.toScheme B S hS).map
    (idealNeighbourhoodι (hS := hS) (hA := hA) (f := f) I n)
  have : _root_.AlgebraicGeometry.IsClosedImmersion ι :=
    _root_.AlgebraicGeometry.IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  obtain ⟨l, hl⟩ := (Scheme.exists_factor_iff_ker_appTop_le ι
    ((BigFppfOver.toScheme B S hS).map φ)).2 (by
    rw [Space.ker_appTop_quotientToAffineOver]
    intro ξ hξ
    have h0 : chartRing φ ((Scheme.ΓSpecIso (.of A)).hom ξ) = 0 := hn hξ
    change ((BigFppfOver.toScheme B S hS).map φ).appTop
      ((Scheme.ΓSpecIso (.of A)).inv ((Scheme.ΓSpecIso (.of A)).hom ξ)) = 0 at h0
    rwa [(Scheme.ΓSpecIso (.of A)).hom_inv_id_apply ξ] at h0)
  exact exists_siteHom_of_toScheme_comp_eq _ φ l hl

/-- A section of the completion over an affine object factors through an infinitesimal
neighbourhood. -/
theorem exists_factor_idealNeighbourhood {U : BigFppfOver B S hS}
    [IsAffine ((BigFppfOver.toScheme B S hS).obj U)] (φ : U ⟶ affineOver B S hS hA f)
    (hφ : Space.HasImageIn B S hS (yoneda.obj (affineOver B S hS hA f))
      (zeroLocusPoints B S hS hA f I) U φ) :
    ∃ (n : ℕ) (l : U ⟶ idealNeighbourhood I n), l ≫ idealNeighbourhoodι I n = φ := by
  obtain ⟨n, hn⟩ := Artin.ContractionSituation.exists_pow_le_ker_of_mem_zeroLocus I φ
    ((hasImageIn_zeroLocusPoints_iff B S hS hA f I U φ).1 hφ)
  exact ⟨n, exists_factor_idealNeighbourhoodι φ hn⟩

/-- The value of `x̂` on a section of the completion over an affine object: the restriction of
`x_n` along a factorization through `Spec(A/I^(n+1))`. -/
def completionValue {U : BigFppfOver B S hS} (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U))
    (φ : U ⟶ affineOver B S hS hA f)
    (hφ : Space.HasImageIn B S hS (yoneda.obj (affineOver B S hS hA f))
      (zeroLocusPoints B S hS hA f I) U φ) : W.obj.obj (op U) :=
  haveI := hU
  W.obj.map (exists_factor_idealNeighbourhood φ hφ).choose_spec.choose.op
    (x (exists_factor_idealNeighbourhood φ hφ).choose)

include hx in
/-- `completionValue x hU φ hφ` is the restriction of `x_n` along any factorization
`U ⟶ Spec(A/I^(n+1))` of `φ`. -/
theorem completionValue_eq {U : BigFppfOver B S hS}
    (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U)) (φ : U ⟶ affineOver B S hS hA f)
    (hφ : Space.HasImageIn B S hS (yoneda.obj (affineOver B S hS hA f))
      (zeroLocusPoints B S hS hA f I) U φ) {n : ℕ} (l : U ⟶ idealNeighbourhood I n)
    (hl : l ≫ idealNeighbourhoodι I n = φ) :
    completionValue x hU φ hφ = W.obj.map l.op (x n) :=
  have := hU
  map_eq_map_of_comp_ι_eq x hx _ _
    ((exists_factor_idealNeighbourhood φ hφ).choose_spec.choose_spec.trans hl.symm)

include hx in
/-- The value of `x̂` on `g ≫ φ` is the restriction along `g` of its value on `φ`. -/
theorem completionValue_comp {U V : BigFppfOver B S hS}
    (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U))
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V)) (g : U ⟶ V)
    (φ : V ⟶ affineOver B S hS hA f)
    (hφ : Space.HasImageIn B S hS (yoneda.obj (affineOver B S hS hA f))
      (zeroLocusPoints B S hS hA f I) V φ)
    (hgφ : Space.HasImageIn B S hS (yoneda.obj (affineOver B S hS hA f))
      (zeroLocusPoints B S hS hA f I) U (g ≫ φ)) :
    completionValue x hU (g ≫ φ) hgφ = W.obj.map g.op (completionValue x hV φ hφ) := by
  have := hV
  obtain ⟨n, l, hl⟩ := exists_factor_idealNeighbourhood φ hφ
  rw [completionValue_eq x hx hV φ hφ l hl,
    completionValue_eq x hx hU _ _ (g ≫ l) (by rw [Category.assoc, hl]),
    op_comp, Functor.map_comp_apply]

include x hx in
/-- The morphism `x̂` on the completion subfunctor, restricted to affine objects. -/
def completionValueTrans :
    (BigAffineFppf.inclusion B S hS).op ⋙ (Space.completionSubfunctor B S hS
      (yoneda.obj (affineOver B S hS hA f)) (zeroLocusPoints B S hS hA f I)).toFunctor ⟶
      (BigAffineFppf.inclusion B S hS).op ⋙ W.obj where
  app U := TypeCat.ofHom fun φ => completionValue x U.unop.2 φ.1.down φ.2
  naturality U V g := by
    ext φ
    exact completionValue_comp x hx V.unop.2 U.unop.2 g.unop.hom φ.1.down φ.2
      ((Space.completionSubfunctor B S hS (yoneda.obj (affineOver B S hS hA f))
        (zeroLocusPoints B S hS hA f I)).map ((BigAffineFppf.inclusion B S hS).op.map g) φ.2)

/-- **The morphism `x̂ : (Spec A)_{/V(I)} ⟶ W` attached to a compatible family
`x_n ∈ W(Spec(A/I^(n+1)))`.** -/
def zeroLocusCompletionLift :
    Space.completionSheaf B S hS (yoneda.obj (affineOver B S hS hA f))
      (zeroLocusPoints B S hS hA f I) ⟶ W :=
  haveI : (BigAffineFppf.inclusion B S hS).IsCoverDense (BigFppfOver.topology B S hS) :=
    Functor.IsDenseSubsite.isCoverDense (BigAffineFppf.topology B S hS)
      (BigFppfOver.topology B S hS) (BigAffineFppf.inclusion B S hS)
  haveI : (BigAffineFppf.inclusion B S hS).IsLocallyFull (BigFppfOver.topology B S hS) :=
    Functor.IsDenseSubsite.isLocallyFull (BigAffineFppf.topology B S hS)
      (BigFppfOver.topology B S hS) (BigAffineFppf.inclusion B S hS)
  ⟨(BigFppfOver.topology B S hS).sheafifyLift
    (Functor.IsCoverDense.sheafHom (ℱ' := W) (completionValueTrans x hx)) W.property⟩

/-- **The value of `x̂`** on the section of the completion given by a morphism `φ : U ⟶ Spec A`
from an affine object factoring as `U ⟶ Spec(A/I^(n+1)) ⟶ Spec A` is the restriction of `x_n`. -/
theorem zeroLocusCompletionLift_apply {U : BigFppfOver B S hS}
    [hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U)] (φ : U ⟶ affineOver B S hS hA f)
    (hφ : Space.HasImageIn B S hS (yoneda.obj (affineOver B S hS hA f))
      (zeroLocusPoints B S hS hA f I) U φ) {n : ℕ} (l : U ⟶ idealNeighbourhood I n)
    (hl : l ≫ idealNeighbourhoodι I n = φ) :
    (zeroLocusCompletionLift x hx).hom.app (op U)
      (((BigFppfOver.topology B S hS).toSheafify (Space.completionSubfunctor B S hS
        (yoneda.obj (affineOver B S hS hA f)) (zeroLocusPoints B S hS hA f I)).toFunctor).app
          (op U) ⟨ULift.up φ, hφ⟩) = W.obj.map l.op (x n) := by
  have := Functor.IsDenseSubsite.isCoverDense (BigAffineFppf.topology B S hS)
    (BigFppfOver.topology B S hS) (BigAffineFppf.inclusion B S hS)
  have := Functor.IsDenseSubsite.isLocallyFull (BigAffineFppf.topology B S hS)
    (BigFppfOver.topology B S hS) (BigAffineFppf.inclusion B S hS)
  let U' : BigAffineFppf B S hS := ⟨U, hU⟩
  have h1 := congrArg (fun η => η.app (op U) ⟨ULift.up φ, hφ⟩)
    (GrothendieckTopology.toSheafify_sheafifyLift (BigFppfOver.topology B S hS)
      (Functor.IsCoverDense.sheafHom (ℱ' := W) (completionValueTrans x hx)) W.property)
  refine h1.trans ?_
  have h2 := congrArg (fun η => η.app (op U') ⟨ULift.up φ, hφ⟩)
    (Functor.IsCoverDense.sheafHom_restrict_eq (ℱ' := W) (completionValueTrans x hx))
  refine h2.trans ?_
  exact completionValue_eq x hx hU φ hφ l hl

end AlgebraicGeometry.FormalSpace

end
