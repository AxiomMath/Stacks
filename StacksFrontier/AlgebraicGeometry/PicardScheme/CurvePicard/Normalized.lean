module

public import StacksFrontier.AlgebraicGeometry.PicardScheme.CurvePicard.DegreeComponents

/-!
# The normalized subfunctor of the Picard functor of a curve, and its translates

Let `X` be a proper scheme of dimension at most one over a field `k` with a rational point, for
which the hypothesis of [Stacks, Tag 0B9N] holds. The points `ξ` of the Picard functor
`Pic_{X/k}(T)` whose fibres satisfy `H¹(X_t, L_t) = 0` and `dim H⁰(X_t, L_t) = 1` form a
subfunctor `F`, and the pullback of `ξ` along `h : T' ⟶ T` lies in `F` exactly when `h` lands in
an open subscheme of `T` determined by `ξ`. This is the fibrewise form of [Stacks, Tag 0B9V]
(the subfunctor of that tag is defined through `Rf_{T,*}L ≅ 𝒩[0]`).

Translating `F` by a rational point `g` of the Picard functor gives the subfunctors
`F_g = {ξ | g + ξ ∈ F}` of the proof of [Stacks, Tag 0B9Q], with the same open-locus property.

## Main definitions

* `Stacks.PicardFunctor.normalizedSubfunctor`: the subfunctor `F`.
* `Stacks.PicardFunctor.translateSubfunctor`: its translate by a section of the Picard functor
  over the base.
* `Stacks.PicardFunctor.normalizedLocus`: the open of `T` cut out by a point of `Pic_{X/k}(T)`.

## Main results

* `Stacks.PicardFunctor.map_mem_normalizedSubfunctor_iff`: the open-locus property of `F`.
* `Stacks.PicardFunctor.map_mem_translateSubfunctor_iff`: the same for the translates.

## References

* [Stacks Project, Tag 0B9V](https://stacks.math.columbia.edu/tag/0B9V)
* [Stacks Project, Tag 0B9Q](https://stacks.math.columbia.edu/tag/0B9Q)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

universe u

namespace Stacks.PicardFunctor

open Stacks.PicardCurve

variable (B : BigFppfSite.{u}) {X S : Scheme.{u}} (hX : B.Contains X) (hS : B.Contains S)
  (f : B.obj hX ⟶ B.obj hS)

/-! ### The group structure of the Picard functor is natural -/

/-- The restriction maps of the Picard functor are additive. -/
theorem picardFunctor_map_add {T T' : BigFppfOver B S hS} (g : T' ⟶ T)
    (ξ η : (picardFunctor B hX hS f).obj (op T)) :
    (picardFunctor B hX hS f).map g.op (ξ + η) =
      (picardFunctor B hX hS f).map g.op ξ + (picardFunctor B hX hS f).map g.op η := by
  apply (picardFunctorAddEquiv B hX hS f T').injective
  have hnat (ζ : (picardFunctor B hX hS f).obj (op T)) :
      picardFunctorAddEquiv B hX hS f T' ((picardFunctor B hX hS f).map g.op ζ) =
        (picardAddFunctor B hX hS f).map g.op (picardFunctorAddEquiv B hX hS f T ζ) :=
    ConcreteCategory.congr_hom
      ((picardFunctorIsoPicardAddFunctor B hX hS f).hom.naturality g.op) ζ
  rw [AddEquiv.map_add (picardFunctorAddEquiv B hX hS f T'), hnat, hnat, hnat,
    AddEquiv.map_add (picardFunctorAddEquiv B hX hS f T)]
  exact map_add ((picardAddFunctor B hX hS f).map g.op).hom _ _

/-- The base object of the site over `S`. -/
abbrev baseObj : BigFppfOver B S hS := Over.mk (𝟙 (B.obj hS))

/-- The structure morphism of a test scheme, as a morphism to the base object. -/
abbrev toBaseObj (T : BigFppfOver B S hS) : T ⟶ baseObj B hS := Over.homMk T.hom

/-- The restriction of a section over the base to a test scheme. -/
abbrev restrictBase (g : (picardFunctor B hX hS f).obj (op (baseObj B hS)))
    (T : BigFppfOver B S hS) : (picardFunctor B hX hS f).obj (op T) :=
  (picardFunctor B hX hS f).map (toBaseObj B hS T).op g

/-- Pulling back the restriction of a section over the base to `T` along `φ : T' ⟶ T` gives its
restriction to `T'`. -/
theorem map_restrictBase (g : (picardFunctor B hX hS f).obj (op (baseObj B hS)))
    {T T' : BigFppfOver B S hS} (φ : T' ⟶ T) :
    (picardFunctor B hX hS f).map φ.op (restrictBase B hX hS f g T) =
      restrictBase B hX hS f g T' := by
  rw [restrictBase, ← Functor.map_comp_apply]
  have h : φ ≫ toBaseObj B hS T = toBaseObj B hS T' := Over.OverMorphism.ext (Over.w φ)
  rw [← op_comp, h]

/-- Translation by a section over the base, at one test scheme. -/
def translateApp (g : (picardFunctor B hX hS f).obj (op (baseObj B hS)))
    (T : BigFppfOver B S hS) :
    (picardFunctor B hX hS f).obj (op T) ≅ (picardFunctor B hX hS f).obj (op T) where
  hom := TypeCat.ofHom fun ξ => restrictBase B hX hS f g T + ξ
  inv := TypeCat.ofHom fun ξ => -restrictBase B hX hS f g T + ξ
  hom_inv_id := by ext ξ; exact neg_add_cancel_left _ _
  inv_hom_id := by ext ξ; exact add_neg_cancel_left _ _

/-- **Translation by a section over the base** is a natural automorphism of the Picard
functor. -/
def translate (g : (picardFunctor B hX hS f).obj (op (baseObj B hS))) :
    picardFunctor B hX hS f ≅ picardFunctor B hX hS f :=
  NatIso.ofComponents (fun T => translateApp B hX hS f g T.unop)
    (fun {T T'} φ => by
      ext ξ
      change restrictBase B hX hS f g T'.unop + (picardFunctor B hX hS f).map φ.unop.op ξ =
        (picardFunctor B hX hS f).map φ.unop.op (restrictBase B hX hS f g T.unop + ξ)
      rw [picardFunctor_map_add B hX hS f φ.unop, map_restrictBase])

/-- At a test scheme `T`, translation by `g` sends `ξ` to the sum of the restriction of `g` to
`T` and `ξ`. -/
theorem translate_hom_app (g : (picardFunctor B hX hS f).obj (op (baseObj B hS)))
    (T : BigFppfOver B S hS) (ξ : (picardFunctor B hX hS f).obj (op T)) :
    (translate B hX hS f g).hom.app (op T) ξ = restrictBase B hX hS f g T + ξ :=
  rfl

variable (σ : S ⟶ X) (hσ : σ ≫ B.inclusion.map f = 𝟙 S)
  (hOiso : ∀ U : BigFppfOver B S hS, IsIso (baseChangeProj B hX hS f U).toLRSHom.toHom.c)

/-! ### The normalized subfunctor -/

/-- **The normalized subfunctor `F` of the Picard functor**: the points `ξ` with
`H¹(X_t, L_t) = 0` and `dim H⁰(X_t, L_t) = 1` on every fibre, for `L` representing `ξ`. -/
def normalizedSubfunctor [IsProper (B.inclusion.map f)] : Subfunctor (picardFunctor B hX hS f) where
  obj T := {ξ | ∀ t, fibreRank B hX hS f σ hσ hOiso T.unop ξ t 1 = 0 ∧
    fibreRank B hX hS f σ hσ hOiso T.unop ξ t 0 = 1}
  map {T T'} g ξ hξ t := by
    change fibreRank B hX hS f σ hσ hOiso T'.unop
        ((picardFunctor B hX hS f).map g.unop.op ξ) t 1 = 0 ∧
      fibreRank B hX hS f σ hσ hOiso T'.unop ((picardFunctor B hX hS f).map g.unop.op ξ) t 0 = 1
    rw [fibreRank_map, fibreRank_map]
    exact hξ _

section Curve

variable {k : Type u} [Field k] (B : BigFppfSite.{u}) {X : Scheme.{u}} (hX : B.Contains X)
  (hk : B.Contains (Spec (.of k))) (f : B.obj hX ⟶ B.obj hk)
  (σ : Spec (.of k) ⟶ X) (hσ : σ ≫ B.inclusion.map f = 𝟙 (Spec (.of k)))
  (hOiso : ∀ U : BigFppfOver B (Spec (.of k)) hk,
    IsIso (baseChangeProj B hX hk f U).toLRSHom.toHom.c)
  [IsProper (B.inclusion.map f)] [X.IsSeparated] [IsNoetherian X]
  (hdim : topologicalKrullDim X ≤ 1)

include hdim in
/-- The locus of a test scheme over which a point of the Picard functor is normalized is
open. -/
theorem isOpen_normalizedLocus (T : BigFppfOver B (Spec (.of k)) hk)
    (ξ : (picardFunctor B hX hk f).obj (op T)) :
    IsOpen {t | fibreRank B hX hk f σ hσ hOiso T ξ t 1 = 0 ∧
      fibreRank B hX hk f σ hσ hOiso T ξ t 0 = 1} := by
  obtain ⟨U, hU, hUaff⟩ := Stacks.TwoAffineCech.exists_cover_isAffineOpen X hdim
  obtain ⟨x, rfl⟩ := surjective_toPicardFunctorHom B hX hk f σ hσ hOiso T ξ
  have h := Stacks.TwoAffineCech.isOpen_setOf_fibreCohomology_of_isPullback
    (B.inclusion.map f) U hU hUaff (B.inclusion.map T.hom) _ _
    (IsPullback.of_hasPullback (B.inclusion.map f) (B.inclusion.map T.hom)) (rep x) 1
  simp only [fibreRank_toPicardFunctorHom]
  exact h

/-- **The open of `T` over which a point of the Picard functor is normalized.** -/
def normalizedLocus (T : BigFppfOver B (Spec (.of k)) hk)
    (ξ : (picardFunctor B hX hk f).obj (op T)) :
    ((BigFppfOver.toScheme B (Spec (.of k)) hk).obj T).Opens :=
  ⟨_, isOpen_normalizedLocus B hX hk f σ hσ hOiso hdim T ξ⟩

/-- **The fibrewise form of Tag 0B9V**: the pullback of a point `ξ` of the Picard functor along
`h : T' ⟶ T` is normalized exactly when `h` lands in the normalized locus of `ξ`. -/
theorem map_mem_normalizedSubfunctor_iff {T T' : BigFppfOver B (Spec (.of k)) hk} (h : T' ⟶ T)
    (ξ : (picardFunctor B hX hk f).obj (op T)) :
    (picardFunctor B hX hk f).map h.op ξ ∈
        (normalizedSubfunctor B hX hk f σ hσ hOiso).obj (op T') ↔
      ∀ t, B.inclusion.map h.left t ∈ normalizedLocus B hX hk f σ hσ hOiso hdim T ξ := by
  change (∀ t, _ ∧ _) ↔ _
  simp only [fibreRank_map]
  rfl

/-- **The translate `F_g = {ξ | g + ξ ∈ F}` of the normalized subfunctor** by a section `g` of
the Picard functor over the base. -/
abbrev translateSubfunctor (g : (picardFunctor B hX hk f).obj (op (baseObj B hk))) :
    Subfunctor (picardFunctor B hX hk f) :=
  (normalizedSubfunctor B hX hk f σ hσ hOiso).preimage (translate B hX hk f g).hom

/-- The open-locus property of the translates of the normalized subfunctor. -/
theorem map_mem_translateSubfunctor_iff (g : (picardFunctor B hX hk f).obj (op (baseObj B hk)))
    {T T' : BigFppfOver B (Spec (.of k)) hk} (h : T' ⟶ T)
    (ξ : (picardFunctor B hX hk f).obj (op T)) :
    (picardFunctor B hX hk f).map h.op ξ ∈
        (translateSubfunctor B hX hk f σ hσ hOiso g).obj (op T') ↔
      ∀ t, B.inclusion.map h.left t ∈ normalizedLocus B hX hk f σ hσ hOiso hdim T
        ((translate B hX hk f g).hom.app (op T) ξ) := by
  rw [← map_mem_normalizedSubfunctor_iff B hX hk f σ hσ hOiso hdim h]
  change (translate B hX hk f g).hom.app (op T') ((picardFunctor B hX hk f).map h.op ξ) ∈
    (normalizedSubfunctor B hX hk f σ hσ hOiso).obj (op T') ↔ _
  rw [translate_hom_app, translate_hom_app, picardFunctor_map_add, map_restrictBase]

end Curve

end Stacks.PicardFunctor
