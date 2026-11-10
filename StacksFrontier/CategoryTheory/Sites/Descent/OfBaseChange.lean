module
public import StacksFrontier.CategoryTheory.Sites.Descent.PullbackDescentData

public import Mathlib.CategoryTheory.Adjunction.Basic
public import StacksFrontier.CategoryTheory.Sites.Descent.PrestackOfCover
public import StacksFrontier.CategoryTheory.Sites.Descent.OfRefinement
public import StacksFrontier.CategoryTheory.Sites.Descent.SingletonCoalgebraObj

/-!
# Effective descent along a family from effective descent after a base change

Let `F` be a pseudofunctor from `LocallyDiscrete Cᵒᵖ` to `Cat`, where `C` has pullbacks, let
`f i : X i ⟶ Y` be a family of morphisms with fixed target and let `g j : Z j ⟶ Y` be a family
along which descent for `F` is effective, and along each of whose base changes descent of
morphisms holds. This file proves that descent along `f` is effective as soon as it is effective
along each base change `{X i ×_Y Z j ⟶ Z j}` of `f`, descent of morphisms holds along each base
change `{X i ×_Y (Z j ×_Y Z k) ⟶ Z j ×_Y Z k}`, and a faithfulness condition holds over the
triple products `Z j ×_Y Z k ×_Y Z l`. For a one-member family `g` this is the categorical
content of Stacks 0GF1; for a covering family it is the locality of effective descent on the
base.

## Main results

* `CategoryTheory.Pseudofunctor.isEquivalence_toDescentData_of_baseChange_unconditional`: the
  transitivity statement.
* `CategoryTheory.Adjunction.map_homEquiv_eq_of_map_eq`: the faithfulness condition over the
  triple product follows from faithfulness over `Z` whenever the relevant base-change morphism
  for a right adjoint is a monomorphism. This is how the condition is discharged for small étale
  sheaves, by the base change theorems for integral and for proper morphisms.

## Implementation notes

Full faithfulness of `F.toDescentData f` is the locality of being a prestack,
`CategoryTheory.Pseudofunctor.isPrestackFor_of_cover`, applied to the covering `{g}`.

Essential surjectivity is proved by constructing the descent of a descent datum `D` for `f`.
Descending its base change along `g j` gives an object `G j` over `Z j`; the pullbacks of `G j`
and `G k` to `Z j ×_Y Z k` are compared through `X i ×_Y (Z j ×_Y Z k)`
(`CategoryTheory.Pseudofunctor.exists_baseChangeGluing`), using that `X i ×_Y Z j` is a base
change, so that each point of `X i ×_Y (Z j ×_Y Z k)` lifts to `X i ×_Y Z j` and to
`X i ×_Y Z k` over the same point of `X i`. The cocycle condition of the resulting descent datum
along `g` holds after pulling back to `X i ×_Y (Z j ×_Y Z k ×_Y Z l)`, which is where the
faithfulness condition over the triple products enters; for a general pseudofunctor it does not
follow from the other hypotheses. Descending along `g` gives an object `M` over `Y`, and the
descent datum of `M` is identified with `D` after refining both along the family
`X i ×_Y Z j ⟶ Y`, the refinement functor `F.DescentData f ⥤ F.DescentData (…)` being fully
faithful by `CategoryTheory.Pseudofunctor.DescentData.nonempty_fullyFaithful_pullFunctor`.

All comparisons are made on explicit components with
`CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom`, and the descent datum along `g`
is built directly on `Limits.pullback` rather than through
`CategoryTheory.Pseudofunctor.DescentData'`: the latter's chosen fibre products are only
definitionally equal to `Limits.pullback`, and rewriting through that identification is not
type correct at the transparency the tactic framework uses.

Nothing here carries a Stacks attribute: this is category-theoretic substrate.

## References

* [Stacks Project, Tag 0GF1](https://stacks.math.columbia.edu/tag/0GF1)
-/

@[expose] public section

universe t t' v' u' v u

namespace CategoryTheory

open Opposite Limits Bicategory Pseudofunctor.LocallyDiscreteOpToCat

namespace Adjunction

variable {𝒜 𝒜' ℬ ℬ' : Type*} [Category 𝒜] [Category 𝒜'] [Category ℬ] [Category ℬ']

/-- **Faithfulness transported along a base-change morphism.** Let `L ⊣ R` be an adjunction,
let `U : 𝒜 ⥤ ℬ` and `U' : 𝒜' ⥤ ℬ'` be functors and let `β : R ⋙ U ⟶ U' ⋙ R'` be a natural
transformation whose components are monomorphisms. If two morphisms `L A ⟶ N` agree after
applying `U'`, their transposes `A ⟶ R N` agree after applying `U`. -/
lemma map_homEquiv_eq_of_map_eq {L : 𝒜 ⥤ 𝒜'} {R : 𝒜' ⥤ 𝒜} (adj : L ⊣ R) (U : 𝒜 ⥤ ℬ)
    (U' : 𝒜' ⥤ ℬ') (R' : ℬ' ⥤ ℬ) (β : R ⋙ U ⟶ U' ⋙ R') [∀ N, Mono (β.app N)] {A : 𝒜}
    {N : 𝒜'} {x y : L.obj A ⟶ N} (h : U'.map x = U'.map y) :
    U.map (adj.homEquiv _ _ x) = U.map (adj.homEquiv _ _ y) := by
  have key : ∀ z : L.obj A ⟶ N, U.map (adj.homEquiv _ _ z) ≫ β.app N =
      U.map (adj.unit.app A) ≫ β.app (L.obj A) ≫ R'.map (U'.map z) := fun z ↦ by
    rw [Adjunction.homEquiv_unit, U.map_comp, Category.assoc]
    exact congrArg (U.map (adj.unit.app A) ≫ ·) (β.naturality z)
  rw [← cancel_mono (β.app N), key, key, h]

end Adjunction

namespace Pseudofunctor

variable {C : Type u} [Category.{v} C] {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}}

section PullHom

/-- Pulling back an identity gives an identity. -/
@[simp]
lemma pullHom_id_eq_id ⦃X₁ : C⦄ ⦃M₁ : F.obj (.mk (op X₁))⦄ ⦃Y : C⦄ ⦃f₁ : Y ⟶ X₁⦄
    ⦃Y' : C⦄ (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (hgf₁ : g ≫ f₁ = gf₁) :
    pullHom (𝟙 ((F.map f₁.op.toLoc).toFunctor.obj M₁)) g gf₁ gf₁ hgf₁ hgf₁ = 𝟙 _ := by
  simp [pullHom]

/-- The morphism `g ↦ pullHom φ g ..` only depends on `g` through its value. -/
lemma pullHom_congr ⦃X₁ X₂ : C⦄ ⦃M₁ : F.obj (.mk (op X₁))⦄ ⦃M₂ : F.obj (.mk (op X₂))⦄
    ⦃Y : C⦄ ⦃f₁ : Y ⟶ X₁⦄ ⦃f₂ : Y ⟶ X₂⦄
    (φ : (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶ (F.map f₂.op.toLoc).toFunctor.obj M₂) ⦃Y' : C⦄
    {g g' : Y' ⟶ Y} (hg : g = g') (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂) (hgf₁ : g ≫ f₁ = gf₁)
    (hgf₂ : g ≫ f₂ = gf₂) :
    pullHom φ g gf₁ gf₂ hgf₁ hgf₂ = pullHom φ g' gf₁ gf₂ (hg ▸ hgf₁) (hg ▸ hgf₂) := by
  subst hg
  rfl

/-- Two morphisms with the same pullback along `u` have the same inverse image along `u`. -/
lemma map_eq_map_of_pullHom_eq {V S X₁ X₂ : C} {M₁ : F.obj (.mk (op X₁))}
    {M₂ : F.obj (.mk (op X₂))} {k₁ : S ⟶ X₁} {k₂ : S ⟶ X₂}
    {φ φ' : (F.map k₁.op.toLoc).toFunctor.obj M₁ ⟶ (F.map k₂.op.toLoc).toFunctor.obj M₂}
    (u : V ⟶ S) (v₁ : V ⟶ X₁) (v₂ : V ⟶ X₂) (hv₁ : u ≫ k₁ = v₁) (hv₂ : u ≫ k₂ = v₂)
    (h : pullHom φ u v₁ v₂ hv₁ hv₂ = pullHom φ' u v₁ v₂ hv₁ hv₂) :
    (F.map u.op.toLoc).toFunctor.map φ = (F.map u.op.toLoc).toFunctor.map φ' := by
  rw [map_eq_pullHom φ u v₁ v₂ hv₁ hv₂, map_eq_pullHom φ' u v₁ v₂ hv₁ hv₂, h]

/-- Pulling back the conjugate of `θ` by the composition comparisons of `u` with `k₁` and `k₂`
is the conjugate, by the composition comparisons of `q` with `k₁` and `k₂`, of the pullback of
`θ`. -/
lemma pullHom_mapComp'_conj {V S T X₁ X₂ : C} (u : V ⟶ S) (k₁ : S ⟶ X₁) (k₂ : S ⟶ X₂)
    {M₁ : F.obj (.mk (op X₁))} {M₂ : F.obj (.mk (op X₂))}
    (θ : (F.map (u ≫ k₁).op.toLoc).toFunctor.obj M₁ ⟶
      (F.map (u ≫ k₂).op.toLoc).toFunctor.obj M₂) (t : T ⟶ V) (q : T ⟶ S) (hq : t ≫ u = q) :
    pullHom ((F.mapComp' k₁.op.toLoc u.op.toLoc (u ≫ k₁).op.toLoc (by
          rw [← Quiver.Hom.comp_toLoc, ← op_comp])).inv.toNatTrans.app M₁ ≫ θ ≫
        (F.mapComp' k₂.op.toLoc u.op.toLoc (u ≫ k₂).op.toLoc (by
          rw [← Quiver.Hom.comp_toLoc, ← op_comp])).hom.toNatTrans.app M₂) t q q hq hq =
      (F.mapComp' k₁.op.toLoc q.op.toLoc (q ≫ k₁).op.toLoc (by
          rw [← Quiver.Hom.comp_toLoc, ← op_comp])).inv.toNatTrans.app M₁ ≫
        pullHom θ t (q ≫ k₁) (q ≫ k₂) (by rw [← hq, Category.assoc])
          (by rw [← hq, Category.assoc]) ≫
        (F.mapComp' k₂.op.toLoc q.op.toLoc (q ≫ k₂).op.toLoc (by
          rw [← Quiver.Hom.comp_toLoc, ← op_comp])).hom.toNatTrans.app M₂ := by
  simp only [pullHom, Functor.map_comp, Category.assoc]
  rw [F.mapComp'₀₁₃_inv_comp_mapComp'₀₂₃_hom_app_assoc k₁.op.toLoc u.op.toLoc t.op.toLoc
      (u ≫ k₁).op.toLoc q.op.toLoc (q ≫ k₁).op.toLoc
      (by rw [← Quiver.Hom.comp_toLoc, ← op_comp])
      (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, hq])
      (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, ← hq, Category.assoc]) M₁,
    F.mapComp'₀₂₃_inv_comp_mapComp'₀₁₃_hom_app k₂.op.toLoc u.op.toLoc t.op.toLoc
      (u ≫ k₂).op.toLoc q.op.toLoc (q ≫ k₂).op.toLoc
      (by rw [← Quiver.Hom.comp_toLoc, ← op_comp])
      (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, hq])
      (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, ← hq, Category.assoc]) M₂]

/-- **Descending a family of pullback morphisms along a family of morphisms of effective
descent for morphisms.** Let `u i : V i ⟶ S` be a family along which `F.toDescentData` is full,
and let `θ i : (u i ≫ k₁)^* M₁ ⟶ (u i ≫ k₂)^* M₂` be morphisms whose pullbacks along any two
maps `t₁, t₂` with `t₁ ≫ u i₁ = t₂ ≫ u i₂` agree. Then the `θ i` are the pullbacks along the
`u i` of a single morphism `k₁^* M₁ ⟶ k₂^* M₂`. -/
lemma exists_pullHom_eq_of_full {ι : Type t} {V : ι → C} {S X₁ X₂ : C} (u : ∀ i, V i ⟶ S)
    [(F.toDescentData u).Full] {M₁ : F.obj (.mk (op X₁))} {M₂ : F.obj (.mk (op X₂))}
    (k₁ : S ⟶ X₁) (k₂ : S ⟶ X₂)
    (θ : ∀ i, (F.map (u i ≫ k₁).op.toLoc).toFunctor.obj M₁ ⟶
      (F.map (u i ≫ k₂).op.toLoc).toFunctor.obj M₂)
    (hθ : ∀ ⦃T : C⦄ (i₁ i₂ : ι) (t₁ : T ⟶ V i₁) (t₂ : T ⟶ V i₂) (r : T ⟶ S)
      (h₁ : t₁ ≫ u i₁ = r) (h₂ : t₂ ≫ u i₂ = r),
      pullHom (θ i₁) t₁ (r ≫ k₁) (r ≫ k₂) (by rw [← h₁, Category.assoc])
          (by rw [← h₁, Category.assoc]) =
        pullHom (θ i₂) t₂ (r ≫ k₁) (r ≫ k₂) (by rw [← h₂, Category.assoc])
          (by rw [← h₂, Category.assoc])) :
    ∃ ψ : (F.map k₁.op.toLoc).toFunctor.obj M₁ ⟶ (F.map k₂.op.toLoc).toFunctor.obj M₂,
      ∀ i, pullHom ψ (u i) (u i ≫ k₁) (u i ≫ k₂) rfl rfl = θ i := by
  let M := (F.map k₁.op.toLoc).toFunctor.obj M₁
  let N := (F.map k₂.op.toLoc).toFunctor.obj M₂
  let Θ : ∀ i, (F.map (u i).op.toLoc).toFunctor.obj M ⟶
      (F.map (u i).op.toLoc).toFunctor.obj N := fun i ↦
    (F.mapComp' k₁.op.toLoc (u i).op.toLoc (u i ≫ k₁).op.toLoc (by
        rw [← Quiver.Hom.comp_toLoc, ← op_comp])).inv.toNatTrans.app M₁ ≫ θ i ≫
      (F.mapComp' k₂.op.toLoc (u i).op.toLoc (u i ≫ k₂).op.toLoc (by
        rw [← Quiver.Hom.comp_toLoc, ← op_comp])).hom.toNatTrans.app M₂
  have key : ∀ ⦃Y : C⦄ (q : Y ⟶ S) (i₁ i₂ : ι) (f₁ : Y ⟶ V i₁) (f₂ : Y ⟶ V i₂)
      (hf₁ : f₁ ≫ u i₁ = q) (hf₂ : f₂ ≫ u i₂ = q),
      (F.map f₁.op.toLoc).toFunctor.map (Θ i₁) ≫
          ((F.mapComp' (u i₁).op.toLoc f₁.op.toLoc q.op.toLoc (by
              rw [← Quiver.Hom.comp_toLoc, ← op_comp, hf₁])).inv.toNatTrans.app N ≫
            (F.mapComp' (u i₂).op.toLoc f₂.op.toLoc q.op.toLoc (by
              rw [← Quiver.Hom.comp_toLoc, ← op_comp, hf₂])).hom.toNatTrans.app N) =
        ((F.mapComp' (u i₁).op.toLoc f₁.op.toLoc q.op.toLoc (by
              rw [← Quiver.Hom.comp_toLoc, ← op_comp, hf₁])).inv.toNatTrans.app M ≫
            (F.mapComp' (u i₂).op.toLoc f₂.op.toLoc q.op.toLoc (by
              rw [← Quiver.Hom.comp_toLoc, ← op_comp, hf₂])).hom.toNatTrans.app M) ≫
          (F.map f₂.op.toLoc).toFunctor.map (Θ i₂) := by
    intro Y q i₁ i₂ f₁ f₂ hf₁ hf₂
    have hp : pullHom (Θ i₁) f₁ q q hf₁ hf₁ = pullHom (Θ i₂) f₂ q q hf₂ hf₂ := by
      simp only [Θ, pullHom_mapComp'_conj]
      rw [hθ i₁ i₂ f₁ f₂ q hf₁ hf₂]
    rw [map_eq_pullHom (Θ i₁) f₁ q q hf₁ hf₁, map_eq_pullHom (Θ i₂) f₂ q q hf₂ hf₂, hp]
    simp
  let Φ : (F.toDescentData u).obj M ⟶ (F.toDescentData u).obj N :=
    { hom := Θ
      comm := fun Y q i₁ i₂ f₁ f₂ hf₁ hf₂ ↦ key q i₁ i₂ f₁ f₂ hf₁ hf₂ }
  obtain ⟨ψ, hψ⟩ := (F.toDescentData u).map_surjective Φ
  refine ⟨ψ, fun i ↦ ?_⟩
  have h : (F.map (u i).op.toLoc).toFunctor.map ψ = Θ i :=
    congrArg (fun φ ↦ DescentData.Hom.hom φ i) hψ
  simp only [pullHom, h, Θ, Category.assoc, Cat.Hom.hom_inv_id_toNatTrans_app_assoc]
  rw [Cat.Hom.hom_inv_id_toNatTrans_app, Category.comp_id]

/-- A family along which `F.toDescentData` is faithful is jointly faithful for the inverse
images. -/
lemma eq_of_toDescentData_faithful {ι : Type t} {V : ι → C} {S : C} (u : ∀ i, V i ⟶ S)
    [(F.toDescentData u).Faithful] {M N : F.obj (.mk (op S))} {φ φ' : M ⟶ N}
    (h : ∀ i, (F.map (u i).op.toLoc).toFunctor.map φ = (F.map (u i).op.toLoc).toFunctor.map φ') :
    φ = φ' :=
  (F.toDescentData u).map_injective (DescentData.hom_ext h)


section PullFunctor

variable {ι : Type t} {S S' : C} {X X' : ι → C} {f : ∀ i, X i ⟶ S}
  {f' : ∀ i, X' i ⟶ S'} {p : S' ⟶ S} {p' : ∀ i, X' i ⟶ X i}
  (w : ∀ i, p' i ≫ f i = f' i ≫ p) (D : F.DescentData f) {G : F.obj (.mk (op S'))}

/-- **A morphism into a pulled-back descent datum, at two points.** Let `φ` be the family of
components of a morphism of descent data from the canonical descent datum of `G` to the
pullback of `D` along a morphism of families, its compatibility written out as `hφ`. Its
pullbacks at two points of the family lying over the same point of the base differ by the
gluing morphism of `D`. -/
lemma pullHom_comp_hom_eq_of_comm
    (φ : ∀ i, (F.map (f' i).op.toLoc).toFunctor.obj G ⟶
      (F.map (p' i).op.toLoc).toFunctor.obj (D.obj i))
    (hφ : ∀ ⦃T : C⦄ (q : T ⟶ S') (i₁ i₂ : ι) (t₁ : T ⟶ X' i₁) (t₂ : T ⟶ X' i₂)
      (h₁ : t₁ ≫ f' i₁ = q) (h₂ : t₂ ≫ f' i₂ = q),
      (F.map t₁.op.toLoc).toFunctor.map (φ i₁) ≫
          DescentData.pullFunctorObjHom (α := fun i ↦ i) w D (t₁ ≫ f' i₁) t₁ t₂ rfl
            (h₂.trans h₁.symm) =
        ((F.mapComp' (f' i₁).op.toLoc t₁.op.toLoc q.op.toLoc (by
              rw [← Quiver.Hom.comp_toLoc, ← op_comp, h₁])).inv.toNatTrans.app G ≫
            (F.mapComp' (f' i₂).op.toLoc t₂.op.toLoc q.op.toLoc (by
              rw [← Quiver.Hom.comp_toLoc, ← op_comp, h₂])).hom.toNatTrans.app G) ≫
          (F.map t₂.op.toLoc).toFunctor.map (φ i₂))
    ⦃T : C⦄ (i₁ i₂ : ι) (t₁ : T ⟶ X' i₁) (t₂ : T ⟶ X' i₂) (q : T ⟶ S')
    (h₁ : t₁ ≫ f' i₁ = q) (h₂ : t₂ ≫ f' i₂ = q) (x₁ : T ⟶ X i₁) (x₂ : T ⟶ X i₂)
    (hx₁ : t₁ ≫ p' i₁ = x₁) (hx₂ : t₂ ≫ p' i₂ = x₂) (q' : T ⟶ S) (hq' : q ≫ p = q') :
    pullHom (φ i₁) t₁ q x₁ h₁ hx₁ ≫
        D.hom q' x₁ x₂ (by rw [← hx₁, Category.assoc, w, reassoc_of% h₁, hq'])
          (by rw [← hx₂, Category.assoc, w, reassoc_of% h₂, hq']) =
      pullHom (φ i₂) t₂ q x₂ h₂ hx₂ := by
  have hc := hφ q i₁ i₂ t₁ t₂ h₁ h₂
  rw [DescentData.pullFunctorObjHom_eq w D (t₁ ≫ f' i₁) t₁ t₂ q' x₁ x₂ rfl
      (h₂.trans h₁.symm) (by rw [h₁, hq']) hx₁ hx₂,
    map_eq_pullHom (φ i₁) t₁ q x₁ h₁ hx₁, map_eq_pullHom (φ i₂) t₂ q x₂ h₂ hx₂] at hc
  simp only [Category.assoc, Cat.Hom.hom_inv_id_toNatTrans_app_assoc] at hc
  rw [cancel_epi] at hc
  simpa only [← Category.assoc, cancel_mono] using hc

/-- The companion of `CategoryTheory.Pseudofunctor.pullHom_comp_hom_eq_of_comm` for a morphism
of descent data out of a pulled-back descent datum into the canonical descent datum of `G`. -/
lemma hom_comp_pullHom_eq_of_comm
    (φ : ∀ i, (F.map (p' i).op.toLoc).toFunctor.obj (D.obj i) ⟶
      (F.map (f' i).op.toLoc).toFunctor.obj G)
    (hφ : ∀ ⦃T : C⦄ (q : T ⟶ S') (i₁ i₂ : ι) (t₁ : T ⟶ X' i₁) (t₂ : T ⟶ X' i₂)
      (h₁ : t₁ ≫ f' i₁ = q) (h₂ : t₂ ≫ f' i₂ = q),
      (F.map t₁.op.toLoc).toFunctor.map (φ i₁) ≫
          ((F.mapComp' (f' i₁).op.toLoc t₁.op.toLoc q.op.toLoc (by
              rw [← Quiver.Hom.comp_toLoc, ← op_comp, h₁])).inv.toNatTrans.app G ≫
            (F.mapComp' (f' i₂).op.toLoc t₂.op.toLoc q.op.toLoc (by
              rw [← Quiver.Hom.comp_toLoc, ← op_comp, h₂])).hom.toNatTrans.app G) =
        DescentData.pullFunctorObjHom (α := fun i ↦ i) w D (t₁ ≫ f' i₁) t₁ t₂ rfl
            (h₂.trans h₁.symm) ≫
          (F.map t₂.op.toLoc).toFunctor.map (φ i₂))
    ⦃T : C⦄ (i₁ i₂ : ι) (t₁ : T ⟶ X' i₁) (t₂ : T ⟶ X' i₂) (q : T ⟶ S')
    (h₁ : t₁ ≫ f' i₁ = q) (h₂ : t₂ ≫ f' i₂ = q) (x₁ : T ⟶ X i₁) (x₂ : T ⟶ X i₂)
    (hx₁ : t₁ ≫ p' i₁ = x₁) (hx₂ : t₂ ≫ p' i₂ = x₂) (q' : T ⟶ S) (hq' : q ≫ p = q') :
    D.hom q' x₁ x₂ (by rw [← hx₁, Category.assoc, w, reassoc_of% h₁, hq'])
          (by rw [← hx₂, Category.assoc, w, reassoc_of% h₂, hq']) ≫
        pullHom (φ i₂) t₂ x₂ q hx₂ h₂ =
      pullHom (φ i₁) t₁ x₁ q hx₁ h₁ := by
  have hc := hφ q i₁ i₂ t₁ t₂ h₁ h₂
  rw [DescentData.pullFunctorObjHom_eq w D (t₁ ≫ f' i₁) t₁ t₂ q' x₁ x₂ rfl
      (h₂.trans h₁.symm) (by rw [h₁, hq']) hx₁ hx₂,
    map_eq_pullHom (φ i₁) t₁ x₁ q hx₁ h₁, map_eq_pullHom (φ i₂) t₂ x₂ q hx₂ h₂] at hc
  simp only [Category.assoc, Cat.Hom.hom_inv_id_toNatTrans_app_assoc] at hc
  rw [cancel_epi] at hc
  simpa only [← Category.assoc, cancel_mono] using hc.symm

end PullFunctor

end PullHom

section BaseChange

variable [HasPullbacks C] {ι : Type t} {κ : Type t'} {Y : C} {X : ι → C} {Z : κ → C}
  (f : ∀ i, X i ⟶ Y) (g : ∀ j, Z j ⟶ Y)

/-- The map `X i ×_Y (Z j ×_Y Z k) ⟶ X i ×_Y Z j` given by the first projection. -/
noncomputable abbrev baseChangeProj₁ (i : ι) (j k : κ) :
    pullback (f i) (pullback.fst (g j) (g k) ≫ g j) ⟶ pullback (f i) (g j) :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ pullback.fst (g j) (g k))
    (pullback.condition.trans (Category.assoc _ _ _).symm)

/-- The map `X i ×_Y (Z j ×_Y Z k) ⟶ X i ×_Y Z k` given by the second projection. -/
noncomputable abbrev baseChangeProj₂ (i : ι) (j k : κ) :
    pullback (f i) (pullback.fst (g j) (g k) ≫ g j) ⟶ pullback (f i) (g k) :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ pullback.snd (g j) (g k))
    (by rw [Category.assoc, ← pullback.condition (f := g j) (g := g k)]; exact pullback.condition)

/-- The composite of `baseChangeProj₁` with the first projection to `X i` is the first
projection of `X i ×_Y (Z j ×_Y Z k)`. -/
@[reassoc (attr := simp)]
lemma baseChangeProj₁_fst (i : ι) (j k : κ) :
    baseChangeProj₁ f g i j k ≫ pullback.fst (f i) (g j) = pullback.fst _ _ :=
  pullback.lift_fst _ _ _

/-- The composite of `baseChangeProj₁` with the projection to `Z j` is the projection of
`X i ×_Y (Z j ×_Y Z k)` to `Z j`. -/
@[reassoc (attr := simp)]
lemma baseChangeProj₁_snd (i : ι) (j k : κ) :
    baseChangeProj₁ f g i j k ≫ pullback.snd (f i) (g j) =
      pullback.snd (f i) (pullback.fst (g j) (g k) ≫ g j) ≫ pullback.fst (g j) (g k) :=
  pullback.lift_snd _ _ _

/-- The composite of `baseChangeProj₂` with the first projection to `X i` is the first
projection of `X i ×_Y (Z j ×_Y Z k)`. -/
@[reassoc (attr := simp)]
lemma baseChangeProj₂_fst (i : ι) (j k : κ) :
    baseChangeProj₂ f g i j k ≫ pullback.fst (f i) (g k) = pullback.fst _ _ :=
  pullback.lift_fst _ _ _

/-- The composite of `baseChangeProj₂` with the projection to `Z k` is the projection of
`X i ×_Y (Z j ×_Y Z k)` to `Z k`. -/
@[reassoc (attr := simp)]
lemma baseChangeProj₂_snd (i : ι) (j k : κ) :
    baseChangeProj₂ f g i j k ≫ pullback.snd (f i) (g k) =
      pullback.snd (f i) (pullback.fst (g j) (g k) ≫ g j) ≫ pullback.snd (g j) (g k) :=
  pullback.lift_snd _ _ _

variable {f g}

/-- **The gluing morphisms over `Z j ×_Y Z k`.** Let `D` be a descent datum for the family `f`,
and let objects `G j` over `Z j` come with mutually inverse identifications `α i j`, `α' i j` of
their inverse images on `X i ×_Y Z j` with those of the components of `D`, compatible with the
gluing of `D` over pairs of points with the same image in `Z j`. If `F.toDescentData` is full
along the base change `{X i ×_Y (Z j ×_Y Z k) ⟶ Z j ×_Y Z k}`, there is a morphism
`ψ : pr₁^* G j ⟶ pr₂^* G k` whose pullback to any point of `Z j ×_Y Z k` lifting to
`X i ×_Y Z j` and to `X i ×_Y Z k` over the same point of `X i` is the composite of the two
identifications there. -/
lemma exists_baseChangeGluing (D : F.DescentData f) (G : ∀ j, F.obj (.mk (op (Z j))))
    (α : ∀ i j, (F.map (pullback.snd (f i) (g j)).op.toLoc).toFunctor.obj (G j) ⟶
      (F.map (pullback.fst (f i) (g j)).op.toLoc).toFunctor.obj (D.obj i))
    (α' : ∀ i j, (F.map (pullback.fst (f i) (g j)).op.toLoc).toFunctor.obj (D.obj i) ⟶
      (F.map (pullback.snd (f i) (g j)).op.toLoc).toFunctor.obj (G j))
    (hα : ∀ ⦃T : C⦄ (j : κ) (i₁ i₂ : ι) (t₁ : T ⟶ pullback (f i₁) (g j))
      (t₂ : T ⟶ pullback (f i₂) (g j))
      (q : T ⟶ Z j) (h₁ : t₁ ≫ pullback.snd _ _ = q) (h₂ : t₂ ≫ pullback.snd _ _ = q)
      (x₁ : T ⟶ X i₁) (x₂ : T ⟶ X i₂) (hx₁ : t₁ ≫ pullback.fst _ _ = x₁)
      (hx₂ : t₂ ≫ pullback.fst _ _ = x₂) (q' : T ⟶ Y) (hq' : q ≫ g j = q'),
      pullHom (α i₁ j) t₁ q x₁ h₁ hx₁ ≫
          D.hom q' x₁ x₂ (by rw [← hx₁, Category.assoc, pullback.condition, reassoc_of% h₁, hq'])
            (by rw [← hx₂, Category.assoc, pullback.condition, reassoc_of% h₂, hq']) =
        pullHom (α i₂ j) t₂ q x₂ h₂ hx₂)
    (hα' : ∀ ⦃T : C⦄ (j : κ) (i₁ i₂ : ι) (t₁ : T ⟶ pullback (f i₁) (g j))
      (t₂ : T ⟶ pullback (f i₂) (g j))
      (q : T ⟶ Z j) (h₁ : t₁ ≫ pullback.snd _ _ = q) (h₂ : t₂ ≫ pullback.snd _ _ = q)
      (x₁ : T ⟶ X i₁) (x₂ : T ⟶ X i₂) (hx₁ : t₁ ≫ pullback.fst _ _ = x₁)
      (hx₂ : t₂ ≫ pullback.fst _ _ = x₂) (q' : T ⟶ Y) (hq' : q ≫ g j = q'),
      D.hom q' x₁ x₂ (by rw [← hx₁, Category.assoc, pullback.condition, reassoc_of% h₁, hq'])
            (by rw [← hx₂, Category.assoc, pullback.condition, reassoc_of% h₂, hq']) ≫
          pullHom (α' i₂ j) t₂ x₂ q hx₂ h₂ =
        pullHom (α' i₁ j) t₁ x₁ q hx₁ h₁) (j k : κ)
    [(F.toDescentData (fun i ↦ pullback.snd (f i) (pullback.fst (g j) (g k) ≫ g j))).Full] :
    ∃ ψ : (F.map (pullback.fst (g j) (g k)).op.toLoc).toFunctor.obj (G j) ⟶
        (F.map (pullback.snd (g j) (g k)).op.toLoc).toFunctor.obj (G k),
      ∀ ⦃T : C⦄ (i : ι) (e₁ : T ⟶ pullback (f i) (g j)) (e₂ : T ⟶ pullback (f i) (g k))
        (x : T ⟶ X i) (he₁ : e₁ ≫ pullback.fst _ _ = x) (he₂ : e₂ ≫ pullback.fst _ _ = x)
        (τ : T ⟶ pullback (g j) (g k)) (z₁ : T ⟶ Z j) (z₂ : T ⟶ Z k)
        (hτ₁ : τ ≫ pullback.fst (g j) (g k) = z₁) (hτ₂ : τ ≫ pullback.snd (g j) (g k) = z₂)
        (hz₁ : e₁ ≫ pullback.snd _ _ = z₁) (hz₂ : e₂ ≫ pullback.snd _ _ = z₂),
        pullHom ψ τ z₁ z₂ hτ₁ hτ₂ =
          pullHom (α i j) e₁ z₁ x hz₁ he₁ ≫ pullHom (α' i k) e₂ x z₂ he₂ hz₂ := by
  let u := fun i ↦ pullback.snd (f i) (pullback.fst (g j) (g k) ≫ g j)
  let θ : ∀ i, (F.map (u i ≫ pullback.fst (g j) (g k)).op.toLoc).toFunctor.obj (G j) ⟶
      (F.map (u i ≫ pullback.snd (g j) (g k)).op.toLoc).toFunctor.obj (G k) := fun i ↦
    pullHom (α i j) (baseChangeProj₁ f g i j k) (u i ≫ pullback.fst (g j) (g k))
        (pullback.fst _ _) (baseChangeProj₁_snd f g i j k) (baseChangeProj₁_fst f g i j k) ≫
      pullHom (α' i k) (baseChangeProj₂ f g i j k) (pullback.fst _ _)
        (u i ≫ pullback.snd (g j) (g k))
        (baseChangeProj₂_fst f g i j k) (baseChangeProj₂_snd f g i j k)
  obtain ⟨ψ, hψ⟩ := exists_pullHom_eq_of_full u (pullback.fst (g j) (g k))
    (pullback.snd (g j) (g k)) θ (by
    intro T i₁ i₂ t₁ t₂ r h₁ h₂
    simp only [θ, pullHom_comp _ _ t₁ _ (t₁ ≫ pullback.fst _ _) _ _ rfl _,
      pullHom_comp _ _ t₂ _ (t₂ ≫ pullback.fst _ _) _ _ rfl _, pullHom_pullHom]
    rw [← hα' k i₁ i₂ (t₁ ≫ baseChangeProj₂ f g i₁ j k) (t₂ ≫ baseChangeProj₂ f g i₂ j k)
        (r ≫ pullback.snd (g j) (g k)) (by simp [← h₁, u]) (by simp [← h₂, u])
        (t₁ ≫ pullback.fst _ _) (t₂ ≫ pullback.fst _ _) (by simp) (by simp)
        ((r ≫ pullback.fst (g j) (g k)) ≫ g j) (by simp [pullback.condition])]
    refine (Category.assoc _ _ _).symm.trans ?_
    rw [hα j i₁ i₂ (t₁ ≫ baseChangeProj₁ f g i₁ j k) (t₂ ≫ baseChangeProj₁ f g i₂ j k)
        (r ≫ pullback.fst (g j) (g k)) (by simp [← h₁, u]) (by simp [← h₂, u])
        (t₁ ≫ pullback.fst _ _) (t₂ ≫ pullback.fst _ _) (by simp) (by simp)
        ((r ≫ pullback.fst (g j) (g k)) ≫ g j) rfl])
  refine ⟨ψ, fun T i e₁ e₂ x he₁ he₂ τ z₁ z₂ hτ₁ hτ₂ hz₁ hz₂ ↦ ?_⟩
  have hxτ : x ≫ f i = τ ≫ pullback.fst (g j) (g k) ≫ g j := by
    rw [← he₁, Category.assoc, pullback.condition, ← Category.assoc, hz₁, ← hτ₁,
      Category.assoc]
  obtain ⟨t, htx, ht⟩ : ∃ t : T ⟶ pullback (f i) (pullback.fst (g j) (g k) ≫ g j),
      t ≫ pullback.fst _ _ = x ∧ t ≫ u i = τ :=
    ⟨pullback.lift x τ hxτ, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have ht₁ : t ≫ baseChangeProj₁ f g i j k = e₁ := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, htx, he₁]
    · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, ht, hτ₁, hz₁]
  have ht₂ : t ≫ baseChangeProj₂ f g i j k = e₂ := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, htx, he₂]
    · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, ht, hτ₂, hz₂]
  rw [pullHom_congr ψ ht.symm, ← pullHom_pullHom ψ (u i) (u i ≫ pullback.fst (g j) (g k))
      (u i ≫ pullback.snd (g j) (g k)) t z₁ z₂ rfl rfl (by rw [← Category.assoc, ht, hτ₁])
      (by rw [← Category.assoc, ht, hτ₂]), hψ i, pullHom_comp _ _ t _ x _ _ htx _,
    pullHom_pullHom, pullHom_pullHom, pullHom_congr (α i j) ht₁, pullHom_congr (α' i k) ht₂]

variable (f g) in
/-- The pullback along a morphism `t` factoring through a member of `f` of the sieve generated
by the structure morphisms `X i ×_Y Z j ⟶ Y` is the sieve generated by the base change of `g`
along `t`. -/
lemma sieve_pullback_ofArrows_baseChange {T : C} (t : T ⟶ Y) (i₀ : ι) (a : T ⟶ X i₀)
    (ha : a ≫ f i₀ = t) :
    Sieve.pullback t (Sieve.ofArrows (fun p : ι × κ ↦ pullback (f p.1) (g p.2))
        (fun p ↦ pullback.fst (f p.1) (g p.2) ≫ f p.1)) =
      Sieve.ofArrows (fun j ↦ pullback t (g j)) (fun j ↦ pullback.fst t (g j)) := by
  apply le_antisymm
  · intro T' t' ht'
    obtain ⟨p, b, hb⟩ := (Sieve.mem_ofArrows_iff _ _ _).1 ht'
    rw [Sieve.mem_ofArrows_iff]
    refine ⟨p.2, pullback.lift t' (b ≫ pullback.snd _ _) ?_, (pullback.lift_fst _ _ _).symm⟩
    rw [hb, Category.assoc, pullback.condition]
  · intro T' t' ht'
    obtain ⟨j, c, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ _).1 ht'
    rw [Sieve.pullback_apply, Sieve.mem_ofArrows_iff]
    refine ⟨(i₀, j), pullback.lift (c ≫ pullback.fst t (g j) ≫ a) (c ≫ pullback.snd t (g j)) ?_,
      ?_⟩
    · rw [Category.assoc, Category.assoc, ha, pullback.condition, Category.assoc]
    · rw [pullback.lift_fst_assoc]
      simp only [Category.assoc, ha]

variable (g) in
/-- The first projection `Z j ×_Y Z k ×_Y Z l ⟶ Z j`, the triple product being presented as
`(Z j ×_Y Z k) ×_{Z k} (Z k ×_Y Z l)`. -/
noncomputable abbrev tripleProj₁ (j k l : κ) :
    pullback (pullback.snd (g j) (g k)) (pullback.fst (g k) (g l)) ⟶ Z j :=
  pullback.fst _ _ ≫ pullback.fst (g j) (g k)

variable (g) in
/-- The second projection `Z j ×_Y Z k ×_Y Z l ⟶ Z k`. -/
noncomputable abbrev tripleProj₂ (j k l : κ) :
    pullback (pullback.snd (g j) (g k)) (pullback.fst (g k) (g l)) ⟶ Z k :=
  pullback.fst _ _ ≫ pullback.snd (g j) (g k)

variable (g) in
/-- The third projection `Z j ×_Y Z k ×_Y Z l ⟶ Z l`. -/
noncomputable abbrev tripleProj₃ (j k l : κ) :
    pullback (pullback.snd (g j) (g k)) (pullback.fst (g k) (g l)) ⟶ Z l :=
  pullback.snd _ _ ≫ pullback.snd (g k) (g l)

variable (g) in
/-- The second and first projections of `Z j ×_Y Z k ×_Y Z l` agree after composing to `Y`. -/
lemma tripleProj₂_comp (j k l : κ) : tripleProj₂ g j k l ≫ g k = tripleProj₁ g j k l ≫ g j := by
  simp only [tripleProj₂, tripleProj₁, Category.assoc]
  rw [pullback.condition (f := g j) (g := g k)]

variable (g) in
/-- The third and first projections of `Z j ×_Y Z k ×_Y Z l` agree after composing to `Y`. -/
lemma tripleProj₃_comp (j k l : κ) : tripleProj₃ g j k l ≫ g l = tripleProj₁ g j k l ≫ g j := by
  simp only [tripleProj₃, tripleProj₁, Category.assoc]
  rw [← pullback.condition (f := g k) (g := g l),
    ← pullback.condition_assoc (f := pullback.snd (g j) (g k)) (g := pullback.fst (g k) (g l)),
    ← pullback.condition (f := g j) (g := g k)]

omit [HasPullbacks C] in
/-- Full faithfulness of descent along a base-changed family gives being a prestack for the
pullback of the sieve. -/
theorem isPrestackFor_pullback_of_fullyFaithful {ι' : Type*} {Z' : ι' → C} (h : ∀ i, Z' i ⟶ Y)
    {T : C} (t : T ⟶ Y) (W : ι' → C) (p : ∀ i, W i ⟶ T) (q : ∀ i, W i ⟶ Z' i)
    (hsq : ∀ i, IsPullback (p i) (q i) t (h i))
    (hp : Nonempty (F.toDescentData p).FullyFaithful) :
    F.IsPrestackFor ((Sieve.ofArrows Z' h).pullback t).arrows := by
  rwa [← Sieve.ofArrows_eq_pullback_of_isPullback h hsq, Sieve.ofArrows,
    F.IsPrestackFor_generate_iff, F.isPrestackFor_ofArrows_iff]

variable (f g) in
/-- **Effective descent along a family, from effective descent after base change along a
covering family.** Let `f i : X i ⟶ Y` and `g j : Z j ⟶ Y` be families such that descent is
effective along `g` and descent of morphisms holds along each base change of `g`. If descent is
effective along each base change `{X i ×_Y Z j ⟶ Z j}` of `f`, if descent of morphisms holds along
each base change `{X i ×_Y (Z j ×_Y Z k) ⟶ Z j ×_Y Z k}`, and if over each triple product
`Z j ×_Y Z k ×_Y Z l` the inverse images along the base change of `f` to it are jointly
faithful on the morphisms `pr₁^* G ⟶ pr₃^* G'`, then descent is effective along `f`.

This is the categorical content of Stacks 0GF1. -/
theorem isEquivalence_toDescentData_of_baseChange_unconditional
    (hg : (F.toDescentData g).IsEquivalence)
    (hgT : ∀ ⦃T : C⦄ (t : T ⟶ Y),
      Nonempty (F.toDescentData (fun j ↦ pullback.fst t (g j))).FullyFaithful)
    (hZ : ∀ j, (F.toDescentData (fun i ↦ pullback.snd (f i) (g j))).IsEquivalence)
    (hZZ : ∀ j k, Nonempty (F.toDescentData
      (fun i ↦ pullback.snd (f i) (pullback.fst (g j) (g k) ≫ g j))).FullyFaithful)
    (hZZZ : ∀ (j k l : κ) (G : F.obj (.mk (op (Z j)))) (G' : F.obj (.mk (op (Z l))))
      (x y : (F.map (tripleProj₁ g j k l).op.toLoc).toFunctor.obj G ⟶
        (F.map (tripleProj₃ g j k l).op.toLoc).toFunctor.obj G'),
      (∀ i, (F.map (pullback.snd (f i) (tripleProj₁ g j k l ≫ g j)).op.toLoc).toFunctor.map x =
        (F.map (pullback.snd (f i) (tripleProj₁ g j k l ≫ g j)).op.toLoc).toFunctor.map y) →
        x = y) :
    (F.toDescentData f).IsEquivalence := by
  -- Full faithfulness: being a prestack for the sieve generated by `f` is local on the base.
  have hpre : F.IsPrestackFor (Sieve.ofArrows X f).arrows :=
    isPrestackFor_of_cover F g (fun j k ↦ ChosenPullback.ofHasPullback (g j) (g k))
      (Sieve.ofArrows X f) (isPrestackFor_of_equivalence F _ hg)
      (fun t ↦ isPrestackFor_pullback_of_fullyFaithful g t
        (fun j ↦ pullback t (g j)) (fun j ↦ pullback.fst t (g j)) (fun j ↦ pullback.snd t (g j))
        (fun j ↦ IsPullback.of_hasPullback t (g j)) (hgT t))
      (fun j ↦ isPrestackFor_pullback_of_equivalence F f (g j) (fun i ↦ pullback (f i) (g j))
        (fun i ↦ pullback.snd (f i) (g j)) (fun i ↦ pullback.fst (f i) (g j))
        (fun i ↦ (IsPullback.of_hasPullback (f i) (g j)).flip) (hZ j))
      (fun j k ↦ isPrestackFor_pullback_of_fullyFaithful f (pullback.fst (g j) (g k) ≫ g j)
        (fun i ↦ pullback (f i) (pullback.fst (g j) (g k) ≫ g j))
        (fun i ↦ pullback.snd (f i) (pullback.fst (g j) (g k) ≫ g j))
        (fun i ↦ pullback.fst (f i) (pullback.fst (g j) (g k) ≫ g j))
        (fun i ↦ (IsPullback.of_hasPullback (f i) (pullback.fst (g j) (g k) ≫ g j)).flip)
        (hZZ j k))
  rw [Sieve.ofArrows, IsPrestackFor_generate_iff, isPrestackFor_ofArrows_iff] at hpre
  obtain ⟨hff⟩ := hpre
  have := hff.full
  have := hff.faithful
  -- Essential surjectivity.
  have := hg
  have : ∀ j k, (F.toDescentData
      (fun i ↦ pullback.snd (f i) (pullback.fst (g j) (g k) ≫ g j))).Full := fun j k ↦
    (hZZ j k).some.full
  have : ∀ j, (F.toDescentData (fun i ↦ pullback.snd (f i) (g j))).Faithful := fun j ↦ by
    have := hZ j; infer_instance
  refine { essSurj := ⟨fun D ↦ ?_⟩ }
  have w : ∀ j i, pullback.fst (f i) (g j) ≫ f i = pullback.snd (f i) (g j) ≫ g j :=
    fun _ _ ↦ pullback.condition
  let DZ := fun j ↦ (DescentData.pullFunctor F (α := fun i ↦ i) (w j)).obj D
  let G := fun j ↦ (F.toDescentData (fun i ↦ pullback.snd (f i) (g j))).objPreimage (DZ j)
  have := hZ
  let e := fun j ↦ (F.toDescentData (fun i ↦ pullback.snd (f i) (g j))).objObjPreimageIso (DZ j)
  let α : ∀ i j, (F.map (pullback.snd (f i) (g j)).op.toLoc).toFunctor.obj (G j) ⟶
      (F.map (pullback.fst (f i) (g j)).op.toLoc).toFunctor.obj (D.obj i) :=
    fun i j ↦ (e j).hom.hom i
  let α' : ∀ i j, (F.map (pullback.fst (f i) (g j)).op.toLoc).toFunctor.obj (D.obj i) ⟶
      (F.map (pullback.snd (f i) (g j)).op.toLoc).toFunctor.obj (G j) :=
    fun i j ↦ (e j).inv.hom i
  have hαα' : ∀ i j, α i j ≫ α' i j = 𝟙 _ := fun i j ↦
    congrArg (fun φ ↦ DescentData.Hom.hom φ i) (e j).hom_inv_id
  have hα'α : ∀ i j, α' i j ≫ α i j = 𝟙 _ := fun i j ↦
    congrArg (fun φ ↦ DescentData.Hom.hom φ i) (e j).inv_hom_id
  have hα : ∀ ⦃T : C⦄ (j : κ) (i₁ i₂ : ι) (t₁ : T ⟶ pullback (f i₁) (g j))
      (t₂ : T ⟶ pullback (f i₂) (g j))
      (q : T ⟶ Z j) (h₁ : t₁ ≫ pullback.snd _ _ = q) (h₂ : t₂ ≫ pullback.snd _ _ = q)
      (x₁ : T ⟶ X i₁) (x₂ : T ⟶ X i₂) (hx₁ : t₁ ≫ pullback.fst _ _ = x₁)
      (hx₂ : t₂ ≫ pullback.fst _ _ = x₂) (q' : T ⟶ Y) (hq' : q ≫ g j = q'),
      pullHom (α i₁ j) t₁ q x₁ h₁ hx₁ ≫
          D.hom q' x₁ x₂ (by rw [← hx₁, Category.assoc, pullback.condition, reassoc_of% h₁, hq'])
            (by rw [← hx₂, Category.assoc, pullback.condition, reassoc_of% h₂, hq']) =
        pullHom (α i₂ j) t₂ q x₂ h₂ hx₂ := fun T j ↦
    pullHom_comp_hom_eq_of_comm (w j) D (fun i ↦ α i j)
      (fun T q i₁ i₂ t₁ t₂ h₁ h₂ ↦ (e j).hom.comm q t₁ t₂ h₁ h₂) (T := T)
  have hα' : ∀ ⦃T : C⦄ (j : κ) (i₁ i₂ : ι) (t₁ : T ⟶ pullback (f i₁) (g j))
      (t₂ : T ⟶ pullback (f i₂) (g j))
      (q : T ⟶ Z j) (h₁ : t₁ ≫ pullback.snd _ _ = q) (h₂ : t₂ ≫ pullback.snd _ _ = q)
      (x₁ : T ⟶ X i₁) (x₂ : T ⟶ X i₂) (hx₁ : t₁ ≫ pullback.fst _ _ = x₁)
      (hx₂ : t₂ ≫ pullback.fst _ _ = x₂) (q' : T ⟶ Y) (hq' : q ≫ g j = q'),
      D.hom q' x₁ x₂ (by rw [← hx₁, Category.assoc, pullback.condition, reassoc_of% h₁, hq'])
            (by rw [← hx₂, Category.assoc, pullback.condition, reassoc_of% h₂, hq']) ≫
          pullHom (α' i₂ j) t₂ x₂ q hx₂ h₂ =
        pullHom (α' i₁ j) t₁ x₁ q hx₁ h₁ := fun T j ↦
    hom_comp_pullHom_eq_of_comm (w j) D (fun i ↦ α' i j)
      (fun T q i₁ i₂ t₁ t₂ h₁ h₂ ↦ (e j).inv.comm q t₁ t₂ h₁ h₂) (T := T)
  choose ψ hψ using exists_baseChangeGluing D G α α' hα hα'
  -- The descent datum along `g`.
  have hE0 : ∀ j, pullHom (ψ j j) (pullback.lift (𝟙 (Z j)) (𝟙 (Z j)) rfl) (𝟙 (Z j)) (𝟙 (Z j))
      (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _) = 𝟙 _ := by
    intro j
    apply eq_of_toDescentData_faithful (fun i ↦ pullback.snd (f i) (g j))
    intro i
    apply map_eq_map_of_pullHom_eq (pullback.snd (f i) (g j)) (pullback.snd (f i) (g j))
      (pullback.snd (f i) (g j)) (Category.comp_id _) (Category.comp_id _)
    rw [pullHom_pullHom, pullHom_id_eq_id,
      hψ j j i (𝟙 _) (𝟙 _) (pullback.fst (f i) (g j)) (Category.id_comp _) (Category.id_comp _) _
        (pullback.snd (f i) (g j)) (pullback.snd (f i) (g j))
        (by rw [Category.assoc, pullback.lift_fst, Category.comp_id])
        (by rw [Category.assoc, pullback.lift_snd, Category.comp_id])
        (Category.id_comp _) (Category.id_comp _),
      pullHom_id, pullHom_id, hαα']
  let w₁₃ : ∀ j k l, pullback (pullback.snd (g j) (g k)) (pullback.fst (g k) (g l)) ⟶
      pullback (g j) (g l) := fun j k l ↦
    pullback.lift (tripleProj₁ g j k l) (tripleProj₃ g j k l) (tripleProj₃_comp g j k l).symm
  have hE1 : ∀ j k l, pullHom (ψ j k) (pullback.fst _ _) (tripleProj₁ g j k l)
        (tripleProj₂ g j k l) rfl rfl ≫
        pullHom (ψ k l) (pullback.snd _ _) (tripleProj₂ g j k l) (tripleProj₃ g j k l)
          pullback.condition.symm rfl =
      pullHom (ψ j l) (w₁₃ j k l) (tripleProj₁ g j k l) (tripleProj₃ g j k l)
        (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _) := by
    intro j k l
    apply hZZZ j k l (G j) (G l)
    intro i
    let u := pullback.snd (f i) (tripleProj₁ g j k l ≫ g j)
    apply map_eq_map_of_pullHom_eq u (u ≫ tripleProj₁ g j k l) (u ≫ tripleProj₃ g j k l) rfl rfl
    have hc : ∀ (m : κ) (k' : pullback (pullback.snd (g j) (g k)) (pullback.fst (g k) (g l)) ⟶
        Z m), k' ≫ g m = tripleProj₁ g j k l ≫ g j →
        pullback.fst (f i) (tripleProj₁ g j k l ≫ g j) ≫ f i = (u ≫ k') ≫ g m :=
      fun m k' hk ↦
        pullback.condition.trans ((congrArg (u ≫ ·) hk.symm).trans (Category.assoc _ _ _).symm)
    let e' : ∀ (m : κ) (k' : pullback (pullback.snd (g j) (g k)) (pullback.fst (g k) (g l)) ⟶
        Z m), k' ≫ g m = tripleProj₁ g j k l ≫ g j →
        (pullback (f i) (tripleProj₁ g j k l ≫ g j) ⟶ pullback (f i) (g m)) :=
      fun m k' hk ↦ pullback.lift (pullback.fst _ _) (u ≫ k') (hc m k' hk)
    have hk₁ : ∀ m k' hk, e' m k' hk ≫ pullback.fst (f i) (g m) = pullback.fst _ _ :=
      fun _ _ _ ↦ pullback.lift_fst _ _ _
    have hk₂ : ∀ m k' hk, e' m k' hk ≫ pullback.snd (f i) (g m) = u ≫ k' :=
      fun _ _ _ ↦ pullback.lift_snd _ _ _
    rw [pullHom_comp _ _ u _ (u ≫ tripleProj₂ g j k l) _ rfl rfl rfl, pullHom_pullHom,
      pullHom_pullHom, pullHom_pullHom,
      hψ j k i _ _ _ (hk₁ j _ rfl) (hk₁ k _ (tripleProj₂_comp g j k l)) (u ≫ pullback.fst _ _) _ _
        (Category.assoc _ _ _) (Category.assoc _ _ _) (hk₂ j _ rfl)
        (hk₂ k _ (tripleProj₂_comp g j k l)),
      hψ k l i _ _ _ (hk₁ k _ (tripleProj₂_comp g j k l)) (hk₁ l _ (tripleProj₃_comp g j k l))
        (u ≫ pullback.snd _ _) _ _
        ((Category.assoc _ _ _).trans (congrArg (u ≫ ·) pullback.condition.symm))
        (Category.assoc _ _ _) (hk₂ k _ (tripleProj₂_comp g j k l))
        (hk₂ l _ (tripleProj₃_comp g j k l)),
      hψ j l i _ _ _ (hk₁ j _ rfl) (hk₁ l _ (tripleProj₃_comp g j k l)) (u ≫ w₁₃ j k l) _ _
        ((Category.assoc _ _ _).trans (congrArg (u ≫ ·) (pullback.lift_fst _ _ _)))
        ((Category.assoc _ _ _).trans (congrArg (u ≫ ·) (pullback.lift_snd _ _ _)))
        (hk₂ j _ rfl) (hk₂ l _ (tripleProj₃_comp g j k l))]
    simp only [Category.assoc]
    rw [← pullHom_comp_assoc, hα'α, pullHom_id_eq_id, Category.id_comp]
  let E : F.DescentData g :=
    { obj := G
      hom := fun T q j₁ j₂ z₁ z₂ hz₁ hz₂ ↦ pullHom (ψ j₁ j₂)
        (pullback.lift (f := g j₁) (g := g j₂) z₁ z₂ (hz₁.trans hz₂.symm))
        z₁ z₂ (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)
      pullHom_hom := by
        intro Y' Y g' q q' hq j₁ j₂ z₁ z₂ hz₁ hz₂ gz₁ gz₂ hgz₁ hgz₂
        rw [pullHom_pullHom]
        refine pullHom_congr (ψ j₁ j₂) ?_ _ _ _ _
        apply pullback.hom_ext
        · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, hgz₁]
        · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, hgz₂]
      hom_self := by
        intro T q j z hz
        have : pullback.lift (f := g j) (g := g j) z z rfl =
            z ≫ pullback.lift (𝟙 (Z j)) (𝟙 (Z j)) rfl := by
          apply pullback.hom_ext
          · rw [pullback.lift_fst, Category.assoc, pullback.lift_fst, Category.comp_id]
          · rw [pullback.lift_snd, Category.assoc, pullback.lift_snd, Category.comp_id]
        rw [pullHom_congr (ψ j j) this, ← pullHom_pullHom (ψ j j) _ (𝟙 (Z j)) (𝟙 (Z j)) z z z
          (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _) (Category.comp_id _)
          (Category.comp_id _), hE0, pullHom_id_eq_id]
      hom_comp := by
        intro T q j k l z₁ z₂ z₃ hz₁ hz₂ hz₃
        obtain ⟨ℓ, hℓa, hℓb⟩ : ∃ ℓ : T ⟶ pullback (pullback.snd (g j) (g k))
              (pullback.fst (g k) (g l)),
            ℓ ≫ pullback.fst _ _ =
              pullback.lift (f := g j) (g := g k) z₁ z₂ (hz₁.trans hz₂.symm) ∧
            ℓ ≫ pullback.snd _ _ =
              pullback.lift (f := g k) (g := g l) z₂ z₃ (hz₂.trans hz₃.symm) :=
          ⟨pullback.lift _ _ (by rw [pullback.lift_snd, pullback.lift_fst]),
            pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
        have hℓ₁ : ℓ ≫ tripleProj₁ g j k l = z₁ := by
          change ℓ ≫ (pullback.fst _ _ ≫ pullback.fst (g j) (g k)) = z₁
          rw [← Category.assoc, hℓa, pullback.lift_fst]
        have hℓ₂ : ℓ ≫ tripleProj₂ g j k l = z₂ := by
          change ℓ ≫ (pullback.fst _ _ ≫ pullback.snd (g j) (g k)) = z₂
          rw [← Category.assoc, hℓa, pullback.lift_snd]
        have hℓ₃ : ℓ ≫ tripleProj₃ g j k l = z₃ := by
          change ℓ ≫ (pullback.snd _ _ ≫ pullback.snd (g k) (g l)) = z₃
          rw [← Category.assoc, hℓb, pullback.lift_snd]
        have e₁₃ : pullback.lift (f := g j) (g := g l) z₁ z₃ (hz₁.trans hz₃.symm) =
            ℓ ≫ w₁₃ j k l := by
          apply pullback.hom_ext
          · rw [pullback.lift_fst, Category.assoc, pullback.lift_fst, hℓ₁]
          · rw [pullback.lift_snd, Category.assoc, pullback.lift_snd, hℓ₃]
        rw [pullHom_congr (ψ j k) hℓa.symm, pullHom_congr (ψ k l) hℓb.symm,
          pullHom_congr (ψ j l) e₁₃,
          ← pullHom_pullHom (ψ j k) _ (tripleProj₁ g j k l) (tripleProj₂ g j k l) ℓ z₁ z₂ rfl rfl
            hℓ₁ hℓ₂,
          ← pullHom_pullHom (ψ k l) _ (tripleProj₂ g j k l) (tripleProj₃ g j k l) ℓ z₂ z₃
            pullback.condition.symm rfl hℓ₂ hℓ₃,
          ← pullHom_pullHom (ψ j l) _ (tripleProj₁ g j k l) (tripleProj₃ g j k l) ℓ z₁ z₃
            (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _) hℓ₁ hℓ₃,
          ← pullHom_comp, hE1] }
  -- The object of `Y` it descends to.
  let M := (F.toDescentData g).objPreimage E
  let β := (F.toDescentData g).objObjPreimageIso E
  -- Both descent data restrict to isomorphic descent data along `X i ×_Y Z j ⟶ Y`.
  let h : ∀ p : ι × κ, pullback (f p.1) (g p.2) ⟶ Y :=
    fun p ↦ pullback.fst (f p.1) (g p.2) ≫ f p.1
  have wf : ∀ p : ι × κ, pullback.fst (f p.1) (g p.2) ≫ f p.1 = h p ≫ 𝟙 Y :=
    fun p ↦ (Category.comp_id _).symm
  have wg : ∀ p : ι × κ, pullback.snd (f p.1) (g p.2) ≫ g p.2 = h p ≫ 𝟙 Y :=
    fun p ↦ pullback.condition.symm.trans (Category.comp_id _).symm
  let P := DescentData.pullFunctor F (f := f) (f' := h) (p := 𝟙 Y) (α := fun p ↦ p.1)
    (p' := fun p ↦ pullback.fst (f p.1) (g p.2)) wf
  let Q := DescentData.pullFunctor F (f := g) (f' := h) (p := 𝟙 Y)
    (α := fun p ↦ p.2) (p' := fun p ↦ pullback.snd (f p.1) (g p.2)) wg
  have hcomm : ∀ ⦃T : C⦄ (p₁ p₂ : ι × κ) (t₁ : T ⟶ pullback (f p₁.1) (g p₁.2))
      (t₂ : T ⟶ pullback (f p₂.1) (g p₂.2)) (q : T ⟶ Y) (h₁ : t₁ ≫ h p₁ = q)
      (h₂ : t₂ ≫ h p₂ = q),
      (F.map t₁.op.toLoc).toFunctor.map (α p₁.1 p₁.2) ≫
          DescentData.pullFunctorObjHom (ι' := ι × κ) (X' := fun p ↦ pullback (f p.1) (g p.2))
            (f' := h) (α := fun p ↦ p.1) (p' := fun p ↦ pullback.fst (f p.1) (g p.2))
            wf D (t₁ ≫ h p₁) t₁ t₂ rfl (h₂.trans h₁.symm) =
        DescentData.pullFunctorObjHom (ι' := ι × κ) (X' := fun p ↦ pullback (f p.1) (g p.2))
            (f' := h) (α := fun p ↦ p.2) (p' := fun p ↦ pullback.snd (f p.1) (g p.2))
            wg E (t₁ ≫ h p₁) t₁ t₂ rfl (h₂.trans h₁.symm) ≫
          (F.map t₂.op.toLoc).toFunctor.map (α p₂.1 p₂.2) := by
    rintro T ⟨i₁, j₁⟩ ⟨i₂, j₂⟩ t₁ t₂ q h₁ h₂
    have hx : (t₁ ≫ pullback.fst (f i₁) (g j₁)) ≫ f i₁ =
        (t₂ ≫ pullback.snd (f i₂) (g j₂)) ≫ g j₂ := by
      rw [Category.assoc, Category.assoc, ← pullback.condition]
      exact h₁.trans h₂.symm
    obtain ⟨e₂, he₂a, he₂s⟩ : ∃ e₂ : T ⟶ pullback (f i₁) (g j₂),
        e₂ ≫ pullback.fst _ _ = t₁ ≫ pullback.fst _ _ ∧
          e₂ ≫ pullback.snd _ _ = t₂ ≫ pullback.snd _ _ :=
      ⟨pullback.lift _ _ hx, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
    have hz₁ : (t₁ ≫ pullback.snd (f i₁) (g j₁)) ≫ g j₁ = t₁ ≫ h (i₁, j₁) := by
      rw [Category.assoc, ← pullback.condition, ← Category.assoc]
    have hz₂ : (t₂ ≫ pullback.snd (f i₂) (g j₂)) ≫ g j₂ = t₁ ≫ h (i₁, j₁) := by
      rw [Category.assoc, ← pullback.condition]
      exact h₂.trans h₁.symm
    have hEq : DescentData.pullFunctorObjHom (ι' := ι × κ)
        (X' := fun p ↦ pullback (f p.1) (g p.2)) (f' := h) (α := fun p ↦ p.2)
        (p' := fun p ↦ pullback.snd (f p.1) (g p.2))
        wg E (t₁ ≫ h (i₁, j₁)) t₁ t₂ rfl (h₂.trans h₁.symm) =
        (F.mapComp' (pullback.snd (f i₁) (g j₁)).op.toLoc t₁.op.toLoc
            (t₁ ≫ pullback.snd (f i₁) (g j₁)).op.toLoc (by
              rw [← Quiver.Hom.comp_toLoc, ← op_comp])).inv.toNatTrans.app (G j₁) ≫
          pullHom (ψ j₁ j₂) (pullback.lift (f := g j₁) (g := g j₂) (t₁ ≫ pullback.snd _ _)
            (t₂ ≫ pullback.snd _ _) (hz₁.trans hz₂.symm)) (t₁ ≫ pullback.snd _ _)
            (t₂ ≫ pullback.snd _ _) (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _) ≫
          (F.mapComp' (pullback.snd (f i₂) (g j₂)).op.toLoc t₂.op.toLoc
            (t₂ ≫ pullback.snd (f i₂) (g j₂)).op.toLoc (by
              rw [← Quiver.Hom.comp_toLoc, ← op_comp])).hom.toNatTrans.app (G j₂) := by
      rw [DescentData.pullFunctorObjHom_eq (ι' := ι × κ)
        (X' := fun p ↦ pullback (f p.1) (g p.2)) (f' := h) (α := fun p ↦ p.2)
        (p' := fun p ↦ pullback.snd (f p.1) (g p.2)) wg E
        (t₁ ≫ h (i₁, j₁)) t₁ t₂ (t₁ ≫ h (i₁, j₁)) (t₁ ≫ pullback.snd _ _)
        (t₂ ≫ pullback.snd _ _) rfl (h₂.trans h₁.symm) (Category.comp_id _) rfl rfl]
    rw [DescentData.pullFunctorObjHom_eq (ι' := ι × κ)
        (X' := fun p ↦ pullback (f p.1) (g p.2)) (f' := h) (α := fun p ↦ p.1)
        (p' := fun p ↦ pullback.fst (f p.1) (g p.2)) wf D
        (t₁ ≫ h (i₁, j₁)) t₁ t₂ (t₁ ≫ h (i₁, j₁)) (t₁ ≫ pullback.fst _ _)
        (t₂ ≫ pullback.fst _ _) rfl (h₂.trans h₁.symm) (Category.comp_id _) rfl rfl, hEq,
      map_eq_pullHom (α i₁ j₁) t₁ (t₁ ≫ pullback.snd _ _) (t₁ ≫ pullback.fst _ _) rfl rfl,
      map_eq_pullHom (α i₂ j₂) t₂ (t₂ ≫ pullback.snd _ _) (t₂ ≫ pullback.fst _ _) rfl rfl,
      hψ j₁ j₂ i₁ t₁ e₂ (t₁ ≫ pullback.fst _ _) rfl he₂a _ _ _ (pullback.lift_fst _ _ _)
        (pullback.lift_snd _ _ _) rfl he₂s,
      ← hα' j₂ i₁ i₂ e₂ t₂ (t₂ ≫ pullback.snd _ _) he₂s rfl (t₁ ≫ pullback.fst _ _)
        (t₂ ≫ pullback.fst _ _) he₂a rfl (t₁ ≫ h (i₁, j₁)) hz₂]
    have hinv : pullHom (α' i₂ j₂) t₂ (t₂ ≫ pullback.fst _ _) (t₂ ≫ pullback.snd _ _) rfl rfl ≫
        pullHom (α i₂ j₂) t₂ (t₂ ≫ pullback.snd _ _) (t₂ ≫ pullback.fst _ _) rfl rfl = 𝟙 _ := by
      rw [← pullHom_comp, hα'α, pullHom_id_eq_id]
    simp only [Category.assoc, Cat.Hom.hom_inv_id_toNatTrans_app_assoc, reassoc_of% hinv]
  let ι' : Q.obj E ≅ P.obj D := DescentData.isoMk
    (fun p ↦ Iso.mk (α p.1 p.2) (α' p.1 p.2) (hαα' p.1 p.2) (hα'α p.1 p.2))
    (fun T q p₁ p₂ t₁ t₂ h₁ h₂ ↦ hcomm p₁ p₂ t₁ t₂ q h₁ h₂)
  -- The refinement functor `P` is fully faithful.
  have H₃ : ∀ (D₁ D₂ : F.DescentData f) (i : ι),
      Presieve.IsSheafFor (F.presheafHom (D₁.obj i) (D₂.obj i))
        (DescentData.refSieve h (𝟙 (X i)) (f i)).arrows := by
    intro D₁ D₂ i
    have hpre : F.IsPrestackFor (Sieve.pullback (f i) (Sieve.ofArrows _ h)).arrows := by
      rw [sieve_pullback_ofArrows_baseChange f g (f i) i (𝟙 _) (Category.id_comp _),
        Sieve.ofArrows, IsPrestackFor_generate_iff, isPrestackFor_ofArrows_iff]
      exact hgT (f i)
    exact (F.isPrestackFor_iff_isSheafFor' _).1 hpre _ _ (𝟙 _)
  have H₄ : ∀ (D₁ D₂ : F.DescentData f) (i₁ i₂ : ι),
      Presieve.IsSeparatedFor (F.presheafHom (D₁.obj i₁) (D₂.obj i₁))
        (DescentData.refSieve h (ChosenPullback.ofHasPullback (f i₁) (f i₂)).p₁
          (ChosenPullback.ofHasPullback (f i₁) (f i₂)).p).arrows := by
    intro D₁ D₂ i₁ i₂
    have := (hgT (ChosenPullback.ofHasPullback (f i₁) (f i₂)).p).some.faithful
    have hsep := isSeparatedFor_presheafHom_of_faithful (F := F)
      (fun j ↦ pullback.fst (ChosenPullback.ofHasPullback (f i₁) (f i₂)).p (g j))
      (ChosenPullback.ofHasPullback (f i₁) (f i₂)).p₁ (D₁.obj i₁) (D₂.obj i₁)
    rwa [← sieve_pullback_ofArrows_baseChange f g _ i₁
      (ChosenPullback.ofHasPullback (f i₁) (f i₂)).p₁
      (ChosenPullback.ofHasPullback (f i₁) (f i₂)).hp₁] at hsep
  obtain ⟨hP⟩ := DescentData.nonempty_fullyFaithful_pullFunctor (F := F) (f := f) (f' := h)
    (α := fun p ↦ p.1) (p' := fun p ↦ pullback.fst (f p.1) (g p.2)) (fun p ↦ rfl) H₃
    (fun i₁ i₂ ↦ ChosenPullback.ofHasPullback (f i₁) (f i₂)) H₄
  let eP : F.toDescentData f ⋙ P ≅ F.toDescentData h :=
    DescentData.toDescentDataCompPullFunctorIso _ _ ≪≫
      Functor.isoWhiskerRight (Cat.Hom.toNatIso (F.mapId _)) _ ≪≫ Functor.leftUnitor _
  let eQ : F.toDescentData g ⋙ Q ≅ F.toDescentData h :=
    DescentData.toDescentDataCompPullFunctorIso _ _ ≪≫
      Functor.isoWhiskerRight (Cat.Hom.toNatIso (F.mapId _)) _ ≪≫ Functor.leftUnitor _
  exact ⟨M, ⟨hP.preimageIso (eP.app M ≪≫ (eQ.app M).symm ≪≫ Q.mapIso β ≪≫ ι')⟩⟩

end BaseChange

end Pseudofunctor

end CategoryTheory
