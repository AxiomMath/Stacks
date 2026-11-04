module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EventualFinitenessUniverse.Basic
public import StacksFrontier.AlgebraicGeometry.Limits.EventuallyAffine

/-!
# Closed immersions over the base descend to a finite stage

Let `D` be a cofiltered diagram of quasi-compact and quasi-separated schemes whose transition
morphisms are closed immersions, let `S` be a quasi-compact and quasi-separated scheme, and let
`t : D ⟶ (Functor.const _).obj S` exhibit every stage as an `S`-scheme with `t.app i` locally of
finite type. If the induced morphism `lim D ⟶ S` is a closed immersion, then `t.app i` is a
closed immersion for every sufficiently late stage `i`.

This is [Stacks, Tag 0A0N]. Closed-immersion transition morphisms are affine, so the source's
separate assumption that the transitions are affine is not needed here.

## Main results

* `AlgebraicGeometry.EventuallyClosedImmersion.isClosedImmersion_app_of_hom`: a closed immersion
  to `S` at one stage is a closed immersion to `S` at every later stage.
* `AlgebraicGeometry.exists_isClosedImmersion_app_of_isLimit` and
  `AlgebraicGeometry.eventually_isClosedImmersion_app_of_isLimit`: Tag 0A0N with the index
  category in the universe of the schemes.
* `AlgebraicGeometry.exists_isClosedImmersion_app_of_isLimit_of_initiallySmall` and
  `AlgebraicGeometry.eventually_isClosedImmersion_app_of_isLimit_of_initiallySmall`: Tag 0A0N
  with the index universes independent of the scheme universe, at the cost of
  `CategoryTheory.LocallySmall` and `CategoryTheory.InitiallySmall`. This is the faithful
  rendering and carries the attribute.
* `AlgebraicGeometry.exists_isClosedImmersion_app_of_isAffine_of_isLimit`,
  `AlgebraicGeometry.eventually_isClosedImmersion_app_of_isAffine_of_isLimit` and their
  `initiallySmall` forms: the affine case, which is what the proof reduces to.

## Implementation notes

The proof is the Stacks proof. Over one affine open `V` of `S` it is the algebra fact the source
reduces to: if `R → A_i` is of finite type, `A = colim A_i` with `R → A` surjective and all
transition maps `A_i → A_j` surjective, then `R → A_j` is surjective for some `j`. Pick
generators `x₁, …, x_m` of `A_i` over `R`; each has a preimage `r_k` in `R` for its image in `A`,
so `x_k - r_k` dies in `A` and therefore at some stage, by
`AlgebraicGeometry.exists_app_map_eq_zero_of_isLimit`; cofilteredness merges the finitely many
stages into one *through which all of them factor*
(`CategoryTheory.IsCofiltered.exists_hom_factor` — the factoring merge is needed, not just a
common predecessor, because the vanishing has to be transported along the merged morphism), and
at that stage `R` already hits a generating set, so it hits everything.

For this to apply, the inverse image of `V` must be an affine open at the stage, which is Tag
09ZM (`AlgebraicGeometry.exists_isAffineHom_app_of_isLimit`). `S` is quasi-compact, so finitely
many affine opens cover it, and cofilteredness merges the stages they produce; being a closed
immersion is local on the target
(`AlgebraicGeometry.IsClosedImmersion.isZariskiLocalAtTarget`), which finishes the proof.

The dictionary between "closed immersion" and "surjective on sections" is
`AlgebraicGeometry.IsClosedImmersion.of_surjective_of_isAffine`,
`AlgebraicGeometry.IsClosedImmersion.isAffine_surjective_of_isAffine` and
`AlgebraicGeometry.Scheme.Hom.app_surjective`; for "locally of finite type" it is
`AlgebraicGeometry.HasRingHomProperty.appLE`.

Transporting a section's vanishing from one stage to another changes the open it lives on, and
rewriting a morphism underneath `AlgebraicGeometry.Scheme.Hom.app` therefore has no type-correct
motive. Two devices avoid that without raising transparency: the morphism is generalised to a
free variable and substituted (`gen` inside
`AlgebraicGeometry.exists_app_surjective_of_isAffineOpen`), and the comparison with
`AlgebraicGeometry.morphismRestrict_appTop` is made in term mode, where no motive is formed.

## The index universe, and the smallness hypothesis

As for the sibling Tag 09ZM in `StacksDraft.AlgebraicGeometry.F3b.Limits.EventuallyAffine`, the
source's index is a directed *set*, so a form of these statements with the index carrying no
smallness condition relative to the scheme universe has dropped a hypothesis the source has, and
is false. The module documentation of that file exhibits the counterexample for 09ZM; the same
diagram refutes the smallness-free form of every "descends to a finite stage" statement in this
family, because what it breaks is the limit, not the property being descended — its limit is the
empty scheme, over which every morphism is a closed immersion, while no stage is.

Note the contrast with a statement that *constructs* a limit, such as
`AlgebraicGeometry.LimitNoetherianSituation.GoodDiagram.isLimit_imageCone` (Tag 0CNQ), which
needs no smallness at all: exhibiting a cone as limiting is not an eventual statement. A
consumer indexed by an arbitrary directed preorder therefore cannot apply the results below
without supplying the smallness, and that is not a defect of the statement.

## References

* [The Stacks Project, Tag 0A0N](https://stacks.math.columbia.edu/tag/0A0N)
* [The Stacks Project, Tag 09ZM](https://stacks.math.columbia.edu/tag/09ZM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.InitiallySmall

universe v uI u

namespace AlgebraicGeometry

namespace EventuallyClosedImmersion

variable {I : Type uI} [Category.{v} I] {S : Scheme.{u}} {D : I ⥤ Scheme.{u}}

/-- The structure morphism of a stage is a closed immersion as soon as it is one at some earlier
stage, provided the transition morphisms are closed immersions. -/
lemma isClosedImmersion_app_of_hom (t : D ⟶ (Functor.const I).obj S)
    [∀ {i j : I} (g : i ⟶ j), IsClosedImmersion (D.map g)] {i j : I}
    (g : j ⟶ i) (hi : IsClosedImmersion (t.app i : D.obj i ⟶ S)) :
    IsClosedImmersion (t.app j : D.obj j ⟶ S) := by
  have h : (t.app j : D.obj j ⟶ S) = D.map g ≫ (t.app i : D.obj i ⟶ S) := by simp
  rw [h]
  infer_instance

end EventuallyClosedImmersion

/-- Surjectivity of a morphism's sections over an open is carried along an equality of opens. -/
private lemma surjective_app_of_eq {X Y : Scheme.{u}} (f : X ⟶ Y) (U U' : Y.Opens) (h : U = U')
    (hU : Function.Surjective (f.app U).hom) : Function.Surjective (f.app U') := by
  subst h; exact hU

/-- Surjectivity of a morphism's sections over an open passes to the restriction of the morphism
to that open. Proved in term mode: the two spellings of the restricted morphism's codomain are
definitionally but not reducibly equal, so a rewrite here has no type-correct motive. -/
private lemma surjective_appTop_morphismRestrict {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens)
    (h : Function.Surjective (f.app U).hom) :
    Function.Surjective ((f ∣_ U).appTop) := by
  have h' : Function.Surjective (f.app (U.ι ''ᵁ ⊤)) :=
    surjective_app_of_eq f U _ (Scheme.Opens.ι_image_top U).symm h
  rw [morphismRestrict_appTop]
  intro y
  obtain ⟨z, hz⟩ := (ConcreteCategory.bijective_of_isIso
    (X.presheaf.map (eqToHom (image_morphismRestrict_preimage f U ⊤)).op)).2 y
  obtain ⟨w, hw⟩ := h' z
  exact ⟨w, (ConcreteCategory.comp_apply _ _ w).trans (by rw [hw]; exact hz)⟩

/-- Surjectivity on sections over `V` of a stage follows from surjectivity of its composite with
a transition map. -/
private lemma app_surjective_of_surjective_comp {I : Type uI} [Category.{v} I] {S : Scheme.{u}}
    (D : I ⥤ Scheme.{u}) (t : D ⟶ (Functor.const I).obj S) (V : S.Opens) {i j : I} (h : j ⟶ i)
    (hcs : Function.Surjective (((t.app i : D.obj i ⟶ S).app V ≫
      (D.map h).app ((t.app i : D.obj i ⟶ S) ⁻¹ᵁ V)).hom)) :
    Function.Surjective ((t.app j : D.obj j ⟶ S).app V).hom := by
  rw [Scheme.Hom.congr_app (show (t.app j : D.obj j ⟶ S)
    = D.map h ≫ (t.app i : D.obj i ⟶ S) by simp) V,
    CommRingCat.hom_comp, RingHom.coe_comp]
  exact (ConcreteCategory.bijective_of_isIso _).2.comp hcs

/-- Affineness of the structure morphism passes to a later stage. -/
private lemma isAffineHom_app_of_hom {I : Type uI} [Category.{v} I] {S : Scheme.{u}}
    (D : I ⥤ Scheme.{u}) (t : D ⟶ (Functor.const I).obj S)
    [∀ {i j : I} (g : i ⟶ j), IsClosedImmersion (D.map g)] {i j : I} (h : j ⟶ i)
    [IsAffineHom (t.app i : D.obj i ⟶ S)] : IsAffineHom (t.app j : D.obj j ⟶ S) := by
  rw [show (t.app j : D.obj j ⟶ S) = D.map h ≫ (t.app i : D.obj i ⟶ S) by simp]
  infer_instance

/-- Surjectivity on sections over an affine open of the base passes to a later stage. -/
private lemma app_surjective_of_hom {I : Type uI} [Category.{v} I] {S : Scheme.{u}}
    (D : I ⥤ Scheme.{u}) (t : D ⟶ (Functor.const I).obj S)
    [∀ {i j : I} (g : i ⟶ j), IsClosedImmersion (D.map g)]
    (V : S.Opens) (hV : IsAffineOpen V) {i j : I} (h : j ⟶ i)
    [IsAffineHom (t.app i : D.obj i ⟶ S)]
    (hi : Function.Surjective ((t.app i : D.obj i ⟶ S).app V).hom) :
    Function.Surjective ((t.app j : D.obj j ⟶ S).app V).hom := by
  refine app_surjective_of_surjective_comp D t V h ?_
  rw [CommRingCat.hom_comp, RingHom.coe_comp]
  exact ((D.map h).app_surjective _ (hV.preimage (t.app i : D.obj i ⟶ S))).comp hi

section Small

variable {I : Type u} [Category.{u} I] [IsCofiltered I] {S : Scheme.{u}}

/-- **The algebra step of Stacks Tag 0A0N, over one affine open of the base.** If the structure
morphism is affine and locally of finite type at the stage `i₁` and a closed immersion at the
limit, then at some later stage it is surjective on sections over the affine open `V`. -/
private lemma exists_app_surjective_of_isAffineOpen (D : I ⥤ Scheme.{u})
    (t : D ⟶ (Functor.const I).obj S) (c : Cone D) (hc : IsLimit c) (f : c.pt ⟶ S)
    (hf : c.π ≫ t = (Functor.const I).map f)
    [∀ {i j : I} (g : i ⟶ j), IsClosedImmersion (D.map g)] [IsClosedImmersion f]
    (i₁ : I) [IsAffineHom (t.app i₁ : D.obj i₁ ⟶ S)]
    [LocallyOfFiniteType (t.app i₁ : D.obj i₁ ⟶ S)]
    (V : S.Opens) (hV : IsAffineOpen V) :
    ∃ (j : I) (_ : j ⟶ i₁),
      Function.Surjective ((t.app j : D.obj j ⟶ S).app V).hom := by
  classical
  have haff : ∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g) := fun g ↦ inferInstance
  have hπ : c.π.app i₁ ≫ (t.app i₁ : D.obj i₁ ⟶ S) = f := by
    simpa using NatTrans.congr_app hf i₁
  have hU : IsAffineOpen ((t.app i₁ : D.obj i₁ ⟶ S) ⁻¹ᵁ V) :=
    hV.preimage (t.app i₁ : D.obj i₁ ⟶ S)
  -- `Γ(D.obj i₁, U)` is of finite type over `Γ(S, V)`, with generators `s`.
  let alg : Algebra Γ(S, V) Γ(D.obj i₁, (t.app i₁ : D.obj i₁ ⟶ S) ⁻¹ᵁ V) :=
    ((t.app i₁ : D.obj i₁ ⟶ S).app V).hom.toAlgebra
  have halg : algebraMap Γ(S, V) Γ(D.obj i₁, (t.app i₁ : D.obj i₁ ⟶ S) ⁻¹ᵁ V)
      = ((t.app i₁ : D.obj i₁ ⟶ S).app V).hom := rfl
  have hft : RingHom.FiniteType ((t.app i₁ : D.obj i₁ ⟶ S).app V).hom := by
    have h := HasRingHomProperty.appLE (P := @LocallyOfFiniteType)
      (f := (t.app i₁ : D.obj i₁ ⟶ S)) inferInstance ⟨V, hV⟩ ⟨_, hU⟩ le_rfl
    rwa [← Scheme.Hom.app_eq_appLE] at h
  obtain ⟨s, hs⟩ : ∃ s : Finset Γ(D.obj i₁, (t.app i₁ : D.obj i₁ ⟶ S) ⁻¹ᵁ V),
      Algebra.adjoin Γ(S, V) (s : Set Γ(D.obj i₁, (t.app i₁ : D.obj i₁ ⟶ S) ⁻¹ᵁ V)) = ⊤ :=
    hft.out
  -- Sections over `V` pulled back to the limit through the stage `i₁` hit everything.
  have hcomp : (t.app i₁ : D.obj i₁ ⟶ S).app V ≫
      (c.π.app i₁).app ((t.app i₁ : D.obj i₁ ⟶ S) ⁻¹ᵁ V)
      = f.app V ≫ c.pt.presheaf.map
        (eqToHom (by rw [← Scheme.Hom.comp_preimage, hπ])).op :=
    Scheme.Hom.congr_app hπ V
  have hsurjmid : Function.Surjective
      ((t.app i₁ : D.obj i₁ ⟶ S).app V ≫
        (c.π.app i₁).app ((t.app i₁ : D.obj i₁ ⟶ S) ⁻¹ᵁ V)).hom := by
    rw [hcomp, CommRingCat.hom_comp, RingHom.coe_comp]
    exact (ConcreteCategory.bijective_of_isIso _).2.comp (f.app_surjective V hV)
  -- Each section of `U` agrees, at some stage, with one pulled back from `V`.
  have key : ∀ x : Γ(D.obj i₁, (t.app i₁ : D.obj i₁ ⟶ S) ⁻¹ᵁ V),
      ∃ (j : I) (g : j ⟶ i₁) (r : Γ(S, V)),
        ((D.map g).app ((t.app i₁ : D.obj i₁ ⟶ S) ⁻¹ᵁ V)).hom
          (x - ((t.app i₁ : D.obj i₁ ⟶ S).app V).hom r) = 0 := by
    intro x
    obtain ⟨r, hr⟩ := hsurjmid
      (((c.π.app i₁).app ((t.app i₁ : D.obj i₁ ⟶ S) ⁻¹ᵁ V)).hom x)
    rw [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at hr
    obtain ⟨j, g, hg⟩ := exists_app_map_eq_zero_of_isLimit D c hc hU.isCompact
      (x - ((t.app i₁ : D.obj i₁ ⟶ S).app V).hom r) (by rw [map_sub, hr, sub_self])
    exact ⟨j, g, r, hg⟩
  choose jx gx rx hzx using key
  obtain ⟨k, g, hgf⟩ := IsCofiltered.exists_hom_factor
    (fun x : Γ(D.obj i₁, (t.app i₁ : D.obj i₁ ⟶ S) ⁻¹ᵁ V) ↦ gx x) s
  refine ⟨k, g, ?_⟩
  -- Transport each generator's vanishing discrepancy to the merged stage `k`.
  have hvanish : ∀ x ∈ s, ((D.map g).app ((t.app i₁ : D.obj i₁ ⟶ S) ⁻¹ᵁ V)).hom
      (x - ((t.app i₁ : D.obj i₁ ⟶ S).app V).hom (rx x)) = 0 := by
    intro x hx
    obtain ⟨h, hh⟩ := hgf x hx
    have gen : ∀ m : D.obj k ⟶ D.obj i₁, m = D.map h ≫ D.map (gx x) →
        (m.app ((t.app i₁ : D.obj i₁ ⟶ S) ⁻¹ᵁ V)).hom
          (x - ((t.app i₁ : D.obj i₁ ⟶ S).app V).hom (rx x)) = 0 := by
      intro m hm
      subst hm
      -- Stated and closed at the nested spelling, then transferred by `exact`: a rewrite
      -- underneath `Scheme.Hom.app` has no type-correct motive, and term mode forms none.
      have hnest : ((D.map h).app (D.map (gx x) ⁻¹ᵁ (t.app i₁ : D.obj i₁ ⟶ S) ⁻¹ᵁ V)).hom
          (((D.map (gx x)).app ((t.app i₁ : D.obj i₁ ⟶ S) ⁻¹ᵁ V)).hom
            (x - ((t.app i₁ : D.obj i₁ ⟶ S).app V).hom (rx x))) = 0 := by
        rw [hzx x, map_zero]
      exact hnest
    exact gen _ (by rw [hh, D.map_comp])
  have main : ∀ b ∈ Algebra.adjoin Γ(S, V)
      (s : Set Γ(D.obj i₁, (t.app i₁ : D.obj i₁ ⟶ S) ⁻¹ᵁ V)),
      ∃ r : Γ(S, V),
        ((t.app i₁ : D.obj i₁ ⟶ S).app V ≫
            (D.map g).app ((t.app i₁ : D.obj i₁ ⟶ S) ⁻¹ᵁ V)).hom r
          = ((D.map g).app ((t.app i₁ : D.obj i₁ ⟶ S) ⁻¹ᵁ V)).hom b := by
    intro b hb
    induction hb using Algebra.adjoin_induction with
    | mem x hx =>
        refine ⟨rx x, ?_⟩
        have h0 := hvanish x hx
        rw [map_sub, sub_eq_zero] at h0
        rw [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply]
        exact h0.symm
    | algebraMap r =>
        refine ⟨r, ?_⟩
        rw [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, halg]
    | add x y _ _ px py =>
        obtain ⟨r₁, h₁⟩ := px
        obtain ⟨r₂, h₂⟩ := py
        exact ⟨r₁ + r₂, by rw [map_add, map_add, h₁, h₂]⟩
    | mul x y _ _ px py =>
        obtain ⟨r₁, h₁⟩ := px
        obtain ⟨r₂, h₂⟩ := py
        exact ⟨r₁ * r₂, by rw [map_mul, map_mul, h₁, h₂]⟩
  have hsurjk : Function.Surjective
      ((t.app i₁ : D.obj i₁ ⟶ S).app V ≫
        (D.map g).app ((t.app i₁ : D.obj i₁ ⟶ S) ⁻¹ᵁ V)).hom := by
    intro a
    obtain ⟨b, rfl⟩ := (D.map g).app_surjective _ hU a
    exact main b (hs ▸ Algebra.mem_top)
  exact app_surjective_of_surjective_comp D t V g hsurjk

/-- **Stacks Tag 0A0N**, in the form "there is a stage at which the structure morphism is a
closed immersion". The index category lives in the universe of the schemes; see
`AlgebraicGeometry.exists_isClosedImmersion_app_of_isLimit_of_initiallySmall` for the version
with independent index universes, and the module documentation for why no condition at all on
the index category will do. -/
theorem exists_isClosedImmersion_app_of_isLimit (D : I ⥤ Scheme.{u})
    (t : D ⟶ (Functor.const I).obj S) (c : Cone D) (hc : IsLimit c) (f : c.pt ⟶ S)
    (hf : c.π ≫ t = (Functor.const I).map f)
    [CompactSpace S] [QuasiSeparatedSpace S]
    [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
    [∀ {i j : I} (g : i ⟶ j), IsClosedImmersion (D.map g)]
    [∀ i, LocallyOfFiniteType (t.app i : D.obj i ⟶ S)] [IsClosedImmersion f] :
    ∃ i : I, IsClosedImmersion (t.app i : D.obj i ⟶ S) := by
  classical
  have haff : ∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g) := fun g ↦ inferInstance
  -- Stacks 09ZM: at a late enough stage the structure morphism is affine.
  obtain ⟨i₁, hi₁⟩ := exists_isAffineHom_app_of_isLimit D t c hc f hf
  have hi₁' : IsAffineHom (t.app i₁ : D.obj i₁ ⟶ S) := hi₁
  -- A finite cover of `S` by affine opens.
  have hmem : ∀ x : S, ∃ V : S.affineOpens, x ∈ (V : Set S) := fun x ↦ by
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
      S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    exact ⟨⟨V, hV⟩, hxV⟩
  obtain ⟨σ, hσ⟩ := isCompact_univ.elim_finite_subcover
    (fun V : S.affineOpens ↦ (V : Set S)) (fun V ↦ V.1.2)
    fun x _ ↦ Set.mem_iUnion.2 (hmem x)
  -- A stage for each member of the cover, then one stage for all of them.
  have key : ∀ V : S.affineOpens, ∃ (j : I) (_ : j ⟶ i₁),
      Function.Surjective ((t.app j : D.obj j ⟶ S).app (V : S.Opens)).hom :=
    fun V ↦ exists_app_surjective_of_isAffineOpen D t c hc f hf i₁ (V : S.Opens) V.2
  choose jx gx hjx using key
  obtain ⟨k, hk⟩ := IsCofiltered.inf_objs_exists (insert i₁ (σ.image jx))
  have hki₁ : k ⟶ i₁ := (hk (Finset.mem_insert_self _ _)).some
  have hkj : ∀ V ∈ σ, k ⟶ jx V := fun V hV ↦
    (hk (Finset.mem_insert_of_mem (Finset.mem_image_of_mem jx hV))).some
  have hkaff : IsAffineHom (t.app k : D.obj k ⟶ S) := isAffineHom_app_of_hom D t hki₁
  have hsurj : ∀ V ∈ σ,
      Function.Surjective ((t.app k : D.obj k ⟶ S).app (V : S.Opens)).hom := by
    intro V hV
    have := isAffineHom_app_of_hom D t (gx V)
    exact app_surjective_of_hom D t (V : S.Opens) V.2 (hkj V hV) (hjx V)
  -- Being a closed immersion is local on the target.
  have hcover : ⨆ V : σ, ((V : S.affineOpens) : S.Opens) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    obtain ⟨V, hVσ, hxV⟩ := Set.mem_iUnion₂.mp (hσ (Set.mem_univ x))
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨V, hVσ⟩, hxV⟩
  refine ⟨k, ?_⟩
  rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @IsClosedImmersion)
    (fun V : σ ↦ ((V : S.affineOpens) : S.Opens)) hcover]
  intro V
  have h₁ : IsAffine ((V : S.affineOpens) : S.Opens).toScheme := V.1.2
  have h₂ : IsAffine ((t.app k : D.obj k ⟶ S) ⁻¹ᵁ
      ((V : S.affineOpens) : S.Opens)).toScheme :=
    V.1.2.preimage (t.app k : D.obj k ⟶ S)
  refine IsClosedImmersion.of_surjective_of_isAffine _ ?_
  exact surjective_appTop_morphismRestrict _ _ (hsurj V.1 V.2)

/-- **Stacks Tag 0A0N.** Let `lim D` be a cofiltered limit of quasi-compact and quasi-separated
schemes over a quasi-compact and quasi-separated scheme `S`, with transition morphisms closed
immersions and structure morphisms locally of finite type. If `lim D ⟶ S` is a closed immersion,
then `D.obj j ⟶ S` is a closed immersion for every sufficiently late stage `j`.

The index category lives in the universe of the schemes; see
`AlgebraicGeometry.eventually_isClosedImmersion_app_of_isLimit_of_initiallySmall` for the version
with independent index universes, and the module documentation for why no condition at all on the
index category will do. -/
theorem eventually_isClosedImmersion_app_of_isLimit (D : I ⥤ Scheme.{u})
    (t : D ⟶ (Functor.const I).obj S) (c : Cone D) (hc : IsLimit c) (f : c.pt ⟶ S)
    (hf : c.π ≫ t = (Functor.const I).map f)
    [CompactSpace S] [QuasiSeparatedSpace S]
    [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
    [∀ {i j : I} (g : i ⟶ j), IsClosedImmersion (D.map g)]
    [∀ i, LocallyOfFiniteType (t.app i : D.obj i ⟶ S)] [IsClosedImmersion f] :
    ∃ i : I, ∀ {j : I} (_ : j ⟶ i), IsClosedImmersion (t.app j : D.obj j ⟶ S) := by
  obtain ⟨i, hi⟩ := exists_isClosedImmersion_app_of_isLimit D t c hc f hf
  exact ⟨i, fun g ↦ EventuallyClosedImmersion.isClosedImmersion_app_of_hom t g hi⟩

/-- The affine case of `AlgebraicGeometry.exists_isClosedImmersion_app_of_isLimit`, which is what
its proof reduces to. -/
theorem exists_isClosedImmersion_app_of_isAffine_of_isLimit (D : I ⥤ Scheme.{u})
    (t : D ⟶ (Functor.const I).obj S) (c : Cone D) (hc : IsLimit c) (f : c.pt ⟶ S)
    (hf : c.π ≫ t = (Functor.const I).map f)
    [IsAffine S] [∀ i, IsAffine (D.obj i)]
    [∀ {i j : I} (g : i ⟶ j), IsClosedImmersion (D.map g)]
    [∀ i, LocallyOfFiniteType (t.app i : D.obj i ⟶ S)] [IsClosedImmersion f] :
    ∃ i : I, IsClosedImmersion (t.app i : D.obj i ⟶ S) :=
  exists_isClosedImmersion_app_of_isLimit D t c hc f hf

/-- The affine case of `AlgebraicGeometry.eventually_isClosedImmersion_app_of_isLimit`. -/
theorem eventually_isClosedImmersion_app_of_isAffine_of_isLimit (D : I ⥤ Scheme.{u})
    (t : D ⟶ (Functor.const I).obj S) (c : Cone D) (hc : IsLimit c) (f : c.pt ⟶ S)
    (hf : c.π ≫ t = (Functor.const I).map f)
    [IsAffine S] [∀ i, IsAffine (D.obj i)]
    [∀ {i j : I} (g : i ⟶ j), IsClosedImmersion (D.map g)]
    [∀ i, LocallyOfFiniteType (t.app i : D.obj i ⟶ S)] [IsClosedImmersion f] :
    ∃ i : I, ∀ {j : I} (_ : j ⟶ i), IsClosedImmersion (t.app j : D.obj j ⟶ S) :=
  eventually_isClosedImmersion_app_of_isLimit D t c hc f hf

end Small

section InitiallySmall

variable {I : Type uI} [Category.{v} I] [IsCofiltered I]
  [LocallySmall.{u} I] [InitiallySmall.{u} I] {S : Scheme.{u}}

/-- `AlgebraicGeometry.exists_isClosedImmersion_app_of_isLimit` with the index universes
independent of the scheme universe, at the cost of `CategoryTheory.LocallySmall.{u}` and
`CategoryTheory.InitiallySmall.{u}` on the index category. See the module documentation for why
some such condition is necessary. -/
theorem exists_isClosedImmersion_app_of_isLimit_of_initiallySmall (D : I ⥤ Scheme.{u})
    (t : D ⟶ (Functor.const I).obj S) (c : Cone D) (hc : IsLimit c) (f : c.pt ⟶ S)
    (hf : c.π ≫ t = (Functor.const I).map f)
    [CompactSpace S] [QuasiSeparatedSpace S]
    [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
    [∀ {i j : I} (g : i ⟶ j), IsClosedImmersion (D.map g)]
    [∀ i, LocallyOfFiniteType (t.app i : D.obj i ⟶ S)] [IsClosedImmersion f] :
    ∃ i : I, IsClosedImmersion (t.app i : D.obj i ⟶ S) := by
  set A := CofilteredInitialModel.{u} I
  set φ : A ⥤ I := fromCofilteredInitialModel.{u} I with hφ
  let D' : A ⥤ Scheme.{u} := φ ⋙ D
  let t' : D' ⟶ (Functor.const A).obj S :=
    { app a := t.app (φ.obj a)
      naturality a b h := by simp [D'] }
  have h₁ : ∀ {a b : A} (h : a ⟶ b), IsClosedImmersion (D'.map h) := by
    intros; dsimp [D']; infer_instance
  have h₂ : ∀ a : A, CompactSpace (D'.obj a) := by intro a; dsimp [D']; infer_instance
  have h₃ : ∀ a : A, QuasiSeparatedSpace (D'.obj a) := by intro a; dsimp [D']; infer_instance
  have h₄ : ∀ a : A, LocallyOfFiniteType (t'.app a : D'.obj a ⟶ S) := by
    intro a; dsimp [D', t']; infer_instance
  have hc' : IsLimit (c.whisker φ) := (Functor.Initial.isLimitWhiskerEquiv φ c).symm hc
  have hf' : (c.whisker φ).π ≫ t' = (Functor.const A).map f := by
    ext a
    simpa [t'] using NatTrans.congr_app hf (φ.obj a)
  obtain ⟨a, ha⟩ := exists_isClosedImmersion_app_of_isLimit D' t' _ hc' f hf'
  exact ⟨φ.obj a, ha⟩

/-- `AlgebraicGeometry.eventually_isClosedImmersion_app_of_isLimit` with the index universes
independent of the scheme universe, at the cost of `CategoryTheory.LocallySmall.{u}` and
`CategoryTheory.InitiallySmall.{u}` on the index category.

This is the faithful rendering of Tag 0A0N: the source's limit is indexed by a directed set, so
the index is small relative to the schemes and the smallness is part of the statement rather than
an addition to it. See the module documentation, and compare
`AlgebraicGeometry.eventually_isAffineHom_of_isLimit_of_initiallySmall` (Tag 09ZM), which carries
the condition for the same reason and whose counterexample shows it cannot be dropped. -/
@[stacks 0A0N]
theorem eventually_isClosedImmersion_app_of_isLimit_of_initiallySmall (D : I ⥤ Scheme.{u})
    (t : D ⟶ (Functor.const I).obj S) (c : Cone D) (hc : IsLimit c) (f : c.pt ⟶ S)
    (hf : c.π ≫ t = (Functor.const I).map f)
    [CompactSpace S] [QuasiSeparatedSpace S]
    [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
    [∀ {i j : I} (g : i ⟶ j), IsClosedImmersion (D.map g)]
    [∀ i, LocallyOfFiniteType (t.app i : D.obj i ⟶ S)] [IsClosedImmersion f] :
    ∃ i : I, ∀ {j : I} (_ : j ⟶ i), IsClosedImmersion (t.app j : D.obj j ⟶ S) := by
  obtain ⟨i, hi⟩ := exists_isClosedImmersion_app_of_isLimit_of_initiallySmall D t c hc f hf
  exact ⟨i, fun g ↦ EventuallyClosedImmersion.isClosedImmersion_app_of_hom t g hi⟩

end InitiallySmall

section InitiallySmallAffine

variable {I : Type uI} [Category.{v} I] [IsCofiltered I]
  [LocallySmall.{u} I] [InitiallySmall.{u} I] {S : Scheme.{u}}

/-- The affine case of
`AlgebraicGeometry.exists_isClosedImmersion_app_of_isLimit_of_initiallySmall`. -/
theorem exists_isClosedImmersion_app_of_isAffine_of_isLimit_of_initiallySmall
    (D : I ⥤ Scheme.{u}) (t : D ⟶ (Functor.const I).obj S) (c : Cone D) (hc : IsLimit c)
    (f : c.pt ⟶ S) (hf : c.π ≫ t = (Functor.const I).map f)
    [IsAffine S] [∀ i, IsAffine (D.obj i)]
    [∀ {i j : I} (g : i ⟶ j), IsClosedImmersion (D.map g)]
    [∀ i, LocallyOfFiniteType (t.app i : D.obj i ⟶ S)] [IsClosedImmersion f] :
    ∃ i : I, IsClosedImmersion (t.app i : D.obj i ⟶ S) :=
  exists_isClosedImmersion_app_of_isLimit_of_initiallySmall D t c hc f hf

/-- The affine case of
`AlgebraicGeometry.eventually_isClosedImmersion_app_of_isLimit_of_initiallySmall`. -/
theorem eventually_isClosedImmersion_app_of_isAffine_of_isLimit_of_initiallySmall
    (D : I ⥤ Scheme.{u}) (t : D ⟶ (Functor.const I).obj S) (c : Cone D) (hc : IsLimit c)
    (f : c.pt ⟶ S) (hf : c.π ≫ t = (Functor.const I).map f)
    [IsAffine S] [∀ i, IsAffine (D.obj i)]
    [∀ {i j : I} (g : i ⟶ j), IsClosedImmersion (D.map g)]
    [∀ i, LocallyOfFiniteType (t.app i : D.obj i ⟶ S)] [IsClosedImmersion f] :
    ∃ i : I, ∀ {j : I} (_ : j ⟶ i), IsClosedImmersion (t.app j : D.obj j ⟶ S) :=
  eventually_isClosedImmersion_app_of_isLimit_of_initiallySmall D t c hc f hf

end InitiallySmallAffine

end AlgebraicGeometry

end
