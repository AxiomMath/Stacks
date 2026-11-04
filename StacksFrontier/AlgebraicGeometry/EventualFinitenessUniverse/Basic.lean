module

public import StacksFrontier.AlgebraicGeometry.EventualFiniteness.Basic
public import StacksFrontier.AlgebraicGeometry.LimitUniverse.AffineTransitionLimit

/-!
# Eventual finiteness in an inverse limit of schemes, at an independent index universe

Let `S` be a quasi-compact and quasi-separated scheme and let `X = lim Xᵢ` be a directed inverse
limit of quasi-compact and quasi-separated schemes over `S` whose transition morphisms are finite
and whose structure morphisms are locally of finite type.  If `X → S` is integral, then `Xᵢ → S`
is finite for all sufficiently large `i`.  This is [Stacks, Tag 09ZN].

`StacksFrontier/AlgebraicGeometry/EventualFiniteness/Basic.lean` proves this with the index type in
the *same* universe as the schemes, because every declaration of
`Mathlib.AlgebraicGeometry.AffineTransitionLimit` is stated for `I : Type u` with
`[Category.{u} I]` and `D : I ⥤ Scheme.{u}`.  This file removes that coupling, using the
universe-freed forms of Mathlib's results collected in
`StacksFrontier/AlgebraicGeometry/LimitUniverse/AffineTransitionLimit.lean`.

The index universe is freed at the cost of one hypothesis: `CategoryTheory.InitiallySmall.{u} Iᵒᵖ`,
which for a directed preorder `I` says that `I` has a `u`-small cofinal subset (see
`CategoryTheory.initiallySmall_iff_exists_small_weakly_initial_set`).  It is *automatic* whenever
`Small.{u} I`, in particular whenever `I : Type u`, so the statements below subsume the
merged-universe ones; see
`AlgebraicGeometry.eventually_isFinite_of_isLimit_of_isIntegral_of_small`. It is a genuine
restriction in general: `Ordinal.{u}` is a nonempty directed preorder no `u`-small subset of which
is cofinal, so `CategoryTheory.InitiallySmall.{u} (Ordinal.{u})ᵒᵖ` is false
(`CategoryTheory.not_initiallySmall_op_ordinal`).  Note that `CategoryTheory.LocallySmall.{u} Iᵒᵖ`,
the other hypothesis of the universe-freed limit API, *is* automatic for a preorder, by
`CategoryTheory.locallySmall_of_thin`; it bounds the hom types, which for a thin category are
`Prop`-like, whereas the hypothesis above bounds the index up to cofinality.  Of the three
candidate smallness hypotheses this is the weakest: both `Small.{u} I` (via
`CategoryTheory.initiallySmall_of_small_of_locallySmall`) and `EssentiallySmall.{u} I` (via
`CategoryTheory.initiallySmall_of_essentiallySmall`) imply it, and both also fail for
`Ordinal.{u}`.

## Main results

* `CategoryTheory.IsCofiltered.exists_hom_factor`: finitely many morphisms of a cofiltered
  category with a common target have a common factorisation.
* `CategoryTheory.not_initiallySmall_op_ordinal`: the extra hypothesis below is not vacuous.
* `AlgebraicGeometry.EventualFiniteness.exists_isAffineOpen_and_isIntegral_app_of_cofiltered`:
  the affine-base step of [Stacks, Tag 09ZN] for an index category that is *not* assumed thin.
* `AlgebraicGeometry.Scheme.exists_isFinite_app_of_isLimit_of_cofiltered`: some member of a
  cofiltered inverse system of qcqs schemes with finite transition morphisms, locally of finite
  type over a qcqs base, is finite over the base as soon as the limit is integral over the base.
  The index category is not assumed thin.
* `AlgebraicGeometry.Scheme.exists_isFinite_app_of_isLimit_of_initiallySmall`: the same with the
  index universes independent of the scheme universe.
* `AlgebraicGeometry.eventually_isFinite_of_isLimit_of_isIntegral_of_initiallySmall`: the
  directed-preorder form, phrased with `Filter.atTop`, with the index universe independent of the
  scheme universe.
* `AlgebraicGeometry.eventually_isFinite_of_isLimit_of_isIntegral_of_small`: the same under the
  simpler hypothesis `Small.{u} I`.

## Implementation notes

The reindexing is done once, at the top: the whole situation is transported along
`CategoryTheory.InitiallySmall.fromCofilteredInitialModel`, after which every index lives at the
scheme universe and the `Over`-indexed subdiagrams that Mathlib's proofs form internally are small
as well.  The small model produced by Mathlib is cofiltered but *not* thin — thinness is lost
behind the `Exists.choose` of `CategoryTheory.InitiallySmall.exists_of_isCofiltered` — so the
results of the F3 module cannot be applied to it directly.  The first two results below are
therefore the F3 results with `[Quiver.IsThin I]` dropped: where the F3 proof factors a morphism
through a prescribed one by `Subsingleton.elim`, the proofs here invoke
`CategoryTheory.IsCofiltered.exists_hom_factor`, which produces the factorisations from
cofilteredness alone.

## References

* [The Stacks Project, Tag 09ZN](https://stacks.math.columbia.edu/tag/09ZN)
-/

@[expose] public section

universe w v uI u

open CategoryTheory Limits CategoryTheory.InitiallySmall

namespace CategoryTheory.IsCofiltered

/-- In a cofiltered category, finitely many morphisms `gx x : jx x ⟶ j₀` with a common target
have a common factorisation: a single morphism `g : k ⟶ j₀` which factors through each of them.

For a thin category this is `Subsingleton.elim` applied to any morphism `k ⟶ j₀` out of a common
predecessor of the `jx x`, as produced by `CategoryTheory.IsCofiltered.inf_objs_exists`; in general
the factorisations have to be arranged, which is what the proof below does. -/
lemma exists_hom_factor {C : Type uI} [Category.{v} C] [IsCofiltered C] {ι : Type w} {j₀ : C}
    {jx : ι → C} (gx : ∀ x, jx x ⟶ j₀) (s : Finset ι) :
    ∃ (k : C) (g : k ⟶ j₀), ∀ x ∈ s, ∃ h : k ⟶ jx x, g = h ≫ gx x := by
  classical
  induction s using Finset.induction with
  | empty => exact ⟨j₀, 𝟙 j₀, by simp⟩
  | insert a s _ ih =>
    obtain ⟨k, g, hg⟩ := ih
    obtain ⟨n, e, he⟩ : ∃ (n : C) (e : n ⟶ IsCofiltered.min k (jx a)),
        e ≫ IsCofiltered.minToLeft k (jx a) ≫ g =
          e ≫ IsCofiltered.minToRight k (jx a) ≫ gx a :=
      ⟨_, IsCofiltered.eqHom _ _, IsCofiltered.eq_condition _ _⟩
    refine ⟨n, e ≫ IsCofiltered.minToLeft k (jx a) ≫ g, fun x hx ↦ ?_⟩
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact ⟨e ≫ IsCofiltered.minToRight k (jx x), by rw [he, Category.assoc]⟩
    · obtain ⟨h, hh⟩ := hg x hx
      exact ⟨e ≫ IsCofiltered.minToLeft k (jx a) ≫ h, by rw [hh]; simp⟩

end CategoryTheory.IsCofiltered

namespace CategoryTheory

/-- The hypothesis `CategoryTheory.InitiallySmall.{u} Iᵒᵖ` used below is not vacuous: the ordinals
in `Type (u + 1)` form a nonempty directed preorder for which it fails, since a `u`-small set of
ordinals is bounded above and hence not cofinal. -/
theorem not_initiallySmall_op_ordinal : ¬ InitiallySmall.{u} (Ordinal.{u})ᵒᵖ := by
  intro _
  obtain ⟨s, hs, hws⟩ := InitiallySmall.exists_small_weakly_initial_set (J := (Ordinal.{u})ᵒᵖ)
  obtain ⟨b, hb⟩ := Ordinal.bddAbove_iff_small.2 (small_image Opposite.unop s)
  obtain ⟨y, hy, ⟨g⟩⟩ := hws (Opposite.op (b + 1))
  have : b + 1 ≤ b := (leOfHom g.unop).trans (hb ⟨y, hy, rfl⟩)
  simp at this

end CategoryTheory

namespace AlgebraicGeometry

namespace EventualFiniteness

/-- The preimage of `V` in `D k` is the preimage under `D.map h` of its preimage in `D j`. -/
private theorem preimage_app_eq_map_preimage {I : Type uI} [Category.{v} I] {S : Scheme.{u}}
    (D : I ⥤ Scheme.{u}) (t : D ⟶ (Functor.const I).obj S) {j k : I} (h : k ⟶ j)
    (V : S.Opens) : t.app k ⁻¹ᵁ V = D.map h ⁻¹ᵁ (t.app j ⁻¹ᵁ V) := by
  rw [← Scheme.Hom.comp_preimage, map_comp_app]

section SchemeUniverse

variable {I : Type u} [Category.{u} I] {S : Scheme.{u}} (D : I ⥤ Scheme.{u})
    (t : D ⟶ (Functor.const I).obj S) (c : Cone D)
    [IsCofiltered I] [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]

open Stacks.RingTheory.EventualFiniteness in
include c in
/-- The affine-base case of [Stacks, Tag 09ZN].  Over a fixed affine open `V` of the base, the
preimage of `V` is affine and the ring map `Γ(S, V) → Γ(Dⱼ, pⱼ⁻¹V)` is integral at some stage `j`
below any prescribed index.

This is `AlgebraicGeometry.EventualFiniteness.exists_isAffineOpen_and_isIntegral_app_of_isLimit`
without the hypothesis that `I` is thin. -/
lemma exists_isAffineOpen_and_isIntegral_app_of_cofiltered
    [QuasiSeparatedSpace S] (hc : IsLimit c) (f : c.pt ⟶ S) [IsIntegralHom f]
    (hf : ∀ i, f = c.π.app i ≫ t.app i)
    [∀ {i j : I} (g : i ⟶ j), IsFinite (D.map g)]
    [∀ i, LocallyOfFiniteType (t.app i)]
    (i : I) (V : S.Opens) (hV : IsAffineOpen V) :
    ∃ (j : I) (_ : j ⟶ i), IsAffineOpen (t.app j ⁻¹ᵁ V) ∧
      RingHom.IsIntegral (((t.app j).app V).hom) := by
  classical
  have : ∀ j : I, QuasiSeparatedSpace ↥(((Functor.const I).obj S).obj j) :=
    fun _ ↦ inferInstanceAs (QuasiSeparatedSpace ↥S)
  have hUcpt : IsCompact ((t.app i ⁻¹ᵁ V : (D.obj i).Opens) : Set (D.obj i)) :=
    QuasiCompact.isCompact_preimage (f := t.app i) _ V.2 hV.isCompact
  have hlim : IsAffineOpen (c.π.app i ⁻¹ᵁ (t.app i ⁻¹ᵁ V)) := by
    rw [← Scheme.Hom.comp_preimage, ← hf i]; exact hV.preimage f
  obtain ⟨j₀, g₀, haff₀⟩ :=
    exists_isAffineOpen_map_preimage_of_isLimit D c hc (t.app i ⁻¹ᵁ V) hUcpt hlim
  have haff : IsAffineOpen (t.app j₀ ⁻¹ᵁ V) := by
    rw [preimage_app_eq_map_preimage D t g₀]
    exact haff₀
  obtain rfl := hf j₀
  have hintlim : RingHom.IsIntegral ((((c.π.app j₀).app (t.app j₀ ⁻¹ᵁ V)).hom).comp
      (((t.app j₀).app V).hom)) := by
    rw [← Scheme.Hom.comp_app_hom]
    exact IsIntegralHom.isIntegral_app _ V hV
  have hftype : RingHom.FiniteType (((t.app j₀).app V).hom) := by
    have h := HasRingHomProperty.appLE @LocallyOfFiniteType (t.app j₀) inferInstance ⟨V, hV⟩
      ⟨t.app j₀ ⁻¹ᵁ V, haff⟩ le_rfl
    rwa [← Scheme.Hom.app_eq_appLE] at h
  obtain ⟨s, hs⟩ := exists_finset_gens _ hftype
  have key : ∀ x : Γ(D.obj j₀, t.app j₀ ⁻¹ᵁ V), ∃ (j : I) (g : j ⟶ j₀)
      (P : Polynomial Γ(S, V)), P.Monic ∧
      (((D.map g).app (t.app j₀ ⁻¹ᵁ V)).hom)
        (Polynomial.eval₂ (((t.app j₀).app V).hom) x P) = 0 := by
    intro x
    obtain ⟨P, hP, hPx⟩ := hintlim (((c.π.app j₀).app (t.app j₀ ⁻¹ᵁ V)).hom x)
    have h0 : (((c.π.app j₀).app (t.app j₀ ⁻¹ᵁ V)).hom)
        (Polynomial.eval₂ (((t.app j₀).app V).hom) x P) = 0 := by
      rw [Polynomial.hom_eval₂]; exact hPx
    obtain ⟨j, g, hg⟩ := exists_app_map_eq_zero_of_isLimit D c hc
      (U := t.app j₀ ⁻¹ᵁ V) haff.isCompact _ h0
    exact ⟨j, g, P, hP, hg⟩
  choose jx gx Px hPxmonic hPxzero using key
  -- A single stage `k` below `j₀` through which each chosen `gx x`, `x ∈ s`, factors.  This is
  -- where the F3 proof uses thinness of `I`.
  obtain ⟨k, g₁, hg₁⟩ := IsCofiltered.exists_hom_factor gx s
  refine ⟨k, g₁ ≫ g₀, ?_⟩
  have hphi : RingHom.Finite (((D.map g₁).app (t.app j₀ ⁻¹ᵁ V)).hom) :=
    IsFinite.finite_app (D.map g₁) (t.app j₀ ⁻¹ᵁ V) haff
  have hintim : ∀ a : Γ(D.obj j₀, t.app j₀ ⁻¹ᵁ V),
      ((((D.map g₁).app (t.app j₀ ⁻¹ᵁ V)).hom).comp
        (((t.app j₀).app V).hom)).IsIntegralElem
          ((((D.map g₁).app (t.app j₀ ⁻¹ᵁ V)).hom) a) := by
    refine isIntegralElem_image_of_gens (((t.app j₀).app V).hom)
      (((D.map g₁).app (t.app j₀ ⁻¹ᵁ V)).hom) _ hs ?_
    intro x hx
    refine ⟨Px x, hPxmonic x, ?_⟩
    refine (Polynomial.hom_eval₂ (Px x) (((t.app j₀).app V).hom)
      (((D.map g₁).app (t.app j₀ ⁻¹ᵁ V)).hom) x).symm.trans ?_
    obtain ⟨h, hh⟩ := hg₁ x hx
    rw [hh]
    exact app_map_eq_zero_of_comp D (gx x) _ _ _ (hPxzero x)
  have hint2 : RingHom.IsIntegral ((((D.map g₁).app (t.app j₀ ⁻¹ᵁ V)).hom).comp
      (((t.app j₀).app V).hom)) :=
    isIntegral_comp_of_isIntegralElem_image (((t.app j₀).app V).hom)
      (((D.map g₁).app (t.app j₀ ⁻¹ᵁ V)).hom) hphi.to_isIntegral hintim
  have hintring : RingHom.IsIntegral (((D.map g₁ ≫ t.app j₀).app V).hom) := by
    rw [Scheme.Hom.comp_app_hom]; exact hint2
  refine ⟨?_, ?_⟩
  · rw [preimage_app_eq_map_preimage D t g₁]
    exact haff.preimage (D.map g₁)
  · rw [← map_comp_app D t g₁]
    exact hintring

end SchemeUniverse

end EventualFiniteness

open EventualFiniteness in
/-- **Stacks 09ZN**, cofiltered form.  Let `{ Dᵢ }` be a cofiltered inverse system of qcqs schemes
over a qcqs base `S`, with finite transition morphisms and structure morphisms locally of finite
type.  If the induced morphism from the limit to `S` is integral, then some `Dᵢ → S` is finite.

This is `AlgebraicGeometry.Scheme.exists_isFinite_app_of_isLimit` without the hypothesis that `I`
is thin. -/
lemma Scheme.exists_isFinite_app_of_isLimit_of_cofiltered {I : Type u} [Category.{u} I]
    [IsCofiltered I] {S : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S]
    (D : I ⥤ Scheme.{u}) (t : D ⟶ (Functor.const I).obj S) (c : Cone D) (hc : IsLimit c)
    (f : c.pt ⟶ S) [IsIntegralHom f] (hf : ∀ i, f = c.π.app i ≫ t.app i)
    [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
    [∀ {i j : I} (g : i ⟶ j), IsFinite (D.map g)]
    [∀ i, LocallyOfFiniteType (t.app i)] :
    ∃ k : I, IsFinite (t.app k) := by
  classical
  obtain ⟨i₁⟩ := IsCofiltered.nonempty (C := I)
  obtain ⟨σ, hσ⟩ := isCompact_univ.elim_finite_subcover
    (fun U : S.affineOpens ↦ ((U : S.Opens) : Set S)) (fun U ↦ (U : S.Opens).2) (by
      intro x _
      have h : x ∈ (⨆ U : S.affineOpens, (U : S.Opens)) := by
        rw [iSup_affineOpens_eq_top S]; trivial
      simpa using h)
  have key : ∀ U : S.affineOpens, ∃ (j : I) (_ : j ⟶ i₁),
      IsAffineOpen (t.app j ⁻¹ᵁ (U : S.Opens)) ∧
        RingHom.IsIntegral (((t.app j).app (U : S.Opens)).hom) :=
    fun U ↦ exists_isAffineOpen_and_isIntegral_app_of_cofiltered D t c hc f hf i₁ U U.2
  choose jU _ hjU using key
  obtain ⟨k, T⟩ := IsCofiltered.inf_objs_exists (σ.image jU)
  refine ⟨k, (IsFinite.iff_isIntegralHom_and_locallyOfFiniteType _).mpr ⟨?_, inferInstance⟩⟩
  refine isIntegralHom_of_iSup_eq_top _ (fun U : {U // U ∈ σ} ↦ ((U.1 : S.Opens))) ?_ ?_
  · refine TopologicalSpace.Opens.ext ?_
    rw [TopologicalSpace.Opens.coe_iSup]
    refine Set.eq_univ_of_univ_subset (hσ.trans ?_)
    simp only [Set.iUnion_subset_iff]
    intro U hU
    exact Set.subset_iUnion_of_subset ⟨U, hU⟩ le_rfl
  · intro U
    obtain ⟨h⟩ := T (Finset.mem_image_of_mem _ U.2)
    show IsIntegralHom (t.app k ∣_ ((U.1 : S.Opens)))
    have : IsAffine ((U.1 : S.Opens)).toScheme := U.1.2
    have hA : IsAffineOpen (t.app k ⁻¹ᵁ ((U.1 : S.Opens))) := by
      rw [preimage_app_eq_map_preimage D t h]
      exact (hjU U.1).1.preimage (D.map h)
    have hI : RingHom.IsIntegral (((t.app k).app ((U.1 : S.Opens))).hom) := by
      rw [← map_comp_app D t h, Scheme.Hom.comp_app_hom]
      exact RingHom.isIntegral_stableUnderComposition _ _ (hjU U.1).2
        (IsFinite.finite_app (D.map h) _ (hjU U.1).1).to_isIntegral
    exact isIntegralHom_of_isAffine _ hA (isIntegral_app_top_morphismRestrict _ _ hI)

/-- **Stacks 09ZN** with the index universes independent of the scheme universe: some member of a
cofiltered inverse system of qcqs schemes with finite transition morphisms, locally of finite type
over a qcqs base, is finite over the base as soon as the limit is integral over the base.

The hypotheses `CategoryTheory.LocallySmall.{u} I` and `CategoryTheory.InitiallySmall.{u} I` are
the ones under which the universe-freed forms of Mathlib's limit API are available; see
`StacksFrontier/AlgebraicGeometry/LimitUniverse/AffineTransitionLimit.lean`. -/
theorem Scheme.exists_isFinite_app_of_isLimit_of_initiallySmall {I : Type uI} [Category.{v} I]
    [IsCofiltered I] [LocallySmall.{u} I] [InitiallySmall.{u} I]
    {S : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S]
    (D : I ⥤ Scheme.{u}) (t : D ⟶ (Functor.const I).obj S) (c : Cone D) (hc : IsLimit c)
    (f : c.pt ⟶ S) [IsIntegralHom f] (hf : ∀ i, f = c.π.app i ≫ t.app i)
    [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
    [∀ {i j : I} (g : i ⟶ j), IsFinite (D.map g)]
    [∀ i, LocallyOfFiniteType (t.app i)] :
    ∃ k : I, IsFinite (t.app k) := by
  have h₁ : ∀ {a b : CofilteredInitialModel.{u} I} (g : a ⟶ b),
      IsFinite ((fromCofilteredInitialModel.{u} I ⋙ D).map g) := by
    intros; dsimp; infer_instance
  have h₂ : ∀ a, CompactSpace ((fromCofilteredInitialModel.{u} I ⋙ D).obj a) := by
    intro a; dsimp; infer_instance
  have h₃ : ∀ a, QuasiSeparatedSpace ((fromCofilteredInitialModel.{u} I ⋙ D).obj a) := by
    intro a; dsimp; infer_instance
  let t' : (fromCofilteredInitialModel.{u} I ⋙ D) ⟶
      (Functor.const (CofilteredInitialModel.{u} I)).obj S :=
    { app a := t.app ((fromCofilteredInitialModel.{u} I).obj a)
      naturality := fun _ _ g ↦ t.naturality ((fromCofilteredInitialModel.{u} I).map g) }
  have h₄ : ∀ a, LocallyOfFiniteType (t'.app a) := by
    intro a; dsimp [t']; infer_instance
  obtain ⟨b, hb⟩ := Scheme.exists_isFinite_app_of_isLimit_of_cofiltered
    (fromCofilteredInitialModel.{u} I ⋙ D) t' _
    ((Functor.Initial.isLimitWhiskerEquiv (fromCofilteredInitialModel.{u} I) c).symm hc)
    f (fun a ↦ hf ((fromCofilteredInitialModel.{u} I).obj a))
  exact ⟨_, hb⟩

/-- **Stacks 09ZN** for a directed preorder, with the index universe independent of the scheme
universe.  In a directed inverse system of qcqs schemes over a qcqs scheme, if the transition
morphisms are finite, the stages are locally of finite type over the base, and the limit is
integral over the base, then the stages are eventually finite over the base.

The hypothesis `CategoryTheory.InitiallySmall.{u} Iᵒᵖ` says that `I` has a `u`-small cofinal
subset; it is automatic when `Small.{u} I`, see
`AlgebraicGeometry.eventually_isFinite_of_isLimit_of_isIntegral_of_small`. -/
theorem eventually_isFinite_of_isLimit_of_isIntegral_of_initiallySmall
    {I : Type w} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    [InitiallySmall.{u} Iᵒᵖ]
    {S : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S]
    (F : Iᵒᵖ ⥤ Scheme.{u}) (p : F ⟶ (Functor.const Iᵒᵖ).obj S)
    (c : Cone F) (hc : IsLimit c) (f : c.pt ⟶ S)
    (hf : ∀ i, f = c.π.app (Opposite.op i) ≫ p.app (Opposite.op i))
    [IsIntegralHom f]
    [∀ i, CompactSpace (F.obj (Opposite.op i))]
    [∀ i, QuasiSeparatedSpace (F.obj (Opposite.op i))]
    (haffine : ∀ {i j : I} (h : i ≤ j),
      IsAffineHom (F.map (homOfLE h).op))
    (hfinite : ∀ {i j : I} (h : i ≤ j),
      IsFinite (F.map (homOfLE h).op))
    [∀ i, LocallyOfFiniteType (p.app (Opposite.op i))] :
    ∀ᶠ i in Filter.atTop, IsFinite (p.app (Opposite.op i)) := by
  have : ∀ k : Iᵒᵖ, CompactSpace (F.obj k) :=
    fun k ↦ inferInstanceAs (CompactSpace ↥(F.obj (Opposite.op k.unop)))
  have : ∀ k : Iᵒᵖ, QuasiSeparatedSpace (F.obj k) :=
    fun k ↦ inferInstanceAs (QuasiSeparatedSpace ↥(F.obj (Opposite.op k.unop)))
  have : ∀ k : Iᵒᵖ, LocallyOfFiniteType (p.app k) :=
    fun k ↦ inferInstanceAs (LocallyOfFiniteType (p.app (Opposite.op k.unop)))
  have : ∀ {k l : Iᵒᵖ} (g : k ⟶ l), IsAffineHom (F.map g) := by
    intro k l g
    rw [show g = (homOfLE (leOfHom g.unop)).op from rfl]
    exact haffine _
  have : ∀ {k l : Iᵒᵖ} (g : k ⟶ l), IsFinite (F.map g) := by
    intro k l g
    rw [show g = (homOfLE (leOfHom g.unop)).op from rfl]
    exact hfinite _
  obtain ⟨k, hk⟩ := Scheme.exists_isFinite_app_of_isLimit_of_initiallySmall F p c hc f
    (fun k ↦ hf k.unop)
  rw [Filter.eventually_atTop]
  refine ⟨k.unop, fun j hj ↦ ?_⟩
  have := hk
  have hnat : F.map (homOfLE hj).op ≫ p.app k = p.app (Opposite.op j) := by simp
  rw [← hnat]
  infer_instance

/-- **Stacks 09ZN** for a directed preorder whose index type is `u`-small, with the index universe
otherwise independent of the scheme universe.  This is
`AlgebraicGeometry.eventually_isFinite_of_isLimit_of_isIntegral_of_initiallySmall` with its
hypothesis on `Iᵒᵖ` discharged. -/
theorem eventually_isFinite_of_isLimit_of_isIntegral_of_small
    {I : Type w} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)] [Small.{u} I]
    {S : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S]
    (F : Iᵒᵖ ⥤ Scheme.{u}) (p : F ⟶ (Functor.const Iᵒᵖ).obj S)
    (c : Cone F) (hc : IsLimit c) (f : c.pt ⟶ S)
    (hf : ∀ i, f = c.π.app (Opposite.op i) ≫ p.app (Opposite.op i))
    [IsIntegralHom f]
    [∀ i, CompactSpace (F.obj (Opposite.op i))]
    [∀ i, QuasiSeparatedSpace (F.obj (Opposite.op i))]
    (haffine : ∀ {i j : I} (h : i ≤ j),
      IsAffineHom (F.map (homOfLE h).op))
    (hfinite : ∀ {i j : I} (h : i ≤ j),
      IsFinite (F.map (homOfLE h).op))
    [∀ i, LocallyOfFiniteType (p.app (Opposite.op i))] :
    ∀ᶠ i in Filter.atTop, IsFinite (p.app (Opposite.op i)) :=
  have : InitiallySmall.{u} Iᵒᵖ := initiallySmall_of_small_of_locallySmall _
  eventually_isFinite_of_isLimit_of_isIntegral_of_initiallySmall F p c hc f hf haffine hfinite

end AlgebraicGeometry
