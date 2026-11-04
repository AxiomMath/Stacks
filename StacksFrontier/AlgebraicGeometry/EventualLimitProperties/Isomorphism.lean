module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.IsIso
public import Mathlib.Order.Filter.AtTopBot.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EventualLimitProperties.Basic

/-!
# Eventual isomorphisms in a limit of schemes

Let `X = lim Xᵢ` be the limit of a directed inverse system of quasi-compact schemes over a base
scheme `S` whose transition morphisms are closed immersions, and assume that the stages are
locally of finite type over `S`.  If `X` is locally of finite presentation over `S`, then the
projection `X ⟶ Xᵢ` is an isomorphism for all sufficiently large `i`.

## Main results

* `AlgebraicGeometry.EventualLimit.eventually_isIso_π_app`: the eventual isomorphism.
* `AlgebraicGeometry.EventualLimit.eventually_isIso_comp_π_app`: the form of the statement in
  which the limit is replaced by an isomorphic copy of it.

## Implementation notes

The argument is the one in the Stacks project: it is affine-local on a stage.  Choose a stage
`Xᵢ₀` and cover it by finitely many affine opens `V` each of which maps into an affine open `W`
of `S`.  On such a chart the ring `Γ(X, V∞)` is the filtered colimit of the rings `Γ(Xᵢ, Vᵢ)`,
the transition maps are surjective because the transition morphisms are closed immersions, and
`Γ(W) ⟶ Γ(X, V∞)` is of finite presentation while `Γ(W) ⟶ Γ(Xᵢ₀, V)` is of finite type.  Hence
the kernel of the surjection `Γ(Xᵢ₀, V) ⟶ Γ(X, V∞)` is finitely generated, so it is already the
kernel at a finite stage, and from that stage on the comparison map is an isomorphism.

The index universe is independent of the universe of the schemes, which is why the toolkit in
`StacksFrontier/AlgebraicGeometry/EventualLimitProperties/Basic.lean` is used instead of the
corresponding Mathlib results about `AffineTransitionLimit`.

## References

* [Stacks Project, Tag 081B](https://stacks.math.columbia.edu/tag/081B)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Filter Opposite TopologicalSpace

universe u v

namespace AlgebraicGeometry

namespace EventualLimit

/-! ### Auxiliary ring-theoretic facts -/

/-- A surjective ring homomorphism of finite presentation has finitely generated kernel. -/
lemma fg_ker_of_finitePresentation_of_surjective {A B : Type u} [CommRing A] [CommRing B]
    (α : A →+* B) (hα : α.FinitePresentation) (hsurj : Function.Surjective α) :
    (RingHom.ker α).FG := by
  algebraize [α]
  exact Algebra.FinitePresentation.ker_fG_of_surjective (Algebra.ofId A B) hsurj

/-- A property of ring homomorphisms which respects isomorphisms can be read off after
pre- and post-composing with isomorphisms. -/
lemma ringHomProperty_of_comp_isos
    {P : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop}
    (hP : RingHom.RespectsIso @P) {R S T V : CommRingCat.{u}} (a : R ⟶ S) (ha : IsIso a)
    (g : S ⟶ T) (b : T ⟶ V) (hb : IsIso b) (h : P g.hom) : P (a ≫ g ≫ b).hom := by
  have e1 : ((a ≫ (g ≫ b)) : R ⟶ V).hom = ((g ≫ b).hom).comp a.hom := CommRingCat.hom_comp _ _
  have e2 : ((g ≫ b) : S ⟶ V).hom = (b.hom).comp g.hom := CommRingCat.hom_comp _ _
  rw [e1, hP.cancel_left_isIso a (g ≫ b), e2, hP.cancel_right_isIso g b]
  exact h

/-- An affine open neighbourhood of a point inside a prescribed open. -/
lemma exists_isAffineOpen_mem_le {X : Scheme.{u}} (x : X) (O : X.Opens) (hx : x ∈ O) :
    ∃ V : X.Opens, IsAffineOpen V ∧ x ∈ V ∧ V ≤ O := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVO⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hx O.2
  exact ⟨V, hV, hxV, hVO⟩

/-! ### The setting -/

variable {I : Type v} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
  {S : Scheme.{u}} (D : Iᵒᵖ ⥤ Scheme.{u}) (t : D ⟶ (Functor.const Iᵒᵖ).obj S)
  (c : Cone D) (hc : IsLimit c) (p : c.pt ⟶ S)

omit [Nonempty I] [IsDirected I (· ≤ ·)] in
/-- In a directed inverse system of schemes indexed by the opposite of a preorder, if the
transition morphisms coming from the order relation are closed immersions then so is every
transition morphism. -/
lemma isClosedImmersion_map
    [∀ ⦃i j : I⦄ (h : i ≤ j), IsClosedImmersion (D.map (homOfLE h).op)]
    {a b : Iᵒᵖ} (g : a ⟶ b) : IsClosedImmersion (D.map g) := by
  have h : b.unop ≤ a.unop := leOfHom g.unop
  have hg : g = (homOfLE h).op := Quiver.Hom.unop_inj (Subsingleton.elim _ _)
  rw [hg]
  infer_instance

/-! ### The affine-local step -/

include hc in
/-- The affine-local heart of Tag 081B: on an affine chart of a stage which maps into an affine
open of the base, the projections from the limit are isomorphisms at all sufficiently late
stages. -/
lemma exists_isIso_preimageCone_π_app
    [∀ ⦃i j : I⦄ (h : i ≤ j), IsClosedImmersion (D.map (homOfLE h).op)]
    (hp : c.π ≫ t = (Functor.const Iᵒᵖ).map p) [LocallyOfFinitePresentation p]
    (i₀ : I) [LocallyOfFiniteType (t.app (op i₀))]
    {W : S.Opens} (hW : IsAffineOpen W) {V : (D.obj (op i₀)).Opens} (hV : IsAffineOpen V)
    (hVW : V ≤ t.app (op i₀) ⁻¹ᵁ W) :
    ∃ k₁ : Over (op i₀), ∀ (k : Over (op i₀)) (_ : k ⟶ k₁),
      IsIso ((preimageCone D c (op i₀) V).π.app k) := by
  have hci : ∀ {a b : Iᵒᵖ} (g : a ⟶ b), IsClosedImmersion (D.map g) := fun g =>
    isClosedImmersion_map D g
  have hah : ∀ {a b : Iᵒᵖ} (g : a ⟶ b), IsAffineHom (D.map g) := fun g => by
    have := hci g; infer_instance
  set E := preimageDiagram D (op i₀) V with hE
  set d := preimageCone D c (op i₀) V with hdd
  have hd : IsLimit d := isLimitPreimageCone D c hc (op i₀) V
  have hEaff : ∀ k, IsAffine (E.obj k) := isAffine_preimageDiagram_obj D (op i₀) hV
  have hdaff : IsAffine d.pt := isAffine_of_isLimit E d hd
  have : ∀ k : (Over (op i₀))ᵒᵖ, IsAffine ((E.op.obj k).unop) := fun k => hEaff k.unop
  have : PreservesColimit E.op Scheme.Γ := preservesColimit_Γ E.op
  have hΓ : IsColimit (Scheme.Γ.mapCocone d.op) := isColimitOfPreserves Scheme.Γ hd.op
  -- the distinguished index
  set k₀ : Over (op i₀) := Over.mk (𝟙 (op i₀)) with hk₀
  set j₀ : (Over (op i₀))ᵒᵖ := op k₀ with hj₀
  set arr : ∀ j : (Over (op i₀))ᵒᵖ, j₀ ⟶ j := fun j => (Over.mkIdTerminal.from j.unop).op
    with harrdef
  have harr : ∀ {j k : (Over (op i₀))ᵒᵖ} (g : j ⟶ k), arr j ≫ g = arr k := fun g =>
    Quiver.Hom.unop_inj (Over.mkIdTerminal.hom_ext _ _)
  have harr_id : arr j₀ = 𝟙 j₀ := Quiver.Hom.unop_inj (Over.mkIdTerminal.hom_ext _ _)
  -- surjectivity of the structure maps out of `j₀`
  have hsurjmap : ∀ j : (Over (op i₀))ᵒᵖ,
      Function.Surjective ((E.op ⋙ Scheme.Γ).map (arr j)).hom := fun j =>
    (IsClosedImmersion.isAffine_surjective_of_isAffine (E.map (arr j).unop)).2
  -- finite generation of the kernel at `j₀`
  have h1 : c.π.app (op i₀) ≫ t.app (op i₀) = p := NatTrans.congr_app hp (op i₀)
  have hV₀V : D.map (𝟙 (op i₀)) ⁻¹ᵁ V = V := by simp
  have hVW₀ : D.map (𝟙 (op i₀)) ⁻¹ᵁ V ≤ t.app (op i₀) ⁻¹ᵁ W := le_trans (le_of_eq hV₀V) hVW
  have hV₀ : IsAffineOpen (D.map (𝟙 (op i₀)) ⁻¹ᵁ V) := hV.preimage (D.map (𝟙 (op i₀)))
  have hVlim : IsAffineOpen (c.π.app (op i₀) ⁻¹ᵁ V) :=
    isAffineOpen_preimage_π_app D c hc (op i₀) hV
  have e₄ : c.π.app (op i₀) ⁻¹ᵁ V ≤ c.π.app (op i₀) ⁻¹ᵁ (D.map (𝟙 (op i₀)) ⁻¹ᵁ V) :=
    le_of_eq (by rw [hV₀V])
  have hple : c.π.app (op i₀) ⁻¹ᵁ V ≤ p ⁻¹ᵁ W := by
    calc c.π.app (op i₀) ⁻¹ᵁ V ≤ c.π.app (op i₀) ⁻¹ᵁ (t.app (op i₀) ⁻¹ᵁ W) :=
          ((Opens.map _).map (homOfLE hVW)).le
      _ = p ⁻¹ᵁ W := by rw [← Scheme.Hom.comp_preimage, h1]
  have hφ : RingHom.FiniteType
      ((t.app (op i₀)).appLE W (D.map (𝟙 (op i₀)) ⁻¹ᵁ V) hVW₀).hom :=
    HasRingHomProperty.appLE (@LocallyOfFiniteType) _ inferInstance ⟨W, hW⟩ ⟨_, hV₀⟩ hVW₀
  have hβ : RingHom.FinitePresentation (p.appLE W (c.π.app (op i₀) ⁻¹ᵁ V) hple).hom :=
    HasRingHomProperty.appLE (@LocallyOfFinitePresentation) _ inferInstance ⟨W, hW⟩
      ⟨_, hVlim⟩ hple
  have happLEcongr : ∀ (f g : c.pt ⟶ S) (hfg : f = g) (e : c.π.app (op i₀) ⁻¹ᵁ V ≤ f ⁻¹ᵁ W),
      f.appLE W (c.π.app (op i₀) ⁻¹ᵁ V) e =
        g.appLE W (c.π.app (op i₀) ⁻¹ᵁ V) (hfg ▸ e) := by
    intro f g hfg e
    cases hfg
    rfl
  have hcomp : (t.app (op i₀)).appLE W (D.map (𝟙 (op i₀)) ⁻¹ᵁ V) hVW₀ ≫
      (c.π.app (op i₀)).appLE (D.map (𝟙 (op i₀)) ⁻¹ᵁ V) (c.π.app (op i₀) ⁻¹ᵁ V) e₄ =
      p.appLE W (c.π.app (op i₀) ⁻¹ᵁ V) hple := by
    rw [Scheme.Hom.appLE_comp_appLE]
    exact happLEcongr _ _ h1 _
  have happLE₀ : RingHom.FinitePresentation
      ((c.π.app (op i₀)).appLE (D.map (𝟙 (op i₀)) ⁻¹ᵁ V) (c.π.app (op i₀) ⁻¹ᵁ V) e₄).hom := by
    refine RingHom.FinitePresentation.of_comp_finiteType _ ?_ hφ
    rw [← CommRingCat.hom_comp, hcomp]
    exact hβ
  have hres := Scheme.Hom.resLE_app_top (c.π.app (op i₀)) e₄
  have hα : RingHom.FinitePresentation
      ((Scheme.Γ.mapCocone d.op).ι.app j₀).hom := by
    have hgoal : ((Scheme.Γ.mapCocone d.op).ι.app j₀) =
        (D.map (𝟙 (op i₀)) ⁻¹ᵁ V).topIso.hom ≫
          (c.π.app (op i₀)).appLE (D.map (𝟙 (op i₀)) ⁻¹ᵁ V) (c.π.app (op i₀) ⁻¹ᵁ V) e₄ ≫
          (c.π.app (op i₀) ⁻¹ᵁ V).topIso.inv := hres
    rw [hgoal]
    exact ringHomProperty_of_comp_isos RingHom.finitePresentation_respectsIso _
      (Iso.isIso_hom _) _ _ (Iso.isIso_inv _) happLE₀
  have hsurj₀ : Function.Surjective ((Scheme.Γ.mapCocone d.op).ι.app j₀).hom :=
    surjective_ι hΓ j₀ arr hsurjmap
  have hker : (RingHom.ker ((Scheme.Γ.mapCocone d.op).ι.app j₀).hom).FG :=
    fg_ker_of_finitePresentation_of_surjective _ hα hsurj₀
  obtain ⟨j₁, hj₁⟩ := exists_isIso_ι hΓ j₀ arr harr harr_id hsurjmap hker
  refine ⟨j₁.unop, fun k g => ?_⟩
  have hiso : IsIso ((d.π.app k).appTop) := hj₁ (op k) g.op
  have : IsAffine (((Functor.const (Over (op i₀))).obj d.pt).obj k) := hdaff
  have := hEaff k
  have hspec : MorphismProperty.isomorphisms Scheme (Spec.map ((d.π.app k).appTop)) :=
    (MorphismProperty.isomorphisms.iff _).mpr inferInstance
  exact (MorphismProperty.isomorphisms.iff _).mp
    ((MorphismProperty.arrow_mk_iso_iff (MorphismProperty.isomorphisms Scheme)
      (arrowIsoSpecΓOfIsAffine (d.π.app k))).mpr hspec)

/-! ### The eventual isomorphism -/

include hc in
/-- **Stacks 081B (3).**  Let `X = lim Xᵢ` be the limit of a directed inverse system of
quasi-compact schemes over `S` whose transition morphisms are closed immersions and which are
locally of finite type over `S`.  If `X` is locally of finite presentation over `S`, then
`X ⟶ Xᵢ` is an isomorphism for all sufficiently large `i`. -/
@[sga "3 XI 3.11" "more general"]
theorem eventually_isIso_π_app (hp : c.π ≫ t = (Functor.const Iᵒᵖ).map p)
    [∀ i : I, CompactSpace (D.obj (op i))]
    [∀ i : I, LocallyOfFiniteType (t.app (op i))]
    [∀ ⦃i j : I⦄ (h : i ≤ j), IsClosedImmersion (D.map (homOfLE h).op)]
    [LocallyOfFinitePresentation p] :
    ∀ᶠ i in atTop, IsIso (c.π.app (op i)) := by
  classical
  obtain ⟨i₀⟩ := ‹Nonempty I›
  -- cover the stage `i₀` by affine opens each mapping into an affine open of `S`
  have hcov : ∀ x : D.obj (op i₀), ∃ (W : S.Opens) (V : (D.obj (op i₀)).Opens),
      IsAffineOpen W ∧ IsAffineOpen V ∧ x ∈ V ∧ V ≤ t.app (op i₀) ⁻¹ᵁ W := by
    intro x
    obtain ⟨W, hW, hxW, -⟩ :=
      exists_isAffineOpen_mem_le ((t.app (op i₀)).base x) ⊤ (by trivial)
    obtain ⟨V, hV, hxV, hVW⟩ := exists_isAffineOpen_mem_le x (t.app (op i₀) ⁻¹ᵁ W) hxW
    exact ⟨W, V, hW, hV, hxV, hVW⟩
  choose W V hW hV hxV hVW using hcov
  -- a finite subcover
  obtain ⟨σ, hσ⟩ := isCompact_univ.elim_finite_subcover
    (fun x : D.obj (op i₀) => (V x : Set (D.obj (op i₀)))) (fun x => (V x).isOpen)
    (fun y _ => Set.mem_iUnion.mpr ⟨y, hxV y⟩)
  -- the per-chart late indices
  have hchart : ∀ x : D.obj (op i₀), ∃ k₁ : Over (op i₀), ∀ (k : Over (op i₀)) (_ : k ⟶ k₁),
      IsIso ((preimageCone D c (op i₀) (V x)).π.app k) := fun x =>
    exists_isIso_preimageCone_π_app D t c hc p hp i₀ (hW x) (hV x) (hVW x)
  choose k₁ hk₁ using hchart
  obtain ⟨i₁, hi₁⟩ := (insert i₀ (σ.image fun x => (k₁ x).left.unop)).exists_le
  rw [eventually_atTop]
  refine ⟨i₁, fun i hi => ?_⟩
  have hi₀i : i₀ ≤ i := (hi₁ i₀ (Finset.mem_insert_self _ _)).trans hi
  have hcover : (⨆ x : {x // x ∈ σ}, D.map (homOfLE hi₀i).op ⁻¹ᵁ V x.1) = ⊤ := by
    rw [← Scheme.Hom.preimage_iSup]
    refine top_le_iff.mp fun y _ => ?_
    obtain ⟨x, hx, hy⟩ := Set.mem_iUnion₂.mp (hσ (Set.mem_univ ((D.map (homOfLE hi₀i).op).base y)))
    exact Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hy⟩
  refine (MorphismProperty.isomorphisms.iff _).mp
    (IsZariskiLocalAtTarget.of_iSup_eq_top (P := MorphismProperty.isomorphisms Scheme) _
      hcover fun x => ?_)
  have hle : (k₁ x.1).left.unop ≤ i :=
    (hi₁ _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ x.2))).trans hi
  have hk : (Over.mk (homOfLE hi₀i).op : Over (op i₀)) ⟶ k₁ x.1 :=
    Over.homMk ((homOfLE hle).op) (Subsingleton.elim _ _)
  have hiso := hk₁ x.1 (Over.mk (homOfLE hi₀i).op) hk
  have heq : c.π.app (op i) ⁻¹ᵁ (D.map (homOfLE hi₀i).op ⁻¹ᵁ V x.1)
      = c.π.app (op i₀) ⁻¹ᵁ V x.1 := by
    rw [← Scheme.Hom.comp_preimage, c.w]
  rw [← Scheme.Hom.resLE_eq_morphismRestrict,
    Scheme.Hom.resLE_congr (c.π.app (op i)) _ rfl heq (MorphismProperty.isomorphisms Scheme)]
  exact (MorphismProperty.isomorphisms.iff _).mpr hiso

include hc in
/-- **Stacks 081B (3)**, in the form in which the limit is presented through an isomorphism
`f : Y ≅ lim Xᵢ`: the composites `Y ⟶ Xᵢ` are isomorphisms for all sufficiently large `i`. -/
@[stacks 081B "eventually_isomorphism"]
theorem eventually_isIso_comp_π_app (hp : c.π ≫ t = (Functor.const Iᵒᵖ).map p)
    {Y : Scheme.{u}} (f : Y ⟶ c.pt) [IsIso f]
    [∀ i : I, CompactSpace (D.obj (op i))]
    [∀ i : I, LocallyOfFiniteType (t.app (op i))]
    [∀ ⦃i j : I⦄ (h : i ≤ j), IsClosedImmersion (D.map (homOfLE h).op)]
    [LocallyOfFinitePresentation (f ≫ p)] :
    ∀ᶠ i in atTop, IsIso (f ≫ c.π.app (op i)) := by
  have hlfp : LocallyOfFinitePresentation p := by
    have h : p = inv f ≫ (f ≫ p) := by
      rw [← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
    rw [h]
    infer_instance
  exact (eventually_isIso_π_app D t c hc p hp).mono fun i hi => inferInstance

end EventualLimit

end AlgebraicGeometry
