module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.RingTheory.FiniteType
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EventualLimitProperties.Basic

/-!
# Eventual closed immersions into a limit of schemes

Let `X = lim Xᵢ` be the limit of a directed inverse system of quasi-compact schemes over a base
scheme `S` whose transition morphisms are affine.  A closed immersion `Y ⟶ X` whose source is
locally of finite type over `S` is already a closed immersion into `Xᵢ` for all sufficiently
large `i`.

## Main results

* `AlgebraicGeometry.EventualLimit.exists_ι_app_eq`: every element of a filtered colimit of
  rings comes from one of the stages.
* `AlgebraicGeometry.EventualLimit.exists_surjective_comp_ι`: a surjection out of a filtered
  colimit of rings onto a ring of finite type over one stage is already surjective at all
  sufficiently late stages.
* `AlgebraicGeometry.EventualLimit.exists_isClosedImmersion_comp_π_app_of_isAffine`: the affine
  case of the eventual closed immersion.
* `AlgebraicGeometry.EventualLimit.isAffineHom_map`: in a directed inverse system indexed by the
  opposite of a preorder, affineness of the transition morphisms coming from the order relation
  gives affineness of every transition morphism.
* `AlgebraicGeometry.EventualLimit.eventually_isClosedImmersion_comp_π_app`: the eventual closed
  immersion.

## Implementation notes

The argument is the one in the Stacks project: it is affine-local on a stage.  Choose a stage
`Xᵢ₀` and an affine open `V ⊆ Xᵢ₀`.  The preimage of `V` in `X` is affine, its ring of global
sections is the filtered colimit of the rings of global sections of the preimages of `V` at the
later stages, and the preimage of it in `Y` is an affine closed subscheme, so the induced map of
global sections is surjective.  Since `Y` is locally of finite type over `S`, the ring of global
sections of that closed subscheme is a finitely generated algebra over the ring of the chart at
`i₀`; picking generators and lifting each of them to a single stage shows that the map from the
chart at some later stage is already surjective, that is, that the corresponding restriction of
`Y ⟶ Xⱼ` is a closed immersion.  Quasi-compactness of `Xᵢ₀` lets finitely many such charts cover
it, and a single stage then works for all of them.

Joint surjectivity of the colimit maps is proved directly, by exhibiting the elements coming from
the stages as a subring through which the colimit cocone factors, rather than through a
preservation statement for the forgetful functor.  This keeps the index category in an arbitrary
universe, which is the point of the toolkit in
`StacksFrontier/AlgebraicGeometry/EventualLimitProperties/Basic.lean`.

## References

* [Stacks Project, Tag 081B](https://stacks.math.columbia.edu/tag/081B)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Filter Opposite

universe u v w

namespace AlgebraicGeometry

namespace EventualLimit

/-! ### Joint surjectivity in a filtered colimit of rings -/

section FilteredColimit

variable {J : Type w} [Category.{v} J] {F : J ⥤ CommRingCat.{u}}

/-- A structure map of a diagram of rings followed by the colimit map at its target is the
colimit map at its source. -/
private lemma ι_app_map_apply (d : Cocone F) {j k : J} (g : j ⟶ k) (x : F.obj j) :
    (d.ι.app k).hom ((F.map g).hom x) = (d.ι.app j).hom x := by
  rw [← ConcreteCategory.comp_apply, d.w g]

/-- `ι_app_map_apply` after composing with a further map `q` out of the vertex. -/
private lemma ι_app_map_comp_apply (d : Cocone F) {T : CommRingCat.{u}} (q : d.pt ⟶ T) {j k : J}
    (g : j ⟶ k) (x : F.obj j) :
    (d.ι.app k ≫ q).hom ((F.map g).hom x) = (d.ι.app j ≫ q).hom x := by
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply]
  rw [ι_app_map_apply]

variable [IsFiltered J]

/-- The elements of the vertex of a cocone on a filtered diagram of rings which come from one of
the stages.  Filteredness of the index category makes them a subring. -/
private def jointRange (d : Cocone F) : Subring d.pt where
  carrier := {z | ∃ (j : J) (x : F.obj j), (d.ι.app j).hom x = z}
  one_mem' := ⟨Classical.choice IsFiltered.nonempty, 1, map_one _⟩
  zero_mem' := ⟨Classical.choice IsFiltered.nonempty, 0, map_zero _⟩
  mul_mem' := by
    rintro a b ⟨j, x, rfl⟩ ⟨k, y, rfl⟩
    refine ⟨IsFiltered.max j k, (F.map (IsFiltered.leftToMax j k)).hom x *
      (F.map (IsFiltered.rightToMax j k)).hom y, ?_⟩
    rw [map_mul, ι_app_map_apply, ι_app_map_apply]
  add_mem' := by
    rintro a b ⟨j, x, rfl⟩ ⟨k, y, rfl⟩
    refine ⟨IsFiltered.max j k, (F.map (IsFiltered.leftToMax j k)).hom x +
      (F.map (IsFiltered.rightToMax j k)).hom y, ?_⟩
    rw [map_add, ι_app_map_apply, ι_app_map_apply]
  neg_mem' := by
    rintro a ⟨j, x, rfl⟩
    exact ⟨j, -x, map_neg _ _⟩

/-- Every element of a filtered colimit of rings is the image of an element of one of the
stages. -/
lemma exists_ι_app_eq {d : Cocone F} (hd : IsColimit d) (z : d.pt) :
    ∃ (j : J) (x : F.obj j), (d.ι.app j).hom x = z := by
  have hmem (j : J) (y : F.obj j) : (d.ι.app j).hom y ∈ jointRange d := ⟨j, y, rfl⟩
  let e : Cocone F :=
    { pt := CommRingCat.of (jointRange d)
      ι :=
      { app j := CommRingCat.ofHom ((d.ι.app j).hom.codRestrict (jointRange d) (hmem j))
        naturality := fun j k g => by
          ext y
          refine Subtype.ext ?_
          change (d.ι.app k).hom ((F.map g).hom y) = (d.ι.app j).hom y
          exact ι_app_map_apply d g y } }
  have hcomp : hd.desc e ≫ CommRingCat.ofHom (jointRange d).subtype = 𝟙 d.pt := by
    refine hd.hom_ext fun j => ?_
    rw [← Category.assoc, hd.fac e j, Category.comp_id]
    ext y
    rfl
  have h2 := congrArg (fun r : d.pt ⟶ d.pt => r.hom z) hcomp
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_id,
    RingHom.id_apply, CommRingCat.hom_ofHom] at h2
  obtain ⟨j, x, hx⟩ := ((hd.desc e).hom z).2
  exact ⟨j, x, hx.trans h2⟩

/-- Let a cocone on a filtered diagram of rings be a colimit and let `q` be a surjection from its
vertex onto a ring `T`.  If `T` is of finite type over the stage `j₀`, then `q` composed with the
colimit map is already surjective at all sufficiently late stages.

Each of finitely many algebra generators of `T` over the stage `j₀` lifts to the colimit, hence to
a single stage, and any stage beyond `j₀` and all of those works. -/
lemma exists_surjective_comp_ι {d : Cocone F} (hd : IsColimit d) (j₀ : J)
    {T : CommRingCat.{u}} (q : d.pt ⟶ T) (hq : Function.Surjective q.hom)
    (hft : RingHom.FiniteType (d.ι.app j₀ ≫ q).hom) :
    ∃ j₁ : J, ∀ (j : J) (_ : j₁ ⟶ j), Function.Surjective (d.ι.app j ≫ q).hom := by
  classical
  have hstage : ∀ b : T, ∃ (j : J) (x : F.obj j), q.hom ((d.ι.app j).hom x) = b := by
    intro b
    obtain ⟨a, ha⟩ := hq b
    obtain ⟨j, x, hx⟩ := exists_ι_app_eq hd a
    exact ⟨j, x, by rw [hx, ha]⟩
  choose jb xb hxb using hstage
  let : Algebra (F.obj j₀) T := (d.ι.app j₀ ≫ q).hom.toAlgebra
  obtain ⟨σ, hσ⟩ := (hft : Algebra.FiniteType (F.obj j₀) T).out
  obtain ⟨m, hm⟩ := IsFiltered.sup_objs_exists (insert j₀ (σ.image jb))
  obtain ⟨g₀⟩ := hm (Finset.mem_insert_self j₀ (σ.image jb))
  let : Algebra (F.obj j₀) (F.obj m) := (F.map g₀).hom.toAlgebra
  let : Algebra (F.obj m) T := (d.ι.app m ≫ q).hom.toAlgebra
  have : IsScalarTower (F.obj j₀) (F.obj m) T := IsScalarTower.of_algebraMap_eq fun y => by
    exact (ι_app_map_comp_apply d q g₀ y).symm
  let ψ : F.obj m →ₐ[F.obj j₀] T := IsScalarTower.toAlgHom _ _ _
  have hψ (y : F.obj m) : ψ y = (d.ι.app m ≫ q).hom y := rfl
  have hgen : (σ : Set T) ⊆ (ψ.range : Set T) := by
    intro b hb
    obtain ⟨gb⟩ := hm (Finset.mem_insert_of_mem
      (Finset.mem_image_of_mem jb (Finset.mem_coe.mp hb)))
    exact ⟨(F.map gb).hom (xb b), (hψ _).trans ((ι_app_map_comp_apply d q gb _).trans (hxb b))⟩
  have hle : Algebra.adjoin (F.obj j₀) (σ : Set T) ≤ ψ.range := Algebra.adjoin_le hgen
  rw [hσ] at hle
  have hsurjψ : Function.Surjective ψ := (AlgHom.range_eq_top ψ).mp (top_le_iff.mp hle)
  have hsurjm : Function.Surjective (d.ι.app m ≫ q).hom := fun z => by
    obtain ⟨y, hy⟩ := hsurjψ z
    exact ⟨y, (hψ y).symm.trans hy⟩
  refine ⟨m, fun j g z => ?_⟩
  obtain ⟨y, hy⟩ := hsurjm z
  exact ⟨(F.map g).hom y, (ι_app_map_comp_apply d q g y).trans hy⟩

end FilteredColimit

/-! ### The affine case -/

/-- Let `Z ⟶ lim Eₖ` be a closed immersion into a cofiltered limit of affine schemes whose
composite with the projection to one stage `k₀` is locally of finite type.  Then there is a stage
`k₁` such that `Z ⟶ Eₖ` is a closed immersion for every stage `k` with a morphism to `k₁`.

The ring of global sections of the limit is the filtered colimit of those of the stages, and
`Γ(Z)` is a finitely generated algebra over the ring of the stage `k₀`, so a finite set of
generators is already hit at a single stage.

The two hypotheses on `g` are explicit arguments rather than instances because the composites
with the legs of a cone on a diagram of open subschemes are not syntactically recognised by
instance search. -/
lemma exists_isClosedImmersion_comp_π_app_of_isAffine {K : Type w} [Category.{v} K]
    [IsCofiltered K] (E : K ⥤ Scheme.{u}) [∀ k, IsAffine (E.obj k)]
    (e : Cone E) (he : IsLimit e) {Z : Scheme.{u}} (g : Z ⟶ e.pt)
    (hg : IsClosedImmersion g) (k₀ : K) (hgft : LocallyOfFiniteType (g ≫ e.π.app k₀)) :
    ∃ k₁ : K, ∀ (k : K) (_ : k ⟶ k₁), IsClosedImmersion (g ≫ e.π.app k) := by
  have := hg
  have := hgft
  have hpt : IsAffine e.pt := isAffine_of_isLimit E e he
  obtain ⟨hZaff, hsurj⟩ := IsClosedImmersion.isAffine_surjective_of_isAffine g
  have := hZaff
  have hft : RingHom.FiniteType ((g ≫ e.π.app k₀).appTop).hom := by
    simpa [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE] using
      (g ≫ e.π.app k₀).finiteType_appLE (isAffineOpen_top _) (isAffineOpen_top _) (by simp)
  have : ∀ k : Kᵒᵖ, IsAffine ((E.op.obj k).unop) := fun k =>
    inferInstanceAs (IsAffine (E.obj k.unop))
  have : PreservesColimit E.op Scheme.Γ := preservesColimit_Γ E.op
  have hΓ : IsColimit (Scheme.Γ.mapCocone e.op) := isColimitOfPreserves Scheme.Γ he.op
  have hι : ∀ k : K, (Scheme.Γ.mapCocone e.op).ι.app (op k) ≫ g.appTop =
      (g ≫ e.π.app k).appTop := fun k => (Scheme.Hom.comp_appTop _ _).symm
  have hftι : RingHom.FiniteType
      ((Scheme.Γ.mapCocone e.op).ι.app (op k₀) ≫ g.appTop).hom := by
    rwa [hι k₀]
  obtain ⟨j₁, hj₁⟩ := exists_surjective_comp_ι hΓ (op k₀) g.appTop hsurj hftι
  refine ⟨j₁.unop, fun k hk => ?_⟩
  have hs := hj₁ (op k) hk.op
  rw [hι k] at hs
  exact IsClosedImmersion.of_surjective_of_isAffine _ hs

/-! ### The setting -/

variable {I : Type v} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
  {S Y : Scheme.{u}} (D : Iᵒᵖ ⥤ Scheme.{u}) (t : D ⟶ (Functor.const Iᵒᵖ).obj S)
  (c : Cone D) (hc : IsLimit c) (s : c.pt ⟶ S) (f : Y ⟶ c.pt)

omit [Nonempty I] [IsDirected I (· ≤ ·)] in
/-- In a directed inverse system of schemes indexed by the opposite of a preorder, if the
transition morphisms coming from the order relation are affine then so is every transition
morphism. -/
lemma isAffineHom_map [∀ ⦃i j : I⦄ (h : i ≤ j), IsAffineHom (D.map (homOfLE h).op)]
    {a b : Iᵒᵖ} (g : a ⟶ b) : IsAffineHom (D.map g) := by
  have h : b.unop ≤ a.unop := leOfHom g.unop
  have hg : g = (homOfLE h).op := Quiver.Hom.unop_inj (Subsingleton.elim _ _)
  rw [hg]
  infer_instance

/-! ### The affine-local step -/

include hc in
/-- The affine-local heart of Tag 081B (1): on an affine open `V` of a stage `i₀`, the restriction
of `Y ⟶ Xⱼ` over the preimage of `V` is a closed immersion for all sufficiently late stages
`j`. -/
private lemma exists_isClosedImmersion_morphismRestrict
    [∀ ⦃i j : I⦄ (h : i ≤ j), IsAffineHom (D.map (homOfLE h).op)]
    (hcomm : c.π ≫ t = (Functor.const Iᵒᵖ).map s)
    [LocallyOfFiniteType (f ≫ s)] [IsClosedImmersion f]
    (i₀ : I) {V : (D.obj (op i₀)).Opens} (hV : IsAffineOpen V) :
    ∃ k₁ : Over (op i₀), ∀ (k : Over (op i₀)) (_ : k ⟶ k₁),
      IsClosedImmersion ((f ≫ c.π.app k.left) ∣_ (D.map k.hom ⁻¹ᵁ V)) := by
  have hah : ∀ {a b : Iᵒᵖ} (g : a ⟶ b), IsAffineHom (D.map g) := fun g => isAffineHom_map D g
  have hd : IsLimit (preimageCone D c (op i₀) V) := isLimitPreimageCone D c hc (op i₀) V
  have hEaff : ∀ k, IsAffine ((preimageDiagram D (op i₀) V).obj k) :=
    isAffine_preimageDiagram_obj D (op i₀) hV
  -- the restriction of `f` over the chart in the limit
  have hφ : IsClosedImmersion (f.resLE (c.π.app (op i₀) ⁻¹ᵁ V)
      (f ⁻¹ᵁ (c.π.app (op i₀) ⁻¹ᵁ V)) le_rfl) := by
    rw [Scheme.Hom.resLE_eq_morphismRestrict]
    exact IsZariskiLocalAtTarget.restrict (P := @IsClosedImmersion) inferInstance _
  -- the preimages of `V` in the limit and at the distinguished stage agree
  have hpre : ∀ k : Over (op i₀),
      c.π.app k.left ⁻¹ᵁ (D.map k.hom ⁻¹ᵁ V) = c.π.app (op i₀) ⁻¹ᵁ V := fun k => by
    rw [← Scheme.Hom.comp_preimage, c.w]
  -- the restriction of `f` is locally of finite type over the chart at the distinguished stage
  have h1 : c.π.app (op i₀) ≫ t.app (op i₀) = s := NatTrans.congr_app hcomm (op i₀)
  have hid : D.map (𝟙 (op i₀)) ⁻¹ᵁ V = V := by simp
  have hle₀ : f ⁻¹ᵁ (c.π.app (op i₀) ⁻¹ᵁ V) ≤
      (f ≫ c.π.app (op i₀)) ⁻¹ᵁ (D.map (𝟙 (op i₀)) ⁻¹ᵁ V) := by
    rw [Scheme.Hom.comp_preimage, hid]
  have hχ : LocallyOfFiniteType ((f ≫ c.π.app (op i₀)).resLE (D.map (𝟙 (op i₀)) ⁻¹ᵁ V)
      (f ⁻¹ᵁ (c.π.app (op i₀) ⁻¹ᵁ V)) hle₀) := by
    have hfac : ((f ≫ c.π.app (op i₀)).resLE (D.map (𝟙 (op i₀)) ⁻¹ᵁ V)
        (f ⁻¹ᵁ (c.π.app (op i₀) ⁻¹ᵁ V)) hle₀) ≫
        ((D.map (𝟙 (op i₀)) ⁻¹ᵁ V).ι ≫ t.app (op i₀)) =
        (f ⁻¹ᵁ (c.π.app (op i₀) ⁻¹ᵁ V)).ι ≫ (f ≫ s) := by
      rw [← Category.assoc, Scheme.Hom.resLE_comp_ι]
      simp only [Category.assoc, h1]
    have hsrc : LocallyOfFiniteType
        ((f ⁻¹ᵁ (c.π.app (op i₀) ⁻¹ᵁ V)).ι ≫ (f ≫ s)) := inferInstance
    rw [← hfac] at hsrc
    have := hsrc
    exact locallyOfFiniteType_of_comp _ ((D.map (𝟙 (op i₀)) ⁻¹ᵁ V).ι ≫ t.app (op i₀))
  have hψ : LocallyOfFiniteType (f.resLE (c.π.app (op i₀) ⁻¹ᵁ V)
      (f ⁻¹ᵁ (c.π.app (op i₀) ⁻¹ᵁ V)) le_rfl ≫
      (c.π.app (op i₀)).resLE (D.map (𝟙 (op i₀)) ⁻¹ᵁ V) (c.π.app (op i₀) ⁻¹ᵁ V)
        (le_of_eq (hpre (Over.mk (𝟙 (op i₀)))).symm)) := by
    rwa [Scheme.Hom.resLE_comp_resLE]
  obtain ⟨k₁, hk₁⟩ := exists_isClosedImmersion_comp_π_app_of_isAffine
    (preimageDiagram D (op i₀) V) (preimageCone D c (op i₀) V) hd
    (f.resLE (c.π.app (op i₀) ⁻¹ᵁ V) (f ⁻¹ᵁ (c.π.app (op i₀) ⁻¹ᵁ V)) le_rfl) hφ
    (Over.mk (𝟙 (op i₀))) hψ
  refine ⟨k₁, fun k hk => ?_⟩
  have hcl : IsClosedImmersion (f.resLE (c.π.app (op i₀) ⁻¹ᵁ V)
      (f ⁻¹ᵁ (c.π.app (op i₀) ⁻¹ᵁ V)) le_rfl ≫
      (c.π.app k.left).resLE (D.map k.hom ⁻¹ᵁ V) (c.π.app (op i₀) ⁻¹ᵁ V)
        (le_of_eq (hpre k).symm)) := hk₁ k hk
  rw [Scheme.Hom.resLE_comp_resLE] at hcl
  have heq : (f ≫ c.π.app k.left) ⁻¹ᵁ (D.map k.hom ⁻¹ᵁ V)
      = f ⁻¹ᵁ (c.π.app (op i₀) ⁻¹ᵁ V) := by
    rw [Scheme.Hom.comp_preimage, hpre k]
  rwa [← Scheme.Hom.resLE_eq_morphismRestrict,
    Scheme.Hom.resLE_congr (f ≫ c.π.app k.left) _ rfl heq (@IsClosedImmersion)]

/-! ### The eventual closed immersion -/

include hc in
/-- **Stacks 081B (1).**  Let `X = lim Xᵢ` be the limit of a directed inverse system of
quasi-compact schemes over `S` whose transition morphisms are affine.  If `f : Y ⟶ X` is a closed
immersion and `Y` is locally of finite type over `S`, then the composite `Y ⟶ Xᵢ` is a closed
immersion for all sufficiently large `i`. -/
@[stacks 081B "part (1)"]
theorem eventually_isClosedImmersion_comp_π_app
    (hcomm : c.π ≫ t = (Functor.const Iᵒᵖ).map s)
    [∀ i : I, CompactSpace (D.obj (op i))]
    [∀ ⦃i j : I⦄ (h : i ≤ j), IsAffineHom (D.map (homOfLE h).op)]
    [LocallyOfFiniteType (f ≫ s)] [IsClosedImmersion f] :
    ∀ᶠ i in atTop, IsClosedImmersion (f ≫ c.π.app (op i)) := by
  classical
  obtain ⟨i₀⟩ := ‹Nonempty I›
  -- cover the stage `i₀` by affine opens
  have hcov : ∀ x : D.obj (op i₀), ∃ V : (D.obj (op i₀)).Opens, IsAffineOpen V ∧ x ∈ V := by
    intro x
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
      (D.obj (op i₀)).isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    exact ⟨V, hV, hxV⟩
  choose V hV hxV using hcov
  obtain ⟨σ, hσ⟩ := isCompact_univ.elim_finite_subcover
    (fun x : D.obj (op i₀) => (V x : Set (D.obj (op i₀)))) (fun x => (V x).isOpen)
    (fun y _ => Set.mem_iUnion.mpr ⟨y, hxV y⟩)
  -- the per-chart late indices
  choose k₁ hk₁ using fun x =>
    exists_isClosedImmersion_morphismRestrict D t c hc s f hcomm i₀ (hV x)
  obtain ⟨i₁, hi₁⟩ := (insert i₀ (σ.image fun x => (k₁ x).left.unop)).exists_le
  rw [eventually_atTop]
  refine ⟨i₁, fun i hi => ?_⟩
  have hi₀i : i₀ ≤ i := (hi₁ i₀ (Finset.mem_insert_self _ _)).trans hi
  have hcover : (⨆ x : {x // x ∈ σ}, D.map (homOfLE hi₀i).op ⁻¹ᵁ V x.1) = ⊤ := by
    rw [← Scheme.Hom.preimage_iSup]
    refine top_le_iff.mp fun y _ => ?_
    obtain ⟨x, hx, hy⟩ :=
      Set.mem_iUnion₂.mp (hσ (Set.mem_univ ((D.map (homOfLE hi₀i).op).base y)))
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hy⟩
  refine IsZariskiLocalAtTarget.of_iSup_eq_top (P := @IsClosedImmersion) _ hcover fun x => ?_
  have hle : (k₁ x.1).left.unop ≤ i :=
    (hi₁ _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ x.2))).trans hi
  have hk : (Over.mk (homOfLE hi₀i).op : Over (op i₀)) ⟶ k₁ x.1 :=
    Over.homMk ((homOfLE hle).op) (Subsingleton.elim _ _)
  exact hk₁ x.1 (Over.mk (homOfLE hi₀i).op) hk

end EventualLimit

end AlgebraicGeometry
