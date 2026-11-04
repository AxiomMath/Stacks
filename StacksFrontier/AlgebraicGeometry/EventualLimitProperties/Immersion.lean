module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.Order.Filter.AtTopBot.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EventualLimitProperties.ClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Limits.RelativeApproximation.ClosedImmersionDescent

/-!
# Eventual immersions into a limit of schemes

Let `X = lim Xᵢ` be the limit of a directed inverse system of schemes over a base scheme `S`
whose transition morphisms are affine, with the stages only assumed quasi-separated (not
quasi-compact). If `Y ⟶ X` is an immersion, `Y` is locally of finite type over `S` and `Y` is
quasi-compact, then `Y ⟶ Xᵢ` is an immersion for all sufficiently large `i`.

## Main results

* `AlgebraicGeometry.EventualLimit.eventually_isImmersion_comp_π_app_of_quasiSeparatedSpace`:
  **Stacks 081B (2)**, at the source's hypotheses and for an index type in any universe.
* `AlgebraicGeometry.EventualLimit.exists_isCompact_le_of_subset`: a quasi-compact subset of an
  open subscheme lies in a quasi-compact open contained in it.
* `AlgebraicGeometry.EventualLimit.eventually_isImmersion_comp_π_app`: the same conclusion for an
  index type in the universe of the schemes, where Mathlib's `exists_preimage_eq` applies and the
  quasi-separatedness of the stages is not needed.

## Implementation notes

Unlike Stacks 081B (1) (closed immersions, carried by
`AlgebraicGeometry.EventualLimit.eventually_isClosedImmersion_comp_π_app`), the stages here are
not assumed quasi-compact, so a stage cannot in general be covered by finitely many affine opens.
What *is* quasi-compact is `Y`, and an immersion `f : Y ⟶ X` factors, by Stacks 0E2L
(`AlgebraicGeometry.isImmersion_iff_exists`), as a closed immersion into an open `U ⊆ X` followed
by the inclusion of that open, with `U` any open containing the range of `f` and contained in its
`coborderRange`. Covering `Y` by finitely many affine opens of `X`, each placed inside the
`coborderRange` by the basis of affine opens, produces such a `U` which is moreover
quasi-compact, being a finite union of affine opens. Stacks 01Z4 (1), freed from Mathlib's
restriction tying the index-object universe to the scheme universe (reproved here as
`AlgebraicGeometry.EventualLimit.exists_preimage_eq_free`, via a basis of preimages of affine
opens, `AlgebraicGeometry.EventualLimit.isBasis_preimage_isAffineOpen`), then exhibits `U` as
the preimage of a quasi-compact open `U₀` of some stage `j₀`, and `U₀`, being quasi-compact, is
covered by finitely many affine opens, each amenable to the affine-local argument of
Tag 081B (1).

The two directions of transporting closedness between a double restriction `f ∣_ U ∣_ (U.ι⁻¹ᵁW)`
and the direct restriction `f ∣_ W` for `W ≤ U`, via the isomorphism
`AlgebraicGeometry.morphismRestrictRestrict`, are used twice with the roles of `U` and `W`
reversed: once to push the affine-local closed immersions down from the ambient `X` to the
individual charts of `U₀` (as in Tag 081B (1)), and once to push them back up to a single closed
immersion onto the quasi-compact preimage of `U₀` at a late enough stage, from which the
immersion property of the whole map at that stage follows by composing with the open immersion
of that preimage into the stage — `AlgebraicGeometry.IsImmersion` being closed under composition,
unlike `AlgebraicGeometry.IsClosedImmersion`, this final step needs no covering of the whole
stage.

## References

* [Stacks Project, Tag 081B](https://stacks.math.columbia.edu/tag/081B)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Filter Opposite TopologicalSpace
open scoped Set.Notation

universe u v w

namespace AlgebraicGeometry

namespace EventualLimit

/-- A point of an open subscheme lies in an affine open contained in that subscheme. -/
private lemma exists_isAffineOpen_mem_le {X : Scheme.{u}} {x : X} {O : X.Opens} (hx : x ∈ O) :
    ∃ W : X.Opens, IsAffineOpen W ∧ x ∈ W ∧ W ≤ O := by
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWO⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hx O.isOpen
  exact ⟨W, hW, hxW, hWO⟩

/-- A quasi-compact subset of an open subscheme of a scheme lies in a quasi-compact open
contained in that open subscheme: it is covered by finitely many affine opens contained in it. -/
lemma exists_isCompact_le_of_subset (X : Scheme.{u}) {K : Set X} (hK : IsCompact K)
    (O : X.Opens) (hKO : K ⊆ O) :
    ∃ U : X.Opens, IsCompact (U : Set X) ∧ K ⊆ U ∧ U ≤ O := by
  classical
  have hW : ∀ x ∈ K, ∃ W : X.Opens, IsAffineOpen W ∧ x ∈ W ∧ W ≤ O := fun _ hx =>
    exists_isAffineOpen_mem_le (hKO hx)
  choose! W hWa hxW hWO using hW
  obtain ⟨t, htK, hcov⟩ := hK.elim_nhds_subcover (fun x => (W x : Set X))
    (fun x hx => (W x).isOpen.mem_nhds (hxW x hx))
  refine ⟨⨆ x ∈ t, W x, ?_, ?_, iSup₂_le fun x hx => hWO x (htK x hx)⟩
  · simp only [TopologicalSpace.Opens.coe_iSup]
    exact t.isCompact_biUnion fun x hx => (hWa x (htK x hx)).isCompact
  · simpa only [TopologicalSpace.Opens.coe_iSup] using hcov

/-! ### The eventual immersion, for an index in the universe of the schemes -/

section UniverseTiedIndex

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
  {S Y : Scheme.{u}} (D : Iᵒᵖ ⥤ Scheme.{u}) (t : D ⟶ (Functor.const Iᵒᵖ).obj S)
  (c : Cone D) (hc : IsLimit c) (s : c.pt ⟶ S) (f : Y ⟶ c.pt)

include hc in
/-- Let `X = lim Xᵢ` be the limit of a directed inverse system of schemes over `S` whose
transition morphisms are affine.  If `f : Y ⟶ X` is an immersion, `Y` is quasi-compact and `Y`
is locally of finite type over `S`, then the composite `Y ⟶ Xᵢ` is an immersion for all
sufficiently large `i`.  This is Stacks 081B, part (2), with the quasi-separatedness of the
stages dropped. -/
theorem eventually_isImmersion_comp_π_app
    (hcomm : c.π ≫ t = (Functor.const Iᵒᵖ).map s)
    [∀ ⦃i j : I⦄ (h : i ≤ j), IsAffineHom (D.map (homOfLE h).op)]
    [CompactSpace Y] [LocallyOfFiniteType (f ≫ s)] [IsImmersion f] :
    ∀ᶠ i in atTop, IsImmersion (f ≫ c.π.app (op i)) := by
  classical
  have : ∀ {a b : Iᵒᵖ} (g : a ⟶ b), IsAffineHom (D.map g) := fun g => isAffineHom_map D g
  -- A quasi-compact open of the limit in which `Y` is closed, and its descent to a stage.
  obtain ⟨U, hUc, hRU, hUO⟩ := exists_isCompact_le_of_subset c.pt
    (isCompact_range f.continuous) f.coborderRange subset_coborder
  obtain ⟨⟨k⟩, V, hVc, hV⟩ := exists_preimage_eq D c hc U hUc
  let W : c.pt.Opens := c.π.app (op k) ⁻¹ᵁ V
  have hRW : Set.range f ⊆ W := by
    show Set.range f ⊆ ((c.π.app (op k) ⁻¹ᵁ V : c.pt.Opens) : Set c.pt)
    rwa [hV]
  -- The system of preimages of `V` in the stages above `k`, indexed by the tail above `k`.
  let E := limitTailOverEquiv k
  let D' := E.functor ⋙ preimageDiagram D (op k) V
  let c' : Cone D' := (preimageCone D c (op k) V).whisker E.functor
  have hc' : IsLimit c' :=
    (isLimitPreimageCone D c hc (op k) V).whiskerEquivalence E
  -- The open immersion of the cone point of `c'`, which is `W`, into the limit.
  let ιW : c'.pt ⟶ c.pt := W.ι
  have : IsOpenImmersion ιW := inferInstanceAs (IsOpenImmersion W.ι)
  let f' : Y ⟶ c'.pt := IsOpenImmersion.lift ιW f (by
    rwa [show Set.range ιW = (W : Set c.pt) from Scheme.Opens.range_ι W])
  have hf' : f' ≫ ιW = f := IsOpenImmersion.lift_fac _ _ _
  have hWO : W ≤ f.coborderRange := by
    show c.π.app (op k) ⁻¹ᵁ V ≤ f.coborderRange
    rwa [hV]
  let ιO : c'.pt ⟶ f.coborderRange := c.pt.homOfLE hWO
  have hcl : f' ≫ ιO = f.liftCoborder := by
    apply (cancel_mono f.coborderRange.ι).1
    rw [Category.assoc, show ιO ≫ f.coborderRange.ι = ιW from Scheme.homOfLE_ι _ _, hf',
      Scheme.Hom.liftCoborder_ι]
  have : IsOpenImmersion ιO := inferInstanceAs (IsOpenImmersion (c.pt.homOfLE hWO))
  have : IsClosedImmersion (f' ≫ ιO) := by
    rw [hcl]
    infer_instance
  have : IsClosedImmersion f' := IsClosedImmersion.of_comp f' ιO
  let t' : D' ⟶ (Functor.const (LimitTail I k)ᵒᵖ).obj S :=
    { app := fun j => (preimageDiagramι D (op k) V).app (E.functor.obj j) ≫
        t.app (E.functor.obj j).left
      naturality := fun j j' φ => by
        show ((preimageDiagram D (op k) V).map (E.functor.map φ) ≫
            (preimageDiagramι D (op k) V).app (E.functor.obj j')) ≫ t.app _ =
          ((preimageDiagramι D (op k) V).app (E.functor.obj j) ≫ t.app _) ≫ 𝟙 S
        have h2 : (Over.forget (op k) ⋙ D).map (E.functor.map φ) ≫ t.app _ = t.app _ :=
          (t.naturality (E.functor.map φ).left).trans (Category.comp_id _)
        rw [(preimageDiagramι D (op k) V).naturality (E.functor.map φ), Category.assoc, h2]
        exact (Category.comp_id _).symm }
  let s' : c'.pt ⟶ S := ιW ≫ s
  have hcomm' : c'.π ≫ t' = (Functor.const (LimitTail I k)ᵒᵖ).map s' := by
    refine NatTrans.ext (funext fun j => ?_)
    have h : c.π.app (E.functor.obj j).left ≫ t.app (E.functor.obj j).left = s := by
      simpa using congrArg (fun η => η.app (E.functor.obj j).left) hcomm
    show (c.π.app (E.functor.obj j).left).resLE _ _ _ ≫
        (Scheme.Opens.ι _ ≫ t.app (E.functor.obj j).left) = (W.ι ≫ s) ≫ 𝟙 S
    rw [← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc, h, Category.comp_id]
  have : ∀ j : LimitTail I k, CompactSpace (D'.obj (op j)) := fun j =>
    isCompact_iff_compactSpace.mp
      (QuasiCompact.isCompact_preimage (f := D.map (E.functor.obj (op j)).hom) _ V.2 hVc)
  have : ∀ ⦃i j : LimitTail I k⦄ (h : i ≤ j), IsAffineHom (D'.map (homOfLE h).op) :=
    fun _ _ h => inferInstanceAs
      (IsAffineHom ((preimageDiagram D (op k) V).map (E.functor.map (homOfLE h).op)))
  have : Nonempty (LimitTail I k) := ⟨⟨k, le_rfl⟩⟩
  have : IsDirected (LimitTail I k) (· ≤ ·) := by
    refine ⟨fun x y => ?_⟩
    obtain ⟨m, hxm, hym⟩ := IsDirected.directed (r := (· ≤ ·)) x.1 y.1
    exact ⟨⟨m, x.2.trans hxm⟩, hxm, hym⟩
  have hfs : f' ≫ s' = f ≫ s := by
    rw [← hf', Category.assoc]
  have : LocallyOfFiniteType (f' ≫ s') := by
    rw [hfs]
    infer_instance
  have hres := eventually_isClosedImmersion_comp_π_app D' t' c' hc' s' f' hcomm'
  obtain ⟨j₀, hj₀⟩ := eventually_atTop.1 hres
  refine eventually_atTop.2 ⟨j₀.1, fun i hi => ?_⟩
  let j : LimitTail I k := ⟨i, j₀.2.trans hi⟩
  have : IsClosedImmersion (f' ≫ c'.π.app (op j)) := hj₀ j hi
  let ιj : D'.obj (op j) ⟶ D.obj (op i) := (preimageDiagramι D (op k) V).app (E.functor.obj (op j))
  have : IsOpenImmersion ιj := inferInstanceAs
    (IsOpenImmersion ((preimageDiagramι D (op k) V).app (E.functor.obj (op j))))
  have h3 : c'.π.app (op j) ≫ ιj = ιW ≫ c.π.app (op i) := Scheme.Hom.resLE_comp_ι _ _
  have heq : f ≫ c.π.app (op i) = (f' ≫ c'.π.app (op j)) ≫ ιj := by
    rw [Category.assoc, h3, ← Category.assoc, hf']
  rw [heq]
  infer_instance

end UniverseTiedIndex

/-! ### Restricting an immersion onto an open containing its range -/

/-- A locally closed subset of a topological space containing `s` and contained in `coborder s`
is closed in the induced topology of any open set sandwiched between `s` and `coborder s`. -/
private lemma isClosed_preimage_val_of_subset_coborder {X : Type*} [TopologicalSpace X]
    {s U : Set X} (hsU : s ⊆ U) (hUc : U ⊆ coborder s) : IsClosed (U ↓∩ s) := by
  rw [isClosed_preimage_val, Set.inter_eq_right.mpr hsU]
  exact (Set.inter_subset_inter_left _ hUc).trans coborder_inter_closure.subset

variable {X Y : Scheme.{u}}

/-- The lift of a morphism along the inclusion of an open set containing its range. -/
private noncomputable def liftTo (f : X ⟶ Y) {U : Y.Opens} (hfU : Set.range f ⊆ (U : Set Y)) :
    X ⟶ U.toScheme :=
  IsOpenImmersion.lift U.ι f (by rwa [Scheme.Opens.range_ι])

@[reassoc (attr := simp)]
private lemma liftTo_ι (f : X ⟶ Y) {U : Y.Opens} (hfU : Set.range f ⊆ (U : Set Y)) :
    liftTo f hfU ≫ U.ι = f :=
  IsOpenImmersion.lift_fac _ _ _

/-- An immersion restricted to an open set containing its range and contained in its
`coborderRange` is a closed immersion.  This mirrors Mathlib's proof that `f.liftCoborder` is a
closed immersion, with the maximal open `f.coborderRange` replaced by `U`. -/
private lemma isClosedImmersion_liftTo (f : X ⟶ Y) [IsImmersion f] {U : Y.Opens}
    (hfU : Set.range f ⊆ (U : Set Y)) (hUc : U ≤ f.coborderRange) :
    IsClosedImmersion (liftTo f hfU) := by
  have : IsPreimmersion (liftTo f hfU ≫ U.ι) := by
    simp only [liftTo_ι]; infer_instance
  have : IsPreimmersion (liftTo f hfU) := .of_comp (liftTo f hfU) U.ι
  refine .of_isPreimmersion _ ?_
  have hrange : Set.range (liftTo f hfU).base = (U : Set Y) ↓∩ Set.range f.base := by
    apply Set.image_injective.mpr U.ι.isEmbedding.injective
    rw [← Set.range_comp, ← TopCat.coe_comp, ← Scheme.Hom.comp_base, liftTo_ι]
    exact (Set.image_preimage_eq_of_subset (by rwa [Scheme.Opens.range_ι])).symm
  rw [hrange]
  exact isClosed_preimage_val_of_subset_coborder hfU hUc

/-- The restriction of a morphism onto an open `U` equal to its full source `V`, when `U`
contains the range of the morphism, is the lift of the morphism onto `U` composed with the
canonical isomorphism of the full source with `V`. -/
private lemma resLE_top_eq_liftTo (f : X ⟶ Y) {U : Y.Opens} (hfU : Set.range f ⊆ (U : Set Y))
    (e : (⊤ : X.Opens) ≤ f ⁻¹ᵁ U) :
    f.resLE U ⊤ e = X.topIso.hom ≫ liftTo f hfU := by
  rw [← cancel_mono U.ι, Scheme.Hom.resLE_comp_ι, Category.assoc, liftTo_ι]
  rfl

/-- A morphism restricted (via `morphismRestrict`) onto an open set containing its range is a
closed immersion exactly when its lift onto that open set is. -/
private lemma isClosedImmersion_morphismRestrict_iff_liftTo (f : X ⟶ Y) {U : Y.Opens}
    (hfU : Set.range f ⊆ (U : Set Y)) :
    IsClosedImmersion (f ∣_ U) ↔ IsClosedImmersion (liftTo f hfU) := by
  have hfpre : f ⁻¹ᵁ U = ⊤ := top_le_iff.mp fun x _ => hfU ⟨x, rfl⟩
  rw [← Scheme.Hom.resLE_eq_morphismRestrict,
    Scheme.Hom.resLE_congr f _ rfl hfpre (@IsClosedImmersion), resLE_top_eq_liftTo f hfU _]
  exact MorphismProperty.cancel_left_of_respectsIso (@IsClosedImmersion) X.topIso.hom _

/-- An immersion restricted (via `morphismRestrict`) onto an open set containing its range and
contained in its `coborderRange` is a closed immersion. -/
private lemma isClosedImmersion_morphismRestrict_of_subset_coborderRange
    (f : X ⟶ Y) [IsImmersion f] {U : Y.Opens}
    (hfU : Set.range f ⊆ (U : Set Y)) (hUc : U ≤ f.coborderRange) :
    IsClosedImmersion (f ∣_ U) := by
  exact (isClosedImmersion_morphismRestrict_iff_liftTo f hfU).2 (isClosedImmersion_liftTo f hfU hUc)

/-! ### Transporting closedness between nested restrictions -/

/-- Restricting a morphism onto `U` and then onto the preimage of `W ≤ U` in `U` is a closed
immersion exactly when the direct restriction onto `W` is. -/
private lemma isClosedImmersion_morphismRestrict_restrict_iff (f : X ⟶ Y) {U W : Y.Opens}
    (hWU : W ≤ U) :
    IsClosedImmersion ((f ∣_ U) ∣_ (U.ι ⁻¹ᵁ W)) ↔ IsClosedImmersion (f ∣_ W) := by
  have himg : U.ι ''ᵁ (U.ι ⁻¹ᵁ W) = W := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
      inf_eq_right.mpr hWU]
  rw [MorphismProperty.arrow_mk_iso_iff (P := @IsClosedImmersion)
    (morphismRestrictRestrict f U (U.ι ⁻¹ᵁ W)), himg]

/-! ### From a closed immersion on an open containing the range to an immersion -/

/-- If a family of opens with supremum `U` is pulled back along the inclusion of `U`, the
pullbacks cover all of the subscheme `U` defines. -/
private lemma iSup_preimage_ι_eq_top {U : Y.Opens} {ι : Type*} (Vfam : ι → Y.Opens)
    (hVU : (⨆ i, Vfam i) = U) : (⨆ i, U.ι ⁻¹ᵁ Vfam i) = ⊤ := by
  rw [← Scheme.Hom.preimage_iSup, hVU]
  exact U.ι_preimage_self

/-- If a morphism restricted (via `morphismRestrict`) onto an open `U` containing its range is a
closed immersion, the morphism itself is an immersion. -/
private lemma isImmersion_of_isClosedImmersion_morphismRestrict (g : X ⟶ Y) {U : Y.Opens}
    (hgU : Set.range g ⊆ (U : Set Y)) (hg : IsClosedImmersion (g ∣_ U)) : IsImmersion g := by
  have := (isClosedImmersion_morphismRestrict_iff_liftTo g hgU).1 hg
  rw [← liftTo_ι g hgU]
  infer_instance

/-! ### A global-sections identity -/

/-- The structure map of a restriction, viewed through the identification of global sections
with sections over the full open, is the corresponding `appLE`. -/
private lemma appLE_eq_topIso_inv_comp_resLE_appTop (f : X ⟶ Y) (U : Y.Opens) (V : X.Opens)
    (e : V ≤ f ⁻¹ᵁ U) :
    f.appLE U V e = U.topIso.inv ≫ (f.resLE U V e).appTop ≫ V.topIso.hom := by
  have hw : U.topIso.hom ≫ f.appLE U V e = (f.resLE U V e).appTop ≫ V.topIso.hom :=
    (arrowResLEAppIso f U V e).hom.w
  rw [← hw, Iso.inv_hom_id_assoc]

/-! ### The setting -/

variable {I : Type v} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
  {S : Scheme.{u}} (D : Iᵒᵖ ⥤ Scheme.{u}) (t : D ⟶ (Functor.const Iᵒᵖ).obj S)
  (c : Cone D) (hc : IsLimit c) (s : c.pt ⟶ S) (f : Y ⟶ c.pt)

include hc in
/-- The preimages, in the limit, of the affine opens of the stages form a basis of its
topology.  Used to locate a given quasi-compact open of the limit as the preimage of a
quasi-compact open of some stage, below. -/
private lemma isBasis_preimage_isAffineOpen
    [∀ ⦃i j : I⦄ (h : i ≤ j), IsAffineHom (D.map (homOfLE h).op)] :
    TopologicalSpace.Opens.IsBasis
      { (c.π.app i ⁻¹ᵁ V : c.pt.Opens) | (i : Iᵒᵖ) (V : (D.obj i).Opens)
        (_ : IsAffineOpen V) } := by
  classical
  have hah : ∀ {a b : Iᵒᵖ} (g : a ⟶ b), IsAffineHom (D.map g) := fun g => isAffineHom_map D g
  refine TopologicalSpace.Opens.isBasis_iff_nbhd.mpr fun {U x} hxU => ?_
  obtain ⟨i⟩ := IsCofiltered.nonempty (C := Iᵒᵖ)
  have : IsCofiltered (Over i) := inferInstance
  have : IsFiltered (Over i)ᵒᵖ := inferInstance
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    (D.obj i).isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (c.π.app i x)) isOpen_univ
  have hEaff : ∀ j, IsAffine ((preimageDiagram D i V).obj j) := isAffine_preimageDiagram_obj D i hV
  have : ∀ j : (Over i)ᵒᵖ, IsAffine ((preimageDiagram D i V).op.obj j).unop := fun j => hEaff j.unop
  have : PreservesColimit (preimageDiagram D i V).op Scheme.Γ :=
    preservesColimit_Γ (D := (preimageDiagram D i V).op)
  have hΓ : IsColimit (Scheme.Γ.mapCocone (preimageCone D c i V).op) :=
    isColimitOfPreserves Scheme.Γ (isLimitPreimageCone D c hc i V).op
  obtain ⟨r, hrU, hxr⟩ := (isAffineOpen_preimage_π_app D c hc i hV).exists_basicOpen_le
    (V := U) ⟨x, hxU⟩ hxV
  obtain ⟨j, s, hs⟩ := exists_ι_app_eq hΓ ((c.π.app i ⁻¹ᵁ V).topIso.inv r)
  obtain ⟨s, rfl⟩ := (D.map j.unop.hom ⁻¹ᵁ V).topIso.symm.commRingCatIsoToRingEquiv.surjective s
  have h : c.π.app j.unop.left ⁻¹ᵁ D.map j.unop.hom ⁻¹ᵁ V = c.π.app i ⁻¹ᵁ V :=
    congr($(c.w j.unop.hom) ⁻¹ᵁ V)
  have hres : r = (c.π.app j.unop.left).appLE (D.map j.unop.hom ⁻¹ᵁ V)
      (c.π.app i ⁻¹ᵁ V) h.ge s := by
    convert! show r = ((D.map j.unop.hom ⁻¹ᵁ V).topIso.inv ≫
      ((preimageCone D c i V).π.app j.unop).appTop ≫
      (c.π.app i ⁻¹ᵁ V).topIso.hom) s from
      (c.π.app i ⁻¹ᵁ V).topIso.commRingCatIsoToRingEquiv.symm_apply_eq.mp hs.symm using 3
    simp only [preimageCone]
    exact appLE_eq_topIso_inv_comp_resLE_appTop _ _ _ _
  refine ⟨_, ⟨j.unop.left, _, (hV.preimage _).basicOpen s, rfl⟩, ?_⟩
  simp only [Functor.const_obj_obj, Scheme.preimage_basicOpen] at hres ⊢
  rw [← c.pt.basicOpen_res_eq _ (eqToHom h.symm).op, ← CommRingCat.comp_apply,
    Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map, ← hres]
  exact ⟨hxr, hrU⟩

include hc in
/-- **Stacks 01Z4 (1), with the index-object universe freed.**  A quasi-compact open of the
limit is the preimage of a quasi-compact open of some stage.  Mathlib's
`AlgebraicGeometry.exists_preimage_eq'` carries the same content but ties the universe of the
index *objects* to the universe of the schemes; the self-contained argument here, via
`isBasis_preimage_isAffineOpen`, does not. -/
private lemma exists_preimage_eq_free
    [∀ ⦃i j : I⦄ (h : i ≤ j), IsAffineHom (D.map (homOfLE h).op)]
    (U : c.pt.Opens) (hU : IsCompact (U : Set c.pt)) :
    ∃ (i : Iᵒᵖ) (V : (D.obj i).Opens), IsCompact (V : Set (D.obj i)) ∧
      c.π.app i ⁻¹ᵁ V = U := by
  classical
  have hah : ∀ {a b : Iᵒᵖ} (g : a ⟶ b), IsAffineHom (D.map g) := fun g => isAffineHom_map D g
  obtain ⟨s, hs, hsf, rfl⟩ := (isBasis_preimage_isAffineOpen D c hc).exists_finite_of_isCompact hU
  have : Finite s := hsf
  choose i V hV hVi using fun x : s => hs x.2
  obtain ⟨j, fj⟩ := IsCofiltered.inf_objs_exists (hsf.toFinset.attach.image
    fun x => i ⟨x.1, by simpa only [Set.Finite.mem_toFinset] using x.2⟩ :)
  replace fj : ∀ b : s, j ⟶ i b := fun b =>
    (@fj (i b) (by simpa using ⟨b.1, b.2, rfl⟩)).some
  refine ⟨j, ⨆ (k : s), D.map (fj _) ⁻¹ᵁ V k, ?_, ?_⟩
  · simp only [TopologicalSpace.Opens.iSup_mk, TopologicalSpace.Opens.carrier_eq_coe,
      TopologicalSpace.Opens.map_coe, TopologicalSpace.Opens.coe_mk]
    exact isCompact_iUnion fun i => ((hV i).preimage _).isCompact
  · simp [-TopologicalSpace.Opens.iSup_mk, Scheme.Hom.preimage_iSup,
      ← Scheme.Hom.comp_preimage, c.w, hVi, sSup_eq_iSup']

include hc in
/-- The affine-local heart of Tag 081B (2): on an affine open `V` of a stage `i₀`, whose
preimage in the limit lies inside a fixed open `Ubig` on which `f` restricts to a closed
immersion, the restriction of `Y ⟶ Xⱼ` onto the preimage of `V` is a closed immersion for all
sufficiently late stages `j`. -/
private lemma exists_isClosedImmersion_morphismRestrict_of_subset
    [∀ ⦃i j : I⦄ (h : i ≤ j), IsAffineHom (D.map (homOfLE h).op)]
    (hcomm : c.π ≫ t = (Functor.const Iᵒᵖ).map s)
    [LocallyOfFiniteType (f ≫ s)]
    {Ubig : c.pt.Opens} (hUbig : IsClosedImmersion (f ∣_ Ubig))
    (i₀ : I) {V : (D.obj (op i₀)).Opens} (hV : IsAffineOpen V)
    (hVU : c.π.app (op i₀) ⁻¹ᵁ V ≤ Ubig) :
    ∃ k₁ : Over (op i₀), ∀ (k : Over (op i₀)) (_ : k ⟶ k₁),
      IsClosedImmersion ((f ≫ c.π.app k.left) ∣_ (D.map k.hom ⁻¹ᵁ V)) := by
  have hah : ∀ {a b : Iᵒᵖ} (g : a ⟶ b), IsAffineHom (D.map g) := fun g => isAffineHom_map D g
  have hd : IsLimit (preimageCone D c (op i₀) V) := isLimitPreimageCone D c hc (op i₀) V
  have hEaff : ∀ k, IsAffine ((preimageDiagram D (op i₀) V).obj k) :=
    isAffine_preimageDiagram_obj D (op i₀) hV
  have hφ : IsClosedImmersion (f.resLE (c.π.app (op i₀) ⁻¹ᵁ V)
      (f ⁻¹ᵁ (c.π.app (op i₀) ⁻¹ᵁ V)) le_rfl) := by
    rw [Scheme.Hom.resLE_eq_morphismRestrict]
    exact (isClosedImmersion_morphismRestrict_restrict_iff f hVU).1
      (IsZariskiLocalAtTarget.restrict (P := @IsClosedImmersion) hUbig _)
  have hpre : ∀ k : Over (op i₀),
      c.π.app k.left ⁻¹ᵁ (D.map k.hom ⁻¹ᵁ V) = c.π.app (op i₀) ⁻¹ᵁ V := fun k => by
    rw [← Scheme.Hom.comp_preimage, c.w]
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
    rw [Scheme.Hom.resLE_comp_resLE]
    exact hχ
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
  rw [← Scheme.Hom.resLE_eq_morphismRestrict,
    Scheme.Hom.resLE_congr (f ≫ c.π.app k.left) _ rfl heq (@IsClosedImmersion)]
  exact hcl

/-! ### The eventual immersion -/

include hc in
/-- **Stacks 081B (2).** Let `X = lim Xᵢ` be the limit of a directed inverse system of schemes
over `S` whose transition morphisms are affine and whose stages are quasi-separated. If
`f : Y ⟶ X` is an immersion, `Y` is locally of finite type over `S`, and `Y` is quasi-compact,
then the composite `Y ⟶ Xᵢ` is an immersion for all sufficiently large `i`.

These are exactly the source's hypotheses, and the index type `I` is in a universe unrelated to
that of the schemes.  `AlgebraicGeometry.EventualLimit.eventually_isImmersion_comp_π_app` drops
the quasi-separatedness of the stages but ties `I` to the universe of the schemes, which is where
Mathlib's `AlgebraicGeometry.exists_preimage_eq` applies. -/
@[stacks 081B "part (2)"]
theorem eventually_isImmersion_comp_π_app_of_quasiSeparatedSpace
    (hcomm : c.π ≫ t = (Functor.const Iᵒᵖ).map s)
    [∀ i : I, QuasiSeparatedSpace (D.obj (op i))]
    [∀ ⦃i j : I⦄ (h : i ≤ j), IsAffineHom (D.map (homOfLE h).op)]
    [LocallyOfFiniteType (f ≫ s)] [IsImmersion f] [CompactSpace Y] :
    ∀ᶠ i in atTop, IsImmersion (f ≫ c.π.app (op i)) := by
  classical
  have hah : ∀ {a b : Iᵒᵖ} (g : a ⟶ b), IsAffineHom (D.map g) := fun g => isAffineHom_map D g
  -- cover `Y` by finitely many affine opens of `c.pt`, each inside the coborder of `f`
  have hcov : ∀ y : Y, ∃ V : c.pt.Opens, IsAffineOpen V ∧ y ∈ f ⁻¹ᵁ V ∧ V ≤ f.coborderRange :=
    fun y => exists_isAffineOpen_mem_le (O := f.coborderRange) (subset_coborder ⟨y, rfl⟩)
  choose V hV hyV hVc using hcov
  obtain ⟨σ, hσ⟩ := isCompact_univ.elim_finite_subcover
    (fun y : Y => ((f ⁻¹ᵁ (V y) : Y.Opens) : Set Y)) (fun y => (f ⁻¹ᵁ (V y)).isOpen)
    (fun z _ => Set.mem_iUnion.mpr ⟨z, hyV z⟩)
  -- assemble the finitely many charts into a single quasi-compact open `Ubig`
  set Ubig : c.pt.Opens := ⨆ y : {y // y ∈ σ}, V y.1 with hUbigdef
  have hUbigrange : Set.range f ⊆ (Ubig : Set c.pt) := by
    rintro _ ⟨y, rfl⟩
    obtain ⟨z, hz, hy⟩ := Set.mem_iUnion₂.mp (hσ (Set.mem_univ y))
    exact Opens.mem_iSup.mpr ⟨⟨z, hz⟩, hy⟩
  have hUbigc : Ubig ≤ f.coborderRange := iSup_le fun y => hVc y.1
  have hUbigcompact : IsCompact (Ubig : Set c.pt) := by
    rw [hUbigdef, Opens.coe_iSup]
    exact isCompact_iUnion fun y => (hV y.1).isCompact
  have hUbigcl : IsClosedImmersion (f ∣_ Ubig) :=
    isClosedImmersion_morphismRestrict_of_subset_coborderRange f hUbigrange hUbigc
  -- `Ubig` is the preimage of a quasi-compact open of some stage
  obtain ⟨j₀, U₀, hU₀compact, hU₀eq⟩ := exists_preimage_eq_free D c hc Ubig hUbigcompact
  -- cover `U₀` by finitely many affine opens
  have hcov₀ : ∀ x : (U₀ : Set (D.obj j₀)), ∃ W : (D.obj j₀).Opens, IsAffineOpen W ∧
      (x : D.obj j₀) ∈ W ∧ W ≤ U₀ :=
    fun x => exists_isAffineOpen_mem_le (O := U₀) x.2
  choose W hW hxW hWU₀ using hcov₀
  obtain ⟨σ₀, hσ₀⟩ := hU₀compact.elim_finite_subcover
    (fun x : (U₀ : Set (D.obj j₀)) => (W x : Set (D.obj j₀))) (fun x => (W x).isOpen)
    (fun z hz => Set.mem_iUnion.mpr ⟨⟨z, hz⟩, hxW ⟨z, hz⟩⟩)
  -- the per-chart late indices, at the index `i₀ := j₀.unop` of `I`
  set i₀ : I := j₀.unop with hi₀def
  have hchart : ∀ x : (U₀ : Set (D.obj j₀)), ∃ k₁ : Over (op i₀), ∀ (k : Over (op i₀)) (_ : k ⟶ k₁),
      IsClosedImmersion ((f ≫ c.π.app k.left) ∣_ (D.map k.hom ⁻¹ᵁ W x)) := by
    intro x
    have hVU : c.π.app (op i₀) ⁻¹ᵁ W x ≤ Ubig := by
      have : c.π.app (op i₀) ⁻¹ᵁ W x = c.π.app j₀ ⁻¹ᵁ W x := rfl
      rw [this, ← hU₀eq]
      exact (c.π.app j₀).preimage_mono (hWU₀ x)
    exact exists_isClosedImmersion_morphismRestrict_of_subset D t c hc s f hcomm hUbigcl i₀
      (hW x) hVU
  choose k₁ hk₁ using hchart
  obtain ⟨i₁, hi₁⟩ := (insert i₀ (σ₀.image fun x => (k₁ x).left.unop)).exists_le
  rw [eventually_atTop]
  refine ⟨i₁, fun i hi => ?_⟩
  have hi₀i : i₀ ≤ i := (hi₁ i₀ (Finset.mem_insert_self _ _)).trans hi
  -- the charts of `U₀`, pulled back to stage `i`, cover the preimage of `U₀` at stage `i`
  set Ui : (D.obj (op i)).Opens := D.map (homOfLE hi₀i).op ⁻¹ᵁ U₀ with hUidef
  have hUicover : (⨆ x : {x // x ∈ σ₀}, D.map (homOfLE hi₀i).op ⁻¹ᵁ (W x.1)) = Ui := by
    rw [hUidef]
    refine le_antisymm (iSup_le fun x => (D.map (homOfLE hi₀i).op).preimage_mono (hWU₀ x.1)) ?_
    intro z hz
    obtain ⟨x, hx, hy⟩ :=
      Set.mem_iUnion₂.mp (hσ₀ (hz : (D.map (homOfLE hi₀i).op).base z ∈ (U₀ : Set (D.obj j₀))))
    exact Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hy⟩
  have hUicovertop : (⨆ x : {x // x ∈ σ₀}, Ui.ι ⁻¹ᵁ (D.map (homOfLE hi₀i).op ⁻¹ᵁ (W x.1))) = ⊤ :=
    iSup_preimage_ι_eq_top _ hUicover
  -- the restriction to the preimage of `U₀` at stage `i` is a closed immersion, by gluing
  have hUicl : IsClosedImmersion ((f ≫ c.π.app (op i)) ∣_ Ui) := by
    refine IsZariskiLocalAtTarget.of_iSup_eq_top (P := @IsClosedImmersion) _ hUicovertop
      fun x => ?_
    have hle : (k₁ x.1).left.unop ≤ i :=
      (hi₁ _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ x.2))).trans hi
    have hk : (Over.mk (homOfLE hi₀i).op : Over (op i₀)) ⟶ k₁ x.1 :=
      Over.homMk ((homOfLE hle).op) (Subsingleton.elim _ _)
    have hcl := hk₁ x.1 (Over.mk (homOfLE hi₀i).op) hk
    have hchartle : D.map (homOfLE hi₀i).op ⁻¹ᵁ (W x.1) ≤ Ui :=
      (D.map (homOfLE hi₀i).op).preimage_mono (hWU₀ x.1)
    exact (isClosedImmersion_morphismRestrict_restrict_iff (f ≫ c.π.app (op i)) hchartle).2 hcl
  -- the range of `f ≫ c.π.app (op i)` lies inside `Ui`
  have hcomprange : Set.range (f ≫ c.π.app (op i)) ⊆ (Ui : Set (D.obj (op i))) := by
    have hpreq : c.π.app (op i) ⁻¹ᵁ Ui = Ubig := by
      rw [hUidef, ← Scheme.Hom.comp_preimage, c.w (homOfLE hi₀i).op]
      exact hU₀eq
    rintro _ ⟨y, rfl⟩
    show y ∈ (f ≫ c.π.app (op i)) ⁻¹ᵁ Ui
    rw [Scheme.Hom.comp_preimage, hpreq]
    exact hUbigrange ⟨y, rfl⟩
  exact isImmersion_of_isClosedImmersion_morphismRestrict (f ≫ c.π.app (op i)) hcomprange hUicl

end EventualLimit

end AlgebraicGeometry

end
