module

public import StacksFrontier.AlgebraicGeometry.EventualLimitProperties.Isomorphism
public import StacksFrontier.AlgebraicGeometry.FiniteAlgebraLimitPresentation.Basic
public import StacksFrontier.AlgebraicGeometry.FiniteFactorization.FromSubalgebra
public import StacksFrontier.AlgebraicGeometry.FiniteSubalgebra.Basic
public import StacksFrontier.AlgebraicGeometry.FiniteTypeSubalgebraFiltered.Basic
public import StacksFrontier.AlgebraicGeometry.SubalgebraGeneratedByModule.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Zariski's Main Theorem: the finite factorization

Let `f : X ⟶ S` be a quasi-finite separated morphism of schemes with `S` quasi-compact and
quasi-separated.  Then `f` factors as a quasi-compact open immersion followed by a finite
morphism.  This is [Stacks, Tag 05K0].

If `f` is moreover locally of finite presentation, the finite morphism may be chosen to be of
finite presentation as well.  This is [Stacks, Tag 0F2N].

## Main results

* `Stacks.FiniteFactorization.exists_isOpenImmersion_isFinite_factorization`: the
  factorization.
* `Stacks.FiniteFactorization.exists_isOpenImmersion_isFinite_finitePresentation_factorization`:
  **[Stacks, Tag 0F2N]** — the factorization with the finite morphism of finite presentation.

## Implementation notes

All of the geometry is in
`StacksFrontier.AlgebraicGeometry.FiniteFactorization.FromSubalgebra`, which proves the
factorization from the one input it needs about the relative normalization `ν : S' ⟶ S` of `S`
in `X`: that every finite family of sections of `ν_* 𝒪` over affine opens of `S` is reached by
a *finite* quasi-coherent subalgebra of `ν_* 𝒪`.  This file supplies that input, which is where
quasi-separatedness of `S` is used, and states the tag.

The input is assembled from two existing results.  A single section over a single affine open is
reached by a finite type quasi-coherent subalgebra by
`Stacks.AlgebraicGeometry.SubalgebraGeneratedByModule.exists_finiteTypeSubalgebra_section`, and
for an integral algebra sheaf a finite type quasi-coherent subalgebra is finite, so
`Stacks.AlgebraicGeometry.FiniteSubalgebras.exists_finiteSubalgebra_section_iff` reads that as a
statement about finite subalgebras.  Finitely many of those are then dominated by a single one
because the finite quasi-coherent subalgebras of an integral quasi-coherent algebra sheaf form a
filtered category, which is the directedness assertion of [Stacks, Tag 0817]
(`Stacks.AlgebraicGeometry.FiniteSubalgebras.isFiltered_finiteSubalgebra`); a section reached by
a subalgebra is reached by any subalgebra dominating it, because a morphism of subobjects
commutes with their inclusions into the ambient algebra sheaf.

No inverse limit of schemes is formed anywhere: the comparison morphism `S' ⟶ Spec_S B` of the
geometric half comes from the universal property of the relative spectrum against an arbitrary
scheme over `S`, so only the colimit of algebra sheaves that [Stacks, Tag 0817] provides is
needed.

The refinement [Stacks, Tag 0F2N] does form such a limit, but only for the finite morphism `π`
produced by Tag 05K0.  By [Stacks, Tag 09YY] that morphism is the inverse limit of a directed
system `{ πᵢ : Tᵢ ⟶ S }` of morphisms finite and of finite presentation whose transition maps
are closed immersions.  The open `j(X) ⊆ T` is quasi-compact, so it descends to a
quasi-compact open `V ⊆ Tᵢ` at some stage, and the preimages of `V` in the later stages form a
system whose limit is `j(X) ≅ X`.  Since `X` is locally of finite presentation over `S` while
those preimages are only locally of finite type over `S`, [Stacks, Tag 081B] makes
`X ⟶ (πᵢ')⁻¹(V)` an isomorphism at some later stage `i'`, and `Tᵢ'` is then the required `T`.

The index category of the system of preimages is the category of objects of the index preorder
over the stage `i`, whereas Tag 081B is stated for a system indexed by a directed preorder;
`Stacks.FiniteFactorization.opIciEquivOver` identifies the two.

## References

* [Stacks Project, Tag 05K0](https://stacks.math.columbia.edu/tag/05K0)
* [Stacks Project, Tag 0F2N](https://stacks.math.columbia.edu/tag/0F2N)
* [Stacks Project, Tag 09YY](https://stacks.math.columbia.edu/tag/09YY)
* [Stacks Project, Tag 081B](https://stacks.math.columbia.edu/tag/081B)
* [Stacks Project, Tag 02LR](https://stacks.math.columbia.edu/tag/02LR)
* [Stacks Project, Tag 0817](https://stacks.math.columbia.edu/tag/0817)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.AffineAlgebraEquivalence Stacks.RelativeSpec Stacks.AlgebraicGeometry

universe u

namespace Stacks.FiniteFactorization

/-- **Zariski's Main Theorem (Stacks Project, Tag 05K0).**  A quasi-finite separated morphism
`f : X ⟶ S` onto a quasi-compact quasi-separated scheme factors as a quasi-compact open
immersion `j : X ⟶ T` followed by a finite morphism `π : T ⟶ S`.

Quasi-finiteness is Stacks 02NG, that is, locally quasi-finite and of finite type, which in
Mathlib's vocabulary is `AlgebraicGeometry.LocallyQuasiFinite`,
`AlgebraicGeometry.LocallyOfFiniteType` and `AlgebraicGeometry.QuasiCompact` together.

The affine case of the factorization, [Stacks, Tag 03GU], is
`AlgebraicGeometry.exists_isOpenImmersion_isFinite_factorization`; it is a different statement
and is not used here. -/
@[stacks 05K0,
  ega "III 4.4.12" "Quasi-finite case",
  ega "III 4.4.3" "more general",
  ega "III 4.4.5" "special case",
  ega "IV 18.12.13"]
theorem exists_isOpenImmersion_isFinite_factorization {X S : Scheme.{u}} (f : X ⟶ S)
    [IsSeparated f] [LocallyQuasiFinite f] [LocallyOfFiniteType f] [QuasiCompact f]
    [CompactSpace S] [QuasiSeparatedSpace S] :
    ∃ (T : Scheme.{u}) (j : X ⟶ T) (π : T ⟶ S),
      IsOpenImmersion j ∧ QuasiCompact j ∧ IsFinite π ∧ f = j ≫ π := by
  classical
  refine exists_isOpenImmersion_isFinite_factorization_of_exists_finiteSubalgebra f ?_
  intro Ξ hΞ W hW s
  have := hΞ
  have hAqc : AlgebraSheaf.IsQuasicoherent (pushforwardAlgebra f.fromNormalization) :=
    isQuasicoherent_pushforwardAlgebra f.fromNormalization
  have hAint : AlgebraSheaf.IsIntegral (pushforwardAlgebra f.fromNormalization) :=
    fun U hU => IsIntegralHom.isIntegral_app f.fromNormalization U hU
  have hsec : ∀ x : Ξ,
      ∃ (Bs : FiniteSubalgebras.FiniteSubalgebra (pushforwardAlgebra f.fromNormalization))
        (y : (Bs.obj : AlgebraSheaf S).right.obj.obj (op (W x))),
        Bs.obj.arrow.right.hom.app (op (W x)) y = s x :=
    fun x => (FiniteSubalgebras.exists_finiteSubalgebra_section_iff hAint (s x)).mpr
      (SubalgebraGeneratedByModule.exists_finiteTypeSubalgebra_section _ hAqc (W x) (hW x) (s x))
  choose Bs y hy using hsec
  have hfil := FiniteSubalgebras.isFiltered_finiteSubalgebra
    (pushforwardAlgebra f.fromNormalization) hAqc hAint
  have := Fintype.ofFinite Ξ
  obtain ⟨m, hm⟩ := IsFiltered.sup_objs_exists (Finset.image Bs Finset.univ)
  refine ⟨(m.obj : AlgebraSheaf S), m.property.1, m.property.2, m.obj.arrow, fun x => ?_⟩
  obtain ⟨u⟩ := hm (Finset.mem_image_of_mem Bs (Finset.mem_univ x))
  refine ⟨(Subobject.underlying.map u.hom).right.hom.app (op (W x)) (y x), ?_⟩
  have harr : Subobject.underlying.map u.hom ≫ m.obj.arrow = (Bs x).obj.arrow :=
    Subobject.underlying_arrow u.hom
  calc (m.obj.arrow.right.hom.app (op (W x))).hom
        ((Subobject.underlying.map u.hom).right.hom.app (op (W x)) (y x))
      = ((Subobject.underlying.map u.hom ≫ m.obj.arrow).right.hom.app (op (W x))) (y x) := rfl
    _ = ((Bs x).obj.arrow.right.hom.app (op (W x))) (y x) := by rw [harr]
    _ = s x := hy x

section FinitePresentation

open AlgebraicGeometry.EventualLimit Stacks.FiniteAlgebraLimitPresentation

universe v

/-- For an index `i` of the opposite of a preorder `P`, the opposite of the upper set
`{a // i.unop ≤ a}` is equivalent to the category of objects of `Pᵒᵖ` over `i`.  Both
categories are preorders in which `a` precedes `b` exactly when `b ≤ a` in `P`, so the
comparison functors are mutually inverse and every coherence is a proof of a proposition. -/
noncomputable def opIciEquivOver {P : Type v} [Preorder P] (i : Pᵒᵖ) :
    {a : P // i.unop ≤ a}ᵒᵖ ≌ Over i where
  functor :=
    { obj a := Over.mk (homOfLE a.unop.2).op
      map f := Over.homMk (homOfLE (leOfHom f.unop)).op (Subsingleton.elim _ _)
      map_id _ := Over.OverMorphism.ext (Subsingleton.elim _ _)
      map_comp _ _ := Over.OverMorphism.ext (Subsingleton.elim _ _) }
  inverse :=
    { obj A := op ⟨A.left.unop, leOfHom A.hom.unop⟩
      map f := (homOfLE (leOfHom f.left.unop)).op
      map_id _ := Subsingleton.elim _ _
      map_comp _ _ := Subsingleton.elim _ _ }
  unitIso := NatIso.ofComponents (fun a => eqToIso (by cases a; rfl)) (by intros; rfl)
  counitIso :=
    NatIso.ofComponents (fun A => Over.isoMk (Iso.refl _) (Subsingleton.elim _ _))
      (by intros; rfl)

/-- **Zariski's Main Theorem with finite presentation (Stacks Project, Tag 0F2N).**  Let
`f : X ⟶ S` be a quasi-finite separated morphism onto a quasi-compact quasi-separated scheme,
and assume in addition that `f` is locally of finite presentation.  Then the factorization of
[Stacks, Tag 05K0] into a quasi-compact open immersion `j : X ⟶ T` followed by a finite
morphism `π : T ⟶ S` may be chosen with `π` of finite presentation as well.

Quasi-finiteness is Stacks 02NG, as for Tag 05K0: `AlgebraicGeometry.LocallyQuasiFinite`,
`AlgebraicGeometry.LocallyOfFiniteType` and `AlgebraicGeometry.QuasiCompact` together.  Finite
presentation of `π` is `AlgebraicGeometry.FinitePresentation`, part (3) of [Stacks, Tag 01TP];
for a finite, hence affine, morphism it is the same as being locally of finite presentation,
so this is the tag's "finite and of finite presentation over `S`". -/
@[stacks 0F2N,
  ega "III 4.4.12" "Quasi-finite case",
  ega "III 4.4.3" "more general",
  ega "III 4.4.5" "special case",
  ega "IV 18.12.13" "special case",
  ega "IV 8.12.6"]
theorem exists_isOpenImmersion_isFinite_finitePresentation_factorization
    {X S : Scheme.{u}} (f : X ⟶ S)
    [IsSeparated f] [LocallyQuasiFinite f] [LocallyOfFiniteType f] [QuasiCompact f]
    [LocallyOfFinitePresentation f] [CompactSpace S] [QuasiSeparatedSpace S] :
    ∃ (T : Scheme.{u}) (j : X ⟶ T) (π : T ⟶ S),
      IsOpenImmersion j ∧ QuasiCompact j ∧ IsFinite π ∧ FinitePresentation π ∧ f = j ≫ π := by
  classical
  obtain ⟨T₀, j₀, π₀, hj₀, hj₀qc, hπ₀, hfac⟩ :=
    exists_isOpenImmersion_isFinite_factorization f
  have : IsOpenImmersion j₀ := hj₀
  have : QuasiCompact j₀ := hj₀qc
  have : IsFinite π₀ := hπ₀
  have : CompactSpace T₀ := QuasiCompact.compactSpace_of_compactSpace π₀
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace j₀
  have hU : IsCompact (j₀.opensRange : Set T₀) := isCompact_range j₀.continuous
  -- the limit presentation of the finite morphism `π₀` by finitely presented stages
  let L := finiteLimitPresentationOfIsFinite π₀
  let _ : Preorder L.indexType := L.indexPreorder
  have : Nonempty L.indexType := L.indexNonempty
  have : IsDirected L.indexType (· ≤ ·) := L.indexDirected
  have hclo : ∀ ⦃a b : L.indexType⦄ (h : a ≤ b),
      IsClosedImmersion (L.diagram.map (homOfLE h).op) :=
    fun {_ _} h => L.transitionClosed h
  have : ∀ {a b : L.indexTypeᵒᵖ} (g : a ⟶ b), IsClosedImmersion (L.diagram.map g) :=
    fun g => isClosedImmersion_map L.diagram g
  let c : Cone L.diagram := Cone.mk T₀ L.limitCone
  have hc : IsLimit c := L.isLimit
  obtain ⟨i, V, hV, hVU⟩ := L.compactOpenDescends j₀.opensRange hU
  -- the open `range j₀ ⊆ T₀` is the limit of the preimages of `V` in the stages over `i`
  have hcV : IsLimit (preimageCone L.diagram c i V) := isLimitPreimageCone L.diagram c hc i V
  let J := {a : L.indexType // i.unop ≤ a}
  have : Nonempty J := ⟨⟨i.unop, le_rfl⟩⟩
  have : IsDirected J (· ≤ ·) :=
    ⟨fun a b => by
      obtain ⟨k, hak, hbk⟩ := directed_of (· ≤ ·) a.1 b.1
      exact ⟨⟨k, a.2.trans hak⟩, hak, hbk⟩⟩
  let e : Jᵒᵖ ≌ Over i := opIciEquivOver i
  let D' : Jᵒᵖ ⥤ Scheme.{u} := e.functor ⋙ preimageDiagram L.diagram i V
  let tOver : preimageDiagram L.diagram i V ⟶ (Functor.const (Over i)).obj S :=
    preimageDiagramι L.diagram i V ≫ Functor.whiskerLeft (Over.forget i) L.structureMap
  let t' : D' ⟶ (Functor.const Jᵒᵖ).obj S := Functor.whiskerLeft e.functor tOver
  let c' : Cone D' := Cone.whisker e.functor (preimageCone L.diagram c i V)
  have hc' : IsLimit c' := hcV.whiskerEquivalence e
  let p : c'.pt ⟶ S := (c.π.app i ⁻¹ᵁ V).ι ≫ π₀
  have hπ₀c : ∀ a : L.indexTypeᵒᵖ, c.π.app a ≫ L.structureMap.app a = π₀ :=
    fun a => (L.compatible a).symm
  have hp : c'.π ≫ t' = (Functor.const Jᵒᵖ).map p := by
    ext a
    have h := Scheme.Hom.resLE_comp_ι (c.π.app (e.functor.obj a).left)
      (U := L.diagram.map (e.functor.obj a).hom ⁻¹ᵁ V) (V := c.π.app i ⁻¹ᵁ V)
      (by rw [← Scheme.Hom.comp_preimage, c.w])
    change (c.π.app (e.functor.obj a).left).resLE _ _ _ ≫
      Scheme.Opens.ι _ ≫ L.structureMap.app (e.functor.obj a).left = _
    rw [← Category.assoc, h, Category.assoc, hπ₀c]
    rfl
  -- the limit of that system is the open `range j₀`, which is a copy of `X`
  have hVU' : c.π.app i ⁻¹ᵁ V = j₀.opensRange := hVU
  let fIso : X ≅ (c.π.app i ⁻¹ᵁ V).toScheme := j₀.isoOpensRange ≪≫ (T₀.isoOfEq hVU').symm
  have hres : (T₀.isoOfEq hVU').inv ≫ (c.π.app i ⁻¹ᵁ V).ι = j₀.opensRange.ι :=
    Scheme.isoOfEq_inv_ι T₀ hVU'
  have hι : fIso.hom ≫ (c.π.app i ⁻¹ᵁ V).ι = j₀ := by
    rw [Iso.trans_hom, Category.assoc, Iso.symm_hom, hres,
      Scheme.Hom.isoOpensRange_hom_ι]
  let f' : X ⟶ c'.pt := fIso.hom
  have : IsIso f' := ⟨fIso.inv, fIso.hom_inv_id, fIso.inv_hom_id⟩
  have hf' : f' ≫ p = f := by
    change fIso.hom ≫ (c.π.app i ⁻¹ᵁ V).ι ≫ π₀ = f
    rw [← Category.assoc, hι, ← hfac]
  -- the hypotheses of the eventual-isomorphism criterion at every stage above `i`
  have hcpt : ∀ a : J, CompactSpace (D'.obj (op a)) := fun a =>
    isCompact_iff_compactSpace.mp
      ((L.diagram.map (e.functor.obj (op a)).hom).isCompact_preimage hV)
  have hlft : ∀ a : J, LocallyOfFiniteType (t'.app (op a)) := fun a => by
    have : LocallyOfFinitePresentation (L.structureMap.app (e.functor.obj (op a)).left) :=
      (L.stageFinitePresentation (e.functor.obj (op a)).left).1
    have : LocallyOfFiniteType (L.structureMap.app (e.functor.obj (op a)).left) :=
      inferInstance
    change LocallyOfFiniteType (Scheme.Opens.ι (L.diagram.map (e.functor.obj (op a)).hom ⁻¹ᵁ V)
      ≫ L.structureMap.app (e.functor.obj (op a)).left)
    infer_instance
  have htr : ∀ ⦃a b : J⦄ (h : a ≤ b), IsClosedImmersion (D'.map (homOfLE h).op) :=
    fun {_ _} _ => inferInstanceAs (IsClosedImmersion ((preimageDiagram L.diagram i V).map _))
  have : LocallyOfFinitePresentation (f' ≫ p) := by rw [hf']; infer_instance
  obtain ⟨a, ha⟩ := (eventually_isIso_comp_π_app D' t' c' hc' p hp f').exists
  have : IsIso (f' ≫ c'.π.app (op a)) := ha
  refine ⟨L.diagram.obj (e.functor.obj (op a)).left,
    (f' ≫ c'.π.app (op a)) ≫ (preimageDiagramι L.diagram i V).app (e.functor.obj (op a)),
    L.structureMap.app (e.functor.obj (op a)).left, inferInstance, ?_,
    L.stageFinite _, L.stageFinitePresentation _, ?_⟩
  · have : QuasiSeparated (L.structureMap.app (e.functor.obj (op a)).left) :=
      (L.stageFinitePresentation (e.functor.obj (op a)).left).2.2
    have : QuasiSeparatedSpace (L.diagram.obj (e.functor.obj (op a)).left) :=
      @quasiSeparatedSpace_of_quasiSeparated _ _
        (L.structureMap.app (e.functor.obj (op a)).left)
        (by change QuasiSeparatedSpace S; infer_instance) ‹_›
    infer_instance
  · have h := congrArg (fun η => η.app (op a)) hp
    simp only [NatTrans.comp_app, Functor.const_map_app] at h
    rw [Category.assoc]
    change _ = (f' ≫ c'.π.app (op a)) ≫ t'.app (op a)
    rw [Category.assoc, h, hf']

end FinitePresentation

end Stacks.FiniteFactorization

end
