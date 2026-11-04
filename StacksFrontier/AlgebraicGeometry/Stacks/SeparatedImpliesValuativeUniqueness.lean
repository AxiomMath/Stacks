module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.Valuative.Properness
public import StacksFrontier.AlgebraicGeometry.Stacks.ProperInertiaWhiskerLift
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationAxioms
public import StacksFrontier.AlgebraicGeometry.Stacks.ValuativeCriterionDiagonal
public import StacksFrontier.AlgebraicGeometry.Stacks.ValuativeCriterionDottedGroupoid
public import StacksFrontier.CategoryTheory.DottedArrows.TwoYoneda

/-!
# A separated 1-morphism of algebraic stacks satisfies valuative uniqueness (Stacks 0CLU)

Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over a scheme `S` of a big fppf site. **Stacks
0CLU** says that if `f` is separated — that is, if its relative diagonal `Δ_f` is proper in the
sense of Properties of Stacks, Section 04XB — then `f` satisfies the uniqueness part of the
valuative criterion (**Stacks 0CLG**).

The criterion is a conjunction. Its first half, that every category of dotted arrows be a setoid,
is **Stacks 0CLC**, which asks only that `Δ_f` be *separated* in the sense of Stacks 04XB, and
that is the first conjunct of the properness of `Δ_f` read at each scheme-valued point.

Its second half, that any two dotted arrows `a`, `b` of one valuative diagram be isomorphic, is
the content of the source's proof. The 2-morphisms `β_a : y ⟶ f ∘ a` and `β_b : y ⟶ f ∘ b` are
invertible, so `(a, b, β_b ∘ β_a⁻¹)` is a scheme-valued point of `𝒳 ×_{f, 𝒴, f} 𝒳` over the
spectrum of the valuation ring, and the pair `(α_a, α_b)` fills the resulting valuative diagram
for `Δ_f`. Now `Δ_f` is representable by algebraic spaces (**Stacks 04XS**, part (1)) and proper,
so that diagram has a dotted arrow: its base change along the special point is represented by an
algebraic space whose structure morphism is proper, the generic point of the diagram is a section
of that algebraic space over the spectrum of the fraction field, the valuative criterion of
properness for algebraic spaces (**Stacks 0A40**) extends the section over the whole spectrum, and
the 2-Yoneda lemma turns the extension into a dotted arrow. Finally **Stacks 0E8L**, part (2)
reads off from that dotted arrow a morphism `a ⟶ b`, which the setoid property makes an
isomorphism.

## Main definitions

* `AlgebraicGeometry.Stack.diagonalPairPoint` and `AlgebraicGeometry.Stack.diagonalPairCell`: the
  special point and the filler of the valuative diagram for `Δ_f` attached to two dotted arrows.
* `AlgebraicGeometry.Stack.diagonalPairDiagram`: that valuative diagram.

## Main results

* `AlgebraicGeometry.Stack.nonempty_dottedArrow_of_isProper`: a valuative diagram for a proper
  1-morphism representable by algebraic spaces has a dotted arrow, over the given valuation ring
  and with no extension of the fraction field.
* `AlgebraicGeometry.Stack.valuativeCriterionUniqueness_of_isSeparated`: **Stacks 0CLU**.

## Implementation notes

`AlgebraicGeometry.Stack.nonempty_dottedArrow_of_isProper` is stated for an arbitrary 1-morphism
of algebraic stacks rather than only for `Δ_f`, since nothing in its proof is special to the
diagonal; it is the strong form of the existence part of the valuative criterion — a dotted arrow
over the *given* valuation ring, not merely over a dominating one — which properness gives and
`AlgebraicGeometry.Stack.ValuativeCriterion.Existence` (Stacks 0CLK) does not demand.

`CategoryTheory.BasedCategory.ofFunctor` and
`CategoryTheory.Bicategory.InducedBicategory` are made `implicit_reducible` locally, as in
`StacksFrontier/AlgebraicGeometry/Stacks/ValuativeCriterionDiagonal.lean`: the objects of the slice
of the site appear both as `Over U` and as the object part of the based category attached to
`Over.forget U`, and without that the two spellings are not interchangeable at `implicit`
transparency, so the unifier cannot see that a composite of transports is the transport of the
composite.

The valuative criterion of properness for a morphism of algebraic spaces, in the two forms this
file consumes it — `AlgebraicGeometry.Stack.exists_lift_of_isProper`,
`AlgebraicGeometry.Stack.exists_section_of_isProper` — and the extension of a point of a base
change it yields, `AlgebraicGeometry.Stack.exists_extension_in_represented_fiber`, are stated in
`StacksFrontier/AlgebraicGeometry/Stacks/ProperInertiaWhiskerLift.lean`, which does not depend on
the valuative diagram of Stacks 0CLG and so is also available to Stacks 0CLD.

`CategoryTheory.DottedArrow` is the structure of
`StacksFrontier/CategoryTheory/DottedArrows/Defs.lean`, whose `γ`, `α` and `β` are 2-morphisms, as in
the source; the name is written out because a different structure of the same name in the root
namespace shadows it under `open CategoryTheory`.

## References

* [Stacks Project, Tag 0CLU](https://stacks.math.columbia.edu/tag/0CLU)
* [Stacks Project, Tag 0CLG](https://stacks.math.columbia.edu/tag/0CLG)
* [Stacks Project, Tag 0CLC](https://stacks.math.columbia.edu/tag/0CLC)
* [Stacks Project, Tag 04XS](https://stacks.math.columbia.edu/tag/04XS)
* [Stacks Project, Tag 0A40](https://stacks.math.columbia.edu/tag/0A40)
* [Stacks Project, Tag 0E8L](https://stacks.math.columbia.edu/tag/0E8L)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Bicategory

attribute [local implicit_reducible] CategoryTheory.Bicategory.InducedBicategory
  CategoryTheory.BasedCategory.ofFunctor

namespace AlgebraicGeometry.Stack

universe u w u₁ v₁ u₂

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Existence of a dotted arrow -/

/-- **A valuative diagram for a proper 1-morphism representable by algebraic spaces has a dotted
arrow**, over the given valuation ring and with no extension of the fraction field.

The base change of `g` along the special point is represented by an algebraic space; the generic
point of the diagram is a section of it over the spectrum of the fraction field, which extends to
a section over the spectrum of the valuation ring by the valuative criterion of properness. The
extension is an object of `𝒜` over the special point together with the two comparisons a dotted
arrow asks for at the unit objects, and the 2-Yoneda lemma
(`CategoryTheory.CatFiberedInGroupoids.nonempty_dottedArrow_of_fiberObj`) turns those into a
dotted arrow. -/
theorem nonempty_dottedArrow_of_isProper {𝒜 ℬ : AlgebraicStacks.{u, w} B S hS} (g : 𝒜 ⟶ ℬ)
    (hg : IsProper B S hS g.hom)
    (hrep : IsRepresentableByAlgebraicSpaces B S hS g.hom.hom)
    (D : ValuativeDiagram B S hS 𝒜 ℬ g) :
    Nonempty (CategoryTheory.DottedArrow D.x D.j g.hom D.y D.γ) := by
  let := D.ring
  let := D.domain
  let := D.valuation
  let back := Over.iteratedSliceBackward D.whole
  let V₀ : (schemeFibredCategory B S hS D.generic).val.obj := Over.mk (𝟙 D.generic)
  have hjobj : D.j.hom.obj V₀ = Over.mk D.inclusion := by
    rw [show D.j.hom.toFunctor = Over.map D.inclusion from D.j_canonical]
    show Over.mk (𝟙 D.generic ≫ D.inclusion) = Over.mk D.inclusion
    rw [Category.id_comp]
  let y := back ⋙ D.y.hom.toFunctor
  have hy : y ⋙ ℬ.val.val.p = Over.map D.whole.hom :=
    (congrArg (fun k => back ⋙ k) D.y.hom.w).trans (Over.iteratedSliceBackward_forget D.whole)
  have hgx : (Over.map D.whole.hom).obj (Over.mk D.inclusion.left) = D.generic := by
    show Over.mk (D.inclusion.left ≫ D.whole.hom) = D.generic
    rw [Over.w D.inclusion]
    rfl
  let c₀ : back.obj (Over.mk D.inclusion.left) ≅ Over.mk D.inclusion :=
    Over.isoMk (Over.isoMk (Iso.refl D.generic.left) (by
          show 𝟙 D.generic.left ≫ D.generic.hom = D.inclusion.left ≫ D.whole.hom
          rw [Category.id_comp]
          exact (Over.w D.inclusion).symm)) (by
        apply Over.OverMorphism.ext
        show 𝟙 D.generic.left ≫ D.inclusion.left = D.inclusion.left
        rw [Category.id_comp])
  let c : back.obj (Over.mk D.inclusion.left) ≅ D.j.hom.obj V₀ := c₀ ≪≫ eqToIso hjobj.symm
  have hc₀ : (schemeFibredCategory B S hS D.whole).val.p.IsHomLift (𝟙 D.generic) c₀.hom := by
    show (Over.forget D.whole).IsHomLift (𝟙 D.generic) c₀.hom
    refine IsHomLift.of_fac' _ _ _ hgx rfl ?_
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    simp [c₀, back, Over.iteratedSliceBackward]
    rfl
  have h₁ : (schemeFibredCategory B S hS D.whole).val.p.IsHomLift (𝟙 D.generic)
      (eqToHom hjobj.symm) := IsHomLift.eqToHom_domain_lift_id hjobj.symm rfl
  have hc : (schemeFibredCategory B S hS D.whole).val.p.IsHomLift (𝟙 D.generic) c.hom := by
    show (schemeFibredCategory B S hS D.whole).val.p.IsHomLift (𝟙 D.generic)
      (c₀.hom ≫ eqToHom hjobj.symm)
    exact IsHomLift.comp_lift_id_left _ _ _ _
  have hc' : ℬ.val.val.p.IsHomLift (𝟙 D.generic) (D.y.hom.map c.hom) :=
    Functor.isHomLift_map_of_comp_eq D.y.hom.w (𝟙 D.generic) c.hom
  have hγ : ℬ.val.val.p.IsHomLift (𝟙 D.generic) (D.γ.hom.toNatTrans.app V₀) :=
    D.γ.hom.isHomLift' V₀
  have hγiso : IsIso (D.γ.hom.toNatTrans.app V₀) :=
    Functor.isIso_of_fiber_isGroupoid
      (ℬ.val.isFiberedInGroupoids.fiber_isGroupoid D.generic)
      (D.γ.hom.toNatTrans.app V₀) hγ
  let γIso : D.y.hom.obj (D.j.hom.obj V₀) ≅ g.hom.hom.obj (D.x.hom.obj V₀) :=
    @asIso _ _ _ _ (D.γ.hom.toNatTrans.app V₀) hγiso
  have hγ' : ℬ.val.val.p.IsHomLift (𝟙 D.generic) γIso.hom := hγ
  let q : TwoFibreProductOver (Over.map D.whole.hom) 𝒜.val.val.p ℬ.val.val.p y
      g.hom.hom.toFunctor :=
    { base := D.generic
      x := Over.mk D.inclusion.left
      y := D.x.hom.obj V₀
      hx := hgx
      hy := D.x.hom.w_obj _
      iso := D.y.hom.toFunctor.mapIso c ≪≫ γIso
      vertical := by
        show ℬ.val.val.p.IsHomLift (𝟙 D.generic) (D.y.hom.map c.hom ≫ γIso.hom)
        exact IsHomLift.comp_lift_id_left _ _ _ _ }
  obtain ⟨q', h, hv⟩ := exists_extension_in_represented_fiber B S hS g.hom hg hrep
    D.inclusion D.R D.whole_iso D.generic_iso D.inclusion_spec y hy q rfl
  obtain ⟨qb, qx, qy, qhx, qhy, qiso, qvert⟩ := q'
  subst hv
  have hmk : Over.mk (𝟙 D.whole.left ≫ D.whole.hom) = D.whole := by
    rw [Category.id_comp]
    cases D.whole
    rfl
  have hqb : qb = D.whole := qhx.symm.trans hmk
  subst hqb
  let T₀ : Over D.whole := Over.mk (𝟙 D.whole)
  let e : T₀ ≅ back.obj (Over.mk (𝟙 D.whole.left)) :=
    Over.isoMk (Over.isoMk (Iso.refl D.whole.left)
        (by simp [back, Over.iteratedSliceBackward, T₀])) (by
      apply Over.OverMorphism.ext
      simp [back, Over.iteratedSliceBackward, T₀]
      rfl)
  have he : (schemeFibredCategory B S hS D.whole).val.p.IsHomLift (𝟙 D.whole) e.hom := by
    show (Over.forget D.whole).IsHomLift (𝟙 D.whole) e.hom
    refine IsHomLift.of_fac' _ _ _ rfl ?_ ?_
    · exact hmk
    · apply Over.OverMorphism.ext
      apply ObjectProperty.hom_ext
      simp [e, T₀, back, Over.iteratedSliceBackward]
      rfl
  have he' : ℬ.val.val.p.IsHomLift (𝟙 D.whole) (D.y.hom.toFunctor.map e.hom) :=
    Functor.isHomLift_map_of_comp_eq D.y.hom.w (𝟙 D.whole) e.hom
  have hqv : ℬ.val.val.p.IsHomLift (𝟙 D.whole) qiso.hom := qvert
  have hab : h.a = (Over.homMk D.inclusion.left (Category.comp_id _) :
      Over.mk D.inclusion.left ⟶ Over.mk (𝟙 D.whole.left)) :=
    Over.mkIdTerminal.hom_ext _ _
  have hbe : h.hbase = D.inclusion := by
    rw [TwoFibreProductOver.Hom.hbase_eq, hab]
    apply Over.OverMorphism.ext
    simp
  have hmlift := h.hb
  rw [hbe] at hmlift
  have ht : (Over.mkIdTerminal.from (D.j.hom.obj V₀) : D.j.hom.obj V₀ ⟶ T₀) ≫ e.hom =
      c.inv ≫ back.map h.a :=
    (Iso.eq_comp_inv e).mp (Over.mkIdTerminal.hom_ext _ _)
  have hDtDe : D.y.hom.toFunctor.map (Over.mkIdTerminal.from (D.j.hom.obj V₀)) ≫
      D.y.hom.toFunctor.map e.hom =
      D.y.hom.toFunctor.map c.inv ≫ D.y.hom.toFunctor.map (back.map h.a) :=
    ((D.y.hom.toFunctor.map_comp _ e.hom).symm.trans
      (congrArg D.y.hom.toFunctor.map ht)).trans
        (D.y.hom.toFunctor.map_comp c.inv (back.map h.a))
  have hw := h.w
  refine CatFiberedInGroupoids.nonempty_dottedArrow_of_fiberObj D.inclusion D.j_canonical
    qy qhy h.b hmlift (D.y.hom.toFunctor.map e.hom ≫ qiso.hom)
    (IsHomLift.comp_lift_id_left _ _ _ _) ?_
  show D.γ.hom.toNatTrans.app V₀ ≫ g.hom.hom.toFunctor.map h.b =
    D.y.hom.toFunctor.map (Over.mkIdTerminal.from (D.j.hom.obj V₀)) ≫
      D.y.hom.toFunctor.map e.hom ≫ qiso.hom
  change D.y.hom.toFunctor.map (back.map h.a) ≫ qiso.hom =
    (D.y.hom.toFunctor.map c.hom ≫ D.γ.hom.toNatTrans.app V₀) ≫
      g.hom.hom.toFunctor.map h.b at hw
  rw [← Category.assoc, hDtDe, Category.assoc, hw]
  exact ((congrArg (D.y.hom.toFunctor.map c.inv ≫ ·) (Category.assoc _ _ _)).trans
    (c.map_inv_hom_id_assoc _ _)).symm

/-! ### The valuative diagram of the relative diagonal attached to two dotted arrows -/

variable {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}

/-- The natural isomorphism `y ≅ f ∘ a` underlying the 2-morphism `β` of a dotted arrow: every
2-morphism of categories fibred in groupoids is invertible, componentwise because the fibres are
groupoids. -/
noncomputable def dottedArrowBetaIso (f : 𝒳 ⟶ 𝒴) (D : ValuativeDiagram B S hS 𝒳 𝒴 f)
    (a : CategoryTheory.DottedArrow D.x D.j f.hom D.y D.γ) :
    D.y.hom.toFunctor ≅ (a.a ≫ f.hom).hom.toFunctor :=
  NatIso.ofComponents
    (fun z => @asIso _ _ _ _ (a.β.hom.toNatTrans.app z)
      (Functor.isIso_of_fiber_isGroupoid
        (𝒴.val.isFiberedInGroupoids.fiber_isGroupoid _) _ (a.β.hom.isHomLift' z)))
    (fun g => a.β.hom.toNatTrans.naturality g)

/-- The component of `dottedArrowBetaIso` at an object `z` is the component of `β` at `z`. -/
@[simp] theorem dottedArrowBetaIso_hom_app (f : 𝒳 ⟶ 𝒴) (D : ValuativeDiagram B S hS 𝒳 𝒴 f)
    (a : CategoryTheory.DottedArrow D.x D.j f.hom D.y D.γ)
    (z : (schemeFibredCategory B S hS D.whole).val.obj) :
    (dottedArrowBetaIso B S hS f D a).hom.app z = a.β.hom.toNatTrans.app z := rfl

/-- **The special point of the valuative diagram for the relative diagonal attached to two dotted
arrows.** Two dotted arrows `a`, `b` of a valuative diagram for `f` have `f ∘ a ≅ y ≅ f ∘ b`, so
the pair `(a, b)` together with that identification is a scheme-valued point of `𝒳 ×_𝒴 𝒳` over
the spectrum of the valuation ring. -/
noncomputable def diagonalPairFunctor (f : 𝒳 ⟶ 𝒴) (D : ValuativeDiagram B S hS 𝒳 𝒴 f)
    (a b : CategoryTheory.DottedArrow D.x D.j f.hom D.y D.γ) :
    (schemeFibredCategory B S hS D.whole).val.obj ⥤
      TwoFibreProductOver 𝒳.val.val.p 𝒳.val.val.p 𝒴.val.val.p
        f.hom.hom.toFunctor f.hom.hom.toFunctor :=
  TwoFibreProductOver.lift 𝒳.val.val.p 𝒳.val.val.p 𝒴.val.val.p
    f.hom.hom.toFunctor f.hom.hom.toFunctor (schemeFibredCategory B S hS D.whole).val.p
    a.a.hom.toFunctor b.a.hom.toFunctor a.a.hom.w b.a.hom.w
    ((dottedArrowBetaIso B S hS f D a).symm ≪≫ dottedArrowBetaIso B S hS f D b)
    (fun z => by
      have h₂ : 𝒴.val.val.p.IsHomLift (𝟙 ((schemeFibredCategory B S hS D.whole).val.p.obj z))
          ((dottedArrowBetaIso B S hS f D b).hom.app z) := b.β.hom.isHomLift' z
      have h₄ : 𝒴.val.val.p.IsHomLift (𝟙 ((schemeFibredCategory B S hS D.whole).val.p.obj z))
          (((dottedArrowBetaIso B S hS f D a).app z).hom) := a.β.hom.isHomLift' z
      have h₃ : 𝒴.val.val.p.IsHomLift (𝟙 ((schemeFibredCategory B S hS D.whole).val.p.obj z))
          ((dottedArrowBetaIso B S hS f D a).inv.app z) :=
        IsHomLift.lift_id_inv 𝒴.val.val.p _ ((dottedArrowBetaIso B S hS f D a).app z)
      change 𝒴.val.val.p.IsHomLift _
        ((dottedArrowBetaIso B S hS f D a).inv.app z ≫
          (dottedArrowBetaIso B S hS f D b).hom.app z)
      exact IsHomLift.comp_lift_id_left _ _ _ _)

/-- `AlgebraicGeometry.Stack.diagonalPairFunctor`, read as a 1-morphism of categories fibred in
groupoids into the canonical 2-fibre product `𝒳 ×_{f, 𝒴, f} 𝒳`. -/
noncomputable def diagonalPairPoint (f : 𝒳 ⟶ 𝒴) (D : ValuativeDiagram B S hS 𝒳 𝒴 f)
    (a b : CategoryTheory.DottedArrow D.x D.j f.hom D.y D.γ) :
    schemeFibredCategory B S hS D.whole ⟶
      (AlgebraicStacks.twoFibreProduct B S hS f f).val :=
  Bicategory.InducedBicategory.mkHom
    { toFunctor := diagonalPairFunctor B S hS f D a b
      w := TwoFibreProductOver.lift_comp_structureFunctor .. }

attribute [local implicit_reducible] CategoryTheory.TwoFibreProductOver.lift
  diagonalPairFunctor diagonalPairPoint

/-- A composite `eqToHom ≫ 𝟙 ≫ eqToHom` is an `eqToHom`. -/
theorem eqToHom_comp_id_comp_eqToHom {𝒞 : Type*} [Category 𝒞] {X Y Z : 𝒞} (h₁ : X = Y)
    (h₂ : Y = Z) (e : X = Z) : eqToHom h₁ ≫ 𝟙 Y ≫ eqToHom h₂ = eqToHom e := by
  subst h₁ h₂
  simp

/-- The comparison square of the component of
`AlgebraicGeometry.Stack.diagonalPairCell`, in the form the construction needs. -/
theorem comp_id_eq_inv_comp_comp {𝒞 : Type*} [Category 𝒞] {X Y Z W : 𝒞} (i : X ≅ Y) (u : Y ⟶ W)
    (v : X ⟶ Z) (t : Z ⟶ W) (key : i.hom ≫ u = v ≫ t) : u ≫ 𝟙 W = (i.inv ≫ v) ≫ t := by
  rw [Category.comp_id, Category.assoc, ← key, ← Category.assoc, i.inv_hom_id, Category.id_comp]

/-- **The 2-morphism filling the valuative square for the relative diagonal attached to two
dotted arrows.** A 2-morphism into the 2-fibre product is a pair of 2-morphisms into the two
factors, here the `α` of `a` and the `α` of `b`; the comparison square is the compatibility
triangle of the two dotted arrows read against the one `γ`. -/
noncomputable def diagonalPairCell (f : 𝒳 ⟶ 𝒴) (D : ValuativeDiagram B S hS 𝒳 𝒴 f)
    (a b : CategoryTheory.DottedArrow D.x D.j f.hom D.y D.γ) :
    (D.j ≫ diagonalPairPoint B S hS f D a b) ⟶
      (D.x ≫ (AlgebraicStacks.relativeDiagonal B S hS f).hom) := by
  refine ⟨{ toNatTrans := { app := fun z => ?_, naturality := ?_ }, isHomLift' := ?_ }⟩
  · refine TwoFibreProductOver.Hom.mk' (a.α.hom.toNatTrans.app z) (b.α.hom.toNatTrans.app z)
      ?_ ?_
    · exact (Functor.eqToHom_comp_map_comp_eqToHom 𝒳.val.val.p _ (b.α.hom.isHomLift' z)
            ((D.j ≫ diagonalPairPoint B S hS f D a b).hom.obj z).hy _
            ((D.j.hom.w_obj z).trans (D.x.hom.w_obj z).symm)).trans
        (Functor.eqToHom_comp_map_comp_eqToHom 𝒳.val.val.p _ (a.α.hom.isHomLift' z)
            ((D.j ≫ diagonalPairPoint B S hS f D a b).hom.obj z).hx _
            ((D.j.hom.w_obj z).trans (D.x.hom.w_obj z).symm)).symm
    · have ha := congrArg (fun η => η.hom.toNatTrans.app z) a.compat
      have hb := congrArg (fun η => η.hom.toNatTrans.app z) b.compat
      change D.γ.hom.toNatTrans.app z =
        a.β.hom.toNatTrans.app (D.j.hom.obj z) ≫ 𝟙 _ ≫
          f.hom.hom.toFunctor.map (a.α.hom.toNatTrans.app z) at ha
      change D.γ.hom.toNatTrans.app z =
        b.β.hom.toNatTrans.app (D.j.hom.obj z) ≫ 𝟙 _ ≫
          f.hom.hom.toFunctor.map (b.α.hom.toNatTrans.app z) at hb
      have ha' : D.γ.hom.toNatTrans.app z =
          a.β.hom.toNatTrans.app (D.j.hom.obj z) ≫
            f.hom.hom.toFunctor.map (a.α.hom.toNatTrans.app z) :=
        ha.trans (congrArg (fun t => a.β.hom.toNatTrans.app (D.j.hom.obj z) ≫ t)
          (Category.id_comp (f.hom.hom.toFunctor.map (a.α.hom.toNatTrans.app z))))
      have hb' : D.γ.hom.toNatTrans.app z =
          b.β.hom.toNatTrans.app (D.j.hom.obj z) ≫
            f.hom.hom.toFunctor.map (b.α.hom.toNatTrans.app z) :=
        hb.trans (congrArg (fun t => b.β.hom.toNatTrans.app (D.j.hom.obj z) ≫ t)
          (Category.id_comp (f.hom.hom.toFunctor.map (b.α.hom.toNatTrans.app z))))
      exact comp_id_eq_inv_comp_comp
        ((dottedArrowBetaIso B S hS f D a).app (D.j.hom.obj z))
        (f.hom.hom.toFunctor.map (a.α.hom.toNatTrans.app z))
        (b.β.hom.toNatTrans.app (D.j.hom.obj z))
        (f.hom.hom.toFunctor.map (b.α.hom.toNatTrans.app z)) (ha'.symm.trans hb')
  · intro z z' k
    apply TwoFibreProductOver.Hom.ext'
    · exact a.α.hom.toNatTrans.naturality k
    · exact b.α.hom.toNatTrans.naturality k
  · intro z
    refine IsHomLift.of_fac' (AlgebraicStacks.twoFibreProduct B S hS f f).val.val.p
      (𝟙 _) _ (D.j.hom.w_obj z) (D.x.hom.w_obj z) ?_
    exact (Functor.eqToHom_comp_map_comp_eqToHom 𝒳.val.val.p _ (a.α.hom.isHomLift' z)
          ((D.j ≫ diagonalPairPoint B S hS f D a b).hom.obj z).hx _
          ((D.j.hom.w_obj z).trans (D.x.hom.w_obj z).symm)).trans
      (eqToHom_comp_id_comp_eqToHom _ _ _).symm

/-- **The valuative diagram for the relative diagonal attached to two dotted arrows**: the same
valuation ring and generic point, with special point
`AlgebraicGeometry.Stack.diagonalPairPoint` and filler
`AlgebraicGeometry.Stack.diagonalPairCell`. -/
noncomputable def diagonalPairDiagram (f : 𝒳 ⟶ 𝒴) (D : ValuativeDiagram B S hS 𝒳 𝒴 f)
    (a b : CategoryTheory.DottedArrow D.x D.j f.hom D.y D.γ) :
    ValuativeDiagram B S hS 𝒳 (AlgebraicStacks.twoFibreProduct B S hS f f)
      (AlgebraicStacks.relativeDiagonal B S hS f) where
  R := D.R
  ring := D.ring
  domain := D.domain
  valuation := D.valuation
  generic := D.generic
  whole := D.whole
  generic_iso := D.generic_iso
  whole_iso := D.whole_iso
  inclusion := D.inclusion
  inclusion_spec := D.inclusion_spec
  j := D.j
  j_canonical := D.j_canonical
  x := D.x
  y := diagonalPairPoint B S hS f D a b
  γ := diagonalPairCell B S hS f D a b

/-! ### Stacks 0CLU -/

/-- Cancelling an isomorphism on the left of an identity-prefixed equation. -/
theorem eq_comp_of_inv_comp_eq {𝒞 : Type*} [Category 𝒞] {X Y W : 𝒞} (i : X ≅ Y) (u : X ⟶ W)
    (v : Y ⟶ W) (h : i.inv ≫ u = 𝟙 Y ≫ v) : u = i.hom ≫ v := by
  rw [← i.inv_comp_eq, h, Category.id_comp]

/-- **Stacks 0CLU.** A separated 1-morphism of algebraic stacks satisfies the uniqueness part of
the valuative criterion.

Separatedness is properness of the relative diagonal `Δ_f` in the sense of Stacks 04XB, so `Δ_f`
is in particular separated there and the category of dotted arrows of every valuative diagram is
a setoid by **Stacks 0CLC**. For the second half, two dotted arrows `a`, `b` of one valuative
diagram assemble into a scheme-valued point `(a, b, β_b ∘ β_a⁻¹)` of `𝒳 ×_𝒴 𝒳` whose valuative
diagram for `Δ_f` is filled by `(α_a, α_b)`; `Δ_f` is proper and representable by algebraic spaces
(**Stacks 04XS**), so that diagram has a dotted arrow by the valuative criterion of properness for
algebraic spaces (**Stacks 0A40**), and **Stacks 0E8L** turns that dotted arrow into a morphism
`a ⟶ b`, which the setoid property makes an isomorphism. -/
@[stacks 0CLU]
theorem valuativeCriterionUniqueness_of_isSeparated (f : 𝒳 ⟶ 𝒴)
    (hf : AlgebraicStacks.IsSeparated B S hS f) :
    ValuativeCriterion.Uniqueness B S hS f := by
  have hsep : IsSeparated B S hS (relativeDiagonal.{u, u, u + 1} B S hS 𝒳.val 𝒴.val f.hom) :=
    fun U y hy F hF he => (hf U y hy F hF he).1
  intro D
  have hsetoid :=
    isSetoidCategory_dottedArrow_of_isSeparated_relativeDiagonal B S hS f hsep D
  refine ⟨hsetoid, fun a b => ?_⟩
  obtain ⟨d⟩ := nonempty_dottedArrow_of_isProper B S hS
    (AlgebraicStacks.relativeDiagonal B S hS f) hf
    (isRepresentableByAlgebraicSpaces_relativeDiagonal_algebraicStacks B S hS f)
    (diagonalPairDiagram B S hS f D a b)
  have m := AlgebraicStacks.diagonalDottedArrowHom B S hS
    (diagonalPairDiagram B S hS f D a b) d
  have hβ : b.β = a.β ≫ (m.θ ▷ f.hom) := by
    refine Bicategory.InducedBicategory.hom₂_ext (BasedNatTrans.ext _ _ (NatTrans.ext ?_))
    funext z
    have h := congrArg (fun η => η.hom.toNatTrans.app z) m.cond_β
    change (dottedArrowBetaIso B S hS f D a).inv.app z ≫ b.β.hom.toNatTrans.app z =
      𝟙 _ ≫ f.hom.hom.toFunctor.map (m.θ.hom.toNatTrans.app z) at h
    exact eq_comp_of_inv_comp_eq ((dottedArrowBetaIso B S hS f D a).app z) _ _ h
  let ψ : a ⟶ b := { θ := m.θ, cond_α := m.cond_α, cond_β := hβ }
  have := hsetoid.1 ψ
  exact ⟨asIso ψ⟩

end AlgebraicGeometry.Stack

end
