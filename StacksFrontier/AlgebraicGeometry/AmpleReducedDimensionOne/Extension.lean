module

public import StacksFrontier.AlgebraicGeometry.AmpleReducedDimensionOne.Assembly
public import StacksFrontier.AlgebraicGeometry.SectionExtension.NilpotentRestrict
public import StacksFrontier.AlgebraicGeometry.AffineClosedUnion.Global
public import StacksFrontier.AlgebraicGeometry.AffineClosedUnion.ReducedCover
public import StacksFrontier.AlgebraicGeometry.AmpleTransport.Basic
public import StacksFrontier.AlgebraicGeometry.TwistedSheaf.PushforwardTwist

/-!
# The last paragraph of the proof of Tag 09NX, and the ample sheaf

This file carries out the step the proof of
[Stacks, Tag 09NX](https://stacks.math.columbia.edu/tag/09NX) takes after the invertible sheaf `M`
and the global section `t` of
`StacksDraft.AlgebraicGeometry.F3b.AmpleReducedDimensionOne.Assembly` are in hand, and then
concludes.

Let `x` be a point outside the overlap `T` of the irreducible components.  Then `x` lies on a
single component `Z₁`, and the union `Z` of the remaining components misses `x`.  The pullback
`i^*M` to `Z₁` is ample, so items (3) and (4) of
[Tag 01Q3](https://stacks.math.columbia.edu/tag/01Q3) give an exponent `m ≥ 1` and a global
section `s` of `(i^*M)^{⊗ m}` whose nonvanishing locus is affine, contains `x` and misses `Z`.
A power `s^N` then restricts to zero on the scheme-theoretic intersection `Z₁ ∩ Z`, and the
twisted square of
`StacksDraft.AlgebraicGeometry.F3b.AffineClosedUnion.ReducedCover` extends it to a global section
`c` of `M^{⊗ mN}` on `X` vanishing on `Z`.  Its nonvanishing locus is contained in `Z₁`, has
affine preimage there, and therefore is affine.

## Main results

* `Stacks.AmpleReducedDimensionOne.otherComponents`: the union of the irreducible components
  other than a given one, as a closed set, with
  `otherComponents_sup_componentCloseds` the statement that the two closed sets cover `X` and
  `notMem_otherComponents` the statement that a point off `T` on `C` misses them.
* `Stacks.AmpleReducedDimensionOne.exists_component_section`: **items (3) and (4) of Tag 01Q3 on
  the single component through `x`**, with the containment restated as a disjointness from the
  scheme-theoretic intersection.
* `Stacks.AmpleReducedDimensionOne.unit_app_eq_zero_of_hom`: a morphism of sheaves of modules
  carries a section killed by the unit of `g^* ⊣ g_*` to a section killed by it.
* `Stacks.AmpleReducedDimensionOne.unitRestrict_app_eq_zero_of_unit_app_eq_zero`: **the
  hypothesis of the twisted square, discharged** from the vanishing of
  `AlgebraicGeometry.Scheme.Modules.exists_unit_app_eval_sectionPow'_eq_zero`.
* `Stacks.AmpleReducedDimensionOne.notMem_nonvanishingLocus_of_unit_app_top_eq_zero`: a global
  section killed by the unit of `j^* ⊣ j_*` vanishes everywhere on the image of `j`.
* `Stacks.AmpleReducedDimensionOne.preimage_nonvanishingOpen_eq_of_unit_app_top_eq`: the
  nonvanishing locus of the extended section pulls back to that of the section it extends.
* `Stacks.AmpleReducedDimensionOne.exists_sections_of_notMem_componentOverlap`: **step 7 of the
  proof**, which is exactly the hypothesis
  `Stacks.AmpleReducedDimensionOne.isAmple_of_forall_notMem_componentOverlap` asks for.
* `Stacks.AmpleReducedDimensionOne.exists_isAmple_of_isReduced_of_topologicalKrullDim_le_one`:
  **Tag 09NX.**

## Implementation notes

**The pullback-tensor-power comparison is available and is what makes step 7 possible.** Ampleness
on the component produces a section of `(i^*M)^{⊗ m}`, while the twisted square consumes a
section of `i^*(M^{⊗ m})`; `AlgebraicGeometry.Scheme.Modules.pullbackTensorPowerIso` identifies
the two.  The module docstring of
`StacksDraft.AlgebraicGeometry.F3b.SectionExtension.NilpotentRestrict` says this comparison is
not available in this development, and that is not so: it is in `AmplePullback/Basic.lean` for a
natural-number exponent and in `TwistedSheaf/PushforwardTwist.lean` for an integer one.  What
that file's own route genuinely avoids is a *multiplicativity* of restriction, which is a
different statement.

**Crossing the comparison needs one naturality square and nothing else.**
`unit_app_eq_zero_of_hom` is that square, stated for an arbitrary morphism of sheaves of modules
so that the tensor-power spellings never enter it.  Both `rw` forms of the two steps that use it
fail with *"the target expression is not type-correct under the `implicit` transparency level"* —
the `AlgebraicGeometry.Scheme.Modules` versus
  `structureSheafRing` seam — and the
cure throughout this file is to compose the equations in term mode with
`Eq.trans` and `congrArg`, where no motive is formed.

**An invertibility instance for a pullback cannot be supplied inside a proof when the statement
mentions it.** `AlgebraicGeometry.Scheme.Modules.IsAmple` takes the invertibility as an instance
argument, so `IsAmple Z ((Scheme.Modules.pullback i).obj M)` does not elaborate without it in
scope, even with a `have` of exactly the right spelling in the body: the failure is reported
at the statement.  The statements below therefore carry the binder, as
`AlgebraicGeometry.Scheme.Modules.pullbackTensorPowerIso` does, and the final theorem discharges
it with a `haveI` inside its tactic proof, where it is available before the statements of the
lemmas it applies are elaborated.

**The components are compact, and not by a Noetherianness instance.**
`AlgebraicGeometry.IsNoetherian (componentScheme X C)` is not found by instance search;
`compactSpace_of_quasiCompact` gets the compactness that
`AlgebraicGeometry.Scheme.Modules.exists_unit_app_eval_sectionPow'_eq_zero` needs from
quasi-compactness of the closed immersion instead.

## References

* [Stacks Project, Tag 09NX](https://stacks.math.columbia.edu/tag/09NX)
* [Stacks Project, Tag 01Q3](https://stacks.math.columbia.edu/tag/01Q3)
* [Stacks Project, Tag 09NL](https://stacks.math.columbia.edu/tag/09NL)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open Stacks.Topology.Irreducible
open Stacks.SheafOfModules Stacks.SheafOfModules.Invertible
open RingedSpaceModuleAdjunction
open AlgebraicGeometry.Scheme.IdealSheafData (vanishingIdeal)

universe u

namespace Stacks.AmpleReducedDimensionOne

/-! ### The union of the other components -/

variable (X : Scheme.{u}) [AlgebraicGeometry.IsNoetherian X]

/-- An irreducible component of `X`, as a closed set.  This is the closed set whose vanishing
ideal sheaf cuts out `Stacks.AmpleReducedDimensionOne.componentScheme`.

It is an `abbrev`, and that is load-bearing: as a `def` it hides the closed set from instance
search, and `IsClosedImmersion (componentIntersectionι X C)` is then not found even though the
instance is generic in the two ideal sheaves, because the codomain of that morphism is spelled
`componentScheme X C` while its body produces `(vanishingIdeal (componentCloseds X C)).subscheme`.
With the closed set spelled out on both sides the instance is found as a
`def`, and with the codomain spelled through `componentScheme` it is found only as an `abbrev`. -/
abbrev componentCloseds (C : irreducibleComponents (X : Type u)) : Closeds (X : Type u) :=
  ⟨C.1, isClosed_of_mem_irreducibleComponents C.1 C.2⟩

/-- The union of the irreducible components other than `C` is closed: a Noetherian space has
finitely many irreducible components, and each is closed. -/
theorem isClosed_iUnion_ne (C : irreducibleComponents (X : Type u)) :
    IsClosed (⋃ D : {D : irreducibleComponents (X : Type u) // D ≠ C}, (D.1.1 : Set X)) :=
  have : Finite (irreducibleComponents (X : Type u)) :=
    TopologicalSpace.NoetherianSpace.finite_irreducibleComponents.to_subtype
  isClosed_iUnion_of_finite fun D => isClosed_of_mem_irreducibleComponents D.1.1 D.1.2

/-- The union of the irreducible components other than `C`, as a closed set.  This is the `Z` of
the last paragraph of the proof of Tag 09NX. -/
def otherComponents (C : irreducibleComponents (X : Type u)) : Closeds (X : Type u) :=
  ⟨_, isClosed_iUnion_ne X C⟩

/-- The open complement of the union of the other components. -/
def otherComponentsCompl (C : irreducibleComponents (X : Type u)) : X.Opens :=
  ⟨((otherComponents X C : Set X))ᶜ, (otherComponents X C).isClosed.isOpen_compl⟩

/-- A point lies in the union of the components other than `C` if and only if it lies on some
irreducible component `D ≠ C`. -/
theorem mem_otherComponents_iff {C : irreducibleComponents (X : Type u)} (x : X) :
    x ∈ (otherComponents X C : Set X) ↔
      ∃ D : irreducibleComponents (X : Type u), D ≠ C ∧ x ∈ (D : Set X) := by
  constructor
  · intro hmem
    obtain ⟨D, hD⟩ := Set.mem_iUnion.mp hmem
    exact ⟨D.1, D.2, hD⟩
  · rintro ⟨D, hD, hx⟩
    exact Set.mem_iUnion.mpr ⟨⟨D, hD⟩, hx⟩

/-- **A component and the union of the others cover `X`**, which is the hypothesis the twisted
square of Tag 09NW asks for.  Every point lies on some irreducible component. -/
theorem otherComponents_sup_componentCloseds (C : irreducibleComponents (X : Type u)) :
    otherComponents X C ⊔ componentCloseds X C = ⊤ := by
  refine Closeds.ext (Set.eq_univ_of_forall fun x => ?_)
  rw [Closeds.coe_sup]
  obtain ⟨D, z, hz⟩ := exists_componentι_eq X x
  by_cases h : D = C
  · subst h
    exact Or.inr (hz ▸ (range_componentι X D).le ⟨z, rfl⟩)
  · exact Or.inl ((mem_otherComponents_iff X x).mpr
      ⟨D, h, hz ▸ (range_componentι X D).le ⟨z, rfl⟩⟩)

/-- **A point off the overlap lying on `C` misses every other component.**  It lies on exactly
one component, so lying on a second one is impossible. -/
theorem notMem_otherComponents {C : irreducibleComponents (X : Type u)} {x : X}
    (hx : x ∉ componentOverlap X) (hxC : x ∈ (C : Set X)) :
    x ∈ otherComponentsCompl X C := by
  intro hmem
  obtain ⟨D, hDC, hxD⟩ := (mem_otherComponents_iff X x).mp hmem
  exact hDC ((existsUnique_mem_of_notMem_componentOverlap X hx).unique hxD hxC)

/-- **The complement of the other components lies in the one component.**  This is what turns the
containment of a nonvanishing locus in that complement into the hypothesis of the one-piece
affineness criterion. -/
theorem otherComponentsCompl_subset_range (C : irreducibleComponents (X : Type u)) :
    ((otherComponentsCompl X C : Set X)) ⊆ Set.range (componentι X C).base := by
  intro x hx
  rw [range_componentι]
  have h : x ∈ ((otherComponents X C : Set X) ∪ (componentCloseds X C : Set X)) := by
    rw [← Closeds.coe_sup, otherComponents_sup_componentCloseds]; trivial
  exact h.resolve_left hx

/-- **The source of a quasi-compact morphism into a compact scheme is compact.**  This is how the
components get the `CompactSpace` instance that
`AlgebraicGeometry.Scheme.Modules.exists_unit_app_eval_sectionPow'_eq_zero` asks for. -/
theorem compactSpace_of_quasiCompact {Z : Scheme.{u}} (f : Z ⟶ X) [QuasiCompact f] :
    CompactSpace Z := by
  have h := f.isCompact_preimage (U := (⊤ : X.Opens)) (by simpa using isCompact_univ)
  rw [show (f ⁻¹ᵁ (⊤ : X.Opens)) = ⊤ from rfl] at h
  exact isCompact_univ_iff.mp (by simpa using h)

/-! ### The scheme-theoretic intersection with the other components -/

/-- The inclusion of the scheme-theoretic intersection of a component with the union of the other
components into that component.  This is the `g` of the twisted square. -/
abbrev componentIntersectionι (C : irreducibleComponents (X : Type u)) :
    (vanishingIdeal (otherComponents X C) ⊔ vanishingIdeal (componentCloseds X C)).subscheme ⟶
      componentScheme X C :=
  Scheme.IdealSheafData.inclusion le_sup_right

/-- **The intersection lies inside the other components.**  Its inclusion into `X` factors
through them because the vanishing ideal of the other components is below the ideal cutting the
intersection out, and `support` is antitone. -/
theorem mem_otherComponents_of_componentIntersection (C : irreducibleComponents (X : Type u))
    (z : (vanishingIdeal (otherComponents X C) ⊔
      vanishingIdeal (componentCloseds X C)).subscheme) :
    (componentι X C) ((componentIntersectionι X C) z) ∈ (otherComponents X C : Set X) := by
  have h := Scheme.IdealSheafData.inclusion_subschemeι
    (le_sup_right : vanishingIdeal (componentCloseds X C) ≤
      vanishingIdeal (otherComponents X C) ⊔ vanishingIdeal (componentCloseds X C))
  have hz : (componentι X C) ((componentIntersectionι X C) z)
      = (vanishingIdeal (otherComponents X C) ⊔
          vanishingIdeal (componentCloseds X C)).subschemeι z :=
    congrArg (fun φ : _ ⟶ X => φ z) h
  rw [hz]
  have hsub : (vanishingIdeal (otherComponents X C) ⊔
      vanishingIdeal (componentCloseds X C)).support ≤
        (vanishingIdeal (otherComponents X C)).support :=
    Scheme.IdealSheafData.support_antitone le_sup_left
  have hmem : ((vanishingIdeal (otherComponents X C) ⊔
      vanishingIdeal (componentCloseds X C)).subschemeι) z ∈
      ((vanishingIdeal (otherComponents X C) ⊔
        vanishingIdeal (componentCloseds X C)).support : Set X) := by
    rw [← Scheme.IdealSheafData.range_subschemeι]; exact ⟨z, rfl⟩
  have h2 := hsub hmem
  rwa [Stacks.AffineClosedUnion.support_vanishingIdeal] at h2

/-! ### The section on the component -/

variable (M : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
    (structureSheafRing X.toRingedSpace).property M]

omit [AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
  (structureSheafRing X.toRingedSpace).property M] in
/-- **Items (3) and (4) of Tag 01Q3 on the single component through `x`.**  The pullback of `M`
to the component is ample, so some positive power of it carries a global section whose
nonvanishing locus is affine, contains the chosen point of the component and is disjoint from the
scheme-theoretic intersection with the other components.

The last clause is the containment `Z_1 \ Z` of the source, restated as the hypothesis the
nilpotence step needs: that the nonvanishing locus misses the *image* of the intersection. -/
theorem exists_component_section (C : irreducibleComponents (X : Type u))
    [AlgebraicGeometry.SheafOfModules.IsInvertible (componentScheme X C).toRingedSpace.presheaf
      (structureSheafRing (componentScheme X C).toRingedSpace).property
      ((Scheme.Modules.pullback (componentι X C)).obj M)]
    (hample : AlgebraicGeometry.Scheme.Modules.IsAmple (componentScheme X C)
      ((Scheme.Modules.pullback (componentι X C)).obj M))
    (x' : componentScheme X C)
    (hx' : (componentι X C) x' ∈ otherComponentsCompl X C) :
    ∃ m : ℕ, 1 ≤ m ∧ ∃ s : (tensorPowerModule'
        ((Scheme.Modules.pullback (componentι X C)).obj M) ((m : ℕ) : ℤ)).sections,
      x' ∈ nonvanishingOpen (X := (componentScheme X C).toRingedSpace)
          (tensorPowerModule'
            ((Scheme.Modules.pullback (componentι X C)).obj M) ((m : ℕ) : ℤ)) s ∧
        (∀ z, (componentIntersectionι X C) z ∉
          nonvanishingLocus (X := (componentScheme X C).toRingedSpace)
            (tensorPowerModule'
              ((Scheme.Modules.pullback (componentι X C)).obj M) ((m : ℕ) : ℤ)) s) ∧
          IsAffineOpen (nonvanishingOpen (X := (componentScheme X C).toRingedSpace)
            (tensorPowerModule'
              ((Scheme.Modules.pullback (componentι X C)).obj M) ((m : ℕ) : ℤ)) s) := by
  obtain ⟨m, hm, s, hxs, hle, haff⟩ :=
    exists_sections_mem_nonvanishingOpen_le_of_isAmple
      ((Scheme.Modules.pullback (componentι X C)).obj M) hample
      (componentι X C ⁻¹ᵁ otherComponentsCompl X C) x' hx'
  exact ⟨m, hm, s, hxs,
    fun z hz => (hle hz) (mem_otherComponents_of_componentIntersection X C z), haff⟩

end Stacks.AmpleReducedDimensionOne

/-! ### Crossing the pullback-tensor-power comparison -/

namespace Stacks.AmpleReducedDimensionOne

/-- **A morphism of sheaves of modules carries a section killed by the unit of `g^* ⊣ g_*` to a
section killed by it.**  This is naturality of the unit in the module argument, read on sections;
it is stated for an arbitrary morphism so that no tensor-power spelling occurs in it. -/
theorem unit_app_eq_zero_of_hom {Z W : Scheme.{u}} (g : W ⟶ Z) {A B : Z.Modules} (φ : A ⟶ B)
    (V : Z.Opens) (y : Γ(A, V))
    (h : ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app A).app V y = 0) :
    ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app B).app V
      (AlgebraicGeometry.Scheme.Modules.Hom.app φ V y) = 0 := by
  have hnat := (Scheme.Modules.pullbackPushforwardAdjunction g).unit.naturality φ
  have h1 : AlgebraicGeometry.Scheme.Modules.Hom.app
      (φ ≫ (Scheme.Modules.pullbackPushforwardAdjunction g).unit.app B) V y
      = AlgebraicGeometry.Scheme.Modules.Hom.app
        ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app A ≫
          (Scheme.Modules.pullback g ⋙ Scheme.Modules.pushforward g).map φ) V y :=
    congrArg (fun ψ : A ⟶ _ => AlgebraicGeometry.Scheme.Modules.Hom.app ψ V y) hnat
  refine h1.trans ?_
  rw [AlgebraicGeometry.Scheme.Modules.Hom.comp_app]
  change AlgebraicGeometry.Scheme.Modules.Hom.app
    ((Scheme.Modules.pullback g ⋙ Scheme.Modules.pushforward g).map φ) V
      (AlgebraicGeometry.Scheme.Modules.Hom.app
        ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app A) V y) = 0
  rw [h, map_zero]

section Crossing

variable {Y Z W : Scheme.{u}} (g : W ⟶ Z) (i : Z ⟶ Y) (N : Y.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible Y.toRingedSpace.presheaf
    (structureSheafRing Y.toRingedSpace).property N]
  [AlgebraicGeometry.SheafOfModules.IsInvertible Z.toRingedSpace.presheaf
    (structureSheafRing Z.toRingedSpace).property ((Scheme.Modules.pullback i).obj N)]

/-- **The hypothesis of the twisted square, discharged.**  The canonical restriction leg of
`StacksDraft.AlgebraicGeometry.F3b.AffineClosedUnion.TwistedRestrict` kills the section of
`i^*(N^{⊗ k})` obtained from a section of `(i^*N)^{⊗ k}` that the unit of `g^* ⊣ g_*` kills.

Only naturality of the unit at the comparison isomorphism is used; the composite with the
pullback-composition comparison is linear and so carries `0` to `0`. -/
theorem unitRestrict_app_eq_zero_of_unit_app_eq_zero (k : ℕ)
    (σ : (tensorPowerModule' ((Scheme.Modules.pullback i).obj N) ((k : ℕ) : ℤ)).sections)
    (hvan : ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app
        (tensorPowerModule' ((Scheme.Modules.pullback i).obj N) ((k : ℕ) : ℤ))).app ⊤
          (σ.eval (op ⊤)) = 0) :
    (Stacks.AffineClosedUnion.unitRestrict g i
        (AlgebraicGeometry.Scheme.Modules.tensorPowerModules N ((k : ℕ) : ℤ))).app ⊤
      ((_root_.SheafOfModules.sectionsMap
        (AlgebraicGeometry.Scheme.Modules.pullbackTensorPowerIso i N k).inv σ).eval
          (op ⊤)) = 0 := by
  have key : Stacks.RingedSpace.pullbackUnit g.toLRSHom.toShHom
      ((Stacks.RingedSpace.pullbackFunctor i.toLRSHom.toShHom).obj
        (AlgebraicGeometry.Scheme.Modules.tensorPowerModules N ((k : ℕ) : ℤ)))
      ((opensMap i.toLRSHom.toShHom).op.obj (op (⊤ : Y.Opens)))
      ((_root_.SheafOfModules.sectionsMap
        (AlgebraicGeometry.Scheme.Modules.pullbackTensorPowerIso i N k).inv σ).eval (op ⊤)) = 0 :=
    unit_app_eq_zero_of_hom g
      (AlgebraicGeometry.Scheme.Modules.pullbackTensorPowerIso i N k).inv ⊤
      (σ.eval (op ⊤)) hvan
  refine Eq.trans (Stacks.AffineClosedUnion.unitRestrict_app_apply g i
    (AlgebraicGeometry.Scheme.Modules.tensorPowerModules N ((k : ℕ) : ℤ)) (op ⊤) _) ?_
  exact Eq.trans (congrArg (fun z => PresheafOfModules.Hom.app
    (Stacks.AffineClosedUnion.pullbackCompHom g i
      (AlgebraicGeometry.Scheme.Modules.tensorPowerModules N ((k : ℕ) : ℤ))).val
    ((opensMap g.toLRSHom.toShHom).op.obj
      ((opensMap i.toLRSHom.toShHom).op.obj (op (⊤ : Y.Opens)))) z) key) (map_zero _)

/-- **The preimage of the nonvanishing locus of the extended section is the nonvanishing locus of
the section it extends.**  Tag 0H78 identifies the preimage with the nonvanishing locus of the
pulled-back section, the twisted square says what that section is, and the comparison
isomorphism does not move a nonvanishing locus. -/
theorem preimage_nonvanishingOpen_eq_of_unit_app_top_eq (k : ℕ)
    (σ : (tensorPowerModule' ((Scheme.Modules.pullback i).obj N) ((k : ℕ) : ℤ)).sections)
    (c : Γ(AlgebraicGeometry.Scheme.Modules.tensorPowerModules N ((k : ℕ) : ℤ), ⊤))
    (hc : ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app
        (AlgebraicGeometry.Scheme.Modules.tensorPowerModules N ((k : ℕ) : ℤ))).app ⊤ c
      = (_root_.SheafOfModules.sectionsMap
          (AlgebraicGeometry.Scheme.Modules.pullbackTensorPowerIso i N k).inv σ).eval (op ⊤)) :
    i ⁻¹ᵁ nonvanishingOpen (X := Y.toRingedSpace)
        (AlgebraicGeometry.Scheme.Modules.tensorPowerModules N ((k : ℕ) : ℤ))
        (sectionsOfTop _ c)
      = nonvanishingOpen (X := Z.toRingedSpace)
          (tensorPowerModule' ((Scheme.Modules.pullback i).obj N) ((k : ℕ) : ℤ)) σ := by
  refine preimage_nonvanishingOpen_eq_of_iso i
    (AlgebraicGeometry.Scheme.Modules.tensorPowerModules N ((k : ℕ) : ℤ)) (sectionsOfTop _ c) _ σ
    (AlgebraicGeometry.Scheme.Modules.pullbackTensorPowerIso i N k) ?_
  refine (congrArg _ ((congrArg _ (sectionsOfTop_eval_top _ c)).trans hc)).trans ?_
  exact congrArg (fun φ => (ConcreteCategory.hom (φ.val.app (op ⊤))) (σ.eval (op ⊤)))
    (AlgebraicGeometry.Scheme.Modules.pullbackTensorPowerIso i N k).inv_hom_id

end Crossing

/-- **A global section killed by the unit of `j^* ⊣ j_*` vanishes everywhere on the image of
`j`.**  Tag 0H78 turns the preimage of its nonvanishing locus into the nonvanishing locus of its
restriction, and that restriction is the zero section. -/
theorem notMem_nonvanishingLocus_of_unit_app_top_eq_zero {Y Z : Scheme.{u}} (j : Z ⟶ Y)
    (N : Y.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 N]
    (c : Γ(N, ⊤))
    (hc : ((Scheme.Modules.pullbackPushforwardAdjunction j).unit.app N).app ⊤ c = 0) (z : Z) :
    j z ∉ nonvanishingLocus (X := Y.toRingedSpace) N (sectionsOfTop N c) := by
  intro hmem
  have heq := preimage_nonvanishingOpen_eq_of_iso j N (sectionsOfTop N c)
    ((Scheme.Modules.pullback j).obj N) (sectionsOfTop _ 0) (Iso.refl _)
    (by
      refine Eq.trans ?_ (sectionsOfTop_eval_top _ 0).symm
      exact (congrArg _ (sectionsOfTop_eval_top N c)).trans hc)
  have hz : z ∈ (j ⁻¹ᵁ nonvanishingOpen (X := Y.toRingedSpace) N (sectionsOfTop N c) : Z.Opens) :=
    hmem
  rw [heq] at hz
  exact Set.eq_empty_iff_forall_notMem.mp (nonvanishingLocus_sectionsOfTop_zero _) z hz

end Stacks.AmpleReducedDimensionOne

/-! ### Step 7 of the proof, and the ample sheaf -/

namespace Stacks.AmpleReducedDimensionOne

variable (X : Scheme.{u}) [AlgebraicGeometry.IsNoetherian X] (M : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
    (structureSheafRing X.toRingedSpace).property M]

/-- **Step 7 of the proof of Tag 09NX.**  For a point `x` off the overlap `T`, lying on the
component `C`, with `i^*M` ample on `C`, there are an exponent `n ≥ 1` and a global section of
`M^{⊗ n}` whose nonvanishing locus is affine and contains `x`.

This is exactly the hypothesis `hrest` of
`Stacks.AmpleReducedDimensionOne.isAmple_of_forall_notMem_componentOverlap`, one component at a
time.  The section is produced on the component by items (3) and (4) of Tag 01Q3, raised to a
power so that it restricts to zero on the intersection with the other components, and extended
to `X` by the twisted square; its nonvanishing locus lies in `C`, where its preimage is the
affine nonvanishing locus of the section it extends, so the one-piece case of Tag 09NL makes it
affine. -/
theorem exists_sections_of_notMem_componentOverlap [AlgebraicGeometry.IsReduced X]
    (C : irreducibleComponents (X : Type u))
    [AlgebraicGeometry.SheafOfModules.IsInvertible (componentScheme X C).toRingedSpace.presheaf
      (structureSheafRing (componentScheme X C).toRingedSpace).property
      ((Scheme.Modules.pullback (componentι X C)).obj M)]
    (hample : AlgebraicGeometry.Scheme.Modules.IsAmple (componentScheme X C)
      ((Scheme.Modules.pullback (componentι X C)).obj M))
    {x : X} (hx : x ∉ componentOverlap X) (hxC : x ∈ (C : Set X)) :
    ∃ n : ℕ, 1 ≤ n ∧
      ∃ s : (tensorPower X.toRingedSpace.presheaf
          (structureSheafRing X.toRingedSpace).property M (n : ℤ)).sections,
        x ∈ nonvanishingOpen (X := X.toRingedSpace)
            (tensorPower X.toRingedSpace.presheaf
              (structureSheafRing X.toRingedSpace).property M (n : ℤ)) s ∧
          IsAffineOpen (nonvanishingOpen (X := X.toRingedSpace)
            (tensorPower X.toRingedSpace.presheaf
              (structureSheafRing X.toRingedSpace).property M (n : ℤ)) s) := by
  obtain ⟨x', hx'⟩ := (range_componentι X C).ge hxC
  have hx'mem : (componentι X C) x' ∈ otherComponentsCompl X C :=
    hx' ▸ notMem_otherComponents X hx hxC
  obtain ⟨m, hm, s, hxs, hmiss, haff⟩ := exists_component_section X M C hample x' hx'mem
  have : CompactSpace (componentScheme X C) := compactSpace_of_quasiCompact X (componentι X C)
  have hci : IsClosedImmersion (componentIntersectionι X C) := inferInstance
  have hqc : QuasiCompact (componentIntersectionι X C) := inferInstance
  obtain ⟨N, hN, hvan⟩ :=
    AlgebraicGeometry.Scheme.Modules.exists_unit_app_eval_sectionPow'_eq_zero
      ((Scheme.Modules.pullback (componentι X C)).obj M) (componentIntersectionι X C) s hmiss
  have hb := unitRestrict_app_eq_zero_of_unit_app_eq_zero (componentIntersectionι X C)
    (componentι X C) M (m * N)
    (sectionPow' ((Scheme.Modules.pullback (componentι X C)).obj M) s N) (hvan ⊤)
  obtain ⟨c, hc, -⟩ :=
    Stacks.AffineClosedUnion.existsUnique_unit_app_eq_zero_of_closeds_sup_eq_top
      (AlgebraicGeometry.Scheme.Modules.tensorPowerModules M ((m * N : ℕ) : ℤ))
      (otherComponents X C) (componentCloseds X C)
      (otherComponents_sup_componentCloseds X C) ⊤ _ hb
  have hpre : componentι X C ⁻¹ᵁ nonvanishingOpen (X := X.toRingedSpace)
        (AlgebraicGeometry.Scheme.Modules.tensorPowerModules M ((m * N : ℕ) : ℤ))
        (sectionsOfTop _ c)
      = nonvanishingOpen (X := (componentScheme X C).toRingedSpace)
          (tensorPowerModule' ((Scheme.Modules.pullback (componentι X C)).obj M)
            ((m * N : ℕ) : ℤ))
          (sectionPow' ((Scheme.Modules.pullback (componentι X C)).obj M) s N) :=
    preimage_nonvanishingOpen_eq_of_unit_app_top_eq (componentι X C) M (m * N) _ c hc.2
  have hpreS : componentι X C ⁻¹ᵁ nonvanishingOpen (X := X.toRingedSpace)
        (AlgebraicGeometry.Scheme.Modules.tensorPowerModules M ((m * N : ℕ) : ℤ))
        (sectionsOfTop _ c)
      = nonvanishingOpen (X := (componentScheme X C).toRingedSpace)
          (tensorPowerModule' ((Scheme.Modules.pullback (componentι X C)).obj M)
            ((m : ℕ) : ℤ)) s :=
    hpre.trans (TopologicalSpace.Opens.ext
      (nonvanishingLocus_sectionPow' ((Scheme.Modules.pullback (componentι X C)).obj M) s N hN))
  have hsub : ((nonvanishingOpen (X := X.toRingedSpace)
        (AlgebraicGeometry.Scheme.Modules.tensorPowerModules M ((m * N : ℕ) : ℤ))
        (sectionsOfTop _ c) : Set X)) ⊆ Set.range (componentι X C).base := by
    refine fun y hy => otherComponentsCompl_subset_range X C (fun hyo => ?_)
    have hrange : y ∈ Set.range
        (vanishingIdeal (otherComponents X C)).subschemeι.base := by
      rw [Scheme.IdealSheafData.range_subschemeι,
        Stacks.AffineClosedUnion.support_vanishingIdeal]
      exact hyo
    obtain ⟨z, hz⟩ := hrange
    exact notMem_nonvanishingLocus_of_unit_app_top_eq_zero
      (vanishingIdeal (otherComponents X C)).subschemeι
      (AlgebraicGeometry.Scheme.Modules.tensorPowerModules M ((m * N : ℕ) : ℤ)) c hc.1 z
      (hz ▸ hy)
  refine ⟨m * N, le_trans (by norm_num) (Nat.mul_le_mul hm hN), sectionsOfTop _ c, ?_, ?_⟩
  · have hmem : x' ∈ componentι X C ⁻¹ᵁ nonvanishingOpen (X := X.toRingedSpace)
        (AlgebraicGeometry.Scheme.Modules.tensorPowerModules M ((m * N : ℕ) : ℤ))
        (sectionsOfTop _ c) := hpreS.ge hxs
    exact hx' ▸ hmem
  · refine isAffineOpen_of_isAffineOpen_preimage_of_subset_range (componentι X C) _ hsub ?_
    rw [hpreS]
    exact haff

/-- **[Stacks, Tag 09NX].**  A Noetherian, reduced, separated scheme of topological Krull
dimension at most one carries an ample invertible sheaf.

The sheaf is the `M` glued from the components by Tag 09NE: its distinguished global section `t`
serves every point of the overlap `T`, at exponent one, and
`Stacks.AmpleReducedDimensionOne.exists_sections_of_notMem_componentOverlap` serves every point
off `T`.

The hypothesis is `≤ 1` rather than `= 1`, so this applies to schemes of dimension zero as well
and is stronger than the source's statement.

The name carries `isReduced` because
`StacksTag09NX.exists_isAmple_of_topologicalKrullDim_le_one` already exists and is a *different*
theorem — Tag 09ND for an **integral** scheme, which is the first step of this proof rather than
its conclusion. Two declarations with that name-tail, one of them in a namespace called
`StacksTag09NX`, would be a twin-constant hazard, so the hypothesis
that distinguishes them is in the name. -/
@[stacks 09NX]
theorem exists_isAmple_of_isReduced_of_topologicalKrullDim_le_one (Y : Scheme.{u})
    [AlgebraicGeometry.IsNoetherian Y] [AlgebraicGeometry.IsReduced Y] [Y.IsSeparated]
    (hdim : topologicalKrullDim (Y : Type u) ≤ 1) :
    ∃ (M : Y.Modules)
      (_ : AlgebraicGeometry.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 M),
      AlgebraicGeometry.Scheme.Modules.IsAmple Y M := by
  obtain ⟨M, hM, t, htaff, hT, hcomp⟩ :=
    exists_isAffineOpen_nonvanishingOpen_componentOverlap_subset Y hdim
  have := hM
  refine ⟨M, hM, isAmple_of_forall_notMem_componentOverlap Y M t htaff hT fun x hx => ?_⟩
  obtain ⟨C, hxC, -⟩ := existsUnique_mem_of_notMem_componentOverlap Y hx
  obtain ⟨L, hL, s, e, hample, -⟩ := hcomp C
  have := hL
  have hinvp : AlgebraicGeometry.SheafOfModules.IsInvertible
      (componentScheme Y C).toRingedSpace.presheaf
      (structureSheafRing (componentScheme Y C).toRingedSpace).property
      ((Scheme.Modules.pullback (componentι Y C)).obj M) :=
    AlgebraicGeometry.SheafOfModules.isInvertible_pullback (componentι Y C) M
  exact exists_sections_of_notMem_componentOverlap Y M C
    (AlgebraicGeometry.Scheme.Modules.isAmple_of_iso
      (show L ≅ (Scheme.Modules.pullback (componentι Y C)).obj M from e.symm) hample)
    hx hxC

end Stacks.AmpleReducedDimensionOne

end
