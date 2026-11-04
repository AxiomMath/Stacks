module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleFirstOrderIdeal
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceIdeals

/-!
# The conormal module of a first-order thickening, on an étale chart

Let `X` be an algebraic space over a scheme `S` contained in a big fppf site `B` and let
`Z ⊆ X` be a *first-order* thickening with inclusion `i : Z ⟶ X`.
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalModuleFirstOrderIdeal.lean` includes the conormal
module into the structure sheaf of the ambient space,

`AlgebraicGeometry.Space.firstOrderConormalModuleι : i_*𝒞_{Z/X} ⟶ 𝒪_X`,

pinned by the equation that composing it with the unit `𝓘 ⟶ i_*𝒞_{Z/X}` is the inclusion of the
defining ideal sheaf.  This file reads that inclusion **on the sections over one étale scheme
chart** `V` of `X` and identifies its image there: it is injective, and its range is exactly the
kernel of pullback of regular functions along the closed immersion of schemes `Z ×_X V ⟶ V`,

`𝒞_{Z/X}(V) ≅ ker(Γ(V, ⊤) ⟶ Γ(Z ×_X V, ⊤))`.

That kernel is the module `Stacks.Thickenings.conormalModuleAlong` of the scheme-level
deformation theory of `StacksFrontier/AlgebraicGeometry/Thickenings/Conormal.lean`, which is stated
for an affine ambient thickening as `RingHom.ker i.appTop.hom`.  So this is the comparison of the
conormal module of a first-order thickening of algebraic spaces with its scheme-level avatar on a
chart, and it is what lets a statement of the scheme-level theory be applied to a section of a
module on the small étale site.

## Main results

* `AlgebraicGeometry.Space.injective_firstOrderConormalModuleι_app`: the inclusion is injective
  on the sections over every étale chart.
* `AlgebraicGeometry.Space.range_firstOrderConormalModuleι_app`: its range over a chart is the
  defining ideal of the thickening at that chart.
* `AlgebraicGeometry.Space.mem_range_firstOrderConormalModuleι_app_iff_appTop_eq_zero`:
  **the comparison**, that same range written as `RingHom.ker` of pullback of regular functions
  along the chart-level closed immersion of schemes, in the membership form in which a
  scheme-level element is recognized as a conormal section; and
  `AlgebraicGeometry.Space.existsUnique_firstOrderConormalModuleι_app_eq_of_mem_ker`, which
  produces the conormal section of such an element.
* `AlgebraicGeometry.Space.mem_range_firstOrderConormalModuleι_app_iff`: the same membership,
  against the defining ideal of the thickening at the chart.
* `AlgebraicGeometry.Space.exists_firstOrderConormalModuleι_app_eq`: the surjectivity half on
  its own, producing the conormal section with a prescribed value.

## Implementation notes

**Both halves come from the characterising equation and nothing else.**  The unit
`𝓘 ⟶ i_*𝒞_{Z/X}` of a first-order thickening is an isomorphism of sheaves of modules
(`AlgebraicGeometry.Space.firstOrderConormalModuleIso`), hence bijective on the sections over
every object of the site; and composed with the inclusion it is the inclusion of a submodule of
`𝒪_X`, which is injective on sections with range the submodule.  So the inclusion is injective
with the same range.  No property of the small étale site, and no further geometry, enters.

**Bijectivity on sections is extracted by hand** rather than from an instance.  As the
implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalModuleFirstOrderIdeal.lean` record, instance
resolution for invertibility at a morphism of sheaves of modules on the small étale site does not
terminate, and the two round-trip equations of the isomorphism are what is used instead: each is
read at a section by `CategoryTheory.Iso.hom_inv_id` and
`CategoryTheory.Iso.inv_hom_id` after the applied composite has been turned into a composite
applied, in the same way as
`AlgebraicGeometry.Space.firstOrderConormalModuleι_liftDifference` does.

**The chart-level kernel is `AlgebraicGeometry.Space.definingIdealAt`**, which
`AlgebraicGeometry.Space.definingIdealAt_eq_ker` computes as the kernel of
`AlgebraicGeometry.Scheme.Γ` applied to the chart base change of the inclusion.  No affineness of
the chart is needed for that identification; affineness enters only when the kernel is to be
recognized as `RingHom.ker i.appTop.hom` for an *affine* ambient thickening, which is the shape
the scheme-level deformation theory is stated at and is a hypothesis of that theory, not of this
comparison.

**No `@[stacks]` attribute is placed.**  The identification of `𝒞_{Z/X}` with `𝓘/𝓘²` is
[Stacks Project, Tag 04CN], whose square-zero case the imported file proves and claims no tag
for; what is added here is the passage to the sections over a chart, which is a reading of that
statement and not a clause of any tag.

## References

* [Stacks Project, Tag 04CN](https://stacks.math.columbia.edu/tag/04CN)
* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
* [Stacks Project, Tag 01R4](https://stacks.math.columbia.edu/tag/01R4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X : AlgebraicSpaces B S hS} (Z : ClosedSubspaces B S hS X.1)

/-! ### The unit of a first-order thickening is bijective on the sections over a chart -/

/-- **The unit `𝓘 ⟶ i_*𝒞_{Z/X}` of a first-order thickening is bijective on the sections over
every object of the small étale site.**  It is an isomorphism of sheaves of modules by
`AlgebraicGeometry.Space.firstOrderConormalModuleIso`, and the two round-trip equations of an
isomorphism are inverse functions on sections. -/
theorem bijective_firstOrderConormalModuleIso_app
    (hZ : IsFirstOrderThickening B S hS X Z.1) (U : (SmallEtale B S hS X.1)ᵒᵖ) :
    Function.Bijective ((firstOrderConormalModuleIso B S hS Z hZ).hom.val.app U) := by
  set e := firstOrderConormalModuleIso B S hS Z hZ
  exact ⟨Function.LeftInverse.injective fun x =>
    congrArg (fun f => f.val.app U x) e.hom_inv_id,
    fun y => ⟨_, congrArg (fun f => f.val.app U y) e.inv_hom_id⟩⟩

/-! ### The inclusion of the conormal module on a chart -/

/-- **The sections of the defining ideal sheaf over an étale chart are the defining ideal at that
chart**, as a range: the inclusion of the submodule is the inclusion of a subtype. -/
theorem range_definingIdealSheaf_ι_app (U : (SmallEtale B S hS X.1)ᵒᵖ) :
    Set.range ((definingIdealSheaf B S hS X Z).ι.val.app U) =
      (definingIdealAt B S hS X Z U : Set ((structureRingSheaf B S hS X).obj.obj U)) := by
  refine Set.eq_of_subset_of_subset ?_ ?_
  · rintro y ⟨x, rfl⟩
    exact x.2
  · intro y hy
    exact ⟨⟨y, hy⟩, rfl⟩

/-- **The inclusion `i_*𝒞_{Z/X} ⟶ 𝒪_X` of the conormal module of a first-order thickening,
composed with the unit, is the inclusion of the defining ideal — read at a section.**  This is
`AlgebraicGeometry.Space.firstOrderConormalModuleIso_hom_comp_firstOrderConormalModuleι` on the
sections over one object of the site. -/
theorem firstOrderConormalModuleι_app_firstOrderConormalModuleIso_app
    (hZ : IsFirstOrderThickening B S hS X Z.1) (U : (SmallEtale B S hS X.1)ᵒᵖ)
    (x : ((definingIdealSheaf B S hS X Z).toSheafOfModules).val.obj U) :
    (firstOrderConormalModuleι B S hS Z hZ).val.app U
        ((firstOrderConormalModuleIso B S hS Z hZ).hom.val.app U x) =
      (definingIdealSheaf B S hS X Z).ι.val.app U x :=
  congrArg (fun f => f.val.app U x)
    (firstOrderConormalModuleIso_hom_comp_firstOrderConormalModuleι B S hS Z hZ)

/-- **The inclusion of the conormal module of a first-order thickening is injective on the
sections over every étale chart.**  Composed with the unit it is the inclusion of a submodule of
`𝒪_X`, which is injective on sections, and the unit is bijective on sections. -/
theorem injective_firstOrderConormalModuleι_app
    (hZ : IsFirstOrderThickening B S hS X Z.1) (U : (SmallEtale B S hS X.1)ᵒᵖ) :
    Function.Injective ((firstOrderConormalModuleι B S hS Z hZ).val.app U) := by
  intro a b hab
  obtain ⟨a', rfl⟩ := (bijective_firstOrderConormalModuleIso_app B S hS Z hZ U).2 a
  obtain ⟨b', rfl⟩ := (bijective_firstOrderConormalModuleIso_app B S hS Z hZ U).2 b
  rw [firstOrderConormalModuleι_app_firstOrderConormalModuleIso_app B S hS Z hZ U a',
    firstOrderConormalModuleι_app_firstOrderConormalModuleIso_app B S hS Z hZ U b'] at hab
  exact congrArg _ (Subtype.ext hab)

/-- **The range of the inclusion of the conormal module over an étale chart is the defining ideal
of the thickening at that chart.**  Composed with the unit — which is surjective on sections —
the inclusion is the inclusion of the submodule
`AlgebraicGeometry.Space.definingIdealSheaf`, whose sections are
`AlgebraicGeometry.Space.definingIdealAt`. -/
theorem range_firstOrderConormalModuleι_app
    (hZ : IsFirstOrderThickening B S hS X Z.1) (U : (SmallEtale B S hS X.1)ᵒᵖ) :
    Set.range ((firstOrderConormalModuleι B S hS Z hZ).val.app U) =
      (definingIdealAt B S hS X Z U : Set ((structureRingSheaf B S hS X).obj.obj U)) := by
  rw [← range_definingIdealSheaf_ι_app B S hS Z U,
    ← (bijective_firstOrderConormalModuleIso_app B S hS Z hZ U).2.range_comp]
  exact congrArg Set.range (funext
    (firstOrderConormalModuleι_app_firstOrderConormalModuleIso_app B S hS Z hZ U))

/-- **A section of the structure sheaf over an étale chart is the value of a conormal section
exactly when it lies in the defining ideal of the thickening there.**  The membership form of
`AlgebraicGeometry.Space.range_firstOrderConormalModuleι_app`. -/
theorem mem_range_firstOrderConormalModuleι_app_iff
    (hZ : IsFirstOrderThickening B S hS X Z.1) (U : (SmallEtale B S hS X.1)ᵒᵖ)
    (y : (structureRingSheaf B S hS X).obj.obj U) :
    y ∈ Set.range ((firstOrderConormalModuleι B S hS Z hZ).val.app U) ↔
      y ∈ definingIdealAt B S hS X Z U := by
  rw [range_firstOrderConormalModuleι_app B S hS Z hZ U]
  exact Iff.rfl

/-- **The conormal section with a prescribed value.**  Every section of the structure sheaf over
an étale chart lying in the defining ideal of the thickening is the value of exactly one section
of the conormal module there; this is the existence half, with uniqueness supplied by
`AlgebraicGeometry.Space.injective_firstOrderConormalModuleι_app`. -/
theorem exists_firstOrderConormalModuleι_app_eq
    (hZ : IsFirstOrderThickening B S hS X Z.1) (U : (SmallEtale B S hS X.1)ᵒᵖ)
    {y : (structureRingSheaf B S hS X).obj.obj U} (hy : y ∈ definingIdealAt B S hS X Z U) :
    ∃! c, (firstOrderConormalModuleι B S hS Z hZ).val.app U c = y := by
  obtain ⟨c, hc⟩ := (mem_range_firstOrderConormalModuleι_app_iff B S hS Z hZ U y).2 hy
  exact ⟨c, hc, fun d hd =>
    injective_firstOrderConormalModuleι_app B S hS Z hZ U (hd.trans hc.symm)⟩

/-! ### The comparison with the scheme-level conormal module -/

/-- Membership in the defining ideal at a chart is vanishing of pullback to `Z ×_X V`. -/
private theorem mem_definingIdealAt_iff_appTop_eq_zero (U : SmallEtale B S hS X.1)
    (y : (structureRingSheaf B S hS X).obj.obj (op U)) :
    y ∈ definingIdealAt B S hS X Z (op U) ↔ (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
      (Z.2.2.rep.snd U.1.hom)).op).hom y = 0 := by
  rw [definingIdealAt_eq_ker B S hS X Z U]
  exact RingHom.mem_ker

/-- **The comparison of the conormal module of a first-order thickening of algebraic spaces with
its scheme-level avatar on an étale chart.**  Over an étale scheme chart `V` of `X` the range of
the inclusion `i_*𝒞_{Z/X} ⟶ 𝒪_X` is the kernel of pullback of regular functions along the closed
immersion of schemes `Z ×_X V ⟶ V`.

That kernel is the module of `Stacks.Thickenings.conormalModuleAlong`, which the scheme-level
deformation theory of `StacksFrontier/AlgebraicGeometry/MoreMorphisms/MapDerivationAction.lean` is
stated with as `RingHom.ker i.appTop.hom` for an affine ambient thickening.  Together with
`AlgebraicGeometry.Space.injective_firstOrderConormalModuleι_app` this identifies the two
conormal modules on a chart. -/
theorem mem_range_firstOrderConormalModuleι_app_iff_appTop_eq_zero
    (hZ : IsFirstOrderThickening B S hS X Z.1) (U : SmallEtale B S hS X.1)
    (y : (structureRingSheaf B S hS X).obj.obj (op U)) :
    y ∈ Set.range ((firstOrderConormalModuleι B S hS Z hZ).val.app (op U)) ↔
      (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
        (Z.2.2.rep.snd U.1.hom)).op).hom y = 0 := by
  exact (mem_range_firstOrderConormalModuleι_app_iff B S hS Z hZ (op U) y).trans
    (mem_definingIdealAt_iff_appTop_eq_zero B S hS Z U y)

/-- **The conormal section with a prescribed value, in the scheme-level form.**  A regular
function on an étale scheme chart `V` of `X` killed by pullback along the closed immersion of
schemes `Z ×_X V ⟶ V` — that is, an element of the module
`Stacks.Thickenings.conormalModuleAlong` of the scheme-level deformation theory — is the value of
exactly one section of the conormal module over `V`.

This is the form in which a scheme-level conormal element is turned into a section of
`AlgebraicGeometry.Space.conormalModule`. -/
theorem existsUnique_firstOrderConormalModuleι_app_eq_of_mem_ker
    (hZ : IsFirstOrderThickening B S hS X Z.1) (U : SmallEtale B S hS X.1)
    {y : (structureRingSheaf B S hS X).obj.obj (op U)}
    (hy : (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
      (Z.2.2.rep.snd U.1.hom)).op).hom y = 0) :
    ∃! c, (firstOrderConormalModuleι B S hS Z hZ).val.app (op U) c = y := by
  exact exists_firstOrderConormalModuleι_app_eq B S hS Z hZ (op U)
    ((mem_definingIdealAt_iff_appTop_eq_zero B S hS Z U y).2 hy)

end AlgebraicGeometry.Space

end
