module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.BaseLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.Unramified
public import StacksFrontier.AlgebraicGeometry.Stacks.DeligneMumfordIsomCriterion
public import StacksFrontier.AlgebraicGeometry.Stacks.DeligneMumfordLocus
public import StacksFrontier.AlgebraicGeometry.Stacks.FullSubcategoryBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.IsomGroupSpace
public import StacksFrontier.AlgebraicGeometry.Stacks.OpenLocusFullSubcategory
public import StacksFrontier.AlgebraicGeometry.Stacks.Points
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableMorphismAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationAbsoluteDMEquivalence

/-!
# Field-valued points of the Deligne–Mumford and quasi-Deligne–Mumford loci

**Stacks 0DSN.** For a field-valued point `x` of an algebraic stack `𝒳`, with automorphism group
algebraic space `G_x` over the field of `x`:

1. `x` lies in the Deligne–Mumford locus exactly when `G_x` is unramified over the field;
2. `x` lies in the quasi-Deligne–Mumford locus exactly when `G_x` is locally quasi-finite over
   the field.

The two loci are `AlgebraicGeometry.Stack.dmLocus` and
`AlgebraicGeometry.Stack.quasiDMLocus` of
`StacksFrontier/AlgebraicGeometry/Stacks/DeligneMumfordLocus.lean`, built there as the supremum of
the object properties of the Deligne–Mumford, resp. quasi-Deligne–Mumford, open substacks. By
`AlgebraicGeometry.Stack.dmLocus_apply_iff` membership of the locus is exactly containment in
*some* open substack with the property, which is the form the source's argument takes.

## Proof

The source chooses a smooth chart `U → 𝒳`, cuts out by **Stacks 0DSJ** the largest open
`U' ⊆ U` over which the automorphism group algebraic space `G` of `U → 𝒳` is unramified, resp.
locally quasi-finite, descends it to an open substack by **Stacks 0507**, and identifies the
fibre of `G` at a point with `G_x` after a field extension. The proof here runs the same
argument object by object, which makes the chart and the field extension unnecessary: the
objects `x` of `𝒳` over a scheme `T` whose automorphism group algebraic space `Isom_𝒳(x, x)` is
unramified, resp. locally quasi-finite, over `T` form an open substack
(`AlgebraicGeometry.Stack.automorphismLocusSubstack`). The automorphism group algebraic space of
a pullback of `x` is the base change of `Isom_𝒳(x, x)`, so the 2-fibre product of that substack
with `x` is the base locus of **Stacks 0DSJ**, which is open; and its full subcategory is an
algebraic stack by **Stacks 05UM**. A field-valued point lies in it exactly when its `G_x` has
the property.

It remains to see that an open substack is DM, resp. quasi-DM, exactly when all its objects have
unramified, resp. locally quasi-finite, automorphism group algebraic spaces. That is the content
of **Stacks 0CL0**, parts (4) and (5), for the structure morphism, through the pseudo-torsor
lemma **Stacks 0DSK**: the base change of the diagonal along a point `(x₁, x₂)` is
`Isom_𝒳(x₁, x₂)`, a pseudo-torsor under `Isom_𝒳(x₂, x₂)` (**Stacks 04YP**, part (2)). This is
`AlgebraicGeometry.Stack.isDMOver_iff_forall_isUnramified_isomSpaceOver` and its quasi-DM twin,
read in the absolute sense by **Stacks 050N**. The automorphism group algebraic spaces of an open
substack are those computed in `𝒳`, the inclusion being fully faithful
(`AlgebraicGeometry.Stack.holdsOnEveryEtaleChart_isomSpace_fullSubcategory_iff`).

## Main definitions

* `AlgebraicGeometry.Stack.IsUnramifiedAutomorphismGroupSpace` and
  `AlgebraicGeometry.Stack.IsLocallyQuasiFiniteAutomorphismGroupSpace`: the two conditions on
  `G_x` that **Stacks 0DSN** tests.
* `AlgebraicGeometry.Stack.automorphismLocus`: the objects whose automorphism group algebraic
  space has a given property.
* `AlgebraicGeometry.Stack.automorphismLocusSubstack`: that locus as an open substack, given the
  open subspaces of the bases cutting it out.

## Main results

* `AlgebraicGeometry.Stack.dmLocus_apply_iff_isUnramifiedAutomorphismGroupSpace`:
  **Stacks 0DSN**, part (1).
* `AlgebraicGeometry.Stack.quasiDMLocus_apply_iff_isLocallyQuasiFiniteAutomorphismGroupSpace`:
  **Stacks 0DSN**, part (2).

## Implementation notes

A field-valued point is `AlgebraicGeometry.Stack.FieldValuedPoint`, which records the field, the
object of the site identified with its spectrum, and the object of the fibre category over it;
this is the form **Stacks 04XF** takes in the library. The automorphism group algebraic space is
`AlgebraicGeometry.Stack.automorphismGroupSpace` of **Stacks 04YP**, part (1), taken at that
object of the fibre category, and its structural morphism to the field spectrum is
`.obj.X.hom`. Unramifiedness and local quasi-finiteness are the algebraic-space properties
`AlgebraicGeometry.Space.IsUnramified` (**Stacks 03ZH**) and
`AlgebraicGeometry.Space.IsLocallyQuasiFinite` (**Stacks 03XJ**), tested over the field spectrum
as base, which is the base the group space lives over. Both are the every-étale-chart condition
`AlgebraicGeometry.Space.HoldsOnEveryEtaleChart` at a property of morphisms of schemes, so the
locus and its open substack are built once for an arbitrary such property, together with the
open subspaces cutting the locus out of each base; **Stacks 0DSJ** supplies those in the two
cases of the lemma.

## References

* [Stacks Project, Tag 03XJ](https://stacks.math.columbia.edu/tag/03XJ)
* [Stacks Project, Tag 03ZH](https://stacks.math.columbia.edu/tag/03ZH)
* [Stacks Project, Tag 0507](https://stacks.math.columbia.edu/tag/0507)
* [Stacks Project, Tag 050N](https://stacks.math.columbia.edu/tag/050N)
* [Stacks Project, Tag 05UM](https://stacks.math.columbia.edu/tag/05UM)
* [Stacks Project, Tag 04XF](https://stacks.math.columbia.edu/tag/04XF)
* [Stacks Project, Tag 04YP](https://stacks.math.columbia.edu/tag/04YP)
* [Stacks Project, Tag 0CL0](https://stacks.math.columbia.edu/tag/0CL0)
* [Stacks Project, Tag 0DSJ](https://stacks.math.columbia.edu/tag/0DSJ)
* [Stacks Project, Tag 0DSK](https://stacks.math.columbia.edu/tag/0DSK)
* [Stacks Project, Tag 0DSM](https://stacks.math.columbia.edu/tag/0DSM)
* [Stacks Project, Tag 0DSN](https://stacks.math.columbia.edu/tag/0DSN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The automorphism group algebraic space of a field-valued point `x` of an algebraic stack
`𝒳` is *unramified* over the field of `x`: the condition **Stacks 0DSN**, part (1), tests. -/
noncomputable abbrev IsUnramifiedAutomorphismGroupSpace
    (𝒳 : AlgebraicStacks.{u, w} B S hS) (x : FieldValuedPoint B S hS 𝒳.val.val) : Prop :=
  Space.IsUnramified B x.base.left.1 x.base.left.2
    (automorphismGroupSpace B S hS 𝒳.val 𝒳.property x.base ⟨x.obj, x.over⟩).obj.X.hom

/-- The automorphism group algebraic space of a field-valued point `x` of an algebraic stack
`𝒳` is *locally quasi-finite* over the field of `x`: the condition **Stacks 0DSN**, part (2),
tests. -/
noncomputable abbrev IsLocallyQuasiFiniteAutomorphismGroupSpace
    (𝒳 : AlgebraicStacks.{u, w} B S hS) (x : FieldValuedPoint B S hS 𝒳.val.val) : Prop :=
  Space.IsLocallyQuasiFinite B x.base.left.1 x.base.left.2
    (automorphismGroupSpace B S hS 𝒳.val 𝒳.property x.base ⟨x.obj, x.over⟩).obj.X.hom

/-! ### The locus of objects with a given automorphism property -/

section Locus

variable (P : MorphismProperty Scheme.{u}) (𝒳 : AlgebraicStacks.{u, w} B S hS)

/-- The objects of an algebraic stack `𝒳` whose automorphism group algebraic space has a property
`P` tested on étale charts, over the scheme the object lies over. -/
def automorphismLocus (P : MorphismProperty Scheme.{u}) (𝒳 : AlgebraicStacks.{u, w} B S hS) :
    ObjectProperty 𝒳.val.val.obj := fun x =>
  letI : 𝒳.val.val.p.IsFibered := 𝒳.val.isFiberedInGroupoids.isFibered
  Space.HoldsOnEveryEtaleChart B (𝒳.val.val.p.obj x).left.1 (𝒳.val.val.p.obj x).left.2 P
    (terminal.from (isomSpace B S hS 𝒳.val (𝒳.val.val.p.obj x) (Functor.Fiber.mk rfl)
      (Functor.Fiber.mk rfl)))

/-- Membership of the automorphism locus, read at an object of a fibre. -/
theorem automorphismLocus_iff {U : BigFppfOver B S hS} (x : 𝒳.val.val.p.Fiber U) :
    letI : 𝒳.val.val.p.IsFibered := 𝒳.val.isFiberedInGroupoids.isFibered
    automorphismLocus B S hS P 𝒳 x.1 ↔
      Space.HoldsOnEveryEtaleChart B U.left.1 U.left.2 P
        (terminal.from (isomSpace B S hS 𝒳.val U x x)) := by
  obtain ⟨x, rfl⟩ := x
  rfl

/-- The automorphism locus is closed under isomorphism: an isomorphism of `𝒳` lies over an
isomorphism of the site and is cartesian, so the two automorphism spaces correspond. -/
instance isClosedUnderIsomorphisms_automorphismLocus :
    (automorphismLocus B S hS P 𝒳).IsClosedUnderIsomorphisms := by
  refine ⟨fun {x' x} i hx => ?_⟩
  let : 𝒳.val.val.p.IsFibered := 𝒳.val.isFiberedInGroupoids.isFibered
  let p := 𝒳.val.val.p
  have hlift : p.IsHomLift (p.map i.hom) i.hom := IsHomLift.map p i.hom
  have hm : p.IsStronglyCartesian (p.map i.hom) i.hom :=
    𝒳.val.isFiberedInGroupoids.isStronglyCartesian_homLift _ _
  exact (holdsOnEveryEtaleChart_isomSpace_iff_of_isIso B S hS P 𝒳.val (p.map i.hom)
    (x := Functor.Fiber.mk rfl) (x' := Functor.Fiber.mk rfl) i.hom hm).mp hx

variable (W : ∀ (U : BigFppfOver B S hS) (_x : 𝒳.val.val.p.Fiber U),
    Subfunctor (siteTerminalSpace B S hS U))
  (hWmem : letI : 𝒳.val.val.p.IsFibered := 𝒳.val.isFiberedInGroupoids.isFibered
    ∀ (U : BigFppfOver B S hS) (x : 𝒳.val.val.p.Fiber U)
      (X : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ) (s : (siteTerminalSpace B S hS U).obj X),
      s ∈ (W U x).obj X ↔ Space.HoldsOnEveryEtaleChart B U.left.1 U.left.2 P
        (pullback.snd (isomSpaceOver B S hS 𝒳.val U x x).hom (yonedaEquiv.symm s)))

include hWmem in
/-- **The automorphism locus at a pullback is read off a subfunctor of the base.** Let `W` assign
to every object `x` over `U` a subfunctor of the base whose sections are those over which the
automorphism group algebraic space of `x` has `P`. Then for a morphism `φ : x' ⟶ x` of `𝒳`, lying
over `e : V ⟶ U`, the object `x'` lies in the automorphism locus exactly when the section of the
base given by `V ⟶ U` lies in `W x`. -/
theorem automorphismLocus_iff_mem {U : BigFppfOver B S hS} (x : 𝒳.val.val.p.Fiber U)
    {x' : 𝒳.val.val.obj} (φ : x' ⟶ x.1) :
    automorphismLocus B S hS P 𝒳 x' ↔
      terminal.from (Over.mk (𝒳.val.val.p.map φ ≫ eqToHom x.2).left :
          BigFppfOver B U.left.1 U.left.2) ∈
        (W U x).obj (Opposite.op (Over.mk (𝒳.val.val.p.map φ ≫ eqToHom x.2).left)) := by
  let : 𝒳.val.val.p.IsFibered := 𝒳.val.isFiberedInGroupoids.isFibered
  let p := 𝒳.val.val.p
  let e : p.obj x' ⟶ U := p.map φ ≫ eqToHom x.2
  have hlift : p.IsHomLift e φ := IsHomLift.of_fac' p e φ rfl x.2 (by simp [e])
  have hm : p.IsStronglyCartesian e φ :=
    𝒳.val.isFiberedInGroupoids.isStronglyCartesian_homLift e φ
  let c : BigFppfOver B U.left.1 U.left.2 := Over.mk e.left
  refine Iff.trans ?_ (hWmem U x _ (terminal.from c)).symm
  have hys : yonedaEquiv.symm (terminal.from c) = yoneda.map (terminal.from c) := by
    ext X a
    exact terminalIsTerminal.hom_ext _ _
  rw [hys]
  exact holdsOnEveryEtaleChart_isomSpace_iff_pullbackSnd B S hS P 𝒳.val e
    (x' := Functor.Fiber.mk rfl) φ hm
    (fun X => ⟨fun a b => terminalIsTerminal.hom_ext a b⟩) _ (yoneda.map (terminal.from c))

include hWmem in
/-- The automorphism locus is inherited along any morphism into an object of it. -/
theorem automorphismLocus_of_hom {x x' : 𝒳.val.val.obj} (hx : automorphismLocus B S hS P 𝒳 x)
    (φ : x' ⟶ x) : automorphismLocus B S hS P 𝒳 x' := by
  let p := 𝒳.val.val.p
  let x₀ : p.Fiber (p.obj x) := Functor.Fiber.mk rfl
  rw [automorphismLocus_iff_mem B S hS P 𝒳 W hWmem x₀ (𝟙 x)] at hx
  rw [automorphismLocus_iff_mem B S hS P 𝒳 W hWmem x₀ φ]
  let c : BigFppfOver B (p.obj x).left.1 (p.obj x).left.2 := Over.mk (p.map φ ≫ eqToHom x₀.2).left
  let c₀ : BigFppfOver B (p.obj x).left.1 (p.obj x).left.2 :=
    Over.mk (p.map (𝟙 x) ≫ eqToHom x₀.2).left
  let h : c ⟶ c₀ := Over.homMk (p.map φ).left (by simp [c, c₀])
  have key : (siteTerminalSpace B S hS (p.obj x)).map h.op (terminal.from c₀) = terminal.from c :=
    terminalIsTerminal.hom_ext _ _
  change terminal.from c ∈ (W (p.obj x) x₀).obj (Opposite.op c)
  rw [← key]
  exact (W (p.obj x) x₀).map h.op hx

variable (hWopen : ∀ (U : BigFppfOver B S hS) (x : 𝒳.val.val.p.Fiber U),
  Space.IsOpenSubspace B U.left.1 U.left.2 (W U x))

/-- An object of the big fppf site of `X` whose morphism to the terminal object is an open
immersion of schemes has an open immersion as structure morphism. -/
theorem isOpenImmersion_hom_of_isOpenImmersion_toScheme_map {X : Scheme.{u}} {hX : B.Contains X}
    {V : BigFppfOver B X hX} (f : V ⟶ ⊤_ (BigFppfOver B X hX))
    (hf : _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B X hX).map f)) :
    _root_.AlgebraicGeometry.IsOpenImmersion V.hom.hom := by
  have hV : V.hom = f.left ≫ (⊤_ (BigFppfOver B X hX)).hom := (Over.w f).symm
  let t := terminalIsoIsTerminal (Over.mkIdTerminal (X := B.obj hX))
  have ht : (⊤_ (BigFppfOver B X hX)).hom = t.hom.left := by
    simpa using (Over.w t.hom).symm
  have : IsIso t.hom.left := inferInstanceAs (IsIso ((Over.forget _).map t.hom))
  have : IsIso t.hom.left.hom := inferInstanceAs (IsIso ((ObjectProperty.ι _).map t.hom.left))
  have : _root_.AlgebraicGeometry.IsOpenImmersion f.left.hom := hf
  rw [hV, ht]
  change _root_.AlgebraicGeometry.IsOpenImmersion (f.left.hom ≫ t.hom.left.hom)
  infer_instance

include hWmem hWopen in
/-- **The automorphism locus is open.** For a scheme-valued point `y` of `𝒳` over `U`, the objects
`T` of the big fppf site of `U` for which `y(T)` lies in the automorphism locus are those mapping
to an open subscheme of `U`: the one representing the open subspace `W` attached to the value of
`y` at the terminal object. -/
theorem exists_isOpenImmersion_forall_nonempty_hom_iff_automorphismLocus
    (U : BigFppfOver B S hS) (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒳.val.val.obj)
    (hy : y ⋙ 𝒳.val.val.p = Over.map U.hom) :
    ∃ V : BigFppfOver B U.left.1 U.left.2, _root_.AlgebraicGeometry.IsOpenImmersion V.hom.hom ∧
      ∀ T : BigFppfOver B U.left.1 U.left.2,
        Nonempty (T ⟶ V) ↔ automorphismLocus B S hS P 𝒳 (y.obj T) := by
  let p := 𝒳.val.val.p
  let x₀ : p.Fiber U := Functor.sliceValue p U y hy
  let W₀ := W U x₀
  have hrel := (hWopen U x₀).2
  let g : yoneda.obj (⊤_ (BigFppfOver B U.left.1 U.left.2)) ⟶ siteTerminalSpace B S hS U := 𝟙 _
  let V := hrel.rep.pullback g
  let snd : V ⟶ ⊤_ _ := hrel.rep.snd g
  -- The open subscheme cut out by `W₀`.
  have hmem : ∀ T : BigFppfOver B U.left.1 U.left.2,
      Nonempty (T ⟶ V) ↔ terminal.from T ∈ W₀.obj (Opposite.op T) := by
    refine fun T => ⟨fun ⟨k⟩ => ?_, fun hT => ?_⟩
    · convert ((hrel.rep.fst g).app (Opposite.op T) k).2 using 1
      exact terminalIsTerminal.hom_ext _ _
    · let a : yoneda.obj T ⟶ W₀.toFunctor := yonedaEquiv.symm ⟨terminal.from T, hT⟩
      have hc : a ≫ W₀.ι = yoneda.map (terminal.from T) ≫ g := by
        ext X t
        exact terminalIsTerminal.hom_ext _ _
      exact ⟨yoneda.preimage
        ((hrel.rep.isPullback g).lift a (yoneda.map (terminal.from T)) hc ≫ 𝟙 _)⟩
  refine ⟨V, isOpenImmersion_hom_of_isOpenImmersion_toScheme_map B snd (hrel.property_snd g),
    fun T => (hmem T).trans ?_⟩
  -- Compare the section at `T` with the section at the base of `y(T)`.
  let φ : y.obj T ⟶ x₀.1 := y.map (Functor.toMkId U T)
  rw [automorphismLocus_iff_mem B S hS P 𝒳 W hWmem x₀ φ]
  have hl : (Over.mk (p.map φ ≫ eqToHom x₀.2).left : BigFppfOver B U.left.1 U.left.2) = T := by
    have h := Functor.congr_hom hy (Functor.toMkId U T)
    simp only [Functor.comp_map] at h
    change Over.mk (p.map (y.map (Functor.toMkId U T)) ≫ eqToHom x₀.2).left = T
    rw [h, Functor.overMap_map_toMkId]
    have aux : ∀ {A : BigFppfOver B S hS} (e : A = (Over.map U.hom).obj T),
        (Over.mk (eqToHom e ≫ Functor.structHom U T).left : BigFppfOver B U.left.1 U.left.2) =
          T := by
      rintro A rfl
      simp only [eqToHom_refl, Category.id_comp]
      rfl
    simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
    exact aux _
  rw [hl]

end Locus

/-! ### The open substack of objects with a given automorphism property -/

section Substack

variable (P : MorphismProperty Scheme.{u}) (𝒳 : AlgebraicStacks.{u, w} B S hS)
  (W : ∀ (U : BigFppfOver B S hS) (_x : 𝒳.val.val.p.Fiber U),
    Subfunctor (siteTerminalSpace B S hS U))
  (hWmem : letI : 𝒳.val.val.p.IsFibered := 𝒳.val.isFiberedInGroupoids.isFibered
    ∀ (U : BigFppfOver B S hS) (x : 𝒳.val.val.p.Fiber U)
      (X : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ) (s : (siteTerminalSpace B S hS U).obj X),
      s ∈ (W U x).obj X ↔ Space.HoldsOnEveryEtaleChart B U.left.1 U.left.2 P
        (pullback.snd (isomSpaceOver B S hS 𝒳.val U x x).hom (yonedaEquiv.symm s)))
  (hWopen : ∀ (U : BigFppfOver B S hS) (x : 𝒳.val.val.p.Fiber U),
    Space.IsOpenSubspace B U.left.1 U.left.2 (W U x))

include hWmem hWopen in
/-- The full subcategory on the automorphism locus is an algebraic stack: its inclusion is
representable by algebraic spaces, by the openness of the locus, and the source of a 1-morphism
representable by algebraic spaces into an algebraic stack is one (**Stacks 05UM**). -/
theorem isAlgebraicStack_automorphismLocus :
    IsAlgebraicStack.{u, w} B S hS (fullSubcategoryBased 𝒳 (automorphismLocus B S hS P 𝒳)) :=
  isAlgebraicStack_source_of_isRepresentableByAlgebraicSpaces B S hS
    (𝒳 := CatFiberedInGroupoids.mk (fullSubcategoryBased 𝒳 (automorphismLocus B S hS P 𝒳))
      (isFiberedInGroupoids_fullSubcategoryBased 𝒳
        (fun φ hx => automorphismLocus_of_hom B S hS P 𝒳 W hWmem hx φ))) (𝒴 := 𝒳.val)
    (Bicategory.InducedBicategory.mkHom
      (fullSubcategoryBasedInclusion 𝒳 (automorphismLocus B S hS P 𝒳)))
    (isRepresentableByAlgebraicSpaces_of_openLocus B S hS (automorphismLocus B S hS P 𝒳)
      (fullSubcategoryBasedInclusion 𝒳 (automorphismLocus B S hS P 𝒳)) rfl
      (exists_isOpenImmersion_forall_nonempty_hom_iff_automorphismLocus B S hS P 𝒳 W hWmem
        hWopen))
    𝒳.property

/-- **The open substack of the objects with a given automorphism property.** Given, for every
object `x` over `U`, an open subspace of `U` whose sections are those over which the automorphism
group algebraic space of `x` has `P`, the objects whose automorphism group algebraic space has
`P` form an open substack. -/
noncomputable def automorphismLocusSubstack : OpenSubstack 𝒳 where
  property := automorphismLocus B S hS P 𝒳
  strictlyFull := inferInstance
  isAlgebraic := isAlgebraicStack_automorphismLocus B S hS P 𝒳 W hWmem hWopen
  isOpenImmersion :=
    ⟨isRepresentableByAlgebraicSpaces_of_openLocus B S hS (automorphismLocus B S hS P 𝒳)
      (fullSubcategoryBasedInclusion 𝒳 (automorphismLocus B S hS P 𝒳)) rfl
      (exists_isOpenImmersion_forall_nonempty_hom_iff_automorphismLocus B S hS P 𝒳 W hWmem
        hWopen),
    isOpenImmersion_of_openLocus B S hS (automorphismLocus B S hS P 𝒳)
      (fullSubcategoryBasedInclusion 𝒳 (automorphismLocus B S hS P 𝒳)) rfl
      (exists_isOpenImmersion_forall_nonempty_hom_iff_automorphismLocus B S hS P 𝒳 W hWmem
        hWopen)⟩

/-- The objects of an open substack have the automorphism property of `𝒳` exactly when, as
objects of the open substack, they have the automorphism property computed there. -/
theorem automorphismLocus_toAlgebraicStack_iff (V : OpenSubstack 𝒳)
    (x : V.toAlgebraicStack.val.val.obj) :
    automorphismLocus B S hS P V.toAlgebraicStack x ↔ automorphismLocus B S hS P 𝒳 x.obj :=
  (automorphismLocus_iff B S hS P V.toAlgebraicStack (Functor.Fiber.mk rfl)).trans
    ((holdsOnEveryEtaleChart_isomSpace_fullSubcategory_iff B S hS P 𝒳 V.property
      V.isAlgebraic _ (Functor.Fiber.mk rfl)).trans
      (automorphismLocus_iff B S hS P 𝒳 (Functor.Fiber.mk rfl)).symm)

end Substack

/-! ### Stacks 0DSN -/

/-- The structure morphism of the automorphism group algebraic space of an object is locally of
finite type. -/
private theorem isLocallyOfFiniteType_automorphismGroupSpace_hom
    (𝒳 : AlgebraicStacks.{u, w} B S hS) (U : BigFppfOver B S hS)
    (x : 𝒳.val.val.p.Fiber U) :
    Space.IsLocallyOfFiniteType B U.left.1 U.left.2
      (automorphismGroupSpace B S hS 𝒳.val 𝒳.property U x).obj.X.hom :=
  (holdsOnEveryEtaleChart_isomSpaceOver_hom_iff B S hS 𝒳 _ U x x).mpr
    (isLocallyOfFiniteType_isomPresheaf B S hS 𝒳.val 𝒳.property U x x)

/-- The unramified locus of the base of the automorphism group algebraic space of an object, as
an open subspace (**Stacks 0DSJ**), with its sections described. -/
theorem unramifiedLocus_spec (𝒳 : AlgebraicStacks.{u, w} B S hS) :
    letI : 𝒳.val.val.p.IsFibered := 𝒳.val.isFiberedInGroupoids.isFibered
    (∀ (U : BigFppfOver B S hS) (x : 𝒳.val.val.p.Fiber U)
      (X : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ) (s : (siteTerminalSpace B S hS U).obj X),
      s ∈ (Space.unramifiedBaseLocus B U.left.1 U.left.2
        (automorphismGroupSpace B S hS 𝒳.val 𝒳.property U x)).obj X ↔
        Space.IsUnramified B U.left.1 U.left.2
          (pullback.snd (isomSpaceOver B S hS 𝒳.val U x x).hom (yonedaEquiv.symm s))) ∧
    ∀ (U : BigFppfOver B S hS) (x : 𝒳.val.val.p.Fiber U),
      Space.IsOpenSubspace B U.left.1 U.left.2 (Space.unramifiedBaseLocus B U.left.1 U.left.2
        (automorphismGroupSpace B S hS 𝒳.val 𝒳.property U x)) :=
  ⟨fun U x _ s => Space.mem_unramifiedBaseLocus_iff B U.left.1 U.left.2 _
      (isLocallyOfFiniteType_automorphismGroupSpace_hom B S hS 𝒳 U x) s,
    fun U _x => Space.isOpenSubspace_unramifiedBaseLocus B U.left.1 U.left.2 _⟩

/-- The locally quasi-finite locus of the base of the automorphism group algebraic space of an
object, as an open subspace (**Stacks 0DSJ**), with its sections described. -/
theorem locallyQuasiFiniteLocus_spec (𝒳 : AlgebraicStacks.{u, w} B S hS) :
    letI : 𝒳.val.val.p.IsFibered := 𝒳.val.isFiberedInGroupoids.isFibered
    (∀ (U : BigFppfOver B S hS) (x : 𝒳.val.val.p.Fiber U)
      (X : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ) (s : (siteTerminalSpace B S hS U).obj X),
      s ∈ (Space.locallyQuasiFiniteBaseLocus B U.left.1 U.left.2
        (automorphismGroupSpace B S hS 𝒳.val 𝒳.property U x)).obj X ↔
        Space.IsLocallyQuasiFinite B U.left.1 U.left.2
          (pullback.snd (isomSpaceOver B S hS 𝒳.val U x x).hom (yonedaEquiv.symm s))) ∧
    ∀ (U : BigFppfOver B S hS) (x : 𝒳.val.val.p.Fiber U),
      Space.IsOpenSubspace B U.left.1 U.left.2 (Space.locallyQuasiFiniteBaseLocus B U.left.1
        U.left.2 (automorphismGroupSpace B S hS 𝒳.val 𝒳.property U x)) :=
  ⟨fun U x _ s => Space.mem_locallyQuasiFiniteBaseLocus_iff B U.left.1 U.left.2 _
      (isLocallyOfFiniteType_automorphismGroupSpace_hom B S hS 𝒳 U x) s,
    fun U x => Space.isOpenSubspace_locallyQuasiFiniteBaseLocus B U.left.1 U.left.2 _
      (isLocallyOfFiniteType_automorphismGroupSpace_hom B S hS 𝒳 U x)⟩

variable (hZ : B.Contains (⊤_ Scheme.{u})) (𝒳 : AlgebraicStacks.{u, w} B S hS)

/-- A field-valued point lies in the automorphism locus for `P` exactly when its automorphism
group algebraic space has `P` over the field. -/
theorem automorphismLocus_obj_iff (P : MorphismProperty Scheme.{u})
    (x : FieldValuedPoint B S hS 𝒳.val.val) :
    automorphismLocus B S hS P 𝒳 x.obj ↔ Space.HoldsOnEveryEtaleChart B x.base.left.1
      x.base.left.2 P
      (automorphismGroupSpace B S hS 𝒳.val 𝒳.property x.base ⟨x.obj, x.over⟩).obj.X.hom :=
  (automorphismLocus_iff B S hS P 𝒳 ⟨x.obj, x.over⟩).trans
    (holdsOnEveryEtaleChart_isomSpaceOver_hom_iff B S hS 𝒳 P x.base _ _).symm

/-- All automorphism group algebraic spaces over objects of the site have `P` on étale charts
exactly when all objects lie in the automorphism locus for `P`. -/
private theorem forall_holdsOnEveryEtaleChart_isomSpaceOver_hom_iff_forall_automorphismLocus
    (P : MorphismProperty Scheme.{u}) :
    letI : 𝒳.val.val.p.IsFibered := 𝒳.val.isFiberedInGroupoids.isFibered
    (∀ (U : BigFppfOver B S hS) (x : 𝒳.val.val.p.Fiber U),
      Space.HoldsOnEveryEtaleChart B U.left.1 U.left.2 P (isomSpaceOver B S hS 𝒳.val U x x).hom) ↔
      ∀ x, automorphismLocus B S hS P 𝒳 x :=
  ⟨fun h _ => (automorphismLocus_iff B S hS _ 𝒳 (Functor.Fiber.mk rfl)).mpr
      ((holdsOnEveryEtaleChart_isomSpaceOver_hom_iff B S hS 𝒳 _ _ _ _).mp (h _ _)),
    fun h _ x => (holdsOnEveryEtaleChart_isomSpaceOver_hom_iff B S hS 𝒳 _ _ _ _).mpr
      ((automorphismLocus_iff B S hS _ 𝒳 x).mp (h x.1))⟩

/-- An algebraic stack is Deligne–Mumford exactly when all its objects lie in its unramified
automorphism locus. -/
theorem isAbsolutelyDM_iff_forall_automorphismLocus :
    AlgebraicStacks.IsAbsolutelyDM B S hS hZ 𝒳 ↔
      ∀ x, automorphismLocus B S hS (@_root_.AlgebraicGeometry.Unramified) 𝒳 x := by
  rw [AlgebraicStacks.isAbsolutelyDM_iff_isDMOver, isDMOver_iff_forall_isUnramified_isomSpaceOver]
  exact forall_holdsOnEveryEtaleChart_isomSpaceOver_hom_iff_forall_automorphismLocus B S hS 𝒳 _

/-- An algebraic stack is quasi-Deligne–Mumford exactly when all its objects lie in its locally
quasi-finite automorphism locus. -/
theorem isAbsolutelyQuasiDM_iff_forall_automorphismLocus :
    AlgebraicStacks.IsAbsolutelyQuasiDM B S hS hZ 𝒳 ↔
      ∀ x, automorphismLocus B S hS
        ((@_root_.AlgebraicGeometry.LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u}) ⊓
          (@_root_.AlgebraicGeometry.LocallyQuasiFinite.{u} : MorphismProperty Scheme.{u}))
        𝒳 x := by
  rw [AlgebraicStacks.isAbsolutelyQuasiDM_iff_isQuasiDMOver,
    isQuasiDMOver_iff_forall_isLocallyQuasiFinite_isomSpaceOver]
  exact forall_holdsOnEveryEtaleChart_isomSpaceOver_hom_iff_forall_automorphismLocus B S hS 𝒳 _

/-- An object lies in an open substack satisfying a property `Q` exactly when it lies in the
automorphism locus, when `Q` means that all objects lie in the automorphism locus for `P`. -/
private theorem exists_openSubstack_iff_automorphismLocus (P : MorphismProperty Scheme.{u})
    (𝒳 : AlgebraicStacks.{u, w} B S hS) (Q : AlgebraicStacks.{u, w} B S hS → Prop)
    (hQ : ∀ 𝒴, Q 𝒴 ↔ ∀ y, automorphismLocus B S hS P 𝒴 y)
    (W : ∀ (U : BigFppfOver B S hS) (_x : 𝒳.val.val.p.Fiber U),
      Subfunctor (siteTerminalSpace B S hS U))
    (hWmem : letI : 𝒳.val.val.p.IsFibered := 𝒳.val.isFiberedInGroupoids.isFibered
      ∀ (U : BigFppfOver B S hS) (x : 𝒳.val.val.p.Fiber U)
        (X : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ) (s : (siteTerminalSpace B S hS U).obj X),
        s ∈ (W U x).obj X ↔ Space.HoldsOnEveryEtaleChart B U.left.1 U.left.2 P
          (pullback.snd (isomSpaceOver B S hS 𝒳.val U x x).hom (yonedaEquiv.symm s)))
    (hWopen : ∀ (U : BigFppfOver B S hS) (x : 𝒳.val.val.p.Fiber U),
      Space.IsOpenSubspace B U.left.1 U.left.2 (W U x))
    (X : 𝒳.val.val.obj) :
    (∃ V : OpenSubstack 𝒳, Q V.toAlgebraicStack ∧ V.property X) ↔
      automorphismLocus B S hS P 𝒳 X := by
  constructor
  · rintro ⟨V, hV, hxV⟩
    exact (automorphismLocus_toAlgebraicStack_iff B S hS _ 𝒳 V ⟨X, hxV⟩).mp ((hQ _).mp hV _)
  · intro hx
    let V := automorphismLocusSubstack B S hS P 𝒳 W hWmem hWopen
    exact ⟨V, (hQ _).mpr fun y => (automorphismLocus_toAlgebraicStack_iff B S hS _ 𝒳 V y).mpr
      y.property, hx⟩

/-- **Stacks 0DSN, part (1).** A field-valued point of an algebraic stack lies in its
Deligne–Mumford locus exactly when its automorphism group algebraic space is unramified over
its field.

The objects of `𝒳` whose automorphism group algebraic space is unramified form an open substack,
`AlgebraicGeometry.Stack.automorphismLocusSubstack`, open because the unramified base locus of
**Stacks 0DSJ** is, and Deligne–Mumford by the pseudo-torsor argument of **Stacks 0CL0** through
**Stacks 0DSK**; conversely an open substack is Deligne–Mumford only if the automorphism group
algebraic spaces of its objects, which are those computed in `𝒳`, are unramified. -/
@[stacks 0DSN "part (1)"]
theorem dmLocus_apply_iff_isUnramifiedAutomorphismGroupSpace
    (x : FieldValuedPoint B S hS 𝒳.val.val) :
    dmLocus B S hS hZ 𝒳 x.obj ↔ IsUnramifiedAutomorphismGroupSpace B S hS 𝒳 x := by
  exact (dmLocus_apply_iff B S hS hZ 𝒳 x.obj).trans
    ((exists_openSubstack_iff_automorphismLocus B S hS _ 𝒳 _
      (isAbsolutelyDM_iff_forall_automorphismLocus B S hS hZ) _
      (unramifiedLocus_spec B S hS 𝒳).1 (unramifiedLocus_spec B S hS 𝒳).2 x.obj).trans
      (automorphismLocus_obj_iff B S hS 𝒳 (@_root_.AlgebraicGeometry.Unramified) x))

/-- **Stacks 0DSN, part (2).** A field-valued point of an algebraic stack lies in its
quasi-Deligne–Mumford locus exactly when its automorphism group algebraic space is locally
quasi-finite over its field. The source says the proof is the same as for part (1), and it
is. -/
@[stacks 0DSN "part (2)"]
theorem quasiDMLocus_apply_iff_isLocallyQuasiFiniteAutomorphismGroupSpace
    (x : FieldValuedPoint B S hS 𝒳.val.val) :
    quasiDMLocus B S hS hZ 𝒳 x.obj ↔
      IsLocallyQuasiFiniteAutomorphismGroupSpace B S hS 𝒳 x := by
  exact (quasiDMLocus_apply_iff B S hS hZ 𝒳 x.obj).trans
    ((exists_openSubstack_iff_automorphismLocus B S hS _ 𝒳 _
      (isAbsolutelyQuasiDM_iff_forall_automorphismLocus B S hS hZ) _
      (locallyQuasiFiniteLocus_spec B S hS 𝒳).1 (locallyQuasiFiniteLocus_spec B S hS 𝒳).2
      x.obj).trans
      (automorphismLocus_obj_iff B S hS 𝒳
        ((@_root_.AlgebraicGeometry.LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u}) ⊓
          (@_root_.AlgebraicGeometry.LocallyQuasiFinite.{u} : MorphismProperty Scheme.{u})) x))

end AlgebraicGeometry.Stack

end
