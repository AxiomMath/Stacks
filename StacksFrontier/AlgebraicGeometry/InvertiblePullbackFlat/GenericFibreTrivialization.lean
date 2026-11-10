module

public import StacksFrontier.AlgebraicGeometry.NonvanishingTrivialization.Basic
public import StacksFrontier.AlgebraicGeometry.InvertiblePullbackFlat.MeromorphicFromGenericStalk
public import StacksFrontier.AlgebraicGeometry.InvertiblePullbackFlat.GenericFibreModuleStalk
public import StacksFrontier.Topology.Sheaves.Modules.Invertible

/-!
# The first paragraph of Stacks Tag 0BD7

Let `φ : X ⟶ Y` be a morphism of schemes with `Y` integral, and let `ℒ` be a sheaf of
`𝒪_X`-modules whose restriction to the generic fibre `X_ξ` is trivial. The first paragraph of
Stacks Tag 0BD7 chooses a trivializing section `s ∈ Γ(X_ξ, ℒ_ξ)` and then says: "Observe that
`X` is integral by Lemma 0BCM. Hence we can think of `s` as a regular meromorphic section of
`ℒ`." This file carries out that passage.

## Main results

* `Stacks.SheafOfModules.bijective_stalkMapL_of_isIso`: an isomorphism of sheaves of modules is
  bijective on every stalk.
* `Stacks.SheafOfModules.span_eq_top_grpGerm_of_isIso_unitHomEquiv_symm`: if multiplication by a
  global section `s` is an isomorphism `𝒪 ⟶ ℒ`, then the germ of `s` generates the stalk of `ℒ`
  at *every* point. No hypothesis on the stalks is needed.
* `Stacks.SheafOfModules.exists_sections_forall_span_eq_top_grpGerm_of_isTrivial`: a trivial
  sheaf of modules has **one** global section whose germ generates the stalk at every point.
* `AlgebraicGeometry.exists_sections_forall_span_eq_top_grpGerm_genericFiber`: that section, for
  `ℒ` restricted to the generic fibre, which is what assumption (5) of Tag 0BD7 supplies.
* `AlgebraicGeometry.forall_span_eq_top_grpStalk_of_isTrivial_genericFiber`: that one section
  generates the stalk of `ℒ` at the image of **every** point of the generic fibre, the generator
  at each being a *named* element — the image of the germ of the section under
  `AlgebraicGeometry.stalkPullbackFiberιAddEquiv`.
* `AlgebraicGeometry.exists_span_eq_top_stalk_genericPoint_of_isTrivial_genericFiber`: its
  existential form at the generic point of `X`.
* `AlgebraicGeometry.exists_meromorphicSection_span_eq_top_of_isTrivial_genericFiber`: the
  paragraph's conclusion — a meromorphic section of `ℒ` generating at the generic point.

## Implementation notes

**Which of these statements carries the strength of assumption (5), and which does not.** The
last two are existential in the generating element, and in that form they are *also* consequences
of invertibility of `ℒ` alone: the stalk of an invertible module at any point is free of rank
one, so a generator exists with no hypothesis about any fibre. So they are the paragraph's
*conclusion* but not its content.

The content is `exists_sections_forall_span_eq_top_grpGerm_of_isTrivial`, where **one** section
generates at **every** point of the generic fibre simultaneously. That is what a global
trivialization on `X_ξ` gives and what pointwise invertibility does not, and it is the form the
later paragraphs of Tag 0BD7 consume when they ask for `s` to be a unit in `A ⊗_R K` at every
chart. The existential forms are recorded because they are what names the meromorphic section;
the quantifier order is where assumption (5) lives.

**And the quantifier order survives the passage to `X` only if the generator is named.**
`forall_span_eq_top_grpStalk_of_isTrivial_genericFiber` is that passage: it keeps the `∀` by
keeping the generator a function of the section and the point, through
`AlgebraicGeometry.stalkPullbackFiberιAddEquiv`. An existential statement applied at two points
of the generic fibre produces two unrelated witnesses, which no later paragraph can use — what
they ask of `s` is that *its own* germ be a unit.

The route to the germ generating is `Stacks.SheafOfModules.stalkMapL_unitHomEquiv_symm_comp`,
which identifies multiplication by the germ of `s` with the stalk map of multiplication by `s`
precomposed with `unitStalkLinearEquiv`. Bijectivity of a stalk map of an isomorphism is not
stated anywhere, so it is proved here: `Stacks.SheafOfModules.TensorStalkRingedSpace.stalkMap` is
  *by definition* a
`TopCat.Presheaf.stalkFunctor` map, so a functor preserves the isomorphism and
`ConcreteCategory` turns it into a bijection.

## References

* [Stacks Project, Tag 0BD7](https://stacks.math.columbia.edu/tag/0BD7)
* [Stacks Project, Tag 01CS](https://stacks.math.columbia.edu/tag/01CS)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open Stacks.SheafOfModules.TensorStalkRingedSpace Stacks.RingedSpace

universe u

namespace Stacks.SheafOfModules

variable {X : AlgebraicGeometry.RingedSpace.{u, u}}
  {M N : SheafOfModules.{u} (structureSheafRing X)}

/-- **An isomorphism of sheaves of modules is bijective on every stalk.**
`Stacks.SheafOfModules.TensorStalkRingedSpace.stalkMap` is defined as a
  `TopCat.Presheaf.stalkFunctor` map, so this is a functor
preserving an isomorphism. -/
theorem bijective_stalkMapL_of_isIso (φ : M ⟶ N) [IsIso φ] (x : X.carrier) :
    Function.Bijective (stalkMapL X M.val N.val φ.val x) := by
  have hval : IsIso φ.val := by
    change IsIso ((SheafOfModules.forget (structureSheafRing X)).map φ)
    infer_instance
  have hstalk : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      ((PresheafOfModules.toPresheaf (O X)).map φ.val)) := inferInstance
  exact (ConcreteCategory.isIso_iff_bijective _).mp hstalk

/-- **A section whose multiplication map is an isomorphism generates every stalk.** If
multiplication by a global section `s` of `L` is an isomorphism `𝒪_X ⟶ L`, then the germ of `s`
at any point generates the stalk of `L` there.

Multiplication by the germ is the stalk map of multiplication by `s`, read through
`unitStalkLinearEquiv` — that is `Stacks.SheafOfModules.stalkMapL_unitHomEquiv_symm_comp` — and
both of those are bijective, so multiplication by the germ is surjective. Note that no local-ring
hypothesis on the stalks appears: this is generation, not a Nakayama argument. -/
theorem span_eq_top_grpGerm_of_isIso_unitHomEquiv_symm
    (L : SheafOfModules.{u} (structureSheafRing X)) (s : L.sections)
    (hs : IsIso (L.unitHomEquiv.symm s)) (x : X.carrier) :
    Submodule.span (ringStalk X x)
      {grpGerm X L.val x ⊤ (Opens.mem_top x) (s.eval (op ⊤))} = ⊤ := by
  have hcomp := stalkMapL_unitHomEquiv_symm_comp s x
  have hb : Function.Bijective ((stalkMapL X (SheafOfModules.unit (structureSheafRing X)).val
      L.val (L.unitHomEquiv.symm s).val x) ∘ (unitStalkLinearEquiv X x)) :=
    (bijective_stalkMapL_of_isIso (L.unitHomEquiv.symm s) x).comp
      (unitStalkLinearEquiv X x).bijective
  rw [hcomp] at hb
  refine Submodule.eq_top_iff'.2 fun w => ?_
  obtain ⟨c, hc⟩ := hb.2 w
  exact Submodule.mem_span_singleton.2 ⟨c, hc⟩

/-- **A trivial sheaf of modules has one global section generating every stalk.** This is the
quantifier order that a global trivialization supplies and that pointwise invertibility does
not: the same `s` works at every point. -/
theorem exists_sections_forall_span_eq_top_grpGerm_of_isTrivial
    (L : SheafOfModules.{u} (structureSheafRing X))
    (h : Nonempty (L ≅ SheafOfModules.unit (structureSheafRing X))) :
    ∃ s : L.sections, ∀ x : X.carrier,
      Submodule.span (ringStalk X x)
        {grpGerm X L.val x ⊤ (Opens.mem_top x) (s.eval (op ⊤))} = ⊤ := by
  obtain ⟨e⟩ := h
  refine ⟨L.unitHomEquiv e.inv, fun x => ?_⟩
  refine span_eq_top_grpGerm_of_isIso_unitHomEquiv_symm L _ ?_ x
  rw [Equiv.symm_apply_apply]
  infer_instance

end Stacks.SheafOfModules

namespace AlgebraicGeometry

/-- **Assumption (5) of Stacks Tag 0BD7, cashed in.** Triviality of `ℒ` on the generic fibre
gives one global section of `ℒ_ξ` whose germ generates the stalk at every point of the generic
fibre. -/
theorem exists_sections_forall_span_eq_top_grpGerm_genericFiber {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsIntegral Y] (L : SheafOfModules.{u} (structureRingSheaf X.toRingedSpace))
    (hgen : AlgebraicGeometry.SheafOfModules.IsTrivial
      (f.fiber (genericPoint Y)).presheaf
      (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat)
        (f.fiber (genericPoint Y)).IsSheaf)
      ((Scheme.Modules.pullback (f.fiberι (genericPoint Y))).obj L)) :
    ∃ s : ((Stacks.RingedSpace.pullbackFunctor
        (f.fiberι (genericPoint Y)).toLRSHom.toShHom).obj L).sections,
      ∀ x₀ : f.fiber (genericPoint Y),
        Submodule.span (ringStalk (f.fiber (genericPoint Y)).toRingedSpace x₀)
          {grpGerm (f.fiber (genericPoint Y)).toRingedSpace
            ((Stacks.RingedSpace.pullbackFunctor
              (f.fiberι (genericPoint Y)).toLRSHom.toShHom).obj L).val x₀ ⊤
            (Opens.mem_top x₀) (s.eval (op ⊤))} = ⊤ :=
  Stacks.SheafOfModules.exists_sections_forall_span_eq_top_grpGerm_of_isTrivial _ hgen

/-- **Assumption (5) of Stacks Tag 0BD7 at every point of `X` lying on the generic fibre, with
the generator named.** There is *one* section `s` of `ℒ_ξ` such that, at *every* point `x₀` of
the generic fibre, a named element of the stalk of `ℒ` at the image of `x₀` — the image of the
germ of `s` under `AlgebraicGeometry.stalkPullbackFiberιAddEquiv` — generates that stalk.

This is the form the later paragraphs of Stacks Tag 0BD7 consume, and it is not what
`AlgebraicGeometry.exists_span_eq_top_stalk_genericPoint_of_isTrivial_genericFiber` below
provides. That statement is existential in the generator, so applying it at two points of the
generic fibre yields two unrelated witnesses; the source needs the germ of a *single* section to
generate at all of them at once, because the ring-theoretic input of the penultimate paragraph
asks for the germ of that one section to be a unit. Carrying a *named* generator across is what
`AlgebraicGeometry.span_eq_top_grpStalk_stalkPullbackFiberιAddEquiv` adds, and
`AlgebraicGeometry.span_eq_top_grpGerm_of_span_eq_top_grpGerm_pullbackUnit` is the case in which
the named generator is visibly the germ of a section of `ℒ`. -/
theorem forall_span_eq_top_grpStalk_of_isTrivial_genericFiber {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsIntegral Y] (L : SheafOfModules.{u} (structureRingSheaf X.toRingedSpace))
    (hgen : AlgebraicGeometry.SheafOfModules.IsTrivial
      (f.fiber (genericPoint Y)).presheaf
      (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat)
        (f.fiber (genericPoint Y)).IsSheaf)
      ((Scheme.Modules.pullback (f.fiberι (genericPoint Y))).obj L)) :
    ∃ s : ((Stacks.RingedSpace.pullbackFunctor
        (f.fiberι (genericPoint Y)).toLRSHom.toShHom).obj L).sections,
      ∀ x₀ : f.fiber (genericPoint Y),
        Submodule.span (ringStalk X.toRingedSpace
            (((f.fiberι (genericPoint Y)).toLRSHom.toShHom).hom.base x₀))
          {stalkPullbackFiberιAddEquiv f (maximalIdeal_stalk_genericPoint_eq_bot Y) L x₀
            (grpGerm (f.fiber (genericPoint Y)).toRingedSpace
              ((Stacks.RingedSpace.pullbackFunctor
                (f.fiberι (genericPoint Y)).toLRSHom.toShHom).obj L).val x₀ ⊤
              (Opens.mem_top x₀) (s.eval (op ⊤)))} = ⊤ := by
  obtain ⟨s, hs⟩ := exists_sections_forall_span_eq_top_grpGerm_genericFiber f L hgen
  exact ⟨s, fun x₀ => span_eq_top_grpStalk_stalkPullbackFiberιAddEquiv f _ L x₀ _ (hs x₀)⟩

/-- **The stalk of `ℒ` at the generic point of `X` is generated by the trivializing section of
the generic fibre.** The generic point of `X` lies in the generic fibre
(`AlgebraicGeometry.genericPoint_mem_range_fiberι_genericPoint`), and the generator is carried
there by `AlgebraicGeometry.forall_span_eq_top_grpStalk_of_isTrivial_genericFiber`, of which this
is the existential form at that one point. -/
theorem exists_span_eq_top_stalk_genericPoint_of_isTrivial_genericFiber {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsIntegral Y] [IrreducibleSpace X] (hsurj : Function.Surjective f.base)
    (L : SheafOfModules.{u} (structureRingSheaf X.toRingedSpace))
    (hgen : AlgebraicGeometry.SheafOfModules.IsTrivial
      (f.fiber (genericPoint Y)).presheaf
      (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat)
        (f.fiber (genericPoint Y)).IsSheaf)
      ((Scheme.Modules.pullback (f.fiberι (genericPoint Y))).obj L)) :
    ∃ m : grpStalk X.toRingedSpace L.val (genericPoint X),
      Submodule.span (ringStalk X.toRingedSpace (genericPoint X)) {m} = ⊤ := by
  obtain ⟨s, hs⟩ := forall_span_eq_top_grpStalk_of_isTrivial_genericFiber f L hgen
  obtain ⟨x₀, hx₀⟩ := genericPoint_mem_range_fiberι_genericPoint f hsurj
  rw [← hx₀]
  exact ⟨_, hs x₀⟩

/-- **The conclusion of the first paragraph of Stacks Tag 0BD7.** Under its assumptions there is
a meromorphic section of `ℒ` whose value at the generic point generates the stalk of `ℒ` there —
the source's "hence we can think of `s` as a regular meromorphic section of `ℒ`".

The section is named: it is `AlgebraicGeometry.meromorphicSectionOfGenericStalk X L m`, and by
`AlgebraicGeometry.exists_unique_eq_meromorphicSectionOfGenericStalk` it is the only meromorphic
section built from `m`. -/
theorem exists_meromorphicSection_span_eq_top_of_isTrivial_genericFiber {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsIntegral Y] [IsIntegral X] (hsurj : Function.Surjective f.base)
    (L : X.Modules) [L.IsQuasicoherent]
    (hgen : AlgebraicGeometry.SheafOfModules.IsTrivial
      (f.fiber (genericPoint Y)).presheaf
      (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat)
        (f.fiber (genericPoint Y)).IsSheaf)
      ((Scheme.Modules.pullback (f.fiberι (genericPoint Y))).obj L)) :
    letI : Module (ringStalk X.toRingedSpace (genericPoint X))
        (grpStalk X.toRingedSpace L.val (genericPoint X)) :=
      stalkModuleStructureRingSheaf (X := X.toRingedSpace) L (genericPoint X)
    ∃ (m : grpStalk X.toRingedSpace L.val (genericPoint X)) (s : MeromorphicSection X.sheaf L),
      Submodule.span (ringStalk X.toRingedSpace (genericPoint X)) {m} = ⊤ ∧
        s = meromorphicSectionOfGenericStalk X L m := by
  obtain ⟨m, hm⟩ :=
    exists_span_eq_top_stalk_genericPoint_of_isTrivial_genericFiber f hsurj L hgen
  exact ⟨m, meromorphicSectionOfGenericStalk X L m, hm, rfl⟩

end AlgebraicGeometry

end
