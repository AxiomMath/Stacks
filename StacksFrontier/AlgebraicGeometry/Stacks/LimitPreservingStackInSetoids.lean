module

public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation.LimitPreservingFunctorOfPoints
public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingEquivalence
public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingObjectsFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingSetoidRepresentable
public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingStructureMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.PresheafArtinAxioms
public import StacksFrontier.AlgebraicGeometry.Stacks.PresheafFibredCategory
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableStackInSetoids
public import StacksFrontier.AlgebraicGeometry.Stacks.StackInSetoidsRepresentableBySpace

/-!
# Limit preservation and representability by an algebraic space of finite presentation

Let `𝒳` be an algebraic stack over the big fppf site of a scheme `S`. Stacks 07XN says that the
following three conditions on `𝒳` are equivalent: (1) `𝒳` is a stack in setoids and its structure
morphism `𝒳 ⟶ (Sch/S)_{fppf}` is limit preserving on objects in the sense of Stacks 06CU; (2) `𝒳`
is a stack in setoids and is limit preserving in the sense of Stacks 07XL, that is the comparison
`colim 𝒳_{Tᵢ} ⥤ 𝒳_T` is an equivalence for every cofiltered inverse system of affine schemes with
limit `T`; (3) `𝒳` is representable by an algebraic space over `S` which is locally of finite
presentation over `S`. This file proves that equivalence, the implication (2) ⟹ (1) being
`AlgebraicGeometry.Stack.isStackInSetoids_and_isLimitPreservingOnObjects_of_isLimitPreserving`.

Condition (3) is `AlgebraicGeometry.Stack.IsRepresentableBySpaceLocallyOfFinitePresentation`:
representability by an algebraic space together with local finite presentation, in the relative
sense of Stacks 03YK, of the structure morphism `𝒳 ⟶ (Sch/S)_{fppf}`.

The target `(Sch/S)_{fppf}` is `AlgebraicGeometry.Stack.terminalCFG`, the big fppf site of `S`
with the identity as structure functor, and the structure morphism is
`AlgebraicGeometry.Stack.toTerminalCFG` viewed as a 1-morphism of the 2-category of categories
fibred in groupoids.

## Main results

* The implication (1) ⟹ (3): an algebraic stack which is a stack in setoids and whose structure
  morphism is limit preserving on objects satisfies
  `AlgebraicGeometry.Stack.IsRepresentableBySpaceLocallyOfFinitePresentation`.
* `AlgebraicGeometry.Stack`'s
  `isStackInSetoids_and_isLimitPreserving_of_isRepresentableBySpaceLocallyOfFinitePresentation`:
  the implication (3) ⟹ (2).
* `AlgebraicGeometry.Stack.isStackInSetoids_isLimitPreserving_tfae`: **Stacks 07XN**, the
  three-way equivalence.

## Implementation notes

*The shape of the proof.* The three implications proved are the cycle (1) ⟹ (3) ⟹ (2) ⟹ (1).
The implication (1) ⟹ (3) is Algebraic Stacks, Proposition 04SZ, for representability, followed
by Stacks 06CX at the structure morphism for its local finite presentation. The implication
(3) ⟹ (2) first passes through the implication (3) ⟹ (1) of
`StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingSetoidRepresentable`, and then follows the
source: limit preservation on objects makes the representing algebraic space `F` locally of
finite presentation over `S` by Stacks 0CM6, where surjectivity of the comparison maps already
suffices, and the bijectivity half of Limits of Spaces, Remark 05N0,
`AlgebraicGeometry.Space.isLocallyOfFinitePresentation_terminal_iff_limitPreserving`, makes the
functor of points of `F` limit preserving. That result is unconditional: it does not go through
the converse of Stacks 04AK, which this repository does not have. The implication (2) ⟹ (1)
needs no input at all, an equivalence of categories being in particular essentially surjective,
and in particular needs neither algebraicity nor the stack condition.

*The bootstrap input.* The implication (1) ⟹ (3) of Stacks 04SZ,
`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpace_of_isStackInSetoids`, rests on
condition (3) of Stacks 04S6, the result of the Bootstrap chapter that a sheaf receiving a
morphism from an algebraic space which is representable by algebraic spaces, surjective, flat and
locally of finite presentation is an algebraic space; that theorem proves it, so it takes no
bootstrap hypothesis. The implication (3) ⟹ (2) does not need it at all: representability is a
hypothesis there, and Stacks 04SZ enters only through its implication (3) ⟹ (1).

*Bridging the fibred category and its representing presheaf.* The fibres of the category attached
to a set-valued presheaf are discrete, so a morphism of it lying over a prescribed morphism of
the site is unique and a vertical morphism is an equality of sections. Under that dictionary the
three descent conditions of
`StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingStageDescent`, which characterise the
comparison of Stacks 07XL at a fixed cone, become: `Deformation.Artin.DescentObj` is
surjectivity of `colim F(Tᵢ) → F(T)`, `Deformation.Artin.DescentHom` is its injectivity, and
`Deformation.Artin.DescentEq` is vacuous. That is why limit preservation of the presheaf gives
limit preservation of the attached category,
`AlgebraicGeometry.Stack.isLimitPreserving_fibredCategory`, and why limit preservation on objects
of the structure morphism gives just the surjectivity that Stacks 0CM6 asks for. Both conditions
are transported between `𝒳` and the attached category by the invariance results of
`StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingEquivalence`, applied to the equivalence
over the site that representability provides.

*Descent of objects from the datum of Stacks 06CU.* The structure functor of `(Sch/S)_{fppf}` is
an identity, so the cartesian comparison in the target that Stacks 06CU asks for may be taken to
be a cone projection, and the vertical isomorphism it returns composes with the cartesian arrow
to the stage. This is the converse of the construction in
`AlgebraicGeometry.Stack.isLimitPreservingOnObjects_toTerminalCFG_of_isLimitPreserving`.

*Index universes.* The implication (2) ⟹ (1) holds at free index universes, and is stated that
way. The equivalence is stated at index categories in the universe `u` of the schemes, which is
the size at which its other inputs are available: Stacks 0CM6
(`AlgebraicGeometry.Space.isLocallyOfFinitePresentation_of_affineLimit_surjective`), Stacks 06CX
(`AlgebraicGeometry.Stack.isLimitPreservingOnObjects_iff_isLocallyOfFinitePresentation`) and the
proved half of Stacks 04AK
(`AlgebraicGeometry.relativelyLimitPreserving_of_isLocallyOfFinitePresentation`) all quantify
over cofiltered index categories there, and they pull in opposite directions for an equivalence,
so neither direction can be moved to a free index universe while the inputs stay where they are.
This is also the size the source's own formulation asks for, an inverse system directed by a set
of schemes of universe `u` being indexed in `Type u`. The object and morphism universes of `𝒳`
are pinned to those of the big fppf site, as they are for
`AlgebraicGeometry.Stack.IsAlgebraicStack`, because Stacks 06CU compares a 1-morphism's source
and target at a single pair of universes and the target here is the site itself.

## References

* [Stacks Project, Tag 07XN](https://stacks.math.columbia.edu/tag/07XN)
* [Stacks Project, Tag 07XL](https://stacks.math.columbia.edu/tag/07XL)
* [Stacks Project, Tag 049J](https://stacks.math.columbia.edu/tag/049J)
* [Stacks Project, Tag 06CU](https://stacks.math.columbia.edu/tag/06CU)
* [Stacks Project, Tag 03XP](https://stacks.math.columbia.edu/tag/03XP)
* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
* [Stacks Project, Tag 04S6](https://stacks.math.columbia.edu/tag/04S6)
* [Stacks Project, Tag 04SV](https://stacks.math.columbia.edu/tag/04SV)
* [Stacks Project, Tag 04SZ](https://stacks.math.columbia.edu/tag/04SZ)
* [Stacks Project, Tag 05N0](https://stacks.math.columbia.edu/tag/05N0)
* [Stacks Project, Tag 06CX](https://stacks.math.columbia.edu/tag/06CX)
* [Stacks Project, Tag 0CM6](https://stacks.math.columbia.edu/tag/0CM6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Stack

universe u v w t

attribute [local implicit_reducible] Functor.Fiber Functor.Fiber.fiberInclusion

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))

/-- **Limit preservation on objects of the structure morphism gives descent of objects.** If the
structure morphism `𝒳 ⟶ (Sch/S)_{fppf}` is limit preserving on objects in the sense of
Stacks 06CU, then every object of `𝒳` over the vertex of a cofiltered cone of affine objects
whose image in schemes is a limit admits a morphism to an object at a finite stage lying over
the corresponding cone projection.

This is the converse of the datum built in
`AlgebraicGeometry.Stack.isLimitPreservingOnObjects_toTerminalCFG_of_isLimitPreserving`: the
cartesian comparison in the target that Stacks 06CU asks for may be taken to be the cone
projection itself, because the structure functor of `(Sch/S)_{fppf}` is an identity, and the
vertical isomorphism Stacks 06CU returns composes with the cartesian arrow to the stage. -/
private theorem descentObj_of_isLimitPreservingOnObjects
    (h : BigFppfOver.IsLimitPreservingOnObjects.{u, v, w, u, u + 1} B S hS 𝒳
      (terminalCFG B S hS) (Bicategory.InducedBicategory.mkHom (toTerminalCFG B S hS 𝒳)))
    {I : Type v} [Category.{w} I] [IsCofiltered I] (D : I ⥤ BigAffineFppf B S hS)
    (c : Cone D) (hc : IsLimit ((BigAffineFppf.toScheme B S hS).mapCone c)) :
    Deformation.Artin.DescentObj 𝒳.val.p (D ⋙ BigAffineFppf.inclusion B S hS)
      ((BigAffineFppf.inclusion B S hS).mapCone c) := by
  have hfib : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
  intro x
  obtain ⟨i⟩ := IsCofiltered.nonempty (C := I)
  have hγ : (𝟭 (BigFppfOver B S hS)).IsStronglyCartesian
      ((BigAffineFppf.inclusion B S hS).map (c.π.app i)) (eqToHom x.2 ≫
        (BigAffineFppf.inclusion B S hS).map (c.π.app i)) :=
    have : (𝟭 (BigFppfOver B S hS)).IsHomLift
        ((BigAffineFppf.inclusion B S hS).map (c.π.app i)) (eqToHom x.2 ≫
          (BigAffineFppf.inclusion B S hS).map (c.π.app i)) :=
      IsHomLift.of_fac' (𝟭 (BigFppfOver B S hS)) _ _ x.2 rfl rfl
    Functor.isFiberedInGroupoids_id.isStronglyCartesian_homLift _ _
  obtain ⟨i', j, x', xU, δ, β, γ', hδ, hβ, hβiso, hγ'', hcomm⟩ :=
    h I D c hc i ⟨(BigAffineFppf.inclusion B S hS).obj (D.obj i), rfl⟩ x _ hγ
  have hiso : IsIso β := hβiso
  have hinv : 𝒳.val.p.IsHomLift
      (𝟙 ((BigAffineFppf.inclusion B S hS).obj c.pt)) (inv β) :=
    IsHomLift.lift_id_inv_isIso 𝒳.val.p _ β
  have hδ' : 𝒳.val.p.IsHomLift
      ((BigAffineFppf.inclusion B S hS).map (c.π.app i')) δ := hδ.toIsHomLift
  have key : 𝒳.val.p.IsHomLift
      ((BigAffineFppf.inclusion B S hS).map (c.π.app i')) (inv β ≫ δ) := by
    simpa only [Category.id_comp] using
      (IsHomLift.comp_lift_id_left' 𝒳.val.p
        ((BigAffineFppf.inclusion B S hS).obj c.pt) (inv β)
        ((BigAffineFppf.inclusion B S hS).map (c.π.app i')) δ)
  exact ⟨i', x', inv β ≫ δ, key⟩

section Presheaf

variable {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- The section named by the object `(U, v)` of the fibre over `U` of the category attached to a
set-valued presheaf is `v`. -/
private theorem presheafFiberElement_mk (U : BigFppfOver B S hS) (v : F.obj (op U)) :
    presheafFiberElement B S hS F
        (⟨⟨U, Discrete.mk v⟩, rfl⟩ : (fibredCategory B S hS F).val.p.Fiber U) = v :=
  presheafFiberElement_eq_of_heq B S hS F _ v HEq.rfl

end Presheaf

section Colimits

variable {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {I : Type u} [Category.{u} I]
  (D : I ⥤ BigFppfOver B S hS) (c : Cone D)

/-- Descent of objects for the category attached to a set-valued presheaf puts every section over
the vertex of a cone in the image of the comparison map out of the colimit of the sections at the
stages. This is the hypothesis of the surjective affine-limit criterion of Stacks 0CM6. -/
private theorem exists_colimit_preimage_of_descentObj
    (h : Deformation.Artin.DescentObj (fibredCategory B S hS F).val.p D c)
    (x : F.obj (op c.pt)) :
    ∃ z : colimit (D.op ⋙ F), colimit.desc (D.op ⋙ F) (F.mapCocone c.op) z = x := by
  obtain ⟨i, xi, δ, hδ⟩ := h ⟨⟨c.pt, Discrete.mk x⟩, rfl⟩
  refine ⟨colimit.ι (D.op ⋙ F) (op i) (presheafFiberElement B S hS F xi), ?_⟩
  rw [colimit.ι_desc_apply]
  exact (presheafFiberElement_map B S hS F (c.π.app i)
    (⟨⟨c.pt, Discrete.mk x⟩, rfl⟩ : (fibredCategory B S hS F).val.p.Fiber c.pt)
    xi δ hδ).trans (presheafFiberElement_mk B S hS c.pt x)

end Colimits

/-- **Limit preservation on objects makes a representing algebraic space locally of finite
presentation.** If `𝒳` is equivalent over the big fppf site of `S` to the category of elements of
an algebraic space `F`, and the structure morphism `𝒳 ⟶ (Sch/S)_{fppf}` is limit preserving on
objects in the sense of Stacks 06CU, then `F ⟶ S` is locally of finite presentation.

This is the surjective affine-limit criterion of Stacks 0CM6, whose hypothesis is what limit
preservation on objects supplies: it descends an object over an affine inverse limit to a finite
stage, which for the category of elements of `F` says that every section over the limit is the
restriction of a section at a stage. -/
private theorem isLocallyOfFinitePresentation_terminal_of_isLimitPreservingOnObjects
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    (e : StacksRepresentableCFG.EquivalenceOver
      𝒳.val.p (presheafOfCategories (F ⋙ typeToCat)).p)
    (h : BigFppfOver.IsLimitPreservingOnObjects.{u, u, u, u, u + 1} B S hS 𝒳
      (terminalCFG B S hS) (Bicategory.InducedBicategory.mkHom (toTerminalCFG B S hS 𝒳))) :
    Space.IsLocallyOfFinitePresentation B S hS (terminal.from F) := by
  refine Space.isLocallyOfFinitePresentation_terminal_of_affineLimit_surjective B S hS hF ?_
  intro I _ _ D c hc hD hpt x
  refine exists_colimit_preimage_of_descentObj B S hS D c ?_ x
  refine Deformation.Artin.descentObj_of_equivalenceOver D c e.symm ?_
  exact descentObj_of_isLimitPreservingOnObjects B S hS 𝒳 h
    { obj := fun i => ⟨D.obj i, hD i⟩
      map := fun a => ObjectProperty.homMk (D.map a) }
    { pt := ⟨c.pt, hpt⟩
      π :=
        { app := fun i => ObjectProperty.homMk (c.π.app i)
          naturality := fun i j a => by
            apply ObjectProperty.hom_ext
            show c.π.app j = c.π.app i ≫ D.map a
            exact (c.w a).symm } } hc

/-- **The implication (1) ⟹ (3) of Stacks 07XN.** An algebraic stack over the big fppf site of
`S` which is a stack in setoids and whose structure morphism to `(Sch/S)_{fppf}` is limit
preserving on objects is representable by an algebraic space locally of finite presentation
over `S`, in the sense of
`AlgebraicGeometry.Stack.IsRepresentableBySpaceLocallyOfFinitePresentation`.

Representability is the implication (1) ⟹ (3) of Stacks 04SZ, which rests on Stacks 04S6; local
finite presentation of the structure morphism is then Stacks 06CX, as
`isRepresentableBySpaceLocallyOfFinitePresentation_of_isLimitPreservingOnObjects`. -/
theorem
isRepresentableBySpaceLocallyOfFinitePresentation_of_isStackInSetoids_and_isLimitPreservingOnObjects
    (halg : IsAlgebraicStack.{u, t} B S hS 𝒳.val)
    (h : 𝒳.val.p.IsStackInSetoids (BigFppfOver.topology B S hS) ∧
      BigFppfOver.IsLimitPreservingOnObjects.{u, u, u, u, u + 1} B S hS 𝒳
        (terminalCFG B S hS) (Bicategory.InducedBicategory.mkHom (toTerminalCFG B S hS 𝒳))) :
    IsRepresentableBySpaceLocallyOfFinitePresentation B S hS 𝒳 :=
  isRepresentableBySpaceLocallyOfFinitePresentation_of_isLimitPreservingOnObjects B S hS 𝒳
    (isRepresentableByAlgebraicSpace_of_isStackInSetoids B S hS 𝒳 halg h.1) h.2

/-- **The implication (3) ⟹ (2) of Stacks 07XN.** A category fibred in groupoids over the big
fppf site of `S` which is representable by an algebraic space locally of finite presentation over
`S`, in the sense of `AlgebraicGeometry.Stack.IsRepresentableBySpaceLocallyOfFinitePresentation`,
is a stack in setoids and is limit preserving in the sense of Stacks 07XL.

The implication (3) ⟹ (1) of
`StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingSetoidRepresentable` gives the
stack-in-setoids clause and limit preservation on objects of the structure morphism. The latter
makes the representing algebraic space `F` locally of finite presentation over `S` by Stacks 0CM6;
Stacks 05N0 turns that into limit preservation of the functor of points of `F`, which passes to the
category of elements by `AlgebraicGeometry.Stack.isLimitPreserving_fibredCategory` and to `𝒳` by
the invariance of limit preservation under equivalence over the site. Algebraicity is not used. -/
theorem isStackInSetoids_and_isLimitPreserving_of_isRepresentableBySpaceLocallyOfFinitePresentation
    (h : IsRepresentableBySpaceLocallyOfFinitePresentation B S hS 𝒳) :
    𝒳.val.p.IsStackInSetoids (BigFppfOver.topology B S hS) ∧
      Deformation.Artin.IsLimitPreserving.{u, u, u, u + 1, u} B S hS 𝒳 := by
  have hset := isStackInSetoids_of_isRepresentableByAlgebraicSpace B S hS 𝒳 h.1
  have hlim := (isLimitPreservingOnObjects_iff_isLocallyOfFinitePresentation B S hS 𝒳
    (terminalCFG B S hS) (Bicategory.InducedBicategory.mkHom (toTerminalCFG B S hS 𝒳))
    (isRepresentableByAlgebraicSpaces_toTerminalCFG B S hS 𝒳 h.1)).2 h.2
  obtain ⟨⟨F, hF, ⟨e⟩⟩, -⟩ := h
  exact ⟨hset, (isLimitPreserving_iff_of_equivalenceOver B S hS 𝒳 (fibredCategory B S hS F) e).2
    (isLimitPreserving_fibredCategory B S hS
      ((Space.isLocallyOfFinitePresentation_terminal_iff_limitPreserving B S hS hF).1
        (isLocallyOfFinitePresentation_terminal_of_isLimitPreservingOnObjects B S hS 𝒳 hF e
          hlim)))⟩

/-- **Stacks 07XN.** For an algebraic stack `𝒳` over the big fppf site of a scheme `S` the
following are equivalent:

1. `𝒳` is a stack in setoids and its structure morphism `𝒳 ⟶ (Sch/S)_{fppf}` is limit preserving
   on objects in the sense of Stacks 06CU;
2. `𝒳` is a stack in setoids and is limit preserving in the sense of Stacks 07XL;
3. `𝒳` is representable by an algebraic space over `S` which is locally of finite presentation
   over `S`, i.e. `AlgebraicGeometry.Stack.IsRepresentableBySpaceLocallyOfFinitePresentation`.

The three implications proved are the cycle (1) ⟹ (3) ⟹ (2) ⟹ (1). Inverse systems are indexed
by categories in the universe `u` of the schemes, which is the size the source's directed inverse
systems have and the size at which the inputs of the two nontrivial implications are available. -/
@[stacks 07XN]
theorem isStackInSetoids_isLimitPreserving_tfae
    (halg : IsAlgebraicStack.{u, t} B S hS 𝒳.val) :
    List.TFAE
      [𝒳.val.p.IsStackInSetoids (BigFppfOver.topology B S hS) ∧
          BigFppfOver.IsLimitPreservingOnObjects.{u, u, u, u, u + 1} B S hS 𝒳
            (terminalCFG B S hS) (Bicategory.InducedBicategory.mkHom (toTerminalCFG B S hS 𝒳)),
        𝒳.val.p.IsStackInSetoids (BigFppfOver.topology B S hS) ∧
          Deformation.Artin.IsLimitPreserving.{u, u, u, u + 1, u} B S hS 𝒳,
        IsRepresentableBySpaceLocallyOfFinitePresentation B S hS 𝒳] := by
  tfae_have 1 → 3 := fun h =>
    isRepresentableBySpaceLocallyOfFinitePresentation_of_isLimitPreservingOnObjects B S hS 𝒳
      (isRepresentableByAlgebraicSpace_of_isStackInSetoids B S hS 𝒳 halg h.1) h.2
  tfae_have 3 → 2 :=
    isStackInSetoids_and_isLimitPreserving_of_isRepresentableBySpaceLocallyOfFinitePresentation
      B S hS 𝒳
  tfae_have 2 → 1 :=
    isStackInSetoids_and_isLimitPreservingOnObjects_of_isLimitPreserving B S hS 𝒳
  tfae_finish

end AlgebraicGeometry.Stack

end
