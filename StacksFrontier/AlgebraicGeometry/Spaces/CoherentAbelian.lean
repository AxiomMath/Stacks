module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SiteCoherenceCokernels
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentDerivedComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentQuasicoherence
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulesAbelian
public import StacksFrontier.AlgebraicGeometry.Topologies.CoherentExtensionOnSite

/-!
# Coherent modules on an algebraic space form an abelian category

Let `F` be an algebraic space over a scheme `S`.  The coherent `𝒪_F`-modules of Stacks 07UA are
closed under kernels, cokernels and extensions inside the category of all `𝒪_F`-modules, and the
category `Coh(𝒪_F)` they form is abelian.

## Main results

* `AlgebraicGeometry.Space.isCoherent_kernel` and
  `AlgebraicGeometry.Space.isCoherent_cokernel`: the kernel and the cokernel of a map of
  coherent modules are coherent.
* `AlgebraicGeometry.Space.isCoherent_X₂_of_shortExact`: an extension of coherent modules is
  coherent, that is, the middle term of a short exact sequence of `𝒪_F`-modules whose outer
  terms are coherent is coherent.
* `AlgebraicGeometry.Space.nonempty_abelian_coherentModules`: the category of coherent
  `𝒪_F`-modules is abelian.
* `AlgebraicGeometry.Space.isCoherent_isClosedUnderExtensions` and
  `AlgebraicGeometry.Space.isCoherent_isClosedUnderFiniteCoproducts` are the extension result
  and the coproduct closure it yields; together with the kernel and cokernel closure
  instances of `StacksFrontier.AlgebraicGeometry.Spaces.CoherentDerivedComparison` they are the
  three inputs out of which `AlgebraicGeometry.Space.coherentModules_abelian_of_closure`
  builds the abelian structure.

## Implementation notes

**Local Noetherianity is a hypothesis of no statement here.**  Stacks 07UC assumes the
algebraic space locally Noetherian, and the hypothesis is indispensable in the source's own
argument, which identifies coherence with quasi-coherence together with finite type (Stacks
07UB) and runs the three closure properties there.  The route taken here does not: the predicate
`AlgebraicGeometry.Space.IsCoherent` carries the sectionwise coherence condition of Stacks
03DL(8) directly, and that condition is closed under kernels, cokernels and extensions over an
*arbitrary* ringed site, by Stacks 01BY.  So the results below are stated without the
hypothesis, which would be dead weight; they specialize to Stacks 07UC on a locally Noetherian
algebraic space.

**The module universe is the universe `u` of the schemes.**  That is the universe in which the
category of `𝒪_F`-modules is abelian, by
`StacksFrontier.AlgebraicGeometry.Spaces.ModulesAbelian`, hence the universe in which a short exact
complex has its first term a kernel of its second map and its third term a cokernel of its
first; and it is the universe in which the quasi-coherence clause of
`AlgebraicGeometry.Space.IsCoherent` follows from its coherence clause, by
`AlgebraicGeometry.Space.isCoherent_of_isCoherentOnSite`.  Together these make every statement
below cost exactly its coherence-on-the-site counterpart: no module is ever assumed
quasi-coherent, and quasi-coherence of the conclusions is free.

**Closure under finite coproducts is not an independent input.**  A binary coproduct in an
additive category is a biproduct, hence an extension of one summand by the other, so it is
covered by the extension result; the empty coproduct is covered by
`AlgebraicGeometry.Space.isCoherent_containsZero` together with closure under isomorphisms, and
the general finite case follows from these two by
`CategoryTheory.ObjectProperty.IsClosedUnderFiniteCoproducts.mk'`.

**The abelian structure is not registered as an instance.**  It is produced by the `def`
`AlgebraicGeometry.Space.coherentModules_abelian_of_closure` once the three closure properties
are available, and is exhibited here as the inhabitant of a `Nonempty`, so that no choice
principle enters a statement.

## References

* [Stacks Project, Tag 07UC](https://stacks.math.columbia.edu/tag/07UC)
* [Stacks Project, Tag 07UA](https://stacks.math.columbia.edu/tag/07UA)
* [Stacks Project, Tag 01BY](https://stacks.math.columbia.edu/tag/01BY)
* [Stacks Project, Tag 0754](https://stacks.math.columbia.edu/tag/0754)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-- **[Stacks, Tag 07UC].** The kernel of a map of coherent modules on an algebraic space is
coherent.

The kernel of a map of coherent sheaves of modules on an arbitrary site is coherent, by
Stacks 01BY (3); quasi-coherence of the kernel is then free at this module universe. -/
@[stacks 07UC "kernel"]
theorem isCoherent_kernel {M N : Modules.{u, u} B S hS F hF} (hM : IsCoherent B S hS F hF M)
    (hN : IsCoherent B S hS F hF N) (φ : M ⟶ N) : IsCoherent B S hS F hF (kernel φ) :=
  let : SheafOfModules.IsCoherentOnSite (kernel φ) :=
    Stacks.SheafOfModules.isCoherentOnSite_kernel hM.toIsCoherentOnSite hN.toIsCoherentOnSite φ
  isCoherent_of_isCoherentOnSite B S hS F hF (kernel φ)

/-- **[Stacks, Tag 07UC].** The cokernel of a map of coherent modules on an algebraic space is
coherent.

The cokernel of a map of coherent sheaves of modules on an arbitrary site is coherent, by
Stacks 01BY (3); quasi-coherence of the cokernel is then free at this module universe. -/
@[stacks 07UC "cokernel"]
theorem isCoherent_cokernel {M N : Modules.{u, u} B S hS F hF} (hM : IsCoherent B S hS F hF M)
    (hN : IsCoherent B S hS F hF N) (φ : M ⟶ N) : IsCoherent B S hS F hF (cokernel φ) :=
  let : SheafOfModules.IsCoherentOnSite (cokernel φ) :=
    Stacks.SheafOfModules.isCoherentOnSite_cokernel φ hM.toIsCoherentOnSite
      hN.toIsCoherentOnSite
  isCoherent_of_isCoherentOnSite B S hS F hF (cokernel φ)

/-- **[Stacks, Tag 07UC].** An extension of coherent modules on an algebraic space is coherent:
the middle term of a short exact sequence of `𝒪_F`-modules whose outer terms are coherent is
coherent.

An extension is represented by a short exact complex of `𝒪_F`-modules, so the statement
quantifies over all extensions of the third term by the first rather than over a choice of one.
The content is Stacks 01BY (4) on the small étale ringed site of `F`; quasi-coherence of the
middle term is free at this module universe. -/
@[stacks 07UC "extensions"]
theorem isCoherent_X₂_of_shortExact {T : ShortComplex (Modules.{u, u} B S hS F hF)}
    (hT : T.ShortExact) (h₁ : IsCoherent B S hS F hF T.X₁)
    (h₃ : IsCoherent B S hS F hF T.X₃) : IsCoherent B S hS F hF T.X₂ :=
  let : SheafOfModules.IsCoherentOnSite T.X₂ :=
    Stacks.SheafOfModules.isCoherentOnSite_X₂_of_shortExact hT h₁.toIsCoherentOnSite
      h₃.toIsCoherentOnSite
  isCoherent_of_isCoherentOnSite B S hS F hF T.X₂

/-- **The coherent modules on an algebraic space are closed under extensions.**  This is
`AlgebraicGeometry.Space.isCoherent_X₂_of_shortExact` as a closure property. -/
instance isCoherent_isClosedUnderExtensions :
    (isCoherent.{u, u} B S hS F hF).IsClosedUnderExtensions where
  prop_X₂_of_shortExact hT h₁ h₃ := isCoherent_X₂_of_shortExact B S hS F hF hT h₁ h₃

/-- **The coherent modules on an algebraic space are closed under binary coproducts.**  A binary
coproduct in an additive category is a biproduct, hence an extension of one summand by the
other, so this is closure under extensions. -/
instance isCoherent_isClosedUnderBinaryCoproducts :
    (isCoherent.{u, u} B S hS F hF).IsClosedUnderBinaryCoproducts := by
  refine ObjectProperty.IsClosedUnderColimitsOfShape.mk' ?_
  rintro _ ⟨G, hG⟩
  exact (isCoherent.{u, u} B S hS F hF).prop_of_iso
    ((biprod.isoCoprod (G.obj ⟨WalkingPair.left⟩) (G.obj ⟨WalkingPair.right⟩)).trans
      (HasColimit.isoOfNatIso (diagramIsoPair G)).symm)
    ((isCoherent.{u, u} B S hS F hF).prop_biprod (hG ⟨WalkingPair.left⟩)
      (hG ⟨WalkingPair.right⟩))

/-- **The coherent modules on an algebraic space are closed under finite coproducts.**  The
empty coproduct is a zero module, which is coherent, and the binary case is closure under
extensions; the general finite case follows from those two. -/
instance isCoherent_isClosedUnderFiniteCoproducts :
    (isCoherent.{u, u} B S hS F hF).IsClosedUnderFiniteCoproducts :=
  ObjectProperty.IsClosedUnderFiniteCoproducts.mk'

/-- **[Stacks, Tag 07UC].** The category `Coh(𝒪_F)` of coherent modules on an algebraic space is
abelian.

The abelian structure is the one a full subcategory of an abelian category closed under kernels,
cokernels and finite coproducts carries, assembled by
`AlgebraicGeometry.Space.coherentModules_abelian_of_closure`; the kernel and cokernel closure
properties are Stacks 01BY (3) on the small étale ringed site and the coproduct one comes from
the extension result above. -/
@[stacks 07UC "abelian category"]
theorem nonempty_abelian_coherentModules :
    Nonempty (Abelian (CoherentModules.{u, u} B S hS F hF)) :=
  ⟨coherentModules_abelian_of_closure B S hS F hF⟩

end AlgebraicGeometry.Space

end
