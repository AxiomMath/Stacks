module

public import Mathlib.Topology.Sheaves.SheafCondition.PairwiseIntersections
public import StacksFrontier.AlgebraicGeometry.FormalScheme.SchemeToFormalScheme
public import StacksFrontier.AlgebraicGeometry.FormalScheme.WeakIdealOfDefinition
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The ideal sheaf of a morphism into a locally topologically ringed space

A morphism `f : 𝔜 ⟶ 𝔛` of locally topologically ringed spaces has a *kernel ideal sheaf*
`ker f ⊆ 𝒪_𝔛`, the kernel of the comparison map `f^♯ : 𝒪_𝔛 ⟶ f_* 𝒪_𝔜` read on sections over
every open. It is an ideal sheaf in the sense of
`AlgebraicGeometry.LocallyTopologicallyRingedSpace.IdealSheaf`: restriction carries it into
itself by naturality of `f^♯`, and it is local because `𝒪_𝔜` is a sheaf, so a section of `𝒪_𝔛`
whose image vanishes near every point of its domain has vanishing image.

This is the map that sends a thickening `i : Z ⟶ 𝔛` to the ideal sheaf classifying it, and so
one half of the data of the correspondence of **Stacks 0AIV** between weak ideals of definition
and thickenings. Nothing here claims that correspondence; see the implementation notes.

## Main definitions

* `AlgebraicGeometry.LocallyTopologicallyRingedSpace.IdealSheaf.ker`: the kernel ideal sheaf of
  a morphism of locally topologically ringed spaces.

## Main results

* `AlgebraicGeometry.LocallyTopologicallyRingedSpace.eq_of_isLimit`,
  `AlgebraicGeometry.LocallyTopologicallyRingedSpace.eq_zero_of_isLimit`,
  `AlgebraicGeometry.LocallyTopologicallyRingedSpace.eq_zero_of_restrict_eq_zero` and
  `AlgebraicGeometry.LocallyTopologicallyRingedSpace.eq_zero_of_locally_zero`: a section of a
  sheaf of topological rings vanishing near every point of its domain is zero, which is the
  sheaf condition that the ideal sheaf field `IdealSheaf.mem_of_locally_mem` asks for.
* `AlgebraicGeometry.LocallyTopologicallyRingedSpace.IdealSheaf.ker_le_ker_comp`: the kernel
  ideal sheaf grows under precomposition, which is the order-reversal of the correspondence of
  Stacks 0AIV.
* `AlgebraicGeometry.LocallyTopologicallyRingedSpace.IdealSheaf.isWeakIdealOfDefinitionOn_ker`:
  the kernel ideal sheaf is a weak ideal of definition over a class of opens as soon as the
  sections of `𝒪_𝔜` over the preimage of a member of the class are discrete at zero and the
  sections of the kernel over a member are topologically nilpotent. The first condition is
  automatic when `𝔜` is the pseudo-discretisation of a scheme and the preimage is quasi-compact,
  which is
  `AlgebraicGeometry.LocallyTopologicallyRingedSpace.IdealSheaf`
  `.isWeakIdealOfDefinitionOn_ker_of_scheme`.

## Implementation notes

The openness half of the weak ideal-of-definition condition is proved here outright: the kernel
of a continuous ring homomorphism into a ring in which `{0}` is open is open. The topological
nilpotence half is a hypothesis, and this is not an oversight. For a thickening `i : Z ⟶ 𝔛` of a
formal scheme the source deduces it from the affine classification — over an affine formal open
`𝔘 ≅ Spf A` the scheme `Z|_𝔘` is `Spec (A / J)` and the surjectivity of `Z → 𝔛` forces `J` to lie
in every open prime of `A`, hence to consist of topologically nilpotent elements. That argument
needs the affineness of `Z|_𝔘`, which in turn needs the comparison between a formal scheme in
the sense of `AlgebraicGeometry.IsFormalScheme` and the affine formal algebraic spaces of
`AlgebraicGeometry.FormalSpace`, where
`AlgebraicGeometry.FormalSpace.existsUnique_weakIdeal_quotient` carries out the affine
classification. That comparison is not in this library, so the conclusion it would give is a
hypothesis here rather than a theorem.

Correspondingly nothing here carries the tag `0AIV`. The tag's correspondence is a bijection,
and its other half — the construction of `(𝔛, 𝒪_𝔛/ℐ)` from a weak ideal of definition `ℐ` —
needs a quotient of a sheaf of *topological* rings by an ideal subsheaf, which does not exist in
this library in any form: the quotient presheaf `U ↦ 𝒪_𝔛(U)/ℐ(U)` is separated, by
`IdealSheaf.mem_of_locally_mem`, but is not a sheaf, and no sheafification of presheaves of
topological rings is available. Stating a bijection with that half assumed would put the tag on
an assumption.

Elementwise separatedness of a sheaf of topological rings is obtained from the explicit limit
cone of `StacksFrontier.Topology.Algebra.RingLimits`, whose apex is a subring of a product, rather
than from `CategoryTheory.Presheaf.IsSheaf.section_ext`: the latter needs the forgetful functor
to `Type` to reflect isomorphisms, which it does not for topological rings — a continuous
bijective ring homomorphism need not be a homeomorphism.

## References

* [Stacks Project, Tag 0AIV](https://stacks.math.columbia.edu/tag/0AIV)
* [Stacks Project, Tag 0AMV](https://stacks.math.columbia.edu/tag/0AMV)
* [Stacks Project, Tag 0B23](https://stacks.math.columbia.edu/tag/0B23)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.LocallyTopologicallyRingedSpace

universe u

/-! ### Elementwise separatedness -/

/-- Two elements of the apex of a limit cone of topological rings with the same image under
every projection are equal: the apex is isomorphic to the subring of compatible families in the
product of the components, where the projections are the coordinates. -/
theorem eq_of_isLimit {J : Type u} [Category.{u} J] {F : J ⥤ TopCommRingCat.{u}}
    {c : Cone F} (hc : IsLimit c) {x y : c.pt.α}
    (h : ∀ j, (c.π.app j).1 x = (c.π.app j).1 y) : x = y := by
  let e := IsLimit.conePointUniqueUpToIso hc (TopCommRingCat.limitConeIsLimit F)
  have ev : ∀ {A B : TopCommRingCat.{u}} {g g' : A ⟶ B}, g = g' → ∀ z, g.1 z = g'.1 z :=
    fun hg z => by rw [hg]
  have key : e.hom.1 x = e.hom.1 y := by
    apply Subtype.ext
    funext j
    have hcomp := IsLimit.conePointUniqueUpToIso_hom_comp hc
      (TopCommRingCat.limitConeIsLimit F) j
    exact (ev hcomp x).trans ((h j).trans (ev hcomp y).symm)
  exact (ev e.hom_inv_id x).symm.trans ((congrArg e.inv.1 key).trans (ev e.hom_inv_id y))

/-- An element of the apex of a limit cone of topological rings all of whose projections vanish
on it is zero. -/
theorem eq_zero_of_isLimit {J : Type u} [Category.{u} J] {F : J ⥤ TopCommRingCat.{u}}
    {c : Cone F} (hc : IsLimit c) {x : c.pt.α} (h : ∀ j, (c.π.app j).1 x = 0) : x = 0 :=
  eq_of_isLimit hc fun j => (h j).trans (map_zero (c.π.app j).1).symm

/-- A section of a sheaf of topological rings over an open covered by a family of opens, whose
restriction to each member of the family vanishes, is zero. This is the elementwise form of the
sheaf condition, read off the limit presenting the sections over a union. -/
theorem eq_zero_of_restrict_eq_zero {Z : TopCat.{u}} {F : Z.Presheaf TopCommRingCat.{u}}
    (hF : F.IsSheaf) {ι : Type u} (W : ι → Opens Z) (V : Opens Z) (hWV : ∀ i, W i ≤ V)
    (hcover : V ≤ iSup W) {s : (F.obj (op V)).α}
    (hzero : ∀ i, (F.map (homOfLE (hWV i)).op).1 s = 0) :
    s = 0 := by
  obtain rfl : V = iSup W := le_antisymm hcover (iSup_le hWV)
  obtain ⟨hc⟩ := hF.isSheafPairwiseIntersections W
  refine eq_zero_of_isLimit hc fun j => ?_
  induction j using Opposite.rec with
  | op j =>
    cases j with
    | single i =>
      exact hzero i
    | pair i i' =>
      change (F.map ((homOfLE (le_iSup W i)).op ≫
        (homOfLE (inf_le_left : W i ⊓ W i' ≤ W i)).op)).1 s = 0
      rw [F.map_comp]
      change (F.map _).1 ((F.map _).1 s) = 0
      rw [hzero i, map_zero]

/-- A section of a sheaf of topological rings vanishing in a neighbourhood of every point of its
domain is zero. -/
theorem eq_zero_of_locally_zero {Z : TopCat.{u}} {F : Z.Presheaf TopCommRingCat.{u}}
    (hF : F.IsSheaf) {V : Opens Z} {s : (F.obj (op V)).α}
    (h : ∀ p ∈ V, ∃ (W : Opens Z) (hW : W ≤ V),
      p ∈ W ∧ (F.map (homOfLE hW).op).1 s = 0) :
    s = 0 := by
  choose W hWV hpW hzero using fun p : V => h p p.property
  exact eq_zero_of_restrict_eq_zero hF W V hWV
    (fun p hp => Opens.mem_iSup.mpr ⟨⟨p, hp⟩, hpW ⟨p, hp⟩⟩) hzero

namespace IdealSheaf

/-! ### The kernel ideal sheaf -/

variable {X Y : LTRS.{u}}

/-- The *kernel ideal sheaf* of a morphism `f : Y ⟶ X` of locally topologically ringed spaces:
the kernel of the comparison map `f^♯ : 𝒪_X ⟶ f_* 𝒪_Y` on the sections over every open. The
subpresheaf condition is the naturality of `f^♯` and the sheaf condition is the separatedness of
`𝒪_Y`. -/
@[sga "3 VIIA 1.3" "more general"]
def ker (f : Y ⟶ X) : IdealSheaf X where
  ideal U := RingHom.ker (f.toHom.c.app (op U)).1
  map_mem := by
    intro U V hVU s hs
    have hnat := congrArg (fun g : X.presheaf.obj (op U) ⟶
        (f.toHom.base _* Y.presheaf).obj (op V) => g.1 s)
      (f.toHom.c.naturality (homOfLE hVU).op)
    refine RingHom.mem_ker.mpr (hnat.trans ?_)
    change ((f.toHom.base _* Y.presheaf).map (homOfLE hVU).op).1
      ((f.toHom.c.app (op U)).1 s) = 0
    rw [RingHom.mem_ker.mp hs, map_zero]
  mem_of_locally_mem := by
    intro U s hlocal
    refine RingHom.mem_ker.mpr (eq_zero_of_locally_zero Y.IsSheaf fun p hp => ?_)
    obtain ⟨V, hVU, hpV, hmem⟩ := hlocal (f.toHom.base p) hp
    refine ⟨(Opens.map f.toHom.base).obj V, fun q hq => hVU hq, hpV, ?_⟩
    exact (congrArg (fun g : X.presheaf.obj (op U) ⟶
        (f.toHom.base _* Y.presheaf).obj (op V) => g.1 s)
      (f.toHom.c.naturality (homOfLE hVU).op)).symm.trans (RingHom.mem_ker.mp hmem)

/-- The ideal of `ker f` over `U` is the kernel of `f^♯` on sections over `U`. -/
@[simp]
theorem ker_ideal (f : Y ⟶ X) (U : Opens X) :
    (ker f).ideal U = RingHom.ker (f.toHom.c.app (op U)).1 :=
  rfl

/-- A section `s` over `U` lies in `ker f` if and only if `f^♯ s = 0`. -/
theorem mem_ker_iff {f : Y ⟶ X} {U : Opens X} {s : (X.presheaf.obj (op U)).α} :
    s ∈ (ker f).ideal U ↔ (f.toHom.c.app (op U)).1 s = 0 :=
  RingHom.mem_ker

/-- The kernel ideal sheaf grows when the morphism is precomposed: a thickening factoring
through another has the larger ideal sheaf. This is the order-reversal of the correspondence of
**Stacks 0AIV**, where a smaller weak ideal of definition cuts out a larger thickening. -/
theorem ker_le_ker_comp {Z : LTRS.{u}} (f : Z ⟶ Y) (g : Y ⟶ X) (U : Opens X) :
    (ker g).ideal U ≤ (ker (f ≫ g)).ideal U := by
  intro s hs
  refine mem_ker_iff.mpr ?_
  rw [show (Hom.toHom (f ≫ g)).c.app (op U) = (Hom.toHom g).c.app (op U) ≫
      (Hom.toHom f).c.app ((Opens.map (Hom.toHom g).base).op.obj (op U)) from
    PresheafedSpace.comp_c_app _ _ _]
  change ((Hom.toHom f).c.app _).1 (((Hom.toHom g).c.app (op U)).1 s) = 0
  rw [mem_ker_iff.mp hs, map_zero]

/-! ### When the kernel is a weak ideal of definition -/

/-- The kernel ideal sheaf of `f : Y ⟶ X` is a weak ideal of definition over a class `𝒜` of
opens of `X` as soon as, over every member `U` of `𝒜`, the zero section of `𝒪_Y` over the
preimage of `U` is isolated and the sections of the kernel over `U` are topologically nilpotent.
The first hypothesis gives the openness of the kernel, the comparison map being continuous. -/
theorem isWeakIdealOfDefinitionOn_ker (f : Y ⟶ X) (𝒜 : Opens X → Prop)
    (hzero : ∀ U : Opens X, 𝒜 U →
      IsOpen ({0} : Set (Y.presheaf.obj (op ((Opens.map f.toHom.base).obj U))).α))
    (hnilp : ∀ U : Opens X, 𝒜 U → ∀ s ∈ (ker f).ideal U, IsTopologicallyNilpotent s) :
    (ker f).IsWeakIdealOfDefinitionOn 𝒜 :=
  fun U hU => ⟨(hzero U hU).preimage (f.toHom.c.app (op U)).2, hnilp U hU⟩

/-- The kernel ideal sheaf of a morphism `f : Z ⟶ X` out of the pseudo-discretisation of a
scheme is a weak ideal of definition over a class `𝒜` of opens of `X` whose members have
quasi-compact preimage and over which the sections of the kernel are topologically nilpotent:
the sections of the pseudo-discretisation of a scheme over a quasi-compact open are discrete.
For a thickening the preimage of an open is homeomorphic to it, so the quasi-compactness
hypothesis is the quasi-compactness of the members of `𝒜`. -/
theorem isWeakIdealOfDefinitionOn_ker_of_scheme {Z : Scheme.{u}} {X : LTRS.{u}}
    (f : schemeToLTRSObj Z ⟶ X) (𝒜 : Opens X → Prop)
    (hcompact : ∀ U : Opens X, 𝒜 U →
      IsCompact ((((Opens.map f.toHom.base).obj U : Opens ↥(schemeToLTRSObj Z))) :
        Set ↥(schemeToLTRSObj Z)))
    (hnilp : ∀ U : Opens X, 𝒜 U → ∀ s ∈ (ker f).ideal U, IsTopologicallyNilpotent s) :
    (ker f).IsWeakIdealOfDefinitionOn 𝒜 := by
  refine isWeakIdealOfDefinitionOn_ker f 𝒜 (fun U hU => ?_) hnilp
  have : DiscreteTopology
      ((schemeToLTRSObj Z).presheaf.obj (op ((Opens.map f.toHom.base).obj U))).α :=
    ⟨pseudoDiscreteTopology_eq_bot Z.presheaf (hcompact U hU)⟩
  exact isOpen_discrete _

end IdealSheaf

end AlgebraicGeometry.LocallyTopologicallyRingedSpace

end
