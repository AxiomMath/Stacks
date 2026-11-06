module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafifiedDirectSum
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentGrothendieck
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRingedToposHom
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.StructureSheafExtensionSections

/-!
# Square-zero extensions of the structure sheaf of an algebraic space

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` contained in a big fppf
site `B`.  [Stacks Project, Tag 05ZT] starts from a short exact sequence

```
0 ⟶ ℐ ⟶ 𝒜 ⟶ 𝒪_X ⟶ 0
```

of sheaves on the **small étale site of `X`**, in which `𝒜` is a sheaf of `f^{-1}𝒪_Y`-algebras,
the map `𝒜 ⟶ 𝒪_X` is a surjection of sheaves of `f^{-1}𝒪_Y`-algebras and `ℐ` is its kernel,
subject to two conditions: `ℐ` is an ideal of square zero in `𝒜`, and `ℐ` is quasi-coherent as
an `𝒪_X`-module.  This file packages exactly that datum as
`AlgebraicGeometry.Space.SquareZeroExtension`.

## Why this has to be defined here

Nothing in this development could state the hypotheses of Tag 05ZT before this file.
`Stacks.Thickenings.SquareZeroExtension` is the datum **for schemes**: its arguments are
`{X S : Scheme}` and its extension sheaf lives on the topological space of `X`, so it cannot
speak about a sheaf on `X_étale` for an algebraic space `X`.  The only other square-zero
extension of a structure sheaf in the tree,
`StacksFrontier/Topology/Sheaves/Modules/SquareZeroExtension.lean`, builds the *trivial* extension
`𝒪 ⋉ N` on a topological space, which is a construction and not a hypothesis.

## Main definitions

* `AlgebraicGeometry.Space.SquareZeroExtension`: the datum above.  `A` is the extension sheaf of
  commutative rings on `X_étale`, `π` its surjection onto `𝒪_X`, `toBase` the `f^{-1}𝒪_Y`-algebra
  structure and `toBase_π` the statement that `π` is a map of `f^{-1}𝒪_Y`-algebras; `I` is the
  kernel, as a quasi-coherent `𝒪_X`-module, included into `A` by `ι`.

## Main results

* `AlgebraicGeometry.Space.SquareZeroExtension.epi_π`: the surjection is an epimorphism.
* `AlgebraicGeometry.Space.SquareZeroExtension.idealAddEquivKer`: **over every object of the
  small étale site the sections of `ℐ` are the kernel ideal of `π`**, as additive groups, with
  `AlgebraicGeometry.Space.SquareZeroExtension.idealToKer_naturality` and
  `AlgebraicGeometry.Space.SquareZeroExtension.idealToKer_smul` recording that the identification
  commutes with restriction and carries the action of `𝒜` through `π`.
* `AlgebraicGeometry.Space.nonempty_squareZeroExtension`: **the datum is inhabited**, by the
  trivial extension `𝒜 = 𝒪_X`, `ℐ = 0`, whose realization is the identity thickening
  `X ⊂ X`.  This is recorded because a hypothesis structure that nothing can satisfy makes every
  statement quantified over it vacuous.

## Implementation notes

**The surjectivity of `π` is local surjectivity, and the exactness is sectionwise.**  Local
surjectivity is what a surjection of sheaves means, and it is what
`AlgebraicGeometry.Space.surjective_app_of_shortExact_of_isQuasicoherentOnSite` upgrades to
honest surjectivity of sections over an *affine* object of `X_étale`, which is the first step of
the proof of Tag 05ZT.  The kernel, by contrast, is pinned sectionwise: `mem_kernel` and
`exact_kernel` say that the image of `ι` over every object is exactly the kernel of `π` there,
and `exact_kernel` asks for a *unique* preimage, so `ι` is injective on sections and `I` is the
kernel rather than a cover of it.  This matches the shape of the scheme-level
`Stacks.Thickenings.SquareZeroExtension`, which is the datum this one ports.

**Why `I` carries its scalars over `𝒪_X` and not over `A`.**  The source asks `ℐ` to be
quasi-coherent *as an `𝒪_X`-module*, and the action of `𝒜` on `ℐ` factors through `𝒪_X`
precisely because `ℐ` has square zero.  The field `smul_lift` records that factorization in the
only form it is used in: a section `a` of `A` acts on a section of `I` through `π a`.  The same
choice is made at the scheme level, and for the same reason it is made in
`StacksFrontier/AlgebraicGeometry/Spaces/Thickenings/ConormalModuleInverseImageKernel.lean`, where
the inclusion of the conormal module of a first-order thickening into `i^{-1}𝒪_X` is a map of
`i^{-1}𝒪_X`-modules and not of `𝒪_Z`-modules.

**The algebra structure is stored in inverse-image form.**  `toBase` is a map
`f^{-1}𝒪_Y ⟶ A` of sheaves of commutative rings on `X_étale`, and `toBase_π` says that
composing it with `π` gives back the inverse-image form `f^♯ : f^{-1}𝒪_Y ⟶ 𝒪_X` of the structure
map of [Stacks Project, Tag 03G8].  Those two fields together are "`𝒜` is a sheaf of
`f^{-1}𝒪_Y`-algebras and `𝒜 ⟶ 𝒪_X` is a surjection of such": the compatibility is a field and
not a side remark, so an existence statement over this structure cannot drop it.

**What this file does not do, and why it carries no `@[stacks]` attribute.**  Tag 05ZT concludes
that such a datum is *realized*: there is a first-order thickening `X ⊂ X'` over `Y` with an
isomorphism `𝒪_{X'} ⟶ 𝒜` of `f^{-1}𝒪_Y`-algebras compatible with the surjections to `𝒪_X`.
That conclusion needs the chart construction `U ↦ Spec(𝒜(U))`, the identification
`ℐ(V) = ℐ(U) ⊗_{𝒪(U)} 𝒪(V)` that makes it étale, and a descent along an étale
equivalence-relation presentation; none of those is here.  The attribute belongs on the theorem
that proves the conclusion at these hypotheses and **on this site**, and until then nothing in
this file claims any part of the tag.

## References

* [Stacks Project, Tag 05ZT](https://stacks.math.columbia.edu/tag/05ZT)
* [Stacks Project, Tag 05YV](https://stacks.math.columbia.edu/tag/05YV), the scheme-level
  statement this one is the algebraic-space analogue of.
* [Stacks Project, Tag 05ZK](https://stacks.math.columbia.edu/tag/05ZK), thickenings of
  algebraic spaces.
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8), the structure map.
* [Stacks Project, Tag 03G9](https://stacks.math.columbia.edu/tag/03G9), quasi-coherent modules
  on an algebraic space.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The inverse image `f^{-1}𝒪_Y` of the structure sheaf of the target of a morphism of
algebraic spaces, as a sheaf of *commutative* rings on the small étale site of the source.

This is the ring sheaf over which the extension sheaf of
`AlgebraicGeometry.Space.SquareZeroExtension` is an algebra.  It is the commutative-ring-valued
companion of `AlgebraicGeometry.Space.structureRingSheafInverseImage`, and it is the domain of
the inverse-image form of the structure map of [Stacks Project, Tag 03G8]. -/
abbrev inverseImageStructureCommRingSheaf {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) :=
  (inverseImageCommRingFunctor (smallEtaleRingedToposHom B S hS f).toToposHom).obj
    (smallEtaleRingedTopos B S hS Y).O

/-- **The hypotheses of [Stacks Project, Tag 05ZT] for an algebraic space.**  A short exact
sequence `0 ⟶ ℐ ⟶ 𝒜 ⟶ 𝒪_X ⟶ 0` of sheaves on the small étale site of `X`, in which `𝒜` is a
sheaf of `f^{-1}𝒪_Y`-algebras, the map to `𝒪_X` is a surjection of such, and the kernel `ℐ` has
square zero and is quasi-coherent as an `𝒪_X`-module. -/
structure SquareZeroExtension {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) where
  /-- The extension sheaf `𝒜`. -/
  A : Sheaf (SmallEtale.topology B S hS X.1) CommRingCat.{u}
  /-- The surjection `𝒜 ⟶ 𝒪_X`. -/
  π : A ⟶ (smallEtaleRingedTopos B S hS X).O
  /-- Sections of the structure sheaf lift locally to the extension sheaf; this is what it means
  for `π` to be a surjection of sheaves. -/
  locallySurjective_π : Sheaf.IsLocallySurjective π
  /-- The `f^{-1}𝒪_Y`-algebra structure of `𝒜`. -/
  toBase : inverseImageStructureCommRingSheaf B S hS f ⟶ A
  /-- `π` is a map of `f^{-1}𝒪_Y`-algebras: it carries the algebra structure of `𝒜` to the
  structure map `f^♯ : f^{-1}𝒪_Y ⟶ 𝒪_X` of [Stacks Project, Tag 03G8]. -/
  toBase_π : toBase ≫ π = (smallEtaleRingedToposHom B S hS f).fSharpInverseImage
  /-- The kernel `ℐ`, as an `𝒪_X`-module. -/
  I : Modules.{u, u} B S hS X.1 X.2
  /-- `ℐ` is quasi-coherent as an `𝒪_X`-module: condition (2) of the source. -/
  quasicoherent : I.IsQuasicoherentOnSite
  /-- The inclusion `ℐ ⟶ 𝒜`, on the sections over each object of the small étale site. -/
  ι (U : (SmallEtale B S hS X.1)ᵒᵖ) : I.val.obj U →+ A.obj.obj U
  /-- The inclusion commutes with restriction. -/
  naturality {U V : (SmallEtale B S hS X.1)ᵒᵖ} (g : U ⟶ V) (x : I.val.obj U) :
    ι V (I.val.map g x) = A.obj.map g (ι U x)
  /-- The inclusion lands in the kernel of `π`. -/
  mem_kernel (U : (SmallEtale B S hS X.1)ᵒᵖ) (x : I.val.obj U) :
    π.hom.app U (ι U x) = 0
  /-- Every section killed by `π` comes from a *unique* section of `ℐ`, so the image of the
  inclusion is exactly the kernel and the inclusion is injective. -/
  exact_kernel (U : (SmallEtale B S hS X.1)ᵒᵖ) (a : A.obj.obj U)
      (ha : π.hom.app U a = 0) : ∃! x, ι U x = a
  /-- The action of `𝒜` on `ℐ` factors through `π`, which is what makes `ℐ` an `𝒪_X`-module. -/
  smul_lift (U : (SmallEtale B S hS X.1)ᵒᵖ) (a : A.obj.obj U) (x : I.val.obj U) :
    ι U (((I.val.obj U).smul (π.hom.app U a)).asHom.hom x) = a * ι U x
  /-- `ℐ` is an ideal of square zero in `𝒜`: condition (1) of the source. -/
  square_zero (U : (SmallEtale B S hS X.1)ᵒᵖ) (x y : I.val.obj U) :
    ι U x * ι U y = 0

/-- The locally surjective quotient map of a square-zero extension is a categorical
epimorphism. -/
theorem SquareZeroExtension.epi_π {X Y : AlgebraicSpaces B S hS} {f : X ⟶ Y}
    (E : SquareZeroExtension B S hS f) : Epi E.π :=
  let : Sheaf.IsLocallySurjective E.π := E.locallySurjective_π
  Sheaf.epi_of_isLocallySurjective E.π

/-- **The kernel of `π` over an object of the small étale site is exactly the image of `ι`
there.**  This is `mem_kernel` and `exact_kernel` read as a description of the ideal
`ker(𝒜(U) ⟶ 𝒪_X(U))`. -/
theorem SquareZeroExtension.mem_ker_iff {X Y : AlgebraicSpaces B S hS} {f : X ⟶ Y}
    (E : SquareZeroExtension B S hS f) (U : (SmallEtale B S hS X.1)ᵒᵖ)
    (a : E.A.obj.obj U) :
    a ∈ RingHom.ker (E.π.hom.app U).hom ↔ ∃ x, E.ι U x = a := by
  rw [RingHom.mem_ker]
  exact ⟨fun ha => (E.exact_kernel U a ha).exists, fun ⟨x, hx⟩ => hx ▸ E.mem_kernel U x⟩

/-- The inclusion of the sections of `ℐ` over an object of the small étale site into the kernel
ideal of `π` there, as a homomorphism of additive groups.  It is the field `ι` with its landing in
the kernel, which is the field `mem_kernel`, recorded in the target. -/
def SquareZeroExtension.idealToKer {X Y : AlgebraicSpaces B S hS} {f : X ⟶ Y}
    (E : SquareZeroExtension B S hS f) (U : (SmallEtale B S hS X.1)ᵒᵖ) :
    E.I.val.obj U →+ RingHom.ker (E.π.hom.app U).hom where
  toFun x := ⟨E.ι U x, E.mem_kernel U x⟩
  map_zero' := Subtype.ext (map_zero (E.ι U))
  map_add' x y := Subtype.ext (map_add (E.ι U) x y)

/-- The section of `𝒜` underlying the image of a section of `ℐ` in the kernel ideal of `π` is its
image under `ι`. -/
theorem SquareZeroExtension.coe_idealToKer {X Y : AlgebraicSpaces B S hS} {f : X ⟶ Y}
    (E : SquareZeroExtension B S hS f) (U : (SmallEtale B S hS X.1)ᵒᵖ) (x : E.I.val.obj U) :
    ((SquareZeroExtension.idealToKer B S hS E U x : E.A.obj.obj U)) = E.ι U x := rfl

/-- **The sections of `ℐ` over an object of the small étale site are exactly the kernel ideal of
`π` there.**  Injectivity is the uniqueness half of `exact_kernel` and surjectivity is its
existence half, in the form `AlgebraicGeometry.Space.SquareZeroExtension.mem_ker_iff`. -/
theorem SquareZeroExtension.bijective_idealToKer {X Y : AlgebraicSpaces B S hS} {f : X ⟶ Y}
    (E : SquareZeroExtension B S hS f) (U : (SmallEtale B S hS X.1)ᵒᵖ) :
    Function.Bijective (SquareZeroExtension.idealToKer B S hS E U) :=
  ⟨fun _ y hxy => (E.exact_kernel U (E.ι U y) (E.mem_kernel U y)).unique
      (congrArg Subtype.val hxy) rfl,
    fun ⟨a, ha⟩ => ((SquareZeroExtension.mem_ker_iff B S hS E U a).mp ha).imp
      fun _ hx => Subtype.ext hx⟩

/-- **Over every object of the small étale site the sections of `ℐ` are the kernel ideal of `π`**,
as additive groups.

This is the identification the base-change step of [Stacks Project, Tag 05ZT] is stated across:
the quasi-coherence of `ℐ` describes the sections of `ℐ`, whereas
`Algebra.Etale.of_ker_sq_eq_bot_of_isBaseChange` asks for a base change of the kernel ideals.  It
is an additive equivalence rather than a linear one because the two sides carry their scalars over
different rings — `ℐ(U)` over `𝒪_X(U)` and the kernel over `𝒜(U)` — and
`AlgebraicGeometry.Space.SquareZeroExtension.idealToKer_smul` is the compatibility that relates
them. -/
def SquareZeroExtension.idealAddEquivKer {X Y : AlgebraicSpaces B S hS} {f : X ⟶ Y}
    (E : SquareZeroExtension B S hS f) (U : (SmallEtale B S hS X.1)ᵒᵖ) :
    E.I.val.obj U ≃+ RingHom.ker (E.π.hom.app U).hom :=
  AddEquiv.ofBijective _ (SquareZeroExtension.bijective_idealToKer B S hS E U)

/-- **The identification of `ℐ` with the kernel ideal commutes with restriction.**  This is the
field `naturality`, read in the kernel. -/
theorem SquareZeroExtension.idealToKer_naturality {X Y : AlgebraicSpaces B S hS} {f : X ⟶ Y}
    (E : SquareZeroExtension B S hS f) {U V : (SmallEtale B S hS X.1)ᵒᵖ} (m : U ⟶ V)
    (x : E.I.val.obj U) :
    ((SquareZeroExtension.idealToKer B S hS E V (E.I.val.map m x) : E.A.obj.obj V)) =
      E.A.obj.map m (SquareZeroExtension.idealToKer B S hS E U x) :=
  E.naturality m x

/-- **The identification of `ℐ` with the kernel ideal carries the action of `𝒜` through `π`**: a
section `a` of `𝒜` acts on the kernel ideal by multiplication, and on `ℐ` through `π a`.  This is
the field `smul_lift`, read in the kernel. -/
theorem SquareZeroExtension.idealToKer_smul {X Y : AlgebraicSpaces B S hS} {f : X ⟶ Y}
    (E : SquareZeroExtension B S hS f) (U : (SmallEtale B S hS X.1)ᵒᵖ)
    (a : E.A.obj.obj U) (x : E.I.val.obj U) :
    SquareZeroExtension.idealToKer B S hS E U
        (((E.I.val.obj U).smul (E.π.hom.app U a)).asHom.hom x) =
      a • SquareZeroExtension.idealToKer B S hS E U x :=
  Subtype.ext (E.smul_lift U a x)

/-- **The ideal `ker(𝒜(U) ⟶ 𝒪_X(U))` has square zero**, for every object `U` of the small étale
site of `X`.  This is the ring-level form of condition (1) of [Stacks Project, Tag 05ZT], and it
is the hypothesis `hI` of `Algebra.Etale.of_ker_sq_eq_bot_of_isBaseChange` for the chart
construction: the sections of `𝒜` over a chart are a square-zero extension of the sections of
`𝒪_X` there. -/
theorem SquareZeroExtension.ker_pow_two_eq_bot {X Y : AlgebraicSpaces B S hS} {f : X ⟶ Y}
    (E : SquareZeroExtension B S hS f) (U : (SmallEtale B S hS X.1)ᵒᵖ) :
    RingHom.ker (E.π.hom.app U).hom ^ 2 = ⊥ := by
  rw [pow_two, eq_bot_iff]
  refine Ideal.mul_le.mpr fun a ha b hb => ?_
  obtain ⟨x, rfl⟩ := (SquareZeroExtension.mem_ker_iff B S hS E U a).mp ha
  obtain ⟨y, rfl⟩ := (SquareZeroExtension.mem_ker_iff B S hS E U b).mp hb
  exact Ideal.mem_bot.mpr (E.square_zero U x y)

/-- **The datum of [Stacks Project, Tag 05ZT] is inhabited.**  The trivial extension takes
`𝒜 = 𝒪_X` with `π` the identity and `ℐ = 0`; its realization is the identity thickening
`X ⊂ X`, which is of first order.

This is worth recording: a hypothesis structure with no inhabitant makes every statement
quantified over it vacuously true, so an existence theorem over `SquareZeroExtension` would
assert nothing.  It is not the interesting case — that is the one coming from a genuine
first-order thickening, whose fields the conormal-module file
`StacksFrontier/AlgebraicGeometry/Spaces/Thickenings/ConormalModuleInverseImageKernel.lean`
supplies. -/
theorem nonempty_squareZeroExtension {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) :
    Nonempty (SquareZeroExtension B S hS f) := by
  obtain ⟨Z, hZ⟩ := HasZeroObject.zero (C := Modules.{u, u} B S hS X.1 X.2)
  exact ⟨{
    A := (smallEtaleRingedTopos B S hS X).O
    π := 𝟙 _
    locallySurjective_π := inferInstance
    toBase := (smallEtaleRingedToposHom B S hS f).fSharpInverseImage
    toBase_π := Category.comp_id _
    I := Z
    quasicoherent := SheafOfModules.IsQuasicoherentOnSite.of_isZero hZ
    ι := fun _ => 0
    naturality := fun _ _ => (map_zero _).symm
    mem_kernel := fun _ _ => map_zero _
    exact_kernel := fun U a ha =>
      ⟨0, (ha : a = 0).symm, fun y _ => (Stacks.subsingleton_of_isZero hZ U).allEq y 0⟩
    smul_lift := fun _ a _ => (mul_zero a).symm
    square_zero := fun _ _ _ => mul_zero 0 }⟩

end AlgebraicGeometry.Space

end
