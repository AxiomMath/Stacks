module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.PicardFunctor

/-!
# The Picard stack rigidified by a section (Stacks 0D2B)

Let `f : X ⟶ B` be a morphism of algebraic spaces over a scheme `S` of a big fppf site, the
standing data of Stacks 0D25, and let `σ : B ⟶ X` be a section of `f`.  Every test scheme `T`
over the base inherits a section `σ_T : T ⟶ X_T` of the projection `f_T : X_T ⟶ T` of the base
change, and `Picardstack_{X/B, σ}` is `Picardstack_{X/B}` rigidified by a trivialisation along
`σ_T`: an object over `(T, h)` is a pair `(L, α)` of an invertible `𝒪_{X_T}`-module `L` and an
isomorphism `α : σ_T^*L ≅ 𝒪_T`.

Stacks 0D2B describes the isomorphism classes of that stack over `T` as the disjoint union, over
the morphisms `h : T ⟶ B`, of the kernel of `σ_T^* : Pic(X_T) ⟶ Pic(T)`.  This file constructs
`σ_T` and the map `σ_T^*` on Picard classes, and proves the half of that description which does
not need the group of global units of a structure sheaf: **an invertible `𝒪_{X_T}`-module carries
a trivialisation along `σ_T` exactly when its Picard class lies in the kernel of `σ_T^*`**, so
that the classes of the invertible modules underlying the objects of `Picardstack_{X/B, σ}` over
`(T, h)` are exactly the elements of that kernel.

## Main definitions

* `AlgebraicGeometry.Space.structureModule`: the structure sheaf of an algebraic space, regarded
  as an invertible module over itself — the module a trivialisation compares with.
* `AlgebraicGeometry.Space.PicardSituation.baseChangeSection`: the section
  `σ_T : T ⟶ X_T` of the base change induced by a section `σ : B ⟶ X`.
* `AlgebraicGeometry.Space.PicardSituation.sectionPicardPullback`: **the map
  `σ_T^* : Pic(X_T) ⟶ Pic(T)` of Stacks 0D2B**, pullback of Picard classes along `σ_T`.

## Main results

* `AlgebraicGeometry.Space.picardClass_eq_zero_iff`: a Picard class vanishes exactly when the
  invertible module is isomorphic to the structure sheaf.
* `AlgebraicGeometry.Space.PicardSituation.baseChangeSection_comp_inclusion` and
  `AlgebraicGeometry.Space.PicardSituation.baseChangeSection_comp_projection`: `σ_T` is a
  section of `f_T`, and composing it with `X_T ⟶ X` gives `h ≫ σ`.
* `AlgebraicGeometry.Space.PicardSituation.sectionPicardPullback_basePicardPullback`: `σ_T^*`
  retracts `f_T^*`, so the kernel of `σ_T^*` is a complement of the image of `Pic(T)` in
  `Pic(X_T)`.
* `AlgebraicGeometry.Space.PicardSituation.sectionPicardPullback_picardClass_eq_zero_iff` and
  `AlgebraicGeometry.Space.PicardSituation.sectionPicardPullback_eq_zero_iff`: **the half of
  Stacks 0D2B recorded here** — the Picard class of an invertible `𝒪_{X_T}`-module lies in the
  kernel of `σ_T^*` exactly when the module admits a trivialisation along `σ_T`, and every
  element of that kernel is the class of such a module.

## Implementation notes

**What of Stacks 0D2B is here, and what is not.**  Stacks 0D2B has two conclusions: that
`Picardstack_{X/B, σ}` is fibred in setoids, and that its isomorphism classes over `T` are
`⨿_h ker(σ_T^*)`.  What is proved here is the identification of the *index set* of that disjoint
union with the section-trivialisable Picard classes: for a fixed test scheme `(T, h)` over the
base, the classes of the invertible `𝒪_{X_T}`-modules that admit a trivialisation along `σ_T` —
that is, of the modules underlying an object of `Picardstack_{X/B, σ}` over `(T, h)` — are
exactly the elements of `ker(σ_T^*)`.  The disjoint union over `h` is then the sum over the
objects `(T, h)` of `AlgebraicGeometry.Space.PicardSituation.SchemesOver`, which is how a test
scheme over the base is presented throughout this development.

The two remaining halves both need the *global units of the structure sheaf of an algebraic
space*, which this development does not carry — see the implementation notes of
`StacksFrontier/AlgebraicGeometry/Quot/PicardFunctor.lean`, which record that there is no sheaf of
units and no group of global units of the structure sheaf of an algebraic space here, so the
corresponding argument of Stacks 0D27 cannot be stated at all.  Concretely:

* *Fibred in setoids.*  The source's argument is that an automorphism of `(T, h, L, α)` is
  multiplication by an invertible global section `u` of `𝒪_{X_T}` with `σ_T^*u = 1`, and that
  `𝒪_T ⟶ f_{T, *}𝒪_{X_T}` being an isomorphism forces `u = 1`.  Writing it down needs the
  identification of the vertical endomorphisms of an invertible module with the global sections
  of the structure sheaf, which is the missing input.
* *Injectivity of the description.*  That two objects with the same underlying class are
  isomorphic needs "any two choices of `α` differ by a global unit on `T`", the same input.

**The hypothesis of Stacks 0D2B is not needed for what is proved.**  Stacks 0D2B assumes
`𝒪_T ⟶ f_{T, *}𝒪_{X_T}` to be an isomorphism for every `T`, which is
`AlgebraicGeometry.Space.PicardSituation.StructureSheafMapIso`.  The equivalence proved here
holds without it: a trivialisation of `σ_T^*L` by the structure sheaf is exactly the vanishing
of its Picard class, by the definition of the Picard group as isomorphism classes.  The
hypothesis is what the *other* two halves need, and it is already available in the library for
the statement that does.

**What the pullback of Picard classes needs.**  As everywhere in
`StacksFrontier/AlgebraicGeometry/Quot/PicardFunctor.lean`, it needs the inverse image of an
invertible module to be invertible, which that file proves as
`AlgebraicGeometry.Space.modulePullbackInvertible`, so `σ_T^*` takes no such argument; its
identity law needs in addition `AlgebraicGeometry.Space.ModulePushforwardCoherence`, the
pseudofunctoriality of Stacks 03LU, which is carried as a hypothesis in the shape that file
fixes.

**Why the section of the base change needs no new geometry.**  `X_T` is the fibre product
`X ×_B T` and `σ_T` is the morphism it induces from `(h ≫ σ, 𝟙_T)`, which is legitimate because
`σ ≫ f = 𝟙_B`.  Its two defining projections are the two lemmas above, and
`AlgebraicGeometry.Space.baseChange_hom_ext` makes it the only such morphism.

## References

* [Stacks Project, Tag 0D2B](https://stacks.math.columbia.edu/tag/0D2B)
* [Stacks Project, Tag 0D25](https://stacks.math.columbia.edu/tag/0D25)
* [Stacks Project, Tag 0D27](https://stacks.math.columbia.edu/tag/0D27)
* [Stacks Project, Tag 01CX](https://stacks.math.columbia.edu/tag/01CX)
* [Stacks Project, Tag 0B8P](https://stacks.math.columbia.edu/tag/0B8P)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### The trivial Picard class -/

/-- The structure sheaf of an algebraic space `Z`, regarded as an `𝒪_Z`-module.  It is the
neutral element for the tensor product, so its Picard class is the zero of `Pic(Z)`, and a
trivialisation of an invertible module is an isomorphism with it. -/
abbrev structureModule (Z : AlgebraicSpaces B S hS) : Modules.{u, u} B S hS Z.1 Z.2 :=
  SheafOfModules.unit _

/-- The structure sheaf is an invertible module. -/
theorem isInvertibleModule_structureModule (Z : AlgebraicSpaces B S hS) :
    IsInvertibleModule Z (structureModule Z) :=
  Stacks.SheafOfModules.isInvertible_unit _ _

/-- The class of the structure sheaf is the zero of `Pic(Z)`: the group law of `Pic(Z)` is the
tensor product, whose neutral element is the structure sheaf. -/
@[simp]
theorem picardClass_structureModule (Z : AlgebraicSpaces B S hS) :
    picardClass Z (structureModule Z) (isInvertibleModule_structureModule Z) = 0 :=
  rfl

/-- **A Picard class vanishes exactly when the module is trivial.**  The class of an invertible
`𝒪_Z`-module is the zero of `Pic(Z)` if and only if the module is isomorphic to the structure
sheaf. -/
theorem picardClass_eq_zero_iff (Z : AlgebraicSpaces B S hS)
    (L : Modules.{u, u} B S hS Z.1 Z.2) (hL : IsInvertibleModule Z L) :
    picardClass Z L hL = 0 ↔ Nonempty (L ≅ structureModule Z) := by
  rw [← picardClass_structureModule Z]
  exact picardClass_eq_picardClass_iff Z L (structureModule Z) hL
    (isInvertibleModule_structureModule Z)

namespace PicardSituation

variable {s : PicardSituation B S hS}

/-! ### The section of a base change -/

/-- **The section `σ_T : T ⟶ X_T` induced by a section `σ : B ⟶ X` of `f`.**  The base change
`X_T` is the fibre product `X ×_B T`, and `σ_T` is the morphism it induces from the pair
`(h ≫ σ, 𝟙_T)`; the two legs agree over the base because `σ ≫ f = 𝟙_B`. -/
def baseChangeSection (σ : s.base ⟶ s.X) (hσ : σ ≫ s.f = 𝟙 s.base) (T : s.SchemesOver) :
    s.baseSpaceAt T ⟶ s.baseChange T :=
  (AlgebraicSpaces.isPullback_fiberProduct B S hS s.f T.hom).lift (T.hom ≫ σ) (𝟙 _)
    (by rw [Category.assoc, hσ, Category.comp_id, Category.id_comp])

/-- Composing `σ_T` with the projection `X_T ⟶ X` gives `h ≫ σ`. -/
@[reassoc (attr := simp)]
theorem baseChangeSection_comp_projection (σ : s.base ⟶ s.X) (hσ : σ ≫ s.f = 𝟙 s.base)
    (T : s.SchemesOver) :
    baseChangeSection σ hσ T ≫ baseChangeProjection s.f T = T.hom ≫ σ :=
  (AlgebraicSpaces.isPullback_fiberProduct B S hS s.f T.hom).lift_fst _ _ _

/-- **`σ_T` is a section of the projection `f_T : X_T ⟶ T` of the base change.** -/
@[reassoc (attr := simp)]
theorem baseChangeSection_comp_inclusion (σ : s.base ⟶ s.X) (hσ : σ ≫ s.f = 𝟙 s.base)
    (T : s.SchemesOver) :
    baseChangeSection σ hσ T ≫ baseChangeInclusion s.f T = 𝟙 (s.baseSpaceAt T) :=
  (AlgebraicSpaces.isPullback_fiberProduct B S hS s.f T.hom).lift_snd _ _ _

/-- `σ_T` is the only morphism `T ⟶ X_T` with those two projections. -/
theorem eq_baseChangeSection (σ : s.base ⟶ s.X) (hσ : σ ≫ s.f = 𝟙 s.base) (T : s.SchemesOver)
    {k : s.baseSpaceAt T ⟶ s.baseChange T}
    (h₁ : k ≫ baseChangeProjection s.f T = T.hom ≫ σ)
    (h₂ : k ≫ baseChangeInclusion s.f T = 𝟙 (s.baseSpaceAt T)) :
    k = baseChangeSection σ hσ T :=
  baseChange_hom_ext s.f
    (h₁.trans (baseChangeSection_comp_projection σ hσ T).symm)
    (h₂.trans (baseChangeSection_comp_inclusion σ hσ T).symm)

/-! ### The map `σ_T^*` on Picard classes -/

/-- **The map `σ_T^* : Pic(X_T) ⟶ Pic(T)` of Stacks 0D2B**: pullback of Picard classes along the
section `σ_T` of the base change. -/
def sectionPicardPullback (σ : s.base ⟶ s.X) (hσ : σ ≫ s.f = 𝟙 s.base) (T : s.SchemesOver)
    (x : s.picardAt T) : s.basePicardAt T :=
  picardPullback (baseChangeSection σ hσ T) x

/-- `σ_T^*` sends the class of `L` to the class of its inverse image along `σ_T`. -/
theorem sectionPicardPullback_picardClass (σ : s.base ⟶ s.X) (hσ : σ ≫ s.f = 𝟙 s.base)
    (T : s.SchemesOver) (L : Modules.{u, u} B S hS (s.baseChange T).1 (s.baseChange T).2)
    (hL : IsInvertibleModule (s.baseChange T) L) :
    sectionPicardPullback σ hσ T (picardClass _ L hL) =
      picardClass _ ((modulePullback B S hS (baseChangeSection σ hσ T)).obj L)
        (modulePullbackInvertible _ L hL) :=
  picardPullback_picardClass _ L hL

/-- **`σ_T^*` retracts `f_T^*`.**  Pulling a Picard class on `T` back to `X_T` along the
projection of the base change and then restricting it along the section returns the class, so
the kernel of `σ_T^*` is a complement of the image of `Pic(T)` in `Pic(X_T)`. -/
theorem sectionPicardPullback_basePicardPullback (hc : ModulePushforwardCoherence B S hS)
    (σ : s.base ⟶ s.X) (hσ : σ ≫ s.f = 𝟙 s.base) (T : s.SchemesOver)
    (x : s.basePicardAt T) :
    sectionPicardPullback σ hσ T (s.basePicardPullback T x) = x := by
  change picardPullback (baseChangeSection σ hσ T)
    (picardPullback (baseChangeInclusion s.f T) x) = x
  rw [← picardPullback_comp, baseChangeSection_comp_inclusion, picardPullback_id hc]

/-! ### The kernel of `σ_T^*` and the trivialisations along `σ_T` -/

/-- **The class of an invertible module lies in the kernel of `σ_T^*` exactly when the module
admits a trivialisation along `σ_T`.**

A trivialisation of `L` along `σ_T` is an isomorphism `σ_T^*L ≅ 𝒪_T`, which is the datum `α`
that rigidifies an object `(T, h, L)` of `Picardstack_{X/B}` into an object of
`Picardstack_{X/B, σ}`.  By the definition of `Pic(T)` as isomorphism classes, having one is the
same as the vanishing of the class of `σ_T^*L`, that is of `σ_T^*` applied to the class of `L`.

This holds with no hypothesis on `𝒪_T ⟶ f_{T, *}𝒪_{X_T}`; see the implementation notes. -/
theorem sectionPicardPullback_picardClass_eq_zero_iff (σ : s.base ⟶ s.X)
    (hσ : σ ≫ s.f = 𝟙 s.base) (T : s.SchemesOver)
    (L : Modules.{u, u} B S hS (s.baseChange T).1 (s.baseChange T).2)
    (hL : IsInvertibleModule (s.baseChange T) L) :
    sectionPicardPullback σ hσ T (picardClass _ L hL) = 0 ↔
      Nonempty ((modulePullback B S hS (baseChangeSection σ hσ T)).obj L ≅
        structureModule (s.baseSpaceAt T)) := by
  rw [sectionPicardPullback_picardClass σ hσ T L hL]
  exact picardClass_eq_zero_iff _ _ _

/-- **The elements of the kernel of `σ_T^*` are exactly the Picard classes of the invertible
`𝒪_{X_T}`-modules carrying a trivialisation along `σ_T`.**

This is the identification of the index set of the disjoint union of Stacks 0D2B: for a test
scheme `(T, h)` over the base, the invertible modules underlying the objects of
`Picardstack_{X/B, σ}` over `(T, h)` — the modules `L` for which a rigidifying isomorphism
`α : σ_T^*L ≅ 𝒪_T` exists — are precisely those whose class is killed by
`σ_T^* : Pic(X_T) ⟶ Pic(T)`.  Stacks 0D2B's description of the isomorphism classes of
`Picardstack_{X/B, σ}` over `T` as `⨿_h ker(σ_T^*)` is the sum of this statement over the
objects `(T, h)` of `AlgebraicGeometry.Space.PicardSituation.SchemesOver`.

**The two other halves of Stacks 0D2B are not proved**: that the stack is fibred in setoids, and
that two objects with the same underlying class are isomorphic.  Both need the global units of
the structure sheaf of an algebraic space, which this development does not carry; see the
implementation notes of the file. -/
@[stacks 0D2B "the index set of the disjoint union: the kernel of σ_T^* on Pic(X_T) is exactly \
the set of classes of the invertible modules admitting a trivialisation along σ_T, i.e. of those \
underlying an object of Picardstack_{X/B, σ}. The fibred-in-setoids conclusion and the \
injectivity of the description are NOT proved: both need the global units of the structure sheaf \
of an algebraic space, which this development does not carry"]
theorem sectionPicardPullback_eq_zero_iff (σ : s.base ⟶ s.X) (hσ : σ ≫ s.f = 𝟙 s.base)
    (T : s.SchemesOver) (x : s.picardAt T) :
    sectionPicardPullback σ hσ T x = 0 ↔
      ∃ (L : Modules.{u, u} B S hS (s.baseChange T).1 (s.baseChange T).2)
        (hL : IsInvertibleModule (s.baseChange T) L), picardClass _ L hL = x ∧
          Nonempty ((modulePullback B S hS (baseChangeSection σ hσ T)).obj L ≅
            structureModule (s.baseSpaceAt T)) := by
  constructor
  · intro hx
    obtain ⟨L, hL, rfl⟩ := exists_picardClass (s.baseChange T) x
    exact ⟨L, hL, rfl, (sectionPicardPullback_picardClass_eq_zero_iff σ hσ T L hL).1 hx⟩
  · rintro ⟨L, hL, rfl, hα⟩
    exact (sectionPicardPullback_picardClass_eq_zero_iff σ hσ T L hL).2 hα

end PicardSituation

end AlgebraicGeometry.Space

end
