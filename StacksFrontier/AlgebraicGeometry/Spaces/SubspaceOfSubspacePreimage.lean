module

public import StacksFrontier.AlgebraicGeometry.Spaces.SubspaceOfSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.SummandSubspaceConormalTransport

/-!
# A closed subspace of a closed subspace is its own inverse image

Let `Z ⊆ Y` be closed subspaces of an algebraic space `W` over a scheme `S` contained in a big
fppf site `B`.  There are two ways to regard `Z` as a closed subspace of `Y`:

* the **image copy** of [Stacks Project, Tag 02YX]: the range of the inclusion
  `Z.toFunctor ⟶ Y.toFunctor`, which is a closed subspace of `Y` by
  `AlgebraicGeometry.Space.isClosedSubspace_of_le`;
* the **inverse image** of [Stacks Project, Tag 083Q]: the preimage of `Z` along the inclusion
  `j : Y ⟶ W`, which is a closed subspace of `Y` by
  `AlgebraicGeometry.Space.isClosedSubspace_preimage` and is what
  `AlgebraicGeometry.Space.preimageSubspace` names.

This file shows the two are **equal**, as subfunctors of `Y` and hence as closed subspaces of
`Y`, and draws the consequences for the conormal module of the pair and for the canonical map of
[Stacks Project, Tag 04CP] out of it.

The identification is needed because the right-hand map of the conormal complex of a chain
`Z ⊆ Y ⊆ W` is the canonical map of the fibre-product square of [Stacks Project, Tag 083Q], so
every statement reached through that complex — in particular
`AlgebraicGeometry.Space.isIso_conormalMap_of_definingIdealSheafSplitting` of
`StacksFrontier/AlgebraicGeometry/Spaces/SummandSubspaceConormalTransport.lean`, the space-level
form of the sentence "by construction `𝒞_{Z/Z'} = i^*𝒞_{X/X'}`" in the proof of
[Stacks Project, Tag 06D8] — speaks about `j⁻¹(Z)`, while a statement about the pair `Z ⊆ Y` as
such speaks about the image copy.

## Main results

* `CategoryTheory.Subfunctor.range_homOfLe_eq_preimage_ι`: for subfunctors `G ≤ G'` of a
  type-valued functor, the range of `G.toFunctor ⟶ G'.toFunctor` is the preimage of `G` along the
  inclusion `G'.toFunctor ⟶ F`.  This is the whole content; everything else transports along it.
* `AlgebraicGeometry.Space.closedSubspaceOfLe`: the image copy, packaged as a closed subspace of
  `Y`.
* `AlgebraicGeometry.Space.preimageSubspace_eq_closedSubspaceOfLe`: **the identification**, as an
  equality of closed subspaces of `Y`.
* `AlgebraicGeometry.Space.heq_conormalModule_closedSubspaceOfLe` and
  `AlgebraicGeometry.Space.heq_definingIdealSheaf_closedSubspaceOfLe`: the conormal module and
  the defining ideal sheaf of the two spellings are identified.
* `AlgebraicGeometry.Space.heq_preimageProjection_closedSubspaceOfLeProjection`: the projection
  `j⁻¹(Z) ⟶ Z` of the fibre-product square is identified with the inverse of the isomorphism of
  `Z` onto its image copy.
* `AlgebraicGeometry.Space.square_comp_of_eq_preimageSubspace` and
  `AlgebraicGeometry.Space.closedSubspaceOfLe_square_comp`: the commutativity datum of the
  composed square, at any spelling of `Z` inside `Y` and at the image copy respectively.
* `AlgebraicGeometry.Space.isIso_conormalMap_of_eq_preimageSubspace_of_splitting`: the conclusion
  of `AlgebraicGeometry.Space.isIso_conormalMap_of_definingIdealSheafSplitting`, restated at
  any closed subspace of `Y` equal to `j⁻¹(Z)` and any vertical morphism identified with the
  composite of the projection.
* `AlgebraicGeometry.Space.isIso_conormalMap_closedSubspaceOfLe_of_definingIdealSheafSplitting`:
  that conclusion at the image copy, which is the spelling in which the square reads
  `(Z ⊆ Y) → (X ⊆ X')`.

## Implementation notes

**Why the equality is not definitional.**  The range is a `Set.range` and the preimage is a
`Set.preimage`, so the two subfunctors have the same members for a reason — a section of `Y` over
`i` lies in the image of `Z.toFunctor` exactly when its image in `W` lies in `Z` — but not by
unfolding.  Since `AlgebraicGeometry.Space.IsClosedSubspace` is a `Prop` and
`AlgebraicGeometry.Space.ClosedSubspaces` a subtype over it, the subfunctor equality upgrades to
an equality of closed subspaces by `Subtype.ext`, and that equality is what all the transports
below use.

**The transports are stated with `HEq`, and the consumer-facing statement is parameterised.**
The conormal module of a closed subspace lives in a category that depends on that closed
subspace, so the two conormal modules have different (equal) types and `HEq` is the only equation
available; the same holds for the two projections.  Carrying `HEq`s into the conclusion of the
invertibility statement would make it useless, so
`AlgebraicGeometry.Space.isIso_conormalMap_of_eq_preimageSubspace_of_splitting` takes the closed
subspace and the vertical morphism as *variables* together with the equations identifying them,
and `subst` eliminates both before the proof begins.  This is the device of the bridge of
[Stacks Project, Tag 06CC], and it is what keeps `eqToHom` out of the statements.

**The image copy's projection is the inverse of an isomorphism.**  The image copy carries no
canonical morphism to `Z` written as a formula: recovering a section of `Z` from a section of the
image means inverting `CategoryTheory.Subfunctor.toRange`, which is an isomorphism because
`CategoryTheory.Subfunctor.homOfLe` is a monomorphism.  The identification of that inverse with
`AlgebraicGeometry.Space.preimageProjection` is read off from
`AlgebraicGeometry.Space.inv_toRange_comp`: the inverse followed by
`CategoryTheory.Subfunctor.homOfLe` is the inclusion of the range, and `homOfLe` does not change
the underlying section.

## What is not proved

* **No `@[stacks]` attribute is placed.**  [Stacks Project, Tag 02YX] is already registered on
  `AlgebraicGeometry.Space.isClosedSubspace_of_le` and [Stacks Project, Tag 083Q] on
  `AlgebraicGeometry.Space.isClosedSubspace_preimage`; the identification of the two
  constructions is an assertion of neither tag.
* **The splitting is still a hypothesis**, exactly as in
  `StacksFrontier/AlgebraicGeometry/Spaces/SummandSubspaceConormalTransport.lean`: nothing here
  produces one.

## References

* [Stacks Project, Tag 02YX](https://stacks.math.columbia.edu/tag/02YX)
* [Stacks Project, Tag 083Q](https://stacks.math.columbia.edu/tag/083Q)
* [Stacks Project, Tag 04CP](https://stacks.math.columbia.edu/tag/04CP)
* [Stacks Project, Tag 06CC](https://stacks.math.columbia.edu/tag/06CC)
* [Stacks Project, Tag 06D8](https://stacks.math.columbia.edu/tag/06D8)
-/

@[expose] public section

open CategoryTheory

universe w u

namespace CategoryTheory.Subfunctor

/-- **A subfunctor of a subfunctor is the inverse image of itself.**  For subfunctors `G ≤ G'` of
a type-valued functor `F`, the range of the inclusion `G.toFunctor ⟶ G'.toFunctor` is the
preimage of `G` along the inclusion `G'.toFunctor ⟶ F`.

A section of `G'` over `i` is in the range exactly when it is `⟨x, _⟩` for some `x` in `G.obj i`,
that is exactly when its underlying section of `F` lies in `G.obj i`. -/
theorem range_homOfLe_eq_preimage_ι {C : Type*} [Category C] {F : C ⥤ Type*}
    {G G' : Subfunctor F} (h : G ≤ G') :
    Subfunctor.range (Subfunctor.homOfLe h) = G.preimage G'.ι := by
  ext i y
  change y ∈ Set.range ((Subfunctor.homOfLe h).app i) ↔ (G'.ι.app i) y ∈ G.obj i
  refine ⟨?_, fun hy ↦ ⟨⟨y.1, hy⟩, Subtype.ext rfl⟩⟩
  rintro ⟨x, rfl⟩
  exact x.2

/-- **Morphisms out of equal subfunctors are identified.**  Two morphisms to a common target out
of two subfunctors of `F` which are equal, and which agree on every section of `F` belonging to
both, are equal up to that identification. -/
theorem heq_hom_of_eq {C : Type*} [Category C] {F H : C ⥤ Type w} {G₁ G₂ : Subfunctor F}
    (h : G₁ = G₂) (a : G₁.toFunctor ⟶ H) (b : G₂.toFunctor ⟶ H)
    (hab : ∀ (i : C) (x : F.obj i) (h₁ : x ∈ G₁.obj i) (h₂ : x ∈ G₂.obj i),
      a.app i ⟨x, h₁⟩ = b.app i ⟨x, h₂⟩) :
    HEq a b := by
  subst h
  refine heq_of_eq ?_
  ext i x
  exact hab i x.1 x.2 x.2

end CategoryTheory.Subfunctor

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {W : AlgebraicSpaces B S hS} (Y Z : ClosedSubspaces B S hS W.1)

/-! ### The image copy and the inverse image agree -/

/-- **The image copy of [Stacks Project, Tag 02YX].**  A closed subspace `Z` of `W` contained in
a closed subspace `Y` of `W`, regarded as a closed subspace of `Y` through the range of the
inclusion `Z.toFunctor ⟶ Y.toFunctor`. -/
noncomputable def closedSubspaceOfLe (hZY : Z.1 ≤ Y.1) :
    ClosedSubspaces B S hS (⟨Y.1.toFunctor, Y.2.1⟩ : AlgebraicSpaces B S hS).1 :=
  ⟨Subfunctor.range (Subfunctor.homOfLe hZY), isClosedSubspace_of_le B S hS Z.1 Y.1 Z.2 hZY⟩

/-- **The identification.**  For closed subspaces `Z ⊆ Y` of `W` the inverse image of `Z` along
the inclusion `j : Y ⟶ W` of [Stacks Project, Tag 083Q] is the image copy of
[Stacks Project, Tag 02YX], as closed subspaces of `Y`.

`AlgebraicGeometry.Space.IsClosedSubspace` is a `Prop`, so the equality of the two underlying
subfunctors — `CategoryTheory.Subfunctor.range_homOfLe_eq_preimage_ι` — is the whole content. -/
theorem preimageSubspace_eq_closedSubspaceOfLe (hZY : Z.1 ≤ Y.1) :
    preimageSubspace B S hS (subspaceInclusion B S hS W Y) Z =
      closedSubspaceOfLe B S hS Y Z hZY :=
  Subtype.ext (Subfunctor.range_homOfLe_eq_preimage_ι hZY).symm

/-! ### The identified data -/

/-- **The conormal modules of the two spellings are identified.**  `𝒞_{j⁻¹(Z)/Y}` and `𝒞_{Z/Y}`,
the latter read at the image copy of [Stacks Project, Tag 02YX], are the same module. -/
theorem heq_conormalModule_closedSubspaceOfLe (hZY : Z.1 ≤ Y.1) :
    HEq (conormalModule B S hS (⟨Y.1.toFunctor, Y.2.1⟩ : AlgebraicSpaces B S hS)
        (preimageSubspace B S hS (subspaceInclusion B S hS W Y) Z))
      (conormalModule B S hS (⟨Y.1.toFunctor, Y.2.1⟩ : AlgebraicSpaces B S hS)
        (closedSubspaceOfLe B S hS Y Z hZY)) := by
  rw [preimageSubspace_eq_closedSubspaceOfLe B S hS Y Z hZY]

/-- **The defining ideal sheaves of the two spellings are identified.** -/
theorem heq_definingIdealSheaf_closedSubspaceOfLe (hZY : Z.1 ≤ Y.1) :
    HEq (definingIdealSheaf B S hS (⟨Y.1.toFunctor, Y.2.1⟩ : AlgebraicSpaces B S hS)
        (preimageSubspace B S hS (subspaceInclusion B S hS W Y) Z))
      (definingIdealSheaf B S hS (⟨Y.1.toFunctor, Y.2.1⟩ : AlgebraicSpaces B S hS)
        (closedSubspaceOfLe B S hS Y Z hZY)) := by
  rw [preimageSubspace_eq_closedSubspaceOfLe B S hS Y Z hZY]

/-- **The projection of the image copy onto `Z`**, the inverse of the isomorphism of `Z` onto its
image inside `Y`.  `CategoryTheory.Subfunctor.homOfLe` is a monomorphism, so
`CategoryTheory.Subfunctor.toRange` of it is an isomorphism. -/
noncomputable def closedSubspaceOfLeProjection (hZY : Z.1 ≤ Y.1) :
    (⟨(closedSubspaceOfLe B S hS Y Z hZY).1.toFunctor,
        (closedSubspaceOfLe B S hS Y Z hZY).2.1⟩ : AlgebraicSpaces B S hS) ⟶
      (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) :=
  ObjectProperty.homMk (asIso (Subfunctor.toRange (Subfunctor.homOfLe hZY))).inv

/-- Morphisms of algebraic spaces out of equal subfunctors of a common presheaf are identified as
soon as the underlying morphisms of presheaves are. -/
private theorem heq_homMk_of_eq {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {G₁ G₂ : Subfunctor F}
    (h : G₁ = G₂) (h₁ : IsAlgebraicSpace B S hS G₁.toFunctor)
    (h₂ : IsAlgebraicSpace B S hS G₂.toFunctor) {T : AlgebraicSpaces B S hS}
    (a : G₁.toFunctor ⟶ T.1) (b : G₂.toFunctor ⟶ T.1) (hab : HEq a b) :
    HEq (ObjectProperty.homMk a : (⟨G₁.toFunctor, h₁⟩ : AlgebraicSpaces B S hS) ⟶ T)
      (ObjectProperty.homMk b : (⟨G₂.toFunctor, h₂⟩ : AlgebraicSpaces B S hS) ⟶ T) := by
  subst h
  obtain rfl := eq_of_heq hab
  exact HEq.rfl

/-- Morphisms of algebraic spaces identified with each other stay identified after composition
with a common morphism. -/
private theorem heq_comp_right {A₁ A₂ T T' : AlgebraicSpaces B S hS} (hA : A₁ = A₂)
    {a : A₁ ⟶ T} {b : A₂ ⟶ T} (hab : HEq a b) (m : T ⟶ T') : HEq (a ≫ m) (b ≫ m) := by
  subst hA
  obtain rfl := eq_of_heq hab
  exact HEq.rfl

/-- **The two projections onto `Z` are identified.**  The projection `j⁻¹(Z) ⟶ Z` of the
fibre-product square of [Stacks Project, Tag 083Q] and the projection
`AlgebraicGeometry.Space.closedSubspaceOfLeProjection` of the image copy both send a section of
`Y` lying in `Z` to that same section, read in `Z`.

For the image copy this is `AlgebraicGeometry.Space.inv_toRange_comp`: the inverse followed by
`CategoryTheory.Subfunctor.homOfLe` is the inclusion of the range, and
`CategoryTheory.Subfunctor.homOfLe` does not change the underlying section. -/
theorem heq_preimageProjection_closedSubspaceOfLeProjection (hZY : Z.1 ≤ Y.1) :
    HEq (preimageProjection B S hS (subspaceInclusion B S hS W Y) Z)
      (closedSubspaceOfLeProjection B S hS Y Z hZY) := by
  have hval : ∀ (i : (BigFppfOver B S hS)ᵒᵖ)
      (y : (Subfunctor.range (Subfunctor.homOfLe hZY)).toFunctor.obj i),
      (((asIso (Subfunctor.toRange (Subfunctor.homOfLe hZY))).inv.app i) y).1 = y.1.1 := by
    intro i y
    have h1 : (Subfunctor.homOfLe hZY).app i
          ((asIso (Subfunctor.toRange (Subfunctor.homOfLe hZY))).inv.app i y) = y.1 :=
      congrArg (fun k ↦ k y) (congr_app (inv_toRange_comp (Subfunctor.homOfLe hZY)) i)
    exact congrArg Subtype.val h1
  exact heq_homMk_of_eq B S hS (Subfunctor.range_homOfLe_eq_preimage_ι hZY).symm _ _
    (T := (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS))
    (Z.1.fromPreimage Y.1.ι)
    (asIso (Subfunctor.toRange (Subfunctor.homOfLe hZY))).inv
    (Subfunctor.heq_hom_of_eq (Subfunctor.range_homOfLe_eq_preimage_ι hZY).symm _ _
      fun i x h₁ h₂ ↦ (Subtype.ext (hval i ⟨x, h₂⟩)).symm)

/-! ### The transported invertibility statement -/

variable {X' : AlgebraicSpaces B S hS} (XX : ClosedSubspaces B S hS X'.1) (g : W ⟶ X')
    (f : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶
      (⟨XX.1.toFunctor, XX.2.1⟩ : AlgebraicSpaces B S hS))
    (hsq : subspaceInclusion B S hS W Z ≫ g = f ≫ subspaceInclusion B S hS X' XX)

/-- The projection of the inverse image and that of the image copy stay identified after
composition with the vertical morphism of the lower square. -/
private theorem heq_preimageProjection_comp (hZY : Z.1 ≤ Y.1) :
    HEq (preimageProjection B S hS (subspaceInclusion B S hS W Y) Z ≫ f)
      (closedSubspaceOfLeProjection B S hS Y Z hZY ≫ f) :=
  heq_comp_right B S hS
    (congrArg
      (fun A : ClosedSubspaces B S hS (⟨Y.1.toFunctor, Y.2.1⟩ : AlgebraicSpaces B S hS).1 ↦
        (⟨A.1.toFunctor, A.2.1⟩ : AlgebraicSpaces B S hS))
      (preimageSubspace_eq_closedSubspaceOfLe B S hS Y Z hZY))
    (heq_preimageProjection_closedSubspaceOfLeProjection B S hS Y Z hZY) f

include hsq in
/-- **The composed square, read at any spelling of `Z` inside `Y`.**
`AlgebraicGeometry.Space.preimageSubspace_square_comp` transported along an identification of the
inverse image `j⁻¹(Z)` with a closed subspace `Zc ⊆ Y` and of the composite projection with a
morphism `q`. -/
theorem square_comp_of_eq_preimageSubspace
    {Zc : ClosedSubspaces B S hS (⟨Y.1.toFunctor, Y.2.1⟩ : AlgebraicSpaces B S hS).1}
    (hZc : preimageSubspace B S hS (subspaceInclusion B S hS W Y) Z = Zc)
    {q : (⟨Zc.1.toFunctor, Zc.2.1⟩ : AlgebraicSpaces B S hS) ⟶
      (⟨XX.1.toFunctor, XX.2.1⟩ : AlgebraicSpaces B S hS)}
    (hq : HEq (preimageProjection B S hS (subspaceInclusion B S hS W Y) Z ≫ f) q) :
    subspaceInclusion B S hS (⟨Y.1.toFunctor, Y.2.1⟩ : AlgebraicSpaces B S hS) Zc ≫
        subspaceInclusion B S hS W Y ≫ g = q ≫ subspaceInclusion B S hS X' XX := by
  subst hZc
  obtain rfl := eq_of_heq hq
  exact preimageSubspace_square_comp B S hS Y Z XX g f hsq

include hsq in
/-- **The composed square at the pair `(Z ⊆ Y) → (X ⊆ X')`.**  The commutativity datum that the
canonical map of [Stacks Project, Tag 04CP] of that square takes, with `Z` read inside `Y`
through the image copy of [Stacks Project, Tag 02YX]. -/
theorem closedSubspaceOfLe_square_comp (hZY : Z.1 ≤ Y.1) :
    subspaceInclusion B S hS (⟨Y.1.toFunctor, Y.2.1⟩ : AlgebraicSpaces B S hS)
          (closedSubspaceOfLe B S hS Y Z hZY) ≫ subspaceInclusion B S hS W Y ≫ g =
      (closedSubspaceOfLeProjection B S hS Y Z hZY ≫ f) ≫ subspaceInclusion B S hS X' XX :=
  square_comp_of_eq_preimageSubspace B S hS Y Z XX g f hsq
    (preimageSubspace_eq_closedSubspaceOfLe B S hS Y Z hZY)
    (heq_preimageProjection_comp B S hS Y Z XX f hZY)

include hsq in
/-- **The summand identification, read at any spelling of `Z` inside `Y`.**  The conclusion of
`AlgebraicGeometry.Space.isIso_conormalMap_of_definingIdealSheafSplitting`, stated for a closed
subspace `Zc ⊆ Y` equal to the inverse image `j⁻¹(Z)` and a vertical morphism identified with the
composite of the projection `j⁻¹(Z) ⟶ Z` with `f`.

Both identifications are hypotheses in `subst`-able position, so the proof substitutes them away
and appeals to the theorem at the inverse-image spelling; the commutativity datum the canonical
map takes is `AlgebraicGeometry.Space.square_comp_of_eq_preimageSubspace`, transported the same
way, so nothing beyond the two identifications is assumed. -/
theorem isIso_conormalMap_of_eq_preimageSubspace_of_splitting (hZY : Z.1 ≤ Y.1)
    (γ : conormalModule B S hS W Z ⟶
      (modulePullback B S hS (subspaceInclusion B S hS W Z)).obj
        (definingIdealSheaf B S hS W Y).toSheafOfModules)
    (hz : conormalMap B S hS Z XX g f hsq ≫ γ = 0)
    (σ : (CategoryTheory.ShortComplex.mk (conormalMap B S hS Z XX g f hsq) γ hz).Splitting)
    (hs : σ.s =
      (show (modulePullback B S hS (subspaceInclusion B S hS W Z)).obj
            (definingIdealSheaf B S hS W Y).toSheafOfModules ⟶
          conormalModule B S hS W Z from
        (modulePullback B S hS (subspaceInclusion B S hS W Z)).map
          (definingIdealSheafHomOfLe B S hS Y Z hZY)))
    {Zc : ClosedSubspaces B S hS (⟨Y.1.toFunctor, Y.2.1⟩ : AlgebraicSpaces B S hS).1}
    (hZc : preimageSubspace B S hS (subspaceInclusion B S hS W Y) Z = Zc)
    {q : (⟨Zc.1.toFunctor, Zc.2.1⟩ : AlgebraicSpaces B S hS) ⟶
      (⟨XX.1.toFunctor, XX.2.1⟩ : AlgebraicSpaces B S hS)}
    (hq : HEq (preimageProjection B S hS (subspaceInclusion B S hS W Y) Z ≫ f) q) :
    IsIso (conormalMap B S hS Zc XX (subspaceInclusion B S hS W Y ≫ g) q
      (square_comp_of_eq_preimageSubspace B S hS Y Z XX g f hsq hZc hq)) := by
  subst hZc
  obtain rfl := eq_of_heq hq
  exact isIso_conormalMap_of_definingIdealSheafSplitting B S hS Y Z XX g f hsq hZY γ hz σ hs

include hsq in
/-- **The summand identification at the pair `(Z ⊆ Y) → (X ⊆ X')`.**  With `Z` regarded as a
closed subspace of `Y` through the image copy of [Stacks Project, Tag 02YX], and with the
vertical morphism the projection `AlgebraicGeometry.Space.closedSubspaceOfLeProjection` followed
by `f`, the canonical map of [Stacks Project, Tag 04CP] of the square is an isomorphism.

This is `AlgebraicGeometry.Space.isIso_conormalMap_of_definingIdealSheafSplitting` with the
inverse-image spelling of its lower-left corner traded for the image copy, through
`AlgebraicGeometry.Space.preimageSubspace_eq_closedSubspaceOfLe` and
`AlgebraicGeometry.Space.heq_preimageProjection_closedSubspaceOfLeProjection`.  It is the shape in
which the proof of [Stacks Project, Tag 06D8] states the identification
`𝒞_{Z/Z'} = i^*𝒞_{X/X'}`. -/
theorem isIso_conormalMap_closedSubspaceOfLe_of_definingIdealSheafSplitting (hZY : Z.1 ≤ Y.1)
    (γ : conormalModule B S hS W Z ⟶
      (modulePullback B S hS (subspaceInclusion B S hS W Z)).obj
        (definingIdealSheaf B S hS W Y).toSheafOfModules)
    (hz : conormalMap B S hS Z XX g f hsq ≫ γ = 0)
    (σ : (CategoryTheory.ShortComplex.mk (conormalMap B S hS Z XX g f hsq) γ hz).Splitting)
    (hs : σ.s =
      (show (modulePullback B S hS (subspaceInclusion B S hS W Z)).obj
            (definingIdealSheaf B S hS W Y).toSheafOfModules ⟶
          conormalModule B S hS W Z from
        (modulePullback B S hS (subspaceInclusion B S hS W Z)).map
          (definingIdealSheafHomOfLe B S hS Y Z hZY)))
    :
    IsIso (conormalMap B S hS (closedSubspaceOfLe B S hS Y Z hZY) XX
      (subspaceInclusion B S hS W Y ≫ g)
      (closedSubspaceOfLeProjection B S hS Y Z hZY ≫ f)
      (closedSubspaceOfLe_square_comp B S hS Y Z XX g f hsq hZY)) :=
  isIso_conormalMap_of_eq_preimageSubspace_of_splitting B S hS Y Z XX g f hsq hZY γ hz σ hs
    (preimageSubspace_eq_closedSubspaceOfLe B S hS Y Z hZY)
    (heq_preimageProjection_comp B S hS Y Z XX f hZY)

end AlgebraicGeometry.Space

end
