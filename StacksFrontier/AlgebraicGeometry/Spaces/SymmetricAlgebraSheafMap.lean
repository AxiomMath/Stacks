module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.UngradedRealizationFunctorial
public import StacksFrontier.AlgebraicGeometry.Spaces.NormalConeOfImmersion

/-!
# Functoriality of the symmetric algebra of a sheaf of modules on an algebraic space

`AlgebraicGeometry.Space.symmetricAlgebraSheaf` sends a sheaf of modules `ℱ` on the small étale
site of an algebraic space `W` to the sheaf of commutative `𝒪_W`-algebras `Sym(ℱ)`.  This file
makes that assignment a **functor**: a morphism `ℱ ⟶ 𝒢` of sheaves of modules induces a morphism
`Sym(ℱ) ⟶ Sym(𝒢)` of algebra sheaves, identities go to identities and composites to composites.

At the scheme level this is `AlgebraicGeometry.Scheme.Modules.symmetricAlgebraSheafMap`, in
`StacksFrontier.AlgebraicGeometry.Constructions.SymmetricAlgebraSheafFunctorial`; the module
documentation of
`StacksFrontier.AlgebraicGeometry.Spaces.Limits.IdealQuotientApproximationSystem` and the attribute
on Stacks 086Z in
`StacksFrontier.AlgebraicGeometry.Spaces.Limits.FiniteAlgebraSurjectiveSystem` both record its
absence at the algebraic-space level as one of the three carried inputs of Stacks 082A.  This
file supplies it.  It does **not** supply the other two halves of that input: quasi-coherence of
`Sym(ℱ)`, and the *ungraded* universal property that produces a map `Sym(ℱ) ⟶ 𝒜` of algebra
sheaves out of a map `ℱ ⟶ 𝒜` of modules.  The ungraded universal property is now available, in
`StacksFrontier.AlgebraicGeometry.Spaces.SymmetricAlgebraSheafUngradedLift`, as
`AlgebraicGeometry.Space.SymAlgSheaf.algebraLift`; quasi-coherence is reduced to its per-degree
statement in `StacksFrontier.AlgebraicGeometry.Spaces.SymmetricAlgebraSheafQuasicoherence`.  See the
implementation notes.

## Main definitions

* `AlgebraicGeometry.Space.commRingSheafMapOfMulComm`: a morphism of sheaves of rings with
  commuting sections, as a morphism of the sheaves of commutative rings they lift to, for a site
  whose morphisms live in a universe of their own.
* `AlgebraicGeometry.Space.ungradedSheafHom`: a unital homomorphism of sheaves of graded algebras,
  as a morphism of their ungraded realizations, for such a site.
* `AlgebraicGeometry.Space.gradedAlgebraSheafMap`: **the morphism of algebra sheaves on an
  algebraic space induced by a unital homomorphism of sheaves of graded algebras with commutative
  homogeneous multiplication.**
* `AlgebraicGeometry.Space.symmetricAlgebraUnitalHom`: **the homomorphism of graded algebras
  `Sym(ℱ) ⟶ Sym(𝒢)` induced by `ℱ ⟶ 𝒢`**, from the universal property of the symmetric algebra.
* `AlgebraicGeometry.Space.symmetricAlgebraSheafMap`: **the induced morphism of algebra sheaves
  `Sym(ℱ) ⟶ Sym(𝒢)`**, and
  `AlgebraicGeometry.Space.symmetricAlgebraSheafFunctor`: **`ℱ ↦ Sym(ℱ)` as a functor from sheaves
  of modules on `W` to algebra sheaves on `W`.**

## Main results

* `AlgebraicGeometry.Space.ungradedSheafHom_id` and `ungradedSheafHom_comp`,
  `AlgebraicGeometry.Space.gradedAlgebraSheafMap_id` and `gradedAlgebraSheafMap_comp`,
  `AlgebraicGeometry.Space.symmetricAlgebraUnitalHom_id` and `symmetricAlgebraUnitalHom_comp`,
  `AlgebraicGeometry.Space.symmetricAlgebraSheafMap_id` and `symmetricAlgebraSheafMap_comp`:
  **functoriality of each of the four layers.**
* `AlgebraicGeometry.Space.symmetricAlgebraGen_symmetricAlgebraUnitalHom`: the induced
  homomorphism restricted to the degree-one generators is the given morphism of modules, which is
  its defining property.
* `AlgebraicGeometry.Space.ringSheaf_symmetricAlgebraSheaf` and
  `AlgebraicGeometry.Space.right_symmetricAlgebraSheafMap`: on underlying sheaves of rings the
  algebra `Sym(ℱ)` is the ungraded realization of the graded `Sym(ℱ)` and the induced morphism is
  the induced morphism of ungraded realizations, so nothing is hidden by the commutative lift.

## Implementation notes

### Four universe-general restatements

The chain that performs this at the scheme level —
`Stacks.CommRingSheaf.presheafMap`, `Stacks.CommRingSheaf.sheafMap`,
`Stacks.CommRingSheaf.sheaf_hom_ext` and
`SheafOfModules.GradedAlgebra.ungradedSheafMap` with
`SheafOfModules.GradedAlgebra.UnitalHom.toPresheafGradedAlgebraHom` — is stated for a site
`C : Type u` with `Category.{u} C`.  The small étale site of an algebraic space is
`AlgebraicGeometry.Space.SmallEtale B S hS F : Type (u + 1)` with morphisms in `Type u`, so none
of them applies.  They are restated here with the two site universes independent, exactly as
`AlgebraicGeometry.Space.commRingSheafOfMulComm` and
`AlgebraicGeometry.Space.mulComm_ungradedSheaf` restate the object-level statements in
`StacksFrontier.AlgebraicGeometry.Spaces.NormalConeOfImmersion`.  The arguments are unchanged; what
is reused rather than repeated is everything that mentions no site
(`Stacks.CommRingSheaf.ofRingCatHom`) and everything already stated universe-generally
(`Stacks.GradedAlgebra.totalSheafMap` and its two functoriality laws,
`Stacks.GradedAlgebra.structureSheafHom_totalSheafMap`, and
`SheafOfModules.GradedAlgebra.IsUniversal.descComp` with `descComp_id` and `descComp_comp`).

### The induced homomorphism is the comparison of the universal property

`AlgebraicGeometry.Space.symmetricAlgebraUnitalHom` is not built by transporting a construction
of `Sym`: it is `SheafOfModules.GradedAlgebra.IsUniversal.descComp` applied to
`AlgebraicGeometry.Space.isSymmetricAlgebra_symmetricAlgebra`, the universal property that is
already proved for an algebraic space.  Its two functoriality laws are therefore uniqueness in
that universal property and nothing else, which is why no computation with sections of a
sheafification appears anywhere below: a section of `Sym(ℱ)` over a chart is only *locally* a
finite sum of homogeneous ones, so an elementwise route would need a local induction.

The side condition of the universal property travels along a morphism of modules for free:
`SheafOfModules.GradedAlgebra.pairwiseCommutes_comp` says that a degree-one generator with
pairwise commuting image still has one after composition.

### What is still missing from the symmetric algebra at the algebraic-space level

One thing, and this file does not supply it.

* **Quasi-coherence of `Sym(ℱ)`** for quasi-coherent `ℱ`.  It is a hypothesis at every use site
  in `StacksFrontier.AlgebraicGeometry.Spaces.NormalConeOfImmersion`, and the source is Stacks 01CK.
  It is now reduced to a per-degree statement in
  `StacksFrontier.AlgebraicGeometry.Spaces.SymmetricAlgebraSheafQuasicoherence`:
  `AlgebraicGeometry.Space.isQuasicoherent_symmetricAlgebraSheaf_of_pieces` concludes it from the
  quasi-coherence of the pieces `Symⁿ(ℱ)` in the degrees `n ≥ 0` and nothing else.  Of the three
  ingredients of that reduction, the identification of the underlying module of the ungraded
  realization with the coproduct of the homogeneous pieces is
  `AlgebraicGeometry.Space.symCoprodIsoUnderlyingModule` there, built as in
  `StacksFrontier.AlgebraicGeometry.Spaces.Chow.LaurentAlgebraQuasicoherence` from
  `Stacks.GradedAlgebra.directSumIsoUnderlyingModule` together with
  `Stacks.sheafifyDirectSumIso` of
  `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafifiedDirectSum`; the vanishing of the pieces
  in negative degrees is
  `AlgebraicGeometry.Space.isZero_symmetricAlgebra_piece_of_neg` there, the instantiation of
  `PresheafOfModules.isZero_symmetricAlgebraSheafify_piece` at this site; and the quasi-coherence
  of the coproduct `∐ₙ Symⁿ(ℱ)` is
  `AlgebraicGeometry.Space.isQuasicoherentOnSite_coprod_symmetricAlgebra_piece` there.  That last
  one needs no uniform covering family and no ringed space: on the small étale site of an
  algebraic space quasi-coherence is *equivalent* to the base change criterion, by
  `AlgebraicGeometry.Space.SmallEtale.isQuasicoherentOnSite_iff_isCartesianOnAffineCharts`, which
  is Stacks 03DX(2) and carries no hypothesis, and that criterion passes to a coproduct over an
  index type of any universe.  What remains owed is the per-degree hypothesis; the two
  obstructions to it are recorded in the implementation notes of that file.

The *ungraded universal property* used to be the second missing thing and is now supplied.  What
the universal property proved here gives is a homomorphism of *graded* algebras out of `Sym(ℱ)`,
determined by a degree-one generator with pairwise commuting image, and nothing below produces a
morphism of *algebra sheaves* `Sym(ℱ) ⟶ 𝒜` out of a morphism of modules `ℱ ⟶ 𝒜`:
`AlgebraicGeometry.Space.gradedAlgebraSheafMap` has a *graded* algebra on both sides.  That
morphism is `AlgebraicGeometry.Space.SymAlgSheaf.algebraLift`, in
`StacksFrontier.AlgebraicGeometry.Spaces.SymmetricAlgebraSheafUngradedLift`, the algebraic-space
analogue of `Stacks.SymAlgSheaf.algebraLift`.

## References

* [Stacks Project, Tag 01CJ](https://stacks.math.columbia.edu/tag/01CJ)
* [Stacks Project, Tag 01CK](https://stacks.math.columbia.edu/tag/01CK)
* [Stacks Project, Tag 082A](https://stacks.math.columbia.edu/tag/082A)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w

namespace AlgebraicGeometry.Space

/-! ### A morphism of sheaves of rings with commuting sections

A universe-general restatement of `Stacks.CommRingSheaf.presheafMap`, `sheafMap` and
`sheaf_hom_ext`; see the implementation notes. -/

section CommRingSheafMap

variable {C : Type u} [Category.{v} C]

/-- A morphism of presheaves of rings whose sections commute, as a morphism of the presheaves of
commutative rings they lift to, for a site whose morphisms live in a universe of their own.  The
carrier and the operations are unchanged, so this is the same data. -/
def commRingPresheafMapOfMulComm {P Q : Cᵒᵖ ⥤ RingCat.{w}}
    (hP : ∀ (W : Cᵒᵖ) (a b : P.obj W), a * b = b * a)
    (hQ : ∀ (W : Cᵒᵖ) (a b : Q.obj W), a * b = b * a) (f : P ⟶ Q) :
    commRingPresheafOfMulComm P hP ⟶ commRingPresheafOfMulComm Q hQ where
  app W := Stacks.CommRingSheaf.ofRingCatHom (hP W) (hQ W) (f.app W)
  naturality W W' g := by
    ext x
    exact congrArg (fun φ => RingCat.Hom.hom φ x) (f.naturality g)

/-- **A morphism of sheaves of rings whose sections commute, as a morphism of the sheaves of
commutative rings they lift to.** -/
def commRingSheafMapOfMulComm {J : GrothendieckTopology C} {T T' : Sheaf J RingCat.{w}}
    (hT : ∀ (W : Cᵒᵖ) (a b : T.obj.obj W), a * b = b * a)
    (hT' : ∀ (W : Cᵒᵖ) (a b : T'.obj.obj W), a * b = b * a) (f : T ⟶ T') :
    commRingSheafOfMulComm T hT ⟶ commRingSheafOfMulComm T' hT' :=
  ObjectProperty.homMk (commRingPresheafMapOfMulComm hT hT' f.hom)

/-- The lift of a morphism of sheaves of rings acts on every section as the original morphism. -/
@[simp]
theorem commRingSheafMapOfMulComm_app {J : GrothendieckTopology C} {T T' : Sheaf J RingCat.{w}}
    (hT : ∀ (W : Cᵒᵖ) (a b : T.obj.obj W), a * b = b * a)
    (hT' : ∀ (W : Cᵒᵖ) (a b : T'.obj.obj W), a * b = b * a) (f : T ⟶ T') (W : Cᵒᵖ)
    (x : T.obj.obj W) :
    ((commRingSheafMapOfMulComm hT hT' f).hom.app W).hom x = (f.hom.app W).hom x :=
  rfl

/-- Two morphisms of sheaves of commutative rings out of the lift of a sheaf of rings agree as
soon as they agree on every section: the lift keeps the carrier. -/
theorem commRingSheafOfMulComm_hom_ext {J : GrothendieckTopology C} {T : Sheaf J RingCat.{w}}
    (hT : ∀ (W : Cᵒᵖ) (a b : T.obj.obj W), a * b = b * a) {O : Sheaf J CommRingCat.{w}}
    {f g : commRingSheafOfMulComm T hT ⟶ O}
    (h : ∀ (W : Cᵒᵖ) (x : T.obj.obj W), (f.hom.app W).hom x = (g.hom.app W).hom x) : f = g :=
  Sheaf.hom_ext (NatTrans.ext (funext fun W => CommRingCat.hom_ext (RingHom.ext (h W))))

end CommRingSheafMap

/-! ### The ungraded realization of a homomorphism of sheaves of graded algebras

A universe-general restatement of
`SheafOfModules.GradedAlgebra.UnitalHom.toPresheafGradedAlgebraHom` and
`SheafOfModules.GradedAlgebra.ungradedSheafMap`; see the implementation notes. -/

section Ungraded

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}
    [HasSheafify J RingCat.{w}]
    {A A' A'' : SheafOfModules.GradedAlgebra.{w, w} R}

/-- A unital homomorphism of sheaves of graded algebras, read as one of the underlying graded
algebras of presheaves of modules.  The data are the same: only the sheaf conditions on the
pieces are forgotten. -/
def unitalHomPresheafHom (f : SheafOfModules.GradedAlgebra.UnitalHom A A') :
    Stacks.GradedAlgebra.UnitalHom A.toPresheafGradedAlgebra A'.toPresheafGradedAlgebra where
  app n := (f.app n).val
  map_mul i j U x y := f.map_mul i j U x y
  map_one U := f.map_one U

/-- **A unital homomorphism of sheaves of graded algebras, as a morphism of their ungraded
realizations as sheaves of rings.** -/
def ungradedSheafHom (f : SheafOfModules.GradedAlgebra.UnitalHom A A') :
    A.ungradedSheaf ⟶ A'.ungradedSheaf :=
  Stacks.GradedAlgebra.totalSheafMap J (unitalHomPresheafHom f)

/-- The morphism of ungraded realizations is compatible with the structure maps from the
structure sheaf, so it is a homomorphism of algebras and not merely of rings. -/
theorem ungradedStructureMap_ungradedSheafHom
    (f : SheafOfModules.GradedAlgebra.UnitalHom A A') :
    A.ungradedStructureMap ≫ ungradedSheafHom f = A'.ungradedStructureMap :=
  Sheaf.hom_ext
    (Stacks.GradedAlgebra.structureSheafHom_totalSheafMap J (unitalHomPresheafHom f))

/-- **The ungraded realization of the identity is the identity.** -/
theorem ungradedSheafHom_id :
    ungradedSheafHom (SheafOfModules.GradedAlgebra.UnitalHom.id A) = 𝟙 A.ungradedSheaf :=
  Stacks.GradedAlgebra.totalSheafMap_id J

/-- **The ungraded realization of a composite is the composite of the realizations.** -/
theorem ungradedSheafHom_comp (ψ : SheafOfModules.GradedAlgebra.UnitalHom A A')
    (χ : SheafOfModules.GradedAlgebra.UnitalHom A' A'') :
    ungradedSheafHom (ψ.comp χ) = ungradedSheafHom ψ ≫ ungradedSheafHom χ :=
  Stacks.GradedAlgebra.totalSheafMap_comp J (unitalHomPresheafHom ψ) (unitalHomPresheafHom χ)

end Ungraded

/-! ### A homomorphism of graded algebras as a morphism of algebra sheaves -/

section GradedAlgebraSheafMap

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (W : AlgebraicSpaces B S hS)

/-- Abbreviation for the graded commutativity hypothesis of
`AlgebraicGeometry.Space.gradedAlgebraSheaf`: the homogeneous multiplication commutes in every
pair of integer degrees. -/
abbrev GradedMulComm (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf B S hS W)) :
    Prop :=
  ∀ (i j : ℤ) (V : (SmallEtale B S hS W.1)ᵒᵖ) (a : (A.piece i).val.obj V)
    (b : (A.piece j).val.obj V), HEq ((A.mul i j).app V a b) ((A.mul j i).app V b a)

variable {A A' A'' : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf B S hS W)}

/-- **The morphism of algebra sheaves on an algebraic space induced by a unital homomorphism of
sheaves of graded algebras with commutative homogeneous multiplication.**  Its underlying
morphism of sheaves of rings is the morphism of ungraded realizations, and it commutes with the
two structure-algebra maps.

This is the algebraic-space analogue of `Stacks.RelativeSpec.gradedAlgebraSheafMap`. -/
def gradedAlgebraSheafMap (f : SheafOfModules.GradedAlgebra.UnitalHom A A')
    (hcA : GradedMulComm B S hS W A) (hcA' : GradedMulComm B S hS W A') :
    gradedAlgebraSheaf B S hS W A hcA ⟶ gradedAlgebraSheaf B S hS W A' hcA' where
  right := commRingSheafMapOfMulComm (mulComm_ungradedSheaf A hcA)
    (mulComm_ungradedSheaf A' hcA') (ungradedSheafHom f)
  comm V r := congrArg
    (fun k : structureRingSheaf B S hS W ⟶ A'.ungradedSheaf => (k.hom.app V).hom r)
    (ungradedStructureMap_ungradedSheafHom f)

/-- The underlying morphism of sheaves of commutative rings of `gradedAlgebraSheafMap` is the lift
of the morphism of their ungraded realizations. -/
@[simp]
theorem right_gradedAlgebraSheafMap (f : SheafOfModules.GradedAlgebra.UnitalHom A A')
    (hcA : GradedMulComm B S hS W A) (hcA' : GradedMulComm B S hS W A') :
    (gradedAlgebraSheafMap B S hS W f hcA hcA').right =
      commRingSheafMapOfMulComm (mulComm_ungradedSheaf A hcA)
        (mulComm_ungradedSheaf A' hcA') (ungradedSheafHom f) :=
  rfl

/-- **The morphism of algebra sheaves induced by the identity is the identity.** -/
theorem gradedAlgebraSheafMap_id (hcA : GradedMulComm B S hS W A) :
    gradedAlgebraSheafMap B S hS W (SheafOfModules.GradedAlgebra.UnitalHom.id A) hcA hcA =
      𝟙 (gradedAlgebraSheaf B S hS W A hcA) :=
  AlgebraSheaf.Hom.ext
    (commRingSheafOfMulComm_hom_ext (mulComm_ungradedSheaf A hcA) fun V x =>
      congrArg (fun k : A.ungradedSheaf ⟶ A.ungradedSheaf => (k.hom.app V).hom x)
        ungradedSheafHom_id)

/-- **The morphism of algebra sheaves induced by a composite is the composite of the induced
morphisms.** -/
theorem gradedAlgebraSheafMap_comp (ψ : SheafOfModules.GradedAlgebra.UnitalHom A A')
    (χ : SheafOfModules.GradedAlgebra.UnitalHom A' A'') (hcA : GradedMulComm B S hS W A)
    (hcA' : GradedMulComm B S hS W A') (hcA'' : GradedMulComm B S hS W A'') :
    gradedAlgebraSheafMap B S hS W (ψ.comp χ) hcA hcA'' =
      gradedAlgebraSheafMap B S hS W ψ hcA hcA' ≫
        gradedAlgebraSheafMap B S hS W χ hcA' hcA'' :=
  AlgebraSheaf.Hom.ext
    (commRingSheafOfMulComm_hom_ext (mulComm_ungradedSheaf A hcA) fun V x =>
      congrArg (fun k : A.ungradedSheaf ⟶ A''.ungradedSheaf => (k.hom.app V).hom x)
        (ungradedSheafHom_comp ψ χ))

end GradedAlgebraSheafMap

/-! ### Functoriality of the symmetric algebra -/

section SymmetricAlgebraFunctorial

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (W : AlgebraicSpaces B S hS)
    {F G H : SheafOfModules.{u} (structureRingSheaf B S hS W)}

/-- **The homomorphism of graded algebras `Sym(ℱ) ⟶ Sym(𝒢)` induced by a morphism `ℱ ⟶ 𝒢` of
sheaves of modules on an algebraic space.**

It is the comparison homomorphism of the universal property
`AlgebraicGeometry.Space.isSymmetricAlgebra_symmetricAlgebra`: the degree-one generator of
`Sym(𝒢)` composed with `φ` still has pairwise commuting image, so it factors uniquely through
the generator of `Sym(ℱ)`. -/
def symmetricAlgebraUnitalHom (φ : F ⟶ G) :
    SheafOfModules.GradedAlgebra.UnitalHom (symmetricAlgebra B S hS W F)
      (symmetricAlgebra B S hS W G) :=
  (isSymmetricAlgebra_symmetricAlgebra B S hS W F).descComp φ
    (symmetricAlgebraGen B S hS W G)
    (SheafOfModules.GradedAlgebra.pairwiseCommutes_comp φ
      (isSymmetricAlgebra_symmetricAlgebra B S hS W G).1)

/-- The induced homomorphism restricted to the degree-one generators is the given morphism of
modules.  This is its defining property. -/
theorem symmetricAlgebraGen_symmetricAlgebraUnitalHom (φ : F ⟶ G) :
    symmetricAlgebraGen B S hS W F ≫ (symmetricAlgebraUnitalHom B S hS W φ).app 1 =
      φ ≫ symmetricAlgebraGen B S hS W G :=
  (isSymmetricAlgebra_symmetricAlgebra B S hS W F).descComp_extends φ _ _

/-- **The homomorphism induced by the identity is the identity.** -/
theorem symmetricAlgebraUnitalHom_id :
    symmetricAlgebraUnitalHom B S hS W (𝟙 F) =
      SheafOfModules.GradedAlgebra.UnitalHom.id (symmetricAlgebra B S hS W F) :=
  (isSymmetricAlgebra_symmetricAlgebra B S hS W F).descComp_id _

/-- **The homomorphism induced by a composite is the composite of the induced
homomorphisms.** -/
theorem symmetricAlgebraUnitalHom_comp (φ : F ⟶ G) (ψ : G ⟶ H) :
    symmetricAlgebraUnitalHom B S hS W (φ ≫ ψ) =
      (symmetricAlgebraUnitalHom B S hS W φ).comp (symmetricAlgebraUnitalHom B S hS W ψ) :=
  (isSymmetricAlgebra_symmetricAlgebra B S hS W F).descComp_comp
    (isSymmetricAlgebra_symmetricAlgebra B S hS W G) φ ψ _ _ _ _

/-- **The morphism of algebra sheaves `Sym(ℱ) ⟶ Sym(𝒢)` induced by a morphism `ℱ ⟶ 𝒢` of sheaves
of modules on an algebraic space.**

This is the algebraic-space analogue of
`AlgebraicGeometry.Scheme.Modules.symmetricAlgebraSheafMap`, whose absence at this level was part
of the first of the three carried inputs of Stacks 082A. -/
def symmetricAlgebraSheafMap (φ : F ⟶ G) :
    symmetricAlgebraSheaf B S hS W F ⟶ symmetricAlgebraSheaf B S hS W G :=
  gradedAlgebraSheafMap B S hS W (symmetricAlgebraUnitalHom B S hS W φ)
    (symmetricAlgebra_mul_comm B S hS W F) (symmetricAlgebra_mul_comm B S hS W G)

/-- **The induced morphism of algebra sheaves is the identity on the identity.** -/
theorem symmetricAlgebraSheafMap_id :
    symmetricAlgebraSheafMap B S hS W (𝟙 F) = 𝟙 (symmetricAlgebraSheaf B S hS W F) := by
  rw [symmetricAlgebraSheafMap, symmetricAlgebraUnitalHom_id]
  exact gradedAlgebraSheafMap_id B S hS W (symmetricAlgebra_mul_comm B S hS W F)

/-- **The induced morphism of algebra sheaves carries a composite to the composite.** -/
theorem symmetricAlgebraSheafMap_comp (φ : F ⟶ G) (ψ : G ⟶ H) :
    symmetricAlgebraSheafMap B S hS W (φ ≫ ψ) =
      symmetricAlgebraSheafMap B S hS W φ ≫ symmetricAlgebraSheafMap B S hS W ψ := by
  rw [symmetricAlgebraSheafMap, symmetricAlgebraUnitalHom_comp]
  exact gradedAlgebraSheafMap_comp B S hS W (symmetricAlgebraUnitalHom B S hS W φ)
    (symmetricAlgebraUnitalHom B S hS W ψ) (symmetricAlgebra_mul_comm B S hS W F)
    (symmetricAlgebra_mul_comm B S hS W G) (symmetricAlgebra_mul_comm B S hS W H)

/-- **`ℱ ↦ Sym(ℱ)` as a functor from the sheaves of modules on an algebraic space to the sheaves
of commutative `𝒪_W`-algebras on it.**  Quasi-coherence is not asserted of any value; see the
implementation notes. -/
def symmetricAlgebraSheafFunctor :
    SheafOfModules.{u} (structureRingSheaf B S hS W) ⥤ AlgebraSheaf.{u, u} B S hS W.1 W.2 where
  obj F := symmetricAlgebraSheaf B S hS W F
  map φ := symmetricAlgebraSheafMap B S hS W φ
  map_id _ := symmetricAlgebraSheafMap_id B S hS W
  map_comp φ ψ := symmetricAlgebraSheafMap_comp B S hS W φ ψ

/-- `symmetricAlgebraSheafFunctor` sends a sheaf of modules `F` to `symmetricAlgebraSheaf F`. -/
@[simp]
theorem symmetricAlgebraSheafFunctor_obj (F : SheafOfModules.{u} (structureRingSheaf B S hS W)) :
    (symmetricAlgebraSheafFunctor B S hS W).obj F = symmetricAlgebraSheaf B S hS W F :=
  rfl

/-- `symmetricAlgebraSheafFunctor` sends a morphism `φ` to `symmetricAlgebraSheafMap φ`. -/
@[simp]
theorem symmetricAlgebraSheafFunctor_map (φ : F ⟶ G) :
    (symmetricAlgebraSheafFunctor B S hS W).map φ = symmetricAlgebraSheafMap B S hS W φ :=
  rfl

/-- On underlying sheaves of rings the algebra sheaf `Sym(ℱ)` is the ungraded realization of the
graded `Sym(ℱ)`: the commutative lift keeps the carrier. -/
theorem ringSheaf_symmetricAlgebraSheaf (F : SheafOfModules.{u} (structureRingSheaf B S hS W)) :
    AlgebraSheaf.ringSheaf (symmetricAlgebraSheaf B S hS W F) =
      commRingSheafOfMulComm (symmetricAlgebra B S hS W F).ungradedSheaf
        (mulComm_ungradedSheaf (symmetricAlgebra B S hS W F)
          (symmetricAlgebra_mul_comm B S hS W F)) :=
  rfl

/-- On underlying sheaves of rings the induced morphism is the morphism of ungraded
realizations. -/
theorem right_symmetricAlgebraSheafMap (φ : F ⟶ G) (V : (SmallEtale B S hS W.1)ᵒᵖ)
    (x : (symmetricAlgebra B S hS W F).ungradedSheaf.obj.obj V) :
    (((symmetricAlgebraSheafMap B S hS W φ).right.hom.app V).hom x) =
      ((ungradedSheafHom (symmetricAlgebraUnitalHom B S hS W φ)).hom.app V).hom x :=
  rfl

end SymmetricAlgebraFunctorial

end AlgebraicGeometry.Space

end
