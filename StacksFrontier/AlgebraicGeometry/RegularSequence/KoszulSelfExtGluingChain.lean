module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraDescentTransport
public import StacksFrontier.AlgebraicGeometry.RegularSequence.KoszulIdealOpenSubspace
public import StacksFrontier.AlgebraicGeometry.RegularSequence.KoszulSelfExtAlgebraDescent
public import StacksFrontier.AlgebraicGeometry.RegularSequence.KoszulSelfExtGluingSteps

/-!
# The descended chain of presentations over an open

The three Koszul-specific links of the chain of presentations of the self-Ext algebra over an
open `U` are proved in
`StacksFrontier.AlgebraicGeometry.RegularSequence.KoszulSelfExtGluingSteps`, each as a statement
about the composition-product algebra **over the structure sheaf of `X|_U`**. The comparison map
of [Stacks, Tag 0BQY] is built in the algebra **descended** along `O_X ↠ O_X/I`, and the local
statements that feed the chain are descended too. This file runs the two links that are not
already descended through the descent, and chains all three.

## Main results

* `SheafOfModules.GradedAlgebra.isExteriorAlgebra_id_descend_of_ringIso`: the identity-generator
  form of the transport along an identification of the quotient the algebra is descended along.
* `SheafOfModules.GradedAlgebra.IsExteriorAlgebra.genOver_id`: the restricted identity generator,
  from the identity generator of the restriction — the shape the gluing primitive consumes.
* `Stacks.AlgebraicGeometry.RegularIdealSheaf.smul_openSubspaceRestrictComplex_piece_eq_zero`
  and `smul_openSubspaceGradedAlgebra_piece_eq_zero`: the annihilation hypothesis of each
  algebra of the chain, transported from the one of the Koszul algebra.
* `RegularIdealSheaf.isExteriorAlgebra_id_descend_openSubspaceRestrictComplex`: the
  descended third link.
* `RegularIdealSheaf.isExteriorAlgebra_id_descend_openSubspaceGradedAlgebra`: the
  descended first link.
* `Stacks.AlgebraicGeometry.RegularIdealSheaf.isExteriorAlgebra_id_over_descend_koszulChain`:
  **the whole chain**, from the descended Koszul conclusion over `U` to the restriction, to the
  slice site at `U`, of the globally descended composition-product algebra of a K-injective
  resolution.
* `Stacks.AlgebraicGeometry.RegularIdealSheaf.isExteriorAlgebra_id_over_descend_koszul` and
  `isExteriorAlgebra_genOver_descend_koszul`: **the hypothesis `hBV` of the gluing of
  [Stacks, Tag 0BQY] at one member of the cover**, with the local conclusion supplied by
  `Stacks.RegularSequence.KoszulChainData.isExteriorAlgebra_extSelfAlgebra`, in the two shapes a
  consumer uses.

## Implementation notes

**One annihilation hypothesis serves for the whole chain.** Each link is a unital homomorphism
of sheaves of graded algebras which is an isomorphism in every degree, and
`SheafOfModules.GradedAlgebra.UnitalHom.smul_piece_eq_zero_of_ker` carries an annihilation
hypothesis across such a homomorphism, so the hypothesis proved for the Koszul algebra —
`Stacks.RegularSequence.KoszulChainData.smul_homologyPiece_eq_zero` — is available for every
algebra of the chain. The descent of each link is then
`SheafOfModules.GradedAlgebra.isExteriorAlgebra_id_descend_of_degreewiseIso`.

**The direction is the one the gluing consumes.** The universal property is known for the
descended Koszul algebra, which is the far end of the chain from the algebra the comparison map
is built in, so every link is traversed backwards; the two directions differ only by
`SheafOfModules.GradedAlgebra.UnitalHom.inverse`.

**What this is used for.** The conclusion below is `hBV` at *one* member of a cover, and
`SheafOfModules.GradedAlgebra.IsExteriorAlgebra.isIso_desc_app_of_coversTop` consumes it at every
member of a family covering the final object; that instantiation is
`Stacks.AlgebraicGeometry.RegularIdealSheaf.isIso_desc_app_koszulRegular` of
`StacksFrontier.AlgebraicGeometry.RegularSequence.KoszulSelfExtGlobal`, and the global statement of
[Stacks, Tag 0BQY] it yields is
`Stacks.AlgebraicGeometry.RegularIdealSheaf.isIso_desc_app_isKoszulRegularIdealSheaf` of
`StacksFrontier.AlgebraicGeometry.RegularSequence.KoszulSelfExtKoszulRegular`.

**The covering family, and no degenerate case for it.** The hypothesis
of [Stacks, Tag 063D] part (2) supplies an open with a generating Koszul-exact sequence only near
each point of the *support* of the quotient. Away from that support the sheaf of ideals already
contains the unit section, and the one-term sequence `(1)` is then itself such a sequence, so the
opens carrying a Koszul presentation cover all of `X`:
`Stacks.AlgebraicGeometry.RegularIdealSheaf.coversTop_koszulPresentationOpen` of
`StacksFrontier.AlgebraicGeometry.RegularIdealSheaf.KoszulUnitCover`, indexed by the subtype of
opens that carry one. An earlier form of this note expected a degenerate case over the zero sheaf of
rings on the opens where the quotient vanishes; that is not what the cover needs.

**Where the three remaining inputs of that instantiation come from.** The first two are two
readings of one fact.

* `hgen`, the equality of the sections of
  `Stacks.AlgebraicGeometry.RegularIdealSheaf.sliceIdealOfSections` with those of
  `Stacks.Sites.idealOfHom` of the restricted global morphism, over the objects of
  `Opens X / U`. This is the tag's own local hypothesis, which
  `Stacks.AlgebraicGeometry.RegularIdealSheaf.IsGeneratedByOn` already records; what separates the
  two is that `IsGeneratedByOn` speaks of the sections over the opens `V ≤ U` of `Opens X` while
  `Stacks.AlgebraicGeometry.RegularIdealSheaf.generatedIdealOn` is an infimum of subsheaves and
  `sliceIdealOfSections` a local closure of an objectwise span. Both local closures live on the
  slice site, so no change of site is involved; the meeting point is the germ criterion
  `Stacks.AlgebraicGeometry.RegularIdealSheaf.mem_generatedIdealOn_iff`, from which a section of
  the generated ideal is locally a combination of the sequence. This is
  `Stacks.AlgebraicGeometry.RegularIdealSheaf.sectionIdeal_sliceIdealOfSections_eq` of
  `StacksFrontier.AlgebraicGeometry.RegularSequence.KoszulSelfExtGlobalGeneration`.
* `θ` together with `hθ`. `Stacks.Sites.quotientRingSheafIso` and
  `Stacks.Sites.toQuotientRingSheaf_comp_quotientRingSheafIso_hom` of
  `StacksFrontier.CategoryTheory.Sites.Modules.QuotientRingSheafRecognition` produce both from the
  equality of `RingHom.ker ((overRingHom α U).hom.app V).hom` with
  `sectionIdeal (sliceIdealOfSections U f) V`, and `Stacks.Sites.kerIdeal_quotientRingHom`
  identifies that kernel with the sheaf of ideals itself, so this is the previous item again.
  This is `Stacks.AlgebraicGeometry.RegularIdealSheaf.sliceQuotientRingHom` of
  `StacksFrontier.AlgebraicGeometry.RegularSequence.KoszulSelfExtGlobalQuotient`, together with its
  local surjectivity and its compatibility with the two quotient maps.
* `hAglob`, that the sheaf of ideals annihilates every homogeneous piece of the
  composition-product algebra of the global resolution. The local analogue is
  `Stacks.RegularSequence.KoszulChainData.smul_homologyPiece_eq_zero`, whose argument identifies
  the piece with a sheaf of homomorphisms into the quotient and so runs on a strictly perfect
  resolution; on all of `X` there is none, [Stacks, Tag 063D] part (2) being local. What the
  global statement rests on instead is that annihilation of a homogeneous piece is local on the
  space, the pieces being sheaves: the tool is
  `Stacks.SheafOfModules.eq_zero_of_locally_eq_zero`, over the cover by the opens of a Koszul
  presentation, with `smul_openSubspaceGradedAlgebra_piece_eq_zero` below on each member. This is
  `Stacks.AlgebraicGeometry.RegularIdealSheaf.smul_globalHomologyPiece_eq_zero` of
  `StacksFrontier.AlgebraicGeometry.RegularSequence.KoszulSelfExtGlobalAnnihilation`; it is not
  unconditional in the complex, taking the presentation of the quotient and the morphism whose
  cokernel it is.

**No `@[stacks]` attribute.** Nothing here is a clause of Tag 0BQY: these are the links of the
chain of presentations one hypothesis of that tag's gluing is transported along.

## References

* [Stacks Project, Tag 0BQY](https://stacks.math.columbia.edu/tag/0BQY)
* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf Opposite TopologicalSpace
open AlgebraicGeometry HomologicalComplex Stacks.ChainComplex

universe u

namespace SheafOfModules.GradedAlgebra

section RingIsoIdentity

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  {O R₁ R₂ : Sheaf J RingCat.{u}}
  (α₁ : O ⟶ R₁) [hα₁ : Presheaf.IsLocallySurjective J α₁.hom]
  (α₂ : O ⟶ R₂) [hα₂ : Presheaf.IsLocallySurjective J α₂.hom]
  (θ : R₁ ⟶ R₂) (hθ : α₁ ≫ θ = α₂) (B : GradedAlgebra.{u, u} O)
  (hB₁ : ∀ (n : ℤ) (V : Cᵒᵖ) (b : O.obj.obj V), b ∈ RingHom.ker (α₁.hom.app V).hom →
    ∀ m : (B.piece n).val.obj V, b • m = 0)
  (hB₂ : ∀ (n : ℤ) (V : Cᵒᵖ) (b : O.obj.obj V), b ∈ RingHom.ker (α₂.hom.app V).hom →
    ∀ m : (B.piece n).val.obj V, b • m = 0)

include hθ in
/-- **The identity-generator form of the transport of the universal property along an
identification of the quotient the algebra is descended along.** If the descent of `B` along one
locally surjective quotient map is the exterior algebra of its own degree-one piece, so is its
descent along a second one identified with the first by a locally surjective comparison carrying
the one quotient map to the other.

`SheafOfModules.GradedAlgebra.isExteriorAlgebra_descend_of_ringIso` tracks a generator, and at
the identity the generator it asks for is the restriction of scalars of the identity followed by
the transport; both are invertible
(`SheafOfModules.GradedAlgebra.isIso_genScalarRestrict` and
`SheafOfModules.GradedAlgebra.isIso_descendRingIsoHom_app`), so
`SheafOfModules.GradedAlgebra.IsExteriorAlgebra.of_id_of_isIso` supplies it. -/
theorem isExteriorAlgebra_id_descend_of_ringIso [hθ' : Presheaf.IsLocallySurjective J θ.hom]
    (h : IsExteriorAlgebra (descend α₁ B hB₁) (𝟙 ((descend α₁ B hB₁).piece 1))) :
    IsExteriorAlgebra (descend α₂ B hB₂) (𝟙 ((descend α₂ B hB₂).piece 1)) := by
  refine isExteriorAlgebra_descend_of_ringIso α₁ α₂ θ hθ B hB₁ hB₂ ?_
  exact IsExteriorAlgebra.of_id_of_isIso _ h

end RingIsoIdentity

section SliceGenerator

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  {B : GradedAlgebra.{u, u} R}

/-- **The restricted identity generator, from the identity generator of the restriction.** The
gluing primitive
`SheafOfModules.GradedAlgebra.IsExteriorAlgebra.isIso_desc_app_of_coversTop` asks for the
universal property of the restriction of the target at the *restricted* generator, while a chain
of presentations delivers it at the identity generator of the restriction. The two differ by the
restriction of an identity, which is invertible, so
`SheafOfModules.GradedAlgebra.IsExteriorAlgebra.of_id_of_isIso` converts. -/
theorem IsExteriorAlgebra.genOver_id (V : C)
    (h : IsExteriorAlgebra (B.over V) (𝟙 ((B.over V).piece 1))) :
    IsExteriorAlgebra (B.over V) (genOver (𝟙 (B.piece 1)) V) :=
  have : IsIso (genOver (𝟙 (B.piece 1)) V) :=
    inferInstanceAs (IsIso ((_root_.SheafOfModules.overFunctor.{u} R V).map
      (𝟙 (B.piece 1))))
  IsExteriorAlgebra.of_id_of_isIso _ h

end SliceGenerator

end SheafOfModules.GradedAlgebra

namespace Stacks.AlgebraicGeometry.RegularIdealSheaf

open Stacks.Sites Stacks.SheafOfModules Stacks.RegularSequence
open Stacks.RegularSequence.KoszulChainData
open _root_.SheafOfModules.GradedAlgebra

attribute [local instance] HasDerivedCategory.standard

variable {X : RingedSpace.{u, u}} (U : Opens X.carrier)
  [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ V : Opens X.carrier,
    HasSheafify ((Opens.grothendieckTopology X.carrier).over V) AddCommGrpCat.{u}]
  [∀ V : Opens X.carrier,
    ((Opens.grothendieckTopology X.carrier).over V).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology ↥U) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology ↥U).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify (Opens.grothendieckTopology ↥U) CommRingCat.{u}]
  [HasWeakSheafify ((Opens.grothendieckTopology X.carrier).over U) CommRingCat.{u}]
  {r : ℕ} (f : Fin r → X.presheaf.obj (op U))
  {A : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology ↥(openSubspace U).carrier)
    (koszulFreeSheaf (openSubspace U).sheaf r)}
  (K : KoszulChainData.{u, u, u} A
    (koszulHomOfSections (openSubspace U).sheaf fun j => sectionOnRestriction X U (f j)))
  [QuasiIso K.augmentation]

/-- **The quotient map of the structure sheaf of `X|_U` that the local statements over `U`
descend along**: the quotient by the sheaf of ideals the Koszul morphism of `f₁, …, f_r`
generates there. -/
abbrev koszulOpenSubspaceQuotient :
    openSubspaceRing U ⟶
      Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u}
        (quotientRingSheaf.{u, u, u} (koszulOpenSubspaceIdeal U f)) :=
  quotientRingHom (koszulOpenSubspaceIdeal U f)

/-- **A sheaf of graded algebras on the slice site over `U`, read on the open subspace, at the
`Stacks.SheafOfModules.openSubspaceRing` spelling of its sheaf of rings.** The ascription is the
point: the structure sheaf of rings of `X.restrict U` is written both as
`AlgebraicGeometry.structureSheafRing (openSubspace U)`, which is the sheaf of
rings `Stacks.SheafOfModules.openSubspaceGradedAlgebra` produces its algebra over, and as
`Stacks.SheafOfModules.openSubspaceRing`, which is the source of
`Stacks.Sites.quotientRingHom` for a sheaf of ideals formed on `X.restrict U`; elaboration
crosses the two and instance search does not, so the scalar action on a homogeneous piece is
found only at one of them. -/
abbrev openSubspaceSliceAlgebra
    (B : _root_.SheafOfModules.GradedAlgebra.{u, u}
      ((structureSheafRing X).over U)) :
    _root_.SheafOfModules.GradedAlgebra.{u, u} (openSubspaceRing U) :=
  openSubspaceGradedAlgebra U B

section Links

variable {F : _root_.SheafOfModules.{u} (structureSheafRing X)}
  (Φ : F ⟶ _root_.SheafOfModules.unit (structureSheafRing X))
  (hgen : ∀ W : (Over U)ᵒᵖ,
    sectionIdeal (sliceIdealOfSections U f) W =
      sectionIdeal (idealOfHom (O := X.sheaf.over U)
        ((_root_.SheafOfModules.overFunctor.{u}
          (structureSheafRing X) U).map Φ)) W)
  (I : CochainComplex (_root_.SheafOfModules.{u}
    (structureSheafRing X)) ℤ) (hI : I.IsKInjective)
  (e : DerivedCategory.Q.obj
      ((single (_root_.SheafOfModules.{u} (structureSheafRing X))
        (ComplexShape.up ℤ) 0).obj (cokernel Φ)) ≅
    DerivedCategory.Q.obj I)

omit [HasWeakSheafify ((Opens.grothendieckTopology X.carrier).over U) CommRingCat.{u}] in
include K hgen hI e in
/-- **The composition-product algebra of the restriction to `U` of a global resolution is
annihilated by the sheaf of ideals.** The comparison of the two models over `U` identifies its
pieces with those of the Koszul algebra, where the annihilation is
`Stacks.RegularSequence.KoszulChainData.smul_homologyPiece_eq_zero`.

**The scalar is ascribed to the sheaf of rings the algebra is indexed by.**
`Stacks.SheafOfModules.homologyGradedAlgebra` produces its algebra over
`structureSheaf (openSubspace U).sheaf`, which is therefore where the scalar action on a
homogeneous piece lives, while `b` is read out of `Stacks.SheafOfModules.openSubspaceRing` — the
canonical `Stacks.SheafOfModules.Tensor.ringSheaf` spelling that `Stacks.Sites.quotientRingHom`
is stated at. The two are one sheaf of rings by `rfl`, so the ascription names a spelling and
weakens nothing; it is the scalar counterpart of the algebra ascriptions
`openSubspaceSliceAlgebra` above and `globalHomologyGradedAlgebra` below. -/
theorem smul_openSubspaceRestrictComplex_piece_eq_zero (n : ℤ) (V : (Opens ↥U)ᵒᵖ)
    (b : (openSubspaceRing U).obj.obj V)
    (hb : b ∈ RingHom.ker ((koszulOpenSubspaceQuotient U f).hom.app V).hom)
    (m : ((homologyGradedAlgebra (openSubspace U).sheaf
      (openSubspaceRestrictComplex U I)).piece n).val.obj V) :
    (show (structureSheaf (openSubspace U).sheaf).obj.obj V from b) • m = 0 :=
  have : IsIso ((restrictedModelComparisonUnitalOfGenerated U f K Φ hgen I hI e).app n) :=
    isIso_restrictedModelComparisonUnitalOfGenerated_app U f K Φ hgen I hI e n
  UnitalHom.smul_piece_eq_zero
    (restrictedModelComparisonUnitalOfGenerated U f K Φ hgen I hI e) n
    (smul_homologyPiece_eq_zero (openSubspace U).sheaf K n V b hb) m

omit [HasWeakSheafify ((Opens.grothendieckTopology X.carrier).over U) CommRingCat.{u}] in
include K hgen hI e in
/-- **The descended third link: the Koszul complex over `U` against the restriction of a global
resolution.** If the descended composition-product algebra of the Koszul cochain complex over
`U` is the exterior algebra of its own degree-one piece, then so is the descent of the
composition-product algebra of the restriction to `U` of a resolution chosen on all of `X`.

`Stacks.AlgebraicGeometry.RegularIdealSheaf.restrictedModelComparisonUnitalOfGenerated` is the
comparison, an isomorphism in every degree, and
`SheafOfModules.GradedAlgebra.isExteriorAlgebra_id_descend_of_degreewiseIso` descends the
transport of the universal property along it. -/
theorem isExteriorAlgebra_id_descend_openSubspaceRestrictComplex
    (h : IsExteriorAlgebra
      (descend (koszulOpenSubspaceQuotient U f)
        (homologyGradedAlgebra (openSubspace U).sheaf (cochain (openSubspace U).sheaf K))
        (smul_homologyPiece_eq_zero (openSubspace U).sheaf K))
      (𝟙 ((descend (koszulOpenSubspaceQuotient U f)
        (homologyGradedAlgebra (openSubspace U).sheaf (cochain (openSubspace U).sheaf K))
        (smul_homologyPiece_eq_zero (openSubspace U).sheaf K)).piece 1))) :
    IsExteriorAlgebra
      (descend (koszulOpenSubspaceQuotient U f)
        (homologyGradedAlgebra (openSubspace U).sheaf (openSubspaceRestrictComplex U I))
        (smul_openSubspaceRestrictComplex_piece_eq_zero U f K Φ hgen I hI e))
      (𝟙 ((descend (koszulOpenSubspaceQuotient U f)
        (homologyGradedAlgebra (openSubspace U).sheaf (openSubspaceRestrictComplex U I))
        (smul_openSubspaceRestrictComplex_piece_eq_zero U f K Φ hgen I hI e)).piece 1)) :=
  isExteriorAlgebra_id_descend_of_degreewiseIso (koszulOpenSubspaceQuotient U f) _ _
    (restrictedModelComparisonUnitalOfGenerated U f K Φ hgen I hI e)
    (fun n => isIso_restrictedModelComparisonUnitalOfGenerated_app U f K Φ hgen I hI e n) h

omit [HasWeakSheafify ((Opens.grothendieckTopology X.carrier).over U) CommRingCat.{u}] in
include K hgen hI e in
/-- **The open-subspace reading of the restriction of the global composition-product algebra is
annihilated by the sheaf of ideals.** The first link of the chain identifies its pieces with
those of the composition-product algebra of the restricted resolution, where the annihilation is
`Stacks.AlgebraicGeometry.RegularIdealSheaf.smul_openSubspaceRestrictComplex_piece_eq_zero`. -/
theorem smul_openSubspaceGradedAlgebra_piece_eq_zero (n : ℤ) (V : (Opens ↥U)ᵒᵖ)
    (b : (openSubspaceRing U).obj.obj V)
    (hb : b ∈ RingHom.ker ((koszulOpenSubspaceQuotient U f).hom.app V).hom)
    (m : ((openSubspaceSliceAlgebra U
      ((RingedSite.homologyGradedAlgebra (ringedSite X.sheaf) I).over U)).piece n).val.obj V) :
    b • m = 0 :=
  UnitalHom.smul_piece_eq_zero (openSubspaceHomologyGradedAlgebraOfSpaceHom U I) n
    (smul_openSubspaceRestrictComplex_piece_eq_zero U f K Φ hgen I hI e n V b hb) m

omit [HasWeakSheafify ((Opens.grothendieckTopology X.carrier).over U) CommRingCat.{u}] in
include K hgen hI e in
/-- **The descended first link: the open subspace against the restriction to the slice site.**
If the descent of the composition-product algebra of the restriction to `U` of a resolution
chosen on all of `X` is the exterior algebra of its own degree-one piece, then so is the descent
of the open-subspace reading of the restriction to the slice site over `U` of the
composition-product algebra of that resolution.

`Stacks.SheafOfModules.openSubspaceHomologyGradedAlgebraOfSpaceHom` is the comparison, an
isomorphism in every degree, and
`SheafOfModules.GradedAlgebra.isExteriorAlgebra_id_descend_of_degreewiseIso` descends the
transport of the universal property along it. -/
theorem isExteriorAlgebra_id_descend_openSubspaceGradedAlgebra
    (h : IsExteriorAlgebra
      (descend (koszulOpenSubspaceQuotient U f)
        (homologyGradedAlgebra (openSubspace U).sheaf (openSubspaceRestrictComplex U I))
        (smul_openSubspaceRestrictComplex_piece_eq_zero U f K Φ hgen I hI e))
      (𝟙 ((descend (koszulOpenSubspaceQuotient U f)
        (homologyGradedAlgebra (openSubspace U).sheaf (openSubspaceRestrictComplex U I))
        (smul_openSubspaceRestrictComplex_piece_eq_zero U f K Φ hgen I hI e)).piece 1))) :
    IsExteriorAlgebra
      (descend (koszulOpenSubspaceQuotient U f)
        (openSubspaceSliceAlgebra U
          ((RingedSite.homologyGradedAlgebra (ringedSite X.sheaf) I).over U))
        (smul_openSubspaceGradedAlgebra_piece_eq_zero U f K Φ hgen I hI e))
      (𝟙 ((descend (koszulOpenSubspaceQuotient U f)
        (openSubspaceSliceAlgebra U
          ((RingedSite.homologyGradedAlgebra (ringedSite X.sheaf) I).over U))
        (smul_openSubspaceGradedAlgebra_piece_eq_zero U f K Φ hgen I hI e)).piece 1)) :=
  isExteriorAlgebra_id_descend_of_degreewiseIso (koszulOpenSubspaceQuotient U f) _ _
    (openSubspaceHomologyGradedAlgebraOfSpaceHom U I)
    (fun n => isIso_openSubspaceHomologyGradedAlgebraOfSpaceHom_app U I n) h

section Chain

/-- **The composition-product algebra of a complex of `O_X`-modules, at the
`AlgebraicGeometry.structureSheafRing` spelling of its sheaf of rings.** The
ascription pins the spelling at which the scalar action on a homogeneous piece is found by
instance search; the sheaf of rings is the same one
`AlgebraicGeometry.RingedSite.homologyGradedAlgebra` produces its algebra over. -/
abbrev globalHomologyGradedAlgebra
    (Q : CochainComplex (_root_.SheafOfModules.{u}
      (structureSheafRing X)) ℤ) :
    _root_.SheafOfModules.GradedAlgebra.{u, u} (structureSheafRing X) :=
  RingedSite.homologyGradedAlgebra (ringedSite X.sheaf) Q

variable {R' : Sheaf (Opens.grothendieckTopology X.carrier) RingCat.{u}}
  (α : structureSheafRing X ⟶ R')
  [Presheaf.IsLocallySurjective (Opens.grothendieckTopology X.carrier) α.hom]
  (hAglob : ∀ (n : ℤ) (W : (Opens X.carrier)ᵒᵖ)
      (b : (structureSheafRing X).obj.obj W),
    b ∈ RingHom.ker (α.hom.app W).hom →
      ∀ m : ((globalHomologyGradedAlgebra I).piece n).val.obj W, b • m = 0)
  (θ : Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u}
      (quotientRingSheaf.{u, u, u} (sliceIdealOfSections U f)) ⟶ R'.over U)
  [Presheaf.IsLocallySurjective ((Opens.grothendieckTopology X.carrier).over U) θ.hom]
  (hθ : quotientRingHom (sliceIdealOfSections U f) ≫ θ = overRingHom α U)

include K hgen hI e hθ in
/-- **The hypothesis `hBV` of the gluing, at one member of the cover.** Let `α : O_X ↠ O_X/𝓘` be
a locally surjective quotient of the structure sheaf of `X`, let `I` be a K-injective complex of
`O_X`-modules presenting the quotient, and let `f₁, …, f_r` be sections over `U` whose Koszul
complex over `U` carries the chain datum `K`. Suppose that over the objects of `Opens X / U` the
sections `f₁, …, f_r` generate the sheaf of ideals `𝓘` — the tag's own local hypothesis, in the
two forms the comparison of the models and the comparison of the quotients consume. Then the
restriction to the slice site at `U` of the globally descended composition-product algebra of
`I` is the exterior algebra of its own degree-one piece as soon as the descended
composition-product algebra of the Koszul complex over `U` is.

This is the whole chain of presentations: the descended third link
(`isExteriorAlgebra_id_descend_openSubspaceRestrictComplex`), the descended first link
(`isExteriorAlgebra_id_descend_openSubspaceGradedAlgebra`), the second link
(`isExteriorAlgebra_id_descend_koszulOpenSubspace`), the identification of the slice quotient by
`f₁, …, f_r` with the restriction of the global quotient
(`SheafOfModules.GradedAlgebra.isExteriorAlgebra_id_descend_of_ringIso`), and the three links of
the descent presentation that separate the open subspace from the slice site
(`Stacks.SheafOfModules.isExteriorAlgebra_id_over_descend_of_openSubspace`).

The conclusion is exactly the hypothesis `hBV` of
`SheafOfModules.GradedAlgebra.IsExteriorAlgebra.isIso_desc_app_of_coversTop`, read at `V = U`. -/
theorem isExteriorAlgebra_id_over_descend_koszulChain
    (h : IsExteriorAlgebra
      (descend (koszulOpenSubspaceQuotient U f)
        (homologyGradedAlgebra (openSubspace U).sheaf (cochain (openSubspace U).sheaf K))
        (smul_homologyPiece_eq_zero (openSubspace U).sheaf K))
      (𝟙 ((descend (koszulOpenSubspaceQuotient U f)
        (homologyGradedAlgebra (openSubspace U).sheaf (cochain (openSubspace U).sheaf K))
        (smul_homologyPiece_eq_zero (openSubspace U).sheaf K)).piece 1))) :
    IsExteriorAlgebra
      ((descend α (globalHomologyGradedAlgebra I) hAglob).over U)
      (𝟙 (((descend α (globalHomologyGradedAlgebra I) hAglob).over U).piece 1)) := by
  have hs : ∀ {R₁ R₂ : Sheaf ((Opens.grothendieckTopology X.carrier).over U) RingCat.{u}}
      (g : R₁ ⟶ R₂), Presheaf.IsLocallySurjective
        ((Opens.grothendieckTopology X.carrier).over U) g.hom →
      Presheaf.IsLocallySurjective (Opens.grothendieckTopology ↥U)
        ((openSubspaceRingPushforward U).map g).hom := fun g hg =>
    Presheaf.isLocallySurjective_whisker (Opens.grothendieckTopology ↥U)
      ((Opens.grothendieckTopology X.carrier).over U) (openSubspaceSiteFunctor U) g.hom
  have hlink2 := isExteriorAlgebra_id_descend_koszulOpenSubspace U f
    (openSubspaceSliceAlgebra U ((globalHomologyGradedAlgebra I).over U))
    (smul_openSubspaceGradedAlgebra_piece_eq_zero U f K Φ hgen I hI e)
    (isExteriorAlgebra_id_descend_openSubspaceGradedAlgebra U f K Φ hgen I hI e
      (isExteriorAlgebra_id_descend_openSubspaceRestrictComplex U f K Φ hgen I hI e h))
  refine isExteriorAlgebra_id_over_descend_of_openSubspace α U
    (globalHomologyGradedAlgebra I) hAglob ?_
  exact isExteriorAlgebra_id_descend_of_ringIso
    (α₁ := openSubspaceQuotientHom U (quotientRingHom (sliceIdealOfSections U f)))
    (α₂ := openSubspaceRingHom U (overRingHom α U))
    (θ := (openSubspaceRingPushforward U).map θ) (hα₂ := hs _ (Presheaf.isLocallySurjective_whisker
      ((Opens.grothendieckTopology X.carrier).over U)
      (Opens.grothendieckTopology X.carrier) (Over.forget U) α.hom)) (hθ' := hs _ inferInstance)
    (hθ := ((openSubspaceRingPushforward U).map_comp _ _).symm.trans
      (congrArg (openSubspaceRingPushforward U).map hθ))
    (B := openSubspaceSliceAlgebra U ((globalHomologyGradedAlgebra I).over U))
    (hB₂ := smul_openSubspaceGradedAlgebra_eq_zero U (overRingHom α U)
      ((globalHomologyGradedAlgebra I).over U)
      (smul_over_eq_zero α U (globalHomologyGradedAlgebra I) hAglob))
    (h := hlink2)

include K hgen hI e hθ in
/-- **The hypothesis `hBV` of the gluing of [Stacks, Tag 0BQY], at one member of the cover,
discharged.** With the local conclusion of the tag over `U` supplied by
`Stacks.RegularSequence.KoszulChainData.isExteriorAlgebra_extSelfAlgebra`, the restriction to the
slice site at `U` of the globally descended composition-product algebra of a K-injective
resolution `I` of the quotient is the exterior algebra of its own degree-one piece.

The hypotheses are the tag's own: `U` is an open over which the sheaf of ideals is generated by
sections `f₁, …, f_r` whose Koszul complex is acyclic in positive degrees — that acyclicity is
what the quasi-isomorphism instance on `K.augmentation` records — together with the two
identifications of the slice quotient that generation supplies. -/
theorem isExteriorAlgebra_id_over_descend_koszul :
    IsExteriorAlgebra
      ((descend α (globalHomologyGradedAlgebra I) hAglob).over U)
      (𝟙 (((descend α (globalHomologyGradedAlgebra I) hAglob).over U).piece 1)) :=
  isExteriorAlgebra_id_over_descend_koszulChain U f K Φ hgen I hI e α hAglob θ hθ
    (KoszulChainData.isExteriorAlgebra_extSelfAlgebra (openSubspace U).sheaf K)

include K hgen hI e hθ in
/-- **The hypothesis `hBV` of the gluing of [Stacks, Tag 0BQY], at one member of the cover, in
the shape the gluing primitive consumes.**
`SheafOfModules.GradedAlgebra.IsExteriorAlgebra.isIso_desc_app_of_coversTop` asks for the
universal property of the restriction of the target algebra at the restriction of the degree-one
generator; the chain delivers it at the identity generator of the restriction, and the two differ
by an invertible morphism. -/
theorem isExteriorAlgebra_genOver_descend_koszul :
    IsExteriorAlgebra
      ((descend α (globalHomologyGradedAlgebra I) hAglob).over U)
      (genOver (𝟙 ((descend α (globalHomologyGradedAlgebra I) hAglob).piece 1)) U) :=
  IsExteriorAlgebra.genOver_id U
    (isExteriorAlgebra_id_over_descend_koszul U f K Φ hgen I hI e α hAglob θ hθ)

end Chain

end Links

end Stacks.AlgebraicGeometry.RegularIdealSheaf

end
