module

public import StacksFrontier.AlgebraicGeometry.Constructions.VectorBundleOfModule
public import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.Punctured
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The zero section of the vector bundle of a quasi-coherent module

Let `S` be a scheme and `ℰ` a quasi-coherent `𝒪_S`-module, and let
`𝐕(ℰ) = Spec_S(Sym(ℰ))` be the vector bundle of
`AlgebraicGeometry.Scheme.Modules.vectorBundle`. The homogeneous pieces of `Sym(ℰ)` vanish in
negative degrees and degree zero is the structure sheaf, so the degree-zero component of a
section of the ungraded realization of `Sym(ℰ)` is a ring homomorphism onto `𝒪_S`: this is the
**augmentation** `Sym(ℰ) ⟶ 𝒪_S`, which kills every positive degree and retracts the structure
map of the algebra. The section of `𝐕(ℰ) ⟶ S` it cuts out is the **zero section**.

Nothing here restricts `ℰ`: it is quasi-coherent and nothing more — not invertible, not finite
locally free — and the base is an arbitrary scheme. For an invertible `ℰ` the same morphism is
`Stacks.LineBundle.Situation.zeroSection`, built from the same mechanism
(`Stacks.RelativeSpec.retractionSection`) over the *other* realization of `Sym(ℰ)` as a sheaf of
commutative algebras; see the implementation notes.

## Main definitions

* `Stacks.CommRingSheaf.presheafHomOut`: a morphism of presheaves of rings *out of* a presheaf of
  rings whose sections commute, read as a morphism of presheaves of commutative rings. This is
  the converse direction of `Stacks.CommRingSheaf.homMk`.
* `AlgebraicGeometry.Scheme.Modules.symmetricAlgebraRingAugmentation` and
  `symmetricAlgebraSheafAugmentation`: **the augmentation `Sym(ℰ) ⟶ 𝒪_S`**, as a morphism of
  sheaves of rings and as a morphism of the presheaves of commutative rings that
  `Stacks.RelativeSpec.retractionSection` consumes.
* `AlgebraicGeometry.Scheme.Modules.vectorBundleZeroSection`: **the zero section
  `S ⟶ 𝐕(ℰ)`.**

## Main results

* `AlgebraicGeometry.Scheme.Modules.hom_comp_symmetricAlgebraSheafAugmentation`: the
  augmentation of `Sym(ℰ)` retracts the structure morphism `𝒪_S ⟶ Sym(ℰ)`.
* `AlgebraicGeometry.Scheme.Modules.vectorBundleZeroSection_comp_vectorBundleToBase`: **the zero
  section splits the projection `𝐕(ℰ) ⟶ S`.**
* `AlgebraicGeometry.Scheme.Modules.isClosedImmersion_vectorBundleZeroSection`: **the zero
  section is a closed immersion.**
* `AlgebraicGeometry.Scheme.Modules.ι_vectorBundleZeroSection`: over an affine open `U` of `S`
  the zero section is the spectrum of the augmentation on sections over `U`, read in the chart of
  `U`.

## Implementation notes

**Two realizations of `Sym(ℰ)` as a sheaf of commutative algebras.** The relative spectrum
consumes a `Stacks.RelativeSpec.AlgebraSheaf`, and the repository realizes `Sym(ℰ)` as one in two
inequivalent ways: `Stacks.RelativeSpec.ungradedAlgebraSheaf`, which sheafifies the
`CommRingCat`-valued presheaf of direct sums, and `Stacks.RelativeSpec.gradedAlgebraSheaf`, which
lifts the `RingCat`-valued sheafification to `CommRingCat` by
`Stacks.CommRingSheaf.sheaf`. `AlgebraicGeometry.Scheme.Modules.vectorBundle` — and so `𝐕(ℰ)` —
is built from the *second*, through
`AlgebraicGeometry.Scheme.Modules.symmetricAlgebraSheaf`, while
`Stacks.RelativeSpec.algebraSheafAugmentation` and hence
`Stacks.LineBundle.Situation.zeroSection` are built from the *first*. The two agree only up to
the isomorphism `Stacks.RelativeSpec.ringSheafIsoUngradedSheaf`, which is why the augmentation is
rebuilt here rather than reused: the zero section of `𝐕(ℰ)` has to be a morphism into `𝐕(ℰ)`
itself, not into a scheme isomorphic to it.

Rebuilding costs only `Stacks.CommRingSheaf.presheafHomOut`: the presheaf-level augmentation is
`Stacks.RelativeSpec.ungradedCommAugmentation` with commutativity forgotten. All the mathematics is
already general: `Stacks.GradedAlgebra.augmentation` and
`Stacks.RelativeSpec.pieceZeroAugmentation` are stated for an arbitrary `ℤ`-graded algebra with
vanishing negative pieces, and `AlgebraicGeometry.Scheme.Modules.symmetricAlgebraPieceZeroIso`,
`symmetricAlgebraPieceZeroIso_hom_one` and `isZero_symmetricAlgebra_piece` hold for an arbitrary
`X` and an arbitrary module sheaf.

**No tag.** Tag 01M2 is the construction of `𝐕(ℰ)` and carries no zero section; the zero section
appears inside the proof of [Stacks, Tag 0B3V] and is not the assertion of a tag of its own, so
nothing here is registered.

## References

* [Stacks Project, Tag 01M2](https://stacks.math.columbia.edu/tag/01M2)
* [Stacks Project, Tag 01LM](https://stacks.math.columbia.edu/tag/01LM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry

universe v u w

namespace Stacks.CommRingSheaf

variable {C : Type u} [Category.{u} C]

/-- A morphism of presheaves of rings out of a presheaf of rings whose sections commute, read as
a morphism of presheaves of commutative rings out of its lift. This is the direction
`Stacks.CommRingSheaf.homMk` does not cover; as there, the carrier and the ring operations are
unchanged, so the components are the same functions. -/
def presheafHomOut {P : Cᵒᵖ ⥤ RingCat.{u}}
    (h : ∀ (W : Cᵒᵖ) (a b : P.obj W), a * b = b * a) (O : Cᵒᵖ ⥤ CommRingCat.{u})
    (f : P ⟶ O ⋙ forget₂ CommRingCat.{u} RingCat.{u}) :
    presheaf P h ⟶ O where
  app W := @CommRingCat.ofHom (P.obj W) (O.obj W) (commRing (P.obj W) (h W)) _ (f.app W).hom
  naturality W W' g := by
    ext x
    exact congrArg (fun φ => RingCat.Hom.hom φ x) (f.naturality g)

end Stacks.CommRingSheaf

namespace AlgebraicGeometry.Scheme.Modules

variable (S : Scheme.{u}) (E : SheafOfModules.{u} S.ringCatSheaf)

/-- **The augmentation of `Sym(ℰ)` on the presheaf of direct sums**, as a morphism of presheaves
of rings onto the structure sheaf of the base: the degree-zero component, which is a ring
homomorphism because the negative pieces of `Sym(ℰ)` vanish and degree zero is free of rank one
on the algebra unit. It is `Stacks.RelativeSpec.ungradedCommAugmentation` with commutativity
forgotten. -/
def symmetricAlgebraTotalAugmentation :
    (symmetricAlgebra S E).toPresheafGradedAlgebra.totalPresheaf ⟶ S.ringCatSheaf.obj :=
  Functor.whiskerRight
    (Stacks.RelativeSpec.ungradedCommAugmentation (symmetricAlgebra S E)
      (symmetricAlgebra_mul_comm S E) (symmetricAlgebraPieceZeroIso S E)
      (symmetricAlgebraPieceZeroIso_hom_one S E) (isZero_symmetricAlgebra_piece S E))
    (forget₂ CommRingCat.{u} RingCat.{u})

/-- The augmentation of `Sym(ℰ)` retracts the structure map `r ↦ r • 1` of the presheaf of direct
sums: `Stacks.RelativeSpec.ungradedCommStructureMap_comp_ungradedCommAugmentation` with
commutativity forgotten. -/
lemma structureHom_comp_symmetricAlgebraTotalAugmentation :
    (symmetricAlgebra S E).toPresheafGradedAlgebra.structureHom ≫
        symmetricAlgebraTotalAugmentation S E = 𝟙 S.ringCatSheaf.obj :=
  congrArg (fun φ => Functor.whiskerRight φ (forget₂ CommRingCat.{u} RingCat.{u}))
    (Stacks.RelativeSpec.ungradedCommStructureMap_comp_ungradedCommAugmentation
      (symmetricAlgebra S E) (symmetricAlgebra_mul_comm S E) (symmetricAlgebraPieceZeroIso S E)
      (symmetricAlgebraPieceZeroIso_hom_one S E) (isZero_symmetricAlgebra_piece S E))

/-- **The augmentation `Sym(ℰ) ⟶ 𝒪_S`, as a morphism of sheaves of rings.** -/
def symmetricAlgebraRingAugmentation :
    (symmetricAlgebra S E).ungradedSheaf ⟶ S.ringCatSheaf :=
  Stacks.GradedAlgebra.totalSheafLift _ _ S.ringCatSheaf (symmetricAlgebraTotalAugmentation S E)

/-- The augmentation `Sym(ℰ) ⟶ 𝒪_S` retracts the structure morphism of the ungraded realization
of `Sym(ℰ)`, as morphisms of presheaves of rings. -/
lemma structureSheafHom_comp_symmetricAlgebraRingAugmentation :
    (symmetricAlgebra S E).toPresheafGradedAlgebra.structureSheafHom
          (Opens.grothendieckTopology (S : TopCat)) ≫
        (symmetricAlgebraRingAugmentation S E).hom = 𝟙 S.ringCatSheaf.obj := by
  show (symmetricAlgebra S E).toPresheafGradedAlgebra.structureHom ≫
      (symmetricAlgebra S E).toPresheafGradedAlgebra.toTotalSheaf
          (Opens.grothendieckTopology (S : TopCat)) ≫
        (symmetricAlgebraRingAugmentation S E).hom = _
  exact (congrArg (fun k => (symmetricAlgebra S E).toPresheafGradedAlgebra.structureHom ≫ k)
      (Stacks.GradedAlgebra.toTotalSheaf_totalSheafLift
        (symmetricAlgebra S E).toPresheafGradedAlgebra _ S.ringCatSheaf
        (symmetricAlgebraTotalAugmentation S E))).trans
    (structureHom_comp_symmetricAlgebraTotalAugmentation S E)

/-- **The augmentation `Sym(ℰ) ⟶ 𝒪_S`**, in the shape
`Stacks.RelativeSpec.retractionSection` consumes: a morphism of the presheaves of commutative
rings underlying the algebra sheaf of `𝐕(ℰ)` and the structure sheaf of the base. -/
def symmetricAlgebraSheafAugmentation :
    (symmetricAlgebraSheaf S E).right.obj ⟶ S.presheaf :=
  Stacks.CommRingSheaf.presheafHomOut _ S.presheaf
    (symmetricAlgebraRingAugmentation S E).hom

/-- **The augmentation `Sym(ℰ) ⟶ 𝒪_S` retracts the structure morphism `𝒪_S ⟶ Sym(ℰ)`** of the
algebra sheaf of `𝐕(ℰ)`. -/
lemma hom_comp_symmetricAlgebraSheafAugmentation :
    (symmetricAlgebraSheaf S E).hom.hom ≫ symmetricAlgebraSheafAugmentation S E =
      𝟙 S.presheaf := by
  refine NatTrans.ext (funext fun W => CommRingCat.hom_ext (RingHom.ext fun r => ?_))
  have h := NatTrans.congr_app
    (structureSheafHom_comp_symmetricAlgebraRingAugmentation S E) W
  exact congrArg (fun φ => RingCat.Hom.hom φ r) h

section

variable [E.IsQuasicoherent]

/-- The relative-spectrum situation whose relative spectrum is `𝐕(ℰ)`: the base `S` with the
quasi-coherent algebra sheaf `Sym(ℰ)`. -/
def vectorBundleSituation : Stacks.RelativeSpec.RelativeSpecSituation.{u} where
  base := S
  algebra := symmetricAlgebraSheaf S E

/-- **The zero section `S ⟶ 𝐕(ℰ)` of the vector bundle of a quasi-coherent module**: the section
of the projection cut out by the augmentation `Sym(ℰ) ⟶ 𝒪_S`.

`ℰ` is quasi-coherent and nothing more, and `S` is an arbitrary scheme. -/
@[ega "II 1.7.9", sga "6 IX 1.6"]
def vectorBundleZeroSection : S ⟶ vectorBundle S E :=
  Stacks.RelativeSpec.retractionSection (vectorBundleSituation S E)
    (symmetricAlgebraSheafAugmentation S E)
    (hom_comp_symmetricAlgebraSheafAugmentation S E)

/-- **The zero section splits the projection `𝐕(ℰ) ⟶ S`.** -/
@[ega "II 1.7.9" "partial", sga "6 IX 1.6" "partial"]
theorem vectorBundleZeroSection_comp_vectorBundleToBase :
    vectorBundleZeroSection S E ≫ vectorBundleToBase S E = 𝟙 S :=
  Stacks.RelativeSpec.retractionSection_comp_toBase (vectorBundleSituation S E)
    (symmetricAlgebraSheafAugmentation S E)
    (hom_comp_symmetricAlgebraSheafAugmentation S E)

/-- **The zero section of `𝐕(ℰ)` is a closed immersion**, being a section of an affine, hence
separated, morphism. -/
instance isClosedImmersion_vectorBundleZeroSection :
    IsClosedImmersion (vectorBundleZeroSection S E) :=
  Stacks.RelativeSpec.isClosedImmersion_retractionSection (vectorBundleSituation S E)
    (symmetricAlgebraSheafAugmentation S E)
    (hom_comp_symmetricAlgebraSheafAugmentation S E)

/-- **Over an affine open `U` of the base the zero section of `𝐕(ℰ)` is the spectrum of the
augmentation of `Sym(ℰ)` on sections over `U`**, read in the chart of `U`. -/
theorem ι_vectorBundleZeroSection (U : S.affineOpens) :
    U.1.ι ≫ vectorBundleZeroSection S E =
      U.1.toSpecΓ ≫ Spec.map ((symmetricAlgebraSheafAugmentation S E).app (op U.1)) ≫
        (Stacks.RelativeSpec.gluedSpectrum (vectorBundleSituation S E)).chart U :=
  Stacks.RelativeSpec.ι_retractionSection (vectorBundleSituation S E)
    (symmetricAlgebraSheafAugmentation S E)
    (hom_comp_symmetricAlgebraSheafAugmentation S E) U

/-- **The open complement of the zero section of `𝐕(ℰ)`**: the vector bundle with its zero
section deleted. -/
@[sga "3 XIX 4.3" "more general"]
def vectorBundleZeroSectionComplement : (vectorBundle S E).Opens :=
  Stacks.RelativeSpec.retractionComplement (vectorBundleSituation S E)
    (symmetricAlgebraSheafAugmentation S E)
    (hom_comp_symmetricAlgebraSheafAugmentation S E)

end

end AlgebraicGeometry.Scheme.Modules

end
