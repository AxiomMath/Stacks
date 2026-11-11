module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Dualizing.DualizingComplexes.SyntomicBaseChange
public import StacksFrontier.RingTheory.Dualizing.TrivialDualityInvertibleKernel
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.DerivedTensorUnconditional
import StacksFrontier.Homology.Tor.DerivedTensorLargeUniverse

/-!
# Tag 0E4D

Let `φ : A → B` be a homomorphism of Noetherian rings which is syntomic and surjective on
spectra, or faithfully flat and a local complete intersection, or faithfully flat of finite type
with Gorenstein fibres.  Then `K` in `D(A)` is a dualizing complex for `A` exactly when
`K ⊗_A^L B` is a dualizing complex for `B` ([Stacks, Tag 0E4D]).

`StacksFrontier.RingTheory.Dualizing.DualizingComplexes.SyntomicBaseChange` states the three cases
at a polynomial presentation with inputs of the ascent direction taken as hypotheses: `hInv`, the
invertibility of the relative dualizing complex `ω^•_{B/A} = φ^!(A)` (cases (1) and (2); in
case (3) it is derived from the Gorenstein fibres by [Stacks, Tag 0E4C]), and `hTensor`, the
tensor formula `φ^!(K) = (K ⊗_A^L B) ⊗_B ω^•_{B/A}`.  Both are proved here: `hInv` for a local
complete intersection, which covers case (1) — syntomic is flat and a local complete
intersection by [Stacks, Tag 07D3] — and case (2); `hTensor` whenever `B` is perfect over the
polynomial algebra of the presentation, which a local complete intersection gives by
[Stacks, Tag 07EN] and a flat map of finite type over a Noetherian base gives by
[Stacks, Tag 067J] (`Dualizing.PolynomialPresentation.isPerfectModule_of_flat`).  The
presentation itself is obtained from finite type, so the three cases are stated under exactly
the hypotheses of the source and with nothing carried, in both directions.

## Main results

* `Dualizing.isDualizingComplex_iff_derivedExtensionScalars_of_syntomic_unconditional` —
  **Tag 0E4D case (1).**
* `Dualizing.isDualizingComplex_iff_derivedExtensionScalars_of_faithfullyFlat_lci_unconditional` —
  **Tag 0E4D case (2).**
* `Dualizing.isDualizingComplex_iff_derivedExtensionScalars_of_gorensteinFibres_unconditional` —
  **Tag 0E4D case (3).**
* `Dualizing.isInvertible_relativeDualizingUnit_of_isLocalCompleteIntersection` — the input
  `hInv`, proved.
* `Dualizing.nonempty_upperShriekFunctor_obj_iso_derivedExtensionScalars_tensor_of_isPerfect`
  and `…_of_lci` — the input `hTensor`, proved.

The three alternative hypotheses of the source are delivered as three theorems, each stating one
whole case, rather than as one disjunction.

## Implementation notes

`hInv` is the invertibility clause of [Stacks, Tag 0E4B], i.e.
`Dualizing.PolynomialPresentation`'s
`isInvertible_upperShriekFunctor_obj_unit_of_isLocalCompleteIntersection`,
which the complete-intersection file proves unconditionally by the local criterion of
[Stacks, Tag 0FNT]; the only work is the change of spelling between the monoidal unit
`ULift A` of the lifted monoidal structure on `ModuleCat A` and `A` itself, which is
`Dualizing.relativeDualizingUnitIso`.

`hTensor` is the composite the module documentation of `SyntomicBaseChange` describes as not
assembled.  It is assembled here in four steps.

* The tensor formula of [Stacks, Tag 0BZU] — in its unconditional form
  `Dualizing.PolynomialPresentation.nonempty_upperShriekFunctor_iso_derivedTensorProduct` and its
  local-complete-intersection reading — gives
  `φ^! ≅ Dualizing.derivedTensorProductOver φ ω^•_{B/A}`, which is by definition the derived
  tensor functor `F` of the change-of-rings bundle of [Stacks, Tag 06Y6] at the representative of
  `ω^•_{B/A}` that the definition happens to choose.  That representative is replaced by a K-flat
  one by [Stacks, Tag 0BYK], `Dualizing.InvertibleKernel.derivedTensorIsoOfDerivedIso`; the
  K-flatness is what the last two steps need.
* The bundle's own `changeOfRings` field factors `F` as `B ⋙ G`: derived extension of scalars
  followed by derived tensoring over `B`.
* `Dualizing.changeOfRingsBIso` identifies `B` with
  `CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsGeneral`, the derived extension
  of scalars that the statement of Tag 0E4D is about.  Both are total left derived functors of
  degreewise extension of scalars — the two spellings
  `CochainComplex.extendScalarsLarge φ ⋙ DerivedCategory.Q` and
  `CochainComplex.DerivedExtensionScalars.extensionOfScalarsComplexGeneral φ` are the same
  functor — so `CategoryTheory.Functor.leftDerivedNatIso` applies with `Iso.refl`.
* `Dualizing.tensorFactorObjIso` identifies `G` with tensoring by `ω^•_{B/A}` in the symmetric
  monoidal structure of [Stacks, Tag 0FNQ].  This is where K-flatness of the representative `N`
  is used twice: tensoring with a K-flat complex preserves quasi-isomorphisms
  ([Stacks, Tag 06Y0]), so `G`'s counit is invertible on *every* complex
  (`Dualizing.isIso_alphaG`), and the comparison of the canonical derived tensor product of
  [Stacks, Tag 0BYI] with the ordinary one is available at a pair of K-flat complexes.  The
  identification is therefore made at one object at a time rather than as a natural
  isomorphism — `Dualizing.nonempty_tensorFactorObjIso`, which resolves the object by a K-flat
  complex — and that is all the statement of Tag 0E4D asks for.

The hypothesis-carrying statements of `SyntomicBaseChange` are kept: they take the inputs at a
single object `K` and an arbitrary presentation, which a consumer holding those inputs for its
own reasons can use without establishing the hypotheses of a case.

## References

* [Stacks Project, Tag 0E4D](https://stacks.math.columbia.edu/tag/0E4D)
* [Stacks Project, Tag 0E4C](https://stacks.math.columbia.edu/tag/0E4C)
* [Stacks Project, Tag 0E4B](https://stacks.math.columbia.edu/tag/0E4B)
* [Stacks Project, Tag 0E4A](https://stacks.math.columbia.edu/tag/0E4A)
* [Stacks Project, Tag 07EN](https://stacks.math.columbia.edu/tag/07EN)
* [Stacks Project, Tag 067J](https://stacks.math.columbia.edu/tag/067J)
* [Stacks Project, Tag 0BZU](https://stacks.math.columbia.edu/tag/0BZU)
* [Stacks Project, Tag 06Y6](https://stacks.math.columbia.edu/tag/06Y6)
* [Stacks Project, Tag 06Y0](https://stacks.math.columbia.edu/tag/06Y0)
* [Stacks Project, Tag 0BYI](https://stacks.math.columbia.edu/tag/0BYI)
* [Stacks Project, Tag 0BYK](https://stacks.math.columbia.edu/tag/0BYK)
* [Stacks Project, Tag 0FNQ](https://stacks.math.columbia.edu/tag/0FNQ)
* [Stacks Project, Tag 07D3](https://stacks.math.columbia.edu/tag/07D3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory
open CochainComplex.DerivedTensor CochainComplex.DerivedExtensionScalars

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace Dualizing

section

variable {A B : Type u} [CommRing A] [CommRing B] [IsNoetherianRing A] [IsNoetherianRing B]

/-! ### The invertibility input -/

/-- The relative dualizing complex read at the monoidal unit of the lifted monoidal structure on
`ModuleCat A` is the one read at `A` itself: the unit is `ULift A`, which is `A` as an
`A`-module. -/
def relativeDualizingUnitIso {f : A →+* B} (p : PolynomialPresentation f) :
    letI : MonoidalCategoryStruct (ModuleCat.{u} A) :=
      ModuleCat.liftedModuleMonoidalStruct.{u, u}
    letI : MonoidalCategory (ModuleCat.{u} A) := ModuleCat.liftedModuleMonoidal.{u, u}
    p.upperShriekFunctor.{u, u}.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
          (MonoidalCategoryStruct.tensorUnit (ModuleCat.{u} A))) ≅
      relativeDualizingUnit p :=
  p.upperShriekFunctor.{u, u}.mapIso
    ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).mapIso
      (ULift.moduleEquiv : ULift.{u} A ≃ₗ[A] A).toModuleIso)

omit [IsNoetherianRing B] in
/-- **The input `hInv` of Tag 0E4D, proved.**  For a local complete intersection homomorphism
`φ : A → B` of Noetherian rings and a polynomial presentation `p` of `φ`, the relative dualizing
complex `ω^•_{B/A} = φ^!(A)` is an invertible object of `D(B)`.

This is the invertibility clause of [Stacks, Tag 0E4B], which
`Dualizing.PolynomialPresentation`'s
`isInvertible_upperShriekFunctor_obj_unit_of_isLocalCompleteIntersection`
proves unconditionally, read at `A` rather than at the monoidal unit of the lifted monoidal
structure. -/
theorem isInvertible_relativeDualizingUnit_of_isLocalCompleteIntersection
    {f : A →+* B} (p : PolynomialPresentation f)
    (hlci : RingHom.IsLocalCompleteIntersection f) :
    letI := (DerivedCategory.Invertible.derivedCategory_symmetricMonoidalCategory B).choose
    MonoidalCategory.IsInvertible (relativeDualizingUnit p) := by
  let := (DerivedCategory.Invertible.derivedCategory_symmetricMonoidalCategory B).choose
  exact isInvertible_of_iso (relativeDualizingUnitIso p)
    (p.isInvertible_upperShriekFunctor_obj_unit_of_isLocalCompleteIntersection hlci)

/-! ### The change-of-rings projection of Tag 06Y6 -/

/-- The extension-of-scalars factor of the change-of-rings bundle of [Stacks, Tag 06Y6] is
derived extension of scalars.

Both are total left derived functors of degreewise extension of scalars followed by localization
— `CochainComplex.extendScalarsLarge φ ⋙ DerivedCategory.Q` and
`CochainComplex.DerivedExtensionScalars.extensionOfScalarsComplexGeneral φ` are two spellings of
one functor — so uniqueness of total left derived functors identifies them. -/
def changeOfRingsBIso (f : A →+* B) (N : CochainComplex (ModuleCat.{u} B) ℤ) :
    (canonicalDerivedTensorChangeOfRings.{u, u, u} f N).B ≅
      (derivedExtensionScalarsGeneral.{u, u, u} f).functor :=
  Functor.leftDerivedNatIso _ _
    (canonicalDerivedTensorChangeOfRings.{u, u, u} f N).alphaB
    (derivedExtensionScalarsGeneral.{u, u, u} f).comparison
    (HomologicalComplex.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ)) (Iso.refl _)

omit [IsNoetherianRing A] [IsNoetherianRing B] in
/-- For a K-flat tensor factor the counit of the tensoring factor of the change-of-rings bundle
of [Stacks, Tag 06Y6] is invertible on every complex, not only on the K-flat ones: tensoring with
a K-flat complex preserves quasi-isomorphisms by [Stacks, Tag 06Y0], so the functor being derived
already inverts the weak equivalences. -/
theorem isIso_alphaG (f : A →+* B) (N : CochainComplex (ModuleCat.{u} B) ℤ) (hN : N.KFlat) :
    IsIso (canonicalDerivedTensorChangeOfRings.{u, u, u} f N).alphaG := by
  refine Functor.isIso_of_isLeftDerivedFunctor_of_inverts _ _
    (W := HomologicalComplex.quasiIso (ModuleCat.{u} B) (ComplexShape.up ℤ)) ?_
  intro X Y g hg
  have : QuasiIso g := hg
  have h : QuasiIso ((CochainComplex.tensorRightLarge.{u, u} N).map g) :=
    CochainComplex.DerivedTensor.quasiIso_tright_map.{u, u} N hN g
  exact (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 h

/-- The tensoring factor of the change-of-rings bundle of [Stacks, Tag 06Y6] at a K-flat complex
`N`, evaluated at a K-flat complex `X`, is the monoidal tensor product of [Stacks, Tag 0FNQ] with
the class of `N`.

The bundle's counit is invertible at `X` by `Dualizing.isIso_alphaG`, and the canonical derived
tensor product of [Stacks, Tag 0BYI] is computed by the ordinary total tensor product at a pair
of K-flat complexes. -/
def tensorFactorObjIso (f : A →+* B) (N : CochainComplex (ModuleCat.{u} B) ℤ) (hN : N.KFlat)
    (X : CochainComplex (ModuleCat.{u} B) ℤ) (hX : X.KFlat) :
    letI := (DerivedCategory.Invertible.derivedCategory_symmetricMonoidalCategory B).choose
    (canonicalDerivedTensorChangeOfRings.{u, u, u} f N).G.obj (DerivedCategory.Q.obj X) ≅
      DerivedCategory.Q.obj X ⊗ DerivedCategory.Q.obj N := by
  letI := (DerivedCategory.Invertible.derivedCategory_symmetricMonoidalCategory B).choose
  let T := canonicalDerivedTensorChangeOfRings.{u, u, u} f N
  let S := canonicalSymmetricDerivedTensorProduct B
  let t := (DerivedCategory.Invertible.derivedCategory_symmetricMonoidalCategory
    B).choose_spec.choose_spec.choose
  have := isIso_alphaG f N hN
  refine asIso (T.alphaG.app X) ≪≫ ?_
  exact (S.tensorProduct.comparison X N hX hN).symm ≪≫
    ((t.app (DerivedCategory.Q.obj X)).app (DerivedCategory.Q.obj N)).symm

omit [IsNoetherianRing B] in
/-- Every object of the derived category is the image of a K-flat complex, by the K-flat
resolutions of [Stacks, Tag 06Y4]. -/
theorem exists_kFlat_rep (X : DerivedCategory (ModuleCat.{u} B)) :
    ∃ N : CochainComplex (ModuleCat.{u} B) ℤ,
      N.KFlat ∧ Nonempty (DerivedCategory.Q.obj N ≅ X) := by
  obtain ⟨N, a, hN, -, ha, -⟩ :=
    CochainComplex.KFlat.exists_kFlat_resolution.{u, u}
      (DerivedCategory.Q.objPreimage X)
  let : QuasiIso a := ha
  exact ⟨N, hN, ⟨asIso (DerivedCategory.Q.map a) ≪≫ DerivedCategory.Q.objObjPreimageIso X⟩⟩

omit [IsNoetherianRing A] [IsNoetherianRing B] in
/-- `Dualizing.tensorFactorObjIso` at an arbitrary object of `D(B)`, obtained by resolving it by
a K-flat complex.  Naturality is lost, and is not needed: Tag 0E4D asks for the identification at
one object. -/
theorem nonempty_tensorFactorObjIso (f : A →+* B)
    (N : CochainComplex (ModuleCat.{u} B) ℤ) (hN : N.KFlat)
    (X : DerivedCategory (ModuleCat.{u} B)) :
    letI := (DerivedCategory.Invertible.derivedCategory_symmetricMonoidalCategory B).choose
    Nonempty ((canonicalDerivedTensorChangeOfRings.{u, u, u} f N).G.obj X ≅
      X ⊗ DerivedCategory.Q.obj N) := by
  let := (DerivedCategory.Invertible.derivedCategory_symmetricMonoidalCategory B).choose
  obtain ⟨X₀, hX₀, ⟨eX⟩⟩ := exists_kFlat_rep X
  exact ⟨(canonicalDerivedTensorChangeOfRings.{u, u, u} f N).G.mapIso eX.symm ≪≫
    tensorFactorObjIso f N hN X₀ hX₀ ≪≫ tensorIso eX (Iso.refl _)⟩

/-! ### The tensor formula input -/

omit [IsNoetherianRing A] [IsNoetherianRing B] in
/-- **The input `hTensor` of Tag 0E4D, proved.**  Let `φ : A → B` be a homomorphism of Noetherian
rings and `p` a polynomial presentation of `φ` whose polynomial algebra makes `B` a perfect
module.  Then for every `K` in `D(A)`

`φ^!(K) ≅ (K ⊗_A^L B) ⊗_B ω^•_{B/A}`,

with `ω^•_{B/A} = φ^!(A)` the relative dualizing complex of `p` and `K ⊗_A^L B` the derived
extension of scalars of `K`.

This is the tensor formula of [Stacks, Tag 0BZU] composed with the change-of-rings projection of
[Stacks, Tag 06Y6]; the four steps are described in the module documentation. -/
theorem nonempty_upperShriekFunctor_obj_iso_derivedExtensionScalars_tensor_of_isPerfect
    (f : A →+* B) (p : PolynomialPresentation f)
    (hp : letI : Module p.Poly B := Module.compHom B p.toRingHom
      StacksDraft.Perfect.IsPerfectModule.{u, u, u + 1} (R := p.Poly) B)
    (K : DerivedCategory (ModuleCat.{u} A)) :
    letI := (DerivedCategory.Invertible.derivedCategory_symmetricMonoidalCategory B).choose
    Nonempty (p.upperShriekFunctor.{u, u}.obj K ≅
      ((derivedExtensionScalarsGeneral.{u, u, u} f).functor.obj K) ⊗
        relativeDualizingUnit p) := by
  let := (DerivedCategory.Invertible.derivedCategory_symmetricMonoidalCategory B).choose
  let : MonoidalCategoryStruct (ModuleCat.{u} A) :=
    ModuleCat.liftedModuleMonoidalStruct.{u, u}
  let : MonoidalCategory (ModuleCat.{u} A) := ModuleCat.liftedModuleMonoidal.{u, u}
  obtain ⟨eF⟩ := p.nonempty_upperShriekFunctor_iso_derivedTensorProduct.{u} hp
  let ω' := p.upperShriekFunctor.{u, u}.obj
    ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
      (MonoidalCategoryStruct.tensorUnit (ModuleCat.{u} A)))
  let Lc := (DerivedCategory.Qh (C := ModuleCat.{u} B)).objPreimage ω' |>.as
  obtain ⟨N, hN, ⟨eQa⟩⟩ := exists_kFlat_rep (DerivedCategory.Q.obj Lc)
  let S := canonicalDerivedTensorChangeOfRings.{u, u, u} f Lc
  let T := canonicalDerivedTensorChangeOfRings.{u, u, u} f N
  let eST : S.F ≅ T.F := InvertibleKernel.derivedTensorIsoOfDerivedIso.{u, u} f eQa.symm S T
  let eOmega : DerivedCategory.Q.obj N ≅ relativeDualizingUnit p :=
    eQa ≪≫ ((DerivedCategory.quotientCompQhIso (ModuleCat.{u} B)).app Lc).symm ≪≫
      (DerivedCategory.Qh (C := ModuleCat.{u} B)).objObjPreimageIso ω' ≪≫
      relativeDualizingUnitIso p
  obtain ⟨eG⟩ := nonempty_tensorFactorObjIso f N hN
    ((derivedExtensionScalarsGeneral.{u, u, u} f).functor.obj K)
  refine ⟨eF.app K ≪≫ eST.app K ≪≫ T.changeOfRings.app K ≪≫ ?_⟩
  exact T.G.mapIso ((changeOfRingsBIso f N).app K) ≪≫ eG ≪≫ tensorIso (Iso.refl _) eOmega

omit [IsNoetherianRing A] [IsNoetherianRing B] in
/-- **The input `hTensor` of Tag 0E4D for a local complete intersection, proved.**  A local
complete intersection homomorphism is perfect by [Stacks, Tag 07EN], so the polynomial algebra of
any presentation makes `B` a perfect module and
`Dualizing.nonempty_upperShriekFunctor_obj_iso_derivedExtensionScalars_tensor_of_isPerfect`
applies. -/
theorem nonempty_upperShriekFunctor_obj_iso_derivedExtensionScalars_tensor_of_lci
    (f : A →+* B) (p : PolynomialPresentation f)
    (hlci : RingHom.IsLocalCompleteIntersection f)
    (K : DerivedCategory (ModuleCat.{u} A)) :
    letI := (DerivedCategory.Invertible.derivedCategory_symmetricMonoidalCategory B).choose
    Nonempty (p.upperShriekFunctor.{u, u}.obj K ≅
      ((derivedExtensionScalarsGeneral.{u, u, u} f).functor.obj K) ⊗
        relativeDualizingUnit p) := by
  refine nonempty_upperShriekFunctor_obj_iso_derivedExtensionScalars_tensor_of_isPerfect f p ?_ K
  have := hlci.perfect
  algebraize [f]
  let : Module p.Poly B := Module.compHom B p.toRingHom
  exact (StacksDraft.Perfect.isPerfectModule_iff_exists_finite_projective_resolution B).mpr
    (Algebra.Perfect.exists_finite_projective_resolution
      (AlgHom.mk p.toRingHom fun r ↦ congrArg (· r) p.commutes) p.surjective)

/-! ### The three cases -/

/-- **Stacks Project, Tag 0E4D, case (1).**  Let `φ : A → B` be a syntomic homomorphism of
Noetherian rings which is surjective on spectra.  Then `K` in `D(A)` is a dualizing complex for
`A` if and only if `K ⊗_A^L B` is a dualizing complex for `B`.

Descent is [Stacks, Tag 0E4A] through the faithful flatness that syntomicity and surjectivity on
spectra give ([Stacks, Tag 07D3] and [Stacks, Tag 00HQ]).  Ascent is [Stacks, Tag 0BZL] at a
polynomial presentation of `φ`, which exists because a syntomic map is of finite type, together
with the two inputs proved above: syntomic is a local complete intersection, so
`Dualizing.isInvertible_relativeDualizingUnit_of_isLocalCompleteIntersection` supplies the
invertibility of `ω^•_{B/A}` and
`Dualizing.nonempty_upperShriekFunctor_obj_iso_derivedExtensionScalars_tensor_of_lci`
the tensor formula. -/
@[stacks 0E4D "case (1): A → B syntomic and surjective on spectra"]
theorem isDualizingComplex_iff_derivedExtensionScalars_of_syntomic_unconditional
    (f : A →+* B) (hsyn : letI := f.toAlgebra; Algebra.Syntomic A B)
    (hsurj : Function.Surjective (PrimeSpectrum.comap f))
    (K : DerivedCategory (ModuleCat.{u} A)) :
    IsDualizingComplex K ↔
      IsDualizingComplex ((derivedExtensionScalarsGeneral.{u, u, u} f).functor.obj K) := by
  have hlci : RingHom.IsLocalCompleteIntersection f :=
    ((RingHom.syntomic_iff_flat_and_isLocalCompleteIntersection f).mp hsyn).2
  obtain ⟨p⟩ := nonempty_polynomialPresentation f hlci.1
  exact isDualizingComplex_iff_derivedExtensionScalars_of_syntomic f hsyn hsurj p K
    (isInvertible_relativeDualizingUnit_of_isLocalCompleteIntersection p hlci)
    (nonempty_upperShriekFunctor_obj_iso_derivedExtensionScalars_tensor_of_lci
      f p hlci K)

/-- **Stacks Project, Tag 0E4D, case (2).**  Let `φ : A → B` be a faithfully flat local complete
intersection homomorphism of Noetherian rings.  Then `K` in `D(A)` is a dualizing complex for `A`
if and only if `K ⊗_A^L B` is a dualizing complex for `B`.

Descent is [Stacks, Tag 0E4A] at the given faithful flatness.  Ascent is [Stacks, Tag 0BZL] at a
polynomial presentation of `φ`, which exists because a local complete intersection is of finite
type, together with the two inputs proved above from `hlci`. -/
@[stacks 0E4D "case (2): A → B faithfully flat and a local complete intersection"]
theorem isDualizingComplex_iff_derivedExtensionScalars_of_faithfullyFlat_lci_unconditional
    (f : A →+* B) (hff : f.FaithfullyFlat)
    (hlci : RingHom.IsLocalCompleteIntersection f) (K : DerivedCategory (ModuleCat.{u} A)) :
    IsDualizingComplex K ↔
      IsDualizingComplex ((derivedExtensionScalarsGeneral.{u, u, u} f).functor.obj K) := by
  obtain ⟨p⟩ := nonempty_polynomialPresentation f hlci.1
  exact isDualizingComplex_iff_derivedExtensionScalars_of_faithfullyFlat_lci f hff hlci p K
    (isInvertible_relativeDualizingUnit_of_isLocalCompleteIntersection p hlci)
    (nonempty_upperShriekFunctor_obj_iso_derivedExtensionScalars_tensor_of_lci
      f p hlci K)

/-- **Stacks Project, Tag 0E4D, case (3).**  Let `A → B` be a faithfully flat homomorphism of
finite type of Noetherian rings and assume every fibre `B ⊗_A κ(q)` is Gorenstein.  Then `K` in
`D(A)` is a dualizing complex for `A` if and only if `K ⊗_A^L B` is a dualizing complex for `B`.

Descent is [Stacks, Tag 0E4A].  Ascent is [Stacks, Tag 0BZL] at a polynomial presentation `p`,
which exists by finite type, together with two inputs: the invertibility of `ω^•_{B/A}`, which
comes from the Gorenstein fibres by [Stacks, Tag 0E4C], and the tensor formula, whose only input
is perfectness of `B` over the polynomial algebra of `p`, supplied by the flatness contained in
`hff` through `Dualizing.PolynomialPresentation.isPerfectModule_of_flat`. -/
@[stacks 0E4D "case (3): A → B faithfully flat of finite type with Gorenstein fibres"]
theorem isDualizingComplex_iff_derivedExtensionScalars_of_gorensteinFibres_unconditional
    [Algebra A B] (hff : (algebraMap A B).FaithfullyFlat) [Algebra.FiniteType A B]
    (hGor : ∀ (q : Ideal A) [q.IsPrime],
      letI := Algebra.FiniteType.isNoetherianRing q.ResidueField (q.Fiber B)
      IsGorensteinRing (q.Fiber B))
    (K : DerivedCategory (ModuleCat.{u} A)) :
    IsDualizingComplex K ↔
      IsDualizingComplex
        ((derivedExtensionScalarsGeneral.{u, u, u} (algebraMap A B)).functor.obj K) := by
  obtain ⟨p⟩ := nonempty_polynomialPresentation (algebraMap A B)
    (RingHom.finiteType_algebraMap.mpr inferInstance)
  exact isDualizingComplex_iff_derivedExtensionScalars_of_gorensteinFibres hff p
    (fun q _ => hGor q) K
    (nonempty_upperShriekFunctor_obj_iso_derivedExtensionScalars_tensor_of_isPerfect
      (algebraMap A B) p (p.isPerfectModule_of_flat hff.flat) K)

end

end Dualizing

end
