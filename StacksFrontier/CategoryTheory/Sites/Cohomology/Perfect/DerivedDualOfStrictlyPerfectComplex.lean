module

public import Mathlib.CategoryTheory.Monoidal.Rigid.OfEquivalence
public import StacksFrontier.CategoryTheory.Monoidal.Rigid
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.MonoidalStrictBifunctor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.MonoidalStrictSheafTensorAgree
public import StacksFrontier.Homology.MapHomologicalComplexMonoidal
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.KFlatComplexesInTheDerivedCategory
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.LeftDualIsTheDerivedDual
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Duals.DualComplexOfModules
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.StrictlyPerfectIsKFlat

/-!
# The derived dual of a complex with a complex-level left dual

Let `(𝒞, 𝒪)` be a ringed site and let `ℱ^•` be a complex of `𝒪`-modules with a left dual `𝒢^•`
in the monoidal category of complexes of [Stacks, Tag 0FPQ] — for instance the dual complex
`𝒢^• = 𝑆heafHom^•(ℱ^•, 𝒪)` of [Stacks, Tag 0FPR]. If `ℱ^•` and `𝒢^•` are both K-flat then

`ℱ^∨ = R𝑆heafHom_𝒪(ℱ^•, 𝒪) ≅ Q 𝒢^•`  in  `D(𝒪)`,

the derived dual of [Stacks, Tag 08JD] being computed by the complex-level dual.

The complex-level pairing is `Stacks.SheafOfModules.Strict.exactPairingDualComplex`
([Stacks, Tag 0FPR]), and the identification of the derived dual with *any* left dual of `D(𝒪)`
is `AlgebraicGeometry.RingedSite.derivedDualIsoLeftDual` (the second assertion of
[Stacks, Tag 0FPV]). This file passes between them: the complex-level pairing is pushed through
`DerivedCategory.Q` to a pairing for the derived tensor product of [Stacks, Tag 0FPT].

## Main definitions

* `Stacks.SheafOfModules.DerivedMonoidal.idComplexMonoidal`: **the identity functor on
  complexes of `𝒪`-modules is monoidal from the tensor product of [Stacks, Tag 01CA] in its
  strict spelling to the same in its re-seated spelling.** This is
  `SheafOfModules.idMonoidalStrictToSheafTensor` carried to complexes by
  `CategoryTheory.Functor.mapHomologicalComplexMonoidal`.
* `Stacks.SheafOfModules.DerivedMonoidal.exactPairingSheafTensor`,
  `...exactPairingKFlatComplexes`, `...exactPairingQ`: **the complex-level exact pairing pushed
  through `DerivedCategory.Q`** to a pairing for the derived tensor product of
  [Stacks, Tag 0FPT].
* `AlgebraicGeometry.RingedSite.derivedDualIsoQOfExactPairing`: the identification
  `ℱ^∨ ≅ Q 𝒢^•` in `D(𝒪)`.
* `AlgebraicGeometry.RingedSite.derivedDualIsoQDualComplex`: the same at the dual complex of
  [Stacks, Tag 0FPR].

## Main results

* `AlgebraicGeometry.RingedSite.kFlatComplexes_of_isStrictlyPerfect`: a strictly perfect
  complex is K-flat in the form the subcategory of K-flat complexes of [Stacks, Tag 0FPT]
  reads K-flatness in.

## Implementation notes

**Why the identity functor appears.** `Mod(𝒪)` carries two monoidal structures whose tensor
product is the tensor product sheaf of [Stacks, Tag 01CA]:
`Stacks.SheafOfModules.Strict.monoidalCategory`, over which the duality cluster of
[Stacks, Tag 0FNY] and the dual complex of [Stacks, Tag 0FPR] are stated, and
`SheafOfModules.monoidalCategorySheafTensor`, over which the derived tensor product of
[Stacks, Tag 0FPT] is built. They are not the same term, so a `CategoryTheory.ExactPairing` for
one is not one for the other. The identity functor is monoidal between them
(`SheafOfModules.idMonoidalStrictToSheafTensor`, the two structures agreeing on every
structural morphism), and `idComplexMonoidal` below lifts that to complexes;
`CategoryTheory.ExactPairing.map` then transports the pairing. The agreement of the associators
and unitors is `SheafOfModules.associator_eq_strict`, `leftUnitor_eq_strict` and
`rightUnitor_eq_strict`.

**Why the instance arguments of `mapHomologicalComplexMonoidal` are passed positionally.** Both
monoidal structures live on the same type, so instance synthesis cannot be asked for them: a
query `MonoidalCategory (Mod 𝒪)` answers with the re-seated structure whichever one is wanted.
The whole application is therefore written out with `@`, with the strict structure supplied at
the source and the re-seated one at the target, and the auxiliary data of the strict structure
supplied by the three helper theorems above it, each of whose statement names the strict
structure explicitly so that its own synthesis is unambiguous.

**Why `Q` is only monoidal on K-flat complexes.** `D(𝒪)` is the localization of the K-flat
complexes at the quasi-isomorphisms between them, and the monoidal structure of
[Stacks, Tag 0FPT] descends along that localization; the functor carrying it is
`Stacks.SheafOfModules.DerivedMonoidal.kFlatComplexQ`, monoidal by
`Stacks.SheafOfModules.DerivedMonoidal.kFlatComplexQMonoidal`. So the pairing can only be pushed
forward once both complexes are known to be K-flat, which is why
`derivedDualIsoQOfExactPairing` carries those two hypotheses.

**K-flatness of the two complexes.** `derivedDualIsoQDualComplex` takes K-flatness of `ℱ^•` and
of the dual complex as hypotheses. K-flatness of `ℱ^•` holds whenever `ℱ^•` is strictly perfect,
by `kFlatComplexes_of_isStrictlyPerfect`.

The statements below are the composite of [Stacks, Tag 0FPR] (or [Stacks, Tag 0FPS]) with the
second assertion of [Stacks, Tag 0FPV], mediated by the monoidality of the K-flat localization
that [Stacks, Tag 0FPT] is built from.

## References

* [Stacks Project, Tag 0FPQ](https://stacks.math.columbia.edu/tag/0FPQ)
* [Stacks Project, Tag 0FPR](https://stacks.math.columbia.edu/tag/0FPR)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
* [Stacks Project, Tag 0FPV](https://stacks.math.columbia.edu/tag/0FPV)
* [Stacks Project, Tag 08JD](https://stacks.math.columbia.edu/tag/08JD)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

universe d u

namespace Stacks.SheafOfModules.DerivedMonoidal

variable {C : Type u} [SmallCategory.{u} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{u})
variable [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

attribute [local instance] SheafOfModules.monoidalCategorySheafTensor
  SheafOfModules.symmetricCategorySheafTensor SheafOfModules.monoidalPreadditiveSheafTensor
  SheafOfModules.monoidalClosedSheafTensor
  SheafOfModules.preservesColimit_tensorRight_sheafTensor
  CochainComplex.symmetricCategory

/-! ### The identity functor on complexes, between the two tensor products of Tag 01CA -/

/-- The additivity and graded-tensor instances of the tensor product of [Stacks, Tag 01CA], read
at the strict monoidal structure; the three public theorems below are its components. -/
private theorem strict_additive_and_hasTensor :
    @Functor.Additive (Mod R) (Mod R ⥤ Mod R) _ _ _ _
        (@curriedTensor (Mod R) _ (Strict.monoidalUnderlyingRingSheaf R)) ∧
      (∀ X₁ : Mod R, @Functor.Additive (Mod R) (Mod R) _ _ _ _
        ((@curriedTensor (Mod R) _ (Strict.monoidalUnderlyingRingSheaf R)).obj X₁)) ∧
      ∀ X₁ X₂ : GradedObject ℤ (Mod R),
        @GradedObject.HasTensor ℤ _ (Mod R) _ (Strict.monoidalUnderlyingRingSheaf R) X₁ X₂ := by
  let : MonoidalCategory (Mod R) := Strict.monoidalUnderlyingRingSheaf R
  let : MonoidalPreadditive (Mod R) := Strict.monoidalPreadditiveRingSheaf R
  exact ⟨inferInstance, fun _ => inferInstance, fun _ _ => inferInstance⟩

/-- The tensor product of [Stacks, Tag 01CA] is additive in its first variable, read at the
strict monoidal structure. -/
theorem curriedTensorStrictAdditive :
    @Functor.Additive (Mod R) (Mod R ⥤ Mod R) _ _ _ _
      (@curriedTensor (Mod R) _ (Strict.monoidalUnderlyingRingSheaf R)) :=
  (strict_additive_and_hasTensor R).1

/-- The tensor product of [Stacks, Tag 01CA] is additive in its second variable, read at the
strict monoidal structure. -/
theorem curriedTensorStrictObjAdditive (X₁ : Mod R) :
    @Functor.Additive (Mod R) (Mod R) _ _ _ _
      ((@curriedTensor (Mod R) _ (Strict.monoidalUnderlyingRingSheaf R)).obj X₁) :=
  (strict_additive_and_hasTensor R).2.1 X₁

/-- The graded tensor product of two graded `𝒪`-modules exists for the tensor product of
[Stacks, Tag 01CA], read at the strict monoidal structure. -/
theorem hasTensorStrict (X₁ X₂ : GradedObject ℤ (Mod R)) :
    @GradedObject.HasTensor ℤ _ (Mod R) _ (Strict.monoidalUnderlyingRingSheaf R) X₁ X₂ :=
  (strict_additive_and_hasTensor R).2.2 X₁ X₂

/-- **The identity functor on complexes of `𝒪`-modules is monoidal from the total complex of
the tensor product of [Stacks, Tag 01CA] in its strict spelling to the same in its re-seated
spelling.** On modules this is `SheafOfModules.idMonoidalStrictToSheafTensor`, the two
structures agreeing on every structural morphism; here it is carried to complexes by
`CategoryTheory.Functor.mapHomologicalComplexMonoidal`. -/
@[instance_reducible]
def idComplexMonoidal :
    @Functor.Monoidal (Complexes R) _ (Strict.monoidalCategoryCochainComplex R)
      (Complexes R) _ _ ((𝟭 (Mod R)).mapHomologicalComplex (ComplexShape.up ℤ)) :=
  @Functor.mapHomologicalComplexMonoidal
    (Mod R) (Mod R) inferInstance inferInstance
    (Strict.monoidalUnderlyingRingSheaf R) (SheafOfModules.monoidalCategorySheafTensor R)
    inferInstance inferInstance inferInstance inferInstance
    (curriedTensorStrictAdditive R) (curriedTensorStrictObjAdditive R)
    inferInstance inferInstance
    ℤ inferInstance inferInstance (ComplexShape.up ℤ) inferInstance
    (𝟭 (Mod R)) inferInstance (SheafOfModules.idMonoidalStrictToSheafTensor R)
    (hasTensorStrict R)
    (fun X₁ => Strict.preservesColimit_tensorLeft R _ X₁)
    (fun X₂ => Strict.preservesColimit_tensorRight R _ X₂)
    (Strict.hasTensor₄ObjExt R) (Strict.hasGoodTensor₁₂Tensor R)
    (Strict.hasGoodTensorTensor₂₃ R)
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    inferInstance

/-! ### The pairing pushed through `Q` -/

variable [HasDerivedCategory.{d} (Mod R)]

attribute [local instance] derivedMonoidal derivedSymmetric kFlatQ_isLocalization
  CochainComplex.KFlatMonoidal.homotopyMonoidal CochainComplex.KFlatMonoidal.homotopyBraided
  homQMonoidal homQBraided kFlatQMonoidal kFlatQBraided kFlatQuotientMonoidal
  kFlatQuotientLaxBraided kFlatComplexQMonoidal

/-- **An exact pairing of complexes of `𝒪`-modules for the strict tensor product of
[Stacks, Tag 01CA] is one for the re-seated tensor product**, the one the derived tensor product
of [Stacks, Tag 0FPT] is built on. It is the image of the pairing under the identity functor,
`idComplexMonoidal`. -/
@[instance_reducible]
def exactPairingSheafTensor (F G : Complexes R)
    (p : @ExactPairing (Complexes R) _ (Strict.monoidalCategoryCochainComplex R) F G) :
    ExactPairing F G :=
  letI := @ExactPairing.map (Complexes R) (Complexes R) _ _
    (Strict.monoidalCategoryCochainComplex R) _
    ((𝟭 (Mod R)).mapHomologicalComplex (ComplexShape.up ℤ)) (idComplexMonoidal R) F G p
  exactPairingCongr
    ((Functor.mapHomologicalComplexIdIso (Mod R) (ComplexShape.up ℤ)).app F).symm
    ((Functor.mapHomologicalComplexIdIso (Mod R) (ComplexShape.up ℤ)).app G).symm

/-- **An exact pairing of K-flat complexes, read in the monoidal subcategory of K-flat
complexes.** The inclusion of that subcategory is fully faithful and monoidal, so the pairing is
reflected along it by `CategoryTheory.ExactPairing.ofFullyFaithful`. -/
@[instance_reducible]
def exactPairingKFlatComplexes (F G : Complexes R)
    (hF : KFlatComplexes R F) (hG : KFlatComplexes R G)
    (p : @ExactPairing (Complexes R) _ (Strict.monoidalCategoryCochainComplex R) F G) :
    ExactPairing (⟨F, hF⟩ : (KFlatComplexes R).FullSubcategory) ⟨G, hG⟩ :=
  letI : ExactPairing ((KFlatComplexes R).ι.obj ⟨F, hF⟩) ((KFlatComplexes R).ι.obj ⟨G, hG⟩) :=
    exactPairingSheafTensor R F G p
  ExactPairing.ofFullyFaithful (KFlatComplexes R).ι _ _

/-- **The complex-level exact pairing pushed through `DerivedCategory.Q`.** If `ℱ^•` and `𝒢^•`
are K-flat complexes of `𝒪`-modules and `𝒢^•` is a left dual of `ℱ^•` in the monoidal category
of complexes of [Stacks, Tag 0FPQ], then `Q 𝒢^•` is a left dual of `Q ℱ^•` for the derived
tensor product of [Stacks, Tag 0FPT].

This is the image of the pairing under
`Stacks.SheafOfModules.DerivedMonoidal.kFlatComplexQ`, which is monoidal because `D(𝒪)` is the
monoidal localization of the K-flat complexes at the quasi-isomorphisms between them. -/
@[instance_reducible]
def exactPairingQ (F G : Complexes R)
    (hF : KFlatComplexes R F) (hG : KFlatComplexes R G)
    (p : @ExactPairing (Complexes R) _ (Strict.monoidalCategoryCochainComplex R) F G) :
    ExactPairing (DerivedCategory.Q.obj F) (DerivedCategory.Q.obj G) :=
  letI := exactPairingKFlatComplexes R F G hF hG p
  ExactPairing.map (kFlatComplexQ R) ⟨F, hF⟩ ⟨G, hG⟩

end Stacks.SheafOfModules.DerivedMonoidal

/-! ### The derived dual -/

namespace AlgebraicGeometry.RingedSite

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat
attribute [local instance] SheafOfModules.monoidalCategorySheafTensor
  SheafOfModules.symmetricCategorySheafTensor SheafOfModules.monoidalPreadditiveSheafTensor
  SheafOfModules.monoidalClosedSheafTensor
  SheafOfModules.preservesColimit_tensorRight_sheafTensor
  CochainComplex.symmetricCategory

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **A strictly perfect complex of `𝒪`-modules is K-flat**, in the form the subcategory of
K-flat complexes that the derived tensor product of [Stacks, Tag 0FPT] is built from reads
K-flatness in. This is `AlgebraicGeometry.RingedSite.kFlat_of_isStrictlyPerfect`, the two
spellings of K-flatness being the same proposition. -/
theorem kFlatComplexes_of_isStrictlyPerfect
    (F : CochainComplex (Stacks.SheafOfModules.DerivedMonoidal.Mod X.O) ℤ)
    (hF : IsStrictlyPerfect (Stacks.SheafOfModules.Tensor.ringSheaf X.O) F) :
    Stacks.SheafOfModules.DerivedMonoidal.KFlatComplexes X.O F :=
  kFlat_of_isStrictlyPerfect X F hF

variable
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u,
    u} X.O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]

/-- **The derived dual of a complex with a complex-level left dual is the image of that dual.**
Let `ℱ^•` and `𝒢^•` be K-flat complexes of `𝒪`-modules and let `𝒢^•` be a left dual of `ℱ^•` in
the monoidal category of complexes of [Stacks, Tag 0FPQ]. Then

`ℱ^∨ = R𝑆heafHom_𝒪(ℱ^•, 𝒪) ≅ Q 𝒢^•`

in `D(𝒪)`, the derived dual being the one of [Stacks, Tag 08JD].

The pairing is carried into `D(𝒪)` by
`Stacks.SheafOfModules.DerivedMonoidal.exactPairingQ`, and the second assertion of
[Stacks, Tag 0FPV] — `AlgebraicGeometry.RingedSite.derivedDualIsoLeftDual` — then identifies the
derived dual with it. -/
def derivedDualIsoQOfExactPairing
    (F G : CochainComplex (Stacks.SheafOfModules.DerivedMonoidal.Mod X.O) ℤ)
    (hF : Stacks.SheafOfModules.DerivedMonoidal.KFlatComplexes X.O F)
    (hG : Stacks.SheafOfModules.DerivedMonoidal.KFlatComplexes X.O G)
    (p : @ExactPairing _ _ (Stacks.SheafOfModules.Strict.monoidalCategoryCochainComplex X.O) F G) :
    derivedDual X (DerivedCategory.Q.obj F) ≅ DerivedCategory.Q.obj G :=
  letI := Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal X.O
  letI := Stacks.SheafOfModules.DerivedMonoidal.exactPairingQ X.O F G hF hG p
  derivedDualIsoLeftDual (DerivedCategory.Q.obj F) (DerivedCategory.Q.obj G)

/-- **The derived dual is computed by the dual complex of [Stacks, Tag 0FPR].** Let `ℱ^•` be a
complex of `𝒪`-modules whose terms are, locally on the site, direct summands of finite free
`𝒪`-modules, and which vanishes outside a finite set `s` of degrees, and let

`𝒢^• = 𝑆heafHom^•(ℱ^•, 𝒪)`

be the dual complex of [Stacks, Tag 0FPR], with its signed-transpose differential. If `ℱ^•` and
`𝒢^•` are K-flat then the derived dual `ℱ^∨ = R𝑆heafHom_𝒪(ℱ^•, 𝒪)` of [Stacks, Tag 08JD] is
`Q 𝒢^•`. -/
def derivedDualIsoQDualComplex
    (F : CochainComplex (Stacks.SheafOfModules.DerivedMonoidal.Mod X.O) ℤ)
    (hterm : ∀ n : ℤ, Stacks.SheafOfModules.IsLocallyDirectSummandOfFiniteFree X.O.obj
      (Stacks.SheafOfModules.Strict.isSheaf_ringSheaf X.O) (F.X n))
    (s : Finset ℤ) (hb : ∀ m, m ∉ s → IsZero (F.X m))
    (hF : Stacks.SheafOfModules.DerivedMonoidal.KFlatComplexes X.O F)
    (hG : Stacks.SheafOfModules.DerivedMonoidal.KFlatComplexes X.O
      (Stacks.SheafOfModules.Strict.dualComplex X.O F hterm)) :
    derivedDual X (DerivedCategory.Q.obj F) ≅
      DerivedCategory.Q.obj (Stacks.SheafOfModules.Strict.dualComplex X.O F hterm) :=
  derivedDualIsoQOfExactPairing X F _ hF hG
    (Stacks.SheafOfModules.Strict.exactPairingDualComplex X.O F hterm s hb)

end AlgebraicGeometry.RingedSite

end
