module

public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.CompactObjects.ExtensionByZeroUnitAtTerminal
public import StacksFrontier.CategoryTheory.Sites.Cohomology.CompactObjects.PerfectObjectsAreCompact
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.CanonicalBifunctorComparison
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.BoundedBelowTensor
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedTensorCoproducts
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.PerfectDualSiteGlobalSections
import StacksCore.Tactic.StacksAttribute

/-!
# The reduction of Stacks 09JC, carried out

Let `(C, O)` be a ringed site with a final object `X₀` and let `K` be a perfect object of
`D(O)`. The proofs of **Stacks 09JC** and of **Stacks 09J7** open by replacing morphisms out of
`K` by morphisms out of `j_{X₀!}O_{X₀}`:

`Hom_{D(O)}(K, N) = H⁰(X₀, K^∨ ⊗^L_O N) = Hom_{D(O)}(j_{X₀!}O_{X₀}, N ⊗^L_O K^∨)`,

functorially in `N`, where `K^∨ ⊗^L_O -` commutes with direct sums. In
`StacksFrontier.CategoryTheory.Sites.Cohomology.CompactObjects.PerfectObjectsAreCompact` that
replacement is an explicit hypothesis `hreduce` of both clauses. This file **produces it**, so
that clause (b) of Stacks 09JC becomes unconditional.

Three inputs are already in the library and are only assembled here: the bijectivity of the map of
Stacks 08JD for a perfect source (`bijective_derivedTensorDualGlobalSectionsMap_of_isPerfect`,
Stacks 08JJ), its compatibility with composition
(`derivedDualHomFromStructureSheafEquiv_naturality`, Stacks 08JA in the target), and the
identification of the extension by zero of the unit at a final object with the structure sheaf
(`derivedExtensionByZeroUnitIsoStructureSheaf`). The remaining input is the commutation
of `- ⊗^L_O K^∨` with direct sums, and it is proved below as
`preservesColimitsOfShape_derivedTensorFlip`.

## Main results

* `AlgebraicGeometry.RingedSite.curriedTensorIsoDerivedTensor`: the tensor product of the
  monoidal structure of Stacks 0FPT on `D(O)` is the bifunctor of any derived tensor product in
  the sense of Stacks 06YU.
* `AlgebraicGeometry.RingedSite.preservesColimitsOfShape_derivedTensorFlip`: **`- ⊗^L_O E`
  commutes with direct sums**, for every object `E` of `D(O)` and every index type in the
  universe of the site.
* `AlgebraicGeometry.RingedSite.derivedDualHomEquivOfIsoStructureSheaf` and
  `…_naturality`: the reduction, with any object isomorphic to `O[0]` as the source.
* `AlgebraicGeometry.RingedSite.isCompactObject_of_isPerfect_of_isTerminal`: **Stacks 09JC (b)
  with the reduction discharged** — a perfect object of `D(O)` is compact as soon as cohomology
  over the final object has finite cohomological dimension and commutes with direct sums.

## Implementation notes

The commutation with direct sums is obtained from
`Stacks.SheafOfModules.DerivedMonoidal.preservesColimitsOfShape_derivedTensorLeft`, which proves
it for `tensorLeft` at the monoidal structure `derivedMonoidal`, in two steps: the commutativity
constraint `derivedSymmetric` moves it to `tensorRight`, and
`curriedTensorIsoDerivedTensor` — the composite of
`Stacks.SheafOfModules.DerivedMonoidal.derivedTensorBifunctorIso` with
`Stacks.SheafOfModules.DerivedMonoidal.derivedBifunctorTensorIso` read through
`derivedTensorProductDatumOfSite` — transports it to `T.tensor.flip.obj E` for an arbitrary
`Stacks.SheafOfModules.DerivedTensorProduct`. Only the K-flat comparison fields of `T` are used,
so no choice of derived tensor product is privileged; the final statement instantiates `T` at
`Stacks.SheafOfModules.canonicalDerivedTensorProduct` and is therefore free of it.

`HasDerivedCategory.standard` is installed at priority `10000`, not as a plain
`local instance`: the locally small model `SheafOfModules.hasDerivedCategory` was once a global
instance of the import closure, and at the default priority that model won, after which
`derivedDualHomFromStructureSheafEquiv` — proved for the standard model — no longer applies.

The index type of the direct sums is in the universe of the site, which is the universe in which
`Stacks.SmallDerivedCategory.derivedCategoryQ_preservesCoproducts` is available: sheaves of
`O`-modules are Grothendieck abelian relative to that universe and no larger one.

## References

* [Stacks Project, Lemma 20.50.9 (Tag 09JC)](https://stacks.math.columbia.edu/tag/09JC)
* [Stacks Project, Lemma 36.6.2 (Tag 09J7)](https://stacks.math.columbia.edu/tag/09J7)
* [Stacks Project, Tag 08JJ](https://stacks.math.columbia.edu/tag/08JJ)
* [Stacks Project, Tag 08JD](https://stacks.math.columbia.edu/tag/08JD)
* [Stacks Project, Tag 094D](https://stacks.math.columbia.edu/tag/094D)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u c

namespace CategoryTheory.Functor

/-- **An isomorphism of bifunctors, read at a fixed second argument.** For `F G : A ⥤ B ⥤ E`
and `D : B`, an isomorphism `F ≅ G` gives an isomorphism of the functors `F(-)(D)` and
`G(-)(D)`, which is `CategoryTheory.flipFunctor` applied to it and evaluated at `D`, written at
the `Functor.flip` spelling so that instance search sees it. -/
def flipObjIso {A B E : Type*} [Category A] [Category B] [Category E]
    {F G : A ⥤ B ⥤ E} (e : F ≅ G) (D : B) : F.flip.obj D ≅ G.flip.obj D :=
  ((flipFunctor A B E).mapIso e).app D

end CategoryTheory.Functor

namespace AlgebraicGeometry.RingedSite

attribute [local instance 10000] HasDerivedCategory.standard

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ V : X.C, HasSheafify (X.J.over V) AddCommGrpCat.{u}]
  [∀ V : X.C, (X.J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ V : X.C, (X.J.over V).HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
  [∀ V : X.C, (X.J.over V).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]
  (T : Stacks.SheafOfModules.DerivedTensorProduct X)

/-! ### The derived tensor product commutes with direct sums in each variable -/

/-- **The tensor product of the monoidal structure of Stacks 0FPT on `D(O)` is the bifunctor of
any derived tensor product of Stacks 06YU.** Both are compared with
`CochainComplex.KFlatBifunctor.derivedBifunctor`, which descends the total tensor complex of
K-flat complexes; the second comparison uses only the K-flat comparison fields of `T`. -/
def curriedTensorIsoDerivedTensor :
    letI := Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal X.O
    @MonoidalCategory.curriedTensor
        (Stacks.SheafOfModules.DerivedMonoidal.DerivedModules X.O) _ _ ≅ T.tensor :=
  Stacks.SheafOfModules.DerivedMonoidal.derivedTensorBifunctorIso X.O ≪≫
    Stacks.SheafOfModules.DerivedMonoidal.derivedBifunctorTensorIso X.O
      (derivedTensorProductDatumOfSite X T)

omit [∀ V : X.C, HasSheafify (X.J.over V) AddCommGrpCat.{u}]
  [∀ V : X.C, (X.J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ V : X.C, (X.J.over V).HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
  [∀ V : X.C, (X.J.over V).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- **`- ⊗^L_O E` commutes with direct sums.** This is the input of Stacks 09JC's reduction that
the library did not have: `Stacks.SheafOfModules.DerivedMonoidal`
`.preservesColimitsOfShape_derivedTensorLeft` proves it for `E ⊗^L_O -` at the monoidal
structure of Stacks 0FPT, the commutativity constraint of that structure transposes it to the
other variable, and `curriedTensorIsoDerivedTensor` carries it to the bifunctor of `T`.

The index type lies in the universe of the site, in which the localization functor
`Q : C(Mod(O)) ⥤ D(Mod(O))` preserves direct sums. -/
theorem preservesColimitsOfShape_derivedTensorFlip
    (E : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (ι : Type u) :
    PreservesColimitsOfShape (Discrete ι) (T.tensor.flip.obj E) := by
  let := Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal X.O
  let := Stacks.SheafOfModules.DerivedMonoidal.derivedSymmetric X.O
  let := Stacks.SheafOfModules.DerivedMonoidal.preservesColimitsOfShape_derivedTensorLeft
    X.O E ι
  have hright : PreservesColimitsOfShape (Discrete ι) (MonoidalCategory.tensorRight E) :=
    preservesColimitsOfShape_of_natIso (BraidedCategory.tensorLeftIsoTensorRight E)
  exact preservesColimitsOfShape_of_natIso
    (Functor.flipObjIso (curriedTensorIsoDerivedTensor X T) E)

/-! ### The reduction -/

/-- The functor `T = - ⊗^L_O K^∨` of Stacks 09JC's reduction. -/
abbrev derivedTensorDualFunctor
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⥤
      DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
  T.tensor.flip.obj (derivedDual X K)

/-- **The reduction of Stacks 09JC.** For a perfect `K` and any object `A` isomorphic to `O[0]`
in `D(O)`, morphisms `K ⟶ N` are morphisms `A ⟶ N ⊗^L_O K^∨`, as abelian groups.

This is `derivedDualHomFromStructureSheafEquiv` — Stacks 08JJ composed with
`H⁰(C, -) = Hom(O, -)` — with the source object transported along `φ`. The intended `A` is the
extension by zero of the unit at a final object, in either of the two spellings of it that the
two clauses of Stacks 09JC use. -/
def derivedDualHomEquivOfIsoStructureSheaf
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hK : X.IsPerfect K)
    {A : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (φ : A ≅ derivedStructureSheaf X)
    (N : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    (K ⟶ N) ≃+ (A ⟶ (derivedTensorDualFunctor X T K).obj N) :=
  (derivedDualHomFromStructureSheafEquiv X T K N hK).trans
    { toFun g := φ.hom ≫ g
      invFun g := φ.inv ≫ g
      left_inv g := by simp
      right_inv g := by simp
      map_add' _ _ := by simp }

omit [∀ V : X.C, (X.J.over V).HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})] in
/-- **The reduction is compatible with composition**: it carries postcomposition with
`g : N ⟶ N'` to postcomposition with `N ⊗^L_O K^∨ ⟶ N' ⊗^L_O K^∨`. This is the clause Stacks
09JC asks of the reduction, and it is `derivedDualHomFromStructureSheafEquiv_naturality`
followed by associativity. -/
theorem derivedDualHomEquivOfIsoStructureSheaf_naturality
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hK : X.IsPerfect K)
    {A : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (φ : A ≅ derivedStructureSheaf X)
    {N N' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (f : K ⟶ N) (g : N ⟶ N') :
    derivedDualHomEquivOfIsoStructureSheaf X T K hK φ N' (f ≫ g) =
      derivedDualHomEquivOfIsoStructureSheaf X T K hK φ N f ≫
        (derivedTensorDualFunctor X T K).map g := by
  change φ.hom ≫ derivedDualHomFromStructureSheafEquiv X T K N' hK (f ≫ g) =
    (φ.hom ≫ derivedDualHomFromStructureSheafEquiv X T K N hK f) ≫
      (T.tensor.map g).app (derivedDual X K)
  rw [derivedDualHomFromStructureSheafEquiv_naturality X T K hK f g, Category.assoc]

/-! ### Stacks 09JC (b), with the reduction discharged -/

/-- Sheaves of modules on a ringed site have enough injectives. Reinstated from the public
statement because the module proving Stacks 094D declares it only locally. -/
local instance perfectDualModulesEnoughInjectives :
    EnoughInjectives (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
  Stacks.Cohomology.enoughInjectives_of_ringedSite.{u, u, u, u} X

attribute [local instance] Stacks.Cohomology.perfectCompactEvaluationAdditive

omit [∀ V : X.C, (X.J.over V).HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})] in
/-- **Stacks 09JC (b).** Let `(C, O)` be a ringed site with a final object `X₀` and let `K` be a
perfect object of `D(O)`. If `(C, O)` has finite cohomological dimension, that is
`H^p(X₀, F) = 0` for every `O`-module `F` and every `p` beyond a fixed bound, and if the
functors `F ↦ H^p(X₀, F)` commute with direct sums, then `K` is a compact object of `D(O)`.

Unlike `Stacks.Cohomology.isCompactObject_of_isPerfect` this carries no hypothesis standing in
for the reduction of Stacks 08JJ: the functor is `- ⊗^L_O K^∨` for the canonical derived tensor
product of Stacks 06YU, it commutes with direct sums by
`preservesColimitsOfShape_derivedTensorFlip`, and the natural bijection is
`derivedDualHomEquivOfIsoStructureSheaf` at the identification
`derivedExtensionByZeroUnitIsoStructureSheaf` of `j_{X₀!}O_{X₀}[0]` with `O[0]`. Perfectness of
`K` is used exactly where the source uses it, to produce that bijection. What is still a
hypothesis, as in the conditional form, is the commutation `hsums` of the higher cohomology
functors with direct sums, which the source supplies from Stacks 0739. -/
@[stacks 09JC "(b) unbounded compactness of a perfect object, with the 08JJ reduction DISCHARGED \
rather than assumed; the 0739 commutation of the cohomology functors with direct sums is still a \
hypothesis here, and is discharged from hypotheses (2) and (3) of the tag in \
Stacks.Cohomology.QuasiCompactSite.hom_coproduct_bijective_and_isCompactObject_of_isPerfect, \
which states both clauses"]
theorem isCompactObject_of_isPerfect_of_isTerminal (X₀ : X.C) (hX₀ : IsTerminal X₀)
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hK : X.IsPerfect K)
    (hcd : ∃ d : ℤ, ∀ (p : ℕ)
      (G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)), d < (p : ℤ) →
      IsZero (((SheafOfModules.evaluation.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
        (op X₀)).rightDerived p).obj G))
    (hsums : ∀ (p : ℕ) (I : Type u), PreservesColimitsOfShape (Discrete I)
      ((SheafOfModules.evaluation.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
        (op X₀)).rightDerived p)) :
    IsCompactObject.{u} K := by
  set T : Stacks.SheafOfModules.DerivedTensorProduct X :=
    Stacks.SheafOfModules.canonicalDerivedTensorProduct X with hT
  let : ∀ I : Type u,
      PreservesColimitsOfShape (Discrete I) (derivedTensorDualFunctor X T K) :=
    fun I => preservesColimitsOfShape_derivedTensorFlip X T _ I
  exact Stacks.Cohomology.isCompactObject_of_reduction X X₀ K hcd hsums
    (derivedTensorDualFunctor X T K)
    (derivedDualHomEquivOfIsoStructureSheaf X T K hK
      (derivedExtensionByZeroUnitIsoStructureSheaf X X₀ hX₀))
    (fun f g => derivedDualHomEquivOfIsoStructureSheaf_naturality X T K hK _ f g)


/-! ### Stacks 09JC (a), reduced to the Tor amplitude of the dual -/

/-- **The derived tensor product is symmetric**, in the spelling of an arbitrary derived tensor
product of Stacks 06YU: the commutativity constraint of the monoidal structure of Stacks 0FPT
read through `curriedTensorIsoDerivedTensor`. -/
def derivedTensorSymmetryIso
    (A B : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    (T.tensor.obj A).obj B ≅ (T.tensor.obj B).obj A :=
  letI := Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal X.O
  letI := Stacks.SheafOfModules.DerivedMonoidal.derivedSymmetric X.O
  (((curriedTensorIsoDerivedTensor X T).app A).app B).symm ≪≫
    BraidedCategory.braiding A B ≪≫ (((curriedTensorIsoDerivedTensor X T).app B).app A)

omit [∀ V : X.C, HasSheafify (X.J.over V) AddCommGrpCat.{u}]
  [∀ V : X.C, (X.J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ V : X.C, (X.J.over V).HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
  [∀ V : X.C, (X.J.over V).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- **A cohomologically bounded-below object tensored with an object of finite Tor dimension is
bounded below**, with the factor of finite Tor dimension in the *second* variable, which is
where Stacks 09JC's reduction puts the dual `K^∨`.
`Stacks.SheafOfModules.DerivedTensorProduct.isBoundedBelow_tensor_of_hasFiniteTorDimension`
puts it in the first, and `derivedTensorSymmetryIso` exchanges them. -/
@[sga "6 I 5.3" "partial"]
theorem isBoundedBelow_derivedTensorFlip_of_hasFiniteTorDimension
    (E W : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hE : Stacks.SheafOfModules.DerivedTensorProduct.HasFiniteTorDimension T E)
    (hW : DerivedCategoryB.IsBoundedBelow W) :
    DerivedCategoryB.IsBoundedBelow ((T.tensor.obj W).obj E) := by
  obtain ⟨n, hn⟩ :=
    Stacks.SheafOfModules.DerivedTensorProduct.isBoundedBelow_tensor_of_hasFiniteTorDimension
      T E W hE hW
  exact ⟨n, fun i hi => (hn i hi).of_iso
    ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) i).mapIso
      (derivedTensorSymmetryIso X T W E))⟩

omit [∀ V : X.C, (X.J.over V).HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})] in
/-- **Stacks 09JC (a), with every component of the reduction discharged except the Tor
amplitude of the dual.** Let `B` and `Cov` be the covering data of Stacks 0G22, let `X₀` be a
final object of `C` lying in `B`, let `K` be a perfect object of `D(O)` whose dual has finite
Tor dimension, and let `M : I → D(O)` be a family with a bounded-below coproduct. Then morphisms
from `K` into that coproduct are finite sums.

Against `Stacks.Cohomology.hom_coproduct_bijective_of_isPerfect` the four-component hypothesis
`hreduce` is gone, and in its place stands the single mathematical input `hdual`. The functor is
`- ⊗^L_O K^∨`; it preserves the coproduct by
`preservesColimitsOfShape_derivedTensorFlip`, the natural bijection and its compatibility with
composition are `derivedDualHomEquivOfIsoStructureSheaf` and `…_naturality` at
`derivedOverExtensionByZeroUnitIsoStructureSheaf`, and the boundedness below of
`(⨁ Mᵢ) ⊗^L_O K^∨` is `isBoundedBelow_derivedTensorFlip_of_hasFiniteTorDimension` from `hdual`
and the source's own hypothesis that `⨁ Mᵢ` is bounded below.

`hdual` is what the source gets from Stacks 08G8 for a perfect `K`: a perfect object has finite
Tor amplitude. In this library perfectness yields that amplitude only *locally*
(`Stacks.SheafOfModules.DerivedTensorProduct.locallyHasFiniteTorDimension_of_isPerfect`, itself
pinned to `Type 0`), and the local-to-global passage — which on a quasi-compact site with a
cofinal system of finite coverings is the step the source does not comment on — is not available at
this spelling of Tor amplitude; `Stacks.Cohomology.TorAmplitude.hasTorAmplitude_of_iSup_eq_top`
proves exactly that locality, but for the ringed-space predicate
`Stacks.Cohomology.TorAmplitude.HasTorAmplitude` and no bridge between the two predicates
exists. So `hdual` is left as a hypothesis and nothing here is tagged: this is not the clause,
it is the clause minus one input. Perfectness of `K` *is* consumed, for the bijection.

The index type lies in the universe of the site, which is where
`preservesColimitsOfShape_derivedTensorFlip` is available. The index universe of the covering
families is free; `hom_coproduct_bijective_of_isPerfect_of_hasFiniteTorDimension` is this
statement for coverings indexed in `Type`. -/
theorem hom_coproduct_bijective_of_isPerfect_of_hasFiniteTorDimension_anyCoveringUniverse
    (B : Set X.C) (Cov : ∀ U : X.C, Set (PreZeroHypercover.{c} U))
    (hCov : ∀ (U : X.C) (F : PreZeroHypercover.{c} U), Cov U F → F.sieve₀ ∈ X.J U)
    (hfinite : ∀ (U : X.C) (F : PreZeroHypercover.{c} U), Cov U F →
      Stacks.Cohomology.HasIntersectionsIn B F)
    (hcofinal : ∀ (U : X.C), B U → ∀ S ∈ X.J U,
      ∃ F : PreZeroHypercover.{c} U, Cov U F ∧ F.sieve₀ ≤ S)
    (X₀ : X.C) (hX₀ : B X₀) (hterm : IsTerminal X₀)
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hK : X.IsPerfect K)
    (hdual : Stacks.SheafOfModules.DerivedTensorProduct.HasFiniteTorDimension T
      (derivedDual X K))
    {I : Type u} [DecidableEq I]
    (M : I → DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    [HasCoproduct M]
    (hplus : DerivedCategoryB.IsBoundedBelow (∐ M)) :
    Function.Bijective
      (DirectSum.toAddMonoid fun j => Preadditive.rightComp K (Limits.Sigma.ι M j)) := by
  let : PreservesColimitsOfShape (Discrete I) (derivedTensorDualFunctor X T K) :=
    preservesColimitsOfShape_derivedTensorFlip X T _ I
  obtain ⟨n, hn⟩ := isBoundedBelow_derivedTensorFlip_of_hasFiniteTorDimension X T
    (derivedDual X K) (∐ M) hdual hplus
  exact Stacks.Cohomology.hom_coproduct_bijective_of_reduction X B Cov hCov hfinite hcofinal
    X₀ hX₀ K (derivedTensorDualFunctor X T K)
    (derivedDualHomEquivOfIsoStructureSheaf X T K hK
      (derivedOverExtensionByZeroUnitIsoStructureSheaf X X₀ hterm))
    (fun f g => derivedDualHomEquivOfIsoStructureSheaf_naturality X T K hK _ f g)
    M ⟨n, (DerivedCategory.isGE_iff _ n).2 hn⟩

omit [∀ V : X.C, (X.J.over V).HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})] in
/-- **Compactness relative to bounded below objects, for a perfect object whose dual has finite
Tor dimension**, for covering families indexed in `Type`. This is
`hom_coproduct_bijective_of_isPerfect_of_hasFiniteTorDimension_anyCoveringUniverse`, where the
statement and its proof are, read at that index universe. -/
theorem hom_coproduct_bijective_of_isPerfect_of_hasFiniteTorDimension
    (B : Set X.C) (Cov : ∀ U : X.C, Set (PreZeroHypercover.{0} U))
    (hCov : ∀ (U : X.C) (F : PreZeroHypercover.{0} U), Cov U F → F.sieve₀ ∈ X.J U)
    (hfinite : ∀ (U : X.C) (F : PreZeroHypercover.{0} U), Cov U F →
      Stacks.Cohomology.HasIntersectionsIn B F)
    (hcofinal : ∀ (U : X.C), B U → ∀ S ∈ X.J U,
      ∃ F : PreZeroHypercover.{0} U, Cov U F ∧ F.sieve₀ ≤ S)
    (X₀ : X.C) (hX₀ : B X₀) (hterm : IsTerminal X₀)
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hK : X.IsPerfect K)
    (hdual : Stacks.SheafOfModules.DerivedTensorProduct.HasFiniteTorDimension T
      (derivedDual X K))
    {I : Type u} [DecidableEq I]
    (M : I → DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    [HasCoproduct M]
    (hplus : DerivedCategoryB.IsBoundedBelow (∐ M)) :
    Function.Bijective
      (DirectSum.toAddMonoid fun j => Preadditive.rightComp K (Limits.Sigma.ι M j)) :=
  hom_coproduct_bijective_of_isPerfect_of_hasFiniteTorDimension_anyCoveringUniverse X T B Cov
    hCov hfinite hcofinal X₀ hX₀ hterm K hK hdual M hplus

end AlgebraicGeometry.RingedSite


end
