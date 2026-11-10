module

public import StacksFrontier.CategoryTheory.Monoidal.RigidJointlyFaithful
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedCurryingSourceNaturality
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedApplicationUnitLaw
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedDualPairing
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.LeftDualOnARingedSpace
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.PerfectDualTensorHom
import StacksCore.Tactic.StacksAttribute

/-!
# The coevaluation of a perfect object of `D(O_X)`

Let `(X, O_X)` be a ringed space and let `K` be a **perfect** object of the derived category
`D(O_X)` of sheaves of `O_X`-modules, with dual `K^∨ = RSheafHom(K, O_X)`
(`Stacks.SheafOfModules.derivedDual`).  The canonical map `K ⊗^L_{O_X} K^∨ ⟶ RSheafHom(K, K)` of
Stacks 08I1 is an isomorphism, and the **coevaluation** `η : O_X ⟶ K ⊗^L_{O_X} K^∨` is the map
sending `1` to the section corresponding to `id_K` under it.  Together with the evaluation
`ε = Stacks.SheafOfModules.derivedDualEvaluation` it makes `K^∨` a left dual of `K`; that is
Example 0FPC, `Stacks.SheafOfModules.derivedDual_isLeftDual` of
`StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.PerfectDualLeftDual`.

## Main definitions

* `Stacks.SheafOfModules.derivedDualCoevaluation`: the coevaluation `η` of a perfect `K`.
* `Stacks.SheafOfModules.exactPairingDerivedDualOfEvaluationCoevaluation`: an exact pairing from
  the first triangle identity for `(η, ε)`.

## Main results

* `Stacks.SheafOfModules.isIso_derivedTensorDualToSheafHom_self`: the canonical map
  `K ⊗^L_{O_X} K^∨ ⟶ RSheafHom(K, K)` is an isomorphism for a perfect `K`.
* `Stacks.SheafOfModules.derivedDualCoevaluation_comp`: the coevaluation followed by that
  isomorphism is the section corresponding to `id_K`.
* `Stacks.SheafOfModules.eq_id_of_whiskerRight_comp_derivedDualEvaluation`: the evaluation
  detects endomorphisms of `K^∨` — `c ▷ K ≫ ε = ε` only for `c = 𝟙`.
* `Stacks.SheafOfModules.derivedDualCoevaluation_triangle`: the first triangle identity
  `(η ▷ K) ≫ α ≫ (K ◁ ε) = λ ≫ ρ⁻¹` from the equation (E1) — the comparison of Stacks 08I1
  followed by application is the contraction against `ε` — and the unit law (UL) of the
  application morphism.  The chain is

  `(η ▷ K) ≫ α ≫ (K ◁ ε) ≫ ρ = ((η ≫ c₈) ▷ K) ≫ app = (ι ▷ K) ≫ app = λ`.

  (UL) is `Stacks.SheafOfModules.derivedSheafHomCounit_unit_law_monoidal'`, and (E1) follows from
  the composition law `Stacks.SheafOfModules.compositionApplicationLaw` and the right unit law
  of the application morphism, by
  `derivedTensorDualToSheafHom_whiskerRight_comp_derivedSheafHomCounit_of_compositionLaw`.

## Perfectness model

Perfectness is `AlgebraicGeometry.RingedSite.IsPerfect` of Stacks 08G5, read at the ringed site
`Stacks.SheafOfModules.ringedSite Rc` of opens of the space.  It is implied by the ringed-space
notion of Stacks 08CM, by `Stacks.Cohomology.PerfectComplexes.isPerfect_ringedSite_of_isPerfect`.

## Implementation notes

The additivity of `⊗_{O_X}` in each variable and the existence of the total tensor complexes are
pinned as file-local instances from
`StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.LeftDualOnARingedSpace`: the library
instances are stated with the sections universe tied to the site universes as `max u v`, which
instance synthesis cannot solve against the diagonal `u` while those universes are still
metavariables.

The coevaluation is stated in the monoidal spelling of Stacks 0FPT, as
`Stacks.SheafOfModules.derivedDualEvaluation` is, so that the two sit in the same monoidal
structure; its defining property `derivedDualCoevaluation_comp` is stated in the plain spelling,
where both sides are morphisms into `RSheafHom(K, K)`.

## References

* [Stacks Project, Tag 0FPC](https://stacks.math.columbia.edu/tag/0FPC)
* [Stacks Project, Tag 0FPU](https://stacks.math.columbia.edu/tag/0FPU)
* [Stacks Project, Tag 08DQ](https://stacks.math.columbia.edu/tag/08DQ)
* [Stacks Project, Tag 08JJ](https://stacks.math.columbia.edu/tag/08JJ)
* [Stacks Project, Tag 08I1](https://stacks.math.columbia.edu/tag/08I1)
* [Stacks Project, Tag 08JA](https://stacks.math.columbia.edu/tag/08JA)
* [Stacks Project, Tag 08G5](https://stacks.math.columbia.edu/tag/08G5)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
* [Stacks Project, Tag 0FFP](https://stacks.math.columbia.edu/tag/0FFP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory TopologicalSpace Opposite AlgebraicGeometry

universe u

namespace Stacks.SheafOfModules

attribute [local instance] HasDerivedCategory.standard

variable {X : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} X)

/- The three pinnings of the opens-site tensor product this file elaborates against —
`⊗_{O_X}` additive in each variable, and the total complexes of the tensor double complexes
existing — are stated once, in
`StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.LeftDualOnARingedSpace`, and taken from
there.  They are pinned by hand rather than synthesized because the library instances tie the
sections universe to the site universes as `max u v`, which instance synthesis cannot solve
against the diagonal `u` of this cluster while those universes are still metavariables. -/
attribute [local instance] Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorObjAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.hasMapBifunctorSheafTensor

variable (K : DerivedCategory (StructureSheafModules Rc))

/-- **The map `K ⊗^L_{O_X} K^∨ ⟶ RSheafHom(K, K)` is an isomorphism.** For a perfect object `K`
of `D(O_X)` the canonical map of Stacks 08I1 at `M = K` is invertible (Stacks 08DQ). -/
theorem isIso_derivedTensorDualToSheafHom_self (hK : (ringedSite Rc).IsPerfect K) :
    IsIso (derivedTensorDualToSheafHom Rc K K) :=
  isIso_derivedTensorDualToSheafHom_of_isPerfect Rc K K hK

/-- **The coevaluation of a perfect object.** For a perfect object `K` of `D(O_X)` with dual
`K^∨ = RSheafHom(K, O_X)` the coevaluation is the morphism

`η : O_X ⟶ K ⊗^L_{O_X} K^∨`

corresponding to `id_K` under the isomorphism `K ⊗^L_{O_X} K^∨ ≅ RSheafHom(K, K)` of
`isIso_derivedTensorDualToSheafHom_self`: the section corresponding to `id_K`, followed by the
inverse of that isomorphism.  It is stated for the monoidal structure of Stacks 0FPT on
`D(O_X)`, whose tensor product is the derived tensor product and whose unit is the structure
sheaf in degree zero. -/
def derivedDualCoevaluation (hK : (ringedSite Rc).IsPerfect K) :
    (letI := derivedMonoidalStructure Rc
    𝟙_ (DerivedCategory (StructureSheafModules Rc)) ⟶ K ⊗ derivedDual Rc K) :=
  RingedSite.derivedDualCoevaluation (ringedSite Rc) K
    (RingedSite.isIso_derivedTensorDualToSheafHom_of_isPerfect (ringedSite Rc)
      (canonicalDerivedTensorProduct (ringedSite Rc)) K K hK)

/-- **The coevaluation corresponds to `id_K`.** Composing `η` with the isomorphism
`K ⊗^L_{O_X} K^∨ ≅ RSheafHom(K, K)` gives back the section corresponding to the identity of `K`,
`AlgebraicGeometry.RingedSite.derivedIdentitySection`, the class of `id_K` under the two
identifications of Stacks 08JA. -/
theorem derivedDualCoevaluation_comp (hK : (ringedSite Rc).IsPerfect K) :
    derivedDualCoevaluation Rc K hK ≫ derivedTensorDualToSheafHom Rc K K =
      RingedSite.derivedIdentitySection (ringedSite Rc) K :=
  RingedSite.derivedDualCoevaluation_comp (ringedSite Rc) K
    (isIso_derivedTensorDualToSheafHom_self Rc K hK)

/-- **The evaluation of the derived dual detects endomorphisms of `K^∨`.** If `c : K^∨ ⟶ K^∨`
satisfies `c ▷ K ≫ ε = ε` then `c` is the identity. No hypothesis on `K` is needed: the
evaluation is the image of `𝟙_{K^∨}` under the bijection of morphism groups of Stacks 08J8
(`AlgebraicGeometry.RingedSite.derivedDualEvaluation_eq`), and
`AlgebraicGeometry.RingedSite.derivedCurryHomEquiv_eq_tensor_evaluation` says that `c ▷ K ≫ ε`
is the image of `c` under that same bijection, so this is its injectivity. -/
theorem eq_id_of_whiskerRight_comp_derivedDualEvaluation
    (c : derivedDual Rc K ⟶ derivedDual Rc K)
    (hc : letI : MonoidalCategory (DerivedCategory (SheafOfModules.{u}
        (Tensor.ringSheaf.{u, u, u} Rc))) := derivedMonoidalStructure Rc
      c ▷ K ≫ derivedDualEvaluation Rc K = derivedDualEvaluation Rc K) :
    c = 𝟙 (derivedDual Rc K) := by
  have hc' : ((derivedTensorProductFunctor (ringedSite Rc)).map c).app K ≫
      RingedSite.derivedDualEvaluation (ringedSite Rc) K =
        RingedSite.derivedDualEvaluation (ringedSite Rc) K := hc
  change c = 𝟙 (RingedSite.derivedDual (ringedSite Rc) K)
  refine (RingedSite.derivedCurryHomEquiv (ringedSite Rc)
      (RingedSite.derivedDual (ringedSite Rc) K) K
      (RingedSite.derivedStructureSheaf (ringedSite Rc))).injective ?_
  rw [RingedSite.derivedCurryHomEquiv_eq_tensor_evaluation (ringedSite Rc)
      (RingedSite.derivedDual (ringedSite Rc) K) K
      (RingedSite.derivedStructureSheaf (ringedSite Rc)) c,
    ← RingedSite.derivedDualEvaluation_eq (ringedSite Rc) K]
  exact hc'

/-- **One of the two triangle identities implies the other.** For a perfect `K`, with the
coevaluation `η = derivedDualCoevaluation` and the evaluation `ε = derivedDualEvaluation`, the
single identity

`(η ▷ K) ≫ α ≫ (K ◁ ε) = λ ≫ ρ⁻¹`

makes `(K^∨, η, ε)` a left dual of `K`: the other identity follows, by
`CategoryTheory.ExactPairing.ofEvaluationCoevaluation` together with
`Stacks.SheafOfModules.eq_id_of_whiskerRight_comp_derivedDualEvaluation`. -/
@[instance_reducible]
def exactPairingDerivedDualOfEvaluationCoevaluation (hK : (ringedSite Rc).IsPerfect K)
    (h : letI := derivedMonoidalStructure Rc
      derivedDualCoevaluation Rc K hK ▷ K ≫ (α_ K (derivedDual Rc K) K).hom ≫
        K ◁ derivedDualEvaluation Rc K = (λ_ K).hom ≫ (ρ_ K).inv) :
    letI := derivedMonoidalStructure Rc
    ExactPairing K (derivedDual Rc K) :=
  letI := derivedMonoidalStructure Rc
  ExactPairing.ofEvaluationCoevaluation (derivedDualCoevaluation Rc K hK)
    (derivedDualEvaluation Rc K) h fun c hc =>
      eq_id_of_whiskerRight_comp_derivedDualEvaluation Rc K c hc

/-- **The identity section names the identity.** Reading `derivedIdentitySection` back through
the two identifications of Stacks 08JA it was built from gives the identity of `K`. -/
private lemma derivedSheafHomGlobalSectionsEquiv_symm_derivedIdentitySection :
    RingedSite.derivedSheafHomGlobalSectionsEquiv (ringedSite Rc) K K
        ((RingedSite.derivedStructureSheafGlobalSectionsEquiv (ringedSite Rc)
          (((RingedSite.derivedSheafHomBifunctor (ringedSite Rc)).obj (op K)).obj K)).symm
            (RingedSite.derivedIdentitySection (ringedSite Rc) K)) =
      𝟙 K := by
  have key : ∀ L : DerivedCategory (SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} Rc)),
      RingedSite.derivedSheafHomGlobalSectionsEquiv (ringedSite Rc) L L
          ((RingedSite.derivedStructureSheafGlobalSectionsEquiv (ringedSite Rc)
            (((RingedSite.derivedSheafHomBifunctor (ringedSite Rc)).obj (op L)).obj L)).symm
              (RingedSite.derivedIdentitySection (ringedSite Rc) L)) =
        𝟙 L := fun L => by
    rw [RingedSite.derivedIdentitySection_eq (ringedSite Rc) L, AddEquiv.symm_apply_apply]
    exact AddEquiv.apply_symm_apply _ _
  exact key K

/-- **The first triangle identity, from the two equations it reduces to.** Write
`c₈ = derivedTensorDualToSheafHom Rc K K` for the comparison of Stacks 08I1,
`ι = derivedIdentitySection` for the section corresponding to `id_K`, and
`app = derivedSheafHomCounit Rc K K` for the application morphism
`RSheafHom(K, K) ⊗^L_{O_X} K ⟶ K` of Stacks 08J8. Then the triangle identity

`(η ▷ K) ≫ α ≫ (K ◁ ε) = λ ≫ ρ⁻¹`

follows from

* `happ`: `(c₈ ▷ K) ≫ app = α ≫ (K ◁ ε) ≫ ρ`;
* `hunit`: the unit law tying Stacks 08JA at source the structure sheaf to Stacks 08J8, used at
  `y = ι`,

by the chain `(η ▷ K) ≫ α ≫ (K ◁ ε) ≫ ρ = ((η ≫ c₈) ▷ K) ≫ app = (ι ▷ K) ≫ app = λ`, whose
middle step is `derivedDualCoevaluation_comp`.  Both equations hold for every `K`: `hunit` is
`Stacks.SheafOfModules.derivedSheafHomCounit_unit_law_monoidal'`, and `happ` follows from
`Stacks.SheafOfModules.compositionApplicationLaw`. -/
theorem derivedDualCoevaluation_triangle (hK : (ringedSite Rc).IsPerfect K)
    (happ : letI := derivedMonoidalStructure Rc
      derivedTensorDualToSheafHom Rc K K ▷ K ≫ derivedSheafHomCounit Rc K K =
        (α_ K (derivedDual Rc K) K).hom ≫ (K ◁ derivedDualEvaluation Rc K) ≫ (ρ_ K).hom)
    (hunit : letI := derivedMonoidalStructure Rc
      ∀ y : 𝟙_ (DerivedCategory (StructureSheafModules Rc)) ⟶
          ((derivedSheafHom Rc).obj (op K)).obj K,
        y ▷ K ≫ derivedSheafHomCounit Rc K K =
          (λ_ K).hom ≫ RingedSite.derivedSheafHomGlobalSectionsEquiv (ringedSite Rc) K K
            ((RingedSite.derivedStructureSheafGlobalSectionsEquiv (ringedSite Rc)
              (((RingedSite.derivedSheafHomBifunctor (ringedSite Rc)).obj (op K)).obj
                K)).symm y)) :
    letI := derivedMonoidalStructure Rc
    derivedDualCoevaluation Rc K hK ▷ K ≫ (α_ K (derivedDual Rc K) K).hom ≫
        K ◁ derivedDualEvaluation Rc K = (λ_ K).hom ≫ (ρ_ K).inv := by
  let := derivedMonoidalStructure Rc
  have hι : (show 𝟙_ (DerivedCategory (StructureSheafModules Rc)) ⟶
        ((derivedSheafHom Rc).obj (op K)).obj K from
      RingedSite.derivedIdentitySection (ringedSite Rc) K) ▷ K ≫
      derivedSheafHomCounit Rc K K = (λ_ K).hom := by
    rw [hunit, derivedSheafHomGlobalSectionsEquiv_symm_derivedIdentitySection,
      Category.comp_id]
  rw [Iso.eq_comp_inv]
  simp only [Category.assoc]
  rw [← happ, ← Category.assoc, ← comp_whiskerRight, derivedDualCoevaluation_comp]
  exact hι

/-- **The exact pairing from the two equations.** For a perfect `K` the pair
`(η, ε) = (derivedDualCoevaluation, derivedDualEvaluation)` is an exact pairing as soon as the two
equations of `derivedDualCoevaluation_triangle` hold. -/
@[instance_reducible]
def exactPairingDerivedDualOfApplicationLaws (hK : (ringedSite Rc).IsPerfect K)
    (happ : letI := derivedMonoidalStructure Rc
      derivedTensorDualToSheafHom Rc K K ▷ K ≫ derivedSheafHomCounit Rc K K =
        (α_ K (derivedDual Rc K) K).hom ≫ (K ◁ derivedDualEvaluation Rc K) ≫ (ρ_ K).hom)
    (hunit : letI := derivedMonoidalStructure Rc
      ∀ y : 𝟙_ (DerivedCategory (StructureSheafModules Rc)) ⟶
          ((derivedSheafHom Rc).obj (op K)).obj K,
        y ▷ K ≫ derivedSheafHomCounit Rc K K =
          (λ_ K).hom ≫ RingedSite.derivedSheafHomGlobalSectionsEquiv (ringedSite Rc) K K
            ((RingedSite.derivedStructureSheafGlobalSectionsEquiv (ringedSite Rc)
              (((RingedSite.derivedSheafHomBifunctor (ringedSite Rc)).obj (op K)).obj
                K)).symm y)) :
    letI := derivedMonoidalStructure Rc
    ExactPairing K (derivedDual Rc K) :=
  exactPairingDerivedDualOfEvaluationCoevaluation Rc K hK
    (derivedDualCoevaluation_triangle Rc K hK happ hunit)

/-- **The first triangle identity from (E1).** `derivedDualCoevaluation_triangle` with its
`hunit` hypothesis discharged by `Stacks.SheafOfModules.derivedSheafHomCounit_unit_law_monoidal'`.

The law and `hunit` differ only in the inner identification of Stacks 08JA,
`AlgebraicGeometry.RingedSite.derivedStructureSheafGlobalSectionsEquiv`: the law hands it
`RSheafHom(K, K)` through `Stacks.SheafOfModules.derivedSheafHom` and `hunit` through
`AlgebraicGeometry.RingedSite.derivedSheafHomBifunctor`, and its `HasSheafify` and
`WEqualsLocallyBijective` instances are synthesized at `Opens.grothendieckTopology X` in the law
and at `(ringedSite Rc).J` in `hunit`. The two inner identifications are matched by `rfl` before
they are applied, and `DFunLike.congr` and `DFunLike.congr_arg` carry that equality through the
application to `y` and through the outer identification, which is the same term on both sides.
Matching the applied identifications instead makes the unifier unfold the coercions and
evaluate the identifications on `y`, which exceeds the default recursion depth. -/
theorem derivedDualCoevaluation_triangle_of_applicationLaw (hK : (ringedSite Rc).IsPerfect K)
    (happ : letI := derivedMonoidalStructure Rc
      derivedTensorDualToSheafHom Rc K K ▷ K ≫ derivedSheafHomCounit Rc K K =
        (α_ K (derivedDual Rc K) K).hom ≫ (K ◁ derivedDualEvaluation Rc K) ≫ (ρ_ K).hom) :
    letI := derivedMonoidalStructure Rc
    derivedDualCoevaluation Rc K hK ▷ K ≫ (α_ K (derivedDual Rc K) K).hom ≫
        K ◁ derivedDualEvaluation Rc K = (λ_ K).hom ≫ (ρ_ K).inv :=
  derivedDualCoevaluation_triangle Rc K hK happ fun y ↦
    (derivedSheafHomCounit_unit_law_monoidal' Rc K K y).trans
      (whisker_eq _ (DFunLike.congr_arg _ (DFunLike.congr rfl rfl)))

/-- **The exact pairing from (E1).** `exactPairingDerivedDualOfApplicationLaws` with the unit law
discharged. -/
@[instance_reducible]
def exactPairingDerivedDualOfApplicationLaw (hK : (ringedSite Rc).IsPerfect K)
    (happ : letI := derivedMonoidalStructure Rc
      derivedTensorDualToSheafHom Rc K K ▷ K ≫ derivedSheafHomCounit Rc K K =
        (α_ K (derivedDual Rc K) K).hom ≫ (K ◁ derivedDualEvaluation Rc K) ≫ (ρ_ K).hom) :
    letI := derivedMonoidalStructure Rc
    ExactPairing K (derivedDual Rc K) :=
  exactPairingDerivedDualOfEvaluationCoevaluation Rc K hK
    (derivedDualCoevaluation_triangle_of_applicationLaw Rc K hK happ)

end Stacks.SheafOfModules

end
