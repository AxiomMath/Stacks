module

public import Mathlib.Algebra.Homology.QuasiIso
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.SigmaModulesEquivalence
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.DerivedPullback09US
public import StacksFrontier.CategoryTheory.Pi.HomologicalComplex

/-!
# Complexes of sheaves of modules on a coproduct of schemes

Let `Z : I → Scheme` be a family of schemes. Degreewise restriction to the summands,

  `CochainComplex (∐ Z).Modules ℤ ⥤ ∀ i, CochainComplex (Z i).Modules ℤ`,

is an **equivalence of categories**. It is the composite of two equivalences, neither of which
needs a hypothesis on the family: restriction to the summands is an equivalence of the
categories of sheaves of modules, `AlgebraicGeometry.sigmaModulesEquivalence`, and a complex in
a product of preadditive categories is a family of complexes,
`CategoryTheory.Pi.homologicalComplexEquivalence`.

So a family of complexes, one on each summand, *assembles* into one complex on `∐ Z`; a family
of maps of such complexes assembles into one map, uniquely; and the assembly is inverse to
degreewise restriction.

## Main definitions

* `AlgebraicGeometry.sigmaComplexFunctor`: degreewise restriction to the summands, as one
  functor to the product of the categories of complexes on the summands.
* `AlgebraicGeometry.sigmaComplexEquivalence`: **the equivalence**.

## Main results

* `AlgebraicGeometry.sigmaComplexEquivalence_functor`: the functor of the equivalence is
  `AlgebraicGeometry.sigmaComplexFunctor`.
* `AlgebraicGeometry.sigmaHomotopy`: a family of homotopies between the degreewise restrictions
  of two maps of complexes on `∐ Z`, one on each summand, assembles into a homotopy between the
  two maps themselves.
* `AlgebraicGeometry.quasiIso_of_quasiIso_pullback_sigmaι`: a map of complexes on `∐ Z` whose
  restriction to every summand is a quasi-isomorphism is a quasi-isomorphism.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable {I : Type u} (Z : I → Scheme.{u})

/-- Restriction to the summands of a coproduct of schemes is additive. -/
instance sigmaModulesFunctor_additive : (sigmaModulesFunctor Z).Additive where
  map_add := funext fun i => (Scheme.Modules.pullback (Sigma.ι Z i)).map_add

/-- **Degreewise restriction to the summands**, as one functor to the product of the categories
of complexes of sheaves of modules on the summands. -/
def sigmaComplexFunctor :
    CochainComplex (∐ Z : Scheme.{u}).Modules ℤ ⥤ ∀ i, CochainComplex (Z i).Modules ℤ :=
  Functor.pi' fun i =>
    (Scheme.Modules.pullback (Sigma.ι Z i)).mapHomologicalComplex (ComplexShape.up ℤ)

/-- The component of `AlgebraicGeometry.sigmaComplexFunctor` at a summand `Z i` sends a complex to
its degreewise restriction along `Sigma.ι Z i`. -/
@[simp]
theorem sigmaComplexFunctor_obj (K : CochainComplex (∐ Z : Scheme.{u}).Modules ℤ) (i : I) :
    (sigmaComplexFunctor Z).obj K i =
      ((Scheme.Modules.pullback (Sigma.ι Z i)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K := rfl

/-- The component of `AlgebraicGeometry.sigmaComplexFunctor` at a summand `Z i` sends a map of
complexes to its degreewise restriction along `Sigma.ι Z i`. -/
@[simp]
theorem sigmaComplexFunctor_map {K L : CochainComplex (∐ Z : Scheme.{u}).Modules ℤ} (φ : K ⟶ L)
    (i : I) :
    (sigmaComplexFunctor Z).map φ i =
      ((Scheme.Modules.pullback (Sigma.ι Z i)).mapHomologicalComplex
        (ComplexShape.up ℤ)).map φ := rfl

/-- **A complex of sheaves of modules on a coproduct of schemes is a family of complexes on the
summands.** Degreewise restriction to the summands is an equivalence

  `CochainComplex (∐ Z).Modules ℤ ≌ ∀ i, CochainComplex (Z i).Modules ℤ`,

for an arbitrary family of schemes and with no hypothesis on it. -/
def sigmaComplexEquivalence :
    CochainComplex (∐ Z : Scheme.{u}).Modules ℤ ≌ ∀ i, CochainComplex (Z i).Modules ℤ :=
  ((sigmaModulesEquivalence Z).mapHomologicalComplex (ComplexShape.up ℤ)).trans
    (Pi.homologicalComplexEquivalence (ComplexShape.up ℤ))

/-- The equivalence is degreewise restriction to the summands. -/
theorem sigmaComplexEquivalence_functor :
    (sigmaComplexEquivalence Z).functor = sigmaComplexFunctor Z := rfl

/-- Degreewise restriction to the summands is an equivalence. -/
instance sigmaComplexFunctor_isEquivalence : (sigmaComplexFunctor Z).IsEquivalence :=
  sigmaComplexEquivalence_functor Z ▸ inferInstance

/-- **A family of homotopies on the summands assembles into a homotopy on the coproduct.** If
the degreewise restrictions of two maps `x, y : A ⟶ B` of complexes on `∐ Z` are homotopic on
every summand, then `x` and `y` are homotopic. -/
def sigmaHomotopy {A B : CochainComplex (∐ Z : Scheme.{u}).Modules ℤ} {x y : A ⟶ B}
    (H : ∀ i, Homotopy ((sigmaComplexFunctor Z).map x i) ((sigmaComplexFunctor Z).map y i)) :
    Homotopy x y :=
  (sigmaModulesFunctor Z).preimageHomotopy (CategoryTheory.Pi.homotopyPi _ H)

/-! ### Detecting quasi-isomorphy on the summands -/

/-- Restriction to a summand of a coproduct of schemes preserves homology. -/
instance pullbackSigmaι_preservesHomology (i : I) :
    (Scheme.Modules.pullback (Sigma.ι Z i)).PreservesHomology := by
  have : PreservesFiniteLimits (Scheme.Modules.pullback (Sigma.ι Z i)) :=
    preservesFiniteLimits_pullback_of_flat (Sigma.ι Z i)
  have : (Scheme.Modules.pullback (Sigma.ι Z i)).PreservesEpimorphisms :=
    preservesEpimorphisms_of_preservesColimitsOfShape _
  exact Functor.preservesHomology_of_preservesEpis_and_kernels _

/-- **Quasi-isomorphy of a map of complexes of sheaves of modules on a coproduct of schemes is
detected on the summands.** If the degreewise restriction of `φ` to each summand is a
quasi-isomorphism, then `φ` is one. -/
theorem quasiIso_of_quasiIso_pullback_sigmaι
    {K L : CochainComplex (∐ Z : Scheme.{u}).Modules ℤ} (φ : K ⟶ L)
    (h : ∀ i, QuasiIso (((Scheme.Modules.pullback (Sigma.ι Z i)).mapHomologicalComplex
      (ComplexShape.up ℤ)).map φ)) :
    QuasiIso φ := by
  refine (quasiIso_iff φ).2 fun n => ?_
  set S := HomologicalComplex.shortComplexFunctor (∐ Z : Scheme.{u}).Modules
    (ComplexShape.up ℤ) n
  have γ : ShortComplex.LeftHomologyMapData (S.map φ) (S.obj K).leftHomologyData
      (S.obj L).leftHomologyData := default
  rw [quasiIsoAt_iff, γ.quasiIso_iff]
  refine isIso_of_isIso_pullback_sigmaι Z γ.φH fun i => ?_
  refine (γ.quasiIso_map_iff (Scheme.Modules.pullback (Sigma.ι Z i))).mp ?_
  exact (quasiIsoAt_iff _ n).mp ((h i).quasiIsoAt n)

end AlgebraicGeometry

end
