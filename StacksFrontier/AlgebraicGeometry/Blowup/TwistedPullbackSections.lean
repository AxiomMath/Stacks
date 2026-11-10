module

public import StacksFrontier.AlgebraicGeometry.Blowup.TwistVanishingThreshold
public import StacksFrontier.AlgebraicGeometry.Blowup.TwistedPullbackTerms
public import StacksFrontier.AlgebraicGeometry.EilenbergWatts.DirectSums
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.EilenbergWattsGeometricFactor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.TensorSymmetry
public import StacksFrontier.Homology.TensorComplex.BifunctorSingleLeftComplex
public import StacksFrontier.Homology.Tor.KFlatResolutionSingleTensor
public import StacksFrontier.Topology.Sheaves.RingedSpace.ModulePullbackUnit
public import StacksCore.Tactic.StacksAttribute

/-!
# Cohomology of the twisted derived pullback along the affine blowup

Let `A` be a Noetherian ring, `I ⊆ A` an ideal and `p : X ⟶ Spec A` the blowup of `Spec A` in
`I`, with its twists `𝒪_X(q)`. For an `A`-module `M` and `q` large enough,

`RΓ(X, Lp^*(M̃) ⊗^𝐋_{𝒪_X} 𝒪_X(q)) ≅ M ⊗^𝐋_A I^q`  in `D(A)`.

The comparison is the Eilenberg–Watts map of the endofunctor

`Φ(N) = Γ(X, 𝒪_X(q) ⊗_{𝒪_X} p^*(Ñ))`

of `A`-modules. `Φ` is `A`-linear and commutes with arbitrary direct sums, so the canonical map
`Φ(A) ⊗_A N ⟶ Φ(N)` is an isomorphism for every free `N`; and `Φ(A) = Γ(X, 𝒪_X(q))`, which is
`I^q` above the threshold of [Stacks, Tag 0AG6] clause (3). Applying this degreewise to a K-flat
resolution `P^• ⟶ M` by free modules identifies the complex of `A`-linear global sections of
`Tot(p^*P̃^• ⊗ 𝒪_X(q)[0])` with `I^q ⊗_A P^•`, which computes `M ⊗^𝐋_A I^q`; and that complex of
global sections computes `RΓ(X, Lp^*(M̃) ⊗^𝐋 𝒪_X(q))` above the threshold of
[Stacks, Tag 0AG7].

## Main definitions

* `Stacks.Blowup.twistedGeometricFactor`: the functor `N ↦ 𝒪_X(q) ⊗ p^*(Ñ)` from `A`-modules to
  `𝒪_X`-modules.
* `Stacks.Blowup.twistedSectionsFunctor`: `Φ`, the same followed by `A`-linear global sections.

## Main results

* `Stacks.Blowup.linear_twistedSectionsFunctor` and
  `Stacks.Blowup.preservesColimitsOfShape_discrete_twistedSectionsFunctor`: `Φ` is `A`-linear
  and commutes with arbitrary direct sums.
* `Stacks.Blowup.twistedSectionsFunctorObjUnit`: `Φ(A) = Γ(X, 𝒪_X(q))`.
* `Stacks.Blowup.twistedPullbackComplexIsoGeometric`: the total complex
  `Tot(p^*P̃^• ⊗ 𝒪_X(q)[0])` is `N ↦ 𝒪_X(q) ⊗ p^*(Ñ)` applied degreewise to `P^•`.
* `Stacks.Blowup.sectionsTwistedPullbackComplexTensorIdealPowIso`: its complex of `A`-linear
  global sections is `I^q ⊗_A P^•`, for `P^•` a complex of free modules.
* `Stacks.Blowup.nonempty_derivedGlobalSectionsTwistedPullback_iso_derivedTensorIdealPow`:
  **`RΓ(X, Lp^*(M̃) ⊗^𝐋 𝒪_X(q)) ≅ M ⊗^𝐋_A I^q` in `D(A)`**, for any `A`-module `M`, at a `q`
  satisfying the vanishing of [Stacks, Tag 0AG7] and the identification of [Stacks, Tag 0AG6]
  clause (3).
* `Stacks.Blowup`
  `.exists_forall_nonempty_derivedGlobalSectionsTwistedPullback_iso_derivedTensorIdealPow`: the
  same for every `q` above a threshold `q₀` at which `Γ(X, 𝒪_X(q)) ≅ I^q`.

## References

* [Stacks Project, Tag 0G9Z](https://stacks.math.columbia.edu/tag/0G9Z)
* [Stacks Project, Tag 0AG6](https://stacks.math.columbia.edu/tag/0AG6)
* [Stacks Project, Tag 0AG7](https://stacks.math.columbia.edu/tag/0AG7)
* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction
open Stacks.AlgebraicGeometry.TopDegreeBaseChange
open Stacks.Cohomology.AffineBase
open Stacks.Cohomology.DerivedPullbackOfATilde
open Stacks.SheafOfModules.Tensor
open scoped ModuleCat.Algebra

universe u

namespace Stacks.Blowup

variable {A : Type u} [CommRing A] (I : Ideal A)

/-- The affine blowup, read as a scheme over `Spec A` through its structure morphism. -/
abbrev blowUpOver : Over (Spec (CommRingCat.of A)) := Over.mk (toSpec I)

/-- The `A`-linear structure on `𝒪_X`-modules induced by the structure morphism of the affine
blowup. -/
@[instance_reducible]
def blowUpModulesLinear : Linear A (blowUpSpec I).Modules :=
  AlgebraicGeometry.modulesLinear A (blowUpOver I)

/-- The `A`-algebra structure on the functions of the affine blowup induced by its structure
morphism. -/
@[instance_reducible]
def blowUpSectionsAlgebra : Algebra A Γ(blowUpSpec I, ⊤) :=
  baseSectionsAlgebra A (blowUpOver I)

/-! ### The geometric factor `N ↦ 𝒪_X(q) ⊗ p^*(Ñ)` -/

/-- **The functor `N ↦ 𝒪_X(q) ⊗_{𝒪_X} p^*(Ñ)`** from `A`-modules to `𝒪_X`-modules on the affine
blowup. -/
def twistedGeometricFactor (q : ℤ) : ModuleCat.{u} A ⥤ (blowUpSpec I).Modules :=
  geometricFactorFormula A (blowUpOver I) (blowUpTwist I q)

/-- `N ↦ 𝒪_X(q) ⊗ p^*(Ñ)` is an additive functor. -/
instance additive_twistedGeometricFactor (q : ℤ) : (twistedGeometricFactor I q).Additive :=
  additive_geometricFactorFormula A (blowUpOver I) (blowUpTwist I q)

/-- `N ↦ 𝒪_X(q) ⊗ p^*(Ñ)` is `A`-linear: so are sheafification, pullback along a morphism of
`A`-schemes and tensoring with a fixed module. -/
theorem linear_twistedGeometricFactor (q : ℤ) :
    letI := blowUpModulesLinear I
    Functor.Linear A (twistedGeometricFactor I q) :=
  let _ : Linear A (blowUpSpec I).Modules := blowUpModulesLinear I
  linear_geometricFactorFormula A (blowUpOver I) (blowUpTwist I q)

/-- `N ↦ 𝒪_X(q) ⊗ p^*(Ñ)` commutes with arbitrary direct sums: all three factors are left
adjoints or tensor functors. -/
theorem preservesColimitsOfShape_discrete_twistedGeometricFactor (q : ℤ) (J : Type u) :
    PreservesColimitsOfShape (Discrete J) (twistedGeometricFactor I q) :=
  let _ := preservesColimitsOfSize_geometricFactorFormula A (blowUpOver I) (blowUpTwist I q)
  inferInstanceAs (PreservesColimitsOfShape (Discrete J)
    (geometricFactorFormula A (blowUpOver I) (blowUpTwist I q)))

/-! ### The endofunctor `Φ` of `A`-modules -/

/-- **`A`-linear global sections of modules on the affine blowup are `A`-linear.** The `A`-action
on a morphism of `𝒪_X`-modules is multiplication by the image of the scalar in the functions on
each open; at `⊤` that is the `A`-action after restriction of scalars. -/
theorem linear_globalSectionsOver :
    letI := blowUpModulesLinear I
    Functor.Linear A (globalSectionsOver (toSpec I)) := by
  let _ : Linear A (blowUpSpec I).Modules := blowUpModulesLinear I
  let _ : Algebra A Γ(blowUpSpec I, ⊤) := blowUpSectionsAlgebra I
  let _ : Functor.Linear A (moduleGlobalSections (blowUpSpec I)) :=
    linear_moduleGlobalSections A (blowUpOver I)
  let _ : Functor.Linear A
      (ModuleCat.restrictScalars (algebraMap A Γ(blowUpSpec I, ⊤))) :=
    linear_restrictScalars A Γ(blowUpSpec I, ⊤)
  exact inferInstanceAs (Functor.Linear A (moduleGlobalSections (blowUpSpec I) ⋙
    ModuleCat.restrictScalars (algebraMap A Γ(blowUpSpec I, ⊤))))

/-- **The endofunctor `Φ(N) = Γ(X, 𝒪_X(q) ⊗ p^*(Ñ))` of `A`-modules.** -/
def twistedSectionsFunctor (q : ℤ) : ModuleCat.{u} A ⥤ ModuleCat.{u} A :=
  twistedGeometricFactor I q ⋙ globalSectionsOver (toSpec I)

/-- `Φ` is an additive functor. -/
instance additive_twistedSectionsFunctor (q : ℤ) :
    (twistedSectionsFunctor I q).Additive :=
  inferInstanceAs ((twistedGeometricFactor I q ⋙ globalSectionsOver (toSpec I)).Additive)

/-- **`Φ` is `A`-linear.** -/
theorem linear_twistedSectionsFunctor (q : ℤ) :
    Functor.Linear A (twistedSectionsFunctor I q) := by
  let _ : Linear A (blowUpSpec I).Modules := blowUpModulesLinear I
  let _ : Functor.Linear A (twistedGeometricFactor I q) := linear_twistedGeometricFactor I q
  let _ : Functor.Linear A (globalSectionsOver (toSpec I)) := linear_globalSectionsOver I
  exact inferInstanceAs (Functor.Linear A
    (twistedGeometricFactor I q ⋙ globalSectionsOver (toSpec I)))

/-- **`Φ` commutes with arbitrary direct sums.** Global sections over a quasi-compact space do,
and so does the geometric factor. -/
theorem preservesColimitsOfShape_discrete_twistedSectionsFunctor
    [IsNoetherianRing A] (q : ℤ) (J : Type u) :
    PreservesColimitsOfShape (Discrete J) (twistedSectionsFunctor I q) := by
  let _ := preservesColimitsOfShape_discrete_globalSectionsOver (blowUpSpec I) (toSpec I) J
  let _ := preservesColimitsOfShape_discrete_twistedGeometricFactor I q J
  exact inferInstanceAs (PreservesColimitsOfShape (Discrete J)
    (twistedGeometricFactor I q ⋙ globalSectionsOver (toSpec I)))

section Tensor

attribute [local instance] Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorObjAdditive

/-- Any two cochain complexes of `𝒪_X`-modules on the affine blowup have a total tensor complex. -/
local instance hasMapBifunctorSheafTensorTwist :
    ∀ K₁ K₂ : CochainComplex (BlowUpModules I) ℤ,
      HomologicalComplex.HasMapBifunctor K₁ K₂
        (sheafTensor (blowUpRingedSpace I).sheaf) (ComplexShape.up ℤ) :=
  hasMapBifunctor_sheafTensor (blowUpRingedSpace I).sheaf

/-- **The structure sheaf is a unit for the twist**, `𝒪_X(q) ⊗_{𝒪_X} 𝒪_X ≅ 𝒪_X(q)`. -/
def twistTensorUnitIso (q : ℤ) :
    ((sheafTensor (blowUpRingedSpace I).sheaf).obj (blowUpTwist I q)).obj
        (SheafOfModules.unit (structureSheafRing (blowUpRingedSpace I))) ≅ blowUpTwist I q :=
  Iso.app ((sheafTensorBraiding (blowUpRingedSpace I).sheaf).app (blowUpTwist I q)) _ ≪≫
    Stacks.SheafOfModules.Strict.unitTensorIso (blowUpRingedSpace I).sheaf (blowUpTwist I q)

/-- **`Φ(A) = Γ(X, 𝒪_X(q))`**: the sheafification of `A` is the structure sheaf of `Spec A`, its
pullback is the structure sheaf of `X`, and that is a unit for the tensor product. -/
def twistedSectionsFunctorObjUnit (q : ℤ) :
    (twistedSectionsFunctor I q).obj (ModuleCat.of A A) ≅
      (globalSectionsOver (toSpec I)).obj (blowUpTwist I q) :=
  (globalSectionsOver (toSpec I)).mapIso
    (((sheafTensor (blowUpRingedSpace I).sheaf).obj (blowUpTwist I q)).mapIso
      (RingedSpaceModuleAdjunction.modulePullbackUnitIso
        (toSpecRingedSpace I)) ≪≫ twistTensorUnitIso I q)

/-- The Koszul symmetry of the total tensor complex, exchanging `p^*P̃^•` with the twist placed
in degree zero. -/
def twistedPullbackComplexFlipIso (P : CochainComplex (ModuleCat.{u} (CommRingCat.of A)) ℤ)
    (q : ℤ) :
    twistedPullbackComplex I P q ≅
      HomologicalComplex.mapBifunctor
        ((CochainComplex.singleFunctor (BlowUpModules I) 0).obj (blowUpTwist I q))
        (pullbackTildeComplex I P) (sheafTensor (blowUpRingedSpace I).sheaf)
        (ComplexShape.up ℤ) :=
  tensorComplexFlipIso (blowUpRingedSpace I).sheaf (pullbackTildeComplex I P)
    ((CochainComplex.singleFunctor (BlowUpModules I) 0).obj (blowUpTwist I q))

/-- **The total complex `Tot(p^*P̃^• ⊗ 𝒪_X(q)[0])` is `N ↦ 𝒪_X(q) ⊗ p^*(Ñ)` applied degreewise
to `P^•`.** One tensor factor is concentrated in degree zero, so the total complex is the
degreewise tensor product. -/
def twistedPullbackComplexIsoGeometric
    (P : CochainComplex (ModuleCat.{u} (CommRingCat.of A)) ℤ) (q : ℤ) :
    twistedPullbackComplex I P q ≅
      ((twistedGeometricFactor I q).mapHomologicalComplex (ComplexShape.up ℤ)).obj P :=
  letI : ((sheafTensor (blowUpRingedSpace I).sheaf).obj (blowUpTwist I q)).Additive :=
    Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorObjAdditive _ (blowUpTwist I q)
  twistedPullbackComplexFlipIso I P q ≪≫
    HomologicalComplex.mapBifunctorSingleLeftIso (sheafTensor (blowUpRingedSpace I).sheaf)
      (blowUpTwist I q) (pullbackTildeComplex I P)

/-- **The complex of `A`-linear global sections of `Tot(p^*P̃^• ⊗ 𝒪_X(q)[0])` is `Φ` applied
degreewise to `P^•`.** -/
def sectionsTwistedPullbackComplexIso
    (P : CochainComplex (ModuleCat.{u} (CommRingCat.of A)) ℤ) (q : ℤ) :
    ((globalSectionsOver (toSpec I)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (twistedPullbackComplex I P q) ≅
      ((twistedSectionsFunctor I q).mapHomologicalComplex (ComplexShape.up ℤ)).obj P :=
  ((globalSectionsOver (toSpec I)).mapHomologicalComplex (ComplexShape.up ℤ)).mapIso
    (twistedPullbackComplexIsoGeometric I P q)

/-! ### Eilenberg–Watts for `Φ` -/

/-- **The Eilenberg–Watts comparison `Φ(A) ⊗_A P^• ≅ Φ(P^•)` for a complex of free modules.**
`Φ` is `A`-linear and commutes with the direct sums indexed by the given bases, so the
comparison map is an isomorphism in each degree. -/
def wattsTwistedSectionsComplexIso [IsNoetherianRing A]
    (P : CochainComplex (ModuleCat.{u} (CommRingCat.of A)) ℤ) {J : ℤ → Type u}
    (b : ∀ i, Module.Basis (J i) A (P.X i)) (q : ℤ) :
    ((MonoidalCategory.tensorLeft
          ((twistedSectionsFunctor I q).obj (ModuleCat.of A A))).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P ≅
      ((twistedSectionsFunctor I q).mapHomologicalComplex (ComplexShape.up ℤ)).obj P :=
  letI : Functor.Linear A (twistedSectionsFunctor I q) := linear_twistedSectionsFunctor I q
  Stacks.EilenbergWatts.wattsComplexIso (twistedSectionsFunctor I q) P b
    fun i => preservesColimitsOfShape_discrete_twistedSectionsFunctor I q (J i)

/-- The identification `Φ(A) ≅ Iⁿ` carried into the degreewise tensor product with `P^•`.

The hypothesis `hsections` is the identification of [Stacks, Tag 0AG6] clause (3),
`H⁰(X, 𝒪_X(n)) = Iⁿ`, which holds for every `n` above a threshold depending only on `A` and
`I`. -/
def tensorLeftIdealPowComplexIso (n : ℕ)
    (P : CochainComplex (ModuleCat.{u} (CommRingCat.of A)) ℤ)
    (hsections : (globalSectionsOver (toSpec I)).obj (blowUpTwist I (n : ℤ)) ≅
      ModuleCat.of A (I ^ n : Ideal A)) :
    ((MonoidalCategory.tensorLeft
          ((twistedSectionsFunctor I (n : ℤ)).obj
            (ModuleCat.of A A))).mapHomologicalComplex (ComplexShape.up ℤ)).obj P ≅
      ((MonoidalCategory.tensorLeft (ModuleCat.of A (I ^ n : Ideal A))).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P :=
  (NatIso.mapHomologicalComplex
    ((MonoidalCategory.curriedTensor (ModuleCat.{u} A)).mapIso
      (twistedSectionsFunctorObjUnit I (n : ℤ) ≪≫ hsections)) (ComplexShape.up ℤ)).app P

/-- **The complex of `A`-linear global sections of `Tot(p^*P̃^• ⊗ 𝒪_X(n)[0])` is `Iⁿ ⊗_A P^•`**,
for `P^•` a complex of free `A`-modules.

The hypothesis `hsections` is the identification of [Stacks, Tag 0AG6] clause (3). -/
def sectionsTwistedPullbackComplexTensorIdealPowIso [IsNoetherianRing A]
    (P : CochainComplex (ModuleCat.{u} (CommRingCat.of A)) ℤ) {J : ℤ → Type u}
    (b : ∀ i, Module.Basis (J i) A (P.X i)) (n : ℕ)
    (hsections : (globalSectionsOver (toSpec I)).obj (blowUpTwist I (n : ℤ)) ≅
      ModuleCat.of A (I ^ n : Ideal A)) :
    ((globalSectionsOver (toSpec I)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (twistedPullbackComplex I P (n : ℤ)) ≅
      ((MonoidalCategory.tensorLeft (ModuleCat.of A (I ^ n : Ideal A))).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P :=
  sectionsTwistedPullbackComplexIso I P (n : ℤ) ≪≫
    (wattsTwistedSectionsComplexIso I P b (n : ℤ)).symm ≪≫
    tensorLeftIdealPowComplexIso I n P hsections

/-! ### The identification in `D(A)` -/

attribute [local instance 10000] HasDerivedCategory.standard

/-- The `A`-linear derived global sections of a complex of `𝒪_X`-modules, read through the
complex of its `A`-linear global sections. -/
def derivedSectionsTwistedPullbackComplexIso
    (P : CochainComplex (ModuleCat.{u} (CommRingCat.of A)) ℤ) (q : ℤ) :
    (AlgebraicGeometry.homotopyGlobalSectionsOver (toSpec I)).obj
        ((HomotopyCategory.quotient (blowUpSpec I).Modules (ComplexShape.up ℤ)).obj
          (twistedPullbackComplex I P q)) ≅
      DerivedCategory.Q.obj
        (((globalSectionsOver (toSpec I)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (twistedPullbackComplex I P q)) :=
  DerivedCategory.Qh.mapIso
      ((((globalSectionsOver (toSpec I)).mapHomotopyCategoryFactors
        (ComplexShape.up ℤ)).app (twistedPullbackComplex I P q)).symm) ≪≫
    (DerivedCategory.quotientCompQhIso (ModuleCat.{u} A)).app _

/-- **`RΓ(X, Lp^*(M̃) ⊗^𝐋 𝒪_X(n))` is the complex `Iⁿ ⊗_A P^•`** in `D(A)`, for `P^• ⟶ M` a
K-flat resolution by free `A`-modules.

The hypotheses `hvanish` and `hsections` are the vanishing of [Stacks, Tag 0AG7] and the
identification of [Stacks, Tag 0AG6] clause (3), both of which hold for every `n` above a
threshold depending only on `A` and `I`. -/
def derivedGlobalSectionsTwistedPullbackIsoTensorIdealPow [IsNoetherianRing A]
    (M : ModuleCat.{u} (CommRingCat.of A))
    (P : CochainComplex (ModuleCat.{u} (CommRingCat.of A)) ℤ)
    (hP : CochainComplex.KFlat.{u, u} P)
    (g : P ⟶ (CochainComplex.singleFunctor (ModuleCat.{u} (CommRingCat.of A)) 0).obj M)
    (hg : QuasiIso g) {J : ℤ → Type u}
    (b : ∀ i, Module.Basis (J i) A (P.X i)) (n : ℕ)
    (hvanish : ∀ j : ℤ, 0 < j →
      IsZero (((Stacks.Cohomology.sectionsFunctor (blowUpSpec I) ⊤).rightDerivedPlus j).obj
        (blowUpTwist I (n : ℤ))))
    (hsections : (globalSectionsOver (toSpec I)).obj (blowUpTwist I (n : ℤ)) ≅
      ModuleCat.of A (I ^ n : Ideal A)) :
    (AlgebraicGeometry.derivedGlobalSectionsOver (toSpec I)).obj
        (((Stacks.Cohomology.TorAmplitude.derTensor (blowUpRingedSpace I)).tensor.obj
            ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
              (toSpecRingedSpace I)).obj (DerivedCategory.Q.obj (tildeComplex
                ((CochainComplex.singleFunctor (ModuleCat.{u} (CommRingCat.of A)) 0).obj
                  M))))).obj
          (DerivedCategory.Q.obj
            ((CochainComplex.singleFunctor (BlowUpModules I) 0).obj
              (blowUpTwist I (n : ℤ))))) ≅
      DerivedCategory.Q.obj
        (((MonoidalCategory.tensorLeft
            (ModuleCat.of A (I ^ n : Ideal A))).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P) :=
  derivedGlobalSectionsTwistedPullbackIso I M P hP g hg b (n : ℤ) hvanish ≪≫
    derivedSectionsTwistedPullbackComplexIso I P (n : ℤ) ≪≫
    DerivedCategory.Q.mapIso
      (sectionsTwistedPullbackComplexTensorIdealPowIso I P b n hsections)

/-- **Cohomology of the twisted derived pullback along the affine blowup.** For `A` Noetherian,
`I ⊆ A` an ideal, `p : X ⟶ Spec A` the blowup of `Spec A` in `I` and any `A`-module `M`,

`RΓ(X, Lp^*(M̃) ⊗^𝐋_{𝒪_X} 𝒪_X(n)) ≅ M ⊗^𝐋_A Iⁿ`  in `D(A)`,

at a fixed `n` satisfying the hypotheses `hvanish`, the vanishing `H^j(X, 𝒪_X(n)) = 0` for
`j > 0` of [Stacks, Tag 0AG7], and `hsections`, the identification `H⁰(X, 𝒪_X(n)) = Iⁿ` of
[Stacks, Tag 0AG6] clause (3). -/
theorem nonempty_derivedGlobalSectionsTwistedPullback_iso_derivedTensorIdealPow
    [IsNoetherianRing A]
    (M : ModuleCat.{u} (CommRingCat.of A)) (n : ℕ)
    (hvanish : ∀ j : ℤ, 0 < j →
      IsZero (((Stacks.Cohomology.sectionsFunctor (blowUpSpec I) ⊤).rightDerivedPlus j).obj
        (blowUpTwist I (n : ℤ))))
    (hsections : (globalSectionsOver (toSpec I)).obj (blowUpTwist I (n : ℤ)) ≅
      ModuleCat.of A (I ^ n : Ideal A)) :
    Nonempty ((AlgebraicGeometry.derivedGlobalSectionsOver (toSpec I)).obj
        (((Stacks.Cohomology.TorAmplitude.derTensor (blowUpRingedSpace I)).tensor.obj
            ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
              (toSpecRingedSpace I)).obj (DerivedCategory.Q.obj (tildeComplex
                ((CochainComplex.singleFunctor (ModuleCat.{u} (CommRingCat.of A)) 0).obj
                  M))))).obj
          (DerivedCategory.Q.obj
            ((CochainComplex.singleFunctor (BlowUpModules I) 0).obj
              (blowUpTwist I (n : ℤ))))) ≅
      ((CochainComplex.DerivedTensor.canonicalDerivedTensorProduct A).tensor.obj
          (DerivedCategory.Q.obj
            ((CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj M))).obj
        (DerivedCategory.Q.obj
          ((CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj
            (ModuleCat.of A (I ^ n : Ideal A))))) := by
  obtain ⟨P, g, hP, -, hfree, hg⟩ := CochainComplex.KFlat.exists_free_kFlat_resolution M
  let _ : ∀ i : ℤ, Module.Free A (P.X i) := hfree
  exact (CochainComplex.DerivedTensor.nonempty_derivedTensor_iso_tensorLeft_kFlat_resolution
      M (ModuleCat.of A (I ^ n : Ideal A)) P hP g hg).map fun e =>
    derivedGlobalSectionsTwistedPullbackIsoTensorIdealPow I M P hP g hg
      (fun i => Module.Free.chooseBasis A (P.X i)) n hvanish hsections ≪≫ e.symm

/-- **Cohomology of the twisted derived pullback along the affine blowup, above a threshold.**
Let `A` be a Noetherian ring, `I ⊆ A` an ideal and `p : X ⟶ Spec A` the blowup of `Spec A` in
`I`. There is a `q₀` such that for every `n ≥ q₀` at which `H⁰(X, 𝒪_X(n)) ≅ Iⁿ` and every
`A`-module `M`,

`RΓ(X, Lp^*(M̃) ⊗^𝐋_{𝒪_X} 𝒪_X(n)) ≅ M ⊗^𝐋_A Iⁿ`  in `D(A)`. -/
theorem exists_forall_nonempty_derivedGlobalSectionsTwistedPullback_iso_derivedTensorIdealPow
    [IsNoetherianRing A] :
    ∃ q₀ : ℕ, ∀ n : ℕ, q₀ ≤ n →
      ∀ _hsections : (globalSectionsOver (toSpec I)).obj (blowUpTwist I (n : ℤ)) ≅
          ModuleCat.of A (I ^ n : Ideal A),
      ∀ M : ModuleCat.{u} (CommRingCat.of A),
        Nonempty ((AlgebraicGeometry.derivedGlobalSectionsOver (toSpec I)).obj
            (((Stacks.Cohomology.TorAmplitude.derTensor (blowUpRingedSpace I)).tensor.obj
                ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
                  (toSpecRingedSpace I)).obj (DerivedCategory.Q.obj (tildeComplex
                    ((CochainComplex.singleFunctor (ModuleCat.{u} (CommRingCat.of A)) 0).obj
                      M))))).obj
              (DerivedCategory.Q.obj
                ((CochainComplex.singleFunctor (BlowUpModules I) 0).obj
                  (blowUpTwist I (n : ℤ))))) ≅
          ((CochainComplex.DerivedTensor.canonicalDerivedTensorProduct A).tensor.obj
              (DerivedCategory.Q.obj
                ((CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj M))).obj
            (DerivedCategory.Q.obj
              ((CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj
                (ModuleCat.of A (I ^ n : Ideal A))))) := by
  obtain ⟨q₀, hq₀⟩ := exists_forall_isZero_rightDerivedPlus_twistingSheaf_reesGrading I
  exact ⟨q₀, fun n hn hsections M =>
    nonempty_derivedGlobalSectionsTwistedPullback_iso_derivedTensorIdealPow I M n
      (hq₀ n hn) hsections⟩

end Tensor

end Stacks.Blowup

end
