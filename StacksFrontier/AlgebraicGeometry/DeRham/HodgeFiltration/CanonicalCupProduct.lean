module

public import StacksFrontier.Algebra.Homology.Embedding.ExtendMap
public import StacksFrontier.Algebra.Homology.Embedding.MapBifunctorExtend
public import StacksFrontier.AlgebraicGeometry.DeRham.FirstChernClass.FilteredChernCupProduct
public import StacksFrontier.AlgebraicGeometry.DeRham.RealizationComparison
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.DerivedSectionsModelComparison
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.CupPairingNaturality
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.GlobalKunnethMapCanonical
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.GlobalCupProductCocycles
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.RealizationShift
public import StacksFrontier.Topology.Sheaves.Cohomology.FilteredComplexSpectralSequence.CartanEilenbergComparison
import StacksCore.Tactic.StacksAttribute

/-!
# The cup product on the hypercohomology of the brutal truncations

Let `φ : A ⟶ 𝒪_X` be a morphism of sheaves of commutative rings on a ringed space `X`. For
`ℕ`-indexed complexes `K`, `L`, `M` of sheaves of `A`-modules and a multiplication
`m : Tot(K ⊗_A L) ⟶ M`, Cohomology, Section 0FKU produces the cup product

`H^i(X, K) × H^j(X, L) ⟶ H^{i+j}(X, K ⊗^𝐋_A L) ⟶ H^{i+j}(X, Tot(K ⊗_A L)) ⟶ H^{i+j}(X, M)`:

the pairing induced by the global cup product `RΓ(X, K) ⊗^𝐋 RΓ(X, L) ⟶ RΓ(X, K ⊗^𝐋 L)`, followed
by the canonical map from the derived to the ordinary tensor product and by `m`. This file
constructs it, with no parameter, from the global cup product
`Stacks.Cohomology.DerivedGlobalCupProduct.cupProductOnSpace` of the ringed space `(X, A)` — the
relative cup product of Tag 0B68 for the morphism to the point `({*}, Γ(X, A))`, built from the
canonical one-point comparison, for which the cocycle description of Tag 0FP3 and Tag 0FKV are
proved — and proves that it is natural. This is the datum
`AlgebraicGeometry.SheafOfModules.TruncationCupProduct` of
`StacksFrontier.AlgebraicGeometry.DeRham.FirstChernClass.FilteredChernCupProduct` asks for, so every
statement proved there for an arbitrary such datum holds for the cup product of the source.

Applied to the multiplication `σ^{≥i}Ω^• ⊗_A σ^{≥j}Ω^• ⟶ σ^{≥(i + j)}Ω^•` of the Hodge filtration
(Tag 0FM2 restricted to the brutal truncations) this gives the cup products of Section 50.7,
Tag 0FM7,

`H^n(X, σ^{≥i}Ω^•_{X/S}) × H^m(X, σ^{≥j}Ω^•_{X/S}) ⟶ H^{n + m}(X, σ^{≥(i + j)}Ω^•_{X/S})`,

the commutative diagram relating them to the cup product on `H^*_{dR}(X/S)`, and the
multiplicativity `F^iH^n_{dR} ∪ F^jH^m_{dR} ⊂ F^{i + j}H^{n + m}_{dR}` of the Hodge filtration.

## Main definitions

* `AlgebraicGeometry.SheafOfModules.moduleHypercohomologyIso`: the hypercohomology of the
  abelianisation of a complex of sheaves of `A`-modules is the cohomology of its derived global
  sections in modules ([Stacks, Tag 01F1]).
* `AlgebraicGeometry.SheafOfModules.canonicalPairing`: **the cup product of Section 0FKU along a
  multiplication**, with no parameter.
* `AlgebraicGeometry.SheafOfModules.truncationCupProduct`: the cup product with its naturality,
  as a `TruncationCupProduct`.
* `AlgebraicGeometry.SheafOfModules.hodgeFiltrationCup`: **the cup product of Section 50.7 on the
  hypercohomology of the brutal truncations.**
* `AlgebraicGeometry.SheafOfModules.deRhamCup`: the cup product on `H^*_{dR}(X/S)`.

## Main results

* `AlgebraicGeometry.SheafOfModules.canonicalPairing_naturality`: the cup product is natural.
* `AlgebraicGeometry.SheafOfModules.truncatedDeRhamCohomologyAbelianMap_hodgeFiltrationCup`: **the
  commutative diagram of Section 50.7.**
* `AlgebraicGeometry.SheafOfModules.deRhamCup_mem_hodgeFiltrationAbelian`: **the Hodge filtration
  is multiplicative**, `F^iH^n_{dR} ∪ F^jH^m_{dR} ⊂ F^{i + j}H^{n + m}_{dR}`.
* `SheafOfModules.exists_hodgeFiltrationSpectralSequence_iso_cartanEilenbergFirst`: the spectral
  sequence of the Hodge filtration is the Hodge-to-de Rham spectral sequence of Section 0FM6,
  built from a Cartan-Eilenberg resolution.

## References

* [Stacks Project, Section 0FM7](https://stacks.math.columbia.edu/tag/0FM7)
* [Stacks Project, Section 0FKU](https://stacks.math.columbia.edu/tag/0FKU)
* [Stacks Project, Tag 01F1](https://stacks.math.columbia.edu/tag/01F1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory ComplexShape Opposite
open TopologicalSpace
open Stacks.Cohomology.Leray (AbelianSheaf sectionsFunctor)
open Stacks.Cohomology.GlobalKunneth Stacks.Cohomology.DerivedGlobalCupProduct
open Stacks.DerivedTensor.RingedSite
open Stacks.SheafOfModules.Tensor (sheafTensor)
open scoped Stacks.Topology.SheafTensorAdditiveOnOpens CategoryTheory.Prod

universe u

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  Stacks.SheafOfModules.Tensor.ringSheaf

namespace AlgebraicGeometry.SheafOfModules

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Stacks.DerivedIndexing.commShiftRightDerivedFunctorPlus
attribute [local instance] abelianModules hasSheafifyOpens wEqualsLocallyBijectiveOpens

variable {X : RingedSpace.{u, u}} {A : TopCat.Sheaf CommRingCat.{u} X.carrier}

/-- Pasting a commutative square `a ≫ b = c ≫ d` with a commutative square `d ≫ e = f ≫ g`. -/
private lemma square_paste {C : Type*} [Category C] {P Q R S T U : C} {a : P ⟶ Q} {b : Q ⟶ R}
    {c : P ⟶ S} {d : S ⟶ R} {e : R ⟶ T} {f : S ⟶ U} {g : U ⟶ T} (h₁ : a ≫ b = c ≫ d)
    (h₂ : d ≫ e = f ≫ g) : a ≫ b ≫ e = (c ≫ f) ≫ g := by
  rw [← Category.assoc, h₁, Category.assoc, h₂, Category.assoc]

/-- A functor carries a commutative square `a ≫ b = c ≫ d` to a commutative square. -/
private lemma map_square {C D : Type*} [Category C] [Category D] (F : C ⥤ D) {P Q R S : C}
    {a : P ⟶ Q} {b : Q ⟶ R} {c : P ⟶ S} {d : S ⟶ R} (h : a ≫ b = c ≫ d) :
    F.map a ≫ F.map b = F.map c ≫ F.map d := by
  rw [← F.map_comp, ← F.map_comp, h]

/-! ### Complexes of sheaves of modules in the derived category -/

/-- An `ℕ`-indexed complex of sheaves of `A`-modules, extended by zero, as a bounded below complex
of modules over the structure sheaf of the ringed space `(X, A)`. -/
abbrev moduleComplexPlus (K : CochainComplex
    (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A)) ℕ) :
    CochainComplex.Plus
      (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A)) :=
  ⟨K.extend embeddingUpNat, 0, inferInstance⟩

/-- A morphism of `ℕ`-indexed complexes of sheaves of `A`-modules, extended by zero. -/
abbrev moduleComplexPlusMap {K L : CochainComplex
    (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A)) ℕ}
    (f : K ⟶ L) : moduleComplexPlus K ⟶ moduleComplexPlus L :=
  ⟨HomologicalComplex.extendMap f embeddingUpNat⟩

/-- An `ℕ`-indexed complex of sheaves of `A`-modules, extended by zero, as an object of the derived
category of sheaves of modules over `(X, A)`. -/
abbrev moduleDerived (K : CochainComplex
    (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A)) ℕ) :
    DerivedCategory (_root_.SheafOfModules.{u} (structureSheafRing (baseRingedSpace A))) :=
  DerivedCategory.Q.obj (K.extend embeddingUpNat)

/-- The abelianised and extended complex is the underlying complex of abelian sheaves of the
extended complex of modules. -/
def modulePlusIso (K : CochainComplex
    (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A)) ℕ) :
    modulePlus (A := A) K ≅
      (_root_.SheafOfModules.toSheaf
        (structureSheafRing (baseRingedSpace A))).mapCochainComplexPlus.obj
          (moduleComplexPlus K) :=
  ObjectProperty.isoMk _ (HomologicalComplex.mapHomologicalComplexExtendIso
    (_root_.SheafOfModules.toSheaf (underlyingRingSheaf A)) K embeddingUpNat)

/-- The identification `modulePlusIso` is natural in the complex. -/
theorem modulePlusIso_naturality {K L : CochainComplex
    (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A)) ℕ}
    (f : K ⟶ L) :
    modulePlusMap (A := A) f ≫ (modulePlusIso L).hom =
      (modulePlusIso K).hom ≫
        (_root_.SheafOfModules.toSheaf
          (structureSheafRing (baseRingedSpace A))).mapCochainComplexPlus.map
            (moduleComplexPlusMap f) := by
  have h := HomologicalComplex.mapHomologicalComplexExtendIso_inv_naturality
    (_root_.SheafOfModules.toSheaf (underlyingRingSheaf A)) K f embeddingUpNat
  have h' : HomologicalComplex.extendMap
        (((_root_.SheafOfModules.toSheaf (underlyingRingSheaf A)).mapHomologicalComplex
          (up ℕ)).map f) embeddingUpNat ≫
      (HomologicalComplex.mapHomologicalComplexExtendIso
        (_root_.SheafOfModules.toSheaf (underlyingRingSheaf A)) L embeddingUpNat).hom =
      (HomologicalComplex.mapHomologicalComplexExtendIso
        (_root_.SheafOfModules.toSheaf (underlyingRingSheaf A)) K embeddingUpNat).hom ≫
      ((_root_.SheafOfModules.toSheaf (underlyingRingSheaf A)).mapHomologicalComplex
          (up ℤ)).map (HomologicalComplex.extendMap f embeddingUpNat) := by
    rw [← Iso.inv_comp_eq, ← Category.assoc, ← h, Category.assoc, Iso.inv_hom_id,
      Category.comp_id]
  exact ObjectProperty.hom_ext _ h'

/-- **The hypercohomology of the abelianisation of a complex of sheaves of `A`-modules is the
cohomology of its derived global sections in modules** ([Stacks, Tag 01F1]), the module
structure forgotten: the realization comparison
`Stacks.Cohomology.RealizationShift.realizationIsoAt`, which commutes with the shift
identifications (`Stacks.Cohomology.RealizationShift.realizationIsoAt_shift`), read through the
identification of the abelianisation with the underlying complex of abelian sheaves. -/
@[ega "III 6.2.1" "partial"]
def moduleHypercohomologyIso (K : CochainComplex
    (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A)) ℕ) (n : ℤ) :
    moduleHypercohomology (A := A) K n ≅
      (forget₂ (ModuleCat.{u} (baseRing (baseRingedSpace A))) AddCommGrpCat.{u}).obj
        (cohomologyModule (moduleDerived K) n) :=
  (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} n).mapIso
      ((sectionsFunctor X.carrier ⊤).rightDerivedFunctorPlus.mapIso
        (DerivedCategory.Plus.Q.mapIso (modulePlusIso K))) ≪≫
    Stacks.Cohomology.RealizationShift.realizationIsoAt (baseRingedSpace A) (moduleComplexPlus K) n

/-- The identification `moduleHypercohomologyIso` is natural in the complex. -/
theorem moduleHypercohomologyIso_naturality {K L : CochainComplex
    (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A)) ℕ}
    (f : K ⟶ L) (n : ℤ) :
    moduleHypercohomologyMap (A := A) f n ≫ (moduleHypercohomologyIso L n).hom =
      (moduleHypercohomologyIso K n).hom ≫
        (forget₂ (ModuleCat.{u} (baseRing (baseRingedSpace A))) AddCommGrpCat.{u}).map
          ((DerivedCategory.homologyFunctor _ n).map
            ((baseSections (baseRingedSpace A)).map
              (DerivedCategory.Q.map (HomologicalComplex.extendMap f embeddingUpNat)))) := by
  let H := DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} n
  let Φ := (sectionsFunctor X.carrier ⊤).rightDerivedFunctorPlus
  have h₁ := map_square (DerivedCategory.Plus.Q ⋙ Φ ⋙ H) (modulePlusIso_naturality (A := A) f)
  have h₂ := Stacks.Cohomology.RealizationShift.realizationIsoAt_naturality (baseRingedSpace A)
    (moduleComplexPlusMap f) n
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) h₁).trans
    ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) h₂).trans (Category.assoc _ _ _).symm)))

/-- The identification `moduleHypercohomologyIso` is natural in the complex, on elements. -/
private lemma moduleHypercohomologyIso_naturality_apply {K L : CochainComplex
    (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A)) ℕ}
    (f : K ⟶ L) (n : ℤ) (x : moduleHypercohomology (A := A) K n) :
    ((moduleHypercohomologyIso L n).hom.hom ((moduleHypercohomologyMap (A := A) f n).hom x) :
        cohomologyModule (moduleDerived L) n) =
      ((DerivedCategory.homologyFunctor _ n).map ((baseSections (baseRingedSpace A)).map
        (DerivedCategory.Q.map (HomologicalComplex.extendMap f embeddingUpNat)))).hom
        ((moduleHypercohomologyIso K n).hom.hom x) :=
  ConcreteCategory.congr_hom (moduleHypercohomologyIso_naturality f n) x

/-- The identification `moduleHypercohomologyIso`, inverted, is natural in the complex. -/
theorem moduleHypercohomologyIso_inv_naturality_apply {K L : CochainComplex
    (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A)) ℕ}
    (f : K ⟶ L) (n : ℤ) (z : cohomologyModule (moduleDerived K) n) :
    (moduleHypercohomologyMap (A := A) f n).hom ((moduleHypercohomologyIso K n).inv.hom z) =
      (moduleHypercohomologyIso L n).inv.hom
        (((DerivedCategory.homologyFunctor _ n).map
          ((baseSections (baseRingedSpace A)).map
            (DerivedCategory.Q.map (HomologicalComplex.extendMap f embeddingUpNat)))).hom z) := by
  have h : (moduleHypercohomologyIso K n).inv ≫ moduleHypercohomologyMap (A := A) f n =
      (forget₂ (ModuleCat.{u} (baseRing (baseRingedSpace A))) AddCommGrpCat.{u}).map
          ((DerivedCategory.homologyFunctor _ n).map
            ((baseSections (baseRingedSpace A)).map
              (DerivedCategory.Q.map (HomologicalComplex.extendMap f embeddingUpNat)))) ≫
        (moduleHypercohomologyIso L n).inv := by
    rw [Iso.eq_comp_inv, Category.assoc, moduleHypercohomologyIso_naturality,
      Iso.inv_hom_id_assoc]
  exact ConcreteCategory.congr_hom h z

/-! ### The cup product along a multiplication -/

section Pairing

variable {K K' L L' M M' : CochainComplex
  (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A)) ℕ}

/-- The total complex functor on `ℕ`-indexed complexes composes the tensor product in each
variable: tensoring with `g` on the right and then with `f` on the left is `f ⊗ g`. -/
theorem mapBifunctorMap_id_comp_id (f : K ⟶ K') (g : L ⟶ L') :
    HomologicalComplex.mapBifunctorMap (𝟙 K) g (sheafTensor.{u, u, u, u, u} A) (up ℕ) ≫
        HomologicalComplex.mapBifunctorMap f (𝟙 L') (sheafTensor.{u, u, u, u, u} A) (up ℕ) =
      HomologicalComplex.mapBifunctorMap f g (sheafTensor.{u, u, u, u, u} A) (up ℕ) := by
  refine HomologicalComplex.hom_ext _ _ fun n => HomologicalComplex.mapBifunctor.hom_ext
    fun p q hpq => ?_
  simp

/-- **A multiplication `Tot(K ⊗_A L) ⟶ M` of `ℕ`-indexed complexes, read on the extensions by
zero**: the comparison of the `ℤ`-indexed total complex of the extensions with the extension of
the `ℕ`-indexed total complex, followed by the extension of `m`. -/
def multiplicationInt (m : ((tensorBifunctorNat (A := A)).obj K).obj L ⟶ M) :
    HomologicalComplex.mapBifunctor (K.extend embeddingUpNat) (L.extend embeddingUpNat)
        (sheafTensor.{u, u, u, u, u} A) (up ℤ) ⟶ M.extend embeddingUpNat :=
  HomologicalComplex.mapBifunctorExtendHom (sheafTensor.{u, u, u, u, u} A) K L ≫
    HomologicalComplex.extendMap m embeddingUpNat

/-- The extended multiplications of two multiplications compatible along `f`, `g` and `h` are
compatible along the extensions of `f`, `g` and `h`. -/
theorem multiplicationInt_naturality (f : K ⟶ K') (g : L ⟶ L')
    (m : ((tensorBifunctorNat (A := A)).obj K).obj L ⟶ M)
    (m' : ((tensorBifunctorNat (A := A)).obj K').obj L' ⟶ M') (h : M ⟶ M')
    (hm : m ≫ h = ((tensorBifunctorNat (A := A)).obj K).map g ≫
      ((tensorBifunctorNat (A := A)).map f).app L' ≫ m') :
    HomologicalComplex.mapBifunctorMap (HomologicalComplex.extendMap f embeddingUpNat)
        (HomologicalComplex.extendMap g embeddingUpNat) (sheafTensor.{u, u, u, u, u} A) (up ℤ) ≫
        multiplicationInt m' =
      multiplicationInt m ≫ HomologicalComplex.extendMap h embeddingUpNat := by
  have hm' : HomologicalComplex.mapBifunctorMap f g (sheafTensor.{u, u, u, u, u} A) (up ℕ) ≫ m' =
      m ≫ h := by
    rw [hm, ← Category.assoc]
    exact congrArg (· ≫ m') (mapBifunctorMap_id_comp_id f g).symm
  exact square_paste (HomologicalComplex.mapBifunctorExtendHom_naturality f g)
    ((HomologicalComplex.extendMap_comp _ _ _).symm.trans
      ((congrArg (HomologicalComplex.extendMap · embeddingUpNat) hm').trans
        (HomologicalComplex.extendMap_comp _ _ _)))

/-- **The cup product of Cohomology, Section 0FKU along a multiplication**, on cohomology modules:
`H^i(X, K) ⊗ H^j(X, L) ⟶ H^{i + j}(X, K ⊗^𝐋 L) ⟶ H^{i + j}(X, Tot(K ⊗ L)) ⟶ H^{i + j}(X, M)`, the
pairing of the global cup product `cupProductOnSpace` of the ringed space `(X, A)`, followed by the
canonical map from the derived to the ordinary tensor product and by `m`. -/
@[ega "0 12.1.5" "more general"]
def canonicalPairingModule (m : ((tensorBifunctorNat (A := A)).obj K).obj L ⟶ M) (i j : ℤ) :
    cohomologyModule (moduleDerived K) i ⊗ cohomologyModule (moduleDerived L) j ⟶
      cohomologyModule (moduleDerived M) (i + j) :=
  cupPairing (Stacks.Cohomology.DerivedGlobalCupProduct.cupProductOnSpace (baseRingedSpace A))
      (moduleDerived K) (moduleDerived L)
      i j ≫
    (DerivedCategory.homologyFunctor _ (i + j)).map ((baseSections (baseRingedSpace A)).map
      ((canonicalDerivedTensorProduct (baseRingedSpace A).sheaf).toTensor
          (K.extend embeddingUpNat) (L.extend embeddingUpNat) ≫
        DerivedCategory.Q.map (multiplicationInt m)))

/-- The derived-level form of `multiplicationInt_naturality`: the derived tensor product of the
extensions of `f` and `g`, followed by the canonical map to the ordinary tensor product and the
extended `m'`, is the canonical map followed by the extended `m` and the extension of `h`. -/
theorem toTensor_multiplicationInt_naturality (f : K ⟶ K') (g : L ⟶ L')
    (m : ((tensorBifunctorNat (A := A)).obj K).obj L ⟶ M)
    (m' : ((tensorBifunctorNat (A := A)).obj K').obj L' ⟶ M') (h : M ⟶ M')
    (hm : m ≫ h = ((tensorBifunctorNat (A := A)).obj K).map g ≫
      ((tensorBifunctorNat (A := A)).map f).app L' ≫ m') :
    (Functor.uncurry.obj (derivedTensorProductFunctor (baseRingedSpace A).sheaf)).map
        (DerivedCategory.Q.map (HomologicalComplex.extendMap f embeddingUpNat) ×ₘ
          DerivedCategory.Q.map (HomologicalComplex.extendMap g embeddingUpNat)) ≫
        (canonicalDerivedTensorProduct (baseRingedSpace A).sheaf).toTensor
          (K'.extend embeddingUpNat) (L'.extend embeddingUpNat) ≫
        DerivedCategory.Q.map (multiplicationInt m') =
      ((canonicalDerivedTensorProduct (baseRingedSpace A).sheaf).toTensor
          (K.extend embeddingUpNat) (L.extend embeddingUpNat) ≫
        DerivedCategory.Q.map (multiplicationInt m)) ≫
        DerivedCategory.Q.map (HomologicalComplex.extendMap h embeddingUpNat) := by
  have hT : (Functor.uncurry.obj (derivedTensorProductFunctor (baseRingedSpace A).sheaf)).map
        (DerivedCategory.Q.map (HomologicalComplex.extendMap f embeddingUpNat) ×ₘ
          DerivedCategory.Q.map (HomologicalComplex.extendMap g embeddingUpNat)) ≫
        (canonicalDerivedTensorProduct (baseRingedSpace A).sheaf).toTensor
          (K'.extend embeddingUpNat) (L'.extend embeddingUpNat) =
      (canonicalDerivedTensorProduct (baseRingedSpace A).sheaf).toTensor
          (K.extend embeddingUpNat) (L.extend embeddingUpNat) ≫
        DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap
          (HomologicalComplex.extendMap f embeddingUpNat)
          (HomologicalComplex.extendMap g embeddingUpNat) (sheafTensor.{u, u, u, u, u} A)
          (up ℤ)) :=
    (Category.assoc _ _ _).trans
      ((canonicalDerivedTensorProduct (baseRingedSpace A).sheaf).toTensor_naturality _ _)
  exact square_paste hT
    (map_square DerivedCategory.Q (multiplicationInt_naturality f g m m' h hm))

/-- **The cup product along a multiplication is natural.** -/
theorem canonicalPairingModule_naturality (f : K ⟶ K') (g : L ⟶ L')
    (m : ((tensorBifunctorNat (A := A)).obj K).obj L ⟶ M)
    (m' : ((tensorBifunctorNat (A := A)).obj K').obj L' ⟶ M') (h : M ⟶ M')
    (hm : m ≫ h = ((tensorBifunctorNat (A := A)).obj K).map g ≫
      ((tensorBifunctorNat (A := A)).map f).app L' ≫ m') (i j : ℤ)
    (x : cohomologyModule (moduleDerived K) i) (y : cohomologyModule (moduleDerived L) j) :
    ((DerivedCategory.homologyFunctor _ (i + j)).map ((baseSections (baseRingedSpace A)).map
        (DerivedCategory.Q.map (HomologicalComplex.extendMap h embeddingUpNat)))).hom
        ((canonicalPairingModule m i j).hom (x ⊗ₜ y)) =
      (canonicalPairingModule m' i j).hom
        (((DerivedCategory.homologyFunctor _ i).map ((baseSections (baseRingedSpace A)).map
            (DerivedCategory.Q.map (HomologicalComplex.extendMap f embeddingUpNat)))).hom x ⊗ₜ
          ((DerivedCategory.homologyFunctor _ j).map ((baseSections (baseRingedSpace A)).map
            (DerivedCategory.Q.map (HomologicalComplex.extendMap g embeddingUpNat)))).hom y) := by
  have e₁ := cupPairing_naturality_apply
    (Stacks.Cohomology.DerivedGlobalCupProduct.cupProductOnSpace (baseRingedSpace A))
    (DerivedCategory.Q.map (HomologicalComplex.extendMap f embeddingUpNat))
    (DerivedCategory.Q.map (HomologicalComplex.extendMap g embeddingUpNat)) i j x y
  have e₂ := map_square
    (baseSections (baseRingedSpace A) ⋙ DerivedCategory.homologyFunctor _ (i + j))
    (toTensor_multiplicationInt_naturality f g m m' h hm)
  refine Eq.trans ?_ (congrArg (ModuleCat.Hom.hom ((DerivedCategory.homologyFunctor _ (i + j)).map
    ((baseSections (baseRingedSpace A)).map
      ((canonicalDerivedTensorProduct (baseRingedSpace A).sheaf).toTensor
          (K'.extend embeddingUpNat) (L'.extend embeddingUpNat) ≫
        DerivedCategory.Q.map (multiplicationInt m'))))) e₁).symm
  have e₃ := ConcreteCategory.congr_hom e₂
    ((cupPairing (Stacks.Cohomology.DerivedGlobalCupProduct.cupProductOnSpace (baseRingedSpace A))
      (moduleDerived K)
      (moduleDerived L) i j).hom (x ⊗ₜ y))
  exact e₃.symm

/-- **The cup product of Cohomology, Section 0FKU along a multiplication**,

`∪ : H^i(X, K) × H^j(X, L) ⟶ H^{i + j}(X, M)`

for a multiplication `m : Tot(K ⊗_A L) ⟶ M` of `ℕ`-indexed complexes of sheaves of `A`-modules,
on the hypercohomology of their abelianisations: `canonicalPairingModule` read through the
identification `moduleHypercohomologyIso` of Tag 01F1. It is built from the global cup product
`Stacks.Cohomology.DerivedGlobalCupProduct.cupProductOnSpace`, with no parameter. -/
@[ega "0 12.1.5" "more general"]
def canonicalPairing : HypercohomologyPairing (A := A) := fun {K L M} m i j x y =>
  (moduleHypercohomologyIso M (i + j)).inv.hom ((canonicalPairingModule m i j).hom
    (((moduleHypercohomologyIso K i).hom.hom x : cohomologyModule (moduleDerived K) i) ⊗ₜ
      ((moduleHypercohomologyIso L j).hom.hom y : cohomologyModule (moduleDerived L) j)))

/-- **The cup product along a multiplication is natural**: restricting the two factors along `f`
and `g` and the product along `h` are compatible whenever the multiplications are. -/
theorem canonicalPairing_naturality (f : K ⟶ K') (g : L ⟶ L')
    (m : ((tensorBifunctorNat (A := A)).obj K).obj L ⟶ M)
    (m' : ((tensorBifunctorNat (A := A)).obj K').obj L' ⟶ M') (h : M ⟶ M')
    (hm : m ≫ h = ((tensorBifunctorNat (A := A)).obj K).map g ≫
      ((tensorBifunctorNat (A := A)).map f).app L' ≫ m') (i j : ℤ)
    (x : moduleHypercohomology (A := A) K i) (y : moduleHypercohomology (A := A) L j) :
    (moduleHypercohomologyMap (A := A) h (i + j)).hom (canonicalPairing m i j x y) =
      canonicalPairing m' i j ((moduleHypercohomologyMap (A := A) f i).hom x)
        ((moduleHypercohomologyMap (A := A) g j).hom y) := by
  refine (moduleHypercohomologyIso_inv_naturality_apply h (i + j) _).trans ?_
  refine congrArg (moduleHypercohomologyIso M' (i + j)).inv.hom
    ((canonicalPairingModule_naturality f g m m' h hm i j _ _).trans ?_)
  rw [moduleHypercohomologyIso_naturality_apply, moduleHypercohomologyIso_naturality_apply]

end Pairing

/-- **The cup product of Cohomology, Section 0FKU, with its naturality**, as the datum
`AlgebraicGeometry.SheafOfModules.TruncationCupProduct` that the statements of
`StacksFrontier.AlgebraicGeometry.DeRham.FirstChernClass.FilteredChernCupProduct` are proved for:
the pairing `canonicalPairing` built from the global cup product `cupProductOnSpace`. -/
def truncationCupProduct : TruncationCupProduct (A := A) where
  pair := canonicalPairing
  pair_naturality f g m m' h hm i j x y := canonicalPairing_naturality f g m m' h hm i j x y


/-! ### Section 50.7: cup products on the Hodge filtration -/

section HodgeFiltration

variable {φ : A ⟶ X.sheaf}
  (B : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology X.carrier) (moduleOfDifferentials.{u, u, u} φ))
  (D : DeRhamDifferential B)

/-- **The cup product of Section 50.7 on the hypercohomology of the brutal truncations**,

`H^n(X, σ^{≥i}Ω^•_{X/S}) × H^m(X, σ^{≥j}Ω^•_{X/S}) ⟶ H^{n + m}(X, σ^{≥(i + j)}Ω^•_{X/S})`:

the cup product of Cohomology, Section 0FKU along the multiplication
`Tot(σ^{≥i}Ω^• ⊗_A σ^{≥j}Ω^•) ⟶ σ^{≥(i + j)}Ω^•` that the wedge product of Tag 0FM2 restricts to,
`AlgebraicGeometry.SheafOfModules.hodgeFiltrationWedge`. -/
@[stacks 0FM7 "Section 50.7, the top row of the displayed diagram: the cup products \
H^n(X, σ^{≥i}Ω^•) × H^m(X, σ^{≥j}Ω^•) ⟶ H^{n+m}(X, σ^{≥(i+j)}Ω^•), the cup product of Cohomology \
Section 0FKU (the global cup product of the ringed space (X, A) built from the canonical \
one-point comparison) along the \
multiplication Tot(σ^{≥i}Ω^• ⊗ σ^{≥j}Ω^•) ⟶ σ^{≥(i+j)}Ω^• that the wedge product of 0FM2 \
restricts to"]
def hodgeFiltrationCup (p q i j : ℤ) :
    truncatedDeRhamCohomologyAbelian B D p i → truncatedDeRhamCohomologyAbelian B D q j →
      truncatedDeRhamCohomologyAbelian B D (p + q) (i + j) :=
  TruncationCupProduct.cup B D truncationCupProduct p q i j

/-- **The cup product on de Rham cohomology**
`H^i_{dR}(X/S) × H^j_{dR}(X/S) ⟶ H^{i + j}_{dR}(X/S)`, the bottom row of the diagram of
Section 50.7: the cup product of Cohomology, Section 0FKU along the wedge product of Tag 0FM2, in
the abelian-sheaf realization of de Rham cohomology. -/
def deRhamCup (i j : ℤ) :
    deRhamCohomologyAbelian B D i → deRhamCohomologyAbelian B D j →
      deRhamCohomologyAbelian B D (i + j) :=
  TruncationCupProduct.cupDeRham B D truncationCupProduct i j

/-- **The commutative diagram of Section 50.7**: the maps
`H^n(X, σ^{≥p}Ω^•_{X/S}) ⟶ H^n_{dR}(X/S)` induced by the inclusions of the brutal truncations
carry the cup product on the brutal truncations to the cup product on de Rham cohomology. -/
@[stacks 0FM7 "Section 50.7, the commutative diagram it displays, with no parameter: the maps \
H^n(X, σ^{≥p}Ω^•) ⟶ H^n_dR(X/S) induced by the inclusions σ^{≥p}Ω^• ⟶ Ω^• carry the cup product \
H^n(X, σ^{≥i}Ω^•) × H^m(X, σ^{≥j}Ω^•) ⟶ H^{n+m}(X, σ^{≥(i+j)}Ω^•) to the cup product on \
H^*_dR(X/S), both cup products being those of Cohomology Section 0FKU"]
theorem truncatedDeRhamCohomologyAbelianMap_hodgeFiltrationCup (p q i j : ℤ)
    (x : truncatedDeRhamCohomologyAbelian B D p i)
    (y : truncatedDeRhamCohomologyAbelian B D q j) :
    (truncatedDeRhamCohomologyAbelianMap B D (p + q) (i + j)).hom
        (hodgeFiltrationCup B D p q i j x y) =
      deRhamCup B D i j ((truncatedDeRhamCohomologyAbelianMap B D p i).hom x)
        ((truncatedDeRhamCohomologyAbelianMap B D q j).hom y) :=
  TruncationCupProduct.truncationMap_cup B D truncationCupProduct p q i j x y

/-- **The Hodge filtration is multiplicative**, the last assertion of Section 50.7:

`F^iH^n_{dR}(X/S) ∪ F^jH^m_{dR}(X/S) ⊂ F^{i + j}H^{n + m}_{dR}(X/S)`

for the cup product of Cohomology, Section 0FKU on de Rham cohomology. Membership in a step of
the filtration `AlgebraicGeometry.SheafOfModules.hodgeFiltrationAbelian` of Tag 0FM8, a subobject
of `H^n_{dR}`, means being the image of an element of that subobject. -/
@[stacks 0FM7 "Section 50.7, its last assertion, with no parameter: the Hodge filtration is \
multiplicative for the cup product of Cohomology Section 0FKU on de Rham cohomology, \
F^i H^n_dR(X/S) ∪ F^j H^m_dR(X/S) ⊂ F^{i+j} H^{n+m}_dR(X/S)"]
theorem deRhamCup_mem_hodgeFiltrationAbelian (p q i j : ℤ)
    (x : deRhamCohomologyAbelian B D i) (y : deRhamCohomologyAbelian B D j)
    (hx : ∃ u : (hodgeFiltrationAbelian B D p i : AddCommGrpCat.{u}),
      ((hodgeFiltrationAbelian B D p i).arrow).hom u = x)
    (hy : ∃ v : (hodgeFiltrationAbelian B D q j : AddCommGrpCat.{u}),
      ((hodgeFiltrationAbelian B D q j).arrow).hom v = y) :
    ∃ w : (hodgeFiltrationAbelian B D (p + q) (i + j) : AddCommGrpCat.{u}),
      ((hodgeFiltrationAbelian B D (p + q) (i + j)).arrow).hom w = deRhamCup B D i j x y :=
  TruncationCupProduct.cupDeRham_mem_hodgeFiltrationAbelian B D truncationCupProduct p q i j x y
    hx hy

/-- **The spectral sequence of the Hodge filtration is the Hodge-to-de Rham spectral sequence of
Section 0FM6.** The spectral sequence of Cohomology, Lemma 0BKK for `Ω^•_{X/S}` filtered by its
brutal truncations is bounded, converges to the hypercohomology of `Ω^•_{X/S}`, and is isomorphic
to the first spectral sequence of every Cartan-Eilenberg resolution of `Ω^•_{X/S}`
(Derived Categories, Lemma 015J), which is how Section 0FM6 constructs the Hodge-to-de Rham
spectral sequence; this is Cohomology, Example 0FLK, clause (3), for the de Rham complex. -/
@[stacks 0FM7 "Section 50.7: the spectral sequence of Cohomology Lemma 0BKK for Ω^•_{X/S} \
viewed as a filtered complex (by its brutal truncations) is the same as the Hodge-to-de Rham \
spectral sequence of Section 0FM6, i.e. the first spectral sequence of Derived Categories Lemma \
015J built from a Cartan-Eilenberg resolution of Ω^•_{X/S}: one package, bounded, converging to \
the hypercohomology of Ω^•_{X/S}, and isomorphic to the first spectral sequence of every \
Cartan-Eilenberg resolution (Cohomology Example 0FLK)", sga "7 XXII 3.3" "more general"]
theorem exists_hodgeFiltrationSpectralSequence_iso_cartanEilenbergFirst :
    ∃ S : Stacks.Cohomology.FilteredComplex.StupidTruncationSpectralSequence
        (baseRingedSpace A) (deRhamComplexInt (X := X) B D),
      IsBounded S.spectralSequence ∧
      SpectralSequence.AbutsTo S.spectralSequence (fun n =>
        Stacks.Cohomology.FilteredComplex.hypercohomology (baseRingedSpace A) S.RΓ
          (deRhamComplexInt (X := X) B D) n) ∧
      ∀ I : (deRhamComplexInt (X := X) B D).CartanEilenbergResolution,
        Nonempty (S.spectralSequence ≅
          Stacks.Cohomology.FilteredComplex.cartanEilenbergFirstSpectralSequence
            (baseRingedSpace A) I) :=
  Stacks.Cohomology.FilteredComplex.exists_stupidTruncationSpectralSequence_iso_cartanEilenbergFirst
    (baseRingedSpace A) (deRhamComplexInt (X := X) B D) 0 (isStrictlyGE_deRhamComplexInt B D)

end HodgeFiltration

end AlgebraicGeometry.SheafOfModules

end
