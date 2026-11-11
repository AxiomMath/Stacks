module

public import StacksFrontier.Cotangent.Complex
public import StacksFrontier.Cotangent.PolynomialAlgebraSiteDifferentials
public import StacksFrontier.Cotangent.ResolutionPointCriterionSmall
public import StacksCore.Tactic.StacksAttribute

/-!
# The cotangent complex as a derived lower shriek, and `Lπ_!π^{-1} = id`

Let `A → B` be a ring map and let `π` be the morphism of ringed topoi of Tag 08PR, from the
chaotic site `C_{B/A}` of polynomial `A`-algebras augmented to `B` to the ringed point `(*, B)`.
Tag 08PT computes `Lπ_!(ℱ)` by evaluating `ℱ` on a resolution `ε : P_• ⟶ B`; this file reads two
consequences of that computation off the version of Tag 08PT available here,
`CommAlgCat.standardResolutionLeftDerivedLowerShriekNatIso`:

* **Tag 08QE**: `Lπ_!(π^{-1}M) = M`, because `(π^{-1}M)(P_•, ε)` is the constant simplicial
  object on `M`, whose Moore complex is the alternating constant complex;
* **Tag 08PU**: `L_{B/A} = Lπ_!(Ω_{𝒪/A} ⊗_𝒪 B̲)`, because `(Ω_{𝒪/A} ⊗_𝒪 B̲)(P_•, ε)` is the
  simplicial module `B ⊗_{P_•} Ω[P_•⁄A]` whose associated complex is the cotangent complex of
  Tag 08PN.

**Which site.** Every statement below about `π_!` is about the point morphism of the *small
model of the footnote-restricted site*, `CommAlgCat.smallBoundedPolynomialSite A B κ`, with
coefficients in `AddCommGrpCat.{u}` — the site and coefficients of
`StacksFrontier/Cotangent/ResolutionPointCriterionSmall.lean`. The source's `C_{B/A}` *is* the
restricted site: the restriction of the sets of variables is the footnote to the source's
section, and it is what makes the site small enough for the criterion of Tag 08Q9. So the
restricted site is the faithful reading. Nothing here is a statement about
`CommAlgCat.polynomialAbelianLowerShriek`, the `π_!` formed for the unrestricted
`CommAlgCat.polynomialSite` at coefficients `AddCommGrpCat.{max (u + 1) m}`: bridging the two
would need a comparison of the restricted and unrestricted sites — only full faithfulness of
`CommAlgCat.smallBoundedPolynomialSiteToPolynomialSite` is available — together with a shift of
the coefficient universe. See the implementation notes for what else is and is not closed.

## Main definitions

* `Stacks.ChaoticSite.abelianPointInverseImage`: `π^{-1}` on abelian sheaves for the chaotic
  topology on a small category, with coefficients in the universe of the site.
* `CommAlgCat.overDifferentials`, `CommAlgCat.overDifferentialsPush` and
  `CommAlgCat.overDifferentialsFunctor`: the `B`-module `B ⊗_P Ω[P⁄A]` attached to an
  `A`-algebra `P` augmented to `B`, the map it attaches to a morphism over `B`, and the
  resulting functor on `Over B`.
* `CommAlgCat.polynomialCotangentModulePresheaf`,
  `CommAlgCat.smallPolynomialCotangentModulePresheaf` and
  `CommAlgCat.smallPolynomialCotangentSheaf`: the sheaf `i^*Ω_{𝒪/A} = Ω_{𝒪/A} ⊗_𝒪 B̲` of the
  source, on the unrestricted site and on the small model of the restricted site, and the
  latter read as an abelian sheaf.
* `CommAlgCat.smallPolynomialModuleSheaf`: an arbitrary presheaf of `B`-modules on the small
  model of the restricted site, read as an abelian sheaf; the chaotic topology makes every such
  presheaf a sheaf, and `CommAlgCat.smallPolynomialCotangentSheaf` is one instance of it.
* `CommAlgCat.standardResolutionSmallCosimplicialObject`: the standard resolution of `B` over
  `A`, read as a cosimplicial object of the small model of the restricted site.
* `Stacks.mapHomologicalComplexHomologyIso`: for an additive functor preserving homology, the
  homology of the image of a complex is the image of its homology.

## Main results

* `Stacks.ChaoticSite.leftDerivedZeroLowerShriekInverseImageIso` and
  `Stacks.ChaoticSite.isZero_leftDerivedSucc_lowerShriek_inverseImage`: **`Lπ_!(π^{-1}M) = M`**
  on a small chaotic site admitting a point resolution — the sections at the point of
  `L_0π_!(π^{-1}M)` are `M`, and those of `L_nπ_!(π^{-1}M)` vanish for `n > 0`.
* `CommAlgCat.polynomialLeftDerivedZeroLowerShriekInverseImageIso` and
  `CommAlgCat.isZero_polynomialLeftDerivedSuccLowerShriekInverseImage`: **Tag 08QE** for the
  small model of the restricted site `C_{B/A}`, through the standard resolution.
* `CommAlgCat.smallResolutionCotangentModuleIso`: the evaluation of `i^*Ω_{𝒪/A}` on the
  cosimplicial object of a bounded resolution `ε : P_• ⟶ B` is the simplicial `B`-module
  `B ⊗_{P_•} Ω[P_•⁄A]`.
* `CommAlgCat.standardResolutionOverDifferentialsIso`: for the standard resolution that
  simplicial module is `CommAlgCat.cotangentSimplicialModule`, the simplicial module of
  Tag 08PN.
* `CommAlgCat.standardResolutionCotangentMooreComplexIso`: consequently the Moore complex of
  `(i^*Ω_{𝒪/A})(P_•, ε)` is the complex underlying the cotangent complex of Tag 08PN.
* `CommAlgCat.standardResolutionLeftDerivedCotangentComplexIso`: **Tag 08PU** for the small
  model of the restricted site `C_{B/A}`, with `Lπ_!` read degreewise and coefficients forgotten
  to abelian groups: the sections at the point of `L_nπ_!(Ω_{𝒪/A} ⊗_𝒪 B̲)` are the degree `-n`
  cohomology of `L_{B/A}`.
* `CommAlgCat.free_kaehlerDifferential_polynomialSite`: the differentials of each object of
  `C_{B/A}` are a free module over it. This is the input that lets the argument of Tag 08PU
  replace `Li^*` by `i^*`.

## Implementation notes

**What `Lπ_!` means here, and where the rest of Tag 08PU is.** The source states Tag 08PU as
an isomorphism in `D(B)` between `L_{B/A}` and `Lπ_!` of a sheaf of *modules*. The results of
this file use `Lπ_!` on abelian sheaves, read degreewise as the left derived functors of the
`π_!` of Tag 08PF (`Stacks.ChaoticSite.abelianPointLowerShriek`), so the conclusions here are
degreewise and at abelian coefficients. The identification of `i^*Ω_{𝒪/A}` evaluated on the
standard resolution with the simplicial module defining `L_{B/A}` is
`CommAlgCat.standardResolutionCotangentMooreComplexIso`, an isomorphism of *complexes*, not
merely of their homology. The isomorphism in `D(B)` is
`CommAlgCat.standardResolutionCotangentDerivedLowerShriekIso` of
`StacksFrontier/Cotangent/PolynomialAlgebraSiteModuleShriekDerived.lean`. The step
`Li^*Ω_{𝒪/A} = i^*Ω_{𝒪/A}`, whose input is the freeness
`CommAlgCat.free_kaehlerDifferential_polynomialSite` (sheaf-level flatness:
`CommAlgCat.polynomialRelativeDifferentials_isFlat`), is
`CommAlgCat.smallPolynomialDerivedPullbackDifferentialsIso`, an isomorphism in `D(B̲)` on the
small model, and the full chain of the tag in `D(Ab)` is
`CommAlgCat.cotangentComplexIsoDerivedLowerShriekDerivedPullback`, both in
`StacksFrontier/Cotangent/PolynomialAlgebraSiteDerivedPullbackDifferentials.lean`.

**The `Type u` model of `i^*Ω_{𝒪/A}`.** The criterion of Tag 08Q9, hence the computation of
`Lπ_!` on the small model, is stated for coefficients in `AddCommGrpCat.{u}`, the universe of
the site. The sheaf `CommAlgCat.polynomialRelativeDifferentialsBaseChange` of
`StacksFrontier/Cotangent/PolynomialAlgebraSiteDifferentials.lean` cannot be used: it is formed on
the unrestricted site with sections `ULift B ⊗_{ULift P} Ω[ULift P⁄ULift A]` in `Type (u + 1)`,
because the morphism of topoi of Tag 08PR is formed at a coefficient universe at least `u + 1`.
The sheaf used here is therefore the same mathematical object written at `Type u`: by the
source's own description of `i^*Ω_{𝒪/A}` in the proof of Tag 08PU, it "assigns to `α` the
`B`-module `Ω_{P/A} ⊗_{P,α} B`", and `CommAlgCat.overDifferentials` is that module. Identifying
it with the `u + 1`-universe sheaf is a universe-lift comparison of tensor products, not carried
out here.

**Functoriality through the generators.** `CommAlgCat.overDifferentialsPush` is built exactly as
`CommAlgCat.cotangentPush` of `StacksFrontier/Cotangent/Complex.lean` is, but for an arbitrary
morphism of `Over B` rather than for one of the standard resolution; the value on a pure
differential pins it down, and the extensionality principle
`ModuleCat.extendScalars_kaehlerDifferential_hom_ext` then gives the functor laws. Because the
two constructions are the same formula, `CommAlgCat.standardResolutionOverDifferentialsIso`
needs no comparison map: the restriction of `CommAlgCat.overDifferentialsFunctor` along the
standard resolution is `CommAlgCat.cotangentSimplicialModule` on the nose.

## References

* [Stacks Project, Tag 08PN](https://stacks.math.columbia.edu/tag/08PN)
* [Stacks Project, Tag 08PR](https://stacks.math.columbia.edu/tag/08PR)
* [Stacks Project, Tag 08PT](https://stacks.math.columbia.edu/tag/08PT)
* [Stacks Project, Tag 08PU](https://stacks.math.columbia.edu/tag/08PU)
* [Stacks Project, Tag 08QE](https://stacks.math.columbia.edu/tag/08QE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology Simplicial

universe u

/-! ### Homology and an exact functor -/

namespace Stacks

universe v₁ u₁ v₂ u₂

/-- For an additive functor preserving homology, the homology of the image of a complex is the
image of its homology: in each degree the short complex computing the homology of the image is
the image of the short complex computing the homology. -/
def mapHomologicalComplexHomologyIso {C₁ : Type u₁} [Category.{v₁} C₁] [Preadditive C₁]
    {C₂ : Type u₂} [Category.{v₂} C₂] [Preadditive C₂] {ι : Type*} {c : ComplexShape ι}
    (F : C₁ ⥤ C₂) [F.Additive] [F.PreservesHomology]
    (K : HomologicalComplex C₁ c) (i : ι) [K.HasHomology i]
    [((F.mapHomologicalComplex c).obj K).HasHomology i] :
    ((F.mapHomologicalComplex c).obj K).homology i ≅ F.obj (K.homology i) :=
  ShortComplex.mapHomologyIso (K.sc i) F

end Stacks

/-! ### `Lπ_!(π^{-1}M) = M` on a chaotic site with a point resolution -/

namespace Stacks.ChaoticSite

variable (C : Type u) [SmallCategory C]

/-- `π^{-1}` on abelian sheaves for the chaotic topology on a small category, with coefficients
in the universe of the site: restriction along the point functor, the right adjoint of
`Stacks.ChaoticSite.abelianPointLowerShriek`. -/
abbrev abelianPointInverseImage :
    Sheaf (GrothendieckTopology.trivial (Discrete PUnit.{u + 1})) AddCommGrpCat.{u} ⥤
      Sheaf (GrothendieckTopology.trivial C) AddCommGrpCat.{u} :=
  (Functor.star C).sheafPushforwardContinuous AddCommGrpCat.{u}
    (GrothendieckTopology.trivial C) (GrothendieckTopology.trivial (Discrete PUnit.{u + 1}))

/-- The presheaf underlying `π^{-1}M` is the constant presheaf with value the sections of `M` at
the point: restriction along the point functor is the constant diagram. -/
def inverseImageObjIso
    (M : Sheaf (GrothendieckTopology.trivial (Discrete PUnit.{u + 1})) AddCommGrpCat.{u}) :
    (Functor.const Cᵒᵖ).obj ((pointSections.{u, u + 1, u} AddCommGrpCat.{u}).obj M) ≅
      ((abelianPointInverseImage C).obj M).obj :=
  (starWhiskerIso AddCommGrpCat.{u} C).app M.obj

variable {C}

/-- **`(π^{-1}M)(U_•)` is the constant simplicial abelian group on `M`.** Its Moore complex is
therefore the alternating constant complex `M ←0- M ←𝟙- M ←0- ⋯`, which has homology `M` in
degree zero and nothing above. -/
def mooreComplexInverseImageIso (U : CosimplicialObject C)
    (M : Sheaf (GrothendieckTopology.trivial (Discrete PUnit.{u + 1})) AddCommGrpCat.{u}) :
    (cosimplicialMooreComplex U).obj ((abelianPointInverseImage C).obj M).obj ≅
      ChainComplex.alternatingConst.obj
        ((pointSections.{u, u + 1, u} AddCommGrpCat.{u}).obj M) :=
  (alternatingFaceMapComplex AddCommGrpCat.{u}).mapIso
      (Functor.isoWhiskerLeft U.op (inverseImageObjIso C M)).symm ≪≫
    AlgebraicTopology.alternatingFaceMapComplexConst.app _

/-- **`Lπ_!(π^{-1}M) = M` in degree zero.** Let `U_•` be a point resolution of a small chaotic
site `C`. For every abelian sheaf `M` on the point, the sections at the point of
`L_0π_!(π^{-1}M)` are the sections of `M`.

This is the computation of `Lπ_!` on a resolution — `L_nπ_!(ℱ)` is the degree `n` homology of
the Moore complex of `ℱ(U_•)` — applied to `ℱ = π^{-1}M`, whose evaluation on `U_•` is the
constant simplicial object on `M`. -/
def leftDerivedZeroLowerShriekInverseImageIso (U : CosimplicialObject C)
    (hU : IsPointResolution U)
    (M : Sheaf (GrothendieckTopology.trivial (Discrete PUnit.{u + 1})) AddCommGrpCat.{u}) :
    (pointSections.{u, u + 1, u} AddCommGrpCat.{u}).obj
        (((abelianPointLowerShriek C).leftDerived 0).obj
          ((abelianPointInverseImage C).obj M)) ≅
      (pointSections.{u, u + 1, u} AddCommGrpCat.{u}).obj M :=
  (leftDerivedPointLowerShriekNatIso C U hU 0).app ((abelianPointInverseImage C).obj M) ≪≫
    (HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.down ℕ) 0).mapIso
      (mooreComplexInverseImageIso U M) ≪≫
    ChainComplex.alternatingConstHomologyZero _

/-- **`Lπ_!(π^{-1}M) = M` in positive degrees.** Let `U_•` be a point resolution of a small
chaotic site `C`. For every abelian sheaf `M` on the point and every `n > 0`, the sections at the
point of `L_nπ_!(π^{-1}M)` vanish: the Moore complex of the constant simplicial object on `M` is
exact away from degree zero. -/
theorem isZero_leftDerivedSucc_lowerShriek_inverseImage (U : CosimplicialObject C)
    (hU : IsPointResolution U)
    (M : Sheaf (GrothendieckTopology.trivial (Discrete PUnit.{u + 1})) AddCommGrpCat.{u})
    (n : ℕ) :
    IsZero ((pointSections.{u, u + 1, u} AddCommGrpCat.{u}).obj
      (((abelianPointLowerShriek C).leftDerived (n + 1)).obj
        ((abelianPointInverseImage C).obj M))) := by
  refine IsZero.of_iso ?_
    ((leftDerivedPointLowerShriekNatIso C U hU (n + 1)).app
        ((abelianPointInverseImage C).obj M) ≪≫
      (HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.down ℕ)
        (n + 1)).mapIso (mooreComplexInverseImageIso U M))
  exact (ChainComplex.alternatingConst_exactAt
    ((pointSections.{u, u + 1, u} AddCommGrpCat.{u}).obj M) (n + 1)
    (Nat.succ_ne_zero n)).isZero_homology

end Stacks.ChaoticSite

namespace CommAlgCat

open scoped TensorProduct

/-! ### `B ⊗_P Ω[P⁄A]` as a functor of the augmented algebra -/

section Differentials

variable {A : Type u} [CommRing A] {B : CommAlgCat.{u} A}

/-- The augmentation of an `A`-algebra over `B`, read as a ring homomorphism. -/
abbrev augmentationRingHom (X : Over B) : (X.left : Type u) →+* (B : Type u) :=
  X.hom.hom.toRingHom

/-- **The sections of `i^*Ω_{𝒪/A}` over an object of `C_{B/A}`.** For an `A`-algebra `P`
augmented to `B` by `α`, this is the `B`-module `B ⊗_{P,α} Ω[P⁄A]`, the scalar extension of the
differentials of `P` over `A` along the augmentation. -/
def overDifferentials (X : Over B) : ModuleCat.{u} B :=
  (ModuleCat.extendScalars (augmentationRingHom X)).obj
    (ModuleCat.of (X.left : Type u) (KaehlerDifferential A (X.left : Type u)))

/-- The pure differential `1 ⊗ d p` of `CommAlgCat.overDifferentials`. These elements generate,
which is what pins down every map out of it. -/
def overDifferentialsMk (X : Over B) (p : (X.left : Type u)) : overDifferentials X :=
  (1 : B) ⊗ₜ KaehlerDifferential.D A (X.left : Type u) p

/-- Two `B`-linear maps out of `B ⊗_P Ω[P⁄A]` agreeing on every pure differential `1 ⊗ d p` are
equal: the differentials `d p` span `Ω[P⁄A]`. -/
theorem overDifferentials_hom_ext {X : Over B} {N : ModuleCat.{u} B}
    (α β : overDifferentials X ⟶ N)
    (h : ∀ p, α (overDifferentialsMk X p) = β (overDifferentialsMk X p)) : α = β :=
  ModuleCat.extendScalars_kaehlerDifferential_hom_ext (augmentationRingHom X) α β h

/-- A morphism of `A`-algebras over `B` is compatible with the augmentations, read as an identity
of ring homomorphisms. -/
theorem augmentationRingHom_comp {X Y : Over B} (f : X ⟶ Y) :
    (augmentationRingHom Y).comp f.left.hom.toRingHom = augmentationRingHom X :=
  RingHom.ext fun p => ConcreteCategory.congr_hom (Over.w f) p

/-- The `P`-linear map `Ω[P⁄A] → B ⊗_Q Ω[Q⁄A]`, `ω ↦ 1 ⊗ ω`, attached to a map `P ⟶ Q` of
`A`-algebras lying over `B`; it is adjoint to `CommAlgCat.overDifferentialsPush`. -/
def overDifferentialsPushAdjoint {X Y : Over B} (g : X.left ⟶ Y.left)
    (hg : (augmentationRingHom Y).comp g.hom.toRingHom = augmentationRingHom X) :
    ModuleCat.of (X.left : Type u) (KaehlerDifferential A (X.left : Type u)) ⟶
      (ModuleCat.restrictScalars (augmentationRingHom X)).obj (overDifferentials Y) := by
  let P := (X.left : Type u)
  let Q := (Y.left : Type u)
  let : Algebra P Q := g.hom.toRingHom.toAlgebra
  let : Algebra P (B : Type u) := (augmentationRingHom X).toAlgebra
  let : Algebra Q (B : Type u) := (augmentationRingHom Y).toAlgebra
  have : IsScalarTower A P Q :=
    IsScalarTower.of_algebraMap_eq (fun a => (g.hom.commutes a).symm)
  have : IsScalarTower P Q (B : Type u) := IsScalarTower.of_algebraMap_eq' hg.symm
  exact ModuleCat.ofHom
    (X := ModuleCat.of P (KaehlerDifferential A P))
    (Y := (ModuleCat.restrictScalars (augmentationRingHom X)).obj (overDifferentials Y))
    { toFun := fun x => (1 : (B : Type u)) ⊗ₜ[Q] (KaehlerDifferential.map A A P Q x)
      map_add' := by
        intro x y
        change (TensorProduct.mk Q (B : Type u) (KaehlerDifferential A Q) 1)
            (KaehlerDifferential.map A A P Q (x + y)) = _
        rw [map_add]
        exact (TensorProduct.mk Q (B : Type u) (KaehlerDifferential A Q) 1).map_add _ _
      map_smul' := by
        intro p x
        change (1 : (B : Type u)) ⊗ₜ[Q] (KaehlerDifferential.map A A P Q (p • x)) =
          augmentationRingHom X p • ((1 : (B : Type u)) ⊗ₜ[Q]
            (KaehlerDifferential.map A A P Q x))
        rw [map_smul, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
        congr 1 }

/-- The `B`-linear map `B ⊗_P Ω[P⁄A] → B ⊗_Q Ω[Q⁄A]` induced by a map `P ⟶ Q` of `A`-algebras
lying over `B`: the `B`-linear extension of `CommAlgCat.overDifferentialsPushAdjoint`. -/
def overDifferentialsPush {X Y : Over B} (g : X.left ⟶ Y.left)
    (hg : (augmentationRingHom Y).comp g.hom.toRingHom = augmentationRingHom X) :
    overDifferentials X ⟶ overDifferentials Y :=
  ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars (augmentationRingHom X)
    (overDifferentialsPushAdjoint g hg)

/-- `CommAlgCat.overDifferentialsPush` sends the pure differential `1 ⊗ d p` to `1 ⊗ d (g p)`. -/
@[simp]
theorem overDifferentialsPush_mk {X Y : Over B} (g : X.left ⟶ Y.left)
    (hg : (augmentationRingHom Y).comp g.hom.toRingHom = augmentationRingHom X)
    (p : (X.left : Type u)) :
    overDifferentialsPush g hg (overDifferentialsMk X p) = overDifferentialsMk Y (g p) := by
  have key : overDifferentialsPush g hg (overDifferentialsMk X p) =
      (1 : (B : Type u)) • (overDifferentialsPushAdjoint g hg)
        (KaehlerDifferential.D A (X.left : Type u) p) :=
    ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars_tmul
      (augmentationRingHom X) (overDifferentialsPushAdjoint g hg) (1 : (B : Type u))
      (KaehlerDifferential.D A (X.left : Type u) p)
  rw [key, one_smul]
  let P := (X.left : Type u)
  let Q := (Y.left : Type u)
  let _ : Algebra P Q := g.hom.toRingHom.toAlgebra
  let _ : Algebra P (B : Type u) := (augmentationRingHom X).toAlgebra
  let _ : Algebra Q (B : Type u) := (augmentationRingHom Y).toAlgebra
  have : IsScalarTower A P Q :=
    IsScalarTower.of_algebraMap_eq (fun a => (g.hom.commutes a).symm)
  have : IsScalarTower P Q (B : Type u) := IsScalarTower.of_algebraMap_eq' hg.symm
  change (1 : (B : Type u)) ⊗ₜ[Q]
    (KaehlerDifferential.map A A P Q (KaehlerDifferential.D A P p)) = _
  rw [KaehlerDifferential.map_D]
  rfl

/-- **`i^*Ω_{𝒪/A} = Ω_{𝒪/A} ⊗_𝒪 B̲` as a functor of the augmented algebra.** It sends an
`A`-algebra `P` augmented to `B` by `α` to the `B`-module `B ⊗_{P,α} Ω[P⁄A]` and a morphism over
`B` to the `B`-linear map `1 ⊗ d p ↦ 1 ⊗ d (g p)`. The functor laws hold because a map out of
`B ⊗_P Ω[P⁄A]` is determined by its values on the pure differentials. -/
def overDifferentialsFunctor : Over B ⥤ ModuleCat.{u} B where
  obj X := overDifferentials X
  map f := overDifferentialsPush f.left (augmentationRingHom_comp f)
  map_id X := by
    refine overDifferentials_hom_ext _ _ fun p => ?_
    rw [overDifferentialsPush_mk]
    rfl
  map_comp {X Y Z} f g := by
    refine overDifferentials_hom_ext _ _ fun p => ?_
    rw [overDifferentialsPush_mk]
    rw [ConcreteCategory.comp_apply, overDifferentialsPush_mk, overDifferentialsPush_mk]
    rfl

end Differentials

/-! ### The sheaf `i^*Ω_{𝒪/A}` on the site -/

section Site

variable (A : Type u) [CommRing A] (B : CommAlgCat.{u} A) (κ : Cardinal.{u})

/-- **The sheaf `i^*Ω_{𝒪/A} = Ω_{𝒪/A} ⊗_𝒪 B̲` on the unrestricted site
`CommAlgCat.polynomialSite`, with sections in `Type u`**: it sends `(P, α)` to the `B`-module
`B ⊗_{P,α} Ω[P⁄A]`, which is how the source describes `i^*Ω_{𝒪/A}` in the proof of Tag 08PU. The
topology of `C_{B/A}` being chaotic, no sheafification intervenes.

This is not `CommAlgCat.polynomialRelativeDifferentialsBaseChange`: that sheaf is formed at the
coefficient universe of the morphism of topoi of Tag 08PR, so its sections are
`ULift B ⊗_{ULift P} Ω[ULift P⁄ULift A]` in `Type (u + 1)`, whereas the computation of `Lπ_!` on
the small model needs coefficients in `Type u`. -/
def polynomialCotangentModulePresheaf : (polynomialSite A B)ᵒᵖ ⥤ ModuleCat.{u} B :=
  unopUnop (PolynomialAugmentation A B) ⋙ (IsPolynomialAlgebraOver A B).ι ⋙
    overDifferentialsFunctor

/-- **The differentials of each object of `C_{B/A}` are free over it.** Every object `(P, α)` of
the site has `P` a polynomial algebra over `A`, so `Ω[P⁄A]` is free on the variables. This is the
first sentence of the proof of Tag 08PU, the objectwise input to its step `Li^* = i^*`; the
sheaf-level flatness is `CommAlgCat.polynomialRelativeDifferentials_isFlat`, and the step itself,
`Li^*Ω_{𝒪/A} ≅ i^*Ω_{𝒪/A}` in `D(B̲)`, is `CommAlgCat.smallPolynomialDerivedPullbackDifferentialsIso`
of `StacksFrontier/Cotangent/PolynomialAlgebraSiteDerivedPullbackDifferentials.lean`. -/
@[stacks 08PU "the first sentence of the proof: for each object P → B of C_{B/A} the module \
  Ω_{P/A} is a free P-module; this is the input to the step Li^*Ω_{𝒪/A} = i^*Ω_{𝒪/A}, which is \
  CommAlgCat.smallPolynomialDerivedPullbackDifferentialsIso"]
theorem free_kaehlerDifferential_polynomialSite (X : polynomialSite A B) :
    Module.Free (X.unop.obj.left : Type u) Ω[(X.unop.obj.left : Type u)⁄A] :=
  free_kaehlerDifferential_of_isPolynomialAlgebra A X.unop.property

/-- `i^*Ω_{𝒪/A}` on the small model of the footnote-restricted site, as a presheaf of
`B`-modules: the restriction of `CommAlgCat.polynomialCotangentModulePresheaf` along the fully
faithful inclusion of the model into `CommAlgCat.polynomialSite`. -/
def smallPolynomialCotangentModulePresheaf :
    (smallBoundedPolynomialSite A B κ)ᵒᵖ ⥤ ModuleCat.{u} B :=
  (smallBoundedPolynomialSiteToPolynomialSite A B κ).op ⋙
    polynomialCotangentModulePresheaf A B

/-- A presheaf of `B`-modules on the small model of the restricted site `C_{B/A}`, read as an
abelian sheaf. It is a sheaf because the topology of `C_{B/A}` is chaotic. -/
def smallPolynomialModuleSheaf (ℱ : (smallBoundedPolynomialSite A B κ)ᵒᵖ ⥤ ModuleCat.{u} B) :
    Sheaf (GrothendieckTopology.trivial (smallBoundedPolynomialSite A B κ))
      AddCommGrpCat.{u} where
  obj := ℱ ⋙ forget₂ (ModuleCat.{u} B) AddCommGrpCat.{u}
  property := by
    rw [GrothendieckTopology.trivial_eq_bot]
    exact Presheaf.isSheaf_bot _

/-- **`i^*Ω_{𝒪/A}` as an abelian sheaf on the small model of the footnote-restricted site**, the
underlying abelian groups of `CommAlgCat.smallPolynomialCotangentModulePresheaf`. It is a sheaf
because the topology of `C_{B/A}` is chaotic, and it is the sheaf whose derived lower shriek
Tag 08PU computes. -/
def smallPolynomialCotangentSheaf :
    Sheaf (GrothendieckTopology.trivial (smallBoundedPolynomialSite A B κ))
      AddCommGrpCat.{u} :=
  smallPolynomialModuleSheaf A B κ (smallPolynomialCotangentModulePresheaf A B κ)

end Site

/-! ### The evaluation of `i^*Ω_{𝒪/A}` on a resolution -/

section Resolution

variable {A : Type u} [CommRing A] {B : CommAlgCat.{u} A}
  {P : SimplicialObject (CommAlgCat.{u} A)}
  (ε : P ⟶ (SimplicialObject.const (CommAlgCat.{u} A)).obj B) (κ : Cardinal.{u})
  (hPκ : ∀ n, IsPolynomialAlgebraBelow A κ (P.obj n))

/-- **`(i^*Ω_{𝒪/A})(P_•, ε) = B ⊗_{P_•} Ω[P_•⁄A]`.** The evaluation of `i^*Ω_{𝒪/A}` on the
cosimplicial object of a bounded resolution, read in the small model of the restricted site, is
the simplicial `B`-module of base-changed differentials of `P_•`. The small model's objects are
only isomorphic to the terms of the resolution, which is what the comparison here transports
along: it is the restriction of
`CommAlgCat.smallResolutionCosimplicialObjectι` to `i^*Ω_{𝒪/A}`. -/
def smallResolutionCotangentModuleIso :
    (smallResolutionCosimplicialObject ε κ hPκ).op ⋙
        smallPolynomialCotangentModulePresheaf A B κ ≅
      resolutionOver ε ⋙ overDifferentialsFunctor :=
  Functor.isoWhiskerRight (NatIso.op (smallResolutionCosimplicialObjectι ε κ hPκ)).symm
    (polynomialCotangentModulePresheaf A B)

end Resolution

/-! ### Tag 08PU and Tag 08QE at the small model of the restricted site -/

section Standard

variable (A : Type u) [CommRing A] (B : CommAlgCat.{u} A)

/-- **`B ⊗_{P_•} Ω[P_•⁄A]` for the standard resolution is the simplicial module of Tag 08PN.**
No comparison map is involved: `CommAlgCat.overDifferentialsFunctor` and
`CommAlgCat.cotangentSimplicialModule` are built from the same formula, the first for an
arbitrary augmented algebra and the second for the terms of the standard resolution. -/
def standardResolutionOverDifferentialsIso :
    resolutionOver (standardResolution.{u, u} A B).hom ⋙ overDifferentialsFunctor ≅
      (cotangentSimplicialModule.{u, u} A B).object :=
  NatIso.ofComponents fun _ => Iso.refl _

/-- The standard resolution of `B` over `A`, read as a cosimplicial object of the small model of
the site restricted to polynomial algebras on at most
`CommAlgCat.standardResolutionVarCardinal A B` variables. -/
abbrev standardResolutionSmallCosimplicialObject :
    CosimplicialObject (smallBoundedPolynomialSite A B (standardResolutionVarCardinal A B)) :=
  smallResolutionCosimplicialObject (standardResolution.{u, u} A B).hom
    (standardResolutionVarCardinal A B) (standardResolution_isPolynomialAlgebraBelow A B)

/-- **The standard resolution is a point resolution of the small model of the restricted site**:
Tag 08PS transported to the model, which is the hypothesis under which `Lπ_!` is computed by
evaluation on the resolution. -/
theorem isPointResolution_standardResolutionSmallCosimplicialObject :
    Stacks.ChaoticSite.IsPointResolution (standardResolutionSmallCosimplicialObject A B) :=
  isPointResolution_smallResolutionCosimplicialObject (standardResolution.{u, u} A B).hom
    (standardResolutionVarCardinal A B) (standardResolution_isPolynomialAlgebraBelow A B)
    (standardResolution_isResolution.{u, u} A B).trivialKanFibration

/-- **The Moore complex of `(i^*Ω_{𝒪/A})(P_•, ε)` is the complex of `L_{B/A}`.** For the
standard resolution of `B` over `A`, the Moore complex of the simplicial abelian group obtained
by evaluating `i^*Ω_{𝒪/A}` on the cosimplicial object of the small model is the complex
underlying the cotangent complex of Tag 08PN, namely the alternating face map complex of
`CommAlgCat.cotangentSimplicialModule` with its `B`-module structures forgotten.

This is the heart of Tag 08PU: an isomorphism of complexes, not merely of their homology. -/
@[stacks 08PU "the step Lπ_!(Ω_{𝒪/A} ⊗_𝒪 B̲) = (Ω_{𝒪/A} ⊗_𝒪 B̲)(P_•, ε): the evaluation of \
  i^*Ω_{𝒪/A} on the standard resolution is the simplicial module whose complex is L_{B/A}, as an \
  isomorphism of complexes"]
def standardResolutionCotangentMooreComplexIso :
    (Stacks.ChaoticSite.cosimplicialMooreComplex
          (standardResolutionSmallCosimplicialObject A B)).obj
        (smallPolynomialCotangentSheaf A B (standardResolutionVarCardinal A B)).obj ≅
      ((forget₂ (ModuleCat.{u} B) AddCommGrpCat.{u}).mapHomologicalComplex
          (ComplexShape.down ℕ)).obj
        ((alternatingFaceMapComplex (ModuleCat.{u} B)).obj
          (cotangentSimplicialModule.{u, u} A B).object) :=
  (alternatingFaceMapComplex AddCommGrpCat.{u}).mapIso
      (Functor.isoWhiskerRight
        (smallResolutionCotangentModuleIso (standardResolution.{u, u} A B).hom
            (standardResolutionVarCardinal A B)
            (standardResolution_isPolynomialAlgebraBelow A B) ≪≫
          standardResolutionOverDifferentialsIso A B)
        (forget₂ (ModuleCat.{u} B) AddCommGrpCat.{u})) ≪≫
    ((alternatingFaceMapComplexCompMapHomologicalComplexIso
      (forget₂ (ModuleCat.{u} B) AddCommGrpCat.{u})).app
        (cotangentSimplicialModule.{u, u} A B).object).symm

/-- **Tag 08PU at the small model of the restricted site `C_{B/A}`.** The sections at the point
of `L_nπ_!(Ω_{𝒪/A} ⊗_𝒪 B̲)` are the degree `-n` cohomology of the cotangent complex `L_{B/A}` of
Tag 08PN, with its `B`-module structure forgotten; here `π` is the point morphism of the small
model of the footnote-restricted site and `Lπ_!` is read degreewise, as the left derived functors
of the `π_!` of Tag 08PF.

The proof is the source's: Tag 08PT computes `L_nπ_!` on the standard resolution
(`CommAlgCat.standardResolutionLeftDerivedLowerShriekNatIso`), the evaluation of
`Ω_{𝒪/A} ⊗_𝒪 B̲` there is the simplicial module defining `L_{B/A}`
(`CommAlgCat.standardResolutionCotangentMooreComplexIso`), and the cotangent complex is the
reindexing of that simplicial module's alternating face map complex. The step
`Li^*Ω_{𝒪/A} = i^*Ω_{𝒪/A}` of the source is the flatness of `Ω_{𝒪/A}` over `𝒪`,
`CommAlgCat.polynomialRelativeDifferentials_isFlat`; see the implementation notes for what
separates this statement from the source's isomorphism in `D(B)`. -/
@[stacks 08PU "the identification L_{B/A} = Lπ_!(Ω_{𝒪/A} ⊗_𝒪 B̲), for the point morphism of \
  the small model of the footnote-restricted site C_{B/A} and with Lπ_! read degreewise, as the \
  left derived functors of the π_! of Tag 08PF at abelian coefficients: the sections at the point \
  of L_nπ_! are the degree -n cohomology of the cotangent complex of Tag 08PN. The source's \
  isomorphism in D(B) needs the module-level Lπ_!, which is absent from this library"]
def standardResolutionLeftDerivedCotangentComplexIso (n : ℕ) :
    (Stacks.ChaoticSite.pointSections.{u, u + 1, u} AddCommGrpCat.{u}).obj
        (((Stacks.ChaoticSite.abelianPointLowerShriek
              (smallBoundedPolynomialSite A B
                (standardResolutionVarCardinal A B))).leftDerived n).obj
          (smallPolynomialCotangentSheaf A B (standardResolutionVarCardinal A B))) ≅
      (forget₂ (ModuleCat.{u} B) AddCommGrpCat.{u}).obj
        ((cotangentComplex.{u, u} A B).homology (-(n : ℤ))) :=
  (standardResolutionLeftDerivedLowerShriekNatIso A B n).app
      (smallPolynomialCotangentSheaf A B (standardResolutionVarCardinal A B)) ≪≫
    (HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.down ℕ) n).mapIso
      (standardResolutionCotangentMooreComplexIso A B) ≪≫
    Stacks.mapHomologicalComplexHomologyIso (forget₂ (ModuleCat.{u} B) AddCommGrpCat.{u})
      ((alternatingFaceMapComplex (ModuleCat.{u} B)).obj
        (cotangentSimplicialModule.{u, u} A B).object) n ≪≫
    (forget₂ (ModuleCat.{u} B) AddCommGrpCat.{u}).mapIso
      (((alternatingFaceMapComplex (ModuleCat.{u} B)).obj
            (cotangentSimplicialModule.{u, u} A B).object).extendHomologyIso
          (ComplexShape.embeddingUpIntLE 0) (j := n) (j' := -(n : ℤ)) (by simp)).symm

/-- **Tag 08QE at the small model of the restricted site `C_{B/A}`, in degree zero.** The
sections at the point of `L_0π_!(π^{-1}M)` are the sections of `M`, for every abelian sheaf `M`
on the point; here `π` is the point morphism of the small model of the footnote-restricted site.

This is the source's proof: Tag 08PT computes `Lπ_!(π^{-1}M)` by `(π^{-1}M)(P_•, ε)` for the
standard resolution, and that is the constant simplicial object on `M`. -/
@[stacks 08QE "Lπ_!(π^{-1}M) = M in degree zero, for the point morphism of the small model of \
  the footnote-restricted site C_{B/A} at abelian coefficients"]
def polynomialLeftDerivedZeroLowerShriekInverseImageIso
    (M : Sheaf (GrothendieckTopology.trivial (Discrete PUnit.{u + 1})) AddCommGrpCat.{u}) :
    (Stacks.ChaoticSite.pointSections.{u, u + 1, u} AddCommGrpCat.{u}).obj
        (((Stacks.ChaoticSite.abelianPointLowerShriek
              (smallBoundedPolynomialSite A B
                (standardResolutionVarCardinal A B))).leftDerived 0).obj
          ((Stacks.ChaoticSite.abelianPointInverseImage
            (smallBoundedPolynomialSite A B
              (standardResolutionVarCardinal A B))).obj M)) ≅
      (Stacks.ChaoticSite.pointSections.{u, u + 1, u} AddCommGrpCat.{u}).obj M :=
  Stacks.ChaoticSite.leftDerivedZeroLowerShriekInverseImageIso _
    (isPointResolution_standardResolutionSmallCosimplicialObject A B) M

/-- **Tag 08QE at the small model of the restricted site `C_{B/A}`, in positive degrees.** The
sections at the point of `L_nπ_!(π^{-1}M)` vanish for `n > 0`, so together with
`CommAlgCat.polynomialLeftDerivedZeroLowerShriekInverseImageIso` this is the source's
`Lπ_!(π^{-1}M) = M`, read degreewise. -/
@[stacks 08QE "Lπ_!(π^{-1}M) = M in positive degrees: L_nπ_!(π^{-1}M) = 0 for n > 0"]
theorem isZero_polynomialLeftDerivedSuccLowerShriekInverseImage
    (M : Sheaf (GrothendieckTopology.trivial (Discrete PUnit.{u + 1})) AddCommGrpCat.{u})
    (n : ℕ) :
    IsZero ((Stacks.ChaoticSite.pointSections.{u, u + 1, u} AddCommGrpCat.{u}).obj
      (((Stacks.ChaoticSite.abelianPointLowerShriek
            (smallBoundedPolynomialSite A B
              (standardResolutionVarCardinal A B))).leftDerived (n + 1)).obj
        ((Stacks.ChaoticSite.abelianPointInverseImage
          (smallBoundedPolynomialSite A B
            (standardResolutionVarCardinal A B))).obj M))) :=
  Stacks.ChaoticSite.isZero_leftDerivedSucc_lowerShriek_inverseImage _
    (isPointResolution_standardResolutionSmallCosimplicialObject A B) M n

end Standard

end CommAlgCat

end
