module

public import Mathlib.Algebra.Category.ModuleCat.Descent
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.Monoidal.Tor
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology
public import StacksFrontier.Cotangent.Henselization
public import StacksFrontier.Cotangent.TensorProduct
public import StacksFrontier.Homology.ExtendScalars.IndependentUniverses

/-!
# The upper right corner of the fibre-product diagram at a geometric point

Let `X ⟶ B` and `Y ⟶ B` be morphisms of algebraic spaces over a scheme `S`, write
`W = X ×_B Y` with projections `p` and `q`, and let `E` be the object in the upper right corner
of the diagram

```
Lp^*L_{X/B} ⟶ L_{W/Y} ⟶ E
     ‖            ↑        ↑
Lp^*L_{X/B} ⟶ L_{W/B} ⟶ L_{W/X}
                  ↑        ↑
       Lq^*L_{Y/B} ═ Lq^*L_{Y/B}
```

Then `H^i(E) = 0` for `i = 0, -1`, and at a geometric point `(x̄, ȳ) : Spec k ⟶ X ×_B Y` one has
`H^{-2}(E)_{(x̄,ȳ)} = Tor_1^R(A, B) ⊗_{A ⊗_R B} C` for `R = 𝒪_{B,b̄}`, `A = 𝒪_{X,x̄}`,
`B = 𝒪_{Y,ȳ}` and `C = 𝒪_{X ×_B Y,(x̄,ȳ)}`.

This file works at the stalk, in ring-theoretic form: the stalk of `E` is the derived base change
along `A ⊗_R B ⟶ C` of the upper right corner `CommAlgCat.TensorProductNineDiagram.upperRight`
of the nine diagram of `R`, `A` and `B`, and `C` is flat over `A ⊗_R B`.

## Main definitions

* `CommAlgCat.derivedBaseChangeObj`: the derived base change `K ⊗^𝐋_D C` of an object of `D(D)`
  along a `D`-algebra `C`.
* `CommAlgCat.NineDiagramVanishing`: for every nine diagram, its upper right corner has no
  cohomology in degrees `≥ -1`.
* `CommAlgCat.NineDiagramTorOne`: for every nine diagram, the degree `-2` cohomology of its upper
  right corner is an `A ⊗_R B`-module whose underlying `R`-module is `Tor_1^R(A, B)`.

## Main results

* `CommAlgCat.flatTotalDerivedExtensionIso`: along a flat ring map the total derived extension
  of scalars is the functor induced degreewise on derived categories.
* `CommAlgCat.homologyDerivedBaseChangeIsoOfFlat`: cohomology commutes with a flat derived base
  change, `H^i(K ⊗^𝐋_D C) = H^i(K) ⊗_D C`.
* `CommAlgCat.nonempty_derivedBaseChangeObj_cotangentComplexDerived_iso_of_henselization`:
  `L_{A ⊗_R B/R} ⊗^𝐋_{A ⊗_R B} C = L_{C/R}` for `C` a henselization of the local ring
  `A ⊗_R B`.

## Implementation notes

`Tor_1^R(A, B)` is an `A ⊗_R B`-module through the action of `A` on the first variable and of
`B` on the second, and no `Module (A ⊗[R] B)` instance on a Tor module is available, so
`CommAlgCat.NineDiagramTorOne` names that module as an `A ⊗_R B`-module `T` whose underlying
`R`-module is the categorical `Tor_1^R(A, B)`.

`Tor` is Mathlib's `CategoryTheory.Tor`, left-derived in the second variable, which forces the
modules into the universe of `R`; `R`, `A`, `B` and `C` therefore all live in one universe here.

## References

* [Stacks Project, Tag 09DM](https://stacks.math.columbia.edu/tag/09DM)
* [Stacks Project, Tag 09DK](https://stacks.math.columbia.edu/tag/09DK)
* [Stacks Project, Tag 09DB](https://stacks.math.columbia.edu/tag/09DB)
* [Stacks Project, Tag 09D9](https://stacks.math.columbia.edu/tag/09D9)
* [Stacks Project, Tag 08T0](https://stacks.math.columbia.edu/tag/08T0)
* [Stacks Project, Tag 08SV](https://stacks.math.columbia.edu/tag/08SV)
* [Stacks Project, Tag 08UN](https://stacks.math.columbia.edu/tag/08UN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

open scoped TensorProduct

universe u v

namespace CommAlgCat

attribute [local instance] Algebra.TensorProduct.rightAlgebra
attribute [local instance 2000] HasDerivedCategory.standard

/-- The derived base change `K ⊗^𝐋_D C` of an object of `D(D)` along a `D`-algebra `C`, for the
canonical unbounded derived extension of scalars. -/
public noncomputable abbrev derivedBaseChangeObj {D : Type u} [CommRing D] (C : Type u)
    [CommRing C] [Algebra D C] (K : DerivedCategory (ModuleCat.{u} D)) :
    DerivedCategory (ModuleCat.{u} C) :=
  (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars
    (algebraMap D C)).functor.obj K

/-- For a flat ring map, the total left derived functor of extension of scalars is the functor
that extension of scalars induces degreewise on the derived categories. -/
public def flatTotalDerivedExtensionIso {D C : Type u} [CommRing D] [CommRing C]
    (φ : D →+* C) (hφ : φ.Flat) :
    letI := ModuleCat.preservesFiniteLimits_extendScalars_of_flat hφ
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars φ).functor ≅
      (ModuleCat.extendScalars.{u, u, u} φ).mapDerivedCategory := by
  let := ModuleCat.preservesFiniteLimits_extendScalars_of_flat hφ
  let F := ModuleCat.extendScalars.{u, u, u} φ
  let T := CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars φ
  have : IsIso T.comparison := Functor.isIso_of_isLeftDerivedFunctor_of_inverts
    T.functor T.comparison
    (W := HomologicalComplex.quasiIso (ModuleCat.{u} D) (ComplexShape.up ℤ)) (by
      intro X Y g hg
      have : QuasiIso g := hg
      change IsIso (DerivedCategory.Q.map ((F.mapHomologicalComplex _).map g))
      infer_instance)
  exact Localization.liftNatIso DerivedCategory.Q (HomologicalComplex.quasiIso _ _)
    (DerivedCategory.Q ⋙ T.functor) (DerivedCategory.Q ⋙ F.mapDerivedCategory) _ _
    (asIso T.comparison ≪≫ F.mapDerivedCategoryFactors.symm)

/-- For a flat `D`-algebra `C` and an object `K` of `D(D)`, the `i`-th cohomology of
`K ⊗^𝐋_D C` is `H^i(K) ⊗_D C`. -/
public def homologyDerivedBaseChangeIsoOfFlat {D : Type u} [CommRing D] (C : Type u)
    [CommRing C] [Algebra D C] (hC : (algebraMap D C).Flat)
    (K : DerivedCategory (ModuleCat.{u} D)) (i : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} C) i).obj (derivedBaseChangeObj C K) ≅
      (ModuleCat.extendScalars.{u, u, u} (algebraMap D C)).obj
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} D) i).obj K) :=
  let := ModuleCat.preservesFiniteLimits_extendScalars_of_flat hC
  let := ModuleCat.extendScalars_preservesFiniteColimits.{u, u, u} (algebraMap D C)
  (DerivedCategory.homologyFunctor (ModuleCat.{u} C) i).mapIso
      ((flatTotalDerivedExtensionIso (algebraMap D C) hC).app K) ≪≫
    ((ModuleCat.extendScalars.{u, u, u} (algebraMap D C)).mapDerivedCategoryHomologyIso i).app K

/-- For every ring `R`, every pair of `R`-algebras `A` and `B` in the universe of `R` and every
instance of the nine diagram, the object `E` in its upper right corner has no cohomology in
degrees `≥ -1`. -/
public def NineDiagramVanishing : Prop :=
  ∀ (R : Type u) [CommRing R] (A B : Type u) [CommRing A] [CommRing B] [Algebra R A]
    [Algebra R B] (D : TensorProductNineDiagram R A B) (i : ℤ), -1 ≤ i →
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} (A ⊗[R] B)) i).obj D.upperRight)

/-- For every ring `R`, every pair of `R`-algebras `A` and `B` in the universe of `R` and every
instance of the nine diagram, the degree `-2` cohomology of the object `E` in its upper right
corner is an `A ⊗_R B`-module whose underlying `R`-module is `Tor_1^R(A, B)`. -/
public def NineDiagramTorOne : Prop :=
  ∀ (R : Type u) [CommRing R] (A B : Type u) [CommRing A] [CommRing B] [Algebra R A]
    [Algebra R B] (D : TensorProductNineDiagram R A B),
    ∃ T : ModuleCat.{u} (A ⊗[R] B),
      Nonempty ((ModuleCat.restrictScalars (algebraMap R (A ⊗[R] B))).obj T ≅
        ((Tor (ModuleCat.{u} R) 1).obj (ModuleCat.of R A)).obj (ModuleCat.of R B)) ∧
      Nonempty ((DerivedCategory.homologyFunctor (ModuleCat.{u} (A ⊗[R] B)) (-2)).obj
        D.upperRight ≅ T)

/-- If the local ring `A ⊗_R B` has henselization `C`, with residue field extension `L`, then the
derived base change of `L_{A ⊗_R B/R}` along `A ⊗_R B ⟶ C` is `L_{C/R}`. It takes two hypotheses:
`hQX : HasEtaleDiagonalTriangle (A ⊗[R] B)`, and `hT`, that the triangle
`L_{A ⊗_R B/R} ⊗^𝐋 C ⟶ L_{C/R} ⟶ L_{C/A ⊗_R B}` formed by `α`, `β` and `γ` is distinguished. -/
public theorem nonempty_derivedBaseChangeObj_cotangentComplexDerived_iso_of_henselization
    (R : Type u) [CommRing R] (A B : Type u) [CommRing A] [CommRing B] [Algebra R A]
    [Algebra R B] [IsLocalRing (A ⊗[R] B)]
    (L : Type v) [Field L] [Algebra (IsLocalRing.ResidueField (A ⊗[R] B)) L]
    (C : Type u) [CommRing C] [IsLocalRing C] [Algebra (A ⊗[R] B) C]
    [IsLocalRing.IsHenselization (A ⊗[R] B) L C] [Algebra R C]
    [IsScalarTower R (A ⊗[R] B) C] (hQX : HasEtaleDiagonalTriangle.{u} (A ⊗[R] B))
    {α : fundamentalVertex₁.{u, u} R (A ⊗[R] B) C ⟶ fundamentalVertex₂.{u, u} R C}
    {β : fundamentalVertex₂.{u, u} R C ⟶ fundamentalVertex₃.{u, u} (A ⊗[R] B) C}
    {γ : fundamentalVertex₃.{u, u} (A ⊗[R] B) C ⟶
      (fundamentalVertex₁.{u, u} R (A ⊗[R] B) C)⟦(1 : ℤ)⟧}
    (hT : Triangle.mk α β γ ∈ distTriang (DerivedCategory (ModuleCat.{u} C))) :
    Nonempty (derivedBaseChangeObj C
        (cotangentComplexDerived R (CommAlgCat.of R (A ⊗[R] B))) ≅
      cotangentComplexDerived R (CommAlgCat.of R C)) :=
  nonempty_fundamentalVertex₁_iso_fundamentalVertex₂_henselization R (A ⊗[R] B) L C hQX hT

variable {R : Type u} [CommRing R] {A B : Type u} [CommRing A] [CommRing B] [Algebra R A]
  [Algebra R B] (C : Type u) [CommRing C] [Algebra (A ⊗[R] B) C]

end CommAlgCat

end
