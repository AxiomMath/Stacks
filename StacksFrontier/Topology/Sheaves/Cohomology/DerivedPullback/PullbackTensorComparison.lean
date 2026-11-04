module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.TensorProductCompatibility
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.AdjunctionUnconditional
public import Mathlib.CategoryTheory.Localization.Prod
import StacksCore.Tactic.StacksAttribute

/-!
# Derived pullback is monoidal

Let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces.  Stacks 079U is the canonical
bifunctorial isomorphism

`Lf^*(K ⊗^L_{𝒪_Y} L) ≅ Lf^*K ⊗^L_{𝒪_X} Lf^*L`

for `K, L ∈ D(𝒪_Y)`.

## References

* [Stacks Project, Tag 079U](https://stacks.math.columbia.edu/tag/079U)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.SheafOfModules.KFlatPullback (kFlat_modulePullback_unconditional)
open scoped CategoryTheory.Prod

namespace Stacks.Cohomology.DerivedPullbackTensor

universe u

noncomputable section

/-! ### The transport of a total complex, in bifunctor form -/

section Transport

-- Only `Preadditive` is assumed, which is all a total complex needs.  Under `[Abelian A]` the
-- `HasMapBifunctor` binders would reach their zero morphisms through `Abelian.toPreadditive`,
-- which differs syntactically from the `Preadditive` of the concrete `HasMapBifunctor`
-- instances, and the kernel re-checks that mismatch, about 0.6 s, at each use site (#1226).
variable {A B : Type*} [Category A] [Category B] [Preadditive A] [Preadditive B]
  (F : A ⥤ A ⥤ A) (G : B ⥤ B ⥤ B) (P : A ⥤ B)
  [F.Additive] [∀ Z, (F.obj Z).Additive] [G.Additive] [∀ Z, (G.obj Z).Additive] [P.Additive]
  [∀ K L : CochainComplex A ℤ, HomologicalComplex.HasMapBifunctorReg K L F (ComplexShape.up ℤ)]
  [∀ K L : CochainComplex B ℤ, HomologicalComplex.HasMapBifunctorReg K L G (ComplexShape.up ℤ)]

/-- `Tot(F(-, -))`, the total complex of a bifunctor, as a functor on *pairs* of cochain
complexes.  Writing it on the product category rather than in curried form is what makes
naturality in both variables a single statement.

It is a reducible `def` of `Functor.map₂HomologicalComplexReg` rather than an `abbrev` of
Mathlib's `Functor.map₂HomologicalComplex`, so that the kernel compares two spellings of it, and
of its values, argument by argument instead of evaluating `F`. -/
@[reducible] def totalComplexPair :
    CochainComplex A ℤ × CochainComplex A ℤ ⥤ CochainComplex A ℤ :=
  Functor.uncurry.obj (F.map₂HomologicalComplexReg (ComplexShape.up ℤ) (ComplexShape.up ℤ)
    (ComplexShape.up ℤ))

/-- The total complex of a bifunctor, on a morphism of the product category: it is the total
complex of the pair of morphisms.  `CategoryTheory.Functor.uncurry` splits a morphism of a
product into its two one-sided parts, and
`HomologicalComplex.mapBifunctorMap_eq_map₂_comp` recombines them. -/
theorem totalComplexPair_map {K K' L L' : CochainComplex A ℤ} (a : K ⟶ K') (b : L ⟶ L') :
    (totalComplexPair F).map (a ×ₘ b) =
      HomologicalComplex.mapBifunctorMapReg a b F (ComplexShape.up ℤ) :=
  HomologicalComplex.mapBifunctorMap_eq_map₂_comp F _ a b

variable
  [∀ n : ℤ, PreservesColimitsOfShape
    (Discrete ↥(ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) ⁻¹' {n})) P]
  [∀ K L : CochainComplex A ℤ, HomologicalComplex₂.HasTotal
    (HomologicalComplex₂.mapBicomplex P
      (((F.mapBifunctorHomologicalComplex (ComplexShape.up ℤ)
        (ComplexShape.up ℤ)).obj K).obj L)) (ComplexShape.up ℤ)]
  (ε : ∀ a b : A, P.obj ((F.obj a).obj b) ≅ (G.obj (P.obj a)).obj (P.obj b))
  (hε₁ : ∀ {a a' : A} (u : a ⟶ a') (b : A),
    P.map ((F.map u).app b) ≫ (ε a' b).hom = (ε a b).hom ≫ (G.map (P.map u)).app (P.obj b))
  (hε₂ : ∀ (a : A) {b b' : A} (v : b ⟶ b'),
    P.map ((F.obj a).map v) ≫ (ε a b').hom = (ε a b).hom ≫ (G.obj (P.obj a)).map (P.map v))

/-- **The transport of a total complex along a functor, as an isomorphism of bifunctors.**
If the additive functor `P` carries `F` to `G` degreewise, by isomorphisms `ε` natural in
each variable, and preserves the antidiagonal coproducts occurring in a total complex, then

`P(Tot(F(K, L))) ≅ Tot(G(P K, P L))`

naturally in the pair `(K, L)`.  The components are
`CategoryTheory.Functor.mapBifunctorTotalIso` and the naturality is
`CategoryTheory.Functor.mapBifunctorTotalIso_hom_naturality`; the content of this
declaration is that the two assemble into a morphism of bifunctors. -/
def totalComplexPairTransport :
    totalComplexPair F ⋙ P.mapHomologicalComplex (ComplexShape.up ℤ) ≅
      (P.mapHomologicalComplex (ComplexShape.up ℤ)).prod
          (P.mapHomologicalComplex (ComplexShape.up ℤ)) ⋙ totalComplexPair G :=
  NatIso.ofComponents
    (fun KL => CategoryTheory.Functor.mapBifunctorTotalIso F G P P P ε
      (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) hε₁ hε₂ KL.1 KL.2)
    (fun {KL KL'} g => by
      have hA : (totalComplexPair F ⋙ P.mapHomologicalComplex (ComplexShape.up ℤ)).map g =
          (P.mapHomologicalComplex (ComplexShape.up ℤ)).map
            (HomologicalComplex.mapBifunctorMapReg g.1 g.2 F (ComplexShape.up ℤ)) :=
        congrArg (P.mapHomologicalComplex (ComplexShape.up ℤ)).map
          (totalComplexPair_map F g.1 g.2)
      have hB : ((P.mapHomologicalComplex (ComplexShape.up ℤ)).prod
            (P.mapHomologicalComplex (ComplexShape.up ℤ)) ⋙ totalComplexPair G).map g =
          HomologicalComplex.mapBifunctorMapReg
            ((P.mapHomologicalComplex (ComplexShape.up ℤ)).map g.1)
            ((P.mapHomologicalComplex (ComplexShape.up ℤ)).map g.2) G (ComplexShape.up ℤ) :=
        totalComplexPair_map G _ _
      rw [hA, hB]
      exact CategoryTheory.Functor.mapBifunctorTotalIso_hom_naturality F G P P P ε
        (ComplexShape.up ℤ) (ComplexShape.up ℤ) hε₁ hε₂ KL.1 KL'.1 KL.2 KL'.2 g.1 g.2)

end Transport

attribute [local instance] modulePullback_preservesAntidiagonalCoproducts

-- The pullback/pushforward development and the tensor-product development name the structure
-- sheaf of a ringed space differently, by `structureSheafRing` and by
-- `Stacks.SheafOfModules.Tensor.ringSheaf`.  The two are the same sheaf of rings by `rfl`, and
-- a statement mixing them — which every statement here does, since the derived pullback is
-- named at one spelling and the derived tensor product at the other — is not type-correct at
-- `implicit` transparency unless both are unfolded there.  `structureSheafRing` is
-- `@[instance_reducible]` and so already is, but its reduct stops at an explicit-constructor
-- projection while `Tensor.ringSheaf X.sheaf` reduces to `(sheafCompose _ _).obj X.sheaf`, so
-- the Mathlib definitions bridging those also have to unfold here; `modulePullback` needs the
-- attribute for the same reason.  `Tensor.ringSheaf` takes a
-- `Sheaf (Opens.grothendieckTopology X.carrier) CommRingCat` while `X.sheaf` is a
-- `TopCat.Sheaf CommRingCat X.carrier`, so `TopCat.Sheaf` and the `TopCat.Presheaf.IsSheaf` of
-- its sheaf condition have to unfold too.  Without all of this `dsimp` silently does nothing and
-- the subsequent rewrite reports that it did not find a pattern the goal visibly contains.
attribute [local implicit_reducible] StacksDraft.KFlat.modulePullback structureSheafRing
  Stacks.SheafOfModules.Tensor.ringSheaf
  CategoryTheory.sheafCompose AlgebraicGeometry.SheafedSpace.sheaf
  TopCat.Presheaf.IsSheaf TopCat.Sheaf

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-- The degreewise pullback of cochain complexes of modules, `f^*`, at the spelling of the
tensor product of sheaves of modules. -/
abbrev pullbackComplex :
    CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ ⥤
      CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X) ℤ :=
  (StacksDraft.KFlat.modulePullback f).mapHomologicalComplex (ComplexShape.up ℤ)

/-- The total complex of the degreewise pullback of a tensor double complex exists: `f^*`
preserves the antidiagonal coproducts it is assembled from. -/
instance hasTotal_mapBicomplex_modulePullback
    (K L : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ) :
    HomologicalComplex₂.HasTotal
      (HomologicalComplex₂.mapBicomplex (StacksDraft.KFlat.modulePullback f)
        ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf).mapBifunctorHomologicalComplex
          (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj K).obj L)) (ComplexShape.up ℤ) :=
  inferInstance

/-- **The comparison of total tensor complexes, as an isomorphism of bifunctors** on cochain
complexes of `𝒪_Y`-modules:

`f^*Tot(K ⊗_{𝒪_Y} L) ≅ Tot(f^*K ⊗_{𝒪_X} f^*L)`,

natural in the pair `(K, L)`.  This is `totalComplexPairTransport` at the degreewise
comparison of Stacks 01CD, so its value at a pair is `pullbackTensorComplexIsoOfIsIso`. -/
def pullbackTensorComplexNatIso :
    totalComplexPair (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf) ⋙
        pullbackComplex f ≅
      (pullbackComplex f).prod (pullbackComplex f) ⋙
        totalComplexPair (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf) :=
  totalComplexPairTransport (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf)
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf) (StacksDraft.KFlat.modulePullback f)
    (comparisonAppIso f) (fun {_ _} w B => comparisonAppIso_naturality_left f w B)
    (fun A {_ _} w => comparisonAppIso_naturality_right f A w)

/-! ### The derived pullback of a complex, as a natural transformation -/

section Derived

attribute [local instance] HasDerivedCategory.standard

/-- **The comparison `Lf^*(QM) ⟶ Q(f^*M)`, as a morphism of functors on cochain complexes.**
It is the comparison of the left-derived functor `Lf^*` with the degreewise pullback, with the
`Q` versus `Qh ∘ quotient` bridge `DerivedCategory.quotientCompQhIso` inserted at both ends
and Mathlib's `CategoryTheory.Functor.mapHomotopyCategoryFactors` identifying the degreewise
pullback on the homotopy category with the degreewise pullback of complexes. -/
def derivedPullbackNatTrans :
    DerivedCategory.Q ⋙ Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f ⟶
      pullbackComplex f ⋙ DerivedCategory.Q :=
  Functor.whiskerRight (DerivedCategory.quotientCompQhIso _).inv
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f) ≫
    Functor.whiskerLeft (HomotopyCategory.quotient _ (ComplexShape.up ℤ))
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison f) ≫
    Functor.whiskerRight ((RingedSpaceModuleAdjunction.modulePullback f).mapHomotopyCategoryFactors
      (ComplexShape.up ℤ)).hom DerivedCategory.Qh ≫
    Functor.whiskerLeft (pullbackComplex f) (DerivedCategory.quotientCompQhIso _).hom

/-- **A K-flat complex computes the derived pullback**: at a K-flat complex the comparison
`Lf^*(QM) ⟶ Q(f^*M)` is invertible.  The two bridges and
`CategoryTheory.Functor.mapHomotopyCategoryFactors` are isomorphisms unconditionally, and the
middle factor is
`Stacks.Cohomology.KFlatDerivedPullback.isIso_derivedPullbackComparison_app_of_kFlat`. -/
theorem isIso_derivedPullbackNatTrans_app
    (K : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ)
    (hK : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Y K) :
    IsIso ((derivedPullbackNatTrans f).app K) := by
  have := Stacks.Cohomology.KFlatDerivedPullback.isIso_derivedPullbackComparison_app_of_kFlat
    f K hK
  dsimp only [derivedPullbackNatTrans, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app]
  infer_instance

/-! ### The two comparisons into the ordinary total tensor complex -/

section Comparisons

variable [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Y.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **The canonical map from the derived tensor product to the ordinary total tensor
complex**, as a morphism of functors on pairs of cochain complexes of `𝒪_Z`-modules:

`QK ⊗^L_{𝒪_Z} QL ⟶ Q(Tot(K ⊗_{𝒪_Z} L))`.

Its components are the `toTensor` field of Stacks 06YU and its naturality is the
`toTensor_naturality` field. -/
def derivedToTensorNatTrans (Z : RingedSpace.{u, u})
    [HasSheafify (Opens.grothendieckTopology Z.carrier) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology Z.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}] :
    DerivedCategory.Q.prod DerivedCategory.Q ⋙
        Functor.uncurry.obj
          (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Z.sheaf) ⟶
      totalComplexPair (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.sheaf) ⋙
        DerivedCategory.Q where
  app KL := (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct Z.sheaf).toTensor
    KL.1 KL.2
  naturality KL KL' g := by
    have h := (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct Z.sheaf
      ).toTensor_naturality g.1 g.2
    rw [← Category.assoc] at h
    exact h.trans (congrArg
      ((Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct Z.sheaf).toTensor KL.1 KL.2 ≫
        DerivedCategory.Q.map ·)
      (totalComplexPair_map (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.sheaf) g.1 g.2).symm)

/-- The functor `(K, L) ↦ Lf^*(K ⊗^L_{𝒪_Y} L)` on `D(𝒪_Y) × D(𝒪_Y)`. -/
abbrev pullbackOfTensor :
    DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ×
        DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ⥤
      DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X) :=
  Functor.uncurry.obj (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.sheaf) ⋙
    Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f

/-- The functor `(K, L) ↦ Lf^*K ⊗^L_{𝒪_X} Lf^*L` on `D(𝒪_Y) × D(𝒪_Y)`. -/
abbrev tensorOfPullbacks :
    DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ×
        DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ⥤
      DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X) :=
  (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f).prod
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f) ⋙
    Functor.uncurry.obj (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf)

/-- The comparison of `Lf^*(K ⊗^L_{𝒪_Y} L)` with `Q(f^*Tot(K ⊗_{𝒪_Y} L))`: first the
canonical map to the ordinary total tensor complex on `Y`, then the derived pullback of a
complex. -/
def leftComparison :
    DerivedCategory.Q.prod DerivedCategory.Q ⋙ pullbackOfTensor f ⟶
      totalComplexPair (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf) ⋙
        pullbackComplex f ⋙ DerivedCategory.Q :=
  Functor.whiskerRight (derivedToTensorNatTrans Y)
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f) ≫
    Functor.whiskerLeft (totalComplexPair (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf))
      (derivedPullbackNatTrans f)

/-- The comparison of `Lf^*K ⊗^L_{𝒪_X} Lf^*L` with `Q(f^*Tot(K ⊗_{𝒪_Y} L))`: the derived
pullback of each factor, then the canonical map to the ordinary total tensor complex on `X`,
then the comparison of total complexes of Stacks 01CD. -/
def rightComparison :
    DerivedCategory.Q.prod DerivedCategory.Q ⋙ tensorOfPullbacks f ⟶
      totalComplexPair (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf) ⋙
        pullbackComplex f ⋙ DerivedCategory.Q :=
  Functor.whiskerRight ((derivedPullbackNatTrans f).prod (derivedPullbackNatTrans f))
      (Functor.uncurry.obj
        (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf)) ≫
    Functor.whiskerLeft ((pullbackComplex f).prod (pullbackComplex f))
        (derivedToTensorNatTrans X) ≫
      Functor.whiskerRight (pullbackTensorComplexNatIso f).inv DerivedCategory.Q

/-! ### The comparison on K-flat representatives -/

/-- **On a pair of K-flat complexes the left comparison is invertible.**  The canonical map to
the ordinary total tensor complex is the K-flat comparison of Stacks 06YU there, and
`Tot(K ⊗_{𝒪_Y} L)` is itself K-flat by Stacks 079R, so the derived pullback of a complex
computes it. -/
theorem isIso_leftComparison_app
    (K L : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ)
    (hK : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Y K)
    (hL : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Y L) :
    IsIso ((leftComparison f).app (K, L)) := by
  have h : IsIso ((derivedPullbackNatTrans f).app
      ((totalComplexPair (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf)).obj (K, L))) :=
    isIso_derivedPullbackNatTrans_app f _ (kFlat_tensorComplex Y K L hK hL)
  dsimp only [leftComparison, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, derivedToTensorNatTrans]
  rw [(Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct
    Y.sheaf).toTensor_eq_comparison K L hK hL]
  exact IsIso.comp_isIso' (@Functor.map_isIso _ _ _ _ _ _ _ _ (Iso.isIso_hom _)) h

/-- **On a pair of K-flat complexes the right comparison is invertible.**  Each derived
pullback is computed by the degreewise pullback, those are K-flat by Stacks 06YC, and the
canonical map to the ordinary total tensor complex on `X` is the K-flat comparison of Stacks
06YU there. -/
theorem isIso_rightComparison_app
    (K L : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ)
    (hK : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Y K)
    (hL : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Y L) :
    IsIso ((rightComparison f).app (K, L)) := by
  have h₁ := isIso_derivedPullbackNatTrans_app f K hK
  have h₂ := isIso_derivedPullbackNatTrans_app f L hL
  have hKx := kFlat_modulePullback_unconditional f K hK
  have hLx := kFlat_modulePullback_unconditional f L hL
  have hpair : IsIso
      ((derivedPullbackNatTrans f).app K ×ₘ (derivedPullbackNatTrans f).app L) := by
    rw [isIso_prod_iff]
    exact ⟨h₁, h₂⟩
  -- The instance is named rather than searched for.  `inferInstanceAs` here sends instance
  -- search over the components of `pullbackTensorComplexNatIso`, and every `IsIso` instance it
  -- tries is unified against that term, costing about 278 s of elaboration for this one `have`.
  have hcx : IsIso ((pullbackTensorComplexNatIso f).inv.app (K, L)) :=
    ((pullbackTensorComplexNatIso f).app (K, L)).isIso_inv
  dsimp only [rightComparison, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, derivedToTensorNatTrans, NatTrans.prod, Functor.prod_obj]
  rw [(Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct
    X.sheaf).toTensor_eq_comparison _ _ hKx hLx]
  exact IsIso.comp_isIso' (@Functor.map_isIso _ _ _ _ _ _ _ _ hpair)
    (IsIso.comp_isIso' (Iso.isIso_hom _) (@Functor.map_isIso _ _ _ _ _ _ _ _ hcx))

/-- **Stacks 079U on K-flat representatives.**  Both comparisons into `Q(f^*Tot(K ⊗ L))` are
invertible on a pair of K-flat complexes, so they compose to the pullback-tensor isomorphism
`Lf^*(QK ⊗^L QL) ≅ Lf^*(QK) ⊗^L Lf^*(QL)` there. -/
def modelComparison
    (K L : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ)
    (hK : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Y K)
    (hL : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Y L) :
    (pullbackOfTensor f).obj (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L) ≅
      (tensorOfPullbacks f).obj (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L) :=
  haveI := isIso_leftComparison_app f K L hK hL
  haveI := isIso_rightComparison_app f K L hK hL
  asIso ((leftComparison f).app (K, L)) ≪≫ (asIso ((rightComparison f).app (K, L))).symm

/-- **A naturality square for an isomorphism presented as `l ≫ inv r`**, from the naturality
squares of `l` and of `r` over a common map `m` of the shared target.

Stated abstractly and applied by unification.  The conclusion mentions the isomorphisms only
through `Iso.hom`, so matching it against the concrete goal is first order and the descriptions
`he`, `he'` determine every other argument; nothing is unfolded during unification.  Unfolding
`Stacks.Cohomology.DerivedPullbackTensor.modelComparison` in the concrete goal with `dsimp only`
instead makes the simplifier traverse the whole statement, which takes about 275 s. -/
private lemma hom_comp_inv_naturality {C : Type*} [Category C] {V V' W W' Z Z' : C}
    {e : V ≅ W} {e' : V' ≅ W'} {u : V ⟶ V'} {v : W ⟶ W'} {m : Z ⟶ Z'}
    {l : V ⟶ Z} {r : W ⟶ Z} {l' : V' ⟶ Z'} {r' : W' ⟶ Z'} [IsIso r] [IsIso r']
    (he : e.hom = l ≫ inv r) (he' : e'.hom = l' ≫ inv r')
    (hl : u ≫ l' = l ≫ m) (hr : v ≫ r' = r ≫ m) :
    u ≫ e'.hom = e.hom ≫ v := by
  have key : m ≫ inv r' = inv r ≫ v := by
    rw [IsIso.eq_inv_comp, ← Category.assoc, ← hr, Category.assoc, IsIso.hom_inv_id,
      Category.comp_id]
  rw [he, he', ← Category.assoc, hl, Category.assoc, key, Category.assoc]

/-- The comparison on K-flat representatives is natural in cochain maps between them. -/
theorem modelComparison_naturality
    {K K' L L' : CochainComplex
      (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ}
    (a : K ⟶ K') (b : L ⟶ L')
    (hK : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Y K)
    (hK' : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Y K')
    (hL : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Y L)
    (hL' : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Y L') :
    (pullbackOfTensor f).map (DerivedCategory.Q.map a ×ₘ DerivedCategory.Q.map b) ≫
        (modelComparison f K' L' hK' hL').hom =
      (modelComparison f K L hK hL).hom ≫
        (tensorOfPullbacks f).map (DerivedCategory.Q.map a ×ₘ DerivedCategory.Q.map b) := by
  have := isIso_leftComparison_app f K L hK hL
  have := isIso_leftComparison_app f K' L' hK' hL'
  have := isIso_rightComparison_app f K' L' hK' hL'
  have := isIso_rightComparison_app f K L hK hL
  have he : (modelComparison f K L hK hL).hom =
      (leftComparison f).app (K, L) ≫ inv ((rightComparison f).app (K, L)) := rfl
  have he' : (modelComparison f K' L' hK' hL').hom =
      (leftComparison f).app (K', L') ≫ inv ((rightComparison f).app (K', L')) := rfl
  have hl : (pullbackOfTensor f).map (DerivedCategory.Q.map a ×ₘ DerivedCategory.Q.map b) ≫
        (leftComparison f).app (K', L') =
      (leftComparison f).app (K, L) ≫
        (totalComplexPair (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf) ⋙
          pullbackComplex f ⋙ DerivedCategory.Q).map (a ×ₘ b) :=
    (leftComparison f).naturality (a ×ₘ b)
  have hr : (tensorOfPullbacks f).map (DerivedCategory.Q.map a ×ₘ DerivedCategory.Q.map b) ≫
        (rightComparison f).app (K', L') =
      (rightComparison f).app (K, L) ≫
        (totalComplexPair (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf) ⋙
          pullbackComplex f ⋙ DerivedCategory.Q).map (a ×ₘ b) :=
    (rightComparison f).naturality (a ×ₘ b)
  exact hom_comp_inv_naturality he he' hl hr

/-! ### Descent along the K-flat localization -/

/-- The K-flat objects of the homotopy category of `𝒪_Y`-modules, viewed in `D(𝒪_Y)`.  By
Stacks 06YS this is a localization of the K-flat objects at the quasi-isomorphisms between
them, which is what a transformation of functors on `D(𝒪_Y)` descends along. -/
abbrev kFlatQY :=
  CochainComplex.KFlatBifunctor.kFlatQ (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf)

/-- Pairs of K-flat objects of the homotopy category, viewed in `D(𝒪_Y) × D(𝒪_Y)`. -/
abbrev kFlatQPair := (kFlatQY (Y := Y)).prod (kFlatQY (Y := Y))

/-- The quasi-isomorphisms between pairs of K-flat objects. -/
abbrev kFlatQuasiIsoPair :=
  (CochainComplex.KFlatBifunctor.kFlatQuasiIso
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf)).prod
    (CochainComplex.KFlatBifunctor.kFlatQuasiIso
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf))

/-- **`D(𝒪_Y) × D(𝒪_Y)` is the localization of the pairs of K-flat objects at the
quasi-isomorphisms.**  A localization of a product of categories is the product of the
localizations, and each factor is
the instance `CochainComplex.KFlatBifunctor.kFlatQ_isLocalization_of_hasLeftResolutions`. -/
theorem kFlatQPair_isLocalization :
    (kFlatQPair (Y := Y)).IsLocalization (kFlatQuasiIsoPair (Y := Y)) := by
  have : (CochainComplex.KFlatBifunctor.kFlatQuasiIso
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf)).ContainsIdentities := by
    infer_instance
  exact Functor.IsLocalization.prod (kFlatQY (Y := Y)) _ (kFlatQY (Y := Y)) _

/-- The image in `D(𝒪_Y) × D(𝒪_Y)` of a pair of K-flat objects of the homotopy category is
the image of the underlying pair of complexes: the `Q` versus `Qh ∘ quotient` bridge, in both
variables. -/
def kFlatQPairIso (M : (CochainComplex.KFlatBifunctor.kFlatObjects
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf)).FullSubcategory ×
    (CochainComplex.KFlatBifunctor.kFlatObjects
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf)).FullSubcategory) :
    (kFlatQPair (Y := Y)).obj M ≅
      (DerivedCategory.Q.obj M.1.obj.as, DerivedCategory.Q.obj M.2.obj.as) :=
  ((DerivedCategory.quotientCompQhIso _).app M.1.obj.as).prod
    ((DerivedCategory.quotientCompQhIso _).app M.2.obj.as)

/-- The `Q` versus `Qh ∘ quotient` bridge is natural in a morphism of the homotopy category,
which is the class of any of its cochain representatives. -/
private theorem qh_map_comp_quotientCompQhIso_hom
    {M N : HomotopyCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y)
      (ComplexShape.up ℤ)} (g : M ⟶ N) :
    DerivedCategory.Qh.map g ≫ (DerivedCategory.quotientCompQhIso _).hom.app N.as =
      (DerivedCategory.quotientCompQhIso _).hom.app M.as ≫ DerivedCategory.Q.map g.out := by
  have h := DerivedCategory.quotientCompQhIso_hom_naturality
    (C := AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) g.out
  rwa [HomotopyCategory.quotient_map_out] at h

/-- The bridge is natural: a homotopy class between K-flat objects is the class of a cochain
map, and the bridge is natural in cochain maps. -/
theorem kFlatQPairIso_naturality {M N : (CochainComplex.KFlatBifunctor.kFlatObjects
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf)).FullSubcategory ×
    (CochainComplex.KFlatBifunctor.kFlatObjects
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf)).FullSubcategory} (g : M ⟶ N) :
    (kFlatQPair (Y := Y)).map g ≫ (kFlatQPairIso N).hom =
      (kFlatQPairIso M).hom ≫
        (DerivedCategory.Q.map g.1.hom.out ×ₘ DerivedCategory.Q.map g.2.hom.out) := by
  apply Prod.ext
  · exact qh_map_comp_quotientCompQhIso_hom g.1.hom
  · exact qh_map_comp_quotientCompQhIso_hom g.2.hom

/-- Conjugating an isomorphism of values by isomorphisms of the objects preserves a
naturality square.  This is the step that carries the comparison from the chosen cochain
representatives of a pair of K-flat objects to the images of those objects in the derived
category. -/
lemma naturality_transport {C E : Type*} [Category C] [Category E]
    (F G : C ⥤ E) {Z₁ Z₂ Z₁' Z₂' : C} (e₁ : Z₁ ≅ Z₁') (e₂ : Z₂ ≅ Z₂')
    (a : F.obj Z₁' ≅ G.obj Z₁') (b : F.obj Z₂' ≅ G.obj Z₂')
    (u : Z₁ ⟶ Z₂) (v : Z₁' ⟶ Z₂') (hu : u ≫ e₂.hom = e₁.hom ≫ v)
    (hv : F.map v ≫ b.hom = a.hom ≫ G.map v) :
    F.map u ≫ (F.mapIso e₂ ≪≫ b ≪≫ (G.mapIso e₂).symm).hom =
      (F.mapIso e₁ ≪≫ a ≪≫ (G.mapIso e₁).symm).hom ≫ G.map u := by
  have hui : e₁.inv ≫ u = v ≫ e₂.inv := by
    apply (cancel_mono e₂.hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [hu, Iso.inv_hom_id_assoc]
  dsimp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Functor.mapIso_inv]
  simp only [Category.assoc]
  rw [← F.map_comp_assoc, hu, F.map_comp_assoc, reassoc_of% hv, ← G.map_comp, ← G.map_comp,
    hui]

/-- **Stacks 079U on K-flat representatives, as an isomorphism of functors** on pairs of
K-flat objects of the homotopy category of `𝒪_Y`-modules.  Its value at a pair is
`modelComparison`, transported along the `Q` versus `Qh ∘ quotient` bridge; its naturality in
homotopy classes is `modelComparison_naturality` at any cochain representatives of those
classes. -/
def modelsComparison :
    kFlatQPair (Y := Y) ⋙ pullbackOfTensor f ≅
      kFlatQPair (Y := Y) ⋙ tensorOfPullbacks f :=
  NatIso.ofComponents
    (fun M => (pullbackOfTensor f).mapIso (kFlatQPairIso M) ≪≫
      modelComparison f M.1.obj.as M.2.obj.as M.1.property M.2.property ≪≫
        ((tensorOfPullbacks f).mapIso (kFlatQPairIso M)).symm)
    (fun {M N} g => by
      refine naturality_transport _ _ (kFlatQPairIso M) (kFlatQPairIso N)
        (modelComparison f M.1.obj.as M.2.obj.as M.1.property M.2.property)
        (modelComparison f N.1.obj.as N.2.obj.as N.1.property N.2.property)
        ((kFlatQPair (Y := Y)).map g) _ (kFlatQPairIso_naturality g) ?_
      exact modelComparison_naturality f g.1.hom.out g.2.hom.out
        M.1.property N.1.property M.2.property N.2.property)

attribute [local instance] kFlatQPair_isLocalization

/-- **Stacks 079U: derived pullback is monoidal.**  For a morphism of ringed spaces
`f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` there is a canonical isomorphism

`Lf^*(K ⊗^L_{𝒪_Y} L) ≅ Lf^*K ⊗^L_{𝒪_X} Lf^*L`,

bifunctorial in `K, L ∈ D(𝒪_Y)`.

It is constructed the way the source constructs it.  On K-flat representatives both sides are
computed by ordinary total tensor complexes — the K-flat comparison of Stacks 06YU and the
fact that a K-flat complex computes `Lf^*` — and there the comparison is the degreewise
isomorphism `f^*(K^p ⊗_{𝒪_Y} L^q) ≅ f^*K^p ⊗_{𝒪_X} f^*L^q` of Stacks 01CD assembled on total
complexes.  Since `D(𝒪_Y)` is the localization of the K-flat objects of the homotopy category
at the quasi-isomorphisms (Stacks 06YS), the product of two copies of that localization
descends the comparison from K-flat representatives to all of `D(𝒪_Y) × D(𝒪_Y)`, which is
what makes the statement bifunctorial. -/
@[stacks 079U]
def derivedPullbackTensorIso : pullbackOfTensor f ≅ tensorOfPullbacks f :=
  Localization.liftNatIso (kFlatQPair (Y := Y)) (kFlatQuasiIsoPair (Y := Y)) _ _ _ _
    (modelsComparison f)

end Comparisons

end Derived

end

end Stacks.Cohomology.DerivedPullbackTensor

end
