module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.InternalHomStalkTransportClauses
public import StacksFrontier.Topology.Sheaves.Cohomology.KFlat.StalkTensorBifunctor
public import StacksFrontier.Homology.Tor.DerivedTensorUniverse
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.PullbackTensorComparison
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The stalk of a point is monoidal on the one-point space

Let `(X, 𝒪_X)` be a ringed space, `x ∈ X`, and let `Y = {x}` be the one-point ringed space with
structure sheaf `𝒪_{X,x}`.  The stalk at the point identifies `D(𝒪_Y)` with `D(𝒪_{X,x})`.  This
file proves that this identification carries the derived tensor product of `Y` to the derived
tensor product over `𝒪_{X,x}`,

`(K ⊗^L_{𝒪_Y} L)_x ≅ K_x ⊗^L_{𝒪_{X,x}} L_x`,

as an isomorphism of bifunctors, and deduces that it carries the derived internal hom of `Y` to
`RHom_{𝒪_{X,x}}`, the internal hom of the tensor–hom adjunction of Tag 0A63.  This presents the
point as a one-point ringed space over `X` in the sense of `StalkPresentation`.

The proof is the one of Tag 079U for an equivalence: on K-flat representatives both sides are
computed by the ordinary total tensor complex — the stalk of a K-flat complex being K-flat — and
there the comparison is Tag 01CB assembled on total complexes; `D(𝒪_Y) × D(𝒪_Y)` is the
localization of the pairs of K-flat objects of the homotopy category, which descends it.

## Main definitions

* `Stacks.Cohomology.DerivedInternalHomStalk.stalkDerivedTensorIso`: the comparison of the two
  derived tensor bifunctors.
* `Stacks.Cohomology.DerivedInternalHomStalk.pointStalkInternalHomComparison`: the stalk
  identification carries the derived internal hom of `Y` to `RHom_{𝒪_{X,x}}`.
* `Stacks.Cohomology.DerivedInternalHomStalk.pointStalkPresentation`: the presentation of the
  point, for every ringed space and every point.

## Main results

* `Stacks.Cohomology.DerivedInternalHomStalk.kFlat_pointStalkComplex`: the stalk at the point
  preserves K-flatness.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open scoped CategoryTheory.Prod

namespace Stacks.Cohomology.DerivedInternalHomStalk

universe u

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local implicit_reducible] CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf

-- The two `Ring` structures on the stalk ring `𝒪_{X,x}` — the one the `RingCat`-valued stalk
-- carries and `CommRing.toRing` of `stalkCommRing` — differ by nothing but the unfolding of
-- `Stacks.SheafOfModules.Tensor.ringSheaf`: `StacksDraft.StalkTensor.commRing_stalk_ringSheaf` is
-- `StacksDraft.StalkTensor.commRing_stalk` at `X.sheaf.obj ⋙ forget₂ CommRingCat RingCat`, which
-- is the explicit constructor argument of `Tensor.ringSheaf X.sheaf`, and both of those are
-- instances and so already unfold at `TransparencyMode.instances`.  `Tensor.ringSheaf` itself is
-- an ordinary `def`, so without this the two meet only at `implicit` transparency — strictly
-- above `.instances` — and instance *search* cannot cross between them.  That is what made
-- `(ringTensor X x).Additive` unsynthesizable in `pointStalkTensorComplexIso`, whose `B` is fixed
-- at the `RingCat` spelling by `pointStalk`.
--
-- Restored.  The seat was removed on the strength of a declaration-site `@[reducible]` on
-- `Tensor.ringSheaf`, since reverted (`a8c969ee9f820`, "revert the declaration-site
-- `@[reducible]` and restore the 59 file-local attribute entries"), so the paragraph above
-- applies again verbatim.  Naming the module category at the matching `Ring` instance instead
-- (`letI : Ring (stalkRing X x) := @CommRing.toRing _ (stalkCommRing X x)` in an abbreviation
-- for `ModuleCat.{u} (stalkRing X x)`) does remove `(ringTensor X x).Additive` outright, but it
-- migrates the burden along the equivalence's instance set rather than discharging it: the
-- `PreservesColimitsOfShape` and `PreservesFiniteLimits` instances for the stalk functor are
-- themselves declared at the `RingCat`-stalk naming, and come back unsynthesizable in turn.
attribute [local instance_reducible] Stacks.SheafOfModules.Tensor.ringSheaf

section Generic

open Stacks.SheafOfModules.KFlatStalkCriterion

variable (Y : RingedSpace.{u, u}) (y : Y.carrier) (R : Type u) [CommRing R]
  (e : R ≃+* ToType (stalkTensorRing Y y))

/-- The stalk at `y`, read over a ring `R` identified with `𝒪_{Y,y}`. -/
abbrev stalkOver : SheafOfModules.{u} (structureSheafRing Y) ⥤ ModuleCat.{u} R :=
  AlgebraicGeometry.SheafOfModules.stalkFunctor (structureSheafRing Y) y ⋙
    ModuleCat.restrictScalars.{u, u, u} e.toRingHom

/-- **The stalk carries the tensor product to the tensor product**, read over `R`:
`(a ⊗_{𝒪_Y} b)_y ≅ a_y ⊗_R b_y`.  This is Tag 01CB followed by the compatibility of restriction
of scalars along a ring isomorphism with tensor products. -/
def stalkOverTensorIso (a b : SheafOfModules.{u} (structureSheafRing Y)) :
    (stalkOver Y y R e).obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf).obj a).obj b) ≅
      ((CochainComplex.DerivedTensor.moduleTensor.{u, u} R).obj ((stalkOver Y y R e).obj a)).obj
        ((stalkOver Y y R e).obj b) :=
  (ModuleCat.restrictScalars.{u, u, u} e.toRingHom).mapIso (stalkTensorIso Y y a b) ≪≫
    (CochainComplex.DerivedTensor.restrictScalarsTensorIso e _ _).symm

/-- Two commuting squares paste to a commuting square.  Stated over an arbitrary category so that
it applies by unification alone. -/
theorem comp_square {C : Type*} [Category C] {A A' B B' D D' : C} (m : A ⟶ A') (α : A ⟶ B)
    (α' : A' ⟶ B') (n : B ⟶ B') (β : B ⟶ D) (β' : B' ⟶ D') (k : D ⟶ D')
    (h₁ : m ≫ α' = α ≫ n) (h₂ : n ≫ β' = β ≫ k) : m ≫ (α' ≫ β') = (α ≫ β) ≫ k := by
  rw [← Category.assoc, h₁, Category.assoc, h₂, Category.assoc]

/-- Additive maps out of a tensor product agree once they agree on pure tensors. -/
private theorem tensor_addMonoidHom_ext {S M N P : Type*} [CommSemiring S] [AddCommMonoid M]
    [AddCommMonoid N] [AddCommMonoid P] [Module S M] [Module S N] {f g : TensorProduct S M N →+ P}
    (h : ∀ m n, f (.tmul S m n) = g (.tmul S m n)) : f = g := by
  ext z
  induction z using TensorProduct.inductionOn with
  | tmul m n => exact h m n
  | add a b ha hb => simp only [map_add, ha, hb]

/-- The comparison of restriction of scalars with tensor products is natural in the first
variable. -/
theorem restrictScalarsTensorIso_inv_naturality_left
    {M M' : ModuleCat.{u} (ToType (stalkTensorRing Y y))} (f : M ⟶ M')
    (N : ModuleCat.{u} (ToType (stalkTensorRing Y y))) :
    (ModuleCat.restrictScalars.{u, u, u} e.toRingHom).map
        (((MonoidalCategory.curriedTensor
            (ModuleCat.{u} (ToType (stalkTensorRing Y y)))).map f).app N) ≫
      (CochainComplex.DerivedTensor.restrictScalarsTensorIso e M' N).inv =
    (CochainComplex.DerivedTensor.restrictScalarsTensorIso e M N).inv ≫
      ((CochainComplex.DerivedTensor.moduleTensor.{u, u} R).map
        ((ModuleCat.restrictScalars.{u, u, u} e.toRingHom).map f)).app
          ((ModuleCat.restrictScalars.{u, u, u} e.toRingHom).obj N) :=
  ModuleCat.hom_ext (LinearMap.toAddMonoidHom_injective
    (tensor_addMonoidHom_ext fun _ _ => rfl))

/-- The comparison of restriction of scalars with tensor products is natural in the second
variable. -/
theorem restrictScalarsTensorIso_inv_naturality_right
    (M : ModuleCat.{u} (ToType (stalkTensorRing Y y)))
    {N N' : ModuleCat.{u} (ToType (stalkTensorRing Y y))} (g : N ⟶ N') :
    (ModuleCat.restrictScalars.{u, u, u} e.toRingHom).map
        (((MonoidalCategory.curriedTensor
            (ModuleCat.{u} (ToType (stalkTensorRing Y y)))).obj M).map g) ≫
      (CochainComplex.DerivedTensor.restrictScalarsTensorIso e M N').inv =
    (CochainComplex.DerivedTensor.restrictScalarsTensorIso e M N).inv ≫
      ((CochainComplex.DerivedTensor.moduleTensor.{u, u} R).obj
        ((ModuleCat.restrictScalars.{u, u, u} e.toRingHom).obj M)).map
          ((ModuleCat.restrictScalars.{u, u, u} e.toRingHom).map g) :=
  ModuleCat.hom_ext (LinearMap.toAddMonoidHom_injective
    (tensor_addMonoidHom_ext fun _ _ => rfl))

/-- `stalkOverTensorIso` is natural in its first argument. -/
theorem stalkOverTensorIso_naturality_left {a a' : SheafOfModules.{u} (structureSheafRing Y)}
    (f : a ⟶ a') (b : SheafOfModules.{u} (structureSheafRing Y)) :
    (stalkOver Y y R e).map
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf).map f).app b) ≫
        (stalkOverTensorIso Y y R e a' b).hom =
      (stalkOverTensorIso Y y R e a b).hom ≫
        ((CochainComplex.DerivedTensor.moduleTensor.{u, u} R).map
          ((stalkOver Y y R e).map f)).app ((stalkOver Y y R e).obj b) :=
  comp_square _ _ _ _ _ _ _
    (Functor.map_commSq (ModuleCat.restrictScalars.{u, u, u} e.toRingHom)
      ⟨stalkTensorIso_naturality_left Y y f b⟩).w
    (restrictScalarsTensorIso_inv_naturality_left Y y R e _ _)

/-- `stalkOverTensorIso` is natural in its second argument. -/
theorem stalkOverTensorIso_naturality_right (a : SheafOfModules.{u} (structureSheafRing Y))
    {b b' : SheafOfModules.{u} (structureSheafRing Y)} (g : b ⟶ b') :
    (stalkOver Y y R e).map
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf).obj a).map g) ≫
        (stalkOverTensorIso Y y R e a b').hom =
      (stalkOverTensorIso Y y R e a b).hom ≫
        ((CochainComplex.DerivedTensor.moduleTensor.{u, u} R).obj
          ((stalkOver Y y R e).obj a)).map ((stalkOver Y y R e).map g) :=
  comp_square _ _ _ _ _ _ _
    (Functor.map_commSq (ModuleCat.restrictScalars.{u, u, u} e.toRingHom)
      ⟨stalkTensorIso_naturality_right Y y a g⟩).w
    (restrictScalarsTensorIso_inv_naturality_right Y y R e _ _)

end Generic

variable (X : RingedSpace.{u, u}) (x : X.carrier)

attribute [local instance] stalkCommRing

/-- The germ map of the one-point inclusion `Y = {x} ⟶ X` at its point, as a ring isomorphism
`𝒪_{X,x} ≃ 𝒪_{Y,x}`. -/
abbrev pointGermRingEquiv :
    stalkRing X x ≃+* ToType (TopCat.Presheaf.stalk (C := RingCat.{u})
      (structureSheafRing (pointSpace X x)).obj PUnit.unit) :=
  (asIso (Stacks.RingedSpace.stalkRingMap (pointHom X x) PUnit.unit)).ringCatIsoToRingEquiv

/-- The category of sheaves of modules on the one-point space `Y = {x}`. -/
abbrev PointModules := AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules (pointSpace X x)

/-- The identification `Mod(𝒪_Y) ⥤ Mod(𝒪_{X,x})`: the stalk at the point, read over `𝒪_{X,x}`. -/
abbrev pointStalk : PointModules X x ⥤ ModuleCat.{u} (stalkRing X x) :=
  (pointStalkModulesEquiv X x).functor

/-- The tensor product of `𝒪_{X,x}`-modules, as a bifunctor. -/
abbrev ringTensor := CochainComplex.DerivedTensor.moduleTensor.{u, u} (stalkRing X x)

/-- `Tot(- ⊗_{𝒪_{X,x}} -)`, the total tensor complex over the local ring, as a functor on pairs
of cochain complexes.

Naming it, and deliberately *not* writing out its source and target, is what lets the statement
of `pointStalkTensorComplexIso` elaborate.
`CochainComplex.DerivedTensor.moduleTensor` takes its modules over a `CommRing`, so the `Ring`
instance in the `ModuleCat` of `ringTensor X x` is `CommRing.toRing` applied to `stalkCommRing`,
whereas `ModuleCat.{u} (stalkRing X x)` written by hand — which is how the target of
`pointStalk` is spelled, through `restrictedStalkEquivalence` — carries the `Ring` instance of
the `RingCat`-valued stalk.  The two are definitionally equal; what they are not is
interchangeable under instance synthesis, and that crossing is the one recorded in the
implementation notes of
`StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.AdjunctionUnconditional`.  The
instance arguments of `Stacks.Cohomology.DerivedPullbackTensor.totalComplexPair` are stated over
an abelian category, so applying it in a position where the hand-written spelling is already
fixed asks instance search to match `(ringTensor X x).Additive` across the crossing rather than
to choose it; the `instance_reducible` seat on `Stacks.SheafOfModules.Tensor.ringSheaf` at the
top of this file is what opens the one definition the two spellings differ by at the
transparency instance search runs at, and so what lets that match succeed.  Here the
bifunctor's own spelling settles the instances, and the statement below crosses the two
spellings once, by unification. -/
@[sga "4½ Etat_0 1.3.3" "special case"]
abbrev ringTotalComplexPair :=
  Stacks.Cohomology.DerivedPullbackTensor.totalComplexPair (ringTensor X x)

/-- **The stalk at the point carries the tensor product to the tensor product**:
`(a ⊗_{𝒪_Y} b)_x ≅ a_x ⊗_{𝒪_{X,x}} b_x` for sheaves of modules `a`, `b` on `Y = {x}`. -/
def pointStalkTensorIso (a b : PointModules X x) :
    (pointStalk X x).obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          (pointSpace X x).sheaf).obj a).obj b) ≅
      ((ringTensor X x).obj ((pointStalk X x).obj a)).obj ((pointStalk X x).obj b) :=
  stalkOverTensorIso (pointSpace X x) PUnit.unit (stalkRing X x) (pointGermRingEquiv X x) a b

/-- **The stalk at the point carries the total tensor complex to the total tensor complex**,
naturally in the pair of complexes. -/
def pointStalkTensorComplexIso :
    Stacks.Cohomology.DerivedPullbackTensor.totalComplexPair
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (pointSpace X x).sheaf) ⋙
        (pointStalk X x).mapHomologicalComplex (ComplexShape.up ℤ) ≅
      ((pointStalk X x).mapHomologicalComplex (ComplexShape.up ℤ)).prod
          ((pointStalk X x).mapHomologicalComplex (ComplexShape.up ℤ)) ⋙
        ringTotalComplexPair X x :=
  Stacks.Cohomology.DerivedPullbackTensor.totalComplexPairTransport _ _ (pointStalk X x)
    (pointStalkTensorIso X x)
    (fun u b => stalkOverTensorIso_naturality_left (pointSpace X x) PUnit.unit (stalkRing X x)
      (pointGermRingEquiv X x) u b)
    (fun a _ _ v => stalkOverTensorIso_naturality_right (pointSpace X x) PUnit.unit
      (stalkRing X x) (pointGermRingEquiv X x) a v)

/-- The degreewise stalk of a complex of sheaves of modules on `Y = {x}`, over `𝒪_{X,x}`. -/
abbrev pointStalkComplex :
    CochainComplex (PointModules X x) ℤ ⥤ CochainComplex (ModuleCat.{u} (stalkRing X x)) ℤ :=
  (pointStalk X x).mapHomologicalComplex (ComplexShape.up ℤ)

/-- **The stalk at the point preserves K-flatness.**  An acyclic complex `M` of
`𝒪_{X,x}`-modules is the stalk of an acyclic complex `G` on `Y = {x}`, and `M ⊗ L_x` is then
the stalk of `Tot(G ⊗ L)`, which is acyclic when `L` is K-flat. -/
theorem kFlat_pointStalkComplex (L : CochainComplex (PointModules X x) ℤ)
    (hL : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat (pointSpace X x) L) :
    CochainComplex.KFlat.{u, u} ((pointStalkComplex X x).obj L) := by
  intro M hM
  let E := pointStalkModulesEquiv X x
  let G := (E.inverse.mapHomologicalComplex (ComplexShape.up ℤ)).obj M
  have hG : G.Acyclic := HomologicalComplex.Acyclic.map E.inverse hM
  have h₁ := HomologicalComplex.Acyclic.map E.functor (hL G hG)
  have h₂ := HomologicalComplex.Acyclic.of_iso ((pointStalkTensorComplexIso X x).app (G, L)) h₁
  exact HomologicalComplex.Acyclic.of_iso
    ((ringTotalComplexPair X x).mapIso
      (Iso.prod ((NatIso.mapHomologicalComplex E.counitIso (ComplexShape.up ℤ)).app M ≪≫
        (Functor.mapHomologicalComplexIdIso _ (ComplexShape.up ℤ)).app M) (Iso.refl _))) h₂

/-! ### The comparison on K-flat representatives -/

open Stacks.Cohomology.DerivedPullbackTensor
open Stacks.Cohomology.DerivedInternalHomPullback (pullbackTensorUncurried conjugate_naturality)

/-- The stalk identification `D(𝒪_Y) ⥤ D(𝒪_{X,x})` commutes with the localization functors. -/
abbrev pointStalkFactors :
    DerivedCategory.Q ⋙ (pointStalkDerivedEquiv X x).functor ≅
      pointStalkComplex X x ⋙ DerivedCategory.Q :=
  (pointStalk X x).mapDerivedCategoryFactors

/-- The bifunctor `(K, L) ↦ (K ⊗^L_{𝒪_Y} L)_x` on `D(𝒪_Y) × D(𝒪_Y)`. -/
abbrev stalkOfDerivedTensor :
    DerivedCategory (PointModules X x) × DerivedCategory (PointModules X x) ⥤
      DerivedCategory (ModuleCat.{u} (stalkRing X x)) :=
  pullbackTensorUncurried (pointSpace X x) ⋙ (pointStalkDerivedEquiv X x).functor

/-- The bifunctor `(K, L) ↦ K_x ⊗^L_{𝒪_{X,x}} L_x` on `D(𝒪_Y) × D(𝒪_Y)`. -/
abbrev derivedTensorOfStalks :
    DerivedCategory (PointModules X x) × DerivedCategory (PointModules X x) ⥤
      DerivedCategory (ModuleCat.{u} (stalkRing X x)) :=
  (pointStalkDerivedEquiv X x).functor.prod (pointStalkDerivedEquiv X x).functor ⋙
    (stalkDerivedAdjunction X x).tensor

/-- The bifunctor `(K, L) ↦ Q(Tot(K ⊗_{𝒪_Y} L)_x)` on pairs of cochain complexes. -/
abbrev stalkModelTarget :
    CochainComplex (PointModules X x) ℤ × CochainComplex (PointModules X x) ℤ ⥤
      DerivedCategory (ModuleCat.{u} (stalkRing X x)) :=
  totalComplexPair (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
    (pointSpace X x).sheaf) ⋙
    pointStalkComplex X x ⋙ DerivedCategory.Q

/-- **The left-hand comparison** `(QK ⊗^L QL)_x ⟶ Q(Tot(K ⊗ L)_x)`: the canonical map of
Tag 06YU to the ordinary total tensor complex, followed by the stalk. -/
def stalkLeftComparison :
    DerivedCategory.Q.prod DerivedCategory.Q ⋙ stalkOfDerivedTensor X x ⟶ stalkModelTarget X x :=
  Functor.whiskerRight (derivedToTensorNatTrans (pointSpace X x))
      (pointStalkDerivedEquiv X x).functor ≫
    Functor.whiskerLeft
      (totalComplexPair (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        (pointSpace X x).sheaf))
      (pointStalkFactors X x).hom

/-- On a pair of K-flat complexes the left-hand comparison is invertible. -/
theorem isIso_stalkLeftComparison_app (K L : CochainComplex (PointModules X x) ℤ)
    (hK : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat (pointSpace X x) K)
    (hL : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat (pointSpace X x) L) :
    IsIso ((stalkLeftComparison X x).app (K, L)) := by
  dsimp only [stalkLeftComparison, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, derivedToTensorNatTrans]
  rw [(Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct
    (pointSpace X x).sheaf).toTensor_eq_comparison K L hK hL]
  exact IsIso.comp_isIso' (@Functor.map_isIso _ _ _ _ _ _ _ _ (Iso.isIso_hom _))
    (Iso.isIso_hom ((pointStalkFactors X x).app _))

/-- **The right-hand comparison on a pair whose second complex is K-flat**,
`QK_x ⊗^L QL_x ≅ Q(Tot(K ⊗ L)_x)`: the K-flat comparison over `𝒪_{X,x}`, the stalk being
K-flat, followed by the comparison of total tensor complexes. -/
def stalkRightComparisonIso (K L : CochainComplex (PointModules X x) ℤ)
    (hL : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat (pointSpace X x) L) :
    (DerivedCategory.Q.prod DerivedCategory.Q ⋙ derivedTensorOfStalks X x).obj (K, L) ≅
      (stalkModelTarget X x).obj (K, L) :=
  (stalkDerivedAdjunction X x).tensor.mapIso
      (Iso.prod ((pointStalkFactors X x).app K) ((pointStalkFactors X x).app L)) ≪≫
    CochainComplex.DerivedTensor.derivedTensor_comparison.{u, u} (stalkRing X x) _ _
      (kFlat_pointStalkComplex X x L hL) ≪≫
    DerivedCategory.Q.mapIso ((pointStalkTensorComplexIso X x).app (K, L)).symm

/-- Three commuting squares paste to a commuting square. -/
theorem comp_square_three {C : Type*} [Category C] {A₀ A₁ A₂ A₃ B₀ B₁ B₂ B₃ : C}
    {m₀ : A₀ ⟶ B₀} {m₁ : A₁ ⟶ B₁} {m₂ : A₂ ⟶ B₂} {m₃ : A₃ ⟶ B₃}
    {a₁ : A₀ ⟶ A₁} {a₂ : A₁ ⟶ A₂} {a₃ : A₂ ⟶ A₃}
    {b₁ : B₀ ⟶ B₁} {b₂ : B₁ ⟶ B₂} {b₃ : B₂ ⟶ B₃}
    (h₁ : m₀ ≫ b₁ = a₁ ≫ m₁) (h₂ : m₁ ≫ b₂ = a₂ ≫ m₂) (h₃ : m₂ ≫ b₃ = a₃ ≫ m₃) :
    m₀ ≫ (b₁ ≫ (b₂ ≫ b₃)) = (a₁ ≫ (a₂ ≫ a₃)) ≫ m₃ := by
  simp only [Category.assoc]
  rw [reassoc_of% h₁, reassoc_of% h₂, h₃]

/-- The right-hand comparison is natural in cochain maps, the second complexes being K-flat. -/
theorem stalkRightComparisonIso_naturality {K K' L L' : CochainComplex (PointModules X x) ℤ}
    (a : K ⟶ K') (b : L ⟶ L')
    (hL : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat (pointSpace X x) L)
    (hL' : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat (pointSpace X x) L') :
    (DerivedCategory.Q.prod DerivedCategory.Q ⋙ derivedTensorOfStalks X x).map (a ×ₘ b) ≫
        (stalkRightComparisonIso X x K' L' hL').hom =
      (stalkRightComparisonIso X x K L hL).hom ≫ (stalkModelTarget X x).map (a ×ₘ b) := by
  let T := (stalkDerivedAdjunction X x).tensor
  let φ := (pointStalkFactors X x).hom
  have h₁ : T.map (CategoryTheory.Prod.mkHom
        ((DerivedCategory.Q ⋙ (pointStalkDerivedEquiv X x).functor).map a)
        ((DerivedCategory.Q ⋙ (pointStalkDerivedEquiv X x).functor).map b)) ≫
        T.map (CategoryTheory.Prod.mkHom (φ.app K') (φ.app L')) =
      T.map (CategoryTheory.Prod.mkHom (φ.app K) (φ.app L)) ≫
        T.map (CategoryTheory.Prod.mkHom
          ((pointStalkComplex X x ⋙ DerivedCategory.Q).map a)
          ((pointStalkComplex X x ⋙ DerivedCategory.Q).map b)) := by
    rw [← T.map_comp, ← T.map_comp]
    exact congrArg T.map (Prod.ext (φ.naturality a) (φ.naturality b))
  have h₂ := CochainComplex.DerivedTensor.derivedTensor_comparison_naturality.{u, u}
    (stalkRing X x) ((pointStalkComplex X x).map a) ((pointStalkComplex X x).map b)
    (kFlat_pointStalkComplex X x L hL) (kFlat_pointStalkComplex X x L' hL')
  have n := (pointStalkTensorComplexIso X x).inv.naturality (a ×ₘ b)
  have n' := (congrArg (· ≫ (pointStalkTensorComplexIso X x).inv.app (K', L'))
    (totalComplexPair_map (ringTensor X x) ((pointStalkComplex X x).map a)
      ((pointStalkComplex X x).map b)).symm).trans n
  have h₃ := (DerivedCategory.Q.map_comp _ _).symm.trans
    ((congrArg DerivedCategory.Q.map n').trans (DerivedCategory.Q.map_comp _ _))
  have key := comp_square_three h₁ h₂ h₃
  refine Eq.trans ?l (key.trans ?r)
  · rfl
  · rfl


/-- **The comparison on a pair of K-flat representatives**,
`(QK ⊗^L QL)_x ≅ QK_x ⊗^L QL_x`: both comparisons into `Q(Tot(K ⊗ L)_x)` are invertible there. -/
def stalkModelComparison (K L : CochainComplex (PointModules X x) ℤ)
    (hK : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat (pointSpace X x) K)
    (hL : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat (pointSpace X x) L) :
    (stalkOfDerivedTensor X x).obj (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L) ≅
      (derivedTensorOfStalks X x).obj (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L) :=
  haveI := isIso_stalkLeftComparison_app X x K L hK hL
  asIso ((stalkLeftComparison X x).app (K, L)) ≪≫ (stalkRightComparisonIso X x K L hL).symm

/-- The comparison on K-flat representatives is natural in cochain maps between them. -/
theorem stalkModelComparison_naturality {K K' L L' : CochainComplex (PointModules X x) ℤ}
    (a : K ⟶ K') (b : L ⟶ L')
    (hK : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat (pointSpace X x) K)
    (hK' : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat (pointSpace X x) K')
    (hL : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat (pointSpace X x) L)
    (hL' : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat (pointSpace X x) L') :
    (stalkOfDerivedTensor X x).map (DerivedCategory.Q.map a ×ₘ DerivedCategory.Q.map b) ≫
        (stalkModelComparison X x K' L' hK' hL').hom =
      (stalkModelComparison X x K L hK hL).hom ≫
        (derivedTensorOfStalks X x).map (DerivedCategory.Q.map a ×ₘ DerivedCategory.Q.map b) :=
  haveI := isIso_stalkLeftComparison_app X x K L hK hL
  haveI := isIso_stalkLeftComparison_app X x K' L' hK' hL'
  Stacks.Cohomology.DerivedInternalHomPullback.conjugate_comparison _ _ _ _ _ _ _
    ((stalkLeftComparison X x).naturality (a ×ₘ b))
    (stalkRightComparisonIso_naturality X x a b hL hL')

/-! ### Descent along the K-flat localization -/

/-- **The comparison on K-flat representatives, as an isomorphism of functors** on pairs of
K-flat objects of the homotopy category of `𝒪_Y`-modules. -/
def stalkModelsComparison :
    kFlatQPair (Y := pointSpace X x) ⋙ stalkOfDerivedTensor X x ≅
      kFlatQPair (Y := pointSpace X x) ⋙ derivedTensorOfStalks X x :=
  NatIso.ofComponents
    (fun M => (stalkOfDerivedTensor X x).mapIso (kFlatQPairIso M) ≪≫
      stalkModelComparison X x M.1.obj.as M.2.obj.as M.1.property M.2.property ≪≫
        ((derivedTensorOfStalks X x).mapIso (kFlatQPairIso M)).symm)
    (fun {M N} g => by
      refine conjugate_naturality _ _ (kFlatQPairIso M) (kFlatQPairIso N)
        (stalkModelComparison X x M.1.obj.as M.2.obj.as M.1.property M.2.property)
        (stalkModelComparison X x N.1.obj.as N.2.obj.as N.1.property N.2.property)
        ((kFlatQPair (Y := pointSpace X x)).map g) _ (kFlatQPairIso_naturality g) ?_
      exact stalkModelComparison_naturality X x g.1.hom.out g.2.hom.out
        M.1.property N.1.property M.2.property N.2.property)

attribute [local instance] kFlatQPair_isLocalization

/-- **The stalk at `x` is monoidal on the one-point space**: the isomorphism of bifunctors

`(K ⊗^L_{𝒪_Y} L)_x ≅ K_x ⊗^L_{𝒪_{X,x}} L_x`

on `D(𝒪_Y) × D(𝒪_Y)`, for `Y = {x}` the one-point ringed space with structure sheaf `𝒪_{X,x}`,
the derived tensor product on the left being that of Tag 079U and the one on the right that of
the tensor–hom adjunction of Tag 0A63 over `𝒪_{X,x}`. -/
def stalkDerivedTensorIso : stalkOfDerivedTensor X x ≅ derivedTensorOfStalks X x :=
  Localization.liftNatIso (kFlatQPair (Y := pointSpace X x))
    (kFlatQuasiIsoPair (Y := pointSpace X x)) _ _ _ _ (stalkModelsComparison X x)

/-- **The stalk identification carries the derived tensor product of `Y = {x}` to the derived
tensor product over `𝒪_{X,x}`**, at the derived tensor product the derived internal hom of `Y`
is stated at. -/
def pointStalkInternalHomTensorIso :
    Stacks.Cohomology.DerivedInternalHomPullback.internalHomTensorUncurried (pointSpace X x) ⋙
        (pointStalkDerivedEquiv X x).functor ≅
      (pointStalkDerivedEquiv X x).functor.prod (pointStalkDerivedEquiv X x).functor ⋙
        (stalkDerivedAdjunction X x).tensor :=
  Functor.isoWhiskerRight
      (Stacks.Cohomology.DerivedInternalHomPullback.tensorBridge (pointSpace X x)).symm
      (pointStalkDerivedEquiv X x).functor ≪≫
    stalkDerivedTensorIso X x

/-- **`pointStalkDerivedEquiv` carries the derived internal hom of `Y = {x}` to `RHom` over
`𝒪_{X,x}`**: the internal hom of the tensor–hom adjunction of Tag 0A63. -/
def pointStalkInternalHomComparison : PointStalkInternalHomComparison X x :=
  pointStalkInternalHomComparisonOfTensorIso X x (pointStalkInternalHomTensorIso X x)

/-- **The point `x` presented as the one-point ringed space `Y = {x}` over `X`**, for an arbitrary
ringed space and an arbitrary point. -/
def pointStalkPresentation : StalkPresentation X x :=
  stalkPresentationOfInternalHomComparison X x (pointStalkInternalHomComparison X x)

end Stacks.Cohomology.DerivedInternalHomStalk

end
