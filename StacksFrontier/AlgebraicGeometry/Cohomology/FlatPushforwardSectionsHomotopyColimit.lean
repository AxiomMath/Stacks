module

public import StacksFrontier.AlgebraicGeometry.Cohomology.FlatPushforwardHomotopyColimit
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.AffineOpenDerivedStalk
public import StacksFrontier.AlgebraicGeometry.DerivedGlobalSectionsOverLeray
public import StacksFrontier.AlgebraicGeometry.ProperSupportCoherent.ExtFinitenessLeray
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.AffineDerivedEquivalence
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.SupportedSectionsDirectSums
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormulaQCoh
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormulaQCohCoproducts
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.DerivedTensorReseat
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PseudoCoherentThree.TwistedFourierMukai
import StacksCore.Tactic.StacksAttribute

/-!
# [Stacks, Tag 0CRR]: `RΓ(U, Lf^* K)` as a derived colimit of perfect twists of `K`

Let `A` be a ring, `X` a scheme of finite presentation over `A` and `f : U ⟶ X` a flat morphism
of finite presentation. [Stacks, Tag 0CRR] asserts:

1. there is an inverse system of perfect objects `Lₙ` of `D(𝒪_X)` with
   `RΓ(U, Lf^* K) = hocolim RHom_X(Lₙ, K)` in `D(A)`, functorially in `K` in `D_QCoh(𝒪_X)`;
2. there is a system of perfect objects `Eₙ` of `D(𝒪_X)` with
   `RΓ(U, Lf^* K) = hocolim RΓ(X, Eₙ ⊗^𝐋 K)` in `D(A)`, functorially in `K` in `D_QCoh(𝒪_X)`.

## The proof

The source's. `RΓ(U, Lf^* K) = RΓ(X, Rf_* 𝒪_U ⊗^𝐋 K)` functorially in `K`, by the projection
formula ([Stacks, Tag 08EU]) and Leray (`flatPushforwardSectionsComparison`,
`isIso_flatPushforwardSectionsComparison_app`). `Rf_* 𝒪_U = hocolim Eₙ` with `Eₙ` perfect
(`Stacks.Cohomology.CountableSections.exists_isHomotopyColimitWith_derivedPushforward_unit`, which
carries Tags 01ZM, 04AI, 08IB, 0CRQ and 0CRP). `- ⊗^𝐋 K` is exact and commutes with direct sums,
and `RΓ(X, -)` is exact and commutes with direct sums of objects of `D_QCoh(𝒪_X)`
([Stacks, Tag 08DZ], `preservesColimit_derivedGlobalSectionsOver_of_isQuasicoherent`), so both
carry derived colimits to derived colimits.

## Main results

* `exists_isHomotopyColimitWith_derivedGlobalSectionsOver_derivedTensor`:
  **[Stacks, Tag 0CRR] (2)**.

## Implementation notes

"Functorially in `K`" is read as: one system `E` for every `K`, and coprojections
`RΓ(X, K ⊗^𝐋 Eₙ) ⟶ RΓ(U, Lf^* K)` which are the components at `K` of natural transformations
compatible with the transitions. The tensor is written `K ⊗^𝐋 Eₙ`, the source writes
`Eₙ ⊗^𝐋 K`; the two agree by the symmetry of `⊗^𝐋`.

The projection formula, Tor independent base change and the Leray isomorphism exist in this
repository only at `HasDerivedCategory.standard`, so the declarations which use them are stated
there, with the model scoped to each declaration.

## References

* [Stacks Project, Tag 0CRR](https://stacks.math.columbia.edu/tag/0CRR)
* [Stacks Project, Tag 08EU](https://stacks.math.columbia.edu/tag/08EU)
* [Stacks Project, Tag 08DZ](https://stacks.math.columbia.edu/tag/08DZ)
* [Stacks Project, Tag 08DQ](https://stacks.math.columbia.edu/tag/08DQ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open CategoryTheory.Pretriangulated

universe w u

namespace Stacks.Cohomology.CountableSections

attribute [local instance 10000] HasDerivedCategory.standard in
/-- `RΓ_A(X, -)` commutes with direct sums of objects of `D_QCoh(𝒪_X)`. -/
theorem preservesColimitsOfShape_discrete_ι_comp_derivedGlobalSectionsOver {A : Type u}
    [CommRing A] {X : Scheme.{u}} (p : X ⟶ Spec (.of A)) [QuasiCompact p] [QuasiSeparated p]
    (I : Type u) :
    PreservesColimitsOfShape (Discrete I)
      ((DerivedCategoryB.derivedCategoryB (A := X.Modules)
        (SheafOfModules.isQuasicoherent X.ringCatSheaf)).ι ⋙ derivedGlobalSectionsOver p) := by
  have h08DZ : PreservesColimitsOfShape (Discrete I)
      (Stacks.Cohomology.SupportedComplexes.derivedPushforwardQuasicoherent p) :=
    Duality.DerivedPushforward.preservesColimitsOfShape_discrete_qcqsQuasiCoherentDerivedPushforward
      p I
  have := derivedGlobalSectionsQuasicoherent_isEquivalence (CommRingCat.of A)
  have hΓ : PreservesColimitsOfShape (Discrete I)
      (derivedGlobalSectionsQuasicoherent (CommRingCat.of A)) := inferInstance
  let RPq : (DerivedCategoryB.derivedCategoryB (A := X.Modules)
        (SheafOfModules.isQuasicoherent X.ringCatSheaf)).FullSubcategory ⥤
      (DerivedCategoryB.derivedCategoryB (A := (Spec (CommRingCat.of A)).Modules)
        (SheafOfModules.isQuasicoherent (Spec (CommRingCat.of A)).ringCatSheaf)).FullSubcategory :=
    Stacks.Cohomology.SupportedComplexes.derivedPushforwardQuasicoherent p
  have h08DZ' : PreservesColimitsOfShape (Discrete I) RPq := h08DZ
  let ΓQ := derivedGlobalSectionsQuasicoherent (CommRingCat.of A)
  have hcomp : PreservesColimitsOfShape (Discrete I) (RPq ⋙ ΓQ) := inferInstance
  let e : (DerivedCategoryB.derivedCategoryB (A := X.Modules)
        (SheafOfModules.isQuasicoherent X.ringCatSheaf)).ι ⋙ derivedGlobalSectionsOver p ≅
      RPq ⋙ ΓQ :=
    Functor.isoWhiskerLeft _ (derivedGlobalSectionsOverPushforwardIso p)
  exact preservesColimitsOfShape_of_natIso e.symm

/-! ### Coprojections of a derived colimit are compatible with the transitions -/

/-- The coprojections of a derived colimit are compatible with the transition maps of the
system: `fₙ ≫ cₙ₊₁ = cₙ`, read off the vanishing of the composite of the first two maps of the
defining triangle. -/
theorem _root_.CategoryTheory.Pretriangulated.IsHomotopyColimitWith.map_comp_coprojection
    {D : Type*} [Category D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    {F : ℕ ⥤ D} [HasCoproduct F.obj] {K : D} {c : ∀ n, F.obj n ⟶ K}
    (h : IsHomotopyColimitWith F K c) (n : ℕ) :
    F.map (homOfLE (Nat.le_succ n)) ≫ c (n + 1) = c n := by
  obtain ⟨p, q, hT, hc⟩ := h
  have h1 := congrArg (fun φ => Limits.Sigma.ι F.obj n ≫ φ) (comp_distTriang_mor_zero₁₂ _ hT)
  simp only [Triangle.mk_obj₁, Triangle.mk_mor₁, Triangle.mk_mor₂, comp_zero] at h1
  rw [← Category.assoc, Limits.Sigma.ι_comp_desc, Preadditive.sub_comp, sub_eq_zero,
    Category.assoc] at h1
  rw [← hc n, ← hc (n + 1), h1]

/-! ### Direct sums of quasi-coherent families -/

attribute [local instance 10000] HasDerivedCategory.standard in
/-- `RΓ_A(X, -)` preserves the direct sum of a sequence of objects of `D(𝒪_X)` with
quasi-coherent cohomology sheaves, for `X ⟶ Spec A` quasi-compact and quasi-separated. -/
theorem preservesColimit_derivedGlobalSectionsOver_of_isQuasicoherent {A : Type u} [CommRing A]
    {X : Scheme.{u}} (p : X ⟶ Spec (.of A)) [QuasiCompact p] [QuasiSeparated p]
    (K : ℕ → DerivedCategory X.Modules)
    (hK : ∀ n i, ((DerivedCategory.homologyFunctor X.Modules i).obj (K n)).IsQuasicoherent) :
    PreservesColimit (Discrete.functor K) (derivedGlobalSectionsOver p) := by
  let P := DerivedCategoryB.derivedCategoryB (A := X.Modules)
    (SheafOfModules.isQuasicoherent X.ringCatSheaf)
  have hU := preservesColimitsOfShape_discrete_ι_comp_derivedGlobalSectionsOver p (ULift.{u} ℕ)
  have hN : PreservesColimitsOfShape (Discrete ℕ) (P.ι ⋙ derivedGlobalSectionsOver p) :=
    preservesColimitsOfShape_of_equiv (Discrete.equivalence Equiv.ulift) _
  -- the direct sum of the family lies in `D_QCoh(𝒪_X)`
  have hsum : P (∐ K) := fun i =>
    Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_of_isColimit
      (fun k => hK k.as i)
      (isColimitOfPreserves (DerivedCategory.homologyFunctor X.Modules i)
        (colimit.isColimit (Discrete.functor K)))
  let D' : Discrete ℕ ⥤ P.FullSubcategory := P.lift (Discrete.functor K) fun n => hK n.as
  let c : Cocone D' :=
    { pt := ⟨∐ K, hsum⟩
      ι := Discrete.natTrans fun n => ObjectProperty.homMk (Limits.Sigma.ι K n.as) }
  have hι : IsColimit (P.ι.mapCocone c) :=
    (colimit.isColimit (Discrete.functor K)).ofIsoColimit (Cocone.ext (Iso.refl _) fun n => by
      simp [c])
  exact preservesColimit_of_preserves_colimit_cocone (colimit.isColimit (Discrete.functor K))
    ((isColimitOfPreserves (P.ι ⋙ derivedGlobalSectionsOver p)
      (isColimitOfReflects P.ι hι)).ofIsoColimit (Cocone.ext (Iso.refl _) fun n => by simp [c]))

/-! ### The comparison `RΓ(X, M ⊗^L Rf_* 𝒪_U) ⟶ RΓ(U, Lf^* M)` -/

section Comparison

variable {A : Type u} [CommRing A] {X U : Scheme.{u}} (p : X ⟶ Spec (.of A)) (f : U ⟶ X)

attribute [local instance 10000] HasDerivedCategory.standard in
/-- The symmetry `M ⊗^L N ≅ N ⊗^L M` of the derived tensor product of [Stacks, Tag 06YU] on a
scheme, natural in `M`, read off the symmetric monoidal structure of [Stacks, Tag 0FPT]. At
`HasDerivedCategory.standard`, scoped to this declaration, to match the model of the projection
formula. -/
def derivedTensorFlipObjIso (Y : Scheme.{u})
    (N : Stacks.DerivedTensor.RingedSite.DerivedModules Y.toRingedSpace.sheaf) :
    (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.toRingedSpace.sheaf).flip.obj N ≅
      (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.toRingedSpace.sheaf).obj N :=
  letI := Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal Y.toRingedSpace.sheaf
  letI := Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedSymmetric Y.toRingedSpace.sheaf
  have h : Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.toRingedSpace.sheaf =
      MonoidalCategory.curriedTensor _ :=
    (Stacks.SheafOfModules.DerivedMonoidal.curriedTensor_canonicalDerivedMonoidal _).symm
  eqToIso (by rw [h]) ≪≫ (BraidedCategory.tensorLeftIsoTensorRight
    (C := Stacks.DerivedTensor.RingedSite.DerivedModules Y.toRingedSpace.sheaf) N).symm ≪≫
    eqToIso (by rw [h])

attribute [local instance 10000] HasDerivedCategory.standard in
/-- The unit constraint `𝒪_Y ⊗^L M ≅ M` of the derived tensor product on a scheme, natural in
`M`. At `HasDerivedCategory.standard`, scoped to this declaration. -/
def derivedTensorUnitLeftIso (Y : Scheme.{u}) :
    (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.toRingedSpace.sheaf).obj
        (derivedUnitObject Y) ≅ 𝟭 _ :=
  letI := Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal Y.toRingedSpace.sheaf
  have h : Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.toRingedSpace.sheaf =
      MonoidalCategory.curriedTensor _ :=
    (Stacks.SheafOfModules.DerivedMonoidal.curriedTensor_canonicalDerivedMonoidal _).symm
  have hu : derivedUnitObject Y = MonoidalCategory.tensorUnit
      (Stacks.DerivedTensor.RingedSite.DerivedModules Y.toRingedSpace.sheaf) :=
    (Stacks.SheafOfModules.DerivedMonoidal.tensorUnit_canonicalDerivedMonoidal _).symm
  eqToIso (by rw [h, hu]) ≪≫ MonoidalCategory.leftUnitorNatIso
    (Stacks.DerivedTensor.RingedSite.DerivedModules Y.toRingedSpace.sheaf)

attribute [local instance 10000] HasDerivedCategory.standard in
/-- The projection-formula map `Rf_* E ⊗^L M ⟶ Rf_*(E ⊗^L Lf^* M)` of [Stacks, Tag 0B53] as a
natural transformation in `M`. At `HasDerivedCategory.standard`, the model of the projection
formula, scoped to this declaration. -/
def projectionFormulaNatTrans (E : DerivedCategory U.Modules) :
    (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.toRingedSpace.sheaf).obj
        ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward
          f.toLRSHom.toShHom).obj E) ⟶
      Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f.toLRSHom.toShHom ⋙
        (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor U.toRingedSpace.sheaf).obj E ⋙
          Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward
            f.toLRSHom.toShHom where
  app M := Stacks.Cohomology.DerivedProjectionFormula.projectionFormulaMap f.toLRSHom.toShHom E M
  naturality _ _ k :=
    Stacks.Cohomology.DerivedProjectionFormula.projectionFormulaMap_natural_right
      f.toLRSHom.toShHom E k

/-- A morphism `f ≫ p` lies over `Spec A` along the identity of `A`. -/
theorem comp_eq_comp_specMap_id :
    f ≫ p = (f ≫ p) ≫ Spec.map (CommRingCat.ofHom (RingHom.id A)) := by
  rw [show CommRingCat.ofHom (RingHom.id A) = 𝟙 (CommRingCat.of A) from rfl, Spec.map_id,
    Category.comp_id]

attribute [local instance 10000] HasDerivedCategory.standard in
/-- **Leray over the base ring**, `RΓ_A(X, Rf_* -) ≅ RΓ_A(U, -)`: the linear Leray identification
`AlgebraicGeometry.derivedGlobalSectionsOverDerivedPushforwardRestrictScalarsIso` along the
identity of `A`, followed by the identification of restriction of scalars along the identity with
the identity functor. At `HasDerivedCategory.standard`, scoped to this declaration, the model of
the derived pushforward. -/
def derivedGlobalSectionsOverLerayIdIso :
    Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward f.toLRSHom.toShHom ⋙
        derivedGlobalSectionsOver p ≅
      derivedGlobalSectionsOver (f ≫ p) :=
  derivedGlobalSectionsOverDerivedPushforwardRestrictScalarsIso f p (f ≫ p) (RingHom.id A)
      (comp_eq_comp_specMap_id p f) ≪≫
    Functor.isoWhiskerLeft (derivedGlobalSectionsOver (f ≫ p))
      (restrictScalarsIdDerivedIso (RingHom.id A) rfl).symm ≪≫ Functor.rightUnitor _

attribute [local instance 10000] HasDerivedCategory.standard in
/-- **The comparison `RΓ(X, M ⊗^L Rf_* 𝒪_U) ⟶ RΓ(U, Lf^* M)`, natural in `M`**: the symmetry of
`⊗^L`, the projection-formula map `Rf_* 𝒪_U ⊗^L M ⟶ Rf_*(𝒪_U ⊗^L Lf^* M)` of
[Stacks, Tag 0B53], the unit constraint, and the Leray isomorphism
`RΓ(X, Rf_* -) ≅ RΓ(U, -)` (`derivedGlobalSectionsOverLerayIdIso`). It is invertible at every
`M` with quasi-coherent cohomology by [Stacks, Tag 08EU]
(`isIso_flatPushforwardSectionsComparison_app`).

Stated at `HasDerivedCategory.standard`, scoped to this declaration: the projection formula and
the Leray isomorphism exist only at that model. -/
def flatPushforwardSectionsComparison :
    (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.toRingedSpace.sheaf).flip.obj
        ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward
          f.toLRSHom.toShHom).obj (derivedUnitObject U)) ⋙ derivedGlobalSectionsOver p ⟶
      Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f.toLRSHom.toShHom ⋙
        derivedGlobalSectionsOver (f ≫ p) :=
  Functor.whiskerRight (derivedTensorFlipObjIso X _).hom _ ≫
    Functor.whiskerRight (projectionFormulaNatTrans f (derivedUnitObject U)) _ ≫
    Functor.whiskerRight (Functor.whiskerLeft
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f.toLRSHom.toShHom)
      (Functor.whiskerRight (derivedTensorUnitLeftIso U).hom
        (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward
          f.toLRSHom.toShHom))) _ ≫
    Functor.whiskerLeft
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f.toLRSHom.toShHom)
      (derivedGlobalSectionsOverLerayIdIso p f).hom

attribute [local instance 10000] HasDerivedCategory.standard in
/-- The comparison `RΓ(X, M ⊗^L Rf_* 𝒪_U) ⟶ RΓ(U, Lf^* M)` is invertible at every `M` with
quasi-coherent cohomology, for `f` quasi-compact and quasi-separated: the projection formula of
[Stacks, Tag 08EU]. At `HasDerivedCategory.standard`. -/
theorem isIso_flatPushforwardSectionsComparison_app [QuasiCompact f] [QuasiSeparated f]
    (M : DerivedCategory X.Modules)
    (hM : ∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj M).IsQuasicoherent) :
    IsIso ((flatPushforwardSectionsComparison p f).app M) := by
  have hPF : IsIso ((projectionFormulaNatTrans f (derivedUnitObject U)).app M) :=
    Stacks.Cohomology.ProjectionFormulaQCoh.projectionFormulaMap_isIso_of_isQuasicoherent_homology
      f inferInstance inferInstance _ M (isQuasicoherent_homology_derivedUnitObject U) hM
  let e := (derivedGlobalSectionsOver p).mapIso ((derivedTensorFlipObjIso X _).app M) ≪≫
    (derivedGlobalSectionsOver p).mapIso
      (@asIso _ _ _ _ ((projectionFormulaNatTrans f (derivedUnitObject U)).app M) hPF) ≪≫
    (derivedGlobalSectionsOver p).mapIso
      ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward
        f.toLRSHom.toShHom).mapIso ((derivedTensorUnitLeftIso U).app
          ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
            f.toLRSHom.toShHom).obj M))) ≪≫
    (derivedGlobalSectionsOverLerayIdIso p f).app
      ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        f.toLRSHom.toShHom).obj M)
  exact e.isIso_hom

end Comparison

/-! ### [Stacks, Tag 0CRR] (2) -/

section Tag

variable {A : Type u} [CommRing A] {X U : Scheme.{u}} (p : X ⟶ Spec (.of A)) (f : U ⟶ X)

attribute [local instance 10000] HasDerivedCategory.standard in
/-- **[Stacks, Tag 0CRR] (2).** Let `A` be a ring, `X` a scheme of finite presentation over `A`
and `f : U ⟶ X` a flat morphism of finite presentation. Then there is a system `E : ℕ ⥤ D(𝒪_X)`
of perfect objects such that

`RΓ(U, Lf^* K) = hocolim RΓ(X, K ⊗^𝐋 Eₙ)`

in `D(A)`, functorially in `K` in `D_QCoh(𝒪_X)`: there are maps
`cₙ : RΓ(X, - ⊗^𝐋 Eₙ) ⟶ RΓ(U, Lf^* -)`, natural in `K` and compatible with the transitions of the
system, which for every `K` with quasi-coherent cohomology are the coprojections of a derived
colimit. One system `E` serves every `K`.

`RΓ(X, -)` and `RΓ(U, -)` are the `A`-linear derived global sections along `X ⟶ Spec A` and
`U ⟶ X ⟶ Spec A`, `⊗^𝐋` is the derived tensor product of [Stacks, Tag 06YU], `Lf^*` the derived
pullback of [Stacks, Tag 06YJ], and `hocolim` the derived colimit of [Stacks, Tag 090Z].

Stated at `HasDerivedCategory.standard`, scoped to this declaration: the projection formula
([Stacks, Tag 08EU]), Tor independent base change ([Stacks, Tag 08IB]) and the Leray isomorphism
exist only at that model. -/
@[stacks 0CRR "(2)"]
theorem exists_isHomotopyColimitWith_derivedGlobalSectionsOver_derivedTensor
    [LocallyOfFinitePresentation p] [QuasiCompact p] [QuasiSeparated p]
    [Flat f] [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f] :
    ∃ (E : ℕ ⥤ DerivedCategory X.Modules)
      (c : ∀ n, (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor
          X.toRingedSpace.sheaf).flip.obj (E.obj n) ⋙ derivedGlobalSectionsOver p ⟶
        Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f.toLRSHom.toShHom ⋙
          derivedGlobalSectionsOver (f ≫ p)),
      (∀ n, Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) (E.obj n)) ∧
      (∀ n, Functor.whiskerRight ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor
          X.toRingedSpace.sheaf).flip.map (E.map (homOfLE (Nat.le_succ n))))
          (derivedGlobalSectionsOver p) ≫ c (n + 1) = c n) ∧
      ∀ K : DerivedCategory X.Modules,
        (∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj K).IsQuasicoherent) →
        IsHomotopyColimitWith
          (E ⋙ (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor
            X.toRingedSpace.sheaf).obj K ⋙ derivedGlobalSectionsOver p)
          ((derivedGlobalSectionsOver (f ≫ p)).obj
            ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
              f.toLRSHom.toShHom).obj K))
          (fun n => (c n).app K) := by
  let T := Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.toRingedSpace.sheaf
  obtain ⟨E, c₀, hEp, hc⟩ := exists_isHomotopyColimitWith_derivedPushforward_unit p f
  refine ⟨E, fun n => Functor.whiskerRight (T.flip.map (c₀ n)) _ ≫
    flatPushforwardSectionsComparison p f, hEp, fun n => ?_, fun K hK => ?_⟩
  · rw [← Category.assoc]
    congr 1
    ext M
    have h1 : (T.obj M).map (E.map (homOfLE (Nat.le_succ n))) ≫ (T.obj M).map (c₀ (n + 1)) =
        (T.obj M).map (c₀ n) :=
      ((T.obj M).map_comp _ _).symm.trans (congrArg (T.obj M).map (hc.map_comp_coprojection n))
    exact ((derivedGlobalSectionsOver p).map_comp _ _).symm.trans
      (congrArg (derivedGlobalSectionsOver p).map h1)
  · -- `K ⊗^𝐋 -` carries the derived colimit `Rf_* 𝒪_U = hocolim Eₙ` to a derived colimit
    let TK : DerivedCategory X.Modules ⥤ DerivedCategory X.Modules := T.obj K
    let : TK.CommShift ℤ :=
      (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct _).commShift_right K
    have : TK.IsTriangulated :=
      (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct _).exact_right K
    have : PreservesColimitsOfShape (Discrete (ULift.{u} ℕ)) TK :=
      Stacks.DerivedTensor.RingedSite.preservesColimitsOfShape_discrete_derivedTensorProductFunctor
        _ (ULift.{u} ℕ) K
    have : PreservesColimitsOfShape (Discrete ℕ) TK :=
      preservesColimitsOfShape_of_equiv (Discrete.equivalence Equiv.ulift) _
    -- `RΓ(X, -)` carries it to a derived colimit, the terms lying in `D_QCoh(𝒪_X)`
    have hq : ∀ n i, ((DerivedCategory.homologyFunctor X.Modules i).obj
        (TK.obj (E.obj n))).IsQuasicoherent := fun n i =>
      Stacks.Cohomology.ProjectionFormulaQCohCoproducts.isDQCoh_derivedTensor_obj X K (E.obj n)
        hK (fun j => PerfectApproximation.isQuasicoherent_homology_of_isPerfect X _ (hEp n) j) i
    have : PreservesColimit (Discrete.functor (E ⋙ TK).obj) (derivedGlobalSectionsOver p) :=
      preservesColimit_derivedGlobalSectionsOver_of_isQuasicoherent p _ hq
    have hiso := isIso_flatPushforwardSectionsComparison_app p f K hK
    exact (((hc.map TK).map (derivedGlobalSectionsOver p)).of_iso
      (asIso ((flatPushforwardSectionsComparison p f).app K))).congr_coprojections fun n => rfl

end Tag

end Stacks.Cohomology.CountableSections

end
