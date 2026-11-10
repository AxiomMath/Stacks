module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.DimensionZeroSectionsCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.FrobeniusExtensionCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ProperCompactSupportComparison
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportSheafExcisionIso
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.PullbackStalkFrobenius
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricFrobeniusClosedPoint
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LocalInvariantsInjectionInputs
public import StacksFrontier.AlgebraicGeometry.ProperSectionsGeom.FiniteReducedEtale
public import StacksFrontier.AlgebraicGeometry.Limits.NoetherianValuativeCriterion.Separatedness

/-!
# The stalk at a closed point of `Z` inside `H⁰_c(X_k̄, i_* i⁻¹ -)`

Let `X` be separated of finite type over a finite field `k` with `q = p ^ n` elements, with a
compactification `j`, `i : Z ⟶ X` a closed immersion with `Z` reduced and finite over `k`, and
`y = i(z)` a point of `Z`, with residue field `κ(y)` of degree `d` over `k`. For a sheaf `G` of
`Λ`-modules on `X_étale` the stalk of `G` at the geometric point over `y` embeds into
`H⁰_c(X_k̄, i_* i⁻¹ G)`, naturally in `G`, carrying the geometric Frobenius of `κ(y)` to
`(π_X^*) ^ d`.

The chain of identifications, with `k' = κ(y)`, `Y = Z` over `k` and `Y' = Z ×_k k'` over `k'`:

* `H⁰_c(X_k̄, i_* M) ≅ H⁰_c(Z_k̄, M)`
  (`Stacks.EtaleCohomology.compactSupportSheafCohomologyRestrictClosedIso`)
  `≅ H⁰(Z_k̄, M|)` (`Z` is proper,
  `Stacks.EtaleCohomology.compactSupportFrobeniusCohomologyIsoOfIsProper`)
  `≅ H⁰(Y'_k̄, M|)` (`Stacks.EtaleCohomology.frobeniusExtensionCohomologyIso`), carrying `π_Z^d` to
  `π_{Y'}`;
* `Y'` is finite étale over `k'` (`Z` is reduced and `k` perfect), so `H⁰(Y'_k̄, M|)` is the
  product of the blocks at the `k̄`-points of `Y'_k̄`
  (`Stacks.EtaleCohomology.geometricFibreCohomologyZeroIso`);
* the rational point `y'` of `Y'` over `y` gives a `π̄`-fixed `k̄`-point, whose block is the stalk
  of `M` there, with `π_{Y'}` acting as the geometric Frobenius of `k'`
  (`Stacks.EtaleCohomology.blockInclusion_comp_sectionsTwistEndo_of_eq`,
  `Stacks.EtaleCohomology.geometricFrobeniusStalkFunctor_comp_rationalPointSectionsStalkIso_inv`);
* the stalks of inverse images and the comparison of geometric points identify that with the stalk
  of `G` at the geometric point over `y` (`Stacks.Frobenius.frobeniusStalk_comm`).

This proves `Stacks.EtaleCohomology.ClosedPartStalkCompactSupportInput`, an input of the
injection `H⁰_loc ⊆ H¹_c` of Weil II 1.8 in the proof of
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH).

The standard model `HasDerivedCategory.standard` is used because compactly supported cohomology is
defined there.

## Main results

* `Stacks.EtaleCohomology.exists_stalk_closedPart_compactSupport_of_rationalPoint`: the embedding,
  given the extension `k'` and the point.
* `Stacks.EtaleCohomology.closedPartStalkCompactSupportInput`:
  `Stacks.EtaleCohomology.ClosedPartStalkCompactSupportInput` holds.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.Frobenius

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

/-! ### Squares and powers, on variables -/

section Squares

variable {C : Type*} [Category* C]

/-- Two commutative squares paste. -/
lemma comm_comp_of_comm {A B D : C} {a : A ⟶ A} {b : B ⟶ B} {c : D ⟶ D} {e : A ⟶ B}
    {e' : B ⟶ D} (h₁ : a ≫ e = e ≫ b) (h₂ : b ≫ e' = e' ≫ c) : a ≫ e ≫ e' = (e ≫ e') ≫ c := by
  rw [reassoc_of% h₁, h₂, Category.assoc]

/-- An isomorphism intertwining two maps also intertwines them with its inverse. -/
private lemma comp_inv_eq_inv_comp_of_hom_comm_self {A B : C} (e : A ≅ B) {a : B ⟶ B}
    {b : A ⟶ A} (h : b ≫ e.hom = e.hom ≫ a) : a ≫ e.inv = e.inv ≫ b :=
  comp_inv_eq_inv_comp_of_hom_comm e e _ _ h

/-- An intertwining of endomorphisms intertwines their powers. -/
lemma end_pow_comp_of_comm {A B : C} (a : A ⟶ A) (b : B ⟶ B) (e : A ⟶ B) (h : a ≫ e = e ≫ b)
    (m : ℕ) : (End.of a ^ m).asHom ≫ e = e ≫ (End.of b ^ m).asHom := by
  induction m with
  | zero => simp only [pow_zero, End.one_asHom, Category.id_comp, Category.comp_id]
  | succ m ih =>
      rw [pow_succ, pow_succ, End.mul_asHom, End.mul_asHom, Category.assoc, ih]
      exact (reassoc_of% h) _

/-- The power of an endomorphism in `ModuleCat` is the power of the underlying linear map. -/
lemma moduleCat_end_pow_hom {R : Type*} [Ring R] {M : ModuleCat R} (a : End M) (m : ℕ) :
    (a ^ m).asHom.hom = a.asHom.hom ^ m := by
  induction m with
  | zero => rfl
  | succ m ih => rw [pow_succ, End.mul_asHom, ModuleCat.hom_comp, ih, pow_succ]; rfl

/-- The components of the inverse of a natural isomorphism are monomorphisms. -/
lemma mono_inv_app {D E : Type*} [Category* D] [Category* E] {F G : D ⥤ E} (e : F ≅ G) (X : D) :
    Mono (e.inv.app X) :=
  mono_of_mono_fac (e.inv_hom_id_app X)

/-- The components of a natural isomorphism are monomorphisms. -/
lemma mono_hom_app {D E : Type*} [Category* D] [Category* E] {F G : D ⥤ E} (e : F ≅ G) (X : D) :
    Mono (e.hom.app X) :=
  mono_of_mono_fac (e.hom_inv_id_app X)

/-- A functor applied to a component of a natural isomorphism is a monomorphism. -/
lemma mono_map_hom_app {D E B : Type*} [Category* D] [Category* E] [Category* B] {F G : D ⥤ E}
    (e : F ≅ G) (H : E ⥤ B) (X : D) : Mono (H.map (e.hom.app X)) :=
  mono_of_mono_fac (show H.map (e.hom.app X) ≫ H.map (e.inv.app X) = 𝟙 _ by
    rw [← H.map_comp, e.hom_inv_id_app, H.map_id])

/-- A functor applied to a component of the inverse of a natural isomorphism is a
monomorphism. -/
lemma mono_map_inv_app {D E B : Type*} [Category* D] [Category* E] [Category* B] {F G : D ⥤ E}
    (e : F ≅ G) (H : E ⥤ B) (X : D) : Mono (H.map (e.inv.app X)) :=
  mono_map_hom_app e.symm H X

/-- A functor carries powers of an endomorphism to powers. -/
lemma functor_map_end_pow {D : Type*} [Category* D] (F : C ⥤ D) {A : C} (a : End A) (m : ℕ) :
    F.map (a ^ m).asHom = (End.of (F.map a.asHom) ^ m).asHom :=
  congrArg End.asHom (map_pow (F.mapEnd A) a m)

end Squares

/-! ### Functorial forms of the identifications -/

section Functorial

variable (Λ : Type) [CommRing Λ]

/-- The inverse image of a sheaf placed in degree `0` is the inverse image of the complex. -/
def inverseImageSheafSingleIso {X X' : Scheme.{u}} (g : X' ⟶ X) :
    etaleModuleInverseImage.{u, 0} Λ g ⋙ sheafSingleComplex Λ ≅
      sheafSingleComplex Λ ⋙ (etaleModuleInverseImage.{u, 0} Λ g).mapCochainComplexPlus :=
  NatIso.ofComponents
    (fun M => ObjectProperty.isoMk _ ((HomologicalComplex.singleMapHomologicalComplex
      (etaleModuleInverseImage.{u, 0} Λ g) (ComplexShape.up ℤ) 0).app M).symm)
    (fun φ => ObjectProperty.hom_ext _
      ((HomologicalComplex.singleMapHomologicalComplex (etaleModuleInverseImage.{u, 0} Λ g)
        (ComplexShape.up ℤ) 0).inv.naturality φ))

variable {k : Type u} [Field k] [Fintype k]

/-- `Stacks.EtaleCohomology.frobeniusExtensionCohomologyIso` as a natural isomorphism. -/
def frobeniusExtensionCohomologyNatIso (Y : Over (Spec (.of k))) (k' : Type u) [Field k']
    [Algebra k k'] (kbar : Type u) [Field kbar] [Algebra k kbar] [Algebra k' kbar]
    [IsScalarTower k k' kbar] :
    (etaleModuleInverseImage.{u, 0} Λ (extensionProj Y k')).mapCochainComplexPlus ⋙
        fieldBaseChangeRestrictionFunctor.{u, 0} Λ (extensionOver Y k') kbar ⋙
        etaleModuleDerivedDirectImage.{u, 0} Λ
          (pullback.snd (extensionOver Y k').hom (specAlgebraMap k' kbar)) ⋙
        etaleModuleDerivedGlobalSections.{u, 0} Λ (Spec (.of kbar)) ≅
      fieldBaseChangeRestrictionFunctor.{u, 0} Λ Y kbar ⋙
        etaleModuleDerivedDirectImage.{u, 0} Λ (pullback.snd Y.hom (specAlgebraMap k kbar)) ⋙
        etaleModuleDerivedGlobalSections.{u, 0} Λ (Spec (.of kbar)) :=
  NatIso.ofComponents (frobeniusExtensionCohomologyIso Λ Y k' kbar)
    (fun φ => frobeniusExtensionCohomologyIso_hom_naturality Λ Y k' kbar φ)

/-- `Stacks.EtaleCohomology.compactSupportFrobeniusCohomologyIsoOfIsProper` as a natural
isomorphism. -/
def compactSupportFrobeniusFunctorIsoOfIsProper {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [IsProper f] (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar]
    [Algebra k kbar] :
    compactSupportFrobeniusFunctor.{u, 0} Λ f j kbar ≅
      fieldBaseChangeRestrictionFunctor.{u, 0} Λ (Over.mk f) kbar ⋙
        etaleModuleDerivedDirectImage.{u, 0} Λ
          (pullback.snd (Over.mk f).hom (specAlgebraMap k kbar)) ⋙
        etaleModuleDerivedGlobalSections.{u, 0} Λ (Spec (.of kbar)) :=
  NatIso.ofComponents (compactSupportFrobeniusCohomologyIsoOfIsProper Λ f j kbar)
    (fun φ => compactSupportFrobeniusCohomologyIsoOfIsProper_hom_naturality Λ f j kbar φ)

end Functorial

/-! ### The embedding, given the extension `k'` and a point of `Z` over it -/

section Core

variable (Λ : Type) [CommRing Λ] {k : Type u} [Field k] [Fintype k] {X Z : Scheme.{u}}
  (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
  (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [IsAlgClosed kbar]
  [Algebra k kbar] (iZ : Z ⟶ X) [IsClosedImmersion iZ] [IsFinite (iZ ≫ f)] [Etale (iZ ≫ f)]
  (y : X) (k' : Type u) [Field k'] [Fintype k'] [Algebra k k'] [Algebra k' kbar]
  [IsScalarTower k k' kbar]
  (xZ : Spec (.of k') ⟶ Z) (hxZ : xZ ≫ iZ ≫ f = specAlgebraMap k k')
  (θ : GeometricPoint.Hom (geometricPointAt X y) (rationalGeometricPoint kbar (xZ ≫ iZ)))

/-- The base change `Z ×_k k' ⟶ Spec k'` of the étale morphism `Z ⟶ Spec k` is étale. -/
instance etale_extensionOver_closedPart_hom :
    Etale (extensionOver (Over.mk (iZ ≫ f)) k').hom :=
  inferInstanceAs (Etale (pullback.snd (iZ ≫ f) (specAlgebraMap k k')))

/-- The base change `Z ×_k k' ⟶ Spec k'` of the finite morphism `Z ⟶ Spec k` is finite. -/
instance isFinite_extensionOver_closedPart_hom :
    IsFinite (extensionOver (Over.mk (iZ ≫ f)) k').hom :=
  inferInstanceAs (IsFinite (pullback.snd (iZ ≫ f) (specAlgebraMap k k')))

/-- The rational point of `Z ×_k k'` over `k'` given by `xZ`. -/
abbrev closedPartRationalPoint : Spec (.of k') ⟶ (extensionOver (Over.mk (iZ ≫ f)) k').left :=
  pullback.lift xZ (𝟙 _) (by rw [Category.id_comp]; exact hxZ)

omit [Fintype k] [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] [IsClosedImmersion iZ]
  [IsFinite (iZ ≫ f)] [Etale (iZ ≫ f)] [Fintype k'] in
/-- The rational point `closedPartRationalPoint` is a section of `Z ×_k k' ⟶ Spec k'`. -/
lemma closedPartRationalPoint_comp :
    closedPartRationalPoint f iZ k' xZ hxZ ≫ (extensionOver (Over.mk (iZ ≫ f)) k').hom = 𝟙 _ :=
  pullback.lift_snd _ _ _

/-- The `π̄`-fixed `k̄`-point of `(Z ×_k k')_k̄` over the rational point. -/
abbrev closedPartFixedSection :
    EtaleSections (pullback.snd (extensionOver (Over.mk (iZ ≫ f)) k').hom
      (specAlgebraMap k' kbar)) :=
  ⟨rationalPointBaseChangeLift (extensionOver (Over.mk (iZ ≫ f)) k') kbar
      (closedPartRationalPoint f iZ k' xZ hxZ) (closedPartRationalPoint_comp f iZ k' xZ hxZ),
    rationalPointBaseChangeLift_snd _ _ _ _⟩

/-- `H⁰(Y_k̄, -|_{Y_k̄})` on complexes on `Y'.left` for `Y' = Z ×_k k'` over `k'`. -/
abbrev closedPartExtensionCohomology :
    CochainComplex.Plus (EtaleModules.{u, 0} Λ (extensionOver (Over.mk (iZ ≫ f)) k').left) ⥤
      ModuleCat.{u + 1} Λ :=
  fieldBaseChangeRestrictionFunctor.{u, 0} Λ (extensionOver (Over.mk (iZ ≫ f)) k') kbar ⋙
    etaleModuleDerivedDirectImage.{u, 0} Λ
      (pullback.snd (extensionOver (Over.mk (iZ ≫ f)) k').hom (specAlgebraMap k' kbar)) ⋙
    etaleModuleDerivedGlobalSections.{u, 0} Λ (Spec (.of kbar)) ⋙
    DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) 0

/-- On `Z ×_k k'`, the inclusion of the stalk at the rational point as a block of `H⁰`. -/
def closedPartBlockEmbedding :
    rationalPointStalkFunctor.{u, 0} Λ kbar (closedPartRationalPoint f iZ k' xZ hxZ) ⟶
      sheafSingleComplex Λ ⋙ closedPartExtensionCohomology Λ f kbar iZ k' :=
  (rationalPointSectionsStalkIso Λ (extensionOver (Over.mk (iZ ≫ f)) k') kbar
      (closedPartRationalPoint f iZ k' xZ hxZ) (closedPartRationalPoint_comp f iZ k' xZ hxZ)).inv ≫
    blockInclusion Λ (extensionOver (Over.mk (iZ ≫ f)) k') kbar
      (closedPartFixedSection f kbar iZ k' xZ hxZ) ≫
    (geometricFibreCohomologyZeroNatIso Λ (extensionOver (Over.mk (iZ ≫ f)) k') kbar).inv

/-- The map from `H⁰` over `Z ×_k k'` of the inverse image of a sheaf on `Z`, placed in degree
`0`, to `H⁰_c(Z_k̄, -)`, through `H⁰(Z_k̄, -)`. -/
def closedPartExtensionToCompactSupport :
    etaleModuleInverseImage.{u, 0} Λ (extensionProj (Over.mk (iZ ≫ f)) k') ⋙
        sheafSingleComplex Λ ⋙ closedPartExtensionCohomology Λ f kbar iZ k' ⟶
      compactSupportSheafCohomology Λ (iZ ≫ f) (j.restrictClosed iZ) kbar 0 :=
  (Functor.whiskerRight (inverseImageSheafSingleIso Λ (extensionProj (Over.mk (iZ ≫ f)) k')).hom
      (closedPartExtensionCohomology Λ f kbar iZ k') :
    etaleModuleInverseImage.{u, 0} Λ (extensionProj (Over.mk (iZ ≫ f)) k') ⋙
        sheafSingleComplex Λ ⋙ closedPartExtensionCohomology Λ f kbar iZ k' ⟶
      sheafSingleComplex Λ ⋙
        (etaleModuleInverseImage.{u, 0} Λ
          (extensionProj (Over.mk (iZ ≫ f)) k')).mapCochainComplexPlus ⋙
        closedPartExtensionCohomology Λ f kbar iZ k') ≫
  (Functor.whiskerLeft (sheafSingleComplex Λ)
      (Functor.whiskerRight (frobeniusExtensionCohomologyNatIso Λ (Over.mk (iZ ≫ f)) k' kbar).hom
        (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) 0)) :
    sheafSingleComplex Λ ⋙
        (etaleModuleInverseImage.{u, 0} Λ
          (extensionProj (Over.mk (iZ ≫ f)) k')).mapCochainComplexPlus ⋙
        closedPartExtensionCohomology Λ f kbar iZ k' ⟶
      sheafSingleComplex Λ ⋙ (fieldBaseChangeRestrictionFunctor.{u, 0} Λ (Over.mk (iZ ≫ f)) kbar ⋙
        etaleModuleDerivedDirectImage.{u, 0} Λ
          (pullback.snd (Over.mk (iZ ≫ f)).hom (specAlgebraMap k kbar)) ⋙
        etaleModuleDerivedGlobalSections.{u, 0} Λ (Spec (.of kbar))) ⋙
        DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) 0) ≫
  (Functor.whiskerLeft (sheafSingleComplex Λ)
      (Functor.whiskerRight (compactSupportFrobeniusFunctorIsoOfIsProper Λ (iZ ≫ f)
          (j.restrictClosed iZ) kbar).inv
        (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) 0)) :
    sheafSingleComplex Λ ⋙ (fieldBaseChangeRestrictionFunctor.{u, 0} Λ (Over.mk (iZ ≫ f)) kbar ⋙
        etaleModuleDerivedDirectImage.{u, 0} Λ
          (pullback.snd (Over.mk (iZ ≫ f)).hom (specAlgebraMap k kbar)) ⋙
        etaleModuleDerivedGlobalSections.{u, 0} Λ (Spec (.of kbar))) ⋙
        DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) 0 ⟶
      compactSupportSheafCohomology Λ (iZ ≫ f) (j.restrictClosed iZ) kbar 0)

/-- The embedding of the stalk at `xZ` into `H⁰_c(X_k̄, i_* -)`. -/
def closedPartStalkEmbeddingZ :
    rationalPointStalkFunctor.{u, 0} Λ kbar xZ ⟶
      etaleModuleDirectImage.{u, 0} Λ iZ ⋙ compactSupportSheafCohomology Λ f j kbar 0 :=
  (rationalPointStalkPullbackIso Λ (extensionProj (Over.mk (iZ ≫ f)) k') kbar
      (closedPartRationalPoint f iZ k' xZ hxZ) xZ (pullback.lift_fst _ _ _)).inv ≫
    (Functor.whiskerLeft (etaleModuleInverseImage.{u, 0} Λ (extensionProj (Over.mk (iZ ≫ f)) k'))
      (closedPartBlockEmbedding Λ f kbar iZ k' xZ hxZ) :
      etaleModuleInverseImage.{u, 0} Λ (extensionProj (Over.mk (iZ ≫ f)) k') ⋙
          rationalPointStalkFunctor.{u, 0} Λ kbar (closedPartRationalPoint f iZ k' xZ hxZ) ⟶
        etaleModuleInverseImage.{u, 0} Λ (extensionProj (Over.mk (iZ ≫ f)) k') ⋙
          sheafSingleComplex Λ ⋙ closedPartExtensionCohomology Λ f kbar iZ k') ≫
    closedPartExtensionToCompactSupport Λ f j kbar iZ k' ≫
    (compactSupportSheafCohomologyRestrictClosedIso Λ f j kbar 0 iZ).hom

/-- **The embedding of the stalk of `G` at the geometric point over `y` into
`H⁰_c(X_k̄, i_* i⁻¹ G)`**, through the block at the rational point of `Z ×_k k'`. -/
def closedPartStalkEmbedding :
    (Scheme.pointSmallEtale (geometricPointAt X y).hom).sheafFiber
        (A := ModuleCat.{u + 1} Λ) ⟶
      etaleModuleClosedPart Λ iZ ⋙ compactSupportSheafCohomology Λ f j kbar 0 :=
  (GrothendieckTopology.Point.sheafFiberIsoOfIso
    (@asIso _ _ _ _ (smallEtalePointHom X θ) (smallEtalePointHom_isIso _ _))).inv ≫
  (rationalPointStalkPullbackIso Λ iZ kbar xZ (xZ ≫ iZ) rfl).inv ≫
  (Functor.whiskerLeft (etaleModuleInverseImage.{u, 0} Λ iZ)
    (closedPartStalkEmbeddingZ Λ f j kbar iZ k' xZ hxZ) :
    etaleModuleInverseImage.{u, 0} Λ iZ ⋙ rationalPointStalkFunctor.{u, 0} Λ kbar xZ ⟶
      etaleModuleClosedPart Λ iZ ⋙ compactSupportSheafCohomology Λ f j kbar 0)

omit [Fintype k] [LocallyOfFiniteType f] [IsSeparated f] [Fintype k'] in
/-- **The embedding is injective**: it is a composite of isomorphisms and of the inclusion of a
block, which is split by the restriction to the block. -/
theorem mono_closedPartStalkEmbedding_app (G : EtaleModules.{u, 0} Λ X) :
    Mono ((closedPartStalkEmbedding Λ f j kbar iZ y k' xZ hxZ θ).app G) := by
  have hι : ∀ (N : EtaleModules.{u, 0} Λ (extensionOver (Over.mk (iZ ≫ f)) k').left),
      Mono ((blockInclusion Λ (extensionOver (Over.mk (iZ ≫ f)) k') kbar
        (closedPartFixedSection f kbar iZ k' xZ hxZ)).app N) := fun N =>
    mono_of_mono_fac (NatTrans.congr_app
      (blockInclusion_comp_blockRestriction_self Λ (extensionOver (Over.mk (iZ ≫ f)) k') kbar
        (closedPartFixedSection f kbar iZ k' xZ hxZ)) N)
  have hB : ∀ (N : EtaleModules.{u, 0} Λ (extensionOver (Over.mk (iZ ≫ f)) k').left),
      Mono ((closedPartBlockEmbedding Λ f kbar iZ k' xZ hxZ).app N) := fun N =>
    mono_comp' (mono_inv_app _ N) (mono_comp' (hι N) (mono_inv_app _ N))
  have hE : ∀ (N : EtaleModules.{u, 0} Λ Z),
      Mono ((closedPartExtensionToCompactSupport Λ f j kbar iZ k').app N) := fun N =>
    mono_comp' (mono_map_hom_app (inverseImageSheafSingleIso Λ
        (extensionProj (Over.mk (iZ ≫ f)) k')) (closedPartExtensionCohomology Λ f kbar iZ k') N)
      (mono_comp' (mono_map_hom_app (frobeniusExtensionCohomologyNatIso Λ (Over.mk (iZ ≫ f)) k'
          kbar) (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) 0)
          ((sheafSingleComplex Λ).obj N))
        (mono_map_inv_app (compactSupportFrobeniusFunctorIsoOfIsProper Λ (iZ ≫ f)
          (j.restrictClosed iZ) kbar) (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) 0)
          ((sheafSingleComplex Λ).obj N)))
  have hZ : ∀ (N : EtaleModules.{u, 0} Λ Z),
      Mono ((closedPartStalkEmbeddingZ Λ f j kbar iZ k' xZ hxZ).app N) := fun N =>
    mono_comp' (mono_inv_app _ N) (mono_comp' (hB _) (mono_comp' (hE N) (mono_hom_app _ N)))
  exact mono_comp' (mono_inv_app _ G) (mono_comp' (mono_inv_app _ G) (hZ _))

variable (p n : ℕ) [Fact p.Prime] [CharP k p] [CharP kbar p] (hcard : Fintype.card k = p ^ n)
  [CharP k' p] (m : ℕ) (hcard' : Fintype.card k' = p ^ (n * (m + 1)))
  [Finite (X.residueField y)] (hres : Nat.card (X.residueField y) = Fintype.card k')

include hres hcard hcard' in
omit [LocallyOfFiniteType f] [IsSeparated f] in
/-- **The embedding carries the geometric Frobenius of `κ(y)` to `(π_X^*) ^ (m + 1)`**, where
`k'` has `(#k) ^ (m + 1)` elements. -/
theorem closedPartStalkEmbedding_frobenius (G : EtaleModules.{u, 0} Λ X) :
    frobeniusStalk (ModuleCat.{u + 1} Λ) X y G ≫
        (closedPartStalkEmbedding Λ f j kbar iZ y k' xZ hxZ θ).app G =
      (closedPartStalkEmbedding Λ f j kbar iZ y k' xZ hxZ θ).app G ≫
        (End.of ((compactSupportSheafFrobenius Λ f j kbar p n hcard 0).app
          ((etaleModuleClosedPart Λ iZ).obj G)) ^ (m + 1)).asHom := by
  set Y := Over.mk (iZ ≫ f)
  set Y' := extensionOver Y k'
  set x' := closedPartRationalPoint f iZ k' xZ hxZ
  set hx' := closedPartRationalPoint_comp f iZ k' xZ hxZ
  set M := (etaleModuleInverseImage.{u, 0} Λ iZ).obj G
  set N := (etaleModuleInverseImage.{u, 0} Λ (extensionProj Y k')).obj M
  set F := DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) 0
  have h₁ := comp_inv_eq_inv_comp_of_hom_comm_self
    ((GrothendieckTopology.Point.sheafFiberIsoOfIso (A := ModuleCat.{u + 1} Λ)
      (@asIso _ _ _ _ (smallEtalePointHom X θ) (smallEtalePointHom_isIso _ _))).app G)
    (frobeniusStalk_comm (ModuleCat.{u + 1} Λ) X y kbar p (n * (m + 1)) hcard' (xZ ≫ iZ) θ
      hres G).symm
  have h₂ := comp_inv_eq_inv_comp_of_hom_comm_self
    ((rationalPointStalkPullbackIso Λ iZ kbar xZ (xZ ≫ iZ) rfl).app G)
    (geometricFrobeniusStalkFunctor_comp_rationalPointStalkPullbackIso_hom Λ iZ kbar xZ
      (xZ ≫ iZ) rfl p (n * (m + 1)) hcard' G)
  have h₃ := comp_inv_eq_inv_comp_of_hom_comm_self
    ((rationalPointStalkPullbackIso Λ (extensionProj Y k') kbar x' xZ
      (pullback.lift_fst _ _ _)).app M)
    (geometricFrobeniusStalkFunctor_comp_rationalPointStalkPullbackIso_hom Λ (extensionProj Y k')
      kbar x' xZ (pullback.lift_fst _ _ _) p (n * (m + 1)) hcard' M)
  have h₄ := geometricFrobeniusStalkFunctor_comp_rationalPointSectionsStalkIso_inv Λ Y' kbar x' hx'
    p (n * (m + 1)) hcard' N
  have h₅ := (NatTrans.congr_app (blockInclusion_comp_sectionsTwistEndo_of_eq Λ Y' kbar p
    (n * (m + 1)) hcard' (closedPartFixedSection f kbar iZ k' xZ hxZ)
    (rationalPointBaseChangeLift_comp_geometricFrobeniusBaseChange Y' kbar x' hx' p (n * (m + 1))
      hcard').symm) N).symm
  have h₆ := comp_inv_eq_inv_comp_of_hom_comm_self (geometricFibreCohomologyZeroIso Λ Y' kbar N)
    (geometricFibreCohomologyZeroIso_hom_frobenius Λ Y' kbar p (n * (m + 1)) hcard' N)
  have h₇ := functor_map_comp_eq_of_comp_eq F
    (frobeniusRestrictionCohomologyEndo_naturality (Λ := Λ) Y' kbar p (n * (m + 1)) hcard'
      ((inverseImageSheafSingleIso Λ (extensionProj Y k')).hom.app M)).symm
  have h₈ := functor_map_comp_eq_of_comp_eq F
    (frobeniusExtensionCohomologyIso_comm Λ Y k' kbar p n hcard m hcard'
      ((sheafSingleComplex Λ).obj M))
  have h₉ := functor_map_comp_eq_of_comp_eq F
    (end_pow_comp_of_comm _ _ _ (comp_inv_eq_inv_comp_of_hom_comm_self
      (compactSupportFrobeniusCohomologyIsoOfIsProper Λ (iZ ≫ f) (j.restrictClosed iZ) kbar
        ((sheafSingleComplex Λ).obj M))
      (compactSupportFrobeniusCohomologyIsoOfIsProper_hom_frobenius Λ (iZ ≫ f)
        (j.restrictClosed iZ) kbar p n hcard ((sheafSingleComplex Λ).obj M))) (m + 1))
  have h₁₀ := end_pow_comp_of_comm _ _ _ (NatTrans.congr_app
    (compactSupportSheafCohomologyRestrictClosedIso_hom_frobenius Λ f j kbar 0 iZ p n hcard) M)
    (m + 1)
  rw [functor_map_end_pow F (End.of
    (canonicalCompactSupportFrobenius Λ (iZ ≫ f) (j.restrictClosed iZ) kbar p n hcard
      ((sheafSingleComplex Λ).obj M)))] at h₉
  exact comm_comp_of_comm h₁ (comm_comp_of_comm h₂ (comm_comp_of_comm h₃
    (comm_comp_of_comm (comm_comp_of_comm h₄ (comm_comp_of_comm h₅ h₆))
      (comm_comp_of_comm (comm_comp_of_comm h₇ (comm_comp_of_comm h₈ h₉)) h₁₀))))

end Core

/-! ### The input `Stacks.EtaleCohomology.ClosedPartStalkCompactSupportInput` -/

/-- **The stalk at a closed point of `Z` embeds into `H⁰_c(X_k̄, i_* i⁻¹ -)`**, naturally in the
sheaf, carrying the geometric Frobenius of `κ(y)` to `(π_X^*) ^ deg y`: take `k' = κ(y)`, of
degree `d` over `k`, a `k`-embedding `κ(y) ⟶ k̄`, the point `Spec κ(y) ⟶ Z` over `y`
(`κ(y) ≅ κ(z)` for the closed immersion `i`) and a `κ(y)`-embedding `k̄ ⟶ κ(y)^alg`. -/
theorem closedPartStalkCompactSupportInput : ClosedPartStalkCompactSupportInput.{u} := by
  intro k _ _ X Z f _ _ _ j kbar _ _ _ p n _ _ hcard iZ _ _ _ y hy _ Λ _
  obtain ⟨z, rfl⟩ := hy
  have : IsAlgClosed kbar := IsAlgClosure.isAlgClosed k
  have : CharP kbar p := charP_of_injective_algebraMap (algebraMap k kbar).injective p
  have : Etale (iZ ≫ f) :=
    Stacks.AlgebraicGeometry.ProperSectionsGeom.etale_of_isFinite_of_isReduced (iZ ≫ f)
  set k' := X.residueField (iZ.base z)
  let : Fintype k' := Fintype.ofFinite _
  let : Algebra k k' := (Spec.preimage (X.fromSpecResidueField (iZ.base z) ≫ f)).hom.toAlgebra
  have hspec : specAlgebraMap k k' = X.fromSpecResidueField (iZ.base z) ≫ f := by
    change Spec.map (CommRingCat.ofHom
      (Spec.preimage (X.fromSpecResidueField (iZ.base z) ≫ f)).hom) = _
    rw [CommRingCat.ofHom_hom, Spec.map_preimage]
  have : CharP k' p := charP_of_injective_algebraMap (algebraMap k k').injective p
  have : Algebra.IsAlgebraic k k' := Algebra.IsAlgebraic.of_finite k k'
  let : Algebra k' kbar := (IsAlgClosed.lift (R := k) (S := k') (M := kbar)).toRingHom.toAlgebra
  have : IsScalarTower k k' kbar := IsScalarTower.of_algebraMap_eq fun x =>
    ((IsAlgClosed.lift (R := k) (S := k') (M := kbar)).commutes x).symm
  have hpos : 0 < Module.finrank k k' := Module.finrank_pos
  obtain ⟨m, hm⟩ : ∃ m, Module.finrank k k' = m + 1 := ⟨Module.finrank k k' - 1, by omega⟩
  have hcardk' : Fintype.card k' = (p ^ n) ^ (m + 1) := by
    rw [Module.card_eq_pow_finrank (K := k) (V := k'), hcard, hm]
  have hcard' : Fintype.card k' = p ^ (n * (m + 1)) := by rw [hcardk', pow_mul]
  have : IsIso (iZ.residueFieldMap z) := isIso_residueFieldMap_of_isClosedImmersion iZ z
  set xZ : Spec (.of k') ⟶ Z := Spec.map (CategoryTheory.inv (iZ.residueFieldMap z)) ≫
    Z.fromSpecResidueField z
  have hxZi : xZ ≫ iZ = X.fromSpecResidueField (iZ.base z) := by
    rw [Category.assoc, ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField,
      ← Category.assoc, ← Spec.map_comp, IsIso.hom_inv_id, Spec.map_id]
    exact Category.id_comp _
  have hxZ : xZ ≫ iZ ≫ f = specAlgebraMap k k' := by
    rw [← Category.assoc, hxZi, hspec]
  have : Algebra.IsAlgebraic k' kbar := Algebra.IsAlgebraic.tower_top (K := k) k'
  set ψ := IsAlgClosed.lift (R := k') (S := kbar) (M := AlgebraicClosure k')
  let θ : GeometricPoint.Hom (geometricPointAt X (iZ.base z))
      (rationalGeometricPoint kbar (xZ ≫ iZ)) :=
    ⟨Spec.map (CommRingCat.ofHom ψ.toRingHom), by
      change Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫
          (Spec.map (CommRingCat.ofHom (algebraMap k' kbar)) ≫ xZ ≫ iZ) =
        Spec.map (CommRingCat.ofHom (algebraMap k' (AlgebraicClosure k'))) ≫
          X.fromSpecResidueField (iZ.base z)
      rw [hxZi, ← Category.assoc, ← Spec.map_comp]
      congr 2
      ext a
      exact ψ.commutes a⟩
  have hres : Nat.card (X.residueField (iZ.base z)) = Fintype.card k' := Nat.card_eq_fintype_card
  refine ⟨m + 1, m.succ_pos, hres.trans hcardk',
    closedPartStalkEmbedding Λ f j kbar iZ (iZ.base z) k' xZ hxZ θ, fun G => ?_, fun G => ?_⟩
  · exact (ModuleCat.mono_iff_injective _).1
      (mono_closedPartStalkEmbedding_app Λ f j kbar iZ (iZ.base z) k' xZ hxZ θ G)
  · have h := congrArg ModuleCat.Hom.hom (closedPartStalkEmbedding_frobenius Λ f j kbar iZ
      (iZ.base z) k' xZ hxZ θ p n hcard m hcard' hres G)
    rw [ModuleCat.hom_comp, ModuleCat.hom_comp, moduleCat_end_pow_hom] at h
    exact h

end Stacks.EtaleCohomology

end
