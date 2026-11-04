module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
public import StacksFrontier.AlgebraicGeometry.Topologies.ZariskiTopology.StandardOpenCoverSquares
public import StacksFrontier.CategoryTheory.Sites.Cohomology.MayerVietoris.DescentForACoarserTopology

/-!
# Module sheaves on the affine opens of a scheme for the almost chaotic topology

Let `B` be a big Zariski site containing a scheme `S`, and let `𝒪` be a sheaf of commutative rings
for the Zariski topology on the affine opens of `S`. This file records the resulting ringed site
together with its coarsenings to the almost chaotic and to the trivial topology, and compares
module sheaves for the latter two topologies.

Over an empty affine open the structure sheaf is the zero ring, because the empty sieve is a
Zariski covering there; hence the sections of every presheaf of modules vanish over an empty
affine open, and so do its derived sections. Consequently the underlying presheaf of a presheaf
of modules is automatically a sheaf for the almost chaotic topology, and module sheaves for the
trivial topology and for the almost chaotic topology are the same thing. The canonical
Mayer–Vietoris map of a square of affine opens is therefore an isomorphism for one of the two
topologies exactly when it is for the other.

## Main definitions

* `AlgebraicGeometry.SmallAffineZariski.ringedSite` — the affine opens of `S` with their Zariski
  topology and a chosen structure sheaf, and its coarsenings
  `AlgebraicGeometry.SmallAffineZariski.almostChaoticRingedSite` and
  `AlgebraicGeometry.SmallAffineZariski.trivialRingedSite`.
* `AlgebraicGeometry.SmallAffineZariski.almostChaoticTrivialEquivalence` — the equivalence
  between module sheaves for the almost chaotic topology and for the trivial topology.

## Main results

* `AlgebraicGeometry.SmallAffineZariski.isZero_module_obj_of_isEmpty` and
  `AlgebraicGeometry.SmallAffineZariski.isZero_derivedSections_of_isEmpty` — sections and derived
  sections of module sheaves vanish over an empty affine open.
* `AlgebraicGeometry.SmallAffineZariski.isSheaf_almostChaotic` — the underlying presheaf of a
  presheaf of modules is a sheaf for the almost chaotic topology.
* `AlgebraicGeometry.SmallAffineZariski.isCSquareIso_trivial_iff_almostChaotic` — the canonical
  Mayer–Vietoris map of a square is an isomorphism for the trivial topology exactly when it is
  for the almost chaotic topology.

## References

* [Stacks Project, Tag 0F1L](https://stacks.math.columbia.edu/tag/0F1L)
* [Stacks Project, Tag 0F16](https://stacks.math.columbia.edu/tag/0F16)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

open ZeroObject in
/-- A right derived functor of a zero functor is zero. -/
public lemma Functor.isZero_of_isRightDerivedFunctor {C D H : Type*}
    [Category* C] [Category* D] [Category* H] [HasZeroObject H] [HasZeroMorphisms H]
    {L : C ⥤ D} {F : C ⥤ H} (W : MorphismProperty C) [L.IsLocalization W]
    (RF : D ⥤ H) (unit : F ⟶ L ⋙ RF) [RF.IsRightDerivedFunctor unit W] (hF : IsZero F) :
    IsZero RF := by
  let zeroFunctor : D ⥤ H := (Functor.const D).obj (0 : H)
  have hzero : ∀ X, IsZero (zeroFunctor.obj X) := fun _ => isZero_zero H
  let comparison : L ⋙ zeroFunctor ≅ F := (Functor.isZero _ fun X => hzero (L.obj X)).iso hF
  have : zeroFunctor.IsRightDerivedFunctor comparison.inv W :=
    Functor.isRightDerivedFunctor_of_inverts W zeroFunctor comparison
  exact (Functor.isZero zeroFunctor hzero).of_iso
    (Functor.rightDerivedUnique RF zeroFunctor unit comparison.inv W)

/-- A right derived functor of a functor isomorphic to `F` is a right derived functor of `F`,
with the unit transported along the isomorphism. -/
public lemma Functor.isRightDerivedFunctor_of_iso {C D H : Type*}
    [Category* C] [Category* D] [Category* H] {L : C ⥤ D} (W : MorphismProperty C)
    [L.IsLocalization W] {F F' : C ⥤ H} (RF : D ⥤ H) (unit : F ⟶ L ⋙ RF)
    [RF.IsRightDerivedFunctor unit W] (comparison : F' ≅ F) :
    RF.IsRightDerivedFunctor (comparison.hom ≫ unit) W := by
  rw [Functor.isRightDerivedFunctor_iff_isLeftKanExtension]
  exact (Functor.isLeftKanExtension_iff_of_iso₂ unit (comparison.hom ≫ unit)
    comparison.symm (Iso.refl RF) (by simp)).mp
    (Functor.IsRightDerivedFunctor.isLeftKanExtension RF unit W)

/-- An exact additive equivalence induces an equivalence of derived categories. -/
public lemma Functor.isEquivalence_mapDerivedCategory {C D : Type*} [Category* C] [Category* D]
    [Abelian C] [Abelian D] (F : C ⥤ D) [F.Additive] [F.IsEquivalence] :
    F.mapDerivedCategory.IsEquivalence := by
  let morphism := F.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism (ComplexShape.up ℤ)
  have : morphism.functor.IsEquivalence :=
    (F.asEquivalence.mapHomologicalComplex (ComplexShape.up ℤ)).isEquivalence_functor
  have : morphism.IsInduced := by
    constructor
    ext source target arrow
    exact HomologicalComplex.quasiIso_map_iff_of_preservesHomology arrow F
  have : morphism.IsLocalizedEquivalence := morphism.isLocalizedEquivalence_of_isInduced
  exact morphism.localizedFunctor_isEquivalence
    (HomologicalComplexUpToQuasiIso.Q (C := C)) (HomologicalComplexUpToQuasiIso.Q (C := D))

/-- An exact additive faithful functor carries bounded-below objects of the derived category to
bounded-below objects. -/
public lemma Functor.plus_mapDerivedCategory_obj {C D : Type*} [Category* C] [Category* D]
    [Abelian C] [Abelian D] (F : C ⥤ D) [F.Additive] [F.Faithful]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] (K : DerivedCategory C)
    (hK : (DerivedCategory.TStructure.t (C := C)).plus K) :
    (DerivedCategory.TStructure.t (C := D)).plus (F.mapDerivedCategory.obj K) := by
  obtain ⟨degree, hK⟩ := hK
  have : K.IsGE degree := hK
  obtain ⟨complex, strict, ⟨iso⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isGE K degree
  let mapped : CochainComplex D ℤ := (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj complex
  have : mapped.IsStrictlyGE degree :=
    (CochainComplex.isStrictlyGE_mapHomologicalComplex_obj_iff complex F degree).2 strict
  have : (DerivedCategory.Q.obj mapped).IsGE degree := inferInstance
  refine ⟨degree, ?_⟩
  let comparison : DerivedCategory.Q.obj mapped ≅ F.mapDerivedCategory.obj K :=
    (F.mapDerivedCategoryFactors.app complex).symm ≪≫ F.mapDerivedCategory.mapIso iso.symm
  exact DerivedCategory.TStructure.t.isGE_of_iso comparison degree

/-- An isomorphism `F ⋙ G ≅ H` with `G` exact identifies the sources of the derived units of `H`
and of `F` followed by `G`. -/
public noncomputable def Functor.mapHomotopyCategoryQhCompMapDerivedCategoryIso
    {C D E : Type*} [Category* C] [Category* D] [Category* E] [Abelian C] [Abelian D] [Abelian E]
    (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E) [F.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (comparison : F ⋙ G ≅ H) :
    H.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ≅
      (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) ⋙
        G.mapDerivedCategory :=
  Functor.isoWhiskerRight
      (Functor.mapHomotopyCategoryCompIso comparison (ComplexShape.up ℤ)).symm _ ≪≫
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ G.mapDerivedCategoryFactorsh.symm ≪≫
        (Functor.associator _ _ _).symm

end CategoryTheory

namespace HomologicalComplex

/-- The image of an acyclic cochain complex under an exact additive functor is acyclic. -/
public lemma Acyclic.mapHomologicalComplex {C D : Type*} [Category* C] [Category* D]
    [Abelian C] [Abelian D] (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] {K : CochainComplex C ℤ}
    (hK : K.Acyclic) :
    ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).Acyclic :=
  fun degree => (hK degree).map F

end HomologicalComplex

namespace CochainComplex

/-- A cochain complex whose image under an exact additive fully faithful functor is K-injective
is itself K-injective: a null homotopy of the image of a map from an acyclic complex is the
image of a null homotopy. -/
public lemma isKInjective_of_map {C D : Type*} [Category* C] [Category* D]
    [Abelian C] [Abelian D] (F : C ⥤ D) [F.Additive] [F.Full] [F.Faithful]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] (K : CochainComplex C ℤ)
    [CochainComplex.IsKInjective ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)] :
    K.IsKInjective := by
  constructor
  intro source arrow acyclic
  refine ⟨F.preimageHomotopy ?_⟩
  simpa only [Functor.map_zero] using CochainComplex.IsKInjective.homotopyZero
    ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map arrow)
    (HomologicalComplex.Acyclic.mapHomologicalComplex F acyclic)

/-- An additive equivalence carries K-injective cochain complexes to K-injective cochain
complexes. -/
public lemma isKInjective_mapHomologicalComplex_of_equivalence {C D : Type*}
    [Category* C] [Category* D] [Abelian C] [Abelian D] (e : C ≌ D)
    [e.functor.Additive] [e.inverse.Additive] (K : CochainComplex C ℤ) [K.IsKInjective] :
    CochainComplex.IsKInjective
      ((e.functor.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) := by
  let iso : (e.inverse.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      ((e.functor.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≅ K :=
    (Functor.mapHomologicalComplexCompIso e.unitIso.symm (ComplexShape.up ℤ)).app K ≪≫
      (Functor.mapHomologicalComplexIdIso C (ComplexShape.up ℤ)).app K
  have : CochainComplex.IsKInjective ((e.inverse.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      ((e.functor.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) :=
    CochainComplex.isKInjective_of_iso iso.symm
  exact isKInjective_of_map e.inverse _

end CochainComplex

namespace AlgebraicGeometry.SmallAffineZariski

variable (B : BigZariskiSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The trivial topology on the affine opens of `S` is coarser than the Zariski topology. -/
public lemma trivial_le_topology :
    GrothendieckTopology.trivial (SmallAffineZariski B S hS) ≤ topology B S hS :=
  bot_le

/-- The affine opens of `S` with their Zariski topology and a chosen structure sheaf. -/
public abbrev ringedSite (O : Sheaf (topology B S hS) CommRingCat.{u + 1}) :
    RingedSite.{u + 1, u, u + 1} where
  C := SmallAffineZariski B S hS
  J := topology B S hS
  O := O

/-- The affine opens of `S` with the almost chaotic topology and the same structure sheaf. -/
public abbrev almostChaoticRingedSite (O : Sheaf (topology B S hS) CommRingCat.{u + 1}) :
    RingedSite.{u + 1, u, u + 1} :=
  (ringedSite B S hS O).ofLe (almostChaotic_le_topology B S hS)

/-- The affine opens of `S` with the trivial topology and the same structure sheaf. -/
public abbrev trivialRingedSite (O : Sheaf (topology B S hS) CommRingCat.{u + 1}) :
    RingedSite.{u + 1, u, u + 1} :=
  (ringedSite B S hS O).ofLe (trivial_le_topology B S hS)

section Vanishing

/-- Sections of a presheaf of modules over the structure sheaf vanish over an empty affine open:
the empty sieve covers it, so the structure sheaf is the zero ring there. -/
public lemma isZero_module_obj_of_isEmpty (O : Sheaf (topology B S hS) CommRingCat.{u + 1})
    {U : SmallAffineZariski B S hS} (hU : IsEmpty ((toScheme B S hS).obj U))
    (M : PresheafOfModules.{u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite B S hS O).O).obj) :
    IsZero (M.obj (op U)) := by
  have : Subsingleton
      ((Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite B S hS O).O).obj.obj (op U)) :=
    CommRingCat.subsingleton_of_isTerminal
      (O.isTerminalOfBotCover U (bot_mem_topology B S hS hU))
  have : Subsingleton (M.obj (op U)) := Module.subsingleton
    ((Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite B S hS O).O).obj.obj (op U)) (M.obj (op U))
  exact ModuleCat.isZero_of_subsingleton _

/-- Any two sections of a presheaf of modules over an empty affine open are equal. -/
private lemma module_obj_eq_of_isEmpty (O : Sheaf (topology B S hS) CommRingCat.{u + 1})
    {U : SmallAffineZariski B S hS} (hU : IsEmpty ((toScheme B S hS).obj U))
    (M : PresheafOfModules.{u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite B S hS O).O).obj)
    (x y : M.obj (op U)) : x = y :=
  (ModuleCat.isZero_iff_subsingleton.mp (isZero_module_obj_of_isEmpty B S hS O hU M)).elim _ _

/-- Derived sections over an object of a ringed site vanish as soon as the sections of every
module sheaf over it vanish: derived sections are a right derived functor of sections. -/
public lemma isZero_derivedSections_of_isZero_sections
    {T : RingedSite.{u + 1, u, u + 1}} [HasSheafify T.J AddCommGrpCat.{u + 1}]
    [T.J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}] (sq : Square T.C) (U : T.C)
    (h : ∀ M : SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf T.O),
      IsZero ((Stacks.Cohomology.MayerVietoris.sections T U).obj M)) :
    IsZero ((Stacks.MayerVietoris.CanonicalMapOfComplexes.derivedCSquareData.{u + 1, u + 1}
      (R := (Stacks.SheafOfModules.Tensor.ringSheaf T.O)) sq).derivedSections U) := by
  have hcomplex : ∀ I : CochainComplex
      (SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf T.O)) ℤ,
      IsZero ((Stacks.Cohomology.MayerVietoris.sectionsComplex T U).obj I) := by
    intro I
    rw [IsZero.iff_id_eq_zero]
    exact HomologicalComplex.hom_ext _ _ fun degree => (h (I.X degree)).eq_of_src _ _
  have hF : IsZero (Stacks.Cohomology.MayerVietoris.sectionsComplex T U ⋙
      DerivedCategory.Q) :=
    Functor.isZero _ fun I => Functor.map_isZero DerivedCategory.Q (hcomplex I)
  exact Functor.isZero_of_isRightDerivedFunctor
    (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ)) _
    ((Stacks.MayerVietoris.CanonicalMapOfComplexes.derivedCSquareData.{u + 1, u + 1}
      (R := (Stacks.SheafOfModules.Tensor.ringSheaf T.O)) sq).sectionsData.unit U) hF

/-- Derived sections of module sheaves for the trivial topology vanish over an empty affine
open. -/
public lemma isZero_derivedSections_of_isEmpty (O : Sheaf (topology B S hS) CommRingCat.{u + 1})
    (sq : Square (SmallAffineZariski B S hS)) (U : SmallAffineZariski B S hS)
    (hU : IsEmpty ((toScheme B S hS).obj U)) :
    IsZero ((Stacks.MayerVietoris.CanonicalMapOfComplexes.derivedCSquareData.{u + 1, u + 1}
      (R := (Stacks.SheafOfModules.Tensor.ringSheaf (trivialRingedSite B S hS O).O))
        sq).derivedSections U) := by
  apply isZero_derivedSections_of_isZero_sections (T := trivialRingedSite B S hS O)
  intro M
  rw [IsZero.iff_id_eq_zero]
  ext value
  exact module_obj_eq_of_isEmpty B S hS O hU M.val _ _

/-- The underlying presheaf of a presheaf of modules over the structure sheaf is a sheaf for the
almost chaotic topology: over a nonempty affine open only the maximal sieve covers, and over an
empty one all sections vanish. -/
public lemma isSheaf_almostChaotic (O : Sheaf (topology B S hS) CommRingCat.{u + 1})
    (M : PresheafOfModules.{u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite B S hS O).O).obj) :
    Presheaf.IsSheaf (almostChaotic B S hS) M.presheaf := by
  apply (Presheaf.isSheaf_iff_isSheaf_forget (almostChaotic B S hS) M.presheaf
    (forget AddCommGrpCat)).mpr
  rw [isSheaf_iff_isSheaf_of_type]
  intro U T hT
  by_cases hU : IsEmpty ((toScheme B S hS).obj U)
  · intro x _
    refine ⟨0, fun Y f _ => ?_, fun _ _ => module_obj_eq_of_isEmpty B S hS O hU M _ _⟩
    exact module_obj_eq_of_isEmpty B S hS O ((toScheme B S hS).map f).base.hom.1.isEmpty M _ _
  · obtain htop | rfl := (mem_almostChaotic_iff B S hS).mp hT
    · exact absurd htop hU
    · exact Presieve.isSheafFor_top _

end Vanishing

section Transfer

variable (O : Sheaf (topology B S hS) CommRingCat.{u + 1})

/-- A module sheaf for the trivial topology, regarded as a module sheaf for the almost chaotic
topology. -/
public noncomputable def trivialModulesToAlmostChaotic :
    SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf (trivialRingedSite B S hS O).O) ⥤
      SheafOfModules.{u + 1}
          (Stacks.SheafOfModules.Tensor.ringSheaf (almostChaoticRingedSite B S hS O).O) where
  obj M := ⟨M.val, isSheaf_almostChaotic B S hS O M.val⟩
  map f := ⟨f.val⟩
  map_id _ := rfl
  map_comp _ _ := rfl

/-- A module sheaf for the almost chaotic topology, regarded as a module sheaf for the trivial
topology. -/
public noncomputable def almostChaoticModulesToTrivial :
    SheafOfModules.{u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf (almostChaoticRingedSite B S hS O).O) ⥤
      SheafOfModules.{u + 1}
          (Stacks.SheafOfModules.Tensor.ringSheaf (trivialRingedSite B S hS O).O) :=
  Stacks.Sites.CoarserTopology.modulePushforward (trivial_le_almostChaotic B S hS)
    (Stacks.SheafOfModules.Tensor.ringSheaf (almostChaoticRingedSite B S hS O).O)

/-- Two module sheaves with the same underlying presheaf of modules are isomorphic. -/
public def moduleSheafIsoOfValEq {J : GrothendieckTopology (SmallAffineZariski B S hS)}
    {R : Sheaf J RingCat.{u + 1}} {M N : SheafOfModules.{u + 1} R} (h : M.val = N.val) : M ≅ N :=
  (SheafOfModules.fullyFaithfulForget R).preimageIso (eqToIso h)

/-- Regarding a module sheaf for the almost chaotic topology as one for the trivial topology and
back is the identity. -/
public noncomputable def trivialAlmostChaoticUnitIso :
    almostChaoticModulesToTrivial B S hS O ⋙ trivialModulesToAlmostChaotic B S hS O ≅
      𝟭 (SheafOfModules.{u + 1}
          (Stacks.SheafOfModules.Tensor.ringSheaf (almostChaoticRingedSite B S hS O).O)) :=
  NatIso.ofComponents (fun _ => moduleSheafIsoOfValEq B S hS rfl)
    fun _ => SheafOfModules.hom_ext rfl

/-- Regarding a module sheaf for the trivial topology as one for the almost chaotic topology and
back is the identity. -/
public noncomputable def almostChaoticTrivialCounitIso :
    trivialModulesToAlmostChaotic B S hS O ⋙ almostChaoticModulesToTrivial B S hS O ≅
      𝟭 (SheafOfModules.{u + 1}
          (Stacks.SheafOfModules.Tensor.ringSheaf (trivialRingedSite B S hS O).O)) :=
  NatIso.ofComponents (fun _ => moduleSheafIsoOfValEq B S hS rfl)
    fun _ => SheafOfModules.hom_ext rfl

/-- **Module sheaves for the almost chaotic topology are module sheaves for the trivial
topology.** Both are presheaves of modules whose sections vanish over an empty affine open. -/
public noncomputable def almostChaoticTrivialEquivalence :
    SheafOfModules.{u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf (almostChaoticRingedSite B S hS O).O) ≌
      SheafOfModules.{u + 1}
          (Stacks.SheafOfModules.Tensor.ringSheaf (trivialRingedSite B S hS O).O) where
  functor := almostChaoticModulesToTrivial B S hS O
  inverse := trivialModulesToAlmostChaotic B S hS O
  unitIso := (trivialAlmostChaoticUnitIso B S hS O).symm
  counitIso := almostChaoticTrivialCounitIso B S hS O
  functor_unitIso_comp _ := SheafOfModules.hom_ext rfl

/-- Regarding module sheaves for the trivial topology as module sheaves for the almost chaotic
topology is an additive functor. -/
public instance trivialModulesToAlmostChaotic_additive :
    (trivialModulesToAlmostChaotic B S hS O).Additive where
  map_add := SheafOfModules.hom_ext rfl

/-- Regarding module sheaves for the almost chaotic topology as module sheaves for the trivial
topology is an additive functor. -/
public instance almostChaoticModulesToTrivial_additive :
    (almostChaoticModulesToTrivial B S hS O).Additive :=
  Stacks.Sites.CoarserTopology.modulePushforward_additive (trivial_le_almostChaotic B S hS)
    (Stacks.SheafOfModules.Tensor.ringSheaf (almostChaoticRingedSite B S hS O).O)

/-- Regarding module sheaves for the trivial topology as module sheaves for the almost chaotic
topology is an equivalence. -/
public instance trivialModulesToAlmostChaotic_isEquivalence :
    (trivialModulesToAlmostChaotic B S hS O).IsEquivalence :=
  (almostChaoticTrivialEquivalence B S hS O).isEquivalence_inverse

/-- Regarding module sheaves for the almost chaotic topology as module sheaves for the trivial
topology is an equivalence. -/
public instance almostChaoticModulesToTrivial_isEquivalence :
    (almostChaoticModulesToTrivial B S hS O).IsEquivalence :=
  (almostChaoticTrivialEquivalence B S hS O).isEquivalence_functor

/-- The equivalence of derived categories induced by regarding a module sheaf for the almost
chaotic topology as one for the trivial topology. -/
public noncomputable abbrev almostChaoticModulesToTrivialDerived :
    DerivedCategory (SheafOfModules.{u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf (almostChaoticRingedSite B S hS O).O)) ⥤
      DerivedCategory (SheafOfModules.{u + 1}
          (Stacks.SheafOfModules.Tensor.ringSheaf (trivialRingedSite B S hS O).O)) :=
  (almostChaoticModulesToTrivial B S hS O).mapDerivedCategory

/-- The equivalence of derived categories induced by regarding a module sheaf for the trivial
topology as one for the almost chaotic topology. -/
public noncomputable abbrev trivialModulesToAlmostChaoticDerived :
    DerivedCategory (SheafOfModules.{u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf (trivialRingedSite B S hS O).O)) ⥤
      DerivedCategory (SheafOfModules.{u + 1}
          (Stacks.SheafOfModules.Tensor.ringSheaf (almostChaoticRingedSite B S hS O).O)) :=
  (trivialModulesToAlmostChaotic B S hS O).mapDerivedCategory

/-- Pushing a module sheaf for the Zariski topology forward to the trivial topology and
regarding it as a module sheaf for the almost chaotic topology is the pushforward to the almost
chaotic topology. -/
public noncomputable def modulePushforwardAlmostChaoticIso :
    Stacks.Sites.CoarserTopology.modulePushforward (trivial_le_topology B S hS)
          (Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite B S hS O).O) ⋙
        trivialModulesToAlmostChaotic B S hS O ≅
      Stacks.Sites.CoarserTopology.modulePushforward (almostChaotic_le_topology B S hS)
        (Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite B S hS O).O) :=
  NatIso.ofComponents (fun _ => moduleSheafIsoOfValEq B S hS rfl)
    fun _ => SheafOfModules.hom_ext rfl

/-- The canonical Mayer–Vietoris map of a square for the almost chaotic topology at a complex
regarded from the trivial topology is the canonical map for the trivial topology: the sections of
a module sheaf are the same for both topologies. -/
public lemma quasiIso_cSquare_almostChaotic_iff (sq : Square (SmallAffineZariski B S hS))
    (I : CochainComplex (SheafOfModules.{u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf (trivialRingedSite B S hS O).O)) ℤ) :
    QuasiIso (Stacks.Cohomology.MayerVietoris.cSquare
        (S := almostChaoticRingedSite B S hS O) sq
        (((trivialModulesToAlmostChaotic B S hS O).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj I)) ↔
      QuasiIso (Stacks.Cohomology.MayerVietoris.cSquare
        (S := trivialRingedSite B S hS O) sq I) :=
  Iff.rfl

/-- **The canonical Mayer–Vietoris map of a square is an isomorphism for the trivial topology
exactly when it is for the almost chaotic topology.** The two conditions are tested on a
K-injective representative, which the equivalence of the two categories of module sheaves
preserves, and on such a representative the two canonical maps coincide. -/
public lemma isCSquareIso_trivial_iff_almostChaotic (sq : Square (SmallAffineZariski B S hS))
    (K : DerivedCategory (SheafOfModules.{u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf (trivialRingedSite B S hS O).O))) :
    (Stacks.MayerVietoris.CanonicalMapOfComplexes.derivedCSquareData.{u + 1, u + 1}
        (R := (Stacks.SheafOfModules.Tensor.ringSheaf (trivialRingedSite B S hS O).O))
          sq).IsCSquareIso K ↔
      (Stacks.MayerVietoris.CanonicalMapOfComplexes.derivedCSquareData.{u + 1, u + 1}
          (R := (Stacks.SheafOfModules.Tensor.ringSheaf (almostChaoticRingedSite B S hS O).O))
            sq).IsCSquareIso
        ((trivialModulesToAlmostChaoticDerived B S hS O).obj K) := by
  obtain ⟨complex, injective, ⟨representative⟩⟩ :=
    Stacks.MayerVietoris.CanonicalMapOfComplexes.exists_kInjective_iso.{u + 1, u + 1}
      (R := (Stacks.SheafOfModules.Tensor.ringSheaf (trivialRingedSite B S hS O).O)) K
  have hfunctor : (almostChaoticTrivialEquivalence B S hS O).symm.functor.Additive :=
    trivialModulesToAlmostChaotic_additive B S hS O
  have hinverse : (almostChaoticTrivialEquivalence B S hS O).symm.inverse.Additive :=
    almostChaoticModulesToTrivial_additive B S hS O
  have hinjective : CochainComplex.IsKInjective
      (((trivialModulesToAlmostChaotic B S hS O).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj complex) :=
    CochainComplex.isKInjective_mapHomologicalComplex_of_equivalence
      (almostChaoticTrivialEquivalence B S hS O).symm complex
  have mappedRepresentative : DerivedCategory.Q.obj
      (((trivialModulesToAlmostChaotic B S hS O).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj complex) ≅
      (trivialModulesToAlmostChaoticDerived B S hS O).obj K :=
    ((trivialModulesToAlmostChaotic B S hS O).mapDerivedCategoryFactors.app complex).symm ≪≫
      (trivialModulesToAlmostChaotic B S hS O).mapDerivedCategory.mapIso representative
  exact ((Stacks.MayerVietoris.CanonicalMapOfComplexes.derivedCSquareData.{u + 1, u + 1}
        (R := (Stacks.SheafOfModules.Tensor.ringSheaf (trivialRingedSite B S hS O).O))
          sq).isCSquareIso_iff_quasiIso
      K complex representative).trans
    ((quasiIso_cSquare_almostChaotic_iff B S hS O sq complex).symm.trans
      ((Stacks.MayerVietoris.CanonicalMapOfComplexes.derivedCSquareData.{u + 1, u + 1}
          (R := (Stacks.SheafOfModules.Tensor.ringSheaf (almostChaoticRingedSite B S hS O).O))
            sq).isCSquareIso_iff_quasiIso
        ((trivialModulesToAlmostChaoticDerived B S hS O).obj K) _ mappedRepresentative).symm)

end Transfer

end AlgebraicGeometry.SmallAffineZariski

end
