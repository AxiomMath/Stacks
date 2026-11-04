module

public import StacksFrontier.Topology.Sheaves.Cohomology.InvertibleDerivedGlobalSplitting
public import StacksFrontier.Topology.Sheaves.Cohomology.InvertibleDerivedLocalTransport
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.LeftDualLocalCoevaluation
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.RestrictionToAnOpen
public import StacksFrontier.Topology.Sheaves.Cohomology.StrictlyPerfect.TensorProduct
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.TriangleLemmas
public import StacksFrontier.Topology.Sheaves.Cohomology.InvertibleDerivedClauseThreeConverse

/-!
# A chain-level tensor pairing of strictly perfect complexes splits locally

Let `P`, `P'` be strictly perfect complexes on a ringed space `X` and let
`a : 𝒪_X[0] ⟶ Tot(P ⊗ P')` and `b : Tot(P ⊗ P') ⟶ 𝒪_X[0]` be maps of complexes which are mutually
inverse in `D(𝒪_X)`. Then near every point the two composites are homotopic to the identities
(Stacks 08C9), so `Tot(P ⊗ P')` is homotopy equivalent to `𝒪_X[0]` there, and the cohomology of
`P` and `P'` splits there.

## References

* [Stacks Project, Tag 08C9](https://stacks.math.columbia.edu/tag/08C9)
* [Stacks Project, Tag 0FPG](https://stacks.math.columbia.edu/tag/0FPG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open StrictlyPerfect Stacks.SheafOfModules.DerivedMonoidal

universe u d

namespace Stacks.Cohomology.InvertibleDerived

section Generic

variable {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]

/-- A null-homotopy survives an isomorphism of additive functors. -/
public def homotopyZeroOfNatIso {F G : C ⥤ D} [F.Additive] [G.Additive] (e : F ≅ G)
    {A B : CochainComplex C ℤ} (f : A ⟶ B)
    (h : Homotopy ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map f) 0) :
    Homotopy ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map f) 0 := by
  let eC := NatIso.mapHomologicalComplex e (ComplexShape.up ℤ)
  refine (Homotopy.ofEq ?_).trans
    (((h.compLeft (eC.inv.app A)).compRight (eC.hom.app B)).trans (Homotopy.ofEq ?_))
  · rw [Category.assoc, eC.hom.naturality f, ← Category.assoc, eC.inv_hom_id_app,
      Category.id_comp]
  · simp

/-- Two maps of complexes whose composites are null-homotopic up to the identities, after an
additive functor, are a homotopy equivalence there. -/
public def homotopyEquivOfNullHomotopic (F : C ⥤ D) [F.Additive] {A B : CochainComplex C ℤ}
    (a : A ⟶ B) (b : B ⟶ A)
    (h₁ : Homotopy ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map (a ≫ b - 𝟙 A)) 0)
    (h₂ : Homotopy ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map (b ≫ a - 𝟙 B)) 0) :
    HomotopyEquiv ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj A)
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj B) where
  hom := (F.mapHomologicalComplex (ComplexShape.up ℤ)).map a
  inv := (F.mapHomologicalComplex (ComplexShape.up ℤ)).map b
  homotopyHomInvId := Homotopy.equivSubZero.symm
    ((Homotopy.ofEq (by
      rw [Functor.map_sub, Functor.map_comp, CategoryTheory.Functor.map_id])).trans h₁)
  homotopyInvHomId := Homotopy.equivSubZero.symm
    ((Homotopy.ofEq (by
      rw [Functor.map_sub, Functor.map_comp, CategoryTheory.Functor.map_id])).trans h₂)

end Generic

/-- A complex with finitely many nonzero terms vanishes outside an interval. -/
public theorem exists_bounds {C : Type*} [Category* C] [HasZeroMorphisms C]
    (E : CochainComplex C ℤ) (h : {i | ¬ IsZero (E.X i)}.Finite) :
    ∃ a b : ℤ, ∀ i, (i < a ∨ b < i) → IsZero (E.X i) := by
  obtain ⟨a, ha⟩ := h.bddBelow
  obtain ⟨b, hb⟩ := h.bddAbove
  refine ⟨a, b, fun i hi => ?_⟩
  by_contra hz
  rcases hi with hi | hi
  · exact absurd (ha hz) (not_le.mpr hi)
  · exact absurd (hb hz) (not_le.mpr hi)

variable {X : RingedSpace.{u, u}}

/-- Null-homotopies restrict to smaller opens. -/
public theorem nonempty_homotopy_zero_of_le {U V : Opens X.carrier} (h : V ≤ U)
    {A B : CochainComplex (OXMod.{u, u} X) ℤ} (f : A ⟶ B)
    (hU : Nonempty (Homotopy (((restrictModules X U).mapHomologicalComplex
      (ComplexShape.up ℤ)).map f) 0)) :
    Nonempty (Homotopy (((restrictModules X V).mapHomologicalComplex
      (ComplexShape.up ℤ)).map f) 0) := by
  obtain ⟨hU⟩ := hU
  exact ⟨homotopyZeroOfNatIso (RingedSpace.restrictModulesOfLECompIso X h) f
    (((RingedSpace.restrictModulesOfLE X h).mapHomotopy hU).trans
      (Homotopy.ofEq (Functor.map_zero _ _ _)))⟩

/-- The restriction of the unit complex is the unit complex. -/
public def restrictUnitComplexIso (V : Opens X.carrier) :
    ((restrictModules X V).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (LeftDualPerfect.unitComplex X) ≅
      (HomologicalComplex.single (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
        (X.restrict V.isOpenEmbedding).sheaf)) (ComplexShape.up ℤ) 0).obj
        (SheafOfModules.unit _) :=
  (HomologicalComplex.singleMapHomologicalComplex (restrictModules X V) (ComplexShape.up ℤ)
    0).app _ ≪≫ (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).mapIso (restrictUnitIso V)

/-- The restriction of a complex, as a complex over the ring sheaf of the open subspace. -/
public abbrev restrictComplexR (V : Opens X.carrier) (P : CochainComplex (OXMod.{u, u} X) ℤ) :
    CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (X.restrict V.isOpenEmbedding).sheaf)) ℤ :=
  RingedSpace.restrictComplex P V

/-- A homotopy equivalence between the restrictions of the total tensor complex and of the unit
complex, read on the restricted complexes. -/
public def restrictedPairing (V : Opens X.carrier) (P P' : CochainComplex (OXMod.{u, u} X) ℤ)
    (heq : HomotopyEquiv (RingedSpace.restrictComplex
      (((Stacks.SheafOfModules.Tensor.tensorComplex X.sheaf).obj P).obj P') V)
      (((restrictModules X V).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (LeftDualPerfect.unitComplex X))) :
    HomotopyEquiv (HomologicalComplex.mapBifunctor (restrictComplexR V P) (restrictComplexR V P')
      (Stacks.SheafOfModules.Tensor.sheafTensor (X.restrict V.isOpenEmbedding).sheaf)
      (ComplexShape.up ℤ))
      ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj (SheafOfModules.unit _)) :=
  (HomotopyEquiv.ofIso
    (Stacks.Cohomology.RestrictionTensor.restrictComplexTensorIso X V P P').symm).trans
    (heq.trans (HomotopyEquiv.ofIso (restrictUnitComplexIso V)))

variable (X) in
/-- **A chain-level tensor pairing of strictly perfect complexes splits locally.** -/
public theorem exists_localSplitting_of_chainPairing [inst : HasDerivedCategory.{d} (Mod X.sheaf)]
    (P P' : CochainComplex (OXMod.{u, u} X) ℤ) (hP : IsStrictlyPerfect P)
    (hP' : IsStrictlyPerfect P')
    (a : LeftDualPerfect.unitComplex X ⟶
      ((Stacks.SheafOfModules.Tensor.tensorComplex X.sheaf).obj P).obj P')
    (b : ((Stacks.SheafOfModules.Tensor.tensorComplex X.sheaf).obj P).obj P' ⟶
      LeftDualPerfect.unitComplex X)
    (hab : DerivedCategory.Q.map (a ≫ b) = 𝟙 _) (hba : DerivedCategory.Q.map (b ≫ a) = 𝟙 _)
    (x : X.carrier) : ∃ V : Opens X.carrier, x ∈ V ∧ Nonempty (LocalSplitting P P' V) := by
  have hT := StrictlyPerfect.isStrictlyPerfect_tensorComplex X P P' hP hP'
  let : HasDerivedCategory.{d} (OXMod.{u, u} X) := inst
  have key := fun {E : CochainComplex (OXMod.{u, u} X) ℤ} (hE : IsStrictlyPerfect E) (e : E ⟶ E)
      (he : DerivedCategory.Q.map e = 𝟙 _) =>
    RingedSpace.exists_local_homotopy_zero_of_derived_eq_zero (e - 𝟙 _) hE (by simp [he]) x
  obtain ⟨V₁, hx₁, hh₁⟩ := key (LeftDualPerfect.isStrictlyPerfect_unitComplex X) _ hab
  obtain ⟨V₂, hx₂, hh₂⟩ := key hT _ hba
  obtain ⟨k₁⟩ := nonempty_homotopy_zero_of_le (inf_le_left : V₁ ⊓ V₂ ≤ V₁) _
    (RingedSpace.nonempty_homotopy_zero_restrictModules V₁ _ hh₁)
  obtain ⟨k₂⟩ := nonempty_homotopy_zero_of_le (inf_le_right : V₁ ⊓ V₂ ≤ V₂) _
    (RingedSpace.nonempty_homotopy_zero_restrictModules V₂ _ hh₂)
  let V := V₁ ⊓ V₂
  let h := restrictedPairing V P P' (homotopyEquivOfNullHomotopic (restrictModules X V) b a k₂ k₁)
  obtain ⟨a₀, b₀, hz⟩ := exists_bounds P hP.bounded
  obtain ⟨a₀', b₀', hz'⟩ := exists_bounds P' hP'.bounded
  obtain ⟨A⟩ := nonempty_localSplitting_top (X.restrict V.isOpenEmbedding) (restrictComplexR V P)
    (restrictComplexR V P')
    (fun i => RingedSpace.isDirectSummandOfFiniteFree_restrictModules V (hP.directSummand i))
    (fun i => RingedSpace.isDirectSummandOfFiniteFree_restrictModules V (hP'.directSummand i))
    a₀ b₀ a₀' b₀' (fun i hi => (restrictModules X V).map_isZero (hz i hi))
    (fun i hi => (restrictModules X V).map_isZero (hz' i hi)) h
  exact ⟨V.isOpenEmbedding.functor.obj ⊤, ⟨⟨x, ⟨hx₁, hx₂⟩⟩, trivial, rfl⟩,
    ⟨LocalSplitting.transport V (fun k => (restrictModulesHomologyIso P V k).symm)
      (fun k => (restrictModulesHomologyIso P' V k).symm) A⟩⟩

end Stacks.Cohomology.InvertibleDerived

end
