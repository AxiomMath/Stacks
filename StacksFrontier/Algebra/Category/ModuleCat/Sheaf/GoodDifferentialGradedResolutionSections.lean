module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedSectionAdmissible
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedSectionDatum
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreeDifferentialGradedModuleSectionBasis
public import StacksFrontier.Algebra.DifferentialGraded.Module.OrthogonalAcyclic

/-!
# Resolutions whose sections are K-projective, on a chaotic site

Let `C` be a category carrying the chaotic topology, let `O` be a sheaf of commutative rings on
it and let `A` be a sheaf of differential graded `O`-algebras. The tower of the first proof of
Tag 0FSH resolves every right differential graded `A`-module `M` by a module `P` which is flat as
a graded module and K-flat. On the chaotic site it does more: for every object `U`, the
differential graded `A(U)`-module `P(U)` of sections lies in the left orthogonal of the acyclic
objects of the homotopy category `K(A(U))` — it is K-projective over the section algebra.

The proof re-runs the tower with this extra invariant:

* the first stage is a free module `A[S]`, whose sections are a direct sum of shifts of the
  regular module of `A(U)`
  (`SheafOfModules.leftOrthogonal_acyclic'_sectionModule_freeDGModule`);
* each further stage is a twisted extension `0 → P → P[S, c] → A[S][1] → 0`, an admissible short
  exact sequence; taking sections keeps it admissible
  (`SheafOfModules.DifferentialGradedModule.IsAdmissibleShortExact.sectionMap`), the sections of
  `A[S][1]` are the shift of those of `A[S]`, and the left orthogonal is closed under extensions;
* the resolution is the colimit of the stages, and evaluation at an object of a chaotic site
  commutes with colimits, so its sections are the union of the sections of the stages along
  admissible inclusions; the telescope argument of Tag 09KL closes the left orthogonal under such
  unions.

## Main results

* `SheafOfModules.DifferentialGradedModule.leftOrthogonal_sectionModule_of_isColimit_nat`: the
  sections of the colimit of a sequence of admissible inclusions, with bottom stage and
  successive quotients K-projective sectionwise, are K-projective.
* `SheafOfModules.DifferentialGradedModule.exists_flat_quasiIso_sectionwise`: **every right
  differential graded `A`-module receives a quasi-isomorphism from one which is flat as a graded
  module, K-flat, and whose sections over every object are left orthogonal to the acyclic
  differential graded modules over the section algebra.**

## Main definitions

* `SheafOfModules.DifferentialGradedModule.chaoticSectionGoodModuleData`: the flat-resolution
  theory of `A` on `derivedCategory A` whose good modules are flat as graded modules, K-flat,
  and K-projective sectionwise.

## Implementation notes

The left orthogonal is taken for `_root_.DifferentialGradedModule.acyclic'`, the class of acyclic
objects of the homotopy category of differential graded modules at a single universe, which is
where the section algebras live: their coefficient ring is `ULift ℤ` and their modules are in
the universe of the sections. It agrees with the universe-polymorphic class
`_root_.DifferentialGradedModule.acyclic` by definition
(`_root_.DifferentialGradedModule.acyclic'_eq_acyclic`), which is what lets the telescope
argument, stated at independent universes, be applied.

For the colimit, the sections over `U` of the degree-`n` piece are read as a functor to types
through the sheaves of abelian groups, which on the chaotic topology are presheaves: that functor
preserves colimits over `ℕ`, so the sections of the colimit are jointly reached by the stages and
an element dies in the colimit only if it dies at a later stage. The transition maps are
injective on sections, being split by the retractions of the admissible short exact sequences.

## References

* [Stacks Project, Tag 0FSH](https://stacks.math.columbia.edu/tag/0FSH)
* [Stacks Project, Tag 09KL](https://stacks.math.columbia.edu/tag/09KL)
* [Stacks Project, Tag 09KM](https://stacks.math.columbia.edu/tag/09KM)
* [Stacks Project, Tag 0149](https://stacks.math.columbia.edu/tag/0149)
* [Stacks Project, Tag 0FSA](https://stacks.math.columbia.edu/tag/0FSA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf

universe t m v u

namespace SheafOfModules.DifferentialGradedModule

open Stacks Stacks.SheafOfGradedSets

attribute [local instance] GradedAlgebra.sectionsGOne GradedAlgebra.sectionsGMul
  GradedAlgebra.sectionsGRing Stacks.uliftIntAlgebra
  Stacks.SheafOfModules.botWEqualsLocallyBijective

variable {C : Type u} [Category.{v} C]
  [(⊥ : GrothendieckTopology C).HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})]
  [HasWeakSheafify (⊥ : GrothendieckTopology C) (Type m)]
  [HasSheafify (⊥ : GrothendieckTopology C) AddCommGrpCat.{m}]
  {Osharp : Sheaf (⊥ : GrothendieckTopology C) CommRingCat.{t}}
  {A : DifferentialGradedAlgebra.{t, m} (Stacks.SheafOfModules.Tensor.ringSheaf Osharp)}

/-! ### The stages of the tower -/

omit [(⊥ : GrothendieckTopology C).HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})] in
/-- **The sections of the shift of a free module are K-projective**: they are the shift of the
sections of the free module, which have a basis of closed homogeneous elements. -/
theorem leftOrthogonal_sectionModule_shift_freeDGModule
    (S : SheafOfGradedSets.{m} (⊥ : GrothendieckTopology C)) (U : Cᵒᵖ) :
    (_root_.DifferentialGradedModule.acyclic' (A.sectionAlgebra U)).leftOrthogonal
      ((_root_.DifferentialGradedModule.toHomotopyCategory (A.sectionAlgebra U)).obj
        ((shift (freeDGModule S A)).sectionModule U)) := by
  obtain ⟨e⟩ := nonempty_sectionModule_shifted_iso (freeDGModule S A)
    (shiftPackage (freeDGModule S A)) U
  exact _root_.DifferentialGradedModule.leftOrthogonal_acyclic_of_iso _ e.symm
    (_root_.DifferentialGradedModule.leftOrthogonal_acyclic'_of_isClosedBasis
      ((isClosedBasis_freeSectionGenerator S A U).shift 1))

/-- **One step of the tower keeps the sections K-projective.** The sections of a twisted
extension `P[S, c]` sit in the admissible short exact sequence `0 → P(U) → P[S, c](U) → A[S][1](U)
→ 0`, whose outer terms are K-projective when `P(U)` is. -/
theorem leftOrthogonal_sectionModule_twistedExtension
    (S : SheafOfGradedSets.{m} (⊥ : GrothendieckTopology C))
    (P : DifferentialGradedModule.{t, m, m} A)
    (c : GradedGeneratorFamily S (GradedModule.ofDifferentialGraded P))
    (hc : ∀ (n : ℤ) (U : Cᵒᵖ) (s : S.sheaf.obj.obj U) (hs : S.HasDegree U s n),
      homSections (P.complex.d n (n + 1)) U (c.app n U s hs) = 0) (U : Cᵒᵖ)
    (hP : (_root_.DifferentialGradedModule.acyclic' (A.sectionAlgebra U)).leftOrthogonal
      ((_root_.DifferentialGradedModule.toHomotopyCategory (A.sectionAlgebra U)).obj
        (P.sectionModule U))) :
    (_root_.DifferentialGradedModule.acyclic' (A.sectionAlgebra U)).leftOrthogonal
      ((_root_.DifferentialGradedModule.toHomotopyCategory (A.sectionAlgebra U)).obj
        ((twistedExtension S P c hc).sectionModule U)) :=
  _root_.DifferentialGradedModule.leftOrthogonal_acyclic_of_isAdmissibleShortExact _
    (sectionMap (twistedExtensionInclusion S P c hc) U)
    (sectionMap (twistedExtensionProjection S P c hc) U)
    ((twistedExtension_isAdmissibleShortExact S P c hc).sectionMap U) hP
    (leftOrthogonal_sectionModule_shift_freeDGModule S U)

/-! ### The colimit -/

/-- **The sections over `U` of the degree-`n` piece**, as a functor to types, read through the
sheaves of abelian groups. -/
def pieceSectionsFunctor (n : ℤ) (U : Cᵒᵖ) :
    DifferentialGradedModule.{t, m, m} A ⥤ Type m :=
  (forgetToGradedModule A ⋙ GradedModule.pieceFunctor A.toGradedAlgebra n) ⋙
    (SheafOfModules.toSheaf.{m} (Stacks.SheafOfModules.Tensor.ringSheaf Osharp) ⋙
      (sheafBotEquivalence (C := C) AddCommGrpCat.{m}).functor ⋙
        (CategoryTheory.evaluation Cᵒᵖ AddCommGrpCat.{m}).obj U ⋙
          CategoryTheory.forget AddCommGrpCat.{m})

omit [(⊥ : GrothendieckTopology C).HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})]
  [HasWeakSheafify (⊥ : GrothendieckTopology C) (Type m)] in
/-- On a chaotic site, reading the sections over `U` of the degree-`n` piece commutes with
colimits over `ℕ`. -/
theorem preservesColimitsOfShape_pieceSectionsFunctor (n : ℤ) (U : Cᵒᵖ) :
    PreservesColimitsOfShape ℕ (pieceSectionsFunctor (A := A) n U) := by
  unfold pieceSectionsFunctor
  have h1 : PreservesColimitsOfShape ℕ
      (GradedModule.pieceFunctor A.toGradedAlgebra n :
        GradedModule.{t, m, m} A.toGradedAlgebra ⥤
          SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf Osharp)) :=
    have : PreservesColimitsOfSize.{m, m}
        (GradedModule.pieceFunctor A.toGradedAlgebra n :
          GradedModule.{t, m, m} A.toGradedAlgebra ⥤
            SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf Osharp)) :=
      GradedModule.pieceFunctor_preservesColimitsOfSize' n
    (preservesSmallestColimits_of_preservesColimits _).preservesColimitsOfShape
  have h2 : PreservesColimitsOfShape (AsSmall.{m} ℕ)
      (SheafOfModules.toSheaf.{m} (Stacks.SheafOfModules.Tensor.ringSheaf Osharp) ⋙
        (sheafBotEquivalence (C := C) AddCommGrpCat.{m}).functor ⋙
          (CategoryTheory.evaluation Cᵒᵖ AddCommGrpCat.{m}).obj U ⋙
            CategoryTheory.forget AddCommGrpCat.{m}) := by
    have : PreservesColimitsOfShape (AsSmall.{m} ℕ)
        (SheafOfModules.toSheaf.{m} (Stacks.SheafOfModules.Tensor.ringSheaf Osharp)) :=
      (preservesColimitsOfSize_of_univLE.{max u m, m, m, m}
        (SheafOfModules.toSheaf.{m}
          (Stacks.SheafOfModules.Tensor.ringSheaf Osharp))).preservesColimitsOfShape
    infer_instance
  have h3 := preservesColimitsOfShape_of_equiv asSmallNatEquiv.{m}
    (SheafOfModules.toSheaf.{m} (Stacks.SheafOfModules.Tensor.ringSheaf Osharp) ⋙
      (sheafBotEquivalence (C := C) AddCommGrpCat.{m}).functor ⋙
        (CategoryTheory.evaluation Cᵒᵖ AddCommGrpCat.{m}).obj U ⋙
          CategoryTheory.forget AddCommGrpCat.{m})
  infer_instance

omit [(⊥ : GrothendieckTopology C).HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})]
  [HasWeakSheafify (⊥ : GrothendieckTopology C) (Type m)]
  [HasSheafify (⊥ : GrothendieckTopology C) AddCommGrpCat.{m}] in
/-- On sections, the legs of a cocone commute with the transition maps. -/
private theorem sectionMap_ι_app_map {J : Type*} [Category J]
    {P : J ⥤ DifferentialGradedModule.{t, m, m} A} (c : Cocone P) {i j : J} (f : i ⟶ j)
    (U : Cᵒᵖ) (x : (P.obj i).totalSections U) :
    (sectionMap (c.ι.app j) U).toFun ((sectionMap (P.map f) U).toFun x) =
      (sectionMap (c.ι.app i) U).toFun x := by
  change totalSectionsMap U (fun n ↦ (c.ι.app j).toHomologicalComplex.f n)
      (totalSectionsMap U (fun n ↦ (P.map f).toHomologicalComplex.f n) x) =
    totalSectionsMap U (fun n ↦ (c.ι.app i).toHomologicalComplex.f n) x
  rw [← totalSectionsMap_comp]
  exact totalSectionsMap_congr U (fun n ↦ by
    rw [← HomologicalComplex.comp_f]
    exact congrArg (fun φ ↦ HomologicalComplex.Hom.f φ n)
      (congrArg Hom.toHomologicalComplex (c.w f))) x

omit [(⊥ : GrothendieckTopology C).HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})]
  [HasWeakSheafify (⊥ : GrothendieckTopology C) (Type m)]
  [HasSheafify (⊥ : GrothendieckTopology C) AddCommGrpCat.{m}] in
/-- The transition maps of a sequence of admissible inclusions are injective on the sections of
every piece. -/
private theorem injective_sectionsPiece_map {P : ℕ ⥤ DifferentialGradedModule.{t, m, m} A}
    {Q : ℕ → DifferentialGradedModule.{t, m, m} A} {q : ∀ i, P.obj (i + 1) ⟶ Q i}
    (hses : ∀ i, IsAdmissibleShortExact (P.map (homOfLE (Nat.le_succ i))) (q i)) (U : Cᵒᵖ)
    (n : ℤ) {i j : ℕ} (f : i ⟶ j) :
    Function.Injective (fun y : (P.obj i).sectionsPiece U n ↦
      ((P.map f).toHomologicalComplex.f n).val.app U y) := by
  have h₁ : ∀ i : ℕ, Function.Injective
      (fun y : (P.obj i).sectionsPiece U n ↦
        ((P.map (homOfLE (Nat.le_succ i))).toHomologicalComplex.f n).val.app U y) := by
    intro i y y' hyy'
    have h := ((hses i).sectionMap U).injective
      (a₁ := DirectSum.of ((P.obj i).sectionsPiece U) n y)
      (a₂ := DirectSum.of ((P.obj i).sectionsPiece U) n y') (by
        rw [sectionMap_toFun_apply, sectionMap_toFun_apply, totalSectionsMap_of,
          totalSectionsMap_of]
        exact congrArg _ hyy')
    exact DirectSum.of_injective n h
  induction j, (leOfHom f) using Nat.le_induction with
  | base =>
      rw [Subsingleton.elim f (𝟙 i), P.map_id]
      exact fun y y' h ↦ h
  | succ j hij ih =>
      rw [Subsingleton.elim f (homOfLE hij ≫ homOfLE (Nat.le_succ j)), P.map_comp]
      exact (h₁ j).comp (ih (homOfLE hij))

omit [(⊥ : GrothendieckTopology C).HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})]
  [HasWeakSheafify (⊥ : GrothendieckTopology C) (Type m)] in
/-- **The sections of the colimit of a sequence of admissible inclusions are K-projective** as
soon as those of the bottom stage and of the successive quotients are. Evaluation at an object of
a chaotic site commutes with colimits, so the sections of the colimit are the union of the
sections of the stages, along the inclusions — injective, and admissible on sections, being split
— and Tag 09KL applies to that exhaustive filtration. -/
theorem leftOrthogonal_sectionModule_of_isColimit_nat
    {P : ℕ ⥤ DifferentialGradedModule.{t, m, m} A} {c : Cocone P} (hc : IsColimit c)
    (Q : ℕ → DifferentialGradedModule.{t, m, m} A) (q : ∀ i, P.obj (i + 1) ⟶ Q i)
    (hses : ∀ i, IsAdmissibleShortExact (P.map (homOfLE (Nat.le_succ i))) (q i)) (U : Cᵒᵖ)
    (h0 : (_root_.DifferentialGradedModule.acyclic' (A.sectionAlgebra U)).leftOrthogonal
      ((_root_.DifferentialGradedModule.toHomotopyCategory (A.sectionAlgebra U)).obj
        ((P.obj 0).sectionModule U)))
    (hQ : ∀ i, (_root_.DifferentialGradedModule.acyclic' (A.sectionAlgebra U)).leftOrthogonal
      ((_root_.DifferentialGradedModule.toHomotopyCategory (A.sectionAlgebra U)).obj
        ((Q i).sectionModule U))) :
    (_root_.DifferentialGradedModule.acyclic' (A.sectionAlgebra U)).leftOrthogonal
      ((_root_.DifferentialGradedModule.toHomotopyCategory (A.sectionAlgebra U)).obj
        (c.pt.sectionModule U)) := by
  classical
  have hsesU := fun i ↦ (hses i).sectionMap U
  -- the embeddings of the stages into the colimit, on sections
  let emb : ∀ i, (P.obj i).sectionModule U ⟶ c.pt.sectionModule U := fun i ↦
    sectionMap (c.ι.app i) U
  -- the sections of each piece of the colimit are the colimit of the sections of the stages
  have hcn : ∀ n : ℤ, IsColimit ((pieceSectionsFunctor n U).mapCocone c) := fun n ↦
    have := preservesColimitsOfShape_pieceSectionsFunctor (A := A) n U
    isColimitOfPreserves (pieceSectionsFunctor (A := A) n U) hc
  -- the embeddings of the stages are injective
  have hemb : ∀ i, Function.Injective (emb i).toFun := fun i ↦ by
    change Function.Injective (totalSectionsMap U fun n ↦ (c.ι.app i).toHomologicalComplex.f n)
    refine (DirectSum.map_injective _).2 fun n y y' hyy' ↦ ?_
    obtain ⟨j, f, hf⟩ := (Types.FilteredColimit.isColimit_eq_iff' (hcn n)
      (show (P ⋙ pieceSectionsFunctor n U).obj i from y)
      (show (P ⋙ pieceSectionsFunctor n U).obj i from y')).1 hyy'
    exact injective_sectionsPiece_map hses U n f hf
  -- the filtration is exhaustive
  have hexh : ∀ x : c.pt.totalSections U, ∃ i y, (emb i).toFun y = x := fun x ↦ by
    induction x using DirectSum.induction_on with
    | zero => exact ⟨0, 0, map_zero _⟩
    | of n y =>
        obtain ⟨j, z, hz⟩ := Types.jointly_surjective_of_isColimit (hcn n)
          (show ((pieceSectionsFunctor n U).mapCocone c).pt from y)
        refine ⟨j, DirectSum.of ((P.obj j).sectionsPiece U) n
          (show (P.obj j).sectionsPiece U n from z), ?_⟩
        rw [sectionMap_toFun_apply, totalSectionsMap_of]
        exact congrArg _ hz
    | add x x' hx hx' =>
        obtain ⟨i, y, rfl⟩ := hx
        obtain ⟨i', y', rfl⟩ := hx'
        exact ⟨max i i', (sectionMap (P.map (homOfLE (le_max_left i i'))) U).toFun y +
          (sectionMap (P.map (homOfLE (le_max_right i i'))) U).toFun y',
          (map_add _ _ _).trans (congrArg₂ (· + ·) (sectionMap_ι_app_map c _ U y)
            (sectionMap_ι_app_map c _ U y'))⟩
  exact _root_.DifferentialGradedModule.General.leftOrthogonal_acyclic_of_admissibleFiltration
    (fun i ↦ (P.obj i).sectionModule U) (fun i ↦ (Q i).sectionModule U)
    emb (fun i ↦ sectionMap (P.map (homOfLE (Nat.le_succ i))) U)
    (fun i ↦ sectionMap (q i) U) hemb (fun i x ↦ sectionMap_ι_app_map c _ U x)
    (fun i ↦ (hsesU i).admissibleMono)
    (fun i ↦ (hsesU i).surjective) (fun i ↦ (hsesU i).exact.symm) hexh h0 hQ

/-! ### The resolution -/

/-- **One step of the tower, keeping the sections K-projective.** From a right differential
graded `A`-module `P` which is flat as a graded module, K-flat and K-projective sectionwise,
with a homomorphism `τ : P ⟶ M`, the next stage `towerStep τ` has the same three properties,
receives `P` by an admissible inclusion whose cokernel is K-projective sectionwise, carries a
homomorphism to `M` extending `τ`, and annihilates every class of `Hⁿ(P)` which dies in
`Hⁿ(M)`. -/
theorem exists_towerStep_sectionwise {M P : DifferentialGradedModule.{t, m, m} A} (τ : P ⟶ M)
    (hP : (RelativeTensor.IsGradedFlat (GradedModule.ofDifferentialGraded P) ∧
      RelativeTensor.IsKFlat P) ∧
      ∀ U : Cᵒᵖ, (_root_.DifferentialGradedModule.acyclic' (A.sectionAlgebra U)).leftOrthogonal
        ((_root_.DifferentialGradedModule.toHomotopyCategory (A.sectionAlgebra U)).obj
          (P.sectionModule U))) :
    ∃ (Q : DifferentialGradedModule.{t, m, m} A) (σ : Q ⟶ M) (i : P ⟶ Q)
      (Q' : DifferentialGradedModule.{t, m, m} A) (q : Q ⟶ Q'),
      ((RelativeTensor.IsGradedFlat (GradedModule.ofDifferentialGraded Q) ∧
          RelativeTensor.IsKFlat Q) ∧
        ∀ U : Cᵒᵖ, (_root_.DifferentialGradedModule.acyclic' (A.sectionAlgebra U)).leftOrthogonal
          ((_root_.DifferentialGradedModule.toHomotopyCategory (A.sectionAlgebra U)).obj
            (Q.sectionModule U))) ∧
      i ≫ σ = τ ∧
      (∀ (n : ℤ) (Z : SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf Osharp))
          (g : Z ⟶ P.complex.homology n),
          g ≫ HomologicalComplex.homologyMap τ.toHomologicalComplex n = 0 →
            g ≫ HomologicalComplex.homologyMap i.toHomologicalComplex n = 0) ∧
      IsAdmissibleShortExact i q ∧
      ∀ U : Cᵒᵖ, (_root_.DifferentialGradedModule.acyclic' (A.sectionAlgebra U)).leftOrthogonal
        ((_root_.DifferentialGradedModule.toHomotopyCategory (A.sectionAlgebra U)).obj
          (Q'.sectionModule U)) :=
  ⟨towerStep τ, towerStepMap τ, towerStepInclusion τ,
    shift (freeDGModule (boundaryPairs τ.toHomologicalComplex) A),
    twistedExtensionProjection (boundaryPairs τ.toHomologicalComplex) P (boundaryPairFamily τ)
      (boundaryPairFamily_closed τ),
    ⟨⟨twistedExtension_isGradedFlat (boundaryPairs τ.toHomologicalComplex) P
        (boundaryPairFamily τ) (boundaryPairFamily_closed τ) hP.1.1,
      twistedExtension_isKFlat (boundaryPairs τ.toHomologicalComplex) P (boundaryPairFamily τ)
        (boundaryPairFamily_closed τ) hP.1.2⟩,
      fun U ↦ leftOrthogonal_sectionModule_twistedExtension _ P _ _ U (hP.2 U)⟩,
    twistedExtensionInclusion_towerStepMap τ,
    fun n _ g hg ↦ comp_homologyMap_towerStepInclusion_eq_zero τ n g hg,
    twistedExtension_isAdmissibleShortExact _ P _ _,
    fun U ↦ leftOrthogonal_sectionModule_shift_freeDGModule _ U⟩

/-- **On a chaotic site, every right differential graded `A`-module receives a
quasi-isomorphism from a right differential graded `A`-module which is flat as a graded module,
K-flat, and whose sections over every object `U` are left orthogonal to the acyclic
differential graded `A(U)`-modules.**

The tower of the first proof of Tag 0FSH is built from `M` alone: the free module on the closed
sections of `M`, then the twisted extensions by the free modules on the boundary pairs of each
stage, then the colimit. The sections of every stage are K-projective, and so are those of the
colimit. -/
theorem exists_flat_quasiIso_sectionwise (M : DifferentialGradedModule.{t, m, m} A) :
    ∃ (Q : DifferentialGradedModule.{t, m, m} A) (f : Q ⟶ M),
      QuasiIso f.toHomologicalComplex ∧
      RelativeTensor.IsGradedFlat (GradedModule.ofDifferentialGraded Q) ∧
      RelativeTensor.IsKFlat Q ∧
      ∀ U : Cᵒᵖ, (_root_.DifferentialGradedModule.acyclic' (A.sectionAlgebra U)).leftOrthogonal
        ((_root_.DifferentialGradedModule.toHomotopyCategory (A.sectionAlgebra U)).obj
          (Q.sectionModule U)) := by
  classical
  let Stage := {p : Σ P : DifferentialGradedModule.{t, m, m} A, P ⟶ M //
    (RelativeTensor.IsGradedFlat (GradedModule.ofDifferentialGraded p.1) ∧
      RelativeTensor.IsKFlat p.1) ∧
    ∀ U : Cᵒᵖ, (_root_.DifferentialGradedModule.acyclic' (A.sectionAlgebra U)).leftOrthogonal
      ((_root_.DifferentialGradedModule.toHomotopyCategory (A.sectionAlgebra U)).obj
        (p.1.sectionModule U))}
  have step : ∀ r : Stage, ∃ (r' : Stage) (i : r.1.1 ⟶ r'.1.1)
      (Q' : DifferentialGradedModule.{t, m, m} A) (q : r'.1.1 ⟶ Q'),
      i ≫ r'.1.2 = r.1.2 ∧
      (∀ (n : ℤ) (Z : SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf Osharp))
          (g : Z ⟶ (r.1.1).complex.homology n),
          g ≫ HomologicalComplex.homologyMap r.1.2.toHomologicalComplex n = 0 →
            g ≫ HomologicalComplex.homologyMap i.toHomologicalComplex n = 0) ∧
      IsAdmissibleShortExact i q ∧
      ∀ U : Cᵒᵖ, (_root_.DifferentialGradedModule.acyclic' (A.sectionAlgebra U)).leftOrthogonal
        ((_root_.DifferentialGradedModule.toHomotopyCategory (A.sectionAlgebra U)).obj
          (Q'.sectionModule U)) := by
    rintro ⟨⟨P, τ⟩, hP⟩
    obtain ⟨Q, σ, i, Q', q, hQ, hcomm, hkill, hses, hQ'⟩ := exists_towerStep_sectionwise τ hP
    exact ⟨⟨⟨Q, σ⟩, hQ⟩, i, Q', q, hcomm, hkill, hses, hQ'⟩
  choose next transition quot quotMap hcomm hkill hses hquot using step
  let r₀ : Stage := ⟨⟨freeDGModule (closedSections M.complex) A, freeOnClosedSectionsHom M⟩,
    ⟨freeDGModule_isGradedFlat A (closedSections M.complex),
      freeDGModule_isKFlat (closedSections M.complex) A⟩,
    fun U ↦ leftOrthogonal_acyclic'_sectionModule_freeDGModule (closedSections M.complex) A U⟩
  let r : ℕ → Stage := Nat.rec r₀ fun _ x ↦ next x
  let gg (n : ℕ) : (r n).1.1 ⟶ (r (n + 1)).1.1 := transition (r n)
  let F : ℕ ⥤ DifferentialGradedModule.{t, m, m} A := Functor.ofSequence gg
  have hF : ∀ n, F.map (homOfLE (Nat.le_succ n)) = gg n :=
    Functor.ofSequence_map_homOfLE_succ gg
  let c : Cocone F := ⟨M, NatTrans.ofSequence (F := F) (fun n ↦ (r n).1.2) fun n ↦ by
    change F.map (homOfLE (Nat.le_succ n)) ≫ (r (n + 1)).1.2 = (r n).1.2 ≫ 𝟙 M
    rw [hF n, Category.comp_id]
    exact hcomm (r n)⟩
  have : HasColimitsOfShape ℕ (DifferentialGradedModule.{t, m, m} A) := hasColimitsOfShape_nat
  have hflat := isGradedFlat_and_isKFlat_of_isColimit_nat (colimit.isColimit F)
    (fun i ↦ (r i).2.1)
  refine ⟨colimit F, (colimit.isColimit F).desc c,
    quasiIso_desc_of_tower F (colimit.isColimit F) c
      (fun n ↦ epi_homologyMap_freeOnClosedSectionsHom M n) (fun n i Z g hg ↦ ?_),
    hflat.1, hflat.2, fun U ↦ ?_⟩
  · rw [hF i]
    exact hkill (r i) n _ g hg
  · refine leftOrthogonal_sectionModule_of_isColimit_nat (colimit.isColimit F)
      (fun i ↦ quot (r i)) (fun i ↦ quotMap (r i)) (fun i ↦ ?_) U ((r 0).2.2 U)
      (fun i ↦ hquot (r i) U)
    rw [hF i]
    exact hses (r i)

/-! ### The flat-resolution theory with sectionwise K-projective good modules -/

variable (A)

/-- **The flat-resolution theory of `(A, d)` on a chaotic site whose good modules are flat as
graded modules, K-flat, and K-projective sectionwise.** K-flatness makes the tensor product with
an acyclic left differential graded module acyclic, and
`SheafOfModules.DifferentialGradedModule.exists_flat_quasiIso_sectionwise` resolves every right
differential graded `A`-module by a good one. -/
def chaoticSectionGoodModuleData :
    GoodModuleData.{t, m, m, v, u} A (derivedCategory.{t, m, m} A) :=
  GoodModuleData.ofExistsGood
    (fun P ↦ RelativeTensor.IsGradedFlat (GradedModule.ofDifferentialGraded P) ∧
      RelativeTensor.IsKFlat P ∧
      ∀ U : Cᵒᵖ, (_root_.DifferentialGradedModule.acyclic' (A.sectionAlgebra U)).leftOrthogonal
        ((_root_.DifferentialGradedModule.toHomotopyCategory (A.sectionAlgebra U)).obj
          (P.sectionModule U)))
    (fun hP ↦ hP.2.1)
    (fun M ↦ by
      obtain ⟨Q, f, hf, hgf, hkf, hU⟩ := exists_flat_quasiIso_sectionwise (A := A) M
      exact ⟨Q, f, ⟨hgf, hkf, hU⟩, (acyclic_cone_iff_quasiIso A f).2 hf⟩)

/-- The localization functor of `chaoticSectionGoodModuleData A` is the functor
`toDerivedCategory A` to the derived category. -/
@[simp] theorem chaoticSectionGoodModuleData_localization :
    (chaoticSectionGoodModuleData A).localization = toDerivedCategory.{t, m, m} A := rfl

/-- A differential graded module is good for `chaoticSectionGoodModuleData A` exactly when it is
graded flat, K-flat, and each of its section modules is left orthogonal to the acyclic
differential graded modules over the section algebra. -/
@[simp] theorem chaoticSectionGoodModuleData_isGood :
    (chaoticSectionGoodModuleData A).IsGood =
      fun P ↦ RelativeTensor.IsGradedFlat (GradedModule.ofDifferentialGraded P) ∧
        RelativeTensor.IsKFlat P ∧
        ∀ U : Cᵒᵖ, (_root_.DifferentialGradedModule.acyclic' (A.sectionAlgebra U)).leftOrthogonal
          ((_root_.DifferentialGradedModule.toHomotopyCategory (A.sectionAlgebra U)).obj
            (P.sectionModule U)) := rfl

end SheafOfModules.DifferentialGradedModule

end
