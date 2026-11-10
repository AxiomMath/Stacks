module

public import Mathlib.Algebra.Category.ModuleCat.Projective
public import StacksFrontier.Algebra.Category.ModuleCat.NoncommExtendScalars
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.ConstructibleFlat
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleSheaves.ExtensionOfScalars

/-!
# Extension of scalars of constructible flat sheaves, for not necessarily commutative rings

Let `f : R →+* S` be a homomorphism of rings, not necessarily commutative, and let `F` be a
constructible flat sheaf of `R`-modules on the small étale site of a scheme: on a finite
constructible stratification of every affine open it is locally constant with finite projective
values. Then its sheafified extension of scalars `S ⊗_R F` is a constructible flat sheaf of
`S`-modules, the same stratification and the same trivializing coverings serving, with constant
values `S ⊗_R E`. This is the flat analogue of Tag 0GKB
(`Stacks.EtaleCohomology.isConstructibleModuleSheaf_extendScalars`, stated for commutative rings).
Extension of scalars also commutes with inverse images and with constant sheaves.

## Main definitions

* `CategoryTheory.extendScalarsSheafNoncomm`: sheafified extension of scalars.
* `CategoryTheory.extendScalarsSheafNoncommConstantSheafIso`: extension of scalars of a constant
  sheaf is constant.
* `CategoryTheory.sheafPullbackExtendScalarsSheafNoncommIso`: extension of scalars commutes with
  inverse image along a continuous functor.

## Main results

* `Stacks.NoncommChangeOfRings.extendScalars_finite` and
  `Stacks.NoncommChangeOfRings.extendScalars_projective`: extension of scalars preserves finite
  generation and projectivity.
* `AlgebraicGeometry.isConstructibleFlatModuleSheaf_extendScalarsSheafNoncomm`: extension of
  scalars preserves constructible flat sheaves on the small étale site.

## References

* [Stacks Project, Tag 0GKB](https://stacks.math.columbia.edu/tag/0GKB)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u w r v c

namespace Stacks.NoncommChangeOfRings

variable {R S : Type r} [Ring R] [Ring S] (f : R →+* S)

/-- Extension of scalars of a finitely generated module is finitely generated. -/
theorem extendScalars_finite (M : ModuleCat.{max r w} R) [Module.Finite R M] :
    Module.Finite S ((extendScalars.{w} f).obj M) := by
  classical
  obtain ⟨T, hT⟩ := Module.Finite.fg_top (R := R) (M := M)
  refine ⟨⟨T.image (ι f), ?_⟩⟩
  rw [eq_top_iff]
  rintro x -
  induction x using induction_on (f := f) with
  | add x y hx hy => exact Submodule.add_mem _ hx hy
  | pure b m =>
    rw [tmul_eq_smul_tmul_one]
    refine Submodule.smul_mem _ b ?_
    have hm : m ∈ Submodule.span R (T : Set M) := hT ▸ Submodule.mem_top
    induction hm using Submodule.span_induction with
    | mem m hm =>
      exact Submodule.subset_span (Finset.mem_coe.2 (Finset.mem_image_of_mem _ hm))
    | zero => rw [tmul_zero]; exact Submodule.zero_mem _
    | add m m' _ _ h h' => rw [tmul_add]; exact Submodule.add_mem _ h h'
    | smul a m _ h =>
      rw [← tmul_smul, one_mul, ← mul_one (f a), ← smul_tmul]
      exact Submodule.smul_mem _ _ h

/-- Extension of scalars of a projective module is projective. -/
theorem extendScalars_projective (M : ModuleCat.{max r w} R) [Module.Projective R M] :
    Module.Projective S ((extendScalars.{w} f).obj M) := by
  have hM : Projective M := M.projective_of_categoryTheory_projective
  have : Projective ((extendScalars.{w} f).obj M) :=
    (extendRestrictScalarsAdj.{w} f).map_projective M hM
  exact ((extendScalars.{w} f).obj M).projective_of_module_projective

end Stacks.NoncommChangeOfRings

namespace CategoryTheory

variable {R S : Type r} [Ring R] [Ring S] (f : R →+* S)

/-- Extension of scalars of a sheaf of modules along a homomorphism of not necessarily
commutative rings: sectionwise extension of scalars, sheafified. -/
public abbrev extendScalarsSheafNoncomm {C : Type c} [Category.{v} C]
    (J : GrothendieckTopology C) [HasWeakSheafify J (ModuleCat.{max r w} S)] :
    Sheaf J (ModuleCat.{max r w} R) ⥤ Sheaf J (ModuleCat.{max r w} S) :=
  Sheaf.composeAndSheafify J (Stacks.NoncommChangeOfRings.extendScalars.{w} f)

/-- Restriction of scalars along a homomorphism of not necessarily commutative rings sends
sheaves of modules to sheaves of modules. -/
lemma hasSheafCompose_restrictScalarsNoncomm {C : Type c} [Category.{v} C]
    (J : GrothendieckTopology C) :
    J.HasSheafCompose (ModuleCat.restrictScalars.{max r w} f) := by
  let : Limits.PreservesLimitsOfSize.{v, max c v} (ModuleCat.restrictScalars.{max r w} f) :=
    (Stacks.NoncommChangeOfRings.extendRestrictScalarsAdj.{w} f).rightAdjoint_preservesLimits
  exact ⟨fun P hP => Presheaf.isSheaf_comp_of_isSheaf J P _ hP⟩

/-- Extension of scalars of a constant sheaf is constant. -/
def extendScalarsSheafNoncommConstantSheafIso
    {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
    [HasWeakSheafify J (ModuleCat.{max r w} R)]
    [HasWeakSheafify J (ModuleCat.{max r w} S)]
    (E : ModuleCat.{max r w} R) :
    (extendScalarsSheafNoncomm.{w} f J).obj
        ((constantSheaf J (ModuleCat.{max r w} R)).obj E) ≅
      (constantSheaf J (ModuleCat.{max r w} S)).obj
        ((Stacks.NoncommChangeOfRings.extendScalars.{w} f).obj E) := by
  letI := hasSheafCompose_restrictScalarsNoncomm f J
  have : J.PreservesSheafification (Stacks.NoncommChangeOfRings.extendScalars.{w} f) :=
    Sheaf.preservesSheafification_of_adjunction J
      (Stacks.NoncommChangeOfRings.extendRestrictScalarsAdj.{w} f)
  exact ((presheafToSheafCompComposeAndSheafifyIso J
      (Stacks.NoncommChangeOfRings.extendScalars.{w} f)).app
        ((Functor.const Cᵒᵖ).obj E)) ≪≫
    (presheafToSheaf J (ModuleCat.{max r w} S)).mapIso
      (Functor.constComp Cᵒᵖ E (Stacks.NoncommChangeOfRings.extendScalars.{w} f))

/-- Extension of scalars commutes with restriction to a slice of the site. -/
def overPullbackExtendScalarsSheafNoncommIso
    {C : Type c} [Category.{v} C] [Limits.HasBinaryProducts C] (J : GrothendieckTopology C) (U : C)
    [HasWeakSheafify J (ModuleCat.{max r w} S)]
    [HasWeakSheafify (J.over U) (ModuleCat.{max r w} S)]
    (F : Sheaf J (ModuleCat.{max r w} R)) :
    (extendScalarsSheafNoncomm.{w} f (J.over U)).obj
        ((J.overPullback (ModuleCat.{max r w} R) U).obj F) ≅
      (J.overPullback (ModuleCat.{max r w} S) U).obj
        ((extendScalarsSheafNoncomm.{w} f J).obj F) := by
  let T := ModuleCat.restrictScalars.{max r w} f
  letI := hasSheafCompose_restrictScalarsNoncomm f J
  letI := hasSheafCompose_restrictScalarsNoncomm f (J.over U)
  let eJ := Sheaf.adjunction J (Stacks.NoncommChangeOfRings.extendRestrictScalarsAdj.{w} f)
  let eK := Sheaf.adjunction (J.over U)
    (Stacks.NoncommChangeOfRings.extendRestrictScalarsAdj.{w} f)
  let pR := (Over.forgetAdjStar U).sheafPushforwardContinuous
    (E := ModuleCat.{max r w} R) (J.over U) J
  let pS := (Over.forgetAdjStar U).sheafPushforwardContinuous
    (E := ModuleCat.{max r w} S) (J.over U) J
  let rightIso :
      (Over.star U).sheafPushforwardContinuous (ModuleCat.{max r w} S)
          J (J.over U) ⋙ sheafCompose J T ≅
        sheafCompose (J.over U) T ⋙
          (Over.star U).sheafPushforwardContinuous (ModuleCat.{max r w} R)
            J (J.over U) :=
    NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)
  exact (Adjunction.leftAdjointUniq (pR.comp eK) ((eJ.comp pS).ofNatIsoRight rightIso)).app F

/-- Extension of scalars commutes with inverse image along a continuous functor. -/
def sheafPullbackExtendScalarsSheafNoncommIso
    {C D : Type c} [Category.{v} C] [Category.{v} D]
    (G : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [Functor.IsContinuous G J K]
    [HasWeakSheafify J (ModuleCat.{max r w} S)]
    [HasWeakSheafify K (ModuleCat.{max r w} S)]
    [(G.sheafPushforwardContinuous (ModuleCat.{max r w} R) J K).IsRightAdjoint]
    [(G.sheafPushforwardContinuous (ModuleCat.{max r w} S) J K).IsRightAdjoint]
    (F : Sheaf J (ModuleCat.{max r w} R)) :
    (extendScalarsSheafNoncomm.{w} f K).obj
        ((G.sheafPullback (ModuleCat.{max r w} R) J K).obj F) ≅
      (G.sheafPullback (ModuleCat.{max r w} S) J K).obj
        ((extendScalarsSheafNoncomm.{w} f J).obj F) := by
  let T := ModuleCat.restrictScalars.{max r w} f
  letI := hasSheafCompose_restrictScalarsNoncomm f J
  letI := hasSheafCompose_restrictScalarsNoncomm f K
  let eJ := Sheaf.adjunction J (Stacks.NoncommChangeOfRings.extendRestrictScalarsAdj.{w} f)
  let eK := Sheaf.adjunction K (Stacks.NoncommChangeOfRings.extendRestrictScalarsAdj.{w} f)
  let pR := G.sheafAdjunctionContinuous (ModuleCat.{max r w} R) J K
  let pS := G.sheafAdjunctionContinuous (ModuleCat.{max r w} S) J K
  let rightIso :
      G.sheafPushforwardContinuous (ModuleCat.{max r w} S) J K ⋙ sheafCompose J T ≅
        sheafCompose K T ⋙ G.sheafPushforwardContinuous (ModuleCat.{max r w} R) J K :=
    NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)
  exact (Adjunction.leftAdjointUniq (pR.comp eK) ((eJ.comp pS).ofNatIsoRight rightIso)).app F

end CategoryTheory

namespace Stacks.ConstantSheaf

variable {R S : Type r} [Ring R] [Ring S] (f : R →+* S)

/-- Extension of scalars preserves local constancy with finite projective values. -/
theorem isFiniteProjectiveLocallyConstant_extendScalarsSheafNoncomm
    {C : Type c} [Category.{v} C] [Limits.HasBinaryProducts C] (J : GrothendieckTopology C)
    [HasWeakSheafify J (ModuleCat.{max r w} S)]
    [∀ U : C, HasWeakSheafify (J.over U) (ModuleCat.{max r w} R)]
    [∀ U : C, HasWeakSheafify (J.over U) (ModuleCat.{max r w} S)]
    (F : Sheaf J (ModuleCat.{max r w} R))
    (hF : IsFiniteProjectiveLocallyConstant R J F) :
    IsFiniteProjectiveLocallyConstant S J ((extendScalarsSheafNoncomm.{w} f J).obj F) := by
  intro U
  rcases hF U with ⟨I, V, g, hg, hV⟩
  refine ⟨I, V, g, hg, fun i => ?_⟩
  rcases hV i with ⟨E, hfin, hproj, ⟨e⟩⟩
  refine ⟨(Stacks.NoncommChangeOfRings.extendScalars.{w} f).obj E,
    Stacks.NoncommChangeOfRings.extendScalars_finite f E,
    Stacks.NoncommChangeOfRings.extendScalars_projective f E, ⟨?_⟩⟩
  exact (extendScalarsSheafNoncommConstantSheafIso f (J.over (V i)) E).symm ≪≫
    (extendScalarsSheafNoncomm.{w} f (J.over (V i))).mapIso e ≪≫
    overPullbackExtendScalarsSheafNoncommIso f J (V i) F

end Stacks.ConstantSheaf

namespace AlgebraicGeometry

/-- **Extension of scalars preserves constructible flatness**, along a homomorphism of not
necessarily commutative rings: if `F` is a constructible flat sheaf of `R`-modules on the small
étale site of `X`, then its sheafified extension of scalars is a constructible flat sheaf of
`S`-modules. -/
public theorem isConstructibleFlatModuleSheaf_extendScalarsSheafNoncomm
    (B : BigEtaleSite.{u}) (X : B.Scheme) {R S : Type r} [Ring R] [Ring S] (f : R →+* S)
    [HasWeakSheafify (SmallEtale.topology B X.1 X.property) (ModuleCat.{max r w} S)]
    [∀ (A T : B.Scheme) (g : T ⟶ A),
      ((smallEtaleBaseChange B g).sheafPushforwardContinuous (ModuleCat.{max r w} R)
        (SmallEtale.topology B A.1 A.property)
        (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
    [∀ (T : B.Scheme) (V : SmallEtale B T.1 T.property),
      HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V) (ModuleCat.{max r w} R)]
    [∀ (A T : B.Scheme) (g : T ⟶ A),
      ((smallEtaleBaseChange B g).sheafPushforwardContinuous (ModuleCat.{max r w} S)
        (SmallEtale.topology B A.1 A.property)
        (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
    [∀ (T : B.Scheme) (V : SmallEtale B T.1 T.property),
      HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V) (ModuleCat.{max r w} S)]
    (F : Sheaf (SmallEtale.topology B X.1 X.property) (ModuleCat.{max r w} R))
    (hF : IsConstructibleFlatModuleSheaf B X R F) :
    IsConstructibleFlatModuleSheaf B X S
      ((extendScalarsSheafNoncomm.{w} f (SmallEtale.topology B X.1 X.property)).obj F) := by
  intro U
  rcases hF U with ⟨stratification, hstratification⟩
  refine ⟨stratification, fun i => ?_⟩
  let J := SmallEtale.topology B (stratification.piece i).1 (stratification.piece i).property
  have : Limits.HasBinaryProducts
      (SmallEtale B (stratification.piece i).1 (stratification.piece i).property) :=
    hasBinaryProducts_of_hasTerminal_and_pullbacks _
  have : HasWeakSheafify J (ModuleCat.{max r w} S) := SmallEtale.hasWeakSheafify_of_overTerminal J _
    (SmallEtale.finalIsTerminal B (stratification.piece i).1 (stratification.piece i).property)
  exact Stacks.ConstantSheaf.isFiniteProjectiveLocallyConstant_congr S J
    (sheafPullbackExtendScalarsSheafNoncommIso f
      (smallEtaleBaseChange B (stratification.inclusion i))
      (SmallEtale.topology B X.1 X.property) J F)
    (Stacks.ConstantSheaf.isFiniteProjectiveLocallyConstant_extendScalarsSheafNoncomm f J _
      (hstratification i))

end AlgebraicGeometry

end
