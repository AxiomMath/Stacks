module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Constructions.BinaryProducts
public import Mathlib.CategoryTheory.Sites.Adjunction
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.Sheafification
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.ConstructibleExtendScalars
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Limits

/-!
# Extension of scalars preserves constructible étale sheaves

A constructible sheaf of modules on the small étale site remains constructible
after extending scalars along a homomorphism of Noetherian rings.

## Main definitions

* `CategoryTheory.extendScalarsSheaf` is the sheafification of sectionwise extension of
  scalars.

## Main results

* `Stacks.EtaleCohomology.isConstructibleModuleSheaf_extendScalars` asserts
  constructibility after extension of scalars.

## Implementation notes

The tensor product with the constant sheaf of the target ring is represented
by sheafifying the sectionwise tensor product, equivalently extension of
scalars by `ModuleCat.extendScalars`. The source and target module-sheaf
constructibility predicates are those of Tag 03RW.

Sheafification on a small étale site is obtained from sheafification on the site
localized at its final object, which is where the hypotheses of Tag 03RW supply it.

## References

* [Stacks Project, Tag 0GKB](https://stacks.math.columbia.edu/tag/0GKB)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u w r s v c

namespace CategoryTheory

/-- Extension of scalars of a sheaf of modules, formed by sheafifying the
sectionwise extension of scalars. -/
public def extendScalarsSheaf {C : Type c} [Category.{v} C]
    (J : GrothendieckTopology C) (R : Type r) (S : Type s)
    [CommRing R] [CommRing S] [HasWeakSheafify J (ModuleCat.{max r s w} S)]
    (f : R →+* S) :
    Sheaf J (ModuleCat.{max r s w} R) ⥤ Sheaf J (ModuleCat.{max r s w} S) :=
  sheafToPresheaf J (ModuleCat.{max r s w} R) ⋙
    (Functor.whiskeringRight Cᵒᵖ (ModuleCat.{max r s w} R)
      (ModuleCat.{max r s w} S)).obj
      (ModuleCat.extendScalars f) ⋙
    presheafToSheaf J (ModuleCat.{max r s w} S)

private noncomputable def extendScalarsConstantSheafIso
    {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
    (R : Type r) (S : Type s) [CommRing R] [CommRing S]
    [HasWeakSheafify J (ModuleCat.{max r s w} R)]
    [HasWeakSheafify J (ModuleCat.{max r s w} S)]
    (f : R →+* S) (E : ModuleCat.{max r s w} R) :
    (extendScalarsSheaf J R S f).obj
        ((constantSheaf J (ModuleCat.{max r s w} R)).obj E) ≅
      (constantSheaf J (ModuleCat.{max r s w} S)).obj
        ((ModuleCat.extendScalars f).obj E) := by
  have : J.PreservesSheafification (ModuleCat.extendScalars.{r, s, max r s w} f) :=
    Sheaf.preservesSheafification_of_adjunction J
      (ModuleCat.extendRestrictScalarsAdj.{max r s w, r, s} f)
  exact ((presheafToSheafCompComposeAndSheafifyIso J
      (ModuleCat.extendScalars.{r, s, max r s w} f)).app
        ((Functor.const Cᵒᵖ).obj E)) ≪≫
    (presheafToSheaf J (ModuleCat.{max r s w} S)).mapIso
      (Functor.constComp Cᵒᵖ E (ModuleCat.extendScalars.{r, s, max r s w} f))

private noncomputable def overPullbackExtendScalarsAppIso
    {C : Type c} [Category.{v} C] [Limits.HasBinaryProducts C]
    (J : GrothendieckTopology C) (U : C)
    (R : Type r) (S : Type s) [CommRing R] [CommRing S]
    (f : R →+* S)
    [HasWeakSheafify J (ModuleCat.{max r s w} S)]
    [HasWeakSheafify (J.over U) (ModuleCat.{max r s w} S)]
    (F : Sheaf J (ModuleCat.{max r s w} R)) :
    (extendScalarsSheaf (J.over U) R S f).obj
        ((J.overPullback (ModuleCat.{max r s w} R) U).obj F) ≅
      (J.overPullback (ModuleCat.{max r s w} S) U).obj
        ((extendScalarsSheaf J R S f).obj F) := by
  let E := ModuleCat.extendScalars.{r, s, max r s w} f
  let T := ModuleCat.restrictScalars.{max r s w, r, s} f
  letI : Limits.PreservesLimitsOfSize.{v, max c v} T :=
    (ModuleCat.extendRestrictScalarsAdj.{max r s w, r, s} f).rightAdjoint_preservesLimits
  letI : J.HasSheafCompose T :=
    ⟨fun P hP => Presheaf.isSheaf_comp_of_isSheaf J P T hP⟩
  letI : (J.over U).HasSheafCompose T :=
    ⟨fun P hP => Presheaf.isSheaf_comp_of_isSheaf (J.over U) P T hP⟩
  let eJ := Sheaf.adjunction J
    (ModuleCat.extendRestrictScalarsAdj.{max r s w, r, s} f)
  let eK := Sheaf.adjunction (J.over U)
    (ModuleCat.extendRestrictScalarsAdj.{max r s w, r, s} f)
  let pR := (Over.forgetAdjStar U).sheafPushforwardContinuous
    (E := ModuleCat.{max r s w} R) (J.over U) J
  let pS := (Over.forgetAdjStar U).sheafPushforwardContinuous
    (E := ModuleCat.{max r s w} S) (J.over U) J
  let rightIso :
      (Over.star U).sheafPushforwardContinuous (ModuleCat.{max r s w} S)
          J (J.over U) ⋙ sheafCompose J T ≅
        sheafCompose (J.over U) T ⋙
          (Over.star U).sheafPushforwardContinuous (ModuleCat.{max r s w} R)
            J (J.over U) :=
    NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)
  simpa [extendScalarsSheaf, GrothendieckTopology.overPullback,
    Functor.sheafPushforwardContinuous, Sheaf.composeAndSheafify,
    Functor.assoc, E] using
    (Adjunction.leftAdjointUniq (pR.comp eK) ((eJ.comp pS).ofNatIsoRight rightIso)).app F

private noncomputable def sheafPullbackExtendScalarsAppIso
    {C D : Type c} [Category.{v} C] [Category.{v} D]
    (G : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [Functor.IsContinuous G J K]
    (R : Type r) (S : Type s) [CommRing R] [CommRing S]
    (f : R →+* S)
    [HasWeakSheafify J (ModuleCat.{max r s w} S)]
    [HasWeakSheafify K (ModuleCat.{max r s w} S)]
    [(G.sheafPushforwardContinuous (ModuleCat.{max r s w} R) J K).IsRightAdjoint]
    [(G.sheafPushforwardContinuous (ModuleCat.{max r s w} S) J K).IsRightAdjoint]
    (F : Sheaf J (ModuleCat.{max r s w} R)) :
    (extendScalarsSheaf K R S f).obj
        ((G.sheafPullback (ModuleCat.{max r s w} R) J K).obj F) ≅
      (G.sheafPullback (ModuleCat.{max r s w} S) J K).obj
        ((extendScalarsSheaf J R S f).obj F) := by
  let E := ModuleCat.extendScalars.{r, s, max r s w} f
  let T := ModuleCat.restrictScalars.{max r s w, r, s} f
  letI : Limits.PreservesLimitsOfSize.{v, max c v} T :=
    (ModuleCat.extendRestrictScalarsAdj.{max r s w, r, s} f).rightAdjoint_preservesLimits
  letI : J.HasSheafCompose T :=
    ⟨fun P hP => Presheaf.isSheaf_comp_of_isSheaf J P T hP⟩
  letI : K.HasSheafCompose T :=
    ⟨fun P hP => Presheaf.isSheaf_comp_of_isSheaf K P T hP⟩
  let eJ := Sheaf.adjunction J
    (ModuleCat.extendRestrictScalarsAdj.{max r s w, r, s} f)
  let eK := Sheaf.adjunction K
    (ModuleCat.extendRestrictScalarsAdj.{max r s w, r, s} f)
  let pR := G.sheafAdjunctionContinuous (ModuleCat.{max r s w} R) J K
  let pS := G.sheafAdjunctionContinuous (ModuleCat.{max r s w} S) J K
  let rightIso :
      G.sheafPushforwardContinuous (ModuleCat.{max r s w} S) J K ⋙
          sheafCompose J T ≅
        sheafCompose K T ⋙
          G.sheafPushforwardContinuous (ModuleCat.{max r s w} R) J K :=
    NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)
  simpa [extendScalarsSheaf, Sheaf.composeAndSheafify, E] using
    (Adjunction.leftAdjointUniq (pR.comp eK) ((eJ.comp pS).ofNatIsoRight rightIso)).app F

end CategoryTheory

namespace Stacks.ConstantSheaf

private theorem isFiniteTypeLocallyConstant_extendScalars
    {C : Type c} [Category.{v} C] [Limits.HasBinaryProducts C]
    (J : GrothendieckTopology C)
    (R : Type r) (S : Type s) [CommRing R] [CommRing S]
    [HasWeakSheafify J (ModuleCat.{max r s w} S)]
    [∀ U : C, HasWeakSheafify (J.over U) (ModuleCat.{max r s w} R)]
    [∀ U : C, HasWeakSheafify (J.over U) (ModuleCat.{max r s w} S)]
    (f : R →+* S) (F : Sheaf J (ModuleCat.{max r s w} R))
    (hF : IsFiniteTypeLocallyConstant R J F) :
    IsFiniteTypeLocallyConstant S J ((extendScalarsSheaf J R S f).obj F) := by
  intro U
  rcases hF U with ⟨I, V, g, hg, hV⟩
  refine ⟨I, V, g, hg, fun i => ?_⟩
  rcases hV i with ⟨E, hE, ⟨e⟩⟩
  exact ⟨(ModuleCat.extendScalars.{r, s, max r s w} f).obj E,
    AlgebraicGeometry.SmallEtale.isFG_extendScalars f E hE,
    ⟨(extendScalarsConstantSheafIso (J.over (V i)) R S f E).symm ≪≫
      (extendScalarsSheaf (J.over (V i)) R S f).mapIso e ≪≫
      overPullbackExtendScalarsAppIso J (V i) R S f F⟩⟩

private theorem isFiniteTypeLocallyConstant_of_iso
    {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
    (R : Type r) [Ring R]
    [∀ U : C, HasWeakSheafify (J.over U) (ModuleCat.{w} R)]
    {F G : Sheaf J (ModuleCat.{w} R)} (e : F ≅ G)
    (hF : IsFiniteTypeLocallyConstant R J F) :
    IsFiniteTypeLocallyConstant R J G := by
  intro U
  rcases hF U with ⟨I, V, f, hf, h⟩
  refine ⟨I, V, f, hf, fun i => ?_⟩
  rcases h i with ⟨E, hE, ⟨e₀⟩⟩
  exact ⟨E, hE, ⟨e₀ ≪≫ (J.overPullback (ModuleCat.{w} R) (V i)).mapIso e⟩⟩

end Stacks.ConstantSheaf

namespace Stacks.EtaleCohomology

open Stacks.ConstantSheaf

/-- Extension of scalars along a homomorphism of Noetherian rings preserves
constructibility on the small étale site. -/
@[stacks 0GKB]
public theorem isConstructibleModuleSheaf_extendScalars
    (B : BigEtaleSite.{u}) (X : B.Scheme)
    (R : Type r) (S : Type s) [CommRing R] [CommRing S]
    [IsNoetherianRing R] [IsNoetherianRing S] (f : R →+* S)
    [HasWeakSheafify (SmallEtale.topology B X.1 X.property)
      (ModuleCat.{max r s w} S)]
    [∀ (A T : B.Scheme) (g : T ⟶ A),
      ((smallEtaleBaseChange B g).sheafPushforwardContinuous
        (ModuleCat.{max r s w} R)
        (SmallEtale.topology B A.1 A.property)
        (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
    [∀ (T : B.Scheme) (V : SmallEtale B T.1 T.property),
      HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
        (ModuleCat.{max r s w} R)]
    [∀ (A T : B.Scheme) (g : T ⟶ A),
      ((smallEtaleBaseChange B g).sheafPushforwardContinuous
        (ModuleCat.{max r s w} S)
        (SmallEtale.topology B A.1 A.property)
        (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
    [∀ (T : B.Scheme) (V : SmallEtale B T.1 T.property),
      HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
        (ModuleCat.{max r s w} S)]
    (F : Sheaf (SmallEtale.topology B X.1 X.property)
      (ModuleCat.{max r s w} R))
    (hF : IsConstructibleModuleSheaf B X R F) :
    IsConstructibleModuleSheaf B X S
      ((extendScalarsSheaf (SmallEtale.topology B X.1 X.property) R S f).obj F) := by
  show ∀ U : X.1.affineOpens, ∃ s : ConstructibleStratification B X U.1,
      ∀ i, IsFiniteTypeLocallyConstant S
        (SmallEtale.topology B (s.piece i).1 (s.piece i).property)
        (((smallEtaleBaseChange B (s.inclusion i)).sheafPullback
          (ModuleCat.{max r s w} S)
          (SmallEtale.topology B X.1 X.property)
          (SmallEtale.topology B (s.piece i).1 (s.piece i).property)).obj
          ((extendScalarsSheaf (SmallEtale.topology B X.1 X.property) R S f).obj F))
  intro U
  rcases hF U with ⟨stratification, hstratification⟩
  refine ⟨stratification, fun i => ?_⟩
  let J := SmallEtale.topology B (stratification.piece i).1
    (stratification.piece i).property
  let : Limits.HasBinaryProducts
      (SmallEtale B (stratification.piece i).1
        (stratification.piece i).property) :=
    hasBinaryProducts_of_hasTerminal_and_pullbacks _
  let : HasWeakSheafify J (ModuleCat.{max r s w} S) :=
    AlgebraicGeometry.SmallEtale.hasWeakSheafify_of_overTerminal J _
      (SmallEtale.finalIsTerminal B (stratification.piece i).1
        (stratification.piece i).property)
  let G := smallEtaleBaseChange B (stratification.inclusion i)
  exact isFiniteTypeLocallyConstant_of_iso J S
    (sheafPullbackExtendScalarsAppIso G (SmallEtale.topology B X.1 X.property) J R S f F)
    (isFiniteTypeLocallyConstant_extendScalars J R S f _ (hstratification i))

end Stacks.EtaleCohomology
