module

public import Mathlib.CategoryTheory.Sites.DenseSubsite.OneHypercoverDense
public import Mathlib.CategoryTheory.Subfunctor.Image
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardFullyFaithful.Basic
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.AdditivityOfDirectAndInverseImage
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsTopologyUnique
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModuleCompIso
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRingedToposHom
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleSchemeChart
public import StacksFrontier.AlgebraicGeometry.Spaces.SupportedSectionsSubsheaf
import StacksFrontier.AlgebraicGeometry.Spaces.Basic
import StacksFrontier.AlgebraicGeometry.Spaces.Points
import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleSite
import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleSite
import StacksFrontier.AlgebraicGeometry.Topologies.Fppf
import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite

/-!
# Direct image of the sections supported on a closed subset

For a morphism `f : X ⟶ Y` of algebraic spaces over a scheme `S` and a closed subset `T` of
the points of `Y`, the direct image of the subsheaf of an `𝒪_X`-module whose sections are
supported over `|f|⁻¹T` is the subsheaf of the direct image whose sections are supported
on `T`.

## Main results

* `AlgebraicGeometry.Space.pushforward_supportedSectionsSubmodule_range_eq`: the two subsheaves
  of `f_*F` agree chart by chart, as the images of their canonical inclusions.

## References

* [Stacks Project, Tag 085B](https://stacks.math.columbia.edu/tag/085B)
* [Stacks Project, Tag 0859](https://stacks.math.columbia.edu/tag/0859)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite
open CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space
private theorem comparisonFunctor_oneHypercoverDense
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS) :
    Functor.IsOneHypercoverDense.{0} (comparisonFunctor B S hS X)
      (SmallEtale.topology B S hS X.1)
      (SpacesEtale.topology B S hS X) := by
  let C := comparisonFunctor B S hS X
  let := comparisonFunctor_full B S hS X
  let := comparisonFunctor_faithful B S hS X
  constructor
  intro U
  obtain ⟨V, a, ha⟩ := exists_scheme_chart_cover B S hS X U
  obtain ⟨W, p, q, hpq⟩ := exists_scheme_chart_self_intersection B S hS X a
  refine ⟨{
    I₀ := Unit
    X := fun _ => V
    f := fun _ => a
    I₁ := fun _ _ => Unit
    Y := fun {_ _} _ => W
    p₁ := fun {_ _} _ => C.preimage p
    p₂ := fun {_ _} _ => C.preimage q
    w := fun {_ _} _ => by
      change C.map _ ≫ a = C.map _ ≫ a
      simpa only [C.map_preimage] using hpq.w
    mem₀ := ?_
    mem₁₀ := ?_ }⟩
  · convert ha using 1
    apply congrArg Sieve.generate
    funext Z g
    apply propext
    constructor
    · rintro ⟨⟩
      exact ⟨⟩
    · rintro ⟨⟩
      exact ⟨()⟩
  · intro i j Z p₁ p₂ hw
    apply (SmallEtale.topology B S hS X.1).superset_covering
      (S := ⊤) _ ((SmallEtale.topology B S hS X.1).top_mem Z)
    intro Q r hr
    refine ⟨(), r ≫ C.preimage (hpq.lift (C.map p₁) (C.map p₂) hw), ?_, ?_⟩
    · apply C.map_injective
      simp [Functor.map_comp, Category.assoc, hpq.lift_fst]
    · apply C.map_injective
      simp [Functor.map_comp, Category.assoc, hpq.lift_snd]


private def spacesModuleSections
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS) :
    Modules.{u, u} B S hS X.1 X.2 ⥤
      Sheaf (SpacesEtale.topology B S hS X) AddCommGrpCat.{u} := by
  letI := comparisonFunctor_isContinuous B S hS X
  let R := (comparisonFunctor B S hS X).sheafPushforwardContinuous AddCommGrpCat.{u}
    (SmallEtale.topology B S hS X.1)
    (SpacesEtale.topology B S hS X)
  letI : R.IsEquivalence := comparisonFunctor_sheafEquivalence B S hS X _
  exact SheafOfModules.toSheaf _ ⋙ R.inv

private def spacesModuleSectionsIso
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS) :
    letI := comparisonFunctor_isContinuous B S hS X
    spacesModuleSections B S hS X ⋙
      (comparisonFunctor B S hS X).sheafPushforwardContinuous AddCommGrpCat.{u}
        (SmallEtale.topology B S hS X.1)
        (SpacesEtale.topology B S hS X) ≅ SheafOfModules.toSheaf _ := by
  letI := comparisonFunctor_isContinuous B S hS X
  let R := (comparisonFunctor B S hS X).sheafPushforwardContinuous AddCommGrpCat.{u}
    (SmallEtale.topology B S hS X.1)
    (SpacesEtale.topology B S hS X)
  letI : R.IsEquivalence := comparisonFunctor_sheafEquivalence B S hS X _
  exact Functor.isoWhiskerLeft (SheafOfModules.toSheaf _) R.asEquivalence.counitIso

private theorem spacesModuleSections_map_zero
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS)
    (F G : Modules.{u, u} B S hS X.1 X.2) :
    (spacesModuleSections B S hS X).map (0 : F ⟶ G) = 0 := by
  let := comparisonFunctor_isContinuous B S hS X
  let R := (comparisonFunctor B S hS X).sheafPushforwardContinuous AddCommGrpCat.{u}
    (SmallEtale.topology B S hS X.1)
    (SpacesEtale.topology B S hS X)
  let : R.IsEquivalence := comparisonFunctor_sheafEquivalence B S hS X _
  apply R.map_injective
  let : Mono ((spacesModuleSectionsIso B S hS X).hom.app G) :=
    inferInstanceAs (Mono ((spacesModuleSectionsIso B S hS X).app G).hom)
  apply (cancel_mono ((spacesModuleSectionsIso B S hS X).hom.app G)).1
  refine ((spacesModuleSectionsIso B S hS X).hom.naturality (0 : F ⟶ G)).trans ?_
  ext U s
  change 0 = ((spacesModuleSectionsIso B S hS X).hom.app G).hom.app U 0
  exact (map_zero _).symm

/-- The zero map of `𝒪_X`-modules induces the zero map on sections over any object of the
spaces-étale site. -/
private theorem spacesModuleSections_map_zero_app
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS)
    (G : Modules.{u, u} B S hS X.1 X.2)
    (A : SpacesEtale B S hS X)
    (x : ((spacesModuleSections B S hS X).obj G).obj.obj (op A)) :
    ((spacesModuleSections B S hS X).map (0 : G ⟶ G)).hom.app (op A) x = 0 := by
  rw [spacesModuleSections_map_zero B S hS X G G]
  simp only [ObjectProperty.zero_hom, zero_app, AddCommGrpCat.hom_zero,
    AddMonoidHom.zero_apply]

private def pushforwardSpacesSectionsIso
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) :
    letI := comparisonFunctor_isContinuous B S hS Y
    letI := (spacesBaseChange_isMorphismOfSites B S hS f).isContinuous
    ((smallEtaleRingedToposHom B S hS f).pushforwardModules) ⋙
      Sheaf.moduleSheafFunctor
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O)) ≅
    spacesModuleSections B S hS X ⋙
      sheafCompose (SpacesEtale.topology B S hS X) (forget AddCommGrpCat.{u}) ⋙
      (spacesBaseChange B S hS f).functor.sheafPushforwardContinuous (Type u)
        (SpacesEtale.topology B S hS Y)
        (SpacesEtale.topology B S hS X) ⋙
      (comparisonFunctor B S hS Y).sheafPushforwardContinuous (Type u)
        (SmallEtale.topology B S hS Y.1)
        (SpacesEtale.topology B S hS Y) := by
  letI := comparisonFunctor_isContinuous B S hS X
  letI := comparisonFunctor_isContinuous B S hS Y
  letI := (spacesBaseChange_isMorphismOfSites B S hS f).isContinuous
  let FX := sheafCompose (SmallEtale.topology B S hS X.1)
    (forget AddCommGrpCat.{u})
  let H := spacesModuleSections B S hS X ⋙
    sheafCompose (SpacesEtale.topology B S hS X) (forget AddCommGrpCat.{u})
  let RX := (comparisonFunctor B S hS X).sheafPushforwardContinuous (Type u)
    (SmallEtale.topology B S hS X.1)
    (SpacesEtale.topology B S hS X)
  let RX' := (comparisonFunctor B S hS X).sheafPushforwardContinuous (Type u)
    (SmallEtale.topology B S hS X.1)
    (SpacesEtale.topology B S hS X)
  let Q := (smallEtaleRingedToposHom B S hS f).toToposHom.pushforward
  let b := (spacesBaseChange B S hS f).functor.sheafPushforwardContinuous (Type u)
    (SpacesEtale.topology B S hS Y)
    (SpacesEtale.topology B S hS X)
  let i : H ⋙ RX ≅ Sheaf.moduleSheafFunctor
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)) :=
    Functor.isoWhiskerRight (spacesModuleSectionsIso B S hS X) FX
  exact (smallEtaleRingedToposHom B S hS f).pushforwardModulesUnderlyingIso ≪≫
    Functor.isoWhiskerRight i.symm Q ≪≫
    Functor.isoWhiskerLeft H (Functor.isoWhiskerRight
      (Functor.sheafPushforwardContinuousIso (Iso.refl (comparisonFunctor B S hS X)) _ _ _) Q) ≪≫
    Functor.isoWhiskerLeft H (smallEtaleRingedToposHom_pushforward B S hS f) ≪≫
    Functor.isoWhiskerLeft (H ⋙ b)
      (Functor.sheafPushforwardContinuousIso (Iso.refl (comparisonFunctor B S hS Y)).symm _ _ _)

private theorem exists_chart_cover
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS)
    (U : SpacesEtale B S hS X) :
    ∃ (V W : SmallEtale B S hS X.1)
      (a : (comparisonFunctor B S hS X).obj V ⟶ U)
      (p q : (comparisonFunctor B S hS X).obj W ⟶ (comparisonFunctor B S hS X).obj V),
      Sieve.generate (Presieve.singleton a) ∈ SpacesEtale.topology B S hS X U ∧
      IsPullback p q a a := by
  obtain ⟨V, a, ha⟩ := exists_scheme_chart_cover B S hS X U
  obtain ⟨W, p, q, hpq⟩ := exists_scheme_chart_self_intersection B S hS X a
  let eV := (Iso.refl (comparisonFunctor B S hS X)).app V
  let eW := (Iso.refl (comparisonFunctor B S hS X)).app W
  refine ⟨V, W, eV.hom ≫ a, eW.hom ≫ p ≫ eV.inv,
    eW.hom ≫ q ≫ eV.inv, ?_, ?_⟩
  · apply (SpacesEtale.topology B S hS X).superset_covering _ ha
    apply (Sieve.generate_le_iff _ _).mpr
    rintro Z g ⟨⟩
    exact ⟨_, eV.inv, eV.hom ≫ a, ⟨⟩, by simp⟩
  · apply IsPullback.of_iso hpq eW.symm eV.symm eV.symm (Iso.refl U)
    all_goals simp

private theorem restriction_injective_of_cover
    {C : Type*} [Category C] {J : GrothendieckTopology C}
    (F : Sheaf J AddCommGrpCat.{u}) {U V : C} (a : V ⟶ U)
    (ha : Sieve.generate (Presieve.singleton a) ∈ J U) :
    Function.Injective (F.obj.map a.op) := by
  let F' := (sheafCompose J (forget AddCommGrpCat.{u})).obj F
  exact Presieve.isSeparatedFor_singleton.mp
    ((Presieve.isSheafFor_iff_generate (P := F'.obj) _).mpr
      (F'.property.isSheafFor _ ha)).isSeparatedFor

private theorem range_of_restriction_mem_range
    {C : Type*} [Category C] {J : GrothendieckTopology C}
    {F G : Sheaf J AddCommGrpCat.{u}} (m : F ⟶ G)
    (hm : ∀ U, Function.Injective (m.hom.app (op U)))
    {U V W : C} (a : V ⟶ U) (p q : W ⟶ V)
    (ha : Sieve.generate (Presieve.singleton a) ∈ J U)
    (hpq : IsPullback p q a a)
    (s : G.obj.obj (op U))
    (hs : G.obj.map a.op s ∈ Set.range (m.hom.app (op V))) :
    s ∈ Set.range (m.hom.app (op U)) := by
  obtain ⟨t, ht⟩ := hs
  have hcompat : F.obj.map p.op t = F.obj.map q.op t := by
    apply hm W
    simp only [← ConcreteCategory.comp_apply, m.hom.naturality]
    change G.obj.map p.op (m.hom.app (op V) t) = G.obj.map q.op (m.hom.app (op V) t)
    rw [ht]
    simpa only [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp] using
      congrArg (fun k : W ⟶ U => G.obj.map k.op s) hpq.w
  let F' := (sheafCompose J (forget AddCommGrpCat.{u})).obj F
  have hlim := (Equalizer.Presieve.isSheafFor_singleton_iff
    (F := F'.obj) (f := a) (c := PullbackCone.mk p q hpq.w) hpq.isLimit).mp
      ((Presieve.isSheafFor_iff_generate (P := F'.obj) _).mpr (F'.property.isSheafFor _ ha))
  obtain ⟨t₀, ht₀, -⟩ := (Types.type_equalizer_iff_unique _ _).mp hlim t hcompat
  let t' : (F.obj.obj (op U) : Type u) := t₀
  have ht' : F.obj.map a.op t' = t := ht₀
  refine ⟨t', restriction_injective_of_cover G a ha ?_⟩
  have hnat := ConcreteCategory.congr_hom (m.hom.naturality a.op) t'
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at hnat
  rw [← hnat, ht', ht]

private def spacesSectionsChartIso
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS)
    (F : Modules.{u, u} B S hS X.1 X.2)
    (Q : SmallEtale B S hS X.1) :
    ((spacesModuleSections B S hS X).obj F).obj.obj
        (op ((comparisonFunctor B S hS X).obj Q)) ≅
      F.val.presheaf.obj (op Q) := by
  letI := comparisonFunctor_isContinuous B S hS X
  exact ((evaluation _ AddCommGrpCat).obj (op Q)).mapIso
    ((sheafToPresheaf _ _).mapIso ((spacesModuleSectionsIso B S hS X).app F))

private theorem spacesSectionsChartIso_naturality
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS)
    {F G : Modules.{u, u} B S hS X.1 X.2} (m : F ⟶ G)
    (Q : SmallEtale B S hS X.1)
    (s : ((spacesModuleSections B S hS X).obj F).obj.obj
      (op ((comparisonFunctor B S hS X).obj Q))) :
    (spacesSectionsChartIso B S hS X G Q).hom
      (((spacesModuleSections B S hS X).map m).hom.app
        (op ((comparisonFunctor B S hS X).obj Q)) s) =
      m.val.app (op Q) ((spacesSectionsChartIso B S hS X F Q).hom s) := by
  let := comparisonFunctor_isContinuous B S hS X
  exact (congrArg (fun a => a.hom.app (op Q) s)
    ((spacesModuleSectionsIso B S hS X).hom.naturality m))

private theorem spacesSectionsChartIso_map
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS)
    (F : Modules.{u, u} B S hS X.1 X.2)
    {Q Q' : SmallEtale B S hS X.1} (a : Q' ⟶ Q)
    (s : ((spacesModuleSections B S hS X).obj F).obj.obj
      (op ((comparisonFunctor B S hS X).obj Q))) :
    (spacesSectionsChartIso B S hS X F Q').hom
      (((spacesModuleSections B S hS X).obj F).obj.map
        ((comparisonFunctor B S hS X).map a).op s) =
      F.val.map a.op ((spacesSectionsChartIso B S hS X F Q).hom s) := by
  let := comparisonFunctor_isContinuous B S hS X
  exact ConcreteCategory.congr_hom
    (((spacesModuleSectionsIso B S hS X).hom.app F).hom.naturality a.op) s

private theorem spacesModuleSections_injective
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS)
    {F G : Modules.{u, u} B S hS X.1 X.2} (m : F ⟶ G)
    (hm : ∀ Q, Function.Injective (m.val.app (op Q)))
    (A : SpacesEtale B S hS X) :
    Function.Injective (((spacesModuleSections B S hS X).map m).hom.app (op A)) := by
  obtain ⟨Q, Q', a, p, q, ha, hpq⟩ := exists_chart_cover B S hS X A
  intro s t hst
  apply restriction_injective_of_cover ((spacesModuleSections B S hS X).obj F) a ha
  apply (ConcreteCategory.bijective_of_isIso (spacesSectionsChartIso B S hS X F Q).hom).1
  apply hm Q
  rw [← spacesSectionsChartIso_naturality, ← spacesSectionsChartIso_naturality]
  congr 1
  exact (ConcreteCategory.congr_hom
    (((spacesModuleSections B S hS X).map m).hom.naturality a.op) s).trans
      ((congrArg (fun s => ((spacesModuleSections B S hS X).obj G).obj.map a.op s) hst).trans
        (ConcreteCategory.congr_hom
          (((spacesModuleSections B S hS X).map m).hom.naturality a.op) t).symm)

private theorem isOpenSubspace_subfunctorRange_of_openImmersion
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {A G : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (p : A ⟶ G) [Mono p] (hA : AlgebraicGeometry.IsAlgebraicSpace B S hS A)
    (hp : IsOpenImmersion B S hS p) :
    IsOpenSubspace B S hS (Subfunctor.range p) := by
  let e := asIso (Subfunctor.toRange p)
  refine ⟨isAlgebraicSpace_of_iso B S hS e hA, ?_⟩
  let Q := MorphismProperty.presheaf
    (MorphismProperty.inverseImage (@AlgebraicGeometry.IsOpenImmersion.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS))
  have he : Subfunctor.toRange p ≫ (Subfunctor.range p).ι = p :=
    Subfunctor.toRange_ι p
  have hp' : Q (e.hom ≫ (Subfunctor.range p).ι) := he.symm ▸ hp
  let : Q.RespectsIso := inferInstance
  have h := MorphismProperty.RespectsIso.precomp Q e.inv
    (e.hom ≫ (Subfunctor.range p).ι) hp'
  have hfac : e.inv ≫ p = (Subfunctor.range p).ι := (Iso.inv_comp_eq e).2 he.symm
  exact hfac ▸ h

private theorem isQuasiCompact_space_of_iso
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (e : X ≅ Y)
    (hX : IsQuasiCompactSpace B S hS X) :
    IsQuasiCompactSpace B S hS Y := by
  rcases hX with ⟨U, q, hcompact, hsurjective, hetale⟩
  refine ⟨U, q ≫ e.hom, hcompact, ?_, ?_⟩
  · exact MorphismProperty.RespectsIso.postcomp _ e.hom q hsurjective
  · intro U' φ hφ
    exact MorphismProperty.RespectsIso.postcomp _ e.hom (φ ≫ q) (hetale U' φ hφ)

private theorem isQuasiCompact_precomp_iso
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y Z : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (e : X ≅ Y) (f : Y ⟶ Z)
    (hf : IsQuasiCompact B S hS f) :
    IsQuasiCompact B S hS (e.hom ≫ f) := by
  intro W hWalg hWqc k
  let m := pullback.map k (e.hom ≫ f) k f (𝟙 W) e.hom (𝟙 Z)
    (by simp) (by simp)
  have hm : IsIso m := by
    dsimp [m]
    infer_instance
  let e' : pullback k (e.hom ≫ f) ≅ pullback k f := asIso m
  exact isQuasiCompact_space_of_iso B S hS e'.symm (hf W hWalg hWqc k)

private theorem range_pointsMap_pullback
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y Z P : AlgebraicSpaces B S hS}
    {f : X ⟶ Y} {g : Z ⟶ Y} {p : P ⟶ X} {q : P ⟶ Z}
    (hsq : IsPullback p q f g) :
    Set.range (pointsMap B S hS P.1 p.hom) =
      (pointsMap B S hS X.1 f.hom) ⁻¹'
        Set.range (pointsMap B S hS Z.1 g.hom) := by
  ext x
  constructor
  · rintro ⟨w, rfl⟩
    change pointsMap B S hS X.1 f.hom
        (pointsMap B S hS P.1 p.hom w) ∈
          Set.range (pointsMap B S hS Z.1 g.hom)
    have h := congrArg
      (fun k : P ⟶ Y => pointsMap B S hS P.1 k.hom w) hsq.w
    change pointsMap B S hS P.1 (p.hom ≫ f.hom) w =
      pointsMap B S hS P.1 (q.hom ≫ g.hom) w at h
    rw [pointsMap_comp B S hS _ p.hom f.hom,
      pointsMap_comp B S hS _ q.hom g.hom] at h
    exact ⟨pointsMap B S hS P.1 q.hom w, h.symm⟩
  · rintro ⟨z, hz⟩
    obtain ⟨w, _, hwp⟩ := exists_point_of_isPullback B S hS hsq.flip z x hz
    exact ⟨w, hwp⟩

private theorem etaleChart_comp_open
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {A D X : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (i : A ⟶ D) (a : D ⟶ X) (hi : IsOpenImmersion B S hS i)
    (ha : (MorphismProperty.inverseImage (@Etale.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf a) :
    (MorphismProperty.inverseImage (@Etale.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf (i ≫ a) := by
  let P := MorphismProperty.inverseImage (@Etale.{u})
    (AlgebraicGeometry.BigFppfOver.toScheme B S hS)
  have hi' : P.presheaf i := by
    apply MorphismProperty.relative_monotone (P := MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsOpenImmersion.{u}) (AlgebraicGeometry.BigFppfOver.toScheme B S hS))
      (P' := P) ?_ _ hi
    intro D E b hb
    let : AlgebraicGeometry.IsOpenImmersion
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map b) := hb
    exact (inferInstance : Etale ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map b))
  let : MorphismProperty.IsStableUnderComposition (@Etale.{u}) := by
    refine ⟨?_⟩
    intro D E H a b ha hb
    let := ha
    let := hb
    exact Etale.etale_comp a b
  let : P.IsStableUnderComposition :=
    MorphismProperty.IsStableUnderComposition.inverseImage
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)
  let : P.presheaf.IsStableUnderComposition := MorphismProperty.relative_isStableUnderComposition P
  exact MorphismProperty.comp_mem P.presheaf _ _ hi' ha

private theorem chart_complement_pullback
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (T : Set (points B S hS Y.1))
    (W U : SmallEtale B S hS Y.1) (i : U ⟶ W)
    (hiOpen : IsOpenImmersion B S hS (yoneda.map i.hom.left))
    (hi : Set.range (pointsMap B S hS _ (yoneda.map i.hom.left)) =
      pointsMap B S hS _ W.1.hom ⁻¹' Tᶜ)
    (Q : SmallEtale B S hS X.1)
    (a : (comparisonFunctor B S hS X).obj Q ⟶
      (spacesBaseChange B S hS f).functor.obj ((comparisonFunctor B S hS Y).obj W)) :
    ∃ (E : SmallEtale B S hS X.1) (e : E ⟶ Q)
      (b : (comparisonFunctor B S hS X).obj E ⟶
        (spacesBaseChange B S hS f).functor.obj ((comparisonFunctor B S hS Y).obj U)),
      (comparisonFunctor B S hS X).map e ≫ a = b ≫
        (spacesBaseChange B S hS f).functor.map ((comparisonFunctor B S hS Y).map i) ∧
      Set.range (pointsMap B S hS _ (yoneda.map e.hom.left)) =
        pointsMap B S hS _ Q.1.hom ⁻¹'
          (pointsMap B S hS X.1 f.hom ⁻¹' T)ᶜ := by
  let KX := comparisonFunctor B S hS X
  let KY := comparisonFunctor B S hS Y
  let C := spacesBaseChange B S hS f
  let g : Q.1.left ⟶ W.1.left :=
    yoneda.preimage (a.hom.left.hom ≫ (C.projection.app (KY.obj W)).hom)
  have hg : yoneda.map g = a.hom.left.hom ≫ (C.projection.app (KY.obj W)).hom :=
    yoneda.map_preimage _
  have hc : yoneda.map g ≫ W.1.hom = Q.1.hom ≫ f.hom := by
    have h := congrArg (fun k => k.hom) (C.isPullback (KY.obj W)).w
    change (C.projection.app (KY.obj W)).hom ≫ W.1.hom =
      (C.functor.obj (KY.obj W)).1.hom.hom ≫ f.hom at h
    have e1 : yoneda.map g ≫ W.1.hom =
        (a.hom.left.hom ≫ (C.projection.app (KY.obj W)).hom) ≫ W.1.hom :=
      congrArg (fun k => k ≫ W.1.hom) hg
    have e2 : (a.hom.left.hom ≫ (C.projection.app (KY.obj W)).hom) ≫ W.1.hom =
        a.hom.left.hom ≫ ((C.projection.app (KY.obj W)).hom ≫ W.1.hom) :=
      Category.assoc _ _ _
    have e3 : a.hom.left.hom ≫ ((C.projection.app (KY.obj W)).hom ≫ W.1.hom) =
        a.hom.left.hom ≫ ((C.functor.obj (KY.obj W)).1.hom.hom ≫ f.hom) :=
      congrArg (fun k => a.hom.left.hom ≫ k) h
    have e4 : a.hom.left.hom ≫ ((C.functor.obj (KY.obj W)).1.hom.hom ≫ f.hom) =
        (a.hom.left.hom ≫ (C.functor.obj (KY.obj W)).1.hom.hom) ≫ f.hom :=
      (Category.assoc _ _ _).symm
    have e5 : (a.hom.left.hom ≫ (C.functor.obj (KY.obj W)).1.hom.hom) ≫ f.hom =
        Q.1.hom ≫ f.hom :=
      congrArg (fun k => k.hom ≫ f.hom) a.hom.w
    exact e1.trans (e2.trans (e3.trans (e4.trans e5)))
  let E₀ := pullback g i.hom.left
  let p₀ := pullback.fst g i.hom.left
  let q₀ := pullback.snd g i.hom.left
  have hpq : IsPullback (yoneda.map p₀) (yoneda.map q₀) (yoneda.map g)
      (yoneda.map i.hom.left) := Functor.map_isPullback yoneda (IsPullback.of_hasPullback _ _)
  let ES : AlgebraicSpaces B S hS :=
    ⟨yoneda.obj E₀, AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS E₀⟩
  let pp : ES ⟶ (KX.obj Q).1.left := ObjectProperty.homMk (yoneda.map p₀)
  let qq : ES ⟶ (KY.obj U).1.left := ObjectProperty.homMk (yoneda.map q₀)
  let gg : (KX.obj Q).1.left ⟶ (KY.obj W).1.left := ObjectProperty.homMk (yoneda.map g)
  have hsq : IsPullback pp qq gg ((KY.map i).hom.left) := by
    apply IsPullback.of_map_of_faithful (ObjectProperty.ι _)
    exact hpq
  have hpOpen := isOpenImmersion_of_isPullback B S hS hsq.flip hiOpen
  let E : SmallEtale B S hS X.1 :=
    ⟨CostructuredArrow.mk (yoneda.map p₀ ≫ Q.1.hom),
      etaleChart_comp_open B S hS _ _ hpOpen Q.2⟩
  let e : E ⟶ Q := ⟨CostructuredArrow.homMk p₀ rfl⟩
  have hbcomm : qq ≫ (KY.obj U).1.hom =
      (KX.obj E).1.hom ≫ f := by
    apply ObjectProperty.hom_ext
    change yoneda.map q₀ ≫ U.1.hom = (yoneda.map p₀ ≫ Q.1.hom) ≫ f.hom
    rw [Category.assoc, ← hc, ← Category.assoc, hpq.w, Category.assoc, i.hom.w]
  let b : KX.obj E ⟶ C.functor.obj (KY.obj U) :=
    ⟨Over.homMk ((C.isPullback (KY.obj U)).lift qq (KX.obj E).1.hom hbcomm)
      ((C.isPullback (KY.obj U)).lift_snd _ _ _)⟩
  refine ⟨E, e, b, ?_, ?_⟩
  · apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    apply (C.isPullback (KY.obj W)).hom_ext
    · have hn := C.projection.naturality (KY.map i)
      change pp ≫ a.hom.left ≫ C.projection.app (KY.obj W) =
        b.hom.left ≫ (C.functor.map (KY.map i)).hom.left ≫ C.projection.app (KY.obj W)
      change (C.functor.map (KY.map i)).hom.left ≫ C.projection.app (KY.obj W) =
        C.projection.app (KY.obj U) ≫ (KY.map i).hom.left at hn
      rw [hn, ← Category.assoc]
      rw [← Category.assoc b.hom.left,
        show b.hom.left ≫ C.projection.app (KY.obj U) = qq from
          (C.isPullback (KY.obj U)).lift_fst _ _ _]
      apply ObjectProperty.hom_ext
      exact (Category.assoc _ _ _).trans
        ((congrArg (fun k => yoneda.map p₀ ≫ k) hg).symm.trans hpq.w)
    · exact (KX.map e ≫ a).hom.w.trans (b ≫ C.functor.map (KY.map i)).hom.w.symm
  · have hr := range_pointsMap_pullback B S hS hsq
    change Set.range (pointsMap B S hS _ (yoneda.map p₀)) = _
    change Set.range (pointsMap B S hS _ (yoneda.map p₀)) =
      pointsMap B S hS _ (yoneda.map g) ⁻¹'
        Set.range (pointsMap B S hS _ (yoneda.map i.hom.left)) at hr
    rw [hr, hi]
    have he := congrArg (pointsMap B S hS _) hc
    rw [pointsMap_comp, pointsMap_comp] at he
    ext x
    exact (congrArg (fun g => g x ∈ Tᶜ) he).to_iff

private theorem range_submodule_inclusion
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS)
    (M : Modules B S hS X.1 X.2) (N : M.Submodule)
    (U : SmallEtale B S hS X.1) :
    Set.range ((N.ι).val.app (op U)) =
      {s : ↑(M.val.obj (op U)) | s ∈ N.toSubmodule.obj (op U)} := by
  ext s
  constructor
  · rintro ⟨t, rfl⟩
    exact t.2
  · exact fun hs => ⟨⟨s, hs⟩, rfl⟩

private theorem range_supportedSectionsSubmodule
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS)
    (T : Set (points B S hS X.1))
    (F : Modules B S hS X.1 X.2)
    (W : SmallEtale B S hS X.1) :
    Set.range (((supportedSectionsSubmodule B S hS X.1 X.2 T F).ι).val.app
      (op W)) =
    {s : ↑(F.val.obj (op W)) |
      SectionSupportedIn B S hS X.1 X.2 T F W s} := by
  rw [range_submodule_inclusion B S hS X F _ W]
  ext s
  exact (supportedSectionsSubmoduleData B S hS X.1 X.2 T F).2 W s

private theorem spaces_supported_range_iff
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS)
    (T : Set (points B S hS X.1))
    (F : Modules.{u, u} B S hS X.1 X.2)
    (A : SpacesEtale B S hS X)
    (s : ((spacesModuleSections B S hS X).obj F).obj.obj (op A)) :
    s ∈ Set.range (((spacesModuleSections B S hS X).map
      (supportedSectionsSubmodule B S hS X.1 X.2 T F).ι).hom.app (op A)) ↔
    ∀ (Q : SmallEtale B S hS X.1)
      (a : (comparisonFunctor B S hS X).obj Q ⟶ A),
      SectionSupportedIn B S hS X.1 X.2 T F Q
        ((spacesSectionsChartIso B S hS X F Q).hom
          (((spacesModuleSections B S hS X).obj F).obj.map a.op s)) := by
  let N := supportedSectionsSubmodule B S hS X.1 X.2 T F
  let H := spacesModuleSections B S hS X
  have hm (Q) : Function.Injective (N.ι.val.app (op Q)) := Subtype.val_injective
  constructor
  · rintro ⟨t, rfl⟩ Q a
    have hnat := ConcreteCategory.congr_hom ((H.map N.ι).hom.naturality a.op) t
    have hnat' : (H.obj F).obj.map a.op ((H.map N.ι).hom.app (op A) t) =
        (H.map N.ι).hom.app (op ((comparisonFunctor B S hS X).obj Q))
          ((H.obj N.toSheafOfModules).obj.map a.op t) := hnat.symm
    rw [hnat', spacesSectionsChartIso_naturality]
    exact (supportedSectionsSubmoduleData B S hS X.1 X.2 T F).2 Q _ |>.mp
      ((spacesSectionsChartIso B S hS X N.toSheafOfModules Q).hom
        ((H.obj N.toSheafOfModules).obj.map a.op t)).2
  · intro hs
    obtain ⟨Q, Q', a, p, q, ha, hpq⟩ := exists_chart_cover B S hS X A
    apply range_of_restriction_mem_range (H.map N.ι)
      (spacesModuleSections_injective B S hS X N.ι hm) a p q ha hpq
    have ht := hs Q a
    change _ ∈ {s | SectionSupportedIn B S hS X.1 X.2 T F Q s} at ht
    rw [← range_supportedSectionsSubmodule B S hS X T F Q] at ht
    obtain ⟨t, ht⟩ := ht
    refine ⟨(spacesSectionsChartIso B S hS X N.toSheafOfModules Q).inv t, ?_⟩
    apply (ConcreteCategory.bijective_of_isIso (spacesSectionsChartIso B S hS X F Q).hom).1
    rw [spacesSectionsChartIso_naturality]
    have hinv := ConcreteCategory.congr_hom
      (spacesSectionsChartIso B S hS X N.toSheafOfModules Q).inv_hom_id t
    change (spacesSectionsChartIso B S hS X N.toSheafOfModules Q).hom
      ((spacesSectionsChartIso B S hS X N.toSheafOfModules Q).inv t) = t at hinv
    rw [hinv]
    exact ht

private theorem supportedOn_iff_zeroOnOpenChart
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : AlgebraicSpaces B S hS}
    (T : Set (points B S hS X.1))
    (F : Modules B S hS X.1 X.2)
    (W U : SmallEtale B S hS X.1) (i : U ⟶ W)
    (s : F.val.obj (op W))
    (hi : Set.range (pointsMap B S hS
      (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj U))
      (yoneda.map ((SmallEtale.toOver B S hS X.1).map i))) =
      (pointsMap B S hS
        (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj W)) W.1.hom) ⁻¹' Tᶜ) :
    SectionSupportedIn B S hS X.1 X.2 T F W s ↔
      F.val.map i.op s = 0 := by
  let H : Sheaf (SmallEtale.topology B S hS X.1) AddCommGrpCat :=
    (SheafOfModules.toSheaf
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))).obj F
  let sH : H.obj.obj (op W) := s
  let Z := largestOpenZeroLocus B S hS X.1 H W sH
  let : TopologicalSpace (points B S hS
      (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj W))) :=
    pointTopology B S hS _
  change supportOfSection B S hS X.1 H W sH ⊆
        (pointsMap B S hS
          (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj W)) W.1.hom) ⁻¹' T ↔ _
  have hmap : (F.val.map i.op) s = H.obj.map i.op sH := rfl
  have hzero : F.val.map i.op s = 0 ↔ ImageInOpen B S hS X.1 Z.1 i := by
    rw [hmap]
    exact largestOpenZeroLocus_restrict_iff B S hS X.1 H W sH U i
  constructor
  · intro hs
    apply hzero.mpr
    intro y
    have hpoint : pointsMap B S hS
        (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj U))
        (yoneda.map ((SmallEtale.toOver B S hS X.1).map i)) y ∈
        Set.range (pointsMap B S hS
          (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj U))
          (yoneda.map ((SmallEtale.toOver B S hS X.1).map i))) := ⟨y, rfl⟩
    rw [hi] at hpoint
    have hyZ : pointsMap B S hS
        (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj U))
        (yoneda.map ((SmallEtale.toOver B S hS X.1).map i)) y ∈ Z.1 := by
      by_contra hz
      have hsupp : pointsMap B S hS
          (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj U))
          (yoneda.map ((SmallEtale.toOver B S hS X.1).map i)) y ∈
            supportOfSection B S hS X.1 H W sH := by
        simpa [supportOfSection] using hz
      exact hpoint (hs hsupp)
    exact hyZ
  · intro hz x hx
    by_contra hxT
    have hxrange : x ∈ Set.range (pointsMap B S hS
        (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj U))
        (yoneda.map ((SmallEtale.toOver B S hS X.1).map i))) := by
      rw [hi]
      exact hxT
    rcases hxrange with ⟨y, hy⟩
    have hyZ := hzero.mp hz y
    have hxZ : x ∈ Z.1 := by simpa [← hy] using hyZ
    have hxnotZ : x ∉ Z.1 := by
      simpa [supportOfSection] using hx
    exact hxnotZ hxZ

private theorem sectionSupportedIn_iff_restrict_eq_zero
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS)
    (T : Set (points B S hS X.1))
    (hT : @IsClosed _ (pointTopology B S hS X.1) T)
    (F : Modules B S hS X.1 X.2)
    (W : SmallEtale B S hS X.1) (s : F.val.obj (op W)) :
    SectionSupportedIn B S hS X.1 X.2 T F W s ↔
      ∀ (U : SmallEtale B S hS X.1) (i : U ⟶ W),
        ImageInOpen B S hS X.1
          (pointsMap B S hS _ W.1.hom ⁻¹' Tᶜ) i →
        F.val.map i.op s = 0 := by
  classical
  let H := (SheafOfModules.toSheaf _).obj F
  let A := (SmallEtale.toOver B S hS X.1).obj W
  let := pointTopology B S hS X.1
  let := pointTopology B S hS (yoneda.obj A)
  let O : TopologicalSpace.Opens (points B S hS (yoneda.obj A)) :=
    ⟨pointsMap B S hS _ W.1.hom ⁻¹' Tᶜ,
      hT.isOpen_compl.preimage ((pointTopologyFamily B S hS).continuous
        (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS A) X.2 W.1.hom)⟩
  let Z := largestOpenZeroLocus B S hS X.1 H W s
  constructor
  · intro hs U i hi
    apply (largestOpenZeroLocus_restrict_iff B S hS X.1 H W s U i).2
    intro x
    by_contra hx
    exact hi x (hs hx)
  · intro hs x hx
    by_contra hxt
    exact hx (largestOpenZeroLocus_maximal B S hS X.1 H W s O hs hxt)

private theorem chart_over_complement
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (T : Set (points B S hS Y.1))
    (W U : SmallEtale B S hS Y.1) (i : U ⟶ W)
    (hi : Set.range (pointsMap B S hS _ (yoneda.map i.hom.left)) =
      pointsMap B S hS _ W.1.hom ⁻¹' Tᶜ)
    (Q : SmallEtale B S hS X.1)
    (b : (comparisonFunctor B S hS X).obj Q ⟶
      (spacesBaseChange B S hS f).functor.obj ((comparisonFunctor B S hS Y).obj U))
    (x : points B S hS (yoneda.obj Q.1.left)) :
    pointsMap B S hS _ Q.1.hom x ∈
      (pointsMap B S hS X.1 f.hom ⁻¹' T)ᶜ := by
  let C := spacesBaseChange B S hS f
  let V := (comparisonFunctor B S hS Y).obj U
  have hU (z : points B S hS (yoneda.obj U.1.left)) :
      pointsMap B S hS _ U.1.hom z ∈ Tᶜ := by
    have hz : pointsMap B S hS _ (yoneda.map i.hom.left) z ∈
        pointsMap B S hS _ W.1.hom ⁻¹' Tᶜ := by
      rw [← hi]
      exact ⟨z, rfl⟩
    have hw : yoneda.map i.hom.left ≫ W.1.hom = U.1.hom := by simp
    rw [← hw, pointsMap_comp]
    exact hz
  have hc : Q.1.hom ≫ f.hom =
      b.hom.left.hom ≫ (C.projection.app V).hom ≫ U.1.hom := by
    have h := congrArg (fun k => k.hom) (C.isPullback V).w
    change (C.projection.app V).hom ≫ U.1.hom =
      (C.functor.obj V).1.hom.hom ≫ f.hom at h
    rw [h, ← Category.assoc]
    exact (congrArg (fun k => k.hom ≫ f.hom) b.hom.w).symm
  have key : pointsMap B S hS _ (Q.1.hom ≫ f.hom) x =
      pointsMap B S hS _ (b.hom.left.hom ≫ (C.projection.app V).hom ≫ U.1.hom) x :=
    congrArg (fun k => pointsMap B S hS _ k x) hc
  have hl : pointsMap B S hS _ (Q.1.hom ≫ f.hom) x =
      pointsMap B S hS X.1 f.hom (pointsMap B S hS _ Q.1.hom x) :=
    congrFun (pointsMap_comp B S hS _ Q.1.hom f.hom) x
  have hr : pointsMap B S hS _ (b.hom.left.hom ≫ (C.projection.app V).hom ≫ U.1.hom) x =
      pointsMap B S hS _ ((C.projection.app V).hom ≫ U.1.hom)
        (pointsMap B S hS _ b.hom.left.hom x) :=
    congrFun (pointsMap_comp B S hS _ b.hom.left.hom
      ((C.projection.app V).hom ≫ U.1.hom)) x
  have hr2 : pointsMap B S hS _ ((C.projection.app V).hom ≫ U.1.hom)
        (pointsMap B S hS _ b.hom.left.hom x) =
      pointsMap B S hS _ U.1.hom
        (pointsMap B S hS _ (C.projection.app V).hom
          (pointsMap B S hS _ b.hom.left.hom x)) :=
    congrFun (pointsMap_comp B S hS _ (C.projection.app V).hom U.1.hom) _
  change pointsMap B S hS X.1 f.hom
    (pointsMap B S hS _ Q.1.hom x) ∈ Tᶜ
  rw [← hl, key, hr, hr2]
  exact hU _

private theorem spaces_supported_range_eq_zero
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (T : Set (points B S hS Y.1))
    (hT : @IsClosed _ (pointTopology B S hS Y.1) T)
    (F : Modules B S hS X.1 X.2)
    (W U : SmallEtale B S hS Y.1) (i : U ⟶ W)
    (hiOpen : IsOpenImmersion B S hS (yoneda.map i.hom.left))
    (hi : Set.range (pointsMap B S hS _ (yoneda.map i.hom.left)) =
      pointsMap B S hS _ W.1.hom ⁻¹' Tᶜ) :
    Set.range (((spacesModuleSections B S hS X).map
      (supportedSectionsSubmodule B S hS X.1 X.2
        (pointsMap B S hS X.1 f.hom ⁻¹' T) F).ι).hom.app
          (op ((spacesBaseChange B S hS f).functor.obj
            ((comparisonFunctor B S hS Y).obj W)))) =
      {s | ((spacesModuleSections B S hS X).obj F).obj.map
        ((spacesBaseChange B S hS f).functor.map
          ((comparisonFunctor B S hS Y).map i)).op s = 0} := by
  let C := spacesBaseChange B S hS f
  let K := comparisonFunctor B S hS Y
  let H := (spacesModuleSections B S hS X).obj F
  let Tx := pointsMap B S hS X.1 f.hom ⁻¹' T
  let := pointTopology B S hS X.1
  let := pointTopology B S hS Y.1
  have hTx : @IsClosed _ (pointTopology B S hS X.1) Tx :=
    hT.preimage ((pointTopologyFamily B S hS).continuous X.2 Y.2 f.hom)
  ext s
  rw [spaces_supported_range_iff]
  constructor
  · intro hs
    obtain ⟨Q, Q', b, p, q, hb, hpq⟩ := exists_chart_cover B S hS X (C.functor.obj (K.obj U))
    apply restriction_injective_of_cover H b hb
    apply (ConcreteCategory.bijective_of_isIso (spacesSectionsChartIso B S hS X F Q).hom).1
    have hsup := hs Q (b ≫ C.functor.map (K.map i))
    have hz := (sectionSupportedIn_iff_restrict_eq_zero B S hS X Tx hTx F Q _).mp hsup
      Q (𝟙 Q) (by
        intro x
        change pointsMap B S hS _ (yoneda.map (𝟙 Q.1.left)) x ∈
          pointsMap B S hS _ Q.1.hom ⁻¹' Txᶜ
        rw [yoneda.map_id, pointsMap_id]
        exact chart_over_complement B S hS f T W U i hi Q b x)
    change F.val.presheaf.map (𝟙 (op Q)) _ = 0 at hz
    have hid := ConcreteCategory.congr_hom (F.val.presheaf.map_id (op Q))
      ((spacesSectionsChartIso B S hS X F Q).hom
        (((spacesModuleSections B S hS X).obj F).obj.map
          (b ≫ C.functor.map (K.map i)).op s))
    rw [ConcreteCategory.id_apply] at hid
    have hz2 := hid.symm.trans hz
    simp only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply] at hz2
    have hgoal : (spacesSectionsChartIso B S hS X F Q).hom
        (H.obj.map b.op (H.obj.map (C.functor.map (K.map i)).op s)) = 0 := hz2
    simpa only [map_zero] using hgoal
  · intro hs Q a
    obtain ⟨E, e, b, he, hE⟩ := chart_complement_pullback B S hS f T W U i hiOpen hi Q a
    apply (supportedOn_iff_zeroOnOpenChart B S hS Tx F Q E e _ hE).mpr
    rw [← spacesSectionsChartIso_map]
    have hrestrict : H.obj.map ((comparisonFunctor B S hS X).map e).op
          (H.obj.map a.op s) =
        H.obj.map b.op (H.obj.map (C.functor.map (K.map i)).op s) := by
      simpa only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply] using
        congrArg (fun a => H.obj.map a.op s) he
    rw [hrestrict, hs, map_zero, map_zero]
    rfl

private theorem exists_openSubchart
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS)
    (W : SmallEtale B S hS X.1)
    (O : Set (points B S hS
      (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj W))))
    (hO : @IsOpen _ (pointTopology B S hS _) O) :
    ∃ (U : SmallEtale B S hS X.1) (i : U ⟶ W),
      IsOpenImmersion B S hS (yoneda.map i.hom.left) ∧
      Set.range (pointsMap B S hS _
        (yoneda.map ((SmallEtale.toOver B S hS X.1).map i))) = O := by
  classical
  let A := (SmallEtale.toOver B S hS X.1).obj W
  let hA := AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS A
  let := pointTopology B S hS (yoneda.obj A)
  let e := openSubspacesOrderIso B S hS (yoneda.obj A) hA
  let V := e.symm ⟨O, hO⟩
  have hV : Set.range (pointsMap B S hS V.1.toFunctor V.1.ι) = O := by
    rw [← openSubspacesOrderIso_apply B S hS
      (yoneda.obj A) hA V]
    exact congrArg (fun z : TopologicalSpace.Opens _ => z.1) (e.apply_symm_apply ⟨O, hO⟩)
  obtain ⟨C, q, p, hpq⟩ := V.2.2.rep (𝟙 (yoneda.obj A))
  let AS : AlgebraicSpaces B S hS := ⟨yoneda.obj A, hA⟩
  let CS : AlgebraicSpaces B S hS :=
    ⟨yoneda.obj C, AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS C⟩
  let VS : AlgebraicSpaces B S hS := ⟨V.1.toFunctor, V.2.1⟩
  let q' : CS ⟶ AS := ObjectProperty.homMk (yoneda.map q)
  let p' : CS ⟶ VS := ObjectProperty.homMk p
  let j : VS ⟶ AS := ObjectProperty.homMk V.1.ι
  have hsq : IsPullback q' p' (𝟙 AS) j := by
    apply IsPullback.of_map_of_faithful (ObjectProperty.ι _)
    exact hpq.flip
  have hq : IsOpenImmersion B S hS (yoneda.map q) :=
    isOpenImmersion_of_isPullback B S hS hsq.flip V.2.2
  let U : SmallEtale B S hS X.1 :=
    ⟨CostructuredArrow.mk (yoneda.map q ≫ W.1.hom),
      etaleChart_comp_open B S hS _ _ hq W.2⟩
  let i : U ⟶ W := ⟨CostructuredArrow.homMk q (by rfl)⟩
  refine ⟨U, i, hq, ?_⟩
  have h := range_pointsMap_pullback B S hS hsq
  change Set.range (pointsMap B S hS (yoneda.obj C) (yoneda.map q)) = O
  change Set.range (pointsMap B S hS (yoneda.obj C) (yoneda.map q)) =
    pointsMap B S hS (yoneda.obj A) (𝟙 _) ⁻¹'
      Set.range (pointsMap B S hS V.1.toFunctor V.1.ι) at h
  simpa only [pointsMap_id, Set.preimage_id, hV] using h

/-- The component of `AlgebraicGeometry.Space.pushforwardSpacesSectionsIso` over an étale chart
`Q` of the target: from sections of the direct image over `Q` to sections of the module over the
inverse image of `Q` on the spaces-étale site. -/
private def pushforwardChartComparison
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (G : Modules.{u, u} B S hS X.1 X.2) (Q : SmallEtale B S hS Y.1) :
    letI := comparisonFunctor_isContinuous B S hS Y
    letI := (spacesBaseChange_isMorphismOfSites B S hS f).isContinuous
    (((smallEtaleRingedToposHom B S hS f).pushforwardModules).obj G).val.obj (op Q) →
      ((spacesModuleSections B S hS X).obj G).obj.obj
        (op ((spacesBaseChange B S hS f).functor.obj
          ((comparisonFunctor B S hS Y).obj Q))) := by
  letI := comparisonFunctor_isContinuous B S hS Y
  letI := (spacesBaseChange_isMorphismOfSites B S hS f).isContinuous
  exact fun s => ((pushforwardSpacesSectionsIso B S hS f).hom.app G).hom.app (op Q) s

/-- The chart comparison is bijective. -/
private theorem pushforwardChartComparison_bijective
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (G : Modules.{u, u} B S hS X.1 X.2) (Q : SmallEtale B S hS Y.1) :
    Function.Bijective (pushforwardChartComparison B S hS f G Q) := by
  let := comparisonFunctor_isContinuous B S hS Y
  let := (spacesBaseChange_isMorphismOfSites B S hS f).isContinuous
  exact (((sheafToPresheaf _ _).mapIso
    ((pushforwardSpacesSectionsIso B S hS f).app G)).app (op Q)).toEquiv.bijective

/-- The chart comparison is natural in the module. -/
private theorem pushforwardChartComparison_naturality
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    {G G' : Modules.{u, u} B S hS X.1 X.2} (m : G ⟶ G')
    (Q : SmallEtale B S hS Y.1)
    (t : (((smallEtaleRingedToposHom B S hS f).pushforwardModules).obj G).val.obj (op Q)) :
    pushforwardChartComparison B S hS f G' Q
        ((((smallEtaleRingedToposHom B S hS f).pushforwardModules).map m).val.app (op Q) t) =
      ((spacesModuleSections B S hS X).map m).hom.app
        (op ((spacesBaseChange B S hS f).functor.obj
          ((comparisonFunctor B S hS Y).obj Q)))
        (pushforwardChartComparison B S hS f G Q t) := by
  let := comparisonFunctor_isContinuous B S hS Y
  let := (spacesBaseChange_isMorphismOfSites B S hS f).isContinuous
  exact congrArg (fun a => a.hom.app (op Q) t)
    ((pushforwardSpacesSectionsIso B S hS f).hom.naturality m)

/-- The chart comparison takes the zero section to the zero section. -/
private theorem pushforwardChartComparison_zero
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (G : Modules.{u, u} B S hS X.1 X.2) (Q : SmallEtale B S hS Y.1) :
    pushforwardChartComparison B S hS f G Q 0 = 0 :=
  have hzero : (((smallEtaleRingedToposHom B S hS f).pushforwardModules).map
      (0 : G ⟶ G)).val.app (op Q) 0 = 0 := map_zero _
  (congrArg (pushforwardChartComparison B S hS f G Q) hzero).symm.trans
    ((pushforwardChartComparison_naturality B S hS f (0 : G ⟶ G) Q 0).trans
      (spacesModuleSections_map_zero_app B S hS X G _ _))

/-- The chart comparison is compatible with restriction along a morphism of étale charts of
the target. -/
private theorem pushforwardChartComparison_restrict
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (G : Modules.{u, u} B S hS X.1 X.2)
    {Q Q' : SmallEtale B S hS Y.1} (i : Q' ⟶ Q)
    (s : (((smallEtaleRingedToposHom B S hS f).pushforwardModules).obj G).val.obj (op Q)) :
    pushforwardChartComparison B S hS f G Q'
        ((((smallEtaleRingedToposHom B S hS f).pushforwardModules).obj G).val.map i.op s) =
      ((spacesModuleSections B S hS X).obj G).obj.map
        ((spacesBaseChange B S hS f).functor.map
          ((comparisonFunctor B S hS Y).map i)).op
        (pushforwardChartComparison B S hS f G Q s) := by
  let := comparisonFunctor_isContinuous B S hS Y
  let := (spacesBaseChange_isMorphismOfSites B S hS f).isContinuous
  exact ConcreteCategory.congr_hom
    (((pushforwardSpacesSectionsIso B S hS f).hom.app G).hom.naturality i.op) s

/-- The chart comparison carries the image of a map of `𝒪_X`-modules to the image of the
induced map on spaces-étale sections: a section of the direct image over `Q` comes from the
direct image of the source exactly when its comparison image comes from the source. -/
private theorem pushforwardChartComparison_mem_range_iff
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    {G G' : Modules.{u, u} B S hS X.1 X.2} (m : G ⟶ G')
    (Q : SmallEtale B S hS Y.1)
    (s : (((smallEtaleRingedToposHom B S hS f).pushforwardModules).obj G').val.obj (op Q)) :
    (∃ t, (((smallEtaleRingedToposHom B S hS f).pushforwardModules).map m).val.app (op Q) t =
        s) ↔
      pushforwardChartComparison B S hS f G' Q s ∈
        Set.range (((spacesModuleSections B S hS X).map m).hom.app
          (op ((spacesBaseChange B S hS f).functor.obj
            ((comparisonFunctor B S hS Y).obj Q)))) := by
  refine ⟨fun ⟨t, ht⟩ => ht ▸ ⟨pushforwardChartComparison B S hS f G Q t,
    (pushforwardChartComparison_naturality B S hS f m Q t).symm⟩, ?_⟩
  rintro ⟨t, ht⟩
  obtain ⟨t', rfl⟩ := (pushforwardChartComparison_bijective B S hS f G Q).2 t
  exact ⟨t', (pushforwardChartComparison_bijective B S hS f G' Q).1
    ((pushforwardChartComparison_naturality B S hS f m Q t').trans ht)⟩

/-- Vanishing of a section of the direct image after restriction to a subchart is detected by
the chart comparison. -/
private theorem pushforwardChartComparison_restrict_eq_zero_iff
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (G : Modules.{u, u} B S hS X.1 X.2)
    {Q Q' : SmallEtale B S hS Y.1} (i : Q' ⟶ Q)
    (s : (((smallEtaleRingedToposHom B S hS f).pushforwardModules).obj G).val.obj (op Q)) :
    ((spacesModuleSections B S hS X).obj G).obj.map
        ((spacesBaseChange B S hS f).functor.map
          ((comparisonFunctor B S hS Y).map i)).op
        (pushforwardChartComparison B S hS f G Q s) = 0 ↔
      (((smallEtaleRingedToposHom B S hS f).pushforwardModules).obj G).val.map i.op s = 0 :=
  ⟨fun h => (pushforwardChartComparison_bijective B S hS f G Q').1
      (((pushforwardChartComparison_restrict B S hS f G i s).trans h).trans
        (pushforwardChartComparison_zero B S hS f G Q').symm),
    fun h => ((pushforwardChartComparison_restrict B S hS f G i s).symm.trans
      (congrArg (pushforwardChartComparison B S hS f G Q') h)).trans
      (pushforwardChartComparison_zero B S hS f G Q')⟩

/-- A section of the direct image over a chart `W` of `Y` is supported on `T` exactly when it
comes from the direct image of the subsheaf of sections supported over `|f|⁻¹T`, given a
subchart `i : U ⟶ W` representing the part of `W` lying over the complement of `T`. -/
private theorem pushforward_sectionSupportedIn_iff_of_subchart
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (T : Set (points B S hS Y.1))
    (hT : @IsClosed _ (pointTopology B S hS Y.1) T)
    (F : Modules.{u, u} B S hS X.1 X.2)
    (W U : SmallEtale B S hS Y.1) (i : U ⟶ W)
    (hiOpen : IsOpenImmersion B S hS (yoneda.map i.hom.left))
    (hi : Set.range (pointsMap B S hS _ (yoneda.map i.hom.left)) =
      pointsMap B S hS _ W.1.hom ⁻¹' Tᶜ)
    (s : (((smallEtaleRingedToposHom B S hS f).pushforwardModules).obj F).val.obj (op W)) :
    (∃ t, (((smallEtaleRingedToposHom B S hS f).pushforwardModules).map
        (supportedSectionsSubmodule B S hS X.1 X.2
          (pointsMap B S hS X.1 f.hom ⁻¹' T) F).ι).val.app (op W) t = s) ↔
      SectionSupportedIn B S hS Y.1 Y.2 T
        (((smallEtaleRingedToposHom B S hS f).pushforwardModules).obj F) W s :=
  (pushforwardChartComparison_mem_range_iff B S hS f
      (supportedSectionsSubmodule B S hS X.1 X.2
        (pointsMap B S hS X.1 f.hom ⁻¹' T) F).ι W s).trans
    ((Set.ext_iff.mp (spaces_supported_range_eq_zero B S hS f T hT F W U i hiOpen hi)
        (pushforwardChartComparison B S hS f F W s)).trans
      ((pushforwardChartComparison_restrict_eq_zero_iff B S hS f F i s).trans
        (supportedOn_iff_zeroOnOpenChart B S hS T
          (((smallEtaleRingedToposHom B S hS f).pushforwardModules).obj F) W U i s hi).symm))

/-- The identification of the two subsheaves of the direct image over a chart `W` of `Y`, given
a subchart `i : U ⟶ W` that represents the part of `W` lying over the complement of `T`. -/
private theorem pushforward_supportedSections_range_eq_of_subchart
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (T : Set (points B S hS Y.1))
    (hT : @IsClosed _ (pointTopology B S hS Y.1) T)
    (F : Modules.{u, u} B S hS X.1 X.2)
    (W U : SmallEtale B S hS Y.1) (i : U ⟶ W)
    (hiOpen : IsOpenImmersion B S hS (yoneda.map i.hom.left))
    (hi : Set.range (pointsMap B S hS _ (yoneda.map i.hom.left)) =
      pointsMap B S hS _ W.1.hom ⁻¹' Tᶜ) :
    Set.range ((((smallEtaleRingedToposHom B S hS f).pushforwardModules).map
      (supportedSectionsSubmodule B S hS X.1 X.2
        (pointsMap B S hS X.1 f.hom ⁻¹' T) F).ι).val.app (op W)) =
    Set.range (((supportedSectionsSubmodule B S hS Y.1 Y.2 T
      (((smallEtaleRingedToposHom B S hS f).pushforwardModules).obj F)).ι).val.app (op W)) := by
  rw [range_supportedSectionsSubmodule B S hS Y T
    (((smallEtaleRingedToposHom B S hS f).pushforwardModules).obj F) W]
  ext s
  exact pushforward_sectionSupportedIn_iff_of_subchart B S hS f T hT F W U i hiOpen hi s

/-- For a morphism `f : X ⟶ Y` of algebraic spaces over `S`, a closed subset
`T` of the points of `Y` and an `𝒪_X`-module `F`, the direct image of the subsheaf of sections
supported over `|f|⁻¹T` is the subsheaf of `f_*F` of sections supported on `T`: the two
canonical inclusions into `f_*F` have the same image over every étale chart of `Y`. -/
@[stacks 085B "the identification of the two subsheaves of the direct image"]
theorem pushforward_supportedSectionsSubmodule_range_eq
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (T : Set (points B S hS Y.1))
    (hT : @IsClosed _ (pointTopology B S hS Y.1) T)
    (F : Modules.{u, u} B S hS X.1 X.2)
    (W : SmallEtale B S hS Y.1) :
    Set.range ((((smallEtaleRingedToposHom B S hS f).pushforwardModules).map
      (supportedSectionsSubmodule B S hS X.1 X.2
        (pointsMap B S hS X.1 f.hom ⁻¹' T) F).ι).val.app (op W)) =
    Set.range (((supportedSectionsSubmodule B S hS Y.1 Y.2 T
      (((smallEtaleRingedToposHom B S hS f).pushforwardModules).obj F)).ι).val.app (op W)) := by
  let := pointTopology B S hS Y.1
  let A := W.1.left
  let := pointTopology B S hS (yoneda.obj A)
  have hO : IsOpen (pointsMap B S hS (yoneda.obj A) W.1.hom ⁻¹' Tᶜ) :=
    hT.isOpen_compl.preimage ((pointTopologyFamily B S hS).continuous
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS A) Y.2 W.1.hom)
  exact (exists_openSubchart B S hS Y W _ hO).elim fun U hU => hU.elim fun i hiU =>
    pushforward_supportedSections_range_eq_of_subchart B S hS f T hT F W U i hiU.1 hiU.2

end AlgebraicGeometry.Space

end
