module

public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.Abelian.SerreClass.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Coherent
public import StacksFrontier.AlgebraicGeometry.Chow.AdamsOperator.CoherentInclusionExact
public import StacksFrontier.AlgebraicGeometry.Cohomology.Coherent.AbelianCategory
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Support
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.Defs
public import StacksFrontier.Topology.Sheaves.Modules.SupportSection
public import StacksFrontier.Topology.Sheaves.Modules.Exactness
public import StacksFrontier.Topology.Sheaves.Modules.Support
public import StacksCore.Tactic.StacksAttribute

/-!
# Coherent modules supported on a closed subscheme

Let `X` be a locally Noetherian scheme and `Z` a closed subscheme. Coherent modules on `X`
whose set-theoretic support lies in `Z` form a Serre subcategory of coherent modules.

## Main definitions

* `AlgebraicGeometry.supportedCoherentProperty` is the support condition.
* `AlgebraicGeometry.SupportedCoherentModules` is the full category of coherent modules
  supported on `Z`.

## Main results

* `AlgebraicGeometry.supportedCoherentIsSerreClass`: the support condition defines a Serre
  subcategory of coherent modules.

## Implementation notes

A closed subscheme is represented by a closed immersion `i : Z ⟶ X`; its underlying closed
subset is `Set.range i.base`. Support is the support of the associated ringed-space module
sheaf. The abelian structure on coherent modules comes from the general ringed-space result
`Stacks.SheafOfModules.coherentModulesAbelian`.

## References

* [Stacks Project, Tag 0FEP](https://stacks.math.columbia.edu/tag/0FEP)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open CategoryTheory.Limits
open scoped ZeroObject

universe u

namespace AlgebraicGeometry

/-- Coherent sheaves on `X` whose support lies in the closed subscheme `Z`. -/
abbrev supportedCoherentProperty {X Z : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] :
    ObjectProperty (Stacks.SheafOfModules.CoherentModules X.ringCatSheaf) :=
  fun F =>
    (⟨F.obj.val, F.obj.isSheaf⟩ : RingedSpace.ModuleSheaf.{u} X.toRingedSpace).supp ⊆
      Set.range i.base

/-- The full subcategory of coherent sheaves supported on `Z`. -/
@[stacks 0FEP "supported_coherent"]
abbrev SupportedCoherentModules {X Z : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] :=
  (supportedCoherentProperty i).FullSubcategory

private lemma supp_middle_subset_of_stalk_exact
    {X : TopCat.{u}}
    {R : TopCat.Sheaf RingCat.{u} X}
    (F G H : SheafOfModules.{u} (J := Opens.grothendieckTopology X) R)
    (f : SheafOfModules.Hom F G) (g : SheafOfModules.Hom G H)
    (hfg : ∀ x : X,
      Function.Exact
        (fun a => (ConcreteCategory.hom ((TopCat.Presheaf.stalkFunctor Ab.{u} x).map
          ((PresheafOfModules.toPresheaf R.obj).map f.val))) a)
        (fun b => (ConcreteCategory.hom ((TopCat.Presheaf.stalkFunctor Ab.{u} x).map
          ((PresheafOfModules.toPresheaf R.obj).map g.val))) b)) :
    SheafOfModules.supp G ⊆ SheafOfModules.supp F ∪ SheafOfModules.supp H := by
  intro x hx
  by_contra hxUnion
  have hzero (K : SheafOfModules.{u} (J := Opens.grothendieckTopology X) R)
      (hK : x ∉ SheafOfModules.supp K) (a : TopCat.Presheaf.stalk (C := Ab.{u}) K.val.presheaf x) :
      a = 0 := not_not.mp fun ha => hK ⟨a, ha⟩
  change ∃ a : TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf x, a ≠ 0 at hx
  rw [← TopCat.Presheaf.stalkFunctor_obj] at hx
  obtain ⟨a, ha⟩ := hx
  have hfgx := hfg x
  simp only [TopCat.Presheaf.stalkFunctor_obj] at hfgx
  obtain ⟨b, hb⟩ := (hfgx a).mp (hzero H (hxUnion ∘ Or.inr) _)
  exact ha (by rw [← hb, hzero F (hxUnion ∘ Or.inl) b]; exact (AddCommGrpCat.Hom.hom _).map_zero)

/-- Coherent sheaves supported on a closed subscheme form a Serre subcategory. -/
@[stacks 0FEP "supported_coherent"]
instance supportedCoherentIsSerreClass {X Z : Scheme.{u}}
    [IsLocallyNoetherian X] (i : Z ⟶ X) [IsClosedImmersion i] :
    (supportedCoherentProperty i).IsSerreClass := by
  let C := Stacks.SheafOfModules.CoherentModules X.ringCatSheaf
  let M := SheafOfModules.{u} X.ringCatSheaf
  let hAb : Abelian C := Stacks.SheafOfModules.coherentModulesAbelian
    X.ringCatSheaf
  let : Preadditive C := hAb.toPreadditive
  let P := supportedCoherentProperty i
  let : P.ContainsZero := by
    let I : C ⥤ M := ObjectProperty.ι (Stacks.SheafOfModules.coherentModules X.ringCatSheaf)
    refine ⟨0, isZero_zero C, ?_⟩
    have hzero : IsZero (I.obj (0 : C)) := by
      have : PreservesFiniteLimits I :=
        Stacks.SheafOfModules.coherentModules_inclusion_preservesFiniteLimits X.ringCatSheaf
      exact I.map_isZero (isZero_zero C)
    have hstalk (x : X) : IsZero
        ((TopCat.Presheaf.stalkFunctor Ab.{u} x).obj
          ((SheafOfModules.toSheaf X.ringCatSheaf).obj (I.obj (0 : C))).obj) := by
      have hp := Functor.map_isZero (TopCat.Sheaf.forget Ab.{u} X)
        (Functor.map_isZero (SheafOfModules.toSheaf X.ringCatSheaf) hzero)
      exact Functor.map_isZero (TopCat.Presheaf.stalkFunctor Ab.{u} x) hp
    change (AlgebraicGeometry.SheafOfModules.moduleSheafOfModules
      (I.obj (0 : C))).supp ⊆ Set.range i.base
    rw [SheafOfModules.supp_eq_moduleSheaf_supp]
    rintro x ⟨a, ha⟩
    exact False.elim (ha ((AddCommGrpCat.subsingleton_of_isZero (hstalk x)).elim _ _))
  let : P.IsClosedUnderSubobjects := by
    refine ⟨?_⟩
    intro A B f hf hB x hx
    let : Mono f := hf
    let I : C ⥤ M := ObjectProperty.ι (Stacks.SheafOfModules.coherentModules X.ringCatSheaf)
    have : PreservesFiniteLimits I :=
      Stacks.SheafOfModules.coherentModules_inclusion_preservesFiniteLimits _
    let T : ShortComplex M :=
      ShortComplex.mk (0 : (0 : M) ⟶ I.obj A) (I.map f) (by simp)
    have hT : T.Exact := (T.exact_iff_mono (by simp [T])).2 (Functor.map_mono I f)
    let F := AlgebraicGeometry.SheafOfModules.stalkAddCommGroupFunctor X.ringCatSheaf x
    let : F.PreservesZeroMorphisms := ⟨by
      intro Y Z
      change (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map
          ((SheafOfModules.forget X.ringCatSheaf).map (0 : Y ⟶ Z))) = 0
      rw [Functor.map_zero, Functor.map_zero, Functor.map_zero]⟩
    let U := AlgebraicGeometry.SheafOfModules.stalkShortComplex X.ringCatSheaf T x
    have hU : U.Exact :=
      (AlgebraicGeometry.SheafOfModules.exact_iff_stalkShortComplex_exact X.ringCatSheaf T).mp hT x
    have hUf : U.f = 0 := by
      change F.map T.f = 0
      rw [show T.f = 0 by simp [T], Functor.map_zero]
    have hmap : Mono U.g := (U.exact_iff_mono hUf).1 hU
    have hinj : Function.Injective (ConcreteCategory.hom U.g) :=
      (AddCommGrpCat.mono_iff_injective _).mp hmap
    change x ∈ (AlgebraicGeometry.SheafOfModules.moduleSheafOfModules A.obj).supp at hx
    rw [SheafOfModules.supp_eq_moduleSheaf_supp] at hx
    change ∃ a : U.X₂, a ≠ 0 at hx
    obtain ⟨a, ha⟩ := hx
    have ha' : (ConcreteCategory.hom U.g) a ≠ 0 :=
      fun hz => ha (hinj (by simpa only [map_zero] using hz))
    change (AlgebraicGeometry.SheafOfModules.moduleSheafOfModules B.obj).supp
      ⊆ Set.range i.base at hB
    rw [SheafOfModules.supp_eq_moduleSheaf_supp] at hB
    exact hB ⟨ConcreteCategory.hom U.g a, ha'⟩
  let : P.IsClosedUnderQuotients := by
    refine ⟨?_⟩
    intro A B f hf hA x hx
    let : Epi f := hf
    let I : C ⥤ M := ObjectProperty.ι (Stacks.SheafOfModules.coherentModules X.ringCatSheaf)
    have : PreservesFiniteColimits I :=
      Stacks.SheafOfModules.coherentModules_inclusion_preservesFiniteColimits _
    let T : ShortComplex M := ShortComplex.mk (I.map f) (0 : I.obj B ⟶ 0) (by simp)
    have hT : T.Exact := (T.exact_iff_epi (by simp [T])).2 (Functor.map_epi I f)
    let F := AlgebraicGeometry.SheafOfModules.stalkAddCommGroupFunctor X.ringCatSheaf x
    let : F.PreservesZeroMorphisms := ⟨by
      intro Y Z
      change (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map
          ((SheafOfModules.forget X.ringCatSheaf).map (0 : Y ⟶ Z))) = 0
      rw [Functor.map_zero, Functor.map_zero, Functor.map_zero]⟩
    let U := AlgebraicGeometry.SheafOfModules.stalkShortComplex X.ringCatSheaf T x
    have hU : U.Exact :=
      (AlgebraicGeometry.SheafOfModules.exact_iff_stalkShortComplex_exact X.ringCatSheaf T).mp hT x
    have hUg : U.g = 0 := by
      change F.map T.g = 0
      rw [show T.g = 0 by simp [T], Functor.map_zero]
    have hepi : Epi U.f := (U.exact_iff_epi hUg).1 hU
    have hsurj := (AddCommGrpCat.epi_iff_surjective _).mp hepi
    change x ∈ (AlgebraicGeometry.SheafOfModules.moduleSheafOfModules B.obj).supp at hx
    rw [SheafOfModules.supp_eq_moduleSheaf_supp] at hx
    change ∃ b : U.X₂, b ≠ 0 at hx
    obtain ⟨b, hb⟩ := hx
    obtain ⟨a, ha⟩ := hsurj b
    have ha' : a ≠ 0 := fun h => hb (by rw [← ha, h, map_zero])
    change (AlgebraicGeometry.SheafOfModules.moduleSheafOfModules A.obj).supp
      ⊆ Set.range i.base at hA
    rw [SheafOfModules.supp_eq_moduleSheaf_supp] at hA
    exact hA ⟨a, ha'⟩
  let : HasZeroMorphisms C := Preadditive.preadditiveHasZeroMorphisms
  have hExt : @ObjectProperty.IsClosedUnderExtensions C _ P
      Preadditive.preadditiveHasZeroMorphisms := by
    refine ⟨?_⟩
    intro S hS h₁ h₃
    change (AlgebraicGeometry.SheafOfModules.moduleSheafOfModules
      S.X₂.obj).supp ⊆ Set.range i.base
    rw [SheafOfModules.supp_eq_moduleSheaf_supp]
    have hmid := supp_middle_subset_of_stalk_exact
      S.X₁.obj S.X₂.obj S.X₃.obj
      (SheafOfModules.Hom.mk S.f.hom.val) (SheafOfModules.Hom.mk S.g.hom.val) (by
        intro x
        let I : C ⥤ M := ObjectProperty.ι (Stacks.SheafOfModules.coherentModules X.ringCatSheaf)
        have : PreservesFiniteLimits I :=
          Stacks.SheafOfModules.coherentModules_inclusion_preservesFiniteLimits _
        have : PreservesFiniteColimits I :=
          Stacks.SheafOfModules.coherentModules_inclusion_preservesFiniteColimits _
        let T : ShortComplex M := S.map I
        have hT : T.Exact := (hS.exact).map I
        have hstalk := (AlgebraicGeometry.SheafOfModules.exact_iff_stalkShortComplex_exact
          X.ringCatSheaf T).mp hT x
        exact (ShortComplex.ab_exact_iff_function_exact _).mp hstalk)
    have h₁' : SheafOfModules.supp S.X₁.obj ⊆ Set.range i.base := by
      change (AlgebraicGeometry.SheafOfModules.moduleSheafOfModules
        S.X₁.obj).supp ⊆ Set.range i.base at h₁
      rwa [SheafOfModules.supp_eq_moduleSheaf_supp] at h₁
    have h₃' : SheafOfModules.supp S.X₃.obj ⊆ Set.range i.base := by
      change (AlgebraicGeometry.SheafOfModules.moduleSheafOfModules
        S.X₃.obj).supp ⊆ Set.range i.base at h₃
      rwa [SheafOfModules.supp_eq_moduleSheaf_supp] at h₃
    exact hmid.trans (Set.union_subset h₁' h₃')
  change P.IsSerreClass
  exact ObjectProperty.IsSerreClass.mk (toIsClosedUnderExtensions := hExt)

end AlgebraicGeometry
