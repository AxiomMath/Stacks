module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.SheafOfModules
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Limits.Types.Equalizers
public import Mathlib.CategoryTheory.Preadditive.LeftExact
public import Mathlib.CategoryTheory.Sites.Abelian
import StacksCore.Tactic.StacksAttribute

/-!
# Limits and colimits of sheaves of modules

Sheaves of modules over a sheaf of rings have all limits and all colimits, the forgetful
functor to sheaves of abelian groups preserves both, the category is abelian, and its
filtered colimits are exact.

## Main results

* `SheafOfModules.hasLimitsOfSize` and
  `SheafOfModules.instHasColimitsOfSizeOfPresheafOfModulesObjFunctorOppositeRingCatIsSheaf`
  give the existence of limits and of colimits.
* `AlgebraicGeometry.SheafOfModules.hasSheafify_of_locallyBijective`: weak sheafification of
  abelian presheaves is left exact when the maps it inverts are exactly the locally bijective
  ones.
* `AlgebraicGeometry.SheafOfModules.instAbelianSheafOfModules`: the abelian category
  structure, with the module, ring and site universes independent.
* `AlgebraicGeometry.SheafOfModules.instAB5SheafOfModules`: filtered colimits are exact.
* `AlgebraicGeometry.SheafOfModules.toSheaf_preservesLimits` and
  `AlgebraicGeometry.SheafOfModules.toSheaf_preservesColimits`: the canonical,
  diagram-natural compatibility of the forgetful functor with limits and with colimits.

## Implementation notes

The results are stated for sheaves of modules over an arbitrary sheaf of rings, which
includes the sheaf of rings underlying a ringed topos. Existence of limits and of colimits
is taken from Mathlib. The local-bijectivity hypothesis makes weak sheafification left exact:
the map between the kernels of a locally bijective square is itself locally bijective. This
supplies `HasSheafify` without a size restriction on the site, and hence the abelian
structure. Exactness of filtered colimits descends from presheaves along this left exact
reflection; no separator or small-site hypothesis is needed. Preservation by
`SheafOfModules.toSheaf` expresses the canonical comparison isomorphisms with limits and
colimits of abelian sheaves, including their naturality in the diagram. Diagram objects lie
in the module universe `v`, as in the pointwise existence construction; the larger hom
universe of the sheaf category does not enlarge this bound.

## References

* [Stacks Project, Tag 03DB](https://stacks.math.columbia.edu/tag/03DB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

add_to_stacks 03DB "existence of limits" SheafOfModules.hasLimitsOfSize
add_to_stacks 03DB "existence of colimits"
  SheafOfModules.instHasColimitsOfSizeOfPresheafOfModulesObjFunctorOppositeRingCatIsSheaf

universe v v' u' u w'

namespace AlgebraicGeometry.SheafOfModules

section Abelian

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}

/-- A section of an abelian presheaf killed by a map lifts to the kernel of that map. -/
private lemma kernel_app_lift {P Q : Cᵒᵖ ⥤ AddCommGrpCat.{v}} (f : P ⟶ Q)
    (X : Cᵒᵖ) (x : P.obj X) (hx : f.app X x = 0) :
    ∃ y : (kernel f).obj X, (kernel.ι f).app X y = x := by
  let E := (evaluation Cᵒᵖ AddCommGrpCat).obj X ⋙ forget AddCommGrpCat
  exact (Types.unique_of_type_equalizer _ _
    (isLimitForkMapOfIsLimit E (kernel.condition f) (kernelIsKernel f)) x hx).exists

/-- The map induced on kernels by a commuting square whose left edge is locally bijective
and whose right edge is locally injective is itself locally bijective. -/
private lemma kernel_map_locallyBijective
    {P Q P' Q' : Cᵒᵖ ⥤ AddCommGrpCat.{v}} (f : P ⟶ Q) (g : P' ⟶ Q')
    (a : P ⟶ P') (b : Q ⟶ Q') (h : f ≫ b = a ≫ g)
    [Presheaf.IsLocallyInjective J a] [Presheaf.IsLocallySurjective J a]
    [Presheaf.IsLocallyInjective J b] :
    Presheaf.IsLocallyInjective J (kernel.map f g a b h) ∧
      Presheaf.IsLocallySurjective J (kernel.map f g a b h) := by
  let k := kernel.map f g a b h
  have fac : k ≫ kernel.ι g = kernel.ι f ≫ a := by simp [k]
  constructor
  · have : Presheaf.IsLocallyInjective J (kernel.ι f) :=
      Presheaf.isLocallyInjective_of_injective J _ fun X ↦
        (AddCommGrpCat.mono_iff_injective _).mp inferInstance
    have : Presheaf.IsLocallyInjective J (k ≫ kernel.ι g) := by
      rw [fac]
      infer_instance
    exact Presheaf.isLocallyInjective_of_isLocallyInjective J k (kernel.ι g)
  · constructor
    intro X x
    apply J.transitive (Presheaf.imageSieve_mem J a ((kernel.ι g).app _ x))
    rintro Y i ⟨y, hy⟩
    have hb : b.app _ (f.app _ y) = b.app _ 0 := by
      have hxy := ConcreteCategory.congr_hom (NatTrans.congr_app h (op Y)) y
      dsimp at hxy
      rw [hxy, hy, NatTrans.naturality_apply]
      have hz := ConcreteCategory.congr_hom (NatTrans.congr_app (kernel.condition g) (op X)) x
      change g.app _ ((kernel.ι g).app _ x) = 0 at hz
      rw [hz, map_zero, map_zero]
    apply J.superset_covering _ (Presheaf.equalizerSieve_mem J b (f.app _ y) 0 hb)
    intro Z j hj
    have hz : f.app _ (P.map j.op y) = 0 := by
      rw [NatTrans.naturality_apply]
      simpa only [Presheaf.equalizerSieve_apply, map_zero] using hj
    obtain ⟨z, hz'⟩ := kernel_app_lift f (op Z) (P.map j.op y) hz
    refine ⟨z, (AddCommGrpCat.mono_iff_injective ((kernel.ι g).app _)).mp inferInstance ?_⟩
    have hk := ConcreteCategory.congr_hom (NatTrans.congr_app fac (op Z)) z
    dsimp at hk
    rw [hk, hz', NatTrans.naturality_apply, hy]
    simp only [NatTrans.naturality_apply, op_comp, Functor.map_comp,
      ConcreteCategory.comp_apply]

variable [HasWeakSheafify J AddCommGrpCat.{v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{v}]

/-- Weak sheafification of abelian presheaves preserves the kernel of any map. -/
private theorem preservesKernel_sheafification
    [(presheafToSheaf J AddCommGrpCat.{v}).Additive]
    {P Q : Cᵒᵖ ⥤ AddCommGrpCat.{v}} (f : P ⟶ Q) :
    PreservesLimit (parallelPair f 0) (presheafToSheaf J AddCommGrpCat.{v}) := by
  let L := presheafToSheaf J AddCommGrpCat.{v}
  let U := sheafToPresheaf J AddCommGrpCat.{v}
  let a := toSheafify J P
  let b := toSheafify J Q
  have h : f ≫ b = a ≫ U.map (L.map f) := toSheafify_naturality J f
  let k := kernel.map f (U.map (L.map f)) a b h
  have hk : J.W k := by
    rw [J.W_iff_isLocallyBijective]
    exact kernel_map_locallyBijective f _ a b h
  have fac : toSheafify J (kernel f) ≫ U.map (kernelComparison f L) ≫
      kernelComparison (L.map f) U = k := by
    apply equalizer.hom_ext
    simp only [Category.assoc, kernelComparison_comp_ι, ← U.map_comp,
      k, kernel.lift_ι]
    exact (toSheafify_naturality J (kernel.ι f)).symm
  have : J.W (U.map (kernelComparison f L)) := by
    have hη := J.W_toSheafify (kernel f)
    rw [J.W_iff] at hk hη ⊢
    have hiso : IsIso (L.map (toSheafify J (kernel f)) ≫
        L.map (U.map (kernelComparison f L)) ≫ L.map (kernelComparison (L.map f) U)) := by
      simpa only [← L.map_comp, fac] using hk
    exact (isIso_comp_left_iff _ _).mp ((isIso_comp_right_iff _ _).mp hiso)
  have : IsIso (kernelComparison f L) := (J.W_sheafToPresheaf_map_iff_isIso _).mp this
  exact PreservesKernel.of_iso_comparison L f

/-- Weak sheafification of abelian presheaves is left exact when its inverted
maps are precisely the locally bijective maps. -/
theorem hasSheafify_of_locallyBijective : HasSheafify J AddCommGrpCat.{v} := by
  let L := presheafToSheaf J AddCommGrpCat.{v}
  have : L.Additive := (sheafificationAdjunction J AddCommGrpCat).left_adjoint_additive
  have : ∀ {P Q : Cᵒᵖ ⥤ AddCommGrpCat.{v}} (f : P ⟶ Q),
      PreservesLimit (parallelPair f 0) L := preservesKernel_sheafification
  have : HasBinaryBiproducts (Cᵒᵖ ⥤ AddCommGrpCat.{v}) :=
    HasBinaryBiproducts.of_hasBinaryProducts
  have : HasZeroObject (Sheaf J AddCommGrpCat.{v}) :=
    hasZeroObject_of_hasTerminal_object
  have : PreservesFiniteLimits L := L.preservesFiniteLimits_of_preservesKernels
  exact HasSheafify.mk' J AddCommGrpCat (sheafificationAdjunction J AddCommGrpCat)

/-- Sheaves of modules form an abelian category, with the module, ring, and
site universes independent. -/
@[sga "4 II 6.7"]
noncomputable instance (priority := 100) instAbelianSheafOfModules (R : Sheaf J RingCat.{u}) :
    Abelian (_root_.SheafOfModules.{v} R) := by
  have : HasSheafify J AddCommGrpCat.{v} := hasSheafify_of_locallyBijective
  exact _root_.SheafOfModules.instAbelian R

/-- Filtered colimits of sheaves of modules are exact. -/
@[stacks 03DB "exactness of filtered colimits",
  sga "4 II 6.7" "(AB 5)",
  sga "3 I 3.1.1" "more general"]
noncomputable instance instAB5SheafOfModules (R : Sheaf J RingCat.{u}) :
    AB5OfSize.{v, v} (_root_.SheafOfModules.{v} R) := by
  have : HasSheafify J AddCommGrpCat.{v} := hasSheafify_of_locallyBijective
  have (K : Type v) [Category.{v} K] [IsFiltered K] :
      HasExactColimitsOfShape K (PresheafOfModules.{v} R.obj) :=
    HasExactColimitsOfShape.domain_of_functor K (PresheafOfModules.toPresheaf R.obj)
  exact ⟨fun K _ _ ↦
    (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).hasExactColimitsOfShape K⟩

end Abelian

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}
  (R : Sheaf J RingCat.{u})

/-- Forgetting a sheaf of modules to an abelian sheaf preserves all limits
indexed by diagram objects in the module universe. -/
@[stacks 03DB "forgetful functor preserves limits"]
theorem toSheaf_preservesLimits :
    PreservesLimitsOfSize.{max u' v, v} (_root_.SheafOfModules.toSheaf.{v} R) where
  preservesLimitsOfShape {K} _ := by
    have : PreservesLimitsOfShape K
        (_root_.SheafOfModules.toSheaf.{v} R ⋙ sheafToPresheaf J AddCommGrpCat.{v}) :=
      comp_preservesLimitsOfShape (_root_.SheafOfModules.forget.{v} R)
        (PresheafOfModules.toPresheaf R.obj)
    exact preservesLimitsOfShape_of_reflects_of_preserves
      (_root_.SheafOfModules.toSheaf R) (sheafToPresheaf J AddCommGrpCat)

/-- Sheafifying a diagram of presheaves of modules and then forgetting to abelian sheaves
preserves its colimit. -/
private theorem sheafifyToSheaf_preservesColimit {K : Type v} [Category.{w'} K]
    (R : Sheaf J RingCat.{u})
    [HasWeakSheafify J AddCommGrpCat.{v}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{v}]
    (P : K ⥤ PresheafOfModules.{v} R.obj) :
    PreservesColimit P
      (PresheafOfModules.sheafification (𝟙 R.obj) ⋙ _root_.SheafOfModules.toSheaf.{v} R) :=
  (preservesColimit_iff_of_natIso P
    (PresheafOfModules.sheafificationCompToSheaf (𝟙 R.obj))).mpr inferInstance

/-- Forgetting a sheaf of modules to an abelian sheaf preserves the colimit of a single
diagram. -/
private theorem toSheaf_preservesColimit_aux {K : Type v} [Category.{w'} K]
    (R : Sheaf J RingCat.{u})
    [HasWeakSheafify J AddCommGrpCat.{v}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{v}]
    (F : K ⥤ _root_.SheafOfModules.{v} R) :
    PreservesColimit F (_root_.SheafOfModules.toSheaf.{v} R) := by
  let S := PresheafOfModules.sheafification (𝟙 R.obj)
  let P := F ⋙ _root_.SheafOfModules.forget R
  let e : F ≅ P ⋙ S :=
    Functor.isoWhiskerLeft F
      (asIso (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).counit).symm
  have : PreservesColimit P (S ⋙ _root_.SheafOfModules.toSheaf.{v} R) :=
    sheafifyToSheaf_preservesColimit R P
  have : PreservesColimit (P ⋙ S) (_root_.SheafOfModules.toSheaf.{v} R) :=
    preservesColimit_of_preserves_colimit_cocone (isColimitOfPreserves S (colimit.isColimit P))
      (isColimitOfPreserves (S ⋙ _root_.SheafOfModules.toSheaf.{v} R) (colimit.isColimit P))
  exact preservesColimit_of_iso_diagram _ e.symm

/-- Forgetting a sheaf of modules to an abelian sheaf preserves all colimits. -/
@[stacks 03DB "forgetful functor preserves colimits"]
theorem toSheaf_preservesColimits
    [HasWeakSheafify J AddCommGrpCat.{v}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{v}] :
    PreservesColimitsOfSize.{max u' v, v} (_root_.SheafOfModules.toSheaf.{v} R) where
  preservesColimitsOfShape := ⟨toSheaf_preservesColimit_aux R _⟩

attribute [instance] toSheaf_preservesLimits toSheaf_preservesColimits

end AlgebraicGeometry.SheafOfModules
