module

public import StacksFrontier.AlgebraicGeometry.ModuleGlobalSections
public import StacksFrontier.AlgebraicGeometry.AmpleH1Vanishing.SectionsEpi
public import StacksFrontier.AlgebraicGeometry.Ample.AmpleCriteria
public import StacksFrontier.AlgebraicGeometry.Divisors.TensorPower
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorStalkRingedSpace
public import StacksFrontier.AlgebraicGeometry.ProjectionFormula.Basic
public import StacksFrontier.AlgebraicGeometry.ClosedImmersion.RingedSpaceComorphism
public import StacksFrontier.Algebra.Homology.PseudoCoherent
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import StacksFrontier.AlgebraicGeometry.ClosedImmersion.Defs

/-!
# Lifting sections off a closed subscheme from vanishing of the first cohomology

Let `i : Z ⟶ X` be a closed immersion of schemes with ideal sheaf `ℐ`, and let `𝓛` be an
invertible `𝒪_X`-module. If `H¹(X, ℐ ⊗ 𝓛) = 0` then every global section of `i^*𝓛` extends to a
global section of `𝓛`. This is the only cohomological input of the criterion for ampleness of
[Stacks, Tag 0B5P], which [Stacks, Tag 0B5X] uses for the implication "positive degree implies
ample" on a proper curve.

## Main results

* `Stacks.Cohomology.AmpleH1.shortExact_idealSheaf`: the short exact sequence
  `0 ⟶ ℐ ⟶ 𝒪_X ⟶ i_*𝒪_Z ⟶ 0` of a closed immersion of schemes.
* `Stacks.Cohomology.AmpleH1.shortExact_map_tensorLeft` and
  `epi_globalSections_map_tensorLeft_g`: tensoring a short exact sequence by an invertible
  sheaf keeps it short exact, and vanishing of `H¹` of its first term makes global sections
  surjective on the right.
* `Stacks.Cohomology.AmpleH1.epi_globalSections_map_unit_app`: **the surjectivity step of Tag
  0B5P**, `Γ(X, 𝓛) ⟶ Γ(Z, i^*𝓛)` is surjective.

## The argument

Tensor `0 ⟶ ℐ ⟶ 𝒪_X ⟶ i_*𝒪_Z ⟶ 0` by `𝓛`. Tensoring by an invertible sheaf is an equivalence,
so the sequence stays short exact, and
`Stacks.Cohomology.SectionsEpi.epi_map_g_of_isZero_rightDerived_one` turns the assumed vanishing
of `H¹(X, ℐ ⊗ 𝓛)` into surjectivity of `Γ(X, 𝒪_X ⊗ 𝓛) ⟶ Γ(X, i_*𝒪_Z ⊗ 𝓛)`.

What has to be done next is to recognise the two ends. On the left, the left unitor identifies
`𝒪_X ⊗ 𝓛` with `𝓛`. On the right, `i_*𝒪_Z ⊗ 𝓛` is `i_*(i^*𝓛)` by the **projection formula** for
a closed immersion, `Stacks.AffineProjectionFormula.closedImmersionProjectionFormulaIso`, and
the map in question becomes the unit of `i^* ⊣ i_*` at `𝓛`, whose effect on global sections is
restriction `Γ(X, 𝓛) ⟶ Γ(Z, i^*𝓛)`. Both identifications are naturality statements already
proved where those isomorphisms are constructed; the work here is to line them up.

## Implementation notes

**No `@[stacks 0B5P]` attribute is attached.** Tag 0B5P asserts that an invertible sheaf on a
quasi-compact scheme is ample as soon as some positive tensor power kills the first cohomology
of every quasi-coherent ideal sheaf. What is proved here is the cohomological step of that
proof and not the tag: the geometric half — choosing a closed point in the closure of a given
point, an affine open around it, the closed subscheme cut out by the complement together with
that point, and a section of the pullback whose nonvanishing locus is exactly that point — is
not here.

**Which spelling of the category.** Everything below is stated for
`SheafOfModules ((Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf))` and not for
`AlgebraicGeometry.Scheme.Modules X`. The two are definitionally the same type, but
`Scheme.Modules` carries its own `Category` instance (its `Hom` field is
`Scheme.Modules.Hom`), so an instance stated for one is not found at the other, and the whole
pushforward–pullback–ideal-sheaf vocabulary this file consumes is stated at the former. The
retyped `tensorLeft` and `tensorRight` below exist for the same reason.

**The three `private` epimorphism lemmas** at the end of each section take their `IsIso`
hypotheses as explicit arguments rather than as instances. That is deliberate: at the mixed
spellings above, instance search does not cross from one `Category` instance to the other, while
unification against an explicit argument does.

## References

* [Stacks Project, Tag 0B5P](https://stacks.math.columbia.edu/tag/0B5P)
* [Stacks Project, Tag 0B5X](https://stacks.math.columbia.edu/tag/0B5X)
* [Stacks Project, Tag 0FZE](https://stacks.math.columbia.edu/tag/0FZE)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace Stacks.Cohomology.AmpleH1

attribute [local instance] HasDerivedCategory.standard

/-- Symmetry of the tensor product, at the retyped functors. -/
public noncomputable def tensorLeftIsoRight (X : Scheme.{u})
    (L : _root_.SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf))) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).obj (L)) ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).flip.obj (L)) :=
  Stacks.SheafOfModules.Invertible.tensorLeftIsoTensorRight X.presheaf
    (structureSheafRing X.toRingedSpace).property L

/-- Tensoring by an invertible sheaf is an equivalence. -/
public instance tensorLeft_isEquivalence (X : Scheme.{u})
    (L : _root_.SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)))
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf
      (structureSheafRing X.toRingedSpace).property L] :
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).obj (L))).IsEquivalence :=
  AlgebraicGeometry.SheafOfModules.tensorLeftFunctor_isEquivalence X.presheaf
    (structureSheafRing X.toRingedSpace).property L

/-- Tensoring by an invertible sheaf preserves zero morphisms: it is an equivalence, hence
preserves the terminal object, hence the zero object. -/
public instance tensorLeft_preservesZeroMorphisms (X : Scheme.{u})
    (L : _root_.SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)))
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf
      (structureSheafRing X.toRingedSpace).property L] :
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).obj
      (L))).PreservesZeroMorphisms :=
  have : PreservesLimit
      (Functor.empty.{0}
        (_root_.SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf))))
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).obj
        (L))) := inferInstance
  Functor.preservesZeroMorphisms_of_map_zero_object
    ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).obj (L))).mapIso
        HasZeroObject.zeroIsoTerminal ≪≫
      PreservesTerminal.iso
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).obj (L))) ≪≫
      HasZeroObject.zeroIsoTerminal.symm)

/-- **Tensoring a short exact sequence of `𝒪_X`-modules by an invertible sheaf keeps it short
exact.**  Tensoring by an invertible sheaf is an equivalence, so it is exact. -/
public theorem shortExact_map_tensorLeft (X : Scheme.{u})
    (L : _root_.SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)))
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf
      (structureSheafRing X.toRingedSpace).property L]
    {S : ShortComplex
      (_root_.SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)))}
    (hS : S.ShortExact) :
    (S.map (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).obj
      (L)))).ShortExact :=
  hS.map_of_exact _

/-- **The twisted form of the surjectivity step.** If `H¹(X, X₁ ⊗ L) = 0` for the first term of
a short exact sequence, then global sections of the tensored sequence are surjective on the
right.  This is `Stacks.Cohomology.SectionsEpi.epi_map_g_of_isZero_rightDerived_one` applied to
the tensored sequence, with the braiding `X₁ ⊗ L ≅ L ⊗ X₁` absorbing the difference between the
convention in which the hypothesis is stated and the one in which `tensorLeft` acts. -/
public theorem epi_globalSections_map_tensorLeft_g (X : Scheme.{u})
    (L : _root_.SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)))
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf
      (structureSheafRing X.toRingedSpace).property L]
    {S : ShortComplex
      (_root_.SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)))}
    (hS : S.ShortExact)
    (hzero : IsZero (((AlgebraicGeometry.moduleGlobalSections X).rightDerived 1).obj
      ((((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (S.X₁)).obj (L))))) :
    Epi ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).obj (L)) ⋙
      AlgebraicGeometry.moduleGlobalSections X).map S.g) := by
  refine Stacks.Cohomology.SectionsEpi.epi_map_g_of_isZero_rightDerived_one
    (AlgebraicGeometry.moduleGlobalSections X) (shortExact_map_tensorLeft X L hS) ?_
  exact IsZero.of_iso hzero
    (((AlgebraicGeometry.moduleGlobalSections X).rightDerived 1).mapIso
      (Stacks.SheafOfModules.Invertible.tensorProductBraiding X.presheaf
        (structureSheafRing X.toRingedSpace).property L S.X₁))

/-- The same conclusion for tensoring on the right, through the symmetry of the tensor
product. -/
public theorem epi_tensorRight_map_of_tensorLeft (X : Scheme.{u})
    (L : _root_.SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)))
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf
      (structureSheafRing X.toRingedSpace).property L]
    {A B : _root_.SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf))} (φ : A ⟶ B)
    (h : Epi ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).obj (L)) ⋙
      AlgebraicGeometry.moduleGlobalSections X).map φ)) :
    Epi ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).flip.obj (L)) ⋙
      AlgebraicGeometry.moduleGlobalSections X).map φ) :=
  (StacksDraft.PseudoCoherence.epi_map_iff_of_natIso
    (Functor.isoWhiskerRight (tensorLeftIsoRight X L)
      (AlgebraicGeometry.moduleGlobalSections X)) φ).mp h

/-- **The short exact sequence `0 ⟶ ℐ ⟶ 𝒪_X ⟶ i_*𝒪_Z ⟶ 0` of a closed immersion of
schemes**, where `ℐ = Stacks.ClosedImmersion.idealSheaf i` is by definition the kernel of the
comorphism.  Exactness is formal from the kernel; the only input is that the comorphism is an
epimorphism of sheaves of modules, which is
`Stacks.ClosedImmersion.epi_unitToPushforwardObjUnit_structureSheafHom`. -/
public theorem shortExact_idealSheaf {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :
    (ShortComplex.mk
      (kernel.ι (_root_.SheafOfModules.unitToPushforwardObjUnit
        (RingedSpaceModuleAdjunction.structureSheafHom i.toLRSHom.toShHom)))
      (_root_.SheafOfModules.unitToPushforwardObjUnit
        (RingedSpaceModuleAdjunction.structureSheafHom i.toLRSHom.toShHom))
      (kernel.condition _)).ShortExact :=
  have : Epi (_root_.SheafOfModules.unitToPushforwardObjUnit
    (RingedSpaceModuleAdjunction.structureSheafHom i.toLRSHom.toShHom)) :=
    Stacks.ClosedImmersion.epi_unitToPushforwardObjUnit_structureSheafHom i
  { exact := ShortComplex.exact_kernel _ }

/-- **Vanishing of `H¹(X, ℐ ⊗ 𝓛)` makes `Γ(X, 𝒪_X ⊗ 𝓛) ⟶ Γ(X, i_*𝒪_Z ⊗ 𝓛)` surjective.**
The sequence is the one of `shortExact_idealSheaf`, tensored by `𝓛`. -/
public theorem epi_tensorRight_globalSections_map_structureComorphism
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (P : _root_.SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)))
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf
      (structureSheafRing X.toRingedSpace).property P]
    (hzero : IsZero (((AlgebraicGeometry.moduleGlobalSections X).rightDerived 1).obj
      ((((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj
          ((Stacks.ClosedImmersion.idealSheaf i.toLRSHom.toShHom))).obj (P))))) :
    Epi ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).flip.obj (P)) ⋙
        AlgebraicGeometry.moduleGlobalSections X).map
      (_root_.SheafOfModules.unitToPushforwardObjUnit
        (RingedSpaceModuleAdjunction.structureSheafHom i.toLRSHom.toShHom))) := by
  have h1 := shortExact_idealSheaf i
  have h2 := epi_globalSections_map_tensorLeft_g X P h1 hzero
  exact epi_tensorRight_map_of_tensorLeft X P
    (_root_.SheafOfModules.unitToPushforwardObjUnit
      (RingedSpaceModuleAdjunction.structureSheafHom i.toLRSHom.toShHom)) h2

/-- The unit of `i^* ⊣ i_*` at the structure sheaf, followed by the pushforward of the
canonical isomorphism `i^*𝒪_X ≅ 𝒪_Z`, is the structure-sheaf comorphism.  This is the
adjoint-transpose description of the comorphism, read through
`SheafOfModules.pullbackObjUnitToUnit`. -/
public theorem unit_app_unit_comp {Z X : Scheme.{u}} (i : Z ⟶ X)
    [(_root_.SheafOfModules.pushforward
      (RingedSpaceModuleAdjunction.structureSheafHom i.toLRSHom.toShHom)).IsRightAdjoint]
    [(Opens.map i.toLRSHom.toShHom.hom.base).Final] :
    (RingedSpaceModuleAdjunction.modulePullbackPushforwardAdjunction i.toLRSHom.toShHom).unit.app
        (_root_.SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf))) ≫
      (RingedSpaceModuleAdjunction.modulePushforward i.toLRSHom.toShHom).map
        (_root_.SheafOfModules.pullbackObjUnitToUnit
          (RingedSpaceModuleAdjunction.structureSheafHom i.toLRSHom.toShHom)) =
      _root_.SheafOfModules.unitToPushforwardObjUnit
        (RingedSpaceModuleAdjunction.structureSheafHom i.toLRSHom.toShHom) :=
  ((RingedSpaceModuleAdjunction.modulePullbackPushforwardAdjunction
      i.toLRSHom.toShHom).homEquiv_unit _ _ _).symm.trans
    (_root_.SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit _)

/-- **Cancelling an isomorphism inside a functor image.** If `f ≫ g = h` with `g` an
isomorphism and `F.map h` is epi, then `F.map f` is epi.  The isomorphism is an explicit
argument, not an instance, so the lemma applies at a spelling of the category whose
`Category` instance differs from the one instance search would use. -/
private theorem epi_map_of_epi_map_of_comp_eq {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D)
    {A B B' : C} (f : A ⟶ B) (g : B ⟶ B') (h : A ⟶ B') (hfg : f ≫ g = h)
    (hg : IsIso g) (hh : Epi (F.map h)) : Epi (F.map f) :=
  have := hg
  have e1 : F.map f ≫ F.map g = F.map h :=
    (F.map_comp f g).symm.trans (congrArg F.map hfg)
  (epi_comp_iff_of_isIso _ _).mp (e1 ▸ hh)

/-- **The previous surjectivity, restated at the unit of the adjunction.**  The comorphism
`𝒪_X ⟶ i_*𝒪_Z` differs from `i_*` of the unit only by the isomorphism `i^*𝒪_X ≅ 𝒪_Z`, so the
two have the same image after tensoring and taking global sections. -/
public theorem epi_tensorRight_globalSections_map_unit_app_unit
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (P : _root_.SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)))
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf
      (structureSheafRing X.toRingedSpace).property P]
    (hzero : IsZero (((AlgebraicGeometry.moduleGlobalSections X).rightDerived 1).obj
      ((((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj
          ((Stacks.ClosedImmersion.idealSheaf i.toLRSHom.toShHom))).obj (P))))) :
    Epi ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).flip.obj (P)) ⋙
        AlgebraicGeometry.moduleGlobalSections X).map
      ((RingedSpaceModuleAdjunction.modulePullbackPushforwardAdjunction i.toLRSHom.toShHom).unit.app
        (_root_.SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf))))) := by
  let : (_root_.SheafOfModules.pushforward
      (RingedSpaceModuleAdjunction.structureSheafHom i.toLRSHom.toShHom)).IsRightAdjoint :=
    RingedSpaceModuleAdjunction.modulePushforward_isRightAdjoint i.toLRSHom.toShHom
  let : (RingedSpaceModuleAdjunction.modulePullback i.toLRSHom.toShHom).IsLeftAdjoint :=
    ⟨_, ⟨RingedSpaceModuleAdjunction.modulePullbackPushforwardAdjunction i.toLRSHom.toShHom⟩⟩
  let : (Opens.map i.toLRSHom.toShHom.hom.base).Final :=
    CategoryTheory.final_of_representablyFlat _
  have hIso : IsIso (_root_.SheafOfModules.pullbackObjUnitToUnit
      (RingedSpaceModuleAdjunction.structureSheafHom i.toLRSHom.toShHom)) := inferInstance
  have hIso2 : IsIso ((RingedSpaceModuleAdjunction.modulePushforward i.toLRSHom.toShHom).map
      (_root_.SheafOfModules.pullbackObjUnitToUnit
        (RingedSpaceModuleAdjunction.structureSheafHom i.toLRSHom.toShHom))) := inferInstance
  exact epi_map_of_epi_map_of_comp_eq
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).flip.obj (P)) ⋙
      AlgebraicGeometry.moduleGlobalSections X) _ _ _
    (unit_app_unit_comp i) hIso2
    (epi_tensorRight_globalSections_map_structureComorphism i P hzero)


/-- **Transporting an epimorphism across a commuting square inside a functor image.**
If `f ≫ g = h ≫ k` with `g` an isomorphism and `F.map f` epi, then `F.map (h ≫ k)` is epi.
The isomorphism is an explicit argument. -/
private theorem epi_map_comp_of_comp_eq_comp {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D)
    {A B B' A' : C} (f : A ⟶ B) (g : B ⟶ B') (h : A ⟶ A') (k : A' ⟶ B')
    (hfg : f ≫ g = h ≫ k) (hg : IsIso g) (hf : Epi (F.map f)) :
    Epi (F.map (h ≫ k)) := by
  have := hg
  rw [← hfg, F.map_comp]
  infer_instance

open scoped CategoryTheory.Prod in
/-- **The projection formula moves the twist outside the pushforward.**  Tensoring the unit at
`𝒪_X` by `𝓛` and then applying the projection-formula isomorphism of
`Stacks.AffineProjectionFormula.closedImmersionProjectionFormulaIso` equals the unit at
`𝒪_X ⊗ 𝓛` followed by `i_*` of the pullback tensor comparison of [Stacks, Tag 01CD], which is
an isomorphism unconditionally.  Both outer legs being isomorphisms, the epimorphy transfers. -/
public theorem epi_globalSections_map_unit_app_tensorRight_unit
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (P : _root_.SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)))
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf
      (structureSheafRing X.toRingedSpace).property P]
    (hzero : IsZero (((AlgebraicGeometry.moduleGlobalSections X).rightDerived 1).obj
      ((((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj
          ((Stacks.ClosedImmersion.idealSheaf i.toLRSHom.toShHom))).obj (P))))) :
    Epi ((AlgebraicGeometry.moduleGlobalSections X).map
      ((RingedSpaceModuleAdjunction.modulePullbackPushforwardAdjunction i.toLRSHom.toShHom).unit.app
        ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).flip.obj (P))).obj
          (_root_.SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)))))) := by
  have hc : IsIso ((Stacks.RingedSpace.comparisonNatTrans i.toLRSHom.toShHom).app
      (_root_.SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)), P)) :=
    inferInstance
  have hk : IsIso ((RingedSpaceModuleAdjunction.modulePushforward i.toLRSHom.toShHom).map
      ((Stacks.RingedSpace.comparisonNatTrans i.toLRSHom.toShHom).app
        (_root_.SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)), P))) :=
    ((RingedSpaceModuleAdjunction.modulePushforward i.toLRSHom.toShHom).mapIso
      (@asIso _ _ _ _ ((Stacks.RingedSpace.comparisonNatTrans i.toLRSHom.toShHom).app
        (_root_.SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)), P))
          hc)).isIso_hom
  refine epi_map_of_epi_map_of_comp_eq (AlgebraicGeometry.moduleGlobalSections X) _ _ _ rfl hk
    (epi_map_comp_of_comp_eq_comp (AlgebraicGeometry.moduleGlobalSections X)
    ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).flip.obj (P))).map
      ((RingedSpaceModuleAdjunction.modulePullbackPushforwardAdjunction i.toLRSHom.toShHom).unit.app
        (_root_.SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)))))
    (Stacks.AffineProjectionFormula.closedImmersionProjectionFormulaIso i
      ((Stacks.RingedSpace.pullbackFunctor i.toLRSHom.toShHom).obj
        (_root_.SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)))) P).hom
    _ _ ?_ (Iso.isIso_hom _)
    (epi_tensorRight_globalSections_map_unit_app_unit i P hzero))
  have h := (Stacks.AffineProjectionFormula.closedImmersionProjectionFormulaIso_hom_natural_unit
    i (_root_.SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf))) P).trans
      ((RingedSpaceModuleAdjunction.modulePullbackPushforwardAdjunction
        i.toLRSHom.toShHom).homEquiv_unit _ _ _)
  let tensor := Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf
  let unitMap :=
    (RingedSpaceModuleAdjunction.modulePullbackPushforwardAdjunction i.toLRSHom.toShHom).unit.app
      (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf))
  have identityLaw :=
    (congrArg (fun arrow => (tensor.map unitMap).app P ≫ arrow)
      ((tensor.obj ((RingedSpaceModuleAdjunction.modulePushforward i.toLRSHom.toShHom).obj
        ((RingedSpaceModuleAdjunction.modulePullback i.toLRSHom.toShHom).obj
          (_root_.SheafOfModules.unit
            (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf))))).map_id P)).trans
      (Category.comp_id ((tensor.map unitMap).app P))
  exact (congrArg (· ≫ _) identityLaw.symm).trans h


/-- **The surjectivity step of [Stacks, Tag 0B5P].**  Let `i : Z ⟶ X` be a closed immersion of
schemes with ideal sheaf `ℐ`, and let `𝓛` be an invertible `𝒪_X`-module with
`H¹(X, ℐ ⊗ 𝓛) = 0`.  Then `Γ(X, 𝓛) ⟶ Γ(Z, i^*𝓛)` is surjective.

This is the only cohomological input of Tag 0B5P: there the closed subscheme is the one cut out
by `(X ∖ U) ∪ {y}` for an affine open `U` around a closed point `y`, and the section of `i^*𝓛`
that is lifted is one whose nonvanishing locus is exactly `{y}`.

The left unitor `𝒪_X ⊗ 𝓛 ≅ 𝓛` is where the twist is finally removed; naturality of the unit in
that isomorphism is what carries the conclusion from `𝒪_X ⊗ 𝓛` to `𝓛`. -/
public theorem epi_globalSections_map_unit_app
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (P : _root_.SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)))
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf
      (structureSheafRing X.toRingedSpace).property P]
    (hzero : IsZero (((AlgebraicGeometry.moduleGlobalSections X).rightDerived 1).obj
      ((((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj
          ((Stacks.ClosedImmersion.idealSheaf i.toLRSHom.toShHom))).obj (P))))) :
    Epi ((AlgebraicGeometry.moduleGlobalSections X).map
      ((RingedSpaceModuleAdjunction.modulePullbackPushforwardAdjunction
        i.toLRSHom.toShHom).unit.app P)) := by
  have hu : (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).flip.obj (P))).obj
      (_root_.SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf))) ≅ P :=
    Stacks.SheafOfModules.Invertible.tensorProductLeftUnitor X.presheaf
      (structureSheafRing X.toRingedSpace).property P
  have hg : IsIso ((RingedSpaceModuleAdjunction.modulePullback i.toLRSHom.toShHom ⋙
      RingedSpaceModuleAdjunction.modulePushforward i.toLRSHom.toShHom).map hu.hom) :=
    ((RingedSpaceModuleAdjunction.modulePullback i.toLRSHom.toShHom ⋙
      RingedSpaceModuleAdjunction.modulePushforward i.toLRSHom.toShHom).mapIso hu).isIso_hom
  have h := epi_map_comp_of_comp_eq_comp (AlgebraicGeometry.moduleGlobalSections X)
    ((RingedSpaceModuleAdjunction.modulePullbackPushforwardAdjunction i.toLRSHom.toShHom).unit.app
      ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).flip.obj (P))).obj
        (_root_.SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)))))
    ((RingedSpaceModuleAdjunction.modulePullback i.toLRSHom.toShHom ⋙
      RingedSpaceModuleAdjunction.modulePushforward i.toLRSHom.toShHom).map hu.hom) hu.hom _
    ((RingedSpaceModuleAdjunction.modulePullbackPushforwardAdjunction
      i.toLRSHom.toShHom).unit.naturality hu.hom).symm hg
    (epi_globalSections_map_unit_app_tensorRight_unit i P hzero)
  exact epi_of_epi_fac (f := (AlgebraicGeometry.moduleGlobalSections X).map hu.hom)
    ((AlgebraicGeometry.moduleGlobalSections X).map_comp _ _).symm

end Stacks.Cohomology.AmpleH1

end
