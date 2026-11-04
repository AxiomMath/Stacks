module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModelSlices
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModelLinear
public import StacksFrontier.AlgebraicGeometry.Topologies.CoherentOnSiteWeakSerre
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedHomRestriction
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedHomStrictlyPerfectSerre
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.PerfectnessAlongAnExactFunctor
public import StacksFrontier.Homology.PseudoCoherent.Locality
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulesAbelian

/-!
# Coherence of the derived internal Hom out of a perfect object on an algebraic space

Let `X` be an algebraic space, `Y` the equi-universe model of its small étale ringed site and
`e : Mod(𝒪_X) ≌ Mod(𝒪_Y)` the model equivalence
(`AlgebraicGeometry.Space.modulesEquivModelModules`). The derived internal Hom is available on
`Y`, an `AlgebraicGeometry.RingedSite.{u, u, u}`. For a perfect object `P` of `D(𝒪_X)` and an
object `L` all of whose cohomology sheaves are coherent on the small étale site, the cohomology
sheaves of `RSheafHom_Y(e P, e L)`, read back on `X` along `e⁻¹`, are coherent.

This is the coherent clause of Stacks 0D0S for a perfect first argument, the case the proof of
Stacks 0D0T uses after approximating its first argument by a perfect object (Stacks 08HP).

## Implementation notes

The proof is local on `X`: over an étale chart `V` on which `P` has a strictly perfect model, the
slice of `Y` at the model object of `V` has modules equivalent to those of the slice of `X` at `V`
(`AlgebraicGeometry.Space.modelObjSliceModulesEquiv`); the derived internal Hom restricts to slices
(Stacks 08JB); and on the slice, for the weak Serre subcategory of modules whose transport to `X/V`
is coherent, the derived internal Hom out of a strictly perfect complex preserves `D_B`
(`AlgebraicGeometry.RingedSite.derivedCategoryB_derivedSheafHom_of_isStrictlyPerfect`).

## Main results

* `AlgebraicGeometry.Space.isCoherentOnSite_homology_of_modelDerivedSheafHom`: if `N` in
  `D(𝒪_X)` transports to `RSheafHom_Y(e P, e L)` with `P` perfect and `L` of coherent
  cohomology, then every cohomology sheaf of `N` is coherent.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

namespace AlgebraicGeometry.Space

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance 5000] SheafOfModules.instAbelian

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-- The model equivalence preserves finite limits. -/
instance modulesEquivModelModules_functor_preservesFiniteLimits :
    PreservesFiniteLimits (modulesEquivModelModules B S hS F hF).functor := inferInstance

/-- The model equivalence preserves finite colimits. -/
instance modulesEquivModelModules_functor_preservesFiniteColimits :
    PreservesFiniteColimits (modulesEquivModelModules B S hS F hF).functor := inferInstance

/-- The inverse of the model equivalence is additive. -/
instance modulesEquivModelModules_inverse_additive :
    (modulesEquivModelModules B S hS F hF).inverse.Additive where
  map_add := by intros; ext; rfl

/-- The coherence class on the slice of the model at the model object of an étale chart `V`:
the modules whose transport to the slice of `X` at `V` is coherent. -/
abbrev modelSliceCoherent (V : (smallEtaleRingedSite B S hS F hF).C) :
    ObjectProperty (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleModelRingedSite B S hS F hF).O).over (modelObj B S hS F hF V))) :=
  (SheafOfModules.isCoherentOnSite ((Stacks.SheafOfModules.Tensor.ringSheaf
    (smallEtaleRingedSite B S hS F hF).O).over V)).inverseImage
      (modelObjSliceModulesEquiv B S hS F hF V).functor

/-- The coherence class `modelSliceCoherent` on the slice of the model at the model object of an
étale chart `V` is a weak Serre subcategory. -/
theorem isWeakSerre_modelSliceCoherent (V : (smallEtaleRingedSite B S hS F hF).C) :
    WeakSerre.IsWeakSerre (modelSliceCoherent B S hS F hF V) :=
  have := ObjectProperty.isWeakSerreClass_inverseImage_of_isEquivalence
    (modelObjSliceModulesEquiv B S hS F hF V).functor
    (SheafOfModules.isCoherentOnSite ((Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS F hF).O).over V))
  WeakSerre.isWeakSerre_of_isWeakSerreClass _

/-- Restriction of model modules to a slice preserves finite limits. -/
instance modelOverFunctor_preservesFiniteLimits (W : (smallEtaleModelRingedSite B S hS F hF).C) :
    PreservesFiniteLimits (SheafOfModules.overFunctor.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleModelRingedSite B S hS F hF).O) W) :=
  Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteLimits W

/-- Restriction of model modules to a slice preserves finite colimits. -/
instance modelOverFunctor_preservesFiniteColimits (W : (smallEtaleModelRingedSite B S hS F hF).C) :
    PreservesFiniteColimits (SheafOfModules.overFunctor.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleModelRingedSite B S hS F hF).O) W) :=
  Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteColimits W

/-- The inverse of the slice equivalence is additive. -/
instance modelSliceModulesEquiv_inverse_additive (V : (smallEtaleRingedSite B S hS F hF).C) :
    (modelObjSliceModulesEquiv B S hS F hF V).inverse.Additive where
  map_add := by intros; ext; rfl

/-- The derived model equivalence. -/
abbrev modelDerived :
    DerivedCategory (Modules.{u, u} B S hS F hF) ⥤ DerivedCategory (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleModelRingedSite B S hS F hF).O)) :=
  (modulesEquivModelModules B S hS F hF).functor.mapDerivedCategory

/-- On the slice at the model object of `V`, the homology of the transport of `X` is in the
coherence class iff the homology of `X` restricted to `V` is coherent. -/
private theorem modelSliceCoherent_homology_iff (V : (smallEtaleRingedSite B S hS F hF).C)
    (X : DerivedCategory (Modules.{u, u} B S hS F hF)) (j : ℤ) :
    modelSliceCoherent B S hS F hF V
      ((DerivedCategory.homologyFunctor _ j).obj
        ((SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleModelRingedSite B S hS F hF).O)
          (modelObj B S hS F hF V)).mapDerivedCategory.obj
          ((modelDerived B S hS F hF).obj X))) ↔
    SheafOfModules.IsCoherentOnSite
      (((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS F hF) j).obj X).over V) := by
  let oW := SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (smallEtaleModelRingedSite B S hS F hF).O) (modelObj B S hS F hF V)
  let i := (StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso oW j).app
      ((modelDerived B S hS F hF).obj X) ≪≫ oW.mapIso
      ((StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso
        (modulesEquivModelModules B S hS F hF).functor j).app X)
  have := (isWeakSerre_modelSliceCoherent B S hS F hF V).isClosedUnderIsomorphisms
  refine (ObjectProperty.prop_iff_of_iso (modelSliceCoherent B S hS F hF V) i).trans ?_
  let M := (DerivedCategory.homologyFunctor (Modules.{u, u} B S hS F hF) j).obj X
  change SheafOfModules.IsCoherentOnSite ((modelObjSliceModulesEquiv B S hS F hF V).functor.obj
    ((modelObjSliceModulesEquiv B S hS F hF V).inverse.obj (M.over V))) ↔ _
  exact ⟨fun h => Stacks.SheafOfModules.isCoherentOnSite_of_iso
      ((modelObjSliceModulesEquiv B S hS F hF V).counitIso.app _) h,
    fun h => Stacks.SheafOfModules.isCoherentOnSite_of_iso
      ((modelObjSliceModulesEquiv B S hS F hF V).counitIso.app _).symm h⟩

/-- Over an étale chart `V` on which the complex `E` has a strictly perfect model, and for `L`
with coherent cohomology, the restriction of `RSheafHom_Y(e E, e L)` to the model object of `V`
has its cohomology in the coherence class of that slice. -/
theorem derivedCategoryB_over_modelDerivedSheafHom (V : (smallEtaleRingedSite B S hS F hF).C)
    (E : CochainComplex (Modules.{u, u} B S hS F hF) ℤ)
    (hE : (smallEtaleRingedSite B S hS F hF).HasStrictlyPerfectQuasiIso E V)
    (L : DerivedCategory (Modules.{u, u} B S hS F hF))
    (hL : ∀ j : ℤ, SheafOfModules.IsCoherentOnSite
      ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS F hF) j).obj L)) :
    DerivedCategoryB.derivedCategoryB (modelSliceCoherent B S hS F hF V)
      ((SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleModelRingedSite B S hS F hF).O)
          (modelObj B S hS F hF V)).mapDerivedCategory.obj
        (((RingedSite.derivedSheafHomBifunctor (smallEtaleModelRingedSite B S hS F hF)).obj
          (op (DerivedCategory.Q.obj
            (((modulesEquivModelModules B S hS F hF).functor.mapHomologicalComplex
              (ComplexShape.up ℤ)).obj E)))).obj ((modelDerived B S hS F hF).obj L))) := by
  let Y := smallEtaleModelRingedSite B S hS F hF
  let W := modelObj B S hS F hF V
  let e := modulesEquivModelModules B S hS F hF
  let G := fun V' => (modelObjSliceModulesEquiv B S hS F hF V').inverse
  obtain ⟨P', hP', q, hq⟩ := RingedSite.hasStrictlyPerfectQuasiIso_map
    (modelEqv B S hS F hF).functor e.functor G V (modelSliceUnitIso B S hS F hF V)
    (modelSliceSquare B S hS F hF V) E hE
  let Z := Y.over W
  let Bp := modelSliceCoherent B S hS F hF V
  have hB := isWeakSerre_modelSliceCoherent B S hS F hF V
  have hcl := DerivedCategoryB.derivedCategoryB_isClosedUnderIsomorphisms Bp hB
  let oW := SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) W
  let L' := oW.mapDerivedCategory.obj ((modelDerived B S hS F hF).obj L)
  have hL' : DerivedCategoryB.derivedCategoryB Bp L' := by
    intro j
    exact (modelSliceCoherent_homology_iff B S hS F hF V L j).2
      (Stacks.SheafOfModules.isCoherentOnSite_over _ (hL j) V)
  have key := RingedSite.derivedCategoryB_derivedSheafHom_of_isStrictlyPerfect Z Bp hB L' hL' P' hP'
  have := hq
  let iP : oW.mapDerivedCategory.obj (DerivedCategory.Q.obj
      ((e.functor.mapHomologicalComplex (ComplexShape.up ℤ)).obj E)) ≅ DerivedCategory.Q.obj P' :=
    oW.mapDerivedCategoryFactors.app _ ≪≫ (asIso (DerivedCategory.Q.map q)).symm
  exact hcl.of_iso (((RingedSite.derivedSheafHomBifunctor Z).mapIso iP.op).app L' ≪≫
    ((RingedSite.derivedHomRestriction Y W).iso _ _).symm) key

/-- **The cohomology of the derived internal Hom out of a perfect object is coherent.** Let `P` be
a perfect object of `D(𝒪_X)` and `L` an object all of whose cohomology sheaves are coherent on the
small étale site. If `N` is an object of `D(𝒪_X)` whose transport to the model is
`RSheafHom_Y(e P, e L)`, then every cohomology sheaf of `N` is coherent on the small étale site. -/
theorem isCoherentOnSite_homology_of_modelDerivedSheafHom
    (P : DerivedCategory (Modules.{u, u} B S hS F hF))
    (hP : (smallEtaleRingedSite B S hS F hF).IsPerfect P)
    (L : DerivedCategory (Modules.{u, u} B S hS F hF))
    (hL : ∀ j : ℤ, SheafOfModules.IsCoherentOnSite
      ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS F hF) j).obj L))
    (N : DerivedCategory (Modules.{u, u} B S hS F hF))
    (eN : (modelDerived B S hS F hF).obj N ≅
      ((RingedSite.derivedSheafHomBifunctor (smallEtaleModelRingedSite B S hS F hF)).obj
        (op ((modelDerived B S hS F hF).obj P))).obj ((modelDerived B S hS F hF).obj L))
    (i : ℤ) :
    SheafOfModules.IsCoherentOnSite
      ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS F hF) i).obj N) := by
  let Y := smallEtaleModelRingedSite B S hS F hF
  let e := modulesEquivModelModules B S hS F hF
  obtain ⟨E, hE, ⟨eE⟩⟩ := hP
  obtain ⟨K, V, hV, hloc⟩ :=
    RingedSite.exists_coversTop_isStrictlyPerfect_of_isPerfectComplex _ E hE
  refine Stacks.SheafOfModules.isCoherentOnSite_of_coversTop _ V hV (fun k => ?_)
  let W := modelObj B S hS F hF (V k)
  let oW := SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) W
  have hB := isWeakSerre_modelSliceCoherent B S hS F hF (V k)
  have h := derivedCategoryB_over_modelDerivedSheafHom B S hS F hF (V k) E (hloc k) L hL i
  let α : (modelDerived B S hS F hF).obj P ≅
      DerivedCategory.Q.obj ((e.functor.mapHomologicalComplex (ComplexShape.up ℤ)).obj E) :=
    (modelDerived B S hS F hF).mapIso eE.symm ≪≫ e.functor.mapDerivedCategoryFactors.app E
  let iZ : ((RingedSite.derivedSheafHomBifunctor Y).obj (op (DerivedCategory.Q.obj
        ((e.functor.mapHomologicalComplex (ComplexShape.up ℤ)).obj E)))).obj
          ((modelDerived B S hS F hF).obj L) ≅ (modelDerived B S hS F hF).obj N :=
    ((RingedSite.derivedSheafHomBifunctor Y).mapIso α.op).app _ ≪≫ eN.symm
  exact (modelSliceCoherent_homology_iff B S hS F hF (V k) N i).1
    (hB.isClosedUnderIsomorphisms.of_iso
      ((DerivedCategory.homologyFunctor _ i).mapIso (oW.mapDerivedCategory.mapIso iZ)) h)

end AlgebraicGeometry.Space

end
