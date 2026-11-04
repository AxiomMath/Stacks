module

public import StacksFrontier.AlgebraicGeometry.Quot.RelativeKernelFunctor
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedPullbackBoundedAbove
public import StacksFrontier.AlgebraicGeometry.Spaces.UnitEndomorphismValues

/-!
# The values of the degree-zero sections functor

Let `K` be a complex of `𝒪_X`-modules on an algebraic space `X`.  The degree-zero sections
functor `AlgebraicGeometry.Space.degreeZeroSectionsFunctor K` sends a test scheme `g : T ⟶ X` to
the homomorphisms `𝒪_T ⟶ g^*(K⁰/dK⁻¹)` killed by the map to `g^*K¹`.  This file identifies that
value with the global sections of `H⁰(g^*K)` — the inverse image is right exact, so it carries
the degree-zero opcycles of `K` to those of `g^*K` — and, when `K` is K-flat with flat terms and
represents `E ∈ D(𝒪_X)`, with the global sections of `H⁰(Lg^*E)`, which is the value of the
functor of Stacks 08JX, part (1), as `AlgebraicGeometry.Space.degreeZeroPullbackSections`
records it.

## Main definitions

* `HomologicalComplex.homToHomologyEquiv`: morphisms into `Hⁱ(K)` are morphisms into the
  degree-`i` opcycles killed by the map to `K^{i+1}`.
* `HomologicalComplex.mapOpcyclesIsoOfPreservesCokernel`: a functor preserving the cokernel of
  `d : K^{i-1} ⟶ K^i` carries the degree-`i` opcycles of `K` to those of the image complex.
* `AlgebraicGeometry.Space.degreeZeroSectionsEquivHom`: the value at `T` is
  `Hom(𝒪_T, H⁰(g^*K))`.
* `AlgebraicGeometry.Space.degreeZeroSectionsEquiv`: for `K` K-flat with flat terms, the value at
  `T` is `H⁰(T, H⁰(Lg^*E))`.

## References

* [Stacks Project, Tag 08JX](https://stacks.math.columbia.edu/tag/08JX)
* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Iso

/-- Postcomposing with the inverse and then the morphism of an isomorphism does nothing. -/
theorem comp_inv_comp_hom_eq {C : Type*} [Category C] {X Y Z : C} (f : X ⟶ Y) (c : Z ≅ Y) :
    (f ≫ c.inv) ≫ c.hom = f := by
  simp

end CategoryTheory.Iso

namespace HomologicalComplex

variable {C D : Type*} [Category C] [Abelian C] [Category D] [Abelian D]

/-- Morphisms into the degree-`i` cohomology of a cochain complex are the morphisms into the
degree-`i` opcycles killed by the map to the degree-`(i + 1)` term. -/
def homToHomologyEquiv (K : CochainComplex C ℤ) (i j : ℤ) (hij : i + 1 = j) (U : C) :
    {s : U ⟶ K.opcycles i // s ≫ K.fromOpcycles i j = 0} ≃ (U ⟶ K.homology i) where
  toFun s := (K.homologyIsKernel i j ((ComplexShape.up ℤ).next_eq' hij)).lift
    (KernelFork.ofι s.1 s.2)
  invFun t := ⟨t ≫ K.homologyι i, by rw [Category.assoc, K.homologyι_comp_fromOpcycles, comp_zero]⟩
  left_inv s := Subtype.ext
    ((K.homologyIsKernel i j ((ComplexShape.up ℤ).next_eq' hij)).fac (KernelFork.ofι s.1 s.2)
      WalkingParallelPair.zero)
  right_inv t := by
    refine (cancel_mono (K.homologyι i)).1 ?_
    exact (K.homologyIsKernel i j ((ComplexShape.up ℤ).next_eq' hij)).fac
      (KernelFork.ofι (t ≫ K.homologyι i) _) WalkingParallelPair.zero

/-- The underlying morphism of the inverse of `HomologicalComplex.homToHomologyEquiv`. -/
@[simp]
theorem homToHomologyEquiv_symm_apply_coe (K : CochainComplex C ℤ) (i j : ℤ) (hij : i + 1 = j)
    (U : C) (t : U ⟶ K.homology i) :
    ((K.homToHomologyEquiv i j hij U).symm t).1 = t ≫ K.homologyι i :=
  rfl

/-- The composite of a morphism into the cohomology with the inclusion into the opcycles. -/
@[reassoc (attr := simp)]
theorem homToHomologyEquiv_apply_comp (K : CochainComplex C ℤ) (i j : ℤ) (hij : i + 1 = j)
    (U : C) (s : {s : U ⟶ K.opcycles i // s ≫ K.fromOpcycles i j = 0}) :
    K.homToHomologyEquiv i j hij U s ≫ K.homologyι i = s.1 :=
  (K.homologyIsKernel i j ((ComplexShape.up ℤ).next_eq' hij)).fac (KernelFork.ofι s.1 s.2)
    WalkingParallelPair.zero

section MapOpcycles

variable (F : C ⥤ D) [F.PreservesZeroMorphisms] (K : CochainComplex C ℤ) (i j : ℤ)
  (hij : i + 1 = j) [PreservesColimit (parallelPair (K.d i j) 0) F]

include hij

/-- The image under `F` of the cokernel cofork of `d : K^i ⟶ K^j` is a cokernel cofork. -/
def mapOpcyclesIsCokernel :
    IsColimit (CokernelCofork.ofπ (F.map (K.pOpcycles j))
      (by rw [← F.map_comp, K.d_pOpcycles, F.map_zero]) : CokernelCofork (F.map (K.d i j))) :=
  isColimitCoforkMapOfIsColimit' F _ (K.opcyclesIsCokernel i j ((ComplexShape.up ℤ).prev_eq' hij))

/-- The image under `F` of the projection `K^j ⟶ K^j/dK^i` onto the opcycles is an epimorphism. -/
theorem epi_map_pOpcycles : Epi (F.map (K.pOpcycles j)) :=
  epi_of_isColimit_cofork (K.mapOpcyclesIsCokernel F i j hij)

/-- **A functor preserving the cokernel of `d : K^i ⟶ K^j` carries the degree-`j` opcycles of
`K` to those of the image complex.** -/
def mapOpcyclesIsoOfPreservesCokernel :
    F.obj (K.opcycles j) ≅ ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).opcycles j where
  hom := (K.mapOpcyclesIsCokernel F i j hij).desc
    (CokernelCofork.ofπ (((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).pOpcycles j)
      (((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).d_pOpcycles i j))
  inv := ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).descOpcycles
    (F.map (K.pOpcycles j)) i ((ComplexShape.up ℤ).prev_eq' hij)
    (by
      change F.map (K.d i j) ≫ F.map (K.pOpcycles j) = 0
      rw [← F.map_comp, K.d_pOpcycles, F.map_zero])
  hom_inv_id := by
    have := K.epi_map_pOpcycles F i j hij
    rw [← cancel_epi (F.map (K.pOpcycles j)), Category.comp_id]
    have h := (K.mapOpcyclesIsCokernel F i j hij).fac
      (CokernelCofork.ofπ (((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).pOpcycles j)
        (((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).d_pOpcycles i j))
      WalkingParallelPair.one
    rw [← Category.assoc]
    refine (congrArg (· ≫ _) h).trans ?_
    exact ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).p_descOpcycles _ _ _ _
  inv_hom_id := by
    rw [← cancel_epi (((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).pOpcycles j),
      Category.comp_id, ← Category.assoc, HomologicalComplex.p_descOpcycles]
    exact (K.mapOpcyclesIsCokernel F i j hij).fac _ WalkingParallelPair.one

/-- The identification of the opcycles carries the image of the projection of `K` onto its
opcycles to the projection of the image complex onto its opcycles. -/
@[reassoc (attr := simp)]
theorem map_pOpcycles_mapOpcyclesIso_hom :
    F.map (K.pOpcycles j) ≫ (K.mapOpcyclesIsoOfPreservesCokernel F i j hij).hom =
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).pOpcycles j :=
  (K.mapOpcyclesIsCokernel F i j hij).fac _ WalkingParallelPair.one

/-- A morphism out of the image of the opcycles of `K` is determined by its composite with the
image of the projection `K^j ⟶ K^j/dK^i`, also after composing with the identification of the
opcycles. -/
private theorem mapOpcyclesIso_hom_comp_eq {Z : D} (a : F.obj (K.opcycles j) ⟶ Z)
    (b : ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).opcycles j ⟶ Z)
    (h : F.map (K.pOpcycles j) ≫ a =
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).pOpcycles j ≫ b) :
    (K.mapOpcyclesIsoOfPreservesCokernel F i j hij).hom ≫ b = a := by
  have := K.epi_map_pOpcycles F i j hij
  rw [← cancel_epi (F.map (K.pOpcycles j)), map_pOpcycles_mapOpcyclesIso_hom_assoc, h]

/-- The identification of the opcycles is compatible with the maps to the next term. -/
@[reassoc (attr := simp)]
theorem mapOpcyclesIso_hom_fromOpcycles (k : ℤ) :
    (K.mapOpcyclesIsoOfPreservesCokernel F i j hij).hom ≫
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).fromOpcycles j k =
      F.map (K.fromOpcycles j k) :=
  K.mapOpcyclesIso_hom_comp_eq F i j hij _ _ (by simp [← F.map_comp])

/-- The inverse identification of the opcycles is compatible with the maps to the next term. -/
@[reassoc (attr := simp)]
theorem mapOpcyclesIso_inv_map_fromOpcycles (k : ℤ) :
    (K.mapOpcyclesIsoOfPreservesCokernel F i j hij).inv ≫ F.map (K.fromOpcycles j k) =
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).fromOpcycles j k := by
  rw [← K.mapOpcyclesIso_hom_fromOpcycles F i j hij k, Iso.inv_hom_id_assoc]

/-- **Morphisms into the cohomology of the image complex, read before applying `F`.**  For an
isomorphism `e : F U ≅ V`, the morphisms `V ⟶ Hⁱ(F K)` are the morphisms
`α : F U ⟶ F(K^i/dK^{i-1})` with `α ≫ F(d̄) = 0`. -/
def mapHomToHomologyEquiv (k : ℤ) (hjk : j + 1 = k) {U : C} {V : D} (e : F.obj U ≅ V) :
    {α : F.obj U ⟶ F.obj (K.opcycles j) // α ≫ F.map (K.fromOpcycles j k) = 0} ≃
      (V ⟶ ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).homology j) where
  toFun α := ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).homToHomologyEquiv j k hjk _
    ⟨e.inv ≫ α.1 ≫ (K.mapOpcyclesIsoOfPreservesCokernel F i j hij).hom, by
      rw [Category.assoc, Category.assoc, mapOpcyclesIso_hom_fromOpcycles, α.2, comp_zero]⟩
  invFun t := ⟨e.hom ≫ t ≫ ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).homologyι j ≫
      (K.mapOpcyclesIsoOfPreservesCokernel F i j hij).inv, by
    simp only [Category.assoc, mapOpcyclesIso_inv_map_fromOpcycles, homologyι_comp_fromOpcycles,
      comp_zero]⟩
  left_inv α := Subtype.ext (by
    change e.hom ≫ _ ≫ ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).homologyι j ≫ _ = _
    rw [homToHomologyEquiv_apply_comp_assoc]
    simp)
  right_inv t := by
    refine ((((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).homToHomologyEquiv j k hjk
      _).apply_eq_iff_eq_symm_apply).2 (Subtype.ext ?_)
    simp

/-- The underlying morphism of the inverse of `HomologicalComplex.mapHomToHomologyEquiv`. -/
theorem mapHomToHomologyEquiv_symm_apply_coe (k : ℤ) (hjk : j + 1 = k) {U : C} {V : D}
    (e : F.obj U ≅ V) (t : V ⟶ ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).homology j) :
    ((K.mapHomToHomologyEquiv F i j hij k hjk e).symm t).1 =
      e.hom ≫ t ≫ ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).homologyι j ≫
        (K.mapOpcyclesIsoOfPreservesCokernel F i j hij).inv :=
  rfl

/-- `HomologicalComplex.mapOpcyclesIsoOfPreservesCokernel` is natural in the complex. -/
@[reassoc]
theorem map_opcyclesMap_mapOpcyclesIso_hom {K' : CochainComplex C ℤ}
    [PreservesColimit (parallelPair (K'.d i j) 0) F] (φ : K ⟶ K') :
    F.map (opcyclesMap φ j) ≫ (K'.mapOpcyclesIsoOfPreservesCokernel F i j hij).hom =
      (K.mapOpcyclesIsoOfPreservesCokernel F i j hij).hom ≫
        opcyclesMap ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map φ) j :=
  (K.mapOpcyclesIso_hom_comp_eq F i j hij _ _ (by simp [← F.map_comp_assoc])).symm

/-- **`HomologicalComplex.mapHomToHomologyEquiv` is natural in the complex**: postcomposition
with the image of the induced map of opcycles corresponds to postcomposition with the map
induced on cohomology. -/
theorem mapHomToHomologyEquiv_naturality (k : ℤ) (hjk : j + 1 = k) {U : C} {V : D}
    (e : F.obj U ≅ V) {K' : CochainComplex C ℤ} [PreservesColimit (parallelPair (K'.d i j) 0) F]
    (φ : K ⟶ K')
    (α : {α : F.obj U ⟶ F.obj (K.opcycles j) // α ≫ F.map (K.fromOpcycles j k) = 0})
    (hα : (α.1 ≫ F.map (opcyclesMap φ j)) ≫ F.map (K'.fromOpcycles j k) = 0) :
    K'.mapHomToHomologyEquiv F i j hij k hjk e ⟨α.1 ≫ F.map (opcyclesMap φ j), hα⟩ =
      K.mapHomToHomologyEquiv F i j hij k hjk e α ≫
        homologyMap ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map φ) j := by
  refine (cancel_mono (((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K').homologyι j)).1 ?_
  simp only [mapHomToHomologyEquiv, Equiv.coe_fn_mk, homToHomologyEquiv_apply_comp,
    Category.assoc, homologyι_naturality, homToHomologyEquiv_apply_comp_assoc]
  rw [map_opcyclesMap_mapOpcyclesIso_hom]

end MapOpcycles

end HomologicalComplex

namespace AlgebraicGeometry.Space

universe u

attribute [local instance 10000] HasDerivedCategory.standard

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

-- The inverse image of modules is never unfolded here; keeping it opaque stops the unifier from
-- unfolding it when two inverse images along equal morphisms are compared.
attribute [local irreducible] modulePullback

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : AlgebraicSpaces B S hS}

/-- The inverse image of `𝒪`-modules preserves colimits: it is a left adjoint. -/
instance preservesColimitsOfSize_toposModulePullbackData {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) :
    PreservesColimitsOfSize.{0, 0} ((toposModulePullbackData B S hS).pull f) :=
  (modulePullbackAdjunction B S hS f).leftAdjoint_preservesColimits

/-- The inverse image of the structure sheaf is the structure sheaf
(`AlgebraicGeometry.Space.modulePullbackUnitIso`), in the spelling of the modules of the small
étale ringed topos. -/
def modulePullbackUnitIsoTopos {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) :
    ((toposModulePullbackData B S hS).pull f).obj
        (SheafOfModules.unit (ringedToposStructureRingSheaf B S hS Y)) ≅
      SheafOfModules.unit (ringedToposStructureRingSheaf B S hS X) :=
  modulePullbackUnitIso B S hS f

section Family

variable {I : Type*} [Category* I] {π : I ⥤ AlgebraicSpaces B S hS} (κ : PullbackData.ConeTo π X)

/-- **The value of the degree-zero sections functor is the set of homomorphisms out of the
structure sheaf into `H⁰(g^*K)`.** -/
def degreeZeroSectionsEquivHom (K : CochainComplex (toposModules B S hS X) ℤ) (i : I) :
    (degreeZeroSectionsFunctor κ K).obj (Opposite.op i) ≃
      (SheafOfModules.unit _ ⟶
        ((((toposModulePullbackData B S hS).pull (κ.leg i)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K).homology 0) :=
  ((toposModulePullbackData B S hS).relKerFunctorObjEquiv
    (toposModulePullbackData_isCoherent B S hS) κ
    (SheafOfModules.unit _) (K.fromOpcycles 0 1) i).trans <|
    K.mapHomToHomologyEquiv ((toposModulePullbackData B S hS).pull (κ.leg i)) (-1) 0
    (by norm_num) 1 (by norm_num) (modulePullbackUnitIsoTopos (κ.leg i))

/-- The map of opcycles induced by a morphism of complexes commutes with the maps to the next
term. -/
theorem fromOpcycles_comp_f {K K' : CochainComplex (toposModules B S hS X) ℤ} (φ : K ⟶ K') :
    K.fromOpcycles 0 1 ≫ φ.f 1 = HomologicalComplex.opcyclesMap φ 0 ≫ K'.fromOpcycles 0 1 := by
  rw [← cancel_epi (K.pOpcycles 0), HomologicalComplex.p_fromOpcycles_assoc,
    HomologicalComplex.p_opcyclesMap_assoc, HomologicalComplex.p_fromOpcycles, φ.comm]

/-- **The degree-zero sections functor is functorial in the complex.** -/
def degreeZeroSectionsMap {K K' : CochainComplex (toposModules B S hS X) ℤ} (φ : K ⟶ K') :
    degreeZeroSectionsFunctor κ K ⟶ degreeZeroSectionsFunctor κ K' :=
  (toposModulePullbackData B S hS).relKerMap (toposModulePullbackData_isCoherent B S hS) κ
    (𝟙 _) (K.fromOpcycles 0 1) (K'.fromOpcycles 0 1) (HomologicalComplex.opcyclesMap φ 0) (φ.f 1)
    (fromOpcycles_comp_f φ)

/-- **A morphism of complexes inducing isomorphisms on `H⁰` after every inverse image in the
family induces an isomorphism of the degree-zero sections functors.** -/
theorem isIso_degreeZeroSectionsMap {K K' : CochainComplex (toposModules B S hS X) ℤ}
    (φ : K ⟶ K')
    (hφ : ∀ i : I, QuasiIsoAt
        ((((toposModulePullbackData B S hS).pull (κ.leg i)).mapHomologicalComplex
        (ComplexShape.up ℤ)).map φ) 0) :
    IsIso (degreeZeroSectionsMap κ φ) := by
  refine (toposModulePullbackData B S hS).isIso_relKerMap_of_bijective
    (toposModulePullbackData_isCoherent B S hS) κ _ _ _ _ _ _ fun i => ?_
  let F := (toposModulePullbackData B S hS).pull (κ.leg i)
  let e := modulePullbackUnitIsoTopos (κ.leg i)
  let c := @asIso _ _ _ _ (HomologicalComplex.homologyMap
    ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map φ) 0)
    ((quasiIsoAt_iff_isIso_homologyMap _ _).1 (hφ i))
  let E := K.mapHomToHomologyEquiv F (-1) 0 (by norm_num) 1 (by norm_num) e
  let E' := K'.mapHomToHomologyEquiv F (-1) 0 (by norm_num) 1 (by norm_num) e
  let g := (toposModulePullbackData B S hS).relKerMapFun κ
    (𝟙 (SheafOfModules.unit (ringedToposStructureRingSheaf B S hS X))) (K.fromOpcycles 0 1)
    (K'.fromOpcycles 0 1) (HomologicalComplex.opcyclesMap φ 0) (φ.f 1) (fromOpcycles_comp_f φ) i
  have key : ∀ α, E' (g α) = E α ≫ c.hom := by
    intro α
    refine Eq.trans ?_ (K.mapHomToHomologyEquiv_naturality F (-1) 0 (by norm_num) 1
      (by norm_num) e φ α
      (by rw [Category.assoc, ← Functor.map_comp, ← fromOpcycles_comp_f, Functor.map_comp,
        ← Category.assoc, α.2, zero_comp]))
    congr 1
    exact Subtype.ext ((toposModulePullbackData B S hS).relKerMapFun_id_coe κ _ _ _ _ _ _ i α)
  refine ⟨fun a b hab => E.injective ((Iso.cancel_iso_hom_right _ _ c).1 ?_), fun β => ?_⟩
  · rw [← key, ← key]
    exact congrArg E' hab
  · refine ⟨E.symm (E' β ≫ c.inv), E'.injective ?_⟩
    rw [key, Equiv.apply_symm_apply]
    exact Iso.comp_inv_comp_hom_eq _ _

end Family

end AlgebraicGeometry.Space

end
