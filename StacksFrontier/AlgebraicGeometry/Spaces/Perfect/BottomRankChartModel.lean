module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.LocallyFreeChartLocality
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedPullbackLocallyFree
public import StacksFrontier.CategoryTheory.Preadditive.MatrixKernelSplitting

/-!
# Bottom models of an object of the derived category of an algebraic space

A *bottom model* of an object `K` of `D(𝒪_Y)` in degree `a` is a bounded complex `P` of retracts
of finite free `𝒪_Y`-modules, zero below degree `a`, representing `K`, whose terms in degrees `a`
and `a + 1` are free and whose differential `P^a ⟶ P^{a+1}` is given by a matrix `A`. Then
`H^a(Lg^*K)` is the kernel of the pullback of `A` for every morphism `g : Y' ⟶ Y`; when `A` has a
free kernel splitting of rank `r` (`Matrix.HasFreeKernelSplittingKernelRankStratum`), this kernel
is free of rank `r` after every pullback.

## Main definitions

* `AlgebraicGeometry.Space.BottomModel`: a bottom model.

## Main results

* `AlgebraicGeometry.Space.BottomModel.nonempty_homology_iso_free`: a bottom model whose matrix
  has a free kernel splitting of rank `r` has `H^a(Lg^*K) ≅ 𝒪^{⊕r}` for every `g`.
* `AlgebraicGeometry.Space.BottomModel.pullback`: bottom models pull back, with the matrix
  mapped along the induced ring map.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 10000] HasDerivedCategory.standard

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The structure sheaf of an algebraic space, as a module over itself, on the small étale ringed
topos. -/
abbrev ringedToposUnit (Y : AlgebraicSpaces B S hS) :
    SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y) :=
  SheafOfModules.unit _

/-- A *bottom model* of `K` in degree `a` with matrix `A`: a bounded complex of retracts of finite
free modules, zero below degree `a`, representing `K`, whose differential `P^a ⟶ P^{a+1}` is, up
to identifications of its source and target with free modules, the morphism of the matrix `A`
acting through `ψ : R → End 𝒪_Y`. -/
structure BottomModel {Y : AlgebraicSpaces B S hS}
    (K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))) (a : ℤ)
    {R : Type u} [CommRing R] (ψ : R →+* End (ringedToposUnit Y)) {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) R) where
  /-- The complex. -/
  P : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) ℤ
  /-- Its terms are retracts of finite free modules. -/
  retract : ∀ j, IsRetractOfFiniteFree (ringedToposUnit Y) (P.X j)
  /-- An upper bound for its degrees. -/
  b : ℤ
  isStrictlyLE : P.IsStrictlyLE b
  isStrictlyGE : P.IsStrictlyGE a
  /-- The term in degree `a` is free. -/
  e₀ : P.X a ≅ freeObjMatrixKernelSplitting (ringedToposUnit Y) n
  /-- The term in degree `a + 1` is free. -/
  e₁ : P.X (a + 1) ≅ freeObjMatrixKernelSplitting (ringedToposUnit Y) m
  hd : e₀.inv ≫ P.d a (a + 1) ≫ e₁.hom = matrixHomMatrixKernelSplitting (ringedToposUnit Y) ψ A
  /-- The complex represents `K`. -/
  iso : K ≅ DerivedCategory.Q.obj P

/-- Pullback of modules along a morphism of algebraic spaces, typed on the structure sheaves of
the small étale ringed topoi. -/
abbrev pb {Y Y' : AlgebraicSpaces B S hS} (g : Y' ⟶ Y) :
    SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y) ⥤
      SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y') :=
  modulePullback B S hS g

/-- Pullback of modules along a morphism of algebraic spaces is an additive functor. -/
instance {Y Y' : AlgebraicSpaces B S hS} (g : Y' ⟶ Y) : (pb g).Additive :=
  modulePullback_additive g

/-- Pullback carries the structure sheaf to the structure sheaf. -/
abbrev pbUnitIso {Y Y' : AlgebraicSpaces B S hS} (g : Y' ⟶ Y) :
    (pb g).obj (ringedToposUnit Y) ≅ (ringedToposUnit Y') :=
  modulePullbackUnitIso B S hS g

namespace BottomModel

variable {Y Y' : AlgebraicSpaces B S hS}
  {K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))} {a : ℤ}
  {R : Type u} [CommRing R] {ψ : R →+* End (ringedToposUnit Y)} {m n : ℕ}
  {A : Matrix (Fin m) (Fin n) R}

/-- The differential `P^a ⟶ P^{a+1}` of a bottom model is the morphism of the matrix `A`,
transported along the identifications `e₀` and `e₁` of its source and target with free modules. -/
theorem d_eq (M : BottomModel K a ψ A) :
    M.P.d a (a + 1) =
      M.e₀.hom ≫ matrixHomMatrixKernelSplitting (ringedToposUnit Y) ψ A ≫ M.e₁.inv := by
  rw [← M.hd]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]

/-- The derived pullback of `K` is the degreewise pullback of the model. -/
theorem nonempty_derivedPullback_iso (M : BottomModel K a ψ A) (g : Y' ⟶ Y) :
    Nonempty ((smallEtaleDerivedModulePullback B S hS g).obj K ≅
      DerivedCategory.Q.obj (((pb g).mapHomologicalComplex (ComplexShape.up ℤ)).obj M.P)) := by
  have := M.isStrictlyLE
  obtain ⟨e⟩ := nonempty_smallEtaleDerivedModulePullback_obj_Q_iso_modulePullback g M.P M.b
    (fun j => isFlat_of_isRetractOfFiniteFree B S hS _ (M.retract j))
  exact ⟨(smallEtaleDerivedModulePullback B S hS g).mapIso M.iso ≪≫ e⟩

/-- **A bottom model with a free kernel splitting of rank `r` has `H^a(Lg^*K) ≅ 𝒪^{⊕r}` for
every `g`.** The cohomology in degree `a` of a complex zero below `a` is the kernel of its
differential, and the splitting of the matrix makes that kernel free and stable under every
additive functor. -/
theorem nonempty_homology_iso_free (M : BottomModel K a ψ A) {r : ℕ}
    (h : A.HasFreeKernelSplittingKernelRankStratum r) (g : Y' ⟶ Y) :
    Nonempty ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y')) a).obj
        ((smallEtaleDerivedModulePullback B S hS g).obj K) ≅
      freeObjMatrixKernelSplitting (ringedToposUnit Y') r) := by
  obtain ⟨U, V, W, h₁, h₂, h₃⟩ := h
  let O := ringedToposUnit Y
  let u : freeObjMatrixKernelSplitting O r ⟶ M.P.X a :=
    matrixHomMatrixKernelSplitting O ψ U ≫ M.e₀.inv
  let v : M.P.X a ⟶ freeObjMatrixKernelSplitting O r :=
    M.e₀.hom ≫ matrixHomMatrixKernelSplitting O ψ V
  let w : M.P.X (a + 1) ⟶ M.P.X a :=
    M.e₁.hom ≫ matrixHomMatrixKernelSplitting O ψ W ≫ M.e₀.inv
  have e₁ : u ≫ v = 𝟙 _ := by
    simp only [u, v, Category.assoc, Iso.inv_hom_id_assoc, ← matrixHom_mul_matrixKernelSplitting,
      h₁, matrixHom_one_matrixKernelSplitting]
  have e₂ : u ≫ M.P.d a (a + 1) = 0 := by
    rw [M.d_eq]
    simp only [u, Category.assoc, Iso.inv_hom_id_assoc]
    rw [← Category.assoc, ← matrixHom_mul_matrixKernelSplitting, h₂,
      matrixHom_zero_matrixKernelSplitting, zero_comp]
  have e₃ : M.P.d a (a + 1) ≫ w + v ≫ u = 𝟙 _ := by
    rw [M.d_eq]
    simp only [u, v, w, Category.assoc, Iso.inv_hom_id_assoc]
    rw [← Category.assoc (matrixHomMatrixKernelSplitting O ψ A),
      ← matrixHom_mul_matrixKernelSplitting,
      ← Category.assoc (matrixHomMatrixKernelSplitting O ψ V),
      ← matrixHom_mul_matrixKernelSplitting, ← Preadditive.comp_add, ← Preadditive.add_comp,
      ← matrixHom_add_matrixKernelSplitting, h₃, matrixHom_one_matrixKernelSplitting,
      Category.id_comp, Iso.hom_inv_id]
  let G := pb g
  let N := (G.mapHomologicalComplex (ComplexShape.up ℤ)).obj M.P
  obtain ⟨e⟩ := M.nonempty_derivedPullback_iso g
  have := M.isStrictlyGE
  let eH : N.homology a ≅ G.obj (freeObjMatrixKernelSplitting O r) :=
    (N.isoHomologyπ (a - 1) a (by simp)
      ((G.map_isZero (M.P.isZero_of_isStrictlyGE a (a - 1))).eq_of_src _ _)).symm ≪≫
      IsLimit.conePointUniqueUpToIso (N.cyclesIsKernel a (a + 1) (by simp))
        (isLimitMapKernelForkOfSplittingMatrixKernelSplitting G e₁ e₂ e₃)
  exact ⟨(DerivedCategory.homologyFunctor _ a).mapIso e ≪≫
    (DerivedCategory.homologyFunctorFactors _ a).app N ≪≫ eH ≪≫
    freeObjMapIsoMatrixKernelSplitting G (pbUnitIso g) r⟩

/-- **Bottom models pull back.** Along `g : Y' ⟶ Y`, the degreewise pullback of a bottom model of
`K` is a bottom model of `Lg^*K`, whose matrix is the image of `A` under any ring map `θ`
compatible with pullback of endomorphisms of the structure sheaf. -/
def pullback (M : BottomModel K a ψ A) (g : Y' ⟶ Y) {R' : Type u} [CommRing R']
    (ψ' : R' →+* End (ringedToposUnit Y')) (θ : R →+* R')
    (hθ : ∀ x, (ψ' (θ x) : (ringedToposUnit Y') ⟶ (ringedToposUnit Y')) =
      (pbUnitIso g).inv ≫ (pb g).map (ψ x : _ ⟶ _) ≫ (pbUnitIso g).hom) :
    BottomModel ((smallEtaleDerivedModulePullback B S hS g).obj K) a ψ' (A.map θ) :=
  haveI := M.isStrictlyLE
  haveI := M.isStrictlyGE
  { P := ((pb g).mapHomologicalComplex (ComplexShape.up ℤ)).obj M.P
    retract := fun j => IsRetractOfFiniteFree.map (F := pb g) (pbUnitIso g) (M.retract j)
    b := M.b
    isStrictlyLE := inferInstance
    isStrictlyGE := inferInstance
    e₀ := (pb g).mapIso M.e₀ ≪≫ freeObjMapIsoMatrixKernelSplitting (pb g) (pbUnitIso g) n
    e₁ := (pb g).mapIso M.e₁ ≪≫ freeObjMapIsoMatrixKernelSplitting (pb g) (pbUnitIso g) m
    hd := by
      rw [← freeObjMapIso_inv_map_matrixHom_matrixKernelSplitting (pb g) (pbUnitIso g) ψ' θ hθ A,
        ← M.hd]
      simp only [Iso.trans_inv, Iso.trans_hom, Functor.mapIso_inv, Functor.mapIso_hom,
        Category.assoc, Functor.map_comp, Functor.mapHomologicalComplex_obj_d]
    iso := M.nonempty_derivedPullback_iso g |>.some }

end BottomModel

end AlgebraicGeometry.Space
