module

public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
public import Mathlib.CategoryTheory.Limits.Constructions.EventuallyConstant
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import StacksFrontier.Algebra.DifferentialGraded.Module.CochainComplex
public import StacksFrontier.Algebra.DifferentialGraded.Module.Homotopy
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GoodDifferentialGradedResolutionColimit

/-!
# Filtered colimits of differential graded modules

Let `(B, d)` be a differential graded algebra over a commutative ring `R` and let
`T : J ⥤ Mod_{(B, d)}` be a filtered diagram of right differential graded `B`-modules. This file
constructs its colimit concretely. The underlying right `B`-module is the colimit of the
underlying modules, so its elements are germs `ι_j x`; its homogeneous part of degree `n` is the
union of the images of the homogeneous parts of degree `n` of the terms, and its differential is
the colimit of the differentials. The cochain complex underlying the colimit is then the
colimit of the cochain complexes underlying the terms, so cohomology commutes with the colimit.

## Main definitions

* `DifferentialGradedModule.FilteredColimit.colimitModule`: the colimit, a right differential
  graded `B`-module, with coprojections `DifferentialGradedModule.FilteredColimit.ι`.
* `DifferentialGradedModule.FilteredColimit.desc`: the homomorphism out of the colimit attached
  to a cocone.

## Main results

* `DifferentialGradedModule.FilteredColimit.isColimit`: the colimit cocone is a colimit.
* `DifferentialGradedModule.FilteredColimit.isColimitToCochainComplex`: the cochain complexes
  underlying the coprojections form a colimit cocone of cochain complexes.
* `DifferentialGradedModule.FilteredColimit.quasiIso_ι`: **a filtered colimit of differential
  graded modules whose transition maps are quasi-isomorphisms is quasi-isomorphic to each of its
  terms.**

## References

* [Stacks Project, Tag 09JJ](https://stacks.math.columbia.edu/tag/09JJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped DirectSum

universe w x b v u

namespace Stacks.FilteredColimit

variable {Jdx : Type w} [Category.{x} Jdx] [IsFiltered Jdx] {B : Type u} [Category.{v} B]
  [Abelian B] [HasColimitsOfShape Jdx B] [HasExactColimitsOfShape Jdx B] {I : Type b}
  {cs : ComplexShape I}

/-- **A filtered colimit of complexes all of whose transition maps are quasi-isomorphisms is
quasi-isomorphic to each of its terms**, in an abelian category whose colimits of that shape are
exact. Cohomology commutes with the colimit, and the resulting diagram of cohomology objects has
invertible transition maps, so its colimit is attained at every index. -/
theorem quasiIso_ι_of_isColimit (G : Jdx ⥤ HomologicalComplex B cs)
    (hG : ∀ ⦃i j : Jdx⦄ (f : i ⟶ j), QuasiIso (G.map f)) {c : Cocone G} (hc : IsColimit c)
    (j : Jdx) : QuasiIso (c.ι.app j) := by
  rw [quasiIso_iff_isIso_homologyMap]
  intro i
  have := SequentialColimit.preservesColimitsOfShape_homologyFunctor (B := B) (J := Jdx) cs i
  have hec : (G ⋙ HomologicalComplex.homologyFunctor B cs i).IsEventuallyConstantFrom j :=
    fun _ f ↦ (quasiIso_iff_isIso_homologyMap (G.map f)).mp (hG f) i
  exact hec.isIso_ι_of_isColimit (isColimitOfPreserves _ hc)

omit [IsFiltered Jdx] in
/-- **A natural transformation of filtered diagrams of complexes all of whose components are
quasi-isomorphisms induces a quasi-isomorphism of colimits**, in an abelian category whose
colimits of that shape are exact: cohomology commutes with the colimits. -/
theorem quasiIso_of_isColimit {G G' : Jdx ⥤ HomologicalComplex B cs} (τ : G ⟶ G')
    (hτ : ∀ j, QuasiIso (τ.app j)) {c : Cocone G} (hc : IsColimit c) {c' : Cocone G'}
    (hc' : IsColimit c') (φ : c.pt ⟶ c'.pt) (hφ : ∀ j, c.ι.app j ≫ φ = τ.app j ≫ c'.ι.app j) :
    QuasiIso φ := by
  rw [quasiIso_iff_isIso_homologyMap]
  intro i
  have := SequentialColimit.preservesColimitsOfShape_homologyFunctor (B := B) (J := Jdx) cs i
  let H := HomologicalComplex.homologyFunctor B cs i
  have hτH : ∀ j, IsIso ((Functor.whiskerRight τ H).app j) := fun j =>
    (quasiIso_iff_isIso_homologyMap (τ.app j)).mp (hτ j) i
  have : IsIso (Functor.whiskerRight τ H) := NatIso.isIso_of_isIso_app _
  let e := IsColimit.coconePointsIsoOfNatIso (isColimitOfPreserves H hc)
    (isColimitOfPreserves H hc') (asIso (Functor.whiskerRight τ H))
  have he : H.map φ = e.hom := by
    refine (isColimitOfPreserves H hc).hom_ext fun j => ?_
    rw [IsColimit.coconePointsIsoOfNatIso_hom, IsColimit.ι_map]
    change H.map (c.ι.app j) ≫ H.map φ = H.map (τ.app j) ≫ H.map (c'.ι.app j)
    rw [← H.map_comp, ← H.map_comp, hφ]
  change IsIso (H.map φ)
  rw [he]
  infer_instance

end Stacks.FilteredColimit

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R] {B : DifferentialGradedAlgebra.{u, u} R}

/-! ### The underlying right module -/

/-- A homomorphism of differential graded modules, as a homomorphism of right modules. -/
def Hom.toRightLinearMap {M N : DifferentialGradedModule.{u, u, u} B} (f : M ⟶ N) :
    M.M →ₗ[(B.A)ᵐᵒᵖ] N.M where
  toFun := f.toFun
  map_add' := map_add f.toFun
  map_smul' b x := f.map_smul x b.unop

/-- The right linear map underlying `f` sends `x` to `f x`. -/
@[simp] theorem Hom.toRightLinearMap_apply {M N : DifferentialGradedModule.{u, u, u} B}
    (f : M ⟶ N) (x : M.M) : f.toRightLinearMap x = f.toFun x := rfl

/-- The forgetful functor to right `B`-modules. -/
def forgetRightModule (B : DifferentialGradedAlgebra.{u, u} R) :
    DifferentialGradedModule.{u, u, u} B ⥤ ModuleCat.{u} (B.A)ᵐᵒᵖ where
  obj M := ModuleCat.of _ M.M
  map f := ModuleCat.ofHom f.toRightLinearMap

/-- The image of `f` under `forgetRightModule` sends `x` to `f x`. -/
@[simp] theorem forgetRightModule_map_apply {M N : DifferentialGradedModule.{u, u, u} B}
    (f : M ⟶ N) (x : M.M) : (forgetRightModule B).map f x = f.toFun x := rfl

namespace FilteredColimit

variable {J : Type u} [SmallCategory J] [IsFiltered J]
  (T : J ⥤ DifferentialGradedModule.{u, u, u} B)

/-- The colimit of the underlying right modules. -/
abbrev carrier : ModuleCat.{u} (B.A)ᵐᵒᵖ := colimit (T ⋙ forgetRightModule B)

/-- The germ of an element of a term. -/
abbrev germ (j : J) (x : (T.obj j).M) : carrier T :=
  colimit.ι (T ⋙ forgetRightModule B) j x

omit [IsFiltered J] in
/-- The germ of `x` is the germ of its image under a transition map. -/
theorem germ_map {j k : J} (f : j ⟶ k) (x : (T.obj j).M) :
    germ T k ((T.map f).toFun x) = germ T j x :=
  ConcreteCategory.congr_hom (colimit.w (T ⋙ forgetRightModule B) f) x

omit [IsFiltered J] in
/-- Taking germs is additive. -/
theorem germ_add (j : J) (x y : (T.obj j).M) :
    germ T j (x + y) = germ T j x + germ T j y := map_add _ x y

omit [IsFiltered J] in
/-- Taking germs commutes with the right action of `B`. -/
theorem germ_smul (j : J) (b : (B.A)ᵐᵒᵖ) (x : (T.obj j).M) :
    germ T j (b • x) = b • germ T j x := map_smul _ b x

omit [IsFiltered J] in
/-- The germ of zero is zero. -/
theorem germ_zero (j : J) : germ T j 0 = 0 := map_zero _

/-- Every element of the colimit is a germ. -/
theorem exists_germ (z : carrier T) : ∃ (j : J) (x : (T.obj j).M), germ T j x = z :=
  Concrete.colimit_exists_rep _ z

/-- Two germs are equal if and only if the elements become equal under transition maps to a
common index. -/
theorem germ_eq_iff {i j : J} (x : (T.obj i).M) (y : (T.obj j).M) :
    germ T i x = germ T j y ↔
      ∃ (k : J) (f : i ⟶ k) (g : j ⟶ k), (T.map f).toFun x = (T.map g).toFun y :=
  Concrete.colimit_rep_eq_iff_exists (T ⋙ forgetRightModule B) x y

/-- Two elements of the colimit are germs at a common index. -/
theorem exists_germ₂ (z w : carrier T) :
    ∃ (j : J) (x y : (T.obj j).M), germ T j x = z ∧ germ T j y = w := by
  obtain ⟨i, x, rfl⟩ := exists_germ T z
  obtain ⟨i', y, rfl⟩ := exists_germ T w
  exact ⟨IsFiltered.max i i', (T.map (IsFiltered.leftToMax i i')).toFun x,
    (T.map (IsFiltered.rightToMax i i')).toFun y, germ_map T _ x, germ_map T _ y⟩

/-- The structure ring homomorphism `R → Bᵐᵒᵖ`. -/
def scalarHom : R →+* (B.A)ᵐᵒᵖ :=
  (algebraMap R B.A).toOpposite fun _ _ => Algebra.commutes' _ _

/-- The colimit as an `R`-module, through the structure homomorphism. -/
@[implicit_reducible]
def moduleR : Module R (carrier T) := Module.compHom _ (scalarHom (B := B))

attribute [local instance] moduleR

omit [IsFiltered J] in
/-- The action of `r : R` on the colimit is the action of its image in `Bᵐᵒᵖ`. -/
theorem smul_def (r : R) (z : carrier T) : r • z = scalarHom (B := B) r • z := rfl

/-- The actions of `R` and `Bᵐᵒᵖ` on the colimit form a scalar tower. -/
instance : IsScalarTower R (B.A)ᵐᵒᵖ (carrier T) where
  smul_assoc r b z := by
    change (r • b) • z = scalarHom (B := B) r • (b • z)
    rw [← mul_smul]
    congr 1
    apply MulOpposite.unop_injective
    change r • b.unop = b.unop * algebraMap R B.A r
    rw [Algebra.smul_def, Algebra.commutes]

omit [IsFiltered J] in
/-- In a differential graded module, the action of `r` is the action of its image in `Bᵐᵒᵖ`. -/
theorem smul_eq_scalarHom (M : DifferentialGradedModule.{u, u, u} B) (r : R) (x : M.M) :
    r • x = scalarHom (B := B) r • x := by
  calc r • x = r • ((1 : (B.A)ᵐᵒᵖ) • x) := by rw [one_smul]
    _ = (r • (1 : (B.A)ᵐᵒᵖ)) • x := (smul_assoc r (1 : (B.A)ᵐᵒᵖ) x).symm
    _ = scalarHom (B := B) r • x := by
      congr 1
      apply MulOpposite.unop_injective
      change r • (1 : B.A) = algebraMap R B.A r
      rw [Algebra.smul_def, mul_one]

omit [IsFiltered J] in
/-- Taking germs is `R`-linear. -/
theorem germ_smulR (j : J) (r : R) (x : (T.obj j).M) :
    germ T j (r • x) = r • germ T j x := by
  rw [smul_eq_scalarHom, germ_smul, smul_def]

/-- The germ map, as an `R`-linear map. -/
def germₗ (j : J) : (T.obj j).M →ₗ[R] carrier T where
  toFun := germ T j
  map_add' := germ_add T j
  map_smul' := germ_smulR T j

omit [IsFiltered J] in
/-- The `R`-linear germ map sends `x` to its germ. -/
@[simp] theorem germₗ_apply (j : J) (x : (T.obj j).M) : germₗ T j x = germ T j x := rfl

/-! ### The grading -/

/-- The homogeneous part of degree `n` of the colimit: the union of the images of the homogeneous
parts of degree `n` of the terms. -/
def grading (n : ℤ) : Submodule R (carrier T) :=
  ⨆ j, ((T.obj j).grading n).map (germₗ T j)

omit [IsFiltered J] in
/-- The germ of a homogeneous element of degree `n` is homogeneous of degree `n`. -/
theorem germ_mem_grading {j : J} {n : ℤ} {x : (T.obj j).M} (hx : x ∈ (T.obj j).grading n) :
    germ T j x ∈ grading T n :=
  Submodule.mem_iSup_of_mem j ⟨x, hx, rfl⟩

omit [IsFiltered J] in
/-- The image of the degree-`n` part of a term is contained in the image of the degree-`n` part
of any later term. -/
private theorem map_grading_le_map_grading {i k : J} (f : i ⟶ k) (n : ℤ) :
    ((T.obj i).grading n).map (germₗ T i) ≤ ((T.obj k).grading n).map (germₗ T k) := by
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨(T.map f).toFun x, (T.map f).map_grading n x hx, germ_map T f x⟩

/-- An element of the colimit is homogeneous of degree `n` if and only if it is the germ of a
homogeneous element of degree `n` of some term. -/
theorem mem_grading_iff (n : ℤ) (z : carrier T) :
    z ∈ grading T n ↔ ∃ (j : J) (x : (T.obj j).M), x ∈ (T.obj j).grading n ∧ germ T j x = z := by
  refine ⟨fun hz => ?_, ?_⟩
  · have : Nonempty J := IsFiltered.nonempty
    obtain ⟨j, x, hx, rfl⟩ := (Submodule.mem_iSup_of_directed _ fun i k =>
      ⟨IsFiltered.max i k, map_grading_le_map_grading T (IsFiltered.leftToMax i k) n,
        map_grading_le_map_grading T (IsFiltered.rightToMax i k) n⟩).1 hz
    exact ⟨j, x, hx, rfl⟩
  · rintro ⟨j, x, hx, rfl⟩
    exact germ_mem_grading T hx

/-! ### Additive maps out of the colimit -/

/-- The colimit cocone of abelian groups underlying the colimit of right modules. -/
def isColimitAdd : IsColimit ((forget₂ (ModuleCat.{u} (B.A)ᵐᵒᵖ) AddCommGrpCat.{u}).mapCocone
    (colimit.cocone (T ⋙ forgetRightModule B))) :=
  isColimitOfPreserves _ (colimit.isColimit _)

/-- **An additive map out of the colimit** attached to a compatible family of additive maps out
of the terms. -/
def descAdd {G : Type u} [AddCommGroup G] (φ : ∀ j, (T.obj j).M →+ G)
    (hφ : ∀ ⦃j k : J⦄ (f : j ⟶ k) (x : (T.obj j).M), φ k ((T.map f).toFun x) = φ j x) :
    carrier T →+ G :=
  ((isColimitAdd T).desc
    { pt := AddCommGrpCat.of G
      ι := { app := fun j => AddCommGrpCat.ofHom (φ j)
             naturality := fun j k f => by
               ext x
               exact hφ f x } }).hom

omit [IsFiltered J] in
/-- The map `descAdd T φ hφ` sends the germ of `x` at `j` to `φ j x`. -/
@[simp] theorem descAdd_germ {G : Type u} [AddCommGroup G] (φ : ∀ j, (T.obj j).M →+ G)
    (hφ : ∀ ⦃j k : J⦄ (f : j ⟶ k) (x : (T.obj j).M), φ k ((T.map f).toFun x) = φ j x)
    (j : J) (x : (T.obj j).M) : descAdd T φ hφ (germ T j x) = φ j x :=
  ConcreteCategory.congr_hom ((isColimitAdd T).fac _ j) x

/-- Two additive maps out of the colimit agreeing on germs are equal. -/
theorem addHom_ext {G : Type u} [AddCommGroup G] {φ ψ : carrier T →+ G}
    (h : ∀ (j : J) (x : (T.obj j).M), φ (germ T j x) = ψ (germ T j x)) : φ = ψ := by
  ext z
  obtain ⟨j, x, rfl⟩ := exists_germ T z
  exact h j x

/-! ### The decomposition into homogeneous parts -/

/-- The homogeneous part of degree `n` of a term maps into that of the colimit. -/
def germGrading (j : J) (n : ℤ) : (T.obj j).grading n →+ grading T n where
  toFun x := ⟨germ T j x, germ_mem_grading T x.2⟩
  map_zero' := Subtype.ext (germ_zero T j)
  map_add' x y := Subtype.ext (germ_add T j x y)

/-- The decomposition of a term, carried into the homogeneous parts of the colimit. -/
def decompAt (j : J) : (T.obj j).M →+ ⨁ n, grading T n :=
  (DirectSum.map (germGrading T j)).comp
    (DirectSum.decomposeAddEquiv (T.obj j).grading).toAddMonoidHom

omit [IsFiltered J] in
/-- On a homogeneous element of degree `n`, `decompAt` is its germ placed in degree `n`. -/
theorem decompAt_of_mem (j : J) {n : ℤ} {x : (T.obj j).M} (hx : x ∈ (T.obj j).grading n) :
    decompAt T j x = DirectSum.of (fun n => grading T n) n ⟨germ T j x, germ_mem_grading T hx⟩ := by
  change DirectSum.map (germGrading T j) (DirectSum.decompose (T.obj j).grading x) = _
  rw [DirectSum.decompose_of_mem _ hx, DirectSum.map_of]
  rfl

omit [IsFiltered J] in
/-- The maps `decompAt` are compatible with the transition maps. -/
theorem decompAt_map {j k : J} (f : j ⟶ k) (x : (T.obj j).M) :
    decompAt T k ((T.map f).toFun x) = decompAt T j x := by
  induction x using DirectSum.Decomposition.inductionOn (T.obj j).grading with
  | zero => rw [map_zero, map_zero, map_zero]
  | @homogeneous n x =>
      obtain ⟨x, hx⟩ := x
      rw [decompAt_of_mem T k ((T.map f).map_grading _ x hx), decompAt_of_mem T j hx]
      congr 2
      exact germ_map T f x
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]

/-- The decomposition of the colimit into its homogeneous parts. -/
def decompose : carrier T →+ ⨁ n, grading T n :=
  descAdd T (decompAt T) fun _ _ f x => decompAt_map T f x

/-- The colimit is the internal direct sum of its homogeneous parts `grading T n`. -/
instance decomposition : DirectSum.Decomposition (grading T) where
  decompose' := decompose T
  left_inv z := by
    obtain ⟨j, x, rfl⟩ := exists_germ T z
    change DirectSum.coeAddMonoidHom (grading T) (decompose T (germ T j x)) = germ T j x
    rw [decompose, descAdd_germ]
    induction x using DirectSum.Decomposition.inductionOn (T.obj j).grading with
    | zero => rw [map_zero, map_zero, germ_zero]
    | @homogeneous n x =>
        obtain ⟨x, hx⟩ := x
        rw [decompAt_of_mem T j hx, DirectSum.coeAddMonoidHom_of]
    | add x y hx hy => rw [map_add, map_add, hx, hy, germ_add]
  right_inv d := by
    induction d using DirectSum.induction_on with
    | zero => rw [map_zero, map_zero]
    | of n z =>
        obtain ⟨z, hz⟩ := z
        obtain ⟨j, x, hx, rfl⟩ := (mem_grading_iff T n _).1 hz
        rw [DirectSum.coeAddMonoidHom_of]
        change decompose T (germ T j x) = _
        rw [decompose, descAdd_germ, decompAt_of_mem T j hx]
    | add d e hd he => rw [map_add, map_add, hd, he]

/-! ### The differential -/

/-- The differential of the colimit, as an additive map: the colimit of the differentials. -/
def dAdd : carrier T →+ carrier T :=
  descAdd T (fun j => (germₗ T j).toAddMonoidHom.comp (T.obj j).d.toAddMonoidHom)
    fun j k f x => by
      change germ T k ((T.obj k).d ((T.map f).toFun x)) = germ T j ((T.obj j).d x)
      rw [← LinearMap.comp_apply (T.obj k).d, ← (T.map f).map_d, LinearMap.comp_apply,
        germ_map]

omit [IsFiltered J] in
/-- The differential of a germ is the germ of the differential. -/
@[simp] theorem dAdd_germ (j : J) (x : (T.obj j).M) :
    dAdd T (germ T j x) = germ T j ((T.obj j).d x) :=
  descAdd_germ T _ _ j x

/-- The differential of the colimit. -/
def d : carrier T →ₗ[R] carrier T where
  toFun := dAdd T
  map_add' := map_add (dAdd T)
  map_smul' r z := by
    obtain ⟨j, x, rfl⟩ := exists_germ T z
    rw [RingHom.id_apply, ← germ_smulR, dAdd_germ, dAdd_germ, map_smul, germ_smulR]

/-- The differential of a germ is the germ of the differential. -/
@[simp] theorem d_germ (j : J) (x : (T.obj j).M) : d T (germ T j x) = germ T j ((T.obj j).d x) :=
  dAdd_germ T j x

/-! ### The colimit as a differential graded module -/

/-- **The colimit of a filtered diagram of differential graded modules.** -/
def colimitModule : DifferentialGradedModule.{u, u, u} B where
  M := carrier T
  module := moduleR T
  rmodule := inferInstance
  isScalarTower := inferInstance
  grading := grading T
  decomposition := decomposition T
  smul_mem n m z b hz hb := by
    obtain ⟨j, x, hx, rfl⟩ := (mem_grading_iff T n z).1 hz
    rw [← germ_smul]
    exact germ_mem_grading T ((T.obj j).smul_mem n m x b hx hb)
  d := d T
  d_comp_d := by
    ext z
    obtain ⟨j, x, rfl⟩ := exists_germ T z
    change d T (d T (germ T j x)) = 0
    rw [d_germ, d_germ, ← LinearMap.comp_apply, (T.obj j).d_comp_d, LinearMap.zero_apply,
      germ_zero]
  d_mem n z hz := by
    obtain ⟨j, x, hx, rfl⟩ := (mem_grading_iff T n z).1 hz
    rw [d_germ]
    exact germ_mem_grading T ((T.obj j).d_mem n x hx)
  leibniz n m z b hz hb := by
    obtain ⟨j, x, hx, rfl⟩ := (mem_grading_iff T n z).1 hz
    change d T (MulOpposite.op b • germ T j x) =
      MulOpposite.op b • d T (germ T j x) +
        (n.negOnePow : ℤ) • (MulOpposite.op (B.d b) • germ T j x)
    rw [← germ_smul, d_germ, d_germ, ← germ_smul, ← germ_smul,
      (T.obj j).leibniz n m x b hx hb, germ_add]
    exact congrArg _ ((germₗ T j).toAddMonoidHom.map_zsmul _ _)

/-- The coprojection from a term into the colimit. -/
def ι (j : J) : T.obj j ⟶ colimitModule T where
  toFun := germₗ T j
  map_smul x b := germ_smul T j (MulOpposite.op b) x
  map_grading _ _ hx := germ_mem_grading T hx
  map_d := by
    ext x
    exact (d_germ T j x).symm

/-- The coprojection `ι T j` sends `x` to its germ. -/
@[simp] theorem ι_toFun (j : J) (x : (T.obj j).M) : (ι T j).toFun x = germ T j x := rfl

/-- The coprojections are compatible with the transition maps. -/
@[reassoc (attr := simp)]
theorem map_ι {j k : J} (f : j ⟶ k) : T.map f ≫ ι T k = ι T j :=
  Hom.ext (LinearMap.ext fun x => germ_map T f x)

/-- The colimit cocone. -/
def cocone : Cocone T where
  pt := colimitModule T
  ι := { app := ι T, naturality := fun _ _ f => by rw [map_ι]; exact (Category.comp_id _).symm }

/-- The map of right modules out of the colimit attached to a cocone. -/
def descRight (s : Cocone T) : carrier T →ₗ[(B.A)ᵐᵒᵖ] s.pt.M :=
  (colimit.desc (T ⋙ forgetRightModule B) ((forgetRightModule B).mapCocone s)).hom

omit [IsFiltered J] in
/-- The map `descRight T s` sends the germ of `x` at `j` to `s.ι.app j x`. -/
theorem descRight_germ (s : Cocone T) (j : J) (x : (T.obj j).M) :
    descRight T s (germ T j x) = (s.ι.app j).toFun x :=
  ConcreteCategory.congr_hom
    (colimit.ι_desc ((forgetRightModule B).mapCocone s) j) x

/-- The underlying map out of the colimit attached to a cocone. -/
def descLinear (s : Cocone T) : carrier T →ₗ[R] s.pt.M where
  toFun := descRight T s
  map_add' := map_add _
  map_smul' r z := by
    rw [RingHom.id_apply, smul_def, smul_eq_scalarHom s.pt]
    exact map_smul (descRight T s) _ z

omit [IsFiltered J] in
/-- The map `descLinear T s` sends the germ of `x` at `j` to `s.ι.app j x`. -/
theorem descLinear_germ (s : Cocone T) (j : J) (x : (T.obj j).M) :
    descLinear T s (germ T j x) = (s.ι.app j).toFun x :=
  descRight_germ T s j x

/-- **The homomorphism out of the colimit attached to a cocone.** -/
def desc (s : Cocone T) : colimitModule T ⟶ s.pt where
  toFun := descLinear T s
  map_smul z b := map_smul (descRight T s) (MulOpposite.op b) z
  map_grading n z hz := by
    obtain ⟨j, x, hx, rfl⟩ := (mem_grading_iff T n z).1 hz
    change descLinear T s (germ T j x) ∈ _
    rw [descLinear_germ]
    exact (s.ι.app j).map_grading n x hx
  map_d := by
    ext z
    obtain ⟨j, x, rfl⟩ := exists_germ T z
    change descLinear T s (d T (germ T j x)) = s.pt.d (descLinear T s (germ T j x))
    rw [d_germ, descLinear_germ, descLinear_germ]
    exact LinearMap.congr_fun (s.ι.app j).map_d x

/-- The homomorphism `desc T s` sends the germ of `x` at `j` to `s.ι.app j x`. -/
@[simp] theorem desc_germ (s : Cocone T) (j : J) (x : (T.obj j).M) :
    (desc T s).toFun (germ T j x) = (s.ι.app j).toFun x :=
  descLinear_germ T s j x

/-- Two homomorphisms out of the colimit agreeing on germs are equal. -/
theorem hom_ext {Y : DifferentialGradedModule.{u, u, u} B} {φ ψ : colimitModule T ⟶ Y}
    (h : ∀ (j : J) (x : (T.obj j).M), φ.toFun (germ T j x) = ψ.toFun (germ T j x)) : φ = ψ := by
  refine Hom.ext (LinearMap.ext fun z => ?_)
  obtain ⟨j, x, rfl⟩ := exists_germ T z
  exact h j x

/-- **The colimit cocone is a colimit.** -/
def isColimit : IsColimit (cocone T) where
  desc := desc T
  fac s j := Hom.ext (LinearMap.ext fun x => desc_germ T s j x)
  uniq s m hm := hom_ext T fun j x => by
    rw [desc_germ]
    exact LinearMap.congr_fun (congrArg Hom.toFun (hm j)) x

/-! ### The underlying cochain complexes -/

/-- In each degree the homogeneous parts of the coprojections form a colimit cocone of
`R`-modules. -/
def isColimitGrading (n : ℤ) :
    IsColimit ((HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.up ℤ) n).mapCocone
      ((forgetToCochainComplex B).mapCocone (cocone T))) := by
  refine isColimitOfReflects (forget (ModuleCat.{u} R))
    (Types.FilteredColimit.isColimitOf _ _ ?_ ?_)
  · rintro ⟨z, hz⟩
    obtain ⟨j, x, hx, rfl⟩ := (mem_grading_iff T n z).1 hz
    exact ⟨j, ⟨x, hx⟩, rfl⟩
  · rintro i j ⟨x, hx⟩ ⟨y, hy⟩ h
    obtain ⟨k, f, g, hfg⟩ := (germ_eq_iff T x y).1 (congrArg Subtype.val h)
    exact ⟨k, f, g, Subtype.ext hfg⟩

/-- **The cochain complexes underlying the coprojections form a colimit cocone of cochain
complexes**: the cochain complex underlying the colimit is the colimit of the underlying cochain
complexes. -/
def isColimitToCochainComplex :
    IsColimit ((forgetToCochainComplex B).mapCocone (cocone T)) :=
  HomologicalComplex.isColimitOfEval _ _ (isColimitGrading T)

/-- **A filtered colimit of differential graded modules whose transition maps are
quasi-isomorphisms is quasi-isomorphic to each of its terms.** -/
theorem quasiIso_ι
    (hT : ∀ ⦃i j : J⦄ (f : i ⟶ j), QuasiIso ((forgetToCochainComplex B).map (T.map f)))
    (j : J) : QuasiIso ((forgetToCochainComplex B).map (ι T j)) :=
  Stacks.FilteredColimit.quasiIso_ι_of_isColimit (T ⋙ forgetToCochainComplex B) hT
    (isColimitToCochainComplex T) j

/-! ### Maps of diagrams -/

variable {T} {T' T'' : J ⥤ DifferentialGradedModule.{u, u, u} B}

/-- **The homomorphism of colimits induced by a natural transformation of diagrams.** -/
def map (τ : T ⟶ T') : colimitModule T ⟶ colimitModule T' :=
  desc T ⟨colimitModule T', τ ≫ (cocone T').ι⟩

/-- The map `map τ` sends the germ of `x` at `j` to the germ of `τ.app j x`. -/
@[simp] theorem map_germ (τ : T ⟶ T') (j : J) (x : (T.obj j).M) :
    (map τ).toFun (germ T j x) = germ T' j ((τ.app j).toFun x) :=
  desc_germ T _ j x

/-- The map `map τ` commutes with the coprojections. -/
theorem ι_map (τ : T ⟶ T') (j : J) : ι T j ≫ map τ = τ.app j ≫ ι T' j :=
  Hom.ext (LinearMap.ext fun x => map_germ τ j x)

/-- The identity transformation induces the identity of the colimit. -/
theorem map_id : map (𝟙 T) = 𝟙 (colimitModule T) :=
  hom_ext T fun j x => map_germ (𝟙 T) j x

/-- A composite of natural transformations induces the composite of the induced maps. -/
theorem map_comp (τ : T ⟶ T') (τ' : T' ⟶ T'') : map (τ ≫ τ') = map τ ≫ map τ' :=
  hom_ext T fun j x => by
    refine (map_germ (τ ≫ τ') j x).trans ?_
    change _ = (map τ').toFun ((map τ).toFun (germ T j x))
    rw [map_germ, map_germ]
    rfl

/-- **A natural transformation of filtered diagrams whose components are quasi-isomorphisms
induces a quasi-isomorphism of colimits.** -/
theorem quasiIso_map (τ : T ⟶ T')
    (hτ : ∀ j, QuasiIso ((forgetToCochainComplex B).map (τ.app j))) :
    QuasiIso ((forgetToCochainComplex B).map (map τ)) :=
  Stacks.FilteredColimit.quasiIso_of_isColimit (Functor.whiskerRight τ (forgetToCochainComplex B))
    hτ (isColimitToCochainComplex T) (isColimitToCochainComplex T') _ fun j => by
      change (forgetToCochainComplex B).map (ι T j) ≫ (forgetToCochainComplex B).map (map τ) =
        (forgetToCochainComplex B).map (τ.app j) ≫ (forgetToCochainComplex B).map (ι T' j)
      rw [← Functor.map_comp, ← Functor.map_comp, ι_map]

/-- **A colimit over a category with a terminal object is attained there**: the coprojection at
the terminal object is bijective. -/
theorem bijective_ι_of_isTerminal {j : J} (hj : IsTerminal j) :
    Function.Bijective (ι T j).toFun := by
  refine ⟨fun x y hxy => ?_, fun z => ?_⟩
  · obtain ⟨k, f, g, hfg⟩ := (germ_eq_iff T x y).1 hxy
    have h := congrArg (T.map (hj.from k)).toFun hfg
    change (T.map f ≫ T.map (hj.from k)).toFun x = (T.map g ≫ T.map (hj.from k)).toFun y at h
    rwa [← T.map_comp, ← T.map_comp, hj.hom_ext (f ≫ hj.from k) (𝟙 j),
      hj.hom_ext (g ≫ hj.from k) (𝟙 j), T.map_id] at h
  · obtain ⟨k, x, rfl⟩ := exists_germ T z
    exact ⟨(T.map (hj.from k)).toFun x, germ_map T (hj.from k) x⟩

/-! ### Homotopies -/

/-- **The map of right modules out of the colimit attached to a compatible family of maps of
right modules out of the terms.** -/
def descRightOf {P : Type u} [AddCommGroup P] [Module (B.A)ᵐᵒᵖ P]
    (φ : ∀ j, (T.obj j).M →ₗ[(B.A)ᵐᵒᵖ] P)
    (hφ : ∀ ⦃j k : J⦄ (f : j ⟶ k) (x : (T.obj j).M), φ k ((T.map f).toFun x) = φ j x) :
    carrier T →ₗ[(B.A)ᵐᵒᵖ] P :=
  (colimit.desc (T ⋙ forgetRightModule B)
    { pt := ModuleCat.of _ P
      ι := { app := fun j => ModuleCat.ofHom (φ j)
             naturality := fun j k f => by
               ext x
               exact hφ f x } }).hom

omit [IsFiltered J] in
/-- The map `descRightOf φ hφ` sends the germ of `x` at `j` to `φ j x`. -/
theorem descRightOf_germ {P : Type u} [AddCommGroup P] [Module (B.A)ᵐᵒᵖ P]
    (φ : ∀ j, (T.obj j).M →ₗ[(B.A)ᵐᵒᵖ] P)
    (hφ : ∀ ⦃j k : J⦄ (f : j ⟶ k) (x : (T.obj j).M), φ k ((T.map f).toFun x) = φ j x)
    (j : J) (x : (T.obj j).M) : descRightOf φ hφ (germ T j x) = φ j x :=
  ConcreteCategory.congr_hom (colimit.ι_desc (F := T ⋙ forgetRightModule B) _ j) x

/-- The germ of a homotopy, as a map of right modules into the colimit. -/
def homotopyGerm {τ τ' : T ⟶ T'} (h : ∀ j, Homotopy (τ.app j) (τ'.app j)) (j : J) :
    (T.obj j).M →ₗ[(B.A)ᵐᵒᵖ] carrier T' :=
  (colimit.ι (T' ⋙ forgetRightModule B) j).hom ∘ₗ (h j).toLinearMap

omit [IsFiltered J] in
/-- The map `homotopyGerm h j` sends `x` to the germ of `h j x`. -/
theorem homotopyGerm_apply {τ τ' : T ⟶ T'} (h : ∀ j, Homotopy (τ.app j) (τ'.app j)) (j : J)
    (x : (T.obj j).M) : homotopyGerm h j x = germ T' j ((h j).toLinearMap x) := rfl

/-- The map of right modules out of the colimit induced by a compatible family of homotopies,
sending the germ of `x` at `j` to the germ of `h j x`. -/
def homotopyLinear {τ τ' : T ⟶ T'} (h : ∀ j, Homotopy (τ.app j) (τ'.app j))
    (hh : ∀ ⦃j k : J⦄ (f : j ⟶ k) (x : (T.obj j).M),
      (h k).toLinearMap ((T.map f).toFun x) = (T'.map f).toFun ((h j).toLinearMap x)) :
    carrier T →ₗ[(B.A)ᵐᵒᵖ] carrier T' :=
  descRightOf (homotopyGerm h) fun j k f x => by
    rw [homotopyGerm_apply, homotopyGerm_apply, hh, germ_map]

omit [IsFiltered J] in
/-- The map `homotopyLinear h hh` sends the germ of `x` at `j` to the germ of `h j x`. -/
theorem homotopyLinear_germ {τ τ' : T ⟶ T'} (h : ∀ j, Homotopy (τ.app j) (τ'.app j))
    (hh : ∀ ⦃j k : J⦄ (f : j ⟶ k) (x : (T.obj j).M),
      (h k).toLinearMap ((T.map f).toFun x) = (T'.map f).toFun ((h j).toLinearMap x))
    (j : J) (x : (T.obj j).M) :
    homotopyLinear h hh (germ T j x) = germ T' j ((h j).toLinearMap x) :=
  descRightOf_germ _ _ j x

/-- **A compatible family of homotopies between the components of two natural transformations
induces a homotopy between the induced maps of colimits.** -/
def mapHomotopy {τ τ' : T ⟶ T'} (h : ∀ j, Homotopy (τ.app j) (τ'.app j))
    (hh : ∀ ⦃j k : J⦄ (f : j ⟶ k) (x : (T.obj j).M),
      (h k).toLinearMap ((T.map f).toFun x) = (T'.map f).toFun ((h j).toLinearMap x)) :
    Homotopy (map τ) (map τ') where
  toLinearMap := homotopyLinear h hh
  map_grading n z hz := by
    obtain ⟨j, x, hx, rfl⟩ := (mem_grading_iff T n z).1 hz
    change homotopyLinear h hh (germ T j x) ∈ _
    rw [homotopyLinear_germ]
    exact germ_mem_grading T' ((h j).map_grading n x hx)
  homotopy_eq z := by
    obtain ⟨j, x, rfl⟩ := exists_germ T z
    change (map τ).toFun (germ T j x) - (map τ').toFun (germ T j x) =
      d T' (homotopyLinear h hh (germ T j x)) + homotopyLinear h hh (d T (germ T j x))
    rw [map_germ, map_germ, homotopyLinear_germ, d_germ, d_germ, homotopyLinear_germ,
      ← germ_add, ← (h j).homotopy_eq x]
    exact (map_sub (germₗ T' j) _ _).symm

end FilteredColimit

end DifferentialGradedModule
