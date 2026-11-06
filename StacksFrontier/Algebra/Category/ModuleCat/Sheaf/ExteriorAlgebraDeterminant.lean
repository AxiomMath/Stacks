module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Submodule
public import Mathlib.RingTheory.PicardGroup
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraSheafification
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorExteriorSymmetricAlgebras
public import StacksFrontier.Algebra.Module.Projective.Determinant.Basic
public import StacksFrontier.Topology.Sheaves.Modules.Invertible
public import StacksFrontier.Topology.Sheaves.RingedSpace.StalkFinitePresentation
import StacksCore.Tactic.StacksAttribute

/-!
# The determinant of a flat sheaf of modules of finite presentation

Let `O` be a sheaf of commutative rings on a site and `F` a sheaf of `O`-modules with exterior
algebra `⋀(F)`. The determinant `det(F) ⊆ ⋀(F)` is the annihilator of the degree-one part: a
local section of `⋀(F)` lies in it when its restriction to every smaller object is killed by
multiplication by every degree-one section there. The annihilator is graded, so it is the direct
sum over the degrees of the annihilators inside the exterior powers.

For a flat `F` of finite presentation on a ringed space the stalks of `F` are finite projective,
so each stalk of `det(F)` is the determinant line of a finite projective module and is therefore
an invertible module.

## Main definitions

* `SheafOfModules.TensorExteriorSymmetricAlgebras.exteriorAnnihilator`: the annihilator of the
  degree-one part inside the degree-`n` exterior power, as a submodule of that sheaf of modules.
* `SheafOfModules.TensorExteriorSymmetricAlgebras.determinant`: the determinant `det(F)`, the
  direct sum of those annihilators.
* `SheafOfModules.TensorExteriorSymmetricAlgebras.determinantι`: the inclusion
  `det(F) ⟶ ⋀(F)`.
* `Stacks.SheafOfModules.StalkwiseInvertibleDescent`: the statement that a sheaf of modules of
  finite presentation on a ringed space whose stalks are invertible modules is invertible.

## Main results

* `SheafOfModules.TensorExteriorSymmetricAlgebras.mem_exteriorAnnihilator_iff`: membership in
  the annihilator is annihilation by every degree-one section over every smaller object.
* `SheafOfModules.TensorExteriorSymmetricAlgebras.projective_stalk`: the stalk of a flat sheaf
  of modules of finite presentation on a ringed space is a projective module over the local
  ring.
* `SheafOfModules.TensorExteriorSymmetricAlgebras.stalk_invertible_of_determinantStalkEquiv`:
  every stalk of the determinant is an invertible module, given an identification of the stalks
  of `det(F)` with the determinant lines of the stalks of `F`.
* `SheafOfModules.TensorExteriorSymmetricAlgebras.determinant_isInvertible`: the determinant is
  an invertible module, given that identification, the finite presentation of `det(F)` and
  `Stacks.SheafOfModules.StalkwiseInvertibleDescent`.

## References

* [Stacks Project, Tag 0FJN](https://stacks.math.columbia.edu/tag/0FJN)
* [Stacks Project, Tag 0FJA](https://stacks.math.columbia.edu/tag/0FJA)
* [Stacks Project, Tag 01CH](https://stacks.math.columbia.edu/tag/01CH)
* [Stacks Project, Tag 05NE](https://stacks.math.columbia.edu/tag/05NE)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe v u w

/-! ### Stalkwise descent of invertibility, as a hypothesis -/

namespace Stacks.SheafOfModules

open AlgebraicGeometry RingedSpaceModuleAdjunction

/-- **Stalkwise descent of invertibility for modules of finite presentation**: the statement
that every sheaf of modules of finite presentation on the ringed space `Y` whose stalks are all
invertible modules is an invertible module. -/
def StalkwiseInvertibleDescent (Y : RingedSpace.{w, w}) : Prop :=
  ∀ M : _root_.SheafOfModules.{w} (structureSheafRing Y), M.IsFinitePresentation →
    (∀ x : Y, @Module.Invertible _ _ _ _ (stalkModule M x)) →
      AlgebraicGeometry.SheafOfModules.IsInvertible Y.presheaf
        (Presheaf.isSheaf_comp_of_isSheaf _ Y.presheaf
          (forget₂ CommRingCat.{w} RingCat.{w}) Y.IsSheaf) M

end Stacks.SheafOfModules

namespace SheafOfModules.TensorExteriorSymmetricAlgebras

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {Osharp : Sheaf J CommRingCat.{w}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  {F : SheafOfModules.{w} (CategoryTheory.Sheaf.toRingCat J Osharp)}

/-- Countable coproducts of sheaves of modules, stated directly: instance search for
`HasColimit (Discrete.functor _)` in `SheafOfModules` times out under Lean v4.35.0. -/
local instance : HasColimitsOfShape (Discrete ℕ)
    (SheafOfModules.{w} (CategoryTheory.Sheaf.toRingCat J Osharp)) :=
  haveI := PresheafOfModules.hasColimitsOfShape (CategoryTheory.Sheaf.toRingCat J Osharp).obj
    (Discrete ℕ)
  SheafOfModules.instHasColimitsOfShapeOfPresheafOfModulesObjFunctorOppositeRingCatIsSheaf
    (CategoryTheory.Sheaf.toRingCat J Osharp) (Discrete ℕ)

section Annihilator

variable (A : TensorExteriorSymmetricAlgebras J F) (n : ℕ)

/-- A local section of `⋀ⁿ F` over `U` is *exterior annihilated* when its restriction along
every arrow out of `U` is killed by multiplication by every degree-one section there. -/
def IsExteriorAnnihilated {U : Cᵒᵖ} (x : (A.exteriorPower n).val.obj U) : Prop :=
  ∀ (V : Cᵒᵖ) (f : U ⟶ V) (m : F.val.obj V),
    (A.exterior.mul 1 (n : ℤ)).app V (A.exteriorGenerator.val.app V m)
      ((A.exteriorPower n).val.restrictₛₗ f x) = 0

/-- The annihilator of the degree-one part inside `⋀ⁿ F`, as a family of submodules of the
underlying presheaf of modules. -/
noncomputable def exteriorAnnihilatorPresheaf : (A.exteriorPower n).val.Submodule where
  obj U :=
    { carrier := {x | A.IsExteriorAnnihilated n x}
      zero_mem' := fun V f m => by
        rw [map_zero, map_zero]
      add_mem' := fun {x y} hx hy V f m => by
        rw [map_add, map_add, hx V f m, hy V f m, add_zero]
      smul_mem' := fun r x hx V f m => by
        rw [map_smulₛₗ, (A.exterior.mul 1 (n : ℤ)).map_smul_right, hx V f m, smul_zero] }
  map {U U'} g x hx V f m := by
    rw [PresheafOfModules.restrictₛₗ_apply, PresheafOfModules.restrictₛₗ_apply,
      ← PresheafOfModules.map_comp_apply]
    exact hx V (g ≫ f) m

/-- The annihilator of the degree-one part inside `⋀ⁿ F`, as a submodule of a sheaf of modules. -/
noncomputable def exteriorAnnihilator : (A.exteriorPower n).Submodule where
  toSubmodule := A.exteriorAnnihilatorPresheaf n
  isSheaf {U} x hx V f m := by
    refine Stacks.eq_of_isSeparated (A.exterior.piece (1 + (n : ℤ)))
      (J.pullback_stable f.unop hx) ?_
    intro T h hh
    have key : A.IsExteriorAnnihilated n ((A.exteriorPower n).val.restrictₛₗ (f ≫ h.op) x) := hh
    have hval := key (op T) (𝟙 _) (F.val.map h.op m)
    rw [PresheafOfModules.restrictₛₗ_apply, PresheafOfModules.map_id_apply] at hval
    have hnat := (A.exterior.mul 1 (n : ℤ)).naturality (X := V) (Y := op T) h.op
      (A.exteriorGenerator.val.app V m) ((A.exteriorPower n).val.map f x)
    rw [map_zero, PresheafOfModules.restrictₛₗ_apply, hnat,
      ← PresheafOfModules.naturality_apply A.exteriorGenerator.val h.op m,
      ← PresheafOfModules.map_comp_apply]
    exact hval

/-- A local section of `⋀ⁿ F` lies in the annihilator exactly when it is exterior annihilated. -/
@[simp]
lemma mem_exteriorAnnihilator_obj {U : Cᵒᵖ} (x : (A.exteriorPower n).val.obj U) :
    x ∈ (A.exteriorAnnihilator n).toSubmodule.obj U ↔ A.IsExteriorAnnihilated n x :=
  Iff.rfl

/-- **Membership in the determinant in degree `n`.** A local section of `⋀ⁿ F` over `U` lies in
the annihilator exactly when its restriction along every arrow out of `U` is killed by
multiplication by every degree-one section there. -/
lemma mem_exteriorAnnihilator_iff {U : Cᵒᵖ} (x : (A.exteriorPower n).val.obj U) :
    x ∈ (A.exteriorAnnihilator n).toSubmodule.obj U ↔
      ∀ (V : Cᵒᵖ) (f : U ⟶ V) (m : F.val.obj V),
        (A.exterior.mul 1 (n : ℤ)).app V (A.exteriorGenerator.val.app V m)
          ((A.exteriorPower n).val.map f x) = 0 :=
  Iff.rfl

end Annihilator

section Determinant

variable (A : TensorExteriorSymmetricAlgebras J F)

/-- **The determinant `det(F) ⊆ ⋀(F)`.** The annihilator of the degree-one part of the exterior
algebra, formed degree by degree and assembled as a direct sum. -/
noncomputable def determinant : SheafOfModules.{w} (CategoryTheory.Sheaf.toRingCat J Osharp) :=
  ∐ fun n : ℕ => (A.exteriorAnnihilator n).toSheafOfModules

/-- The inclusion of the determinant into the exterior algebra. -/
noncomputable def determinantι : A.determinant ⟶ A.exteriorAlgebraSheaf :=
  CategoryTheory.Limits.Sigma.map fun n : ℕ => (A.exteriorAnnihilator n).ι

/-- The degree-`n` summand of the determinant. -/
noncomputable def determinantSummand (n : ℕ) :
    (A.exteriorAnnihilator n).toSheafOfModules ⟶ A.determinant :=
  CategoryTheory.Limits.Sigma.ι (fun m : ℕ => (A.exteriorAnnihilator m).toSheafOfModules) n

end Determinant

/-! ### Invertibility on a ringed space -/

section RingedSpace

open AlgebraicGeometry RingedSpaceModuleAdjunction

variable {X : RingedSpace.{w, w}} {G : SheafOfModules.{w} (structureSheafRing X)}

/-- **The stalks of a flat sheaf of modules of finite presentation are projective.** -/
lemma projective_stalk [hfp : G.IsFinitePresentation] (x : X)
    (hflat : @Module.Flat _ _ _ _ (Stacks.SheafOfModules.stalkModule G x)) :
    @Module.Projective _ _ _ _ (Stacks.SheafOfModules.stalkModule G x) :=
  let _ := Stacks.SheafOfModules.stalkModule G x
  let _ := hflat
  let _ := Stacks.SheafOfModules.finitePresentation_stalk G x
  Module.Flat.projective_of_finitePresentation

/-- **The stalks of the determinant are invertible modules**, granted the stalkwise
identification `hstalk` of `det(F)_x` with the determinant line of `F_x`. -/
lemma stalk_invertible_of_determinantStalkEquiv
    (F : SheafOfModules.{w} (structureSheafRing X)) [hfp : F.IsFinitePresentation]
    (A : TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology X.carrier) F)
    (hflat : ∀ x : X, @Module.Flat _ _ _ _ (Stacks.SheafOfModules.stalkModule F x))
    (hstalk : ∀ (x : X)
      (hfin : @Module.Finite _ _ _ _ (Stacks.SheafOfModules.stalkModule F x))
      (hproj : @Module.Projective _ _ _ _ (Stacks.SheafOfModules.stalkModule F x)),
      Nonempty (@LinearEquiv _ _ _ _ (RingHom.id _) (RingHom.id _) _ _
        (ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{w}) A.determinant.val.presheaf x))
        (@ProjectiveDeterminant.module _ _ _ _ (Stacks.SheafOfModules.stalkModule F x)
          hfin hproj) _ _
        (Stacks.SheafOfModules.stalkModule A.determinant x) _))
    (x : X) :
    @Module.Invertible _ _ _ _ (Stacks.SheafOfModules.stalkModule A.determinant x) := by
  let instF := Stacks.SheafOfModules.stalkModule F x
  have := Stacks.SheafOfModules.finitePresentation_stalk F x
  have hproj := projective_stalk x (hflat x)
  obtain ⟨e⟩ := hstalk x inferInstance hproj
  have := @ProjectiveDeterminant.invertible _ _ _ _ instF _ hproj
  exact Module.Invertible.congr e.symm

/-- The determinant of a flat sheaf of modules of finite presentation on a ringed space is an
invertible module, granted the stalkwise identification `det(F)_x = det(F_x)`, the finite
presentation of `det(F)` and the stalkwise descent of invertibility. -/
theorem determinant_isInvertible
    (F : SheafOfModules.{w} (structureSheafRing X)) [hfp : F.IsFinitePresentation]
    (A : TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology X.carrier) F)
    (hflat : ∀ x : X, @Module.Flat _ _ _ _ (Stacks.SheafOfModules.stalkModule F x))
    (hstalk : ∀ (x : X)
      (hfin : @Module.Finite _ _ _ _ (Stacks.SheafOfModules.stalkModule F x))
      (hproj : @Module.Projective _ _ _ _ (Stacks.SheafOfModules.stalkModule F x)),
      Nonempty (@LinearEquiv _ _ _ _ (RingHom.id _) (RingHom.id _) _ _
        (ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{w}) A.determinant.val.presheaf x))
        (@ProjectiveDeterminant.module _ _ _ _ (Stacks.SheafOfModules.stalkModule F x)
          hfin hproj) _ _
        (Stacks.SheafOfModules.stalkModule A.determinant x) _))
    (hdet : A.determinant.IsFinitePresentation)
    (hstalkDescent : Stacks.SheafOfModules.StalkwiseInvertibleDescent X) :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf
      (Presheaf.isSheaf_comp_of_isSheaf _ X.presheaf
        (forget₂ CommRingCat.{w} RingCat.{w}) X.IsSheaf) A.determinant :=
  hstalkDescent A.determinant hdet (stalk_invertible_of_determinantStalkEquiv F A hflat hstalk)

end RingedSpace

end SheafOfModules.TensorExteriorSymmetricAlgebras

end
