module

public import Mathlib.Data.Int.Interval
public import Mathlib.RingTheory.Finiteness.Projective
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantSheafFiniteness
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.LocalRepresentationOfADerivedMap
public import StacksFrontier.Homology.Perfect.Defs
import StacksCore.Tactic.StacksAttribute

/-!
# Maps out of a complex of constant sheaves of modules

Let `Λ` be a ring and let `K^•` be a bounded complex of finite projective `Λ`-modules. The
complex of constant sheaves of modules `K̲^•` on a site is then strictly perfect, and
consequently every morphism `K̲^• ⟶ L^•` in the derived category of sheaves of modules is, after
restriction along the arrows of a covering sieve, the image of an honest map of complexes.

## Main results

* `Stacks.SheafOfModules.isDirectSummandOfFiniteFree_obj_of_finite_projective`: an additive
  right exact functor from `Λ`-modules to sheaves of `R`-modules carrying `Λ` to the unit sends
  a finite projective module to a direct summand of a finite free sheaf of modules.
* `Stacks.SheafOfModules.isStrictlyPerfect_mapHomologicalComplex_of_finite_projective`: the same
  functor sends a bounded complex of finite projective modules to a strictly perfect complex.
* `Stacks.SheafOfModules.Constant.isStrictlyPerfect_constantModuleSheafFunctor`: the complex of
  constant sheaves of modules on a bounded complex of finite projective `Λ`-modules is strictly
  perfect over the constant sheaf of rings `Λ̲`.
* `StacksDraft.Perfect.isPerfect_Q_obj_of_finite_projective`: a bounded complex of finite
  projective modules represents a perfect object of the derived category.
* `AlgebraicGeometry.RingedSite.exists_coveringSieve_complexMap_of_finite_projective_valueUniverse`
  and `AlgebraicGeometry.RingedSite.exists_coveringSieve_complexMap_of_finite_projective`: for a
  bounded complex of finite projective `Λ`-modules carried into sheaves of modules by such a
  functor, a morphism out of it in the derived category is represented by a map of complexes on
  a covering sieve.

## References

* [Stacks Project, Tag 09BD](https://stacks.math.columbia.edu/tag/09BD)
* [Stacks Project, Tag 08FR](https://stacks.math.columbia.edu/tag/08FR)
* [Stacks Project, Tag 0657](https://stacks.math.columbia.edu/tag/0657)
* [Stacks Project, Tag 093N](https://stacks.math.columbia.edu/tag/093N)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w d

namespace Stacks.SheafOfModules

section Bounded

variable {A : Type u} [Category.{v} A] [HasZeroMorphisms A]

/-- A cochain complex vanishing strictly below `a` and strictly above `b` is nonzero only in
degrees of the interval `[a, b]`, so the set of those degrees is finite. -/
theorem finite_notIsZero_of_strictlyBounded (P : CochainComplex A ℤ) (a b : ℤ)
    [P.IsStrictlyGE a] [P.IsStrictlyLE b] : {i : ℤ | ¬ IsZero (P.X i)}.Finite :=
  (Set.finite_Icc a b).subset fun i hi =>
    ⟨not_lt.1 fun h => hi (P.isZero_of_isStrictlyGE a i h),
      not_lt.1 fun h => hi (P.isZero_of_isStrictlyLE b i h)⟩

end Bounded

section Transport

variable {Λ : Type w} [Ring Λ] {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{w}} [HasWeakSheafify J AddCommGrpCat.{w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- Discrete colimits of presheaves of modules, supplied directly: instance search for them
times out. -/
local instance (priority := high) (K : Type w) :
    HasColimitsOfShape (Discrete K) (PresheafOfModules.{w} R.obj) :=
  PresheafOfModules.hasColimitsOfShape _ _

/-- An additive right exact functor from `Λ`-modules to sheaves of `R`-modules carrying `Λ` to
the unit object carries the finite free module on an index type `I` to the free sheaf of modules
on `I`. -/
def freeIsoMapFinitePi (Φ : ModuleCat.{w} Λ ⥤ _root_.SheafOfModules.{w} R)
    [PreservesFiniteColimits Φ]
    (e : Φ.obj (ModuleCat.of Λ Λ) ≅ _root_.SheafOfModules.unit R)
    (I : Type w) [Fintype I] [DecidableEq I] :
    _root_.SheafOfModules.free (R := R) I ≅ Φ.obj (ModuleCat.of Λ (I → Λ)) :=
  letI e1 : _root_.SheafOfModules.free (R := R) I ≅
      ∐ (fun _ : I => Φ.obj (ModuleCat.of Λ Λ)) :=
    HasColimit.isoOfNatIso (Discrete.natIso (fun _ => e.symm))
  e1 ≪≫ (HasColimit.isoOfNatIso
      (Discrete.compNatIsoDiscrete (fun _ : I => ModuleCat.of Λ Λ) Φ)).symm ≪≫
    (preservesColimitIso Φ (Discrete.functor (fun _ : I => ModuleCat.of Λ Λ))).symm ≪≫
    Φ.mapIso (Stacks.SheafOfModules.Constant.coprodIsoPi I)

/-- An additive right exact functor from `Λ`-modules to sheaves of `R`-modules carrying `Λ` to
the unit object carries a finite projective `Λ`-module to a direct summand of a finite free
sheaf of `R`-modules. -/
theorem isDirectSummandOfFiniteFree_obj_of_finite_projective
    (Φ : ModuleCat.{w} Λ ⥤ _root_.SheafOfModules.{w} R) [PreservesFiniteColimits Φ]
    (e : Φ.obj (ModuleCat.of Λ Λ) ≅ _root_.SheafOfModules.unit R) (M : ModuleCat.{w} Λ)
    (hfin : Module.Finite Λ M) (hproj : Module.Projective Λ M) :
    IsDirectSummandOfFiniteFree R (Φ.obj M) := by
  classical
  obtain ⟨n, f, g, -, -, hfg⟩ := Module.Finite.exists_comp_eq_id_of_projective Λ M
  let τ : ModuleCat.of Λ (Fin n → Λ) ≅ ModuleCat.of Λ (ULift.{w} (Fin n) → Λ) :=
    (LinearEquiv.funCongrLeft Λ Λ (Equiv.ulift.{w} (α := Fin n))).toModuleIso
  have hir : (ModuleCat.ofHom g ≫ τ.hom) ≫ (τ.inv ≫ ModuleCat.ofHom f) = 𝟙 M := by
    rw [Category.assoc, ← Category.assoc τ.hom, τ.hom_inv_id, Category.id_comp,
      ← ModuleCat.ofHom_comp, hfg, ModuleCat.ofHom_id]
  refine (isDirectSummandOfFiniteFree_iff_free R (Φ.obj M)).mpr
    ⟨n, Φ.map (ModuleCat.ofHom g ≫ τ.hom) ≫ (freeIsoMapFinitePi Φ e (ULift.{w} (Fin n))).inv,
      (freeIsoMapFinitePi Φ e (ULift.{w} (Fin n))).hom ≫
        Φ.map (τ.inv ≫ ModuleCat.ofHom f), ?_⟩
  rw [Category.assoc, ← Category.assoc _ _ (Φ.map (τ.inv ≫ ModuleCat.ofHom f)),
    Iso.inv_hom_id, Category.id_comp, ← Φ.map_comp, hir, CategoryTheory.Functor.map_id]

/-- An additive right exact functor from `Λ`-modules to sheaves of `R`-modules carrying `Λ` to
the unit object carries a bounded complex of finite projective `Λ`-modules to a strictly perfect
complex of sheaves of `R`-modules. -/
theorem isStrictlyPerfect_mapHomologicalComplex_of_finite_projective
    (Φ : ModuleCat.{w} Λ ⥤ _root_.SheafOfModules.{w} R) [Φ.Additive]
    [PreservesFiniteColimits Φ]
    (e : Φ.obj (ModuleCat.of Λ Λ) ≅ _root_.SheafOfModules.unit R)
    {P : CochainComplex (ModuleCat.{w} Λ) ℤ} (hb : {i : ℤ | ¬ IsZero (P.X i)}.Finite)
    (hfin : ∀ i : ℤ, Module.Finite Λ (P.X i)) (hproj : ∀ i : ℤ, Module.Projective Λ (P.X i)) :
    IsStrictlyPerfect R ((Φ.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) where
  bounded := hb.subset fun _ hi hz => hi (Functor.map_isZero Φ hz)
  termDirectSummand i :=
    isDirectSummandOfFiniteFree_obj_of_finite_projective Φ e (P.X i) (hfin i) (hproj i)

end Transport

namespace Constant

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) {Λ : Type w} [Ring Λ]
  [HasWeakSheafify J RingCat.{w}] [J.WEqualsLocallyBijective RingCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- The constant sheaf of modules functor is additive. -/
instance additive_constantModuleSheafFunctor :
    (constantModuleSheafFunctor J (R := Λ)).Additive :=
  letI _ := preservesBinaryBiproducts_of_preservesBinaryCoproducts
    (constantModuleSheafFunctor J (R := Λ))
  Functor.additive_of_preservesBinaryBiproducts _

/-- The constant sheaf of modules on a finite projective `Λ`-module is a direct summand of a
finite free sheaf of modules over the constant sheaf of rings `Λ̲`. -/
theorem isDirectSummandOfFiniteFree_constantModuleSheaf (M : ModuleCat.{w} Λ)
    (hfin : Module.Finite Λ M) (hproj : Module.Projective Λ M) :
    IsDirectSummandOfFiniteFree ((constantSheaf J RingCat.{w}).obj (RingCat.of Λ))
      (constantModuleSheaf J M) :=
  Stacks.SheafOfModules.isDirectSummandOfFiniteFree_obj_of_finite_projective
    (constantModuleSheafFunctor J) (unitIsoConstantModuleSheaf J).symm M hfin hproj

/-- The complex of constant sheaves of modules on a bounded complex of finite projective
`Λ`-modules is strictly perfect over the constant sheaf of rings `Λ̲`. -/
@[stacks 09BD "strict_perfectness_of_the_constant_complex"]
theorem isStrictlyPerfect_constantModuleSheafFunctor
    {P : CochainComplex (ModuleCat.{w} Λ) ℤ} (a b : ℤ)
    [P.IsStrictlyGE a] [P.IsStrictlyLE b]
    (hfin : ∀ i : ℤ, Module.Finite Λ (P.X i)) (hproj : ∀ i : ℤ, Module.Projective Λ (P.X i)) :
    IsStrictlyPerfect ((constantSheaf J RingCat.{w}).obj (RingCat.of Λ))
      (((constantModuleSheafFunctor J (R := Λ)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P) :=
  Stacks.SheafOfModules.isStrictlyPerfect_mapHomologicalComplex_of_finite_projective
    (constantModuleSheafFunctor J) (unitIsoConstantModuleSheaf J).symm
    (Stacks.SheafOfModules.finite_notIsZero_of_strictlyBounded P a b) hfin hproj

end Constant

end Stacks.SheafOfModules

namespace StacksDraft.Perfect

/-- A bounded complex of finite projective `Λ`-modules represents a perfect object of the derived
category of `Λ`-modules, namely its own image under the localisation functor. -/
theorem isPerfect_Q_obj_of_finite_projective {Λ : Type w} [Ring Λ]
    [HasDerivedCategory.{d} (ModuleCat.{w} Λ)] (P : CochainComplex (ModuleCat.{w} Λ) ℤ) (a b : ℤ)
    [P.IsStrictlyGE a] [P.IsStrictlyLE b]
    (hfin : ∀ i : ℤ, Module.Finite Λ (P.X i)) (hproj : ∀ i : ℤ, Module.Projective Λ (P.X i)) :
    IsPerfect (DerivedCategory.Q.obj P) :=
  ⟨P, a, b, inferInstance, inferInstance, hfin, hproj, ⟨Iso.refl _⟩⟩

end StacksDraft.Perfect

namespace AlgebraicGeometry.RingedSite

section AnyValueUniverse

variable (X : RingedSite.{u, v, w}) (U : X.C)
variable [∀ W : X.C, HasSheafify (X.J.over W) AddCommGrpCat.{w}]
variable [∀ W : X.C, (X.J.over W).WEqualsLocallyBijective AddCommGrpCat.{w}]

variable [HasDerivedCategory.{d}
  (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U))]

/-- Let `Φ` be an additive right exact functor from `Λ`-modules to sheaves of `O|_U`-modules
taking `Λ` to the unit object, with modules in an arbitrary universe `w`. Let `K^•` be a bounded
complex of finite projective `Λ`-modules and `L^•` a complex of sheaves of `O|_U`-modules. Any
morphism `Φ(K^•) ⟶ L^•` of `D(O|_U)` is, after restriction along the arrows of a covering sieve
of `U`, the image under the localisation functor of a morphism of complexes. -/
theorem exists_coveringSieve_complexMap_of_finite_projective_valueUniverse
    {Λ : Type w} [Ring Λ]
    (Φ : ModuleCat.{w} Λ ⥤ SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U))
    [Φ.Additive]
    [PreservesFiniteColimits Φ]
    (e : Φ.obj (ModuleCat.of Λ Λ) ≅
      SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U))
    {P : CochainComplex (ModuleCat.{w} Λ) ℤ} (a b : ℤ)
    [P.IsStrictlyGE a] [P.IsStrictlyLE b]
    (hfin : ∀ i : ℤ, Module.Finite Λ (P.X i)) (hproj : ∀ i : ℤ, Module.Projective Λ (P.X i))
    {F : CochainComplex
      (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U)) ℤ}
    (α : DerivedCategory.Q.obj ((Φ.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ⟶
      DerivedCategory.Q.obj F) :
    ∃ S : Sieve U, S ∈ X.J U ∧
      ∀ {V : X.C} (f : V ⟶ U), S f →
        let H := SheafOfModules.overMap (Stacks.SheafOfModules.Tensor.ringSheaf X.O) f
        ∃ (hsheaf : HasSheafify (X.J.over V) AddCommGrpCat.{w})
          (hlocal : (X.J.over V).WEqualsLocallyBijective AddCommGrpCat.{w}),
          letI := hsheaf
          letI := hlocal
          letI : HasDerivedCategory
              (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V)) :=
            HasDerivedCategory.standard _
          ∃ (hadd : H.Additive)
            (hlim : PreservesFiniteLimits H)
            (hcolim : PreservesFiniteColimits H),
            letI := hadd
            letI := hlim
            letI := hcolim
            ∃ β : (H.mapHomologicalComplex (ComplexShape.up ℤ)).obj
                ((Φ.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ⟶
                (H.mapHomologicalComplex (ComplexShape.up ℤ)).obj F,
              H.mapDerivedCategory.map α ≫ H.mapDerivedCategoryFactors.hom.app F =
                H.mapDerivedCategoryFactors.hom.app
                    ((Φ.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≫
                  DerivedCategory.Q.map β :=
  exists_coveringSieve_complexMap_independentUniverses X U
    (Stacks.SheafOfModules.isStrictlyPerfect_mapHomologicalComplex_of_finite_projective Φ e
      (Stacks.SheafOfModules.finite_notIsZero_of_strictlyBounded P a b) hfin hproj) α

end AnyValueUniverse

variable (X : RingedSite.{u, u, 0}) (U : X.C)
variable [∀ W : X.C, HasSheafify (X.J.over W) AddCommGrpCat.{0}]
variable [∀ W : X.C, (X.J.over W).WEqualsLocallyBijective AddCommGrpCat.{0}]

variable [HasDerivedCategory.{d}
  (SheafOfModules.{0} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U))]

/-- Let `Φ` be an additive right exact functor from `Λ`-modules to sheaves of `O|_U`-modules
taking `Λ` to the unit object. Let `K^•` be a bounded complex of finite projective `Λ`-modules
and `L^•` a complex of sheaves of `O|_U`-modules. Any morphism `Φ(K^•) ⟶ L^•` of `D(O|_U)` is,
after restriction along the arrows of a covering sieve of `U`, the image under the localisation
functor of a morphism of complexes. -/
@[stacks 09BD "local_representation_for_a_transported_finite_projective_complex"]
theorem exists_coveringSieve_complexMap_of_finite_projective
    {Λ : Type} [Ring Λ]
    (Φ : ModuleCat.{0} Λ ⥤ SheafOfModules.{0} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U))
    [Φ.Additive]
    [PreservesFiniteColimits Φ]
    (e : Φ.obj (ModuleCat.of Λ Λ) ≅
      SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U))
    {P : CochainComplex (ModuleCat.{0} Λ) ℤ} (a b : ℤ)
    [P.IsStrictlyGE a] [P.IsStrictlyLE b]
    (hfin : ∀ i : ℤ, Module.Finite Λ (P.X i)) (hproj : ∀ i : ℤ, Module.Projective Λ (P.X i))
    {F : CochainComplex
      (SheafOfModules.{0} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U)) ℤ}
    (α : DerivedCategory.Q.obj ((Φ.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ⟶
      DerivedCategory.Q.obj F) :
    ∃ S : Sieve U, S ∈ X.J U ∧
      ∀ {V : X.C} (f : V ⟶ U), S f →
        let H := SheafOfModules.overMap (Stacks.SheafOfModules.Tensor.ringSheaf X.O) f
        ∃ (hsheaf : HasSheafify (X.J.over V) AddCommGrpCat)
          (hlocal : (X.J.over V).WEqualsLocallyBijective AddCommGrpCat),
          letI := hsheaf
          letI := hlocal
          letI : HasDerivedCategory
              (SheafOfModules ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V)) :=
            HasDerivedCategory.standard _
          ∃ (hadd : H.Additive)
            (hlim : PreservesFiniteLimits H)
            (hcolim : PreservesFiniteColimits H),
            letI := hadd
            letI := hlim
            letI := hcolim
            ∃ β : (H.mapHomologicalComplex (ComplexShape.up ℤ)).obj
                ((Φ.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ⟶
                (H.mapHomologicalComplex (ComplexShape.up ℤ)).obj F,
              H.mapDerivedCategory.map α ≫ H.mapDerivedCategoryFactors.hom.app F =
                H.mapDerivedCategoryFactors.hom.app
                    ((Φ.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≫
                  DerivedCategory.Q.map β :=
  exists_coveringSieve_complexMap_of_finite_projective_valueUniverse X U Φ e a b hfin hproj α

end AlgebraicGeometry.RingedSite

end
