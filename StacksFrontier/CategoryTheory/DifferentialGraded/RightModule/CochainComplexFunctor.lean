module

public import Mathlib.Algebra.Homology.HomotopyCategory
public import StacksFrontier.CategoryTheory.DifferentialGraded.RightModule.Cohomology
public import StacksFrontier.CategoryTheory.DifferentialGraded.RightModule.ShiftAxiomB

/-!
# Evaluation at an object, as a functor to complexes of modules

Let `C` be a differential graded category over a commutative ring `R` and let `X` be an object
of `C`. A right differential graded `C`-module `M` has, at `X`, the cochain complex `M X` of
`R`-modules of
`StacksFrontier.CategoryTheory.DifferentialGraded.RightModule.Cohomology`. This file makes that
assignment a functor, first on the category of complexes `Comp(Mod^dg(C))` and then on the
homotopy category:

`ev_X : K(Mod^dg(C)) ⥤ K(ModuleCat R)`.

A closed degree-zero homogeneous morphism is precisely one commuting with the differentials, so
it is a map of the complexes; a degree `-1` homogeneous morphism whose differential is the
difference of two such is precisely a homotopy between them, in Mathlib's sense — the Koszul
sign `(-1)^p` of the differential of a homogeneous morphism is `-1` in degree `-1`, which turns
the graded commutator `d_N ∘ h - (-1)^p h ∘ d_M` into the sum `d_N ∘ h + h ∘ d_M` that
`Homotopy.comm` asks for. So no sign convention has to be reconciled.

For the one-object differential graded category `E = C(K, K)` of
`StacksFrontier.CategoryTheory.DifferentialGraded.EndomorphismDGCategory` this is the whole
underlying-complex functor: a right differential graded `E`-module *is* a single complex of
`R`-modules with an action of `C(K, K)`, and `ev_∗` forgets the action.

## Main definitions

* `DGCategory.RightModule.cochainMap`: a closed degree-zero homogeneous morphism, read at `X`
  as a map of complexes of `R`-modules.
* `DGCategory.RightModule.cochainHomotopy`: a degree `-1` homogeneous morphism, read at `X` as
  a homotopy.
* `DGCategory.RightModule.cochainComplexFunctor`: `ev_X : Comp(Mod^dg(C)) ⥤ CochainComplex R`.
* `DGCategory.RightModule.cochainComplexOnK`: `ev_X : K(Mod^dg(C)) ⥤ K(ModuleCat R)`.

## Main results

* `DGCategory.RightModule.app_d_of_closed`: a closed degree-zero homogeneous morphism commutes
  with the differentials.
* `DGCategory.RightModule.app_homComp_zero`: the composite of two degree-zero homogeneous
  morphisms, read in a single degree.
* `DGCategory.RightModule.cochainComplexOnK_map_mk`: the functor on the homotopy category
  carries the class of a closed degree-zero morphism to the class of its map of complexes.

## Implementation notes

The coboundary of the degree `-1` homogeneous morphism is evaluated through
`DGCategory.RightModule.app_dPrime`, which is stated at a variable degree with a variable target
degree and an equation between them rather than at `-1` and `0`: with the degrees variable the
equation can be substituted away, whereas `(-1 : ℤ) + 1` and `0` are not definitionally equal in
an argument position, so a specialised statement would carry a transport that every later
rewrite would have to step over.

The component of a homogeneous morphism is wrapped in the named
`DGCategory.RightModule.cochainMapComponent` rather than written inline: an anonymous function
inside the structure instance would be a beta-redex that the kernel unfolds at every later use.

## References

* [Stacks Project, Tag 09LK](https://stacks.math.columbia.edu/tag/09LK)
-/

@[expose] public section

namespace DGCategory

universe w v u r

open CategoryTheory

namespace RightModule

variable {R : Type r} [CommRing R] {C : DGCategory.{v, u} R}

/-! ### Transporting the target degree -/

variable {M N P : RightModule.{w} C}

/-- The composite of two degree-zero homogeneous morphisms, read in a single degree. -/
theorem app_homComp_zero (ψ : HomogeneousMap N P 0) (φ : HomogeneousMap M N 0)
    (hmn : (0 : ℤ) + 0 = 0) {x : C.Obj} (i : ℤ) (hi : i + 0 = i) (a : M.obj x i) :
    app (homComp hmn ψ φ) hi a = app ψ (add_zero i) (app φ (add_zero i) a) := by
  rw [app_homComp]
  exact (app_objCast ψ (add_zero i) (add_zero i) (show i + 0 + 0 = i by omega)
      (app φ rfl a)).symm.trans
    (congrArg (app ψ (add_zero i)) (objCast_app φ (add_zero i) a))

/-! ### A closed degree-zero morphism as a map of complexes -/

/-- **A closed degree-zero homogeneous morphism commutes with the differentials.** This is
exactly what closedness says: the graded commutator `d_N ∘ φ - φ ∘ d_M` vanishes. -/
theorem app_d_of_closed {φ : HomogeneousMap M N 0} (hφ : homD φ = 0) {x : C.Obj} {i j : ℤ}
    (h : i + 1 = j) (a : M.obj x i) :
    N.d h (app φ (add_zero i) a) = app φ (add_zero j) (M.d h a) := by
  subst h
  have h0 := congrArg
    (fun ψ : HomogeneousMap M N (0 + 1) => app ψ (show i + (0 + 1) = i + 1 by omega) a) hφ
  simp only [app_homD, zero_app, Int.natAbs_zero, pow_zero, one_smul] at h0
  rw [d_app φ (add_zero i) (rfl : i + 1 = i + 1) (show i + 0 + 1 = i + 1 by omega) a,
    ← sub_eq_zero]
  exact h0

/-- The degree-`i` component of a degree-zero homogeneous morphism, as a map of the degree-`i`
terms of the two complexes. -/
def cochainMapComponent (φ : HomogeneousMap M N 0) (X : C.Obj) (i : ℤ) :
    (M.cochainComplex X).X i ⟶ (N.cochainComplex X).X i :=
  ModuleCat.ofHom (φ.1 ⟨X, i, i, add_zero i⟩)

/-- The underlying linear map of `cochainMapComponent φ X i` is the component of `φ` at
`(X, i, i)`. -/
@[simp] theorem hom_cochainMapComponent (φ : HomogeneousMap M N 0) (X : C.Obj) (i : ℤ) :
    (cochainMapComponent φ X i).hom = φ.1 ⟨X, i, i, add_zero i⟩ := rfl

/-- `cochainMapComponent φ X i` sends `a` to `app φ (add_zero i) a`. -/
theorem cochainMapComponent_apply (φ : HomogeneousMap M N 0) (X : C.Obj) (i : ℤ)
    (a : M.obj X i) : (cochainMapComponent φ X i).hom a = app φ (add_zero i) a := rfl

/-- **A morphism of right differential graded modules, read at `X` as a map of complexes.** A
morphism of `Comp(Mod^dg(C))` is a closed degree-zero homogeneous morphism, and closedness is
commutation with the differentials. -/
def cochainMap (φ : (rightModuleCategory.{w} C).Cocycle M N) (X : C.Obj) :
    M.cochainComplex X ⟶ N.cochainComplex X where
  f i := cochainMapComponent φ.1 X i
  comm' i j hij := by
    obtain rfl : i + 1 = j := hij
    ext a
    simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply,
      cochainComplex_d _ X (rfl : i + 1 = i + 1), ModuleCat.hom_ofHom, dLinear_apply,
      hom_cochainMapComponent, coe_apply]
    exact app_d_of_closed φ.2 (rfl : i + 1 = i + 1) a

/-- The degree-`i` component of `cochainMap φ X` is `cochainMapComponent φ.1 X i`. -/
@[simp] theorem cochainMap_f (φ : (rightModuleCategory.{w} C).Cocycle M N) (X : C.Obj) (i : ℤ) :
    (cochainMap φ X).f i = cochainMapComponent φ.1 X i := rfl

/-! ### Functoriality on the category of complexes -/

/-- **Evaluation at `X` on the category of complexes**, `Comp(Mod^dg(C)) ⥤ CochainComplex R`:
a right differential graded `C`-module goes to the complex `M X`, and a closed degree-zero
morphism to its map of complexes. -/
def cochainComplexFunctor (X : C.Obj) :
    (rightModuleCategory.{w} C).Comp ⥤ CochainComplex (ModuleCat.{w} R) ℤ where
  obj M := RightModule.cochainComplex (C := C) M X
  map φ := cochainMap φ X
  map_id M := by
    ext i a
    exact objCast_rfl (M := M) X a
  map_comp {M N P} φ ψ := by
    ext i a
    exact app_homComp_zero ψ.1 φ.1 (by omega) i (add_zero i) a

/-- `cochainComplexFunctor X` sends a module `M` to the complex `M.cochainComplex X`. -/
@[simp] theorem cochainComplexFunctor_obj (X : C.Obj) (M : (rightModuleCategory.{w} C).Comp) :
    (cochainComplexFunctor.{w} X).obj M = RightModule.cochainComplex (C := C) M X := rfl

/-- `cochainComplexFunctor X` sends a morphism `φ` to `cochainMap φ X`. -/
@[simp] theorem cochainComplexFunctor_map (X : C.Obj) {M N : (rightModuleCategory.{w} C).Comp}
    (φ : M ⟶ N) : (cochainComplexFunctor.{w} X).map φ = cochainMap φ X := rfl

/-! ### Homotopies -/

/-- The degree-`(i, j)` component of the homotopy attached to a degree `-1` homogeneous
morphism: its value when `j + 1 = i`, and zero otherwise. -/
def cochainHomotopyHom (h : HomogeneousMap M N (-1)) (X : C.Obj) (i j : ℤ) :
    (M.cochainComplex X).X i ⟶ (N.cochainComplex X).X j :=
  if e : j + 1 = i then ModuleCat.ofHom (h.1 ⟨X, i, j, by omega⟩) else 0

/-- When `j + 1 = i`, the component `cochainHomotopyHom h X i j` is the component of `h` at
`(X, i, j)`. -/
theorem cochainHomotopyHom_pos (h : HomogeneousMap M N (-1)) (X : C.Obj) {i j : ℤ}
    (e : j + 1 = i) : cochainHomotopyHom h X i j = ModuleCat.ofHom (h.1 ⟨X, i, j, by omega⟩) :=
  dif_pos e

/-- **A degree `-1` homogeneous morphism is a homotopy.** If the difference of two closed
degree-zero morphisms is the coboundary of `h`, then `h`, read at `X`, is a homotopy between
their maps of complexes: the graded commutator in degree `-1` is `d_N ∘ h + h ∘ d_M`, which is
`Homotopy.comm`. -/
def cochainHomotopy {φ ψ : (rightModuleCategory.{w} C).Cocycle M N} (h : HomogeneousMap M N (-1))
    (hh : φ.1 - ψ.1 = (rightModuleCategory.{w} C).d' (show (-1 : ℤ) + 1 = 0 by omega) h)
    (X : C.Obj) : Homotopy (cochainMap φ X) (cochainMap ψ X) where
  hom := cochainHomotopyHom h X
  zero i j hij := dif_neg hij
  comm i := by
    have hsign : (-1 : R) ^ ((-1 : ℤ)).natAbs = -1 := by norm_num
    have key : ∀ a : M.obj X i, app φ.1 (add_zero i) a =
        app h (show i + 1 + -1 = i by omega) (M.d rfl a) +
          N.d (show i - 1 + 1 = i by omega) (app h (show i + -1 = i - 1 by omega) a) +
            app ψ.1 (add_zero i) a := by
      intro a
      have h1 := congrArg
        (fun χ : (rightModuleCategory.{w} C).Hom M N 0 => app χ (add_zero i) a) hh
      rw [app_dPrime (show (-1 : ℤ) + 1 = 0 by omega) h (add_zero i) a, app_homD] at h1
      have h2 : app φ.1 (add_zero i) a - app ψ.1 (add_zero i) a =
          N.d (show i + -1 + 1 = i by omega) (app h rfl a) -
            (-1 : R) ^ ((-1 : ℤ)).natAbs •
              app h (show i + 1 + -1 = i by omega) (M.d rfl a) := h1
      rw [d_app h (show i + -1 = i - 1 by omega) (show i - 1 + 1 = i by omega)
          (show i + -1 + 1 = i by omega) a, ← sub_eq_iff_eq_add, h2, hsign, neg_smul, one_smul,
        sub_neg_eq_add]
      exact add_comm _ _
    rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel i (i + 1) from rfl),
      prevD_eq _ (show (ComplexShape.up ℤ).Rel (i - 1) i from (by omega : i - 1 + 1 = i)),
      cochainHomotopyHom_pos h X (rfl : i + 1 = i + 1),
      cochainHomotopyHom_pos h X (show i - 1 + 1 = i by omega),
      cochainComplex_d M X (rfl : i + 1 = i + 1),
      cochainComplex_d N X (show i - 1 + 1 = i by omega)]
    ext a
    exact key a

/-! ### Functoriality on the homotopy category -/

/-- Homotopic closed degree-zero morphisms have the same image in the homotopy category of
complexes of `R`-modules. -/
theorem quotient_map_cochainMap_eq_of_homotopic
    {φ ψ : (rightModuleCategory.{w} C).Cocycle M N}
    (hh : (rightModuleCategory.{w} C).Homotopic φ ψ) (X : C.Obj) :
    (HomotopyCategory.quotient (ModuleCat.{w} R) (ComplexShape.up ℤ)).map (cochainMap φ X) =
      (HomotopyCategory.quotient (ModuleCat.{w} R) (ComplexShape.up ℤ)).map (cochainMap ψ X) :=
  HomotopyCategory.eq_of_homotopy _ _ (cochainHomotopy hh.choose hh.choose_spec X)

/-- **Evaluation at `X` on the homotopy categories**, `K(Mod^dg(C)) ⥤ K(ModuleCat R)`: the
descent of `DGCategory.RightModule.cochainComplexFunctor` through the homotopy relations, which
exists because the coboundary of a degree `-1` homogeneous morphism is a homotopy. -/
def cochainComplexOnK (X : C.Obj) :
    (rightModuleCategory.{w} C).K ⥤ HomotopyCategory (ModuleCat.{w} R) (ComplexShape.up ℤ) where
  obj M := (HomotopyCategory.quotient (ModuleCat.{w} R) (ComplexShape.up ℤ)).obj
    (RightModule.cochainComplex (C := C) M X)
  map {M N} f := Quotient.liftOn f
    (fun φ => (HomotopyCategory.quotient (ModuleCat.{w} R) (ComplexShape.up ℤ)).map
      (cochainMap φ X))
    (fun _ _ hh => quotient_map_cochainMap_eq_of_homotopic hh X)
  map_id M := by
    show (HomotopyCategory.quotient (ModuleCat.{w} R) (ComplexShape.up ℤ)).map
      (cochainMap ⟨(rightModuleCategory.{w} C).id M, (rightModuleCategory.{w} C).d_id M⟩ X) = _
    rw [show cochainMap
        (⟨(rightModuleCategory.{w} C).id M, (rightModuleCategory.{w} C).d_id M⟩ :
          (rightModuleCategory.{w} C).Cocycle M M) X =
        𝟙 (RightModule.cochainComplex (C := C) M X) from
      (cochainComplexFunctor.{w} (C := C) X).map_id M]
    exact (HomotopyCategory.quotient (ModuleCat.{w} R) (ComplexShape.up ℤ)).map_id _
  map_comp {M N P} f g := by
    refine Quotient.inductionOn₂ f g fun φ ψ => ?_
    show (HomotopyCategory.quotient (ModuleCat.{w} R) (ComplexShape.up ℤ)).map
      (cochainMap ((rightModuleCategory.{w} C).compCocycle ψ φ) X) = _
    rw [show cochainMap ((rightModuleCategory.{w} C).compCocycle ψ φ) X =
        cochainMap φ X ≫ cochainMap ψ X from
      (cochainComplexFunctor.{w} (C := C) X).map_comp φ ψ]
    exact (HomotopyCategory.quotient (ModuleCat.{w} R) (ComplexShape.up ℤ)).map_comp _ _

/-- `cochainComplexOnK X` sends a module `M` to the image of the complex `M.cochainComplex X` in
the homotopy category. -/
@[simp] theorem cochainComplexOnK_obj (X : C.Obj) (M : (rightModuleCategory.{w} C).K) :
    (cochainComplexOnK.{w} X).obj M =
      (HomotopyCategory.quotient (ModuleCat.{w} R) (ComplexShape.up ℤ)).obj
        (RightModule.cochainComplex (C := C) M X) := rfl

/-- The functor on the homotopy category carries the class of a closed degree-zero morphism to
the class of its map of complexes. -/
@[simp] theorem cochainComplexOnK_map_mk (X : C.Obj)
    (φ : (rightModuleCategory.{w} C).Cocycle M N) :
    (cochainComplexOnK.{w} X).map (Quotient.mk _ φ) =
      (HomotopyCategory.quotient (ModuleCat.{w} R) (ComplexShape.up ℤ)).map (cochainMap φ X) :=
  rfl

/-- **Evaluation at `X` commutes with the passage to homotopy classes.** The two functors
`Comp(Mod^dg(C)) ⥤ K(ModuleCat R)` obtained by evaluating at `X` before and after passing to
homotopy classes are equal, not merely isomorphic: both are the identity on objects and send a
closed degree-zero morphism to the homotopy class of its map of complexes. -/
theorem compToK_comp_cochainComplexOnK (X : C.Obj) :
    compToK (rightModuleCategory.{w} C) ⋙ cochainComplexOnK.{w} X =
      cochainComplexFunctor.{w} X ⋙
        HomotopyCategory.quotient (ModuleCat.{w} R) (ComplexShape.up ℤ) :=
  rfl

end RightModule

end DGCategory

end
