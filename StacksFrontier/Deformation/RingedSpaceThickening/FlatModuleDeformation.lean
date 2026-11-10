module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorUnitSections
public import StacksFrontier.Deformation.RingedSpaceThickening.FlatLiftTorsor
public import StacksFrontier.Topology.Sheaves.RingedSpace.ModulePullbackUnit
import StacksCore.Tactic.StacksAttribute

/-!
# Flat modules on flat thickenings of ringed spaces (Stacks 08VR)

Let

```
X  --i-->  X'
|          |
f          f'
v          v
S  --t-->  S'
```

be a morphism of first order thickenings of ringed spaces with ideal sheaves
`ℐ = ker(i^♯)` and `𝒥 = ker(t^♯)`, let the square be strict, let `f'` be flat and let `ℱ` be an
`𝒪_X`-module flat over `S`. Flatness of `f'` identifies `ℐ` with `f^* 𝒥`, so the coefficient
module `ℐ ⊗_{𝒪_X} ℱ` of **Stacks 08LM** becomes `f^* 𝒥 ⊗_{𝒪_X} ℱ`, and **Stacks 08VR** reads
the three statements of **Stacks 08LN**, **Stacks 08LM** and **Stacks 08LJ** in that module: a
lift of `ℱ` to an `𝒪_{X'}`-module flat over `S'` exists exactly when
`o(ℱ, f^* 𝒥 ⊗_{𝒪_X} ℱ, 1) ∈ Ext²_{𝒪_X}(ℱ, f^* 𝒥 ⊗_{𝒪_X} ℱ)` vanishes, the isomorphism classes
of lifts are principal homogeneous under `Ext¹_{𝒪_X}(ℱ, f^* 𝒥 ⊗_{𝒪_X} ℱ)`, and the
automorphisms of a fixed lift restricting to the identity are canonically
`Ext⁰_{𝒪_X}(ℱ, f^* 𝒥 ⊗_{𝒪_X} ℱ)`.

## Main definitions

* `AlgebraicGeometry.RingedSpaceThickening.FlatModuleDeformation.baseIdealTensorIso`: the
  isomorphism that the canonical map `f^* 𝒥 ⊗_{𝒪_X} ℱ ⟶ ℐ ⊗_{𝒪_X} ℱ` becomes under
  `ℐ = f^* 𝒥`.
* `AlgebraicGeometry.RingedSpaceThickening.FlatModuleDeformation.extPostcomp`: composition with
  an isomorphism of the coefficient object, as a bijection of `Ext` groups.
* `AlgebraicGeometry.RingedSpaceThickening.FlatModuleDeformation.flatDeformationObstruction`:
  the class `o(ℱ, f^* 𝒥 ⊗_{𝒪_X} ℱ, 1)`.
* `AlgebraicGeometry.RingedSpaceThickening.FlatModuleDeformation.flatLiftClassDifferenceBase`:
  the difference of two isomorphism classes of flat lifts in
  `Ext¹_{𝒪_X}(ℱ, f^* 𝒥 ⊗_{𝒪_X} ℱ)`.
* `AlgebraicGeometry.RingedSpaceThickening.FlatModuleDeformation.liftCoefficientIso` and
  `FlatModuleDeformation.liftHomEquiv`: the identification of the acting group of
  **Stacks 08LJ** for a flat lift with `Hom_{𝒪_X}(ℱ, f^* 𝒥 ⊗_{𝒪_X} ℱ)`.
* `FlatModuleDeformation.liftInfinitesimalEndo`, `FlatModuleDeformation.identityLiftAut` and
  `FlatModuleDeformation.identityLiftAutEquiv`: the endomorphism `ε_δ : ℱ' ⟶ ℐℱ' ⟶ ℱ'`, the
  automorphism `1 + ε_δ`, and the resulting bijection between the automorphisms of a flat lift
  restricting to the identity and `Hom_{𝒪_X}(ℱ, f^* 𝒥 ⊗_{𝒪_X} ℱ)`.

## Main results

* `FlatModuleDeformation.isIso_baseToSourceIdeal_of_isFlat`: the identification `ℐ = f^* 𝒥` of
  Section 91.6, from flatness of `f'`.
* `FlatModuleDeformation.nonempty_flatLift_iff_flatDeformationObstruction_eq_zero`:
  **Stacks 08VR**, clause (1).
* `FlatModuleDeformation.flatLiftClassDifferenceBase_isPrincipalHomogeneous`: **Stacks 08VR**,
  clause (2).
* `FlatModuleDeformation.exists_identityLiftAut_equiv_ext_zero`: **Stacks 08VR**, clause (3).

## Implementation notes

The obstruction class is pinned, not asserted to exist: `flatDeformationObstruction` *is* the
class `AlgebraicGeometry.RingedSpaceThickening.obstructionClass` of **Stacks 08L8** for the
coefficient module `ℐ ⊗_{𝒪_X} ℱ` and the normalization `c = 1`, pushed along the identification
`ℐ = f^* 𝒥`, so clause (1) is a statement about that recipe. A bare existence statement for a
class with the right zero locus is satisfied by every nonzero class whenever no lift exists.

`extPostcomp e n` is the bijection `x ↦ x · e` of `Ext` groups; `extPostcomp_eq_zero_iff` is
what carries a vanishing criterion from one coefficient module to an isomorphic one, in degree
`2` for clause (1) and in degree `1` for clause (2).

Flatness of `f'` is `AlgebraicGeometry.IsFlat D.f'`, flatness of every stalk map. The
identification `ℐ = f^* 𝒥` is the invertibility of `D.baseToSourceIdeal`, proved in
`isIso_baseToSourceIdeal_of_isFlat` as the source indicates, by **Stacks 08LI** applied to
`𝒪_{X'}`; the definitions `flatDeformationObstruction` and `flatLiftClassDifferenceBase` take
that invertibility as an argument, and the three clauses supply it from flatness of `f'`.

Clause (3) is stated as a bijection between the automorphisms `φ` of `ℱ'` with `i^* φ = 1` and
`Ext⁰_{𝒪_X}(ℱ, f^* 𝒥 ⊗_{𝒪_X} ℱ)`, pinned by the formula `φ = 1 + ε_ξ`. Every endomorphism
restricting to the identity is of that form by **Stacks 08LJ**, and is invertible because
`ε_ξ` factors through the ideal multiple `ℐℱ'`, on which it vanishes, so `ε_ξ² = 0`.

## References

* [Stacks Project, Tag 08VR](https://stacks.math.columbia.edu/tag/08VR)
* [Stacks Project, Tag 08VQ](https://stacks.math.columbia.edu/tag/08VQ)
* [Stacks Project, Tag 08LN](https://stacks.math.columbia.edu/tag/08LN)
* [Stacks Project, Tag 08LM](https://stacks.math.columbia.edu/tag/08LM)
* [Stacks Project, Tag 08LJ](https://stacks.math.columbia.edu/tag/08LJ)
* [Stacks Project, Tag 08LI](https://stacks.math.columbia.edu/tag/08LI)
* [Stacks Project, Tag 08L8](https://stacks.math.columbia.edu/tag/08L8)
* [Stacks Project, Tag 08L1](https://stacks.math.columbia.edu/tag/08L1)
* [Stacks Project, Tag 08KZ](https://stacks.math.columbia.edu/tag/08KZ)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open RingedSpaceModuleAdjunction
open Stacks.SheafOfModules.TensorStalkRingedSpace

universe u w w'

namespace AlgebraicGeometry.RingedSpaceThickening.FlatModuleDeformation

variable (D : MorphismOfThickenings.{u})

/-- Tensoring an isomorphism with the identity on the right gives an isomorphism. -/
theorem isIso_tensorSheafMap_id_right {Y : RingedSpace.{u, u}}
    {A B : SheafOfModules.{u} (structureSheafRing Y)} (f : A ⟶ B) (hf : IsIso f)
    (C : SheafOfModules.{u} (structureSheafRing Y)) :
    IsIso (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨((Y)).presheaf, ((Y)).IsSheaf⟩)).map ((f, (𝟙 C)) : (_, _) ⟶ (_, _)))) :=
  (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨((Y)).presheaf, ((Y)).IsSheaf⟩))).mapIso
    (Iso.prod (@asIso _ _ _ _ f hf) (Iso.refl C))).isIso_hom

/-- **The right unitor `𝒜 ⊗_{𝒪_Y} 𝒪_Y ≅ 𝒜` is natural**: both sides send the local section
`a ⊗ r` to `r • g(a)`. -/
theorem tensorSheafMap_comp_tensorSheafUnitRightIso {Y : RingedSpace.{u, u}}
    {A B : SheafOfModules.{u} (structureSheafRing Y)} (g : A ⟶ B) :
    ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨(Y).presheaf, (Y).IsSheaf⟩)).map
        ((g, (𝟙 (SheafOfModules.unit (structureSheafRing Y)))) : (_, _) ⟶ (_, _))) ≫
        (AlgebraicGeometry.SheafOfModules.tensorSheafUnitRightIso Y B).hom =
      (AlgebraicGeometry.SheafOfModules.tensorSheafUnitRightIso Y A).hom ≫ g := by
  refine tensorSheaf_hom_ext fun V a r₀ => ?_
  let r : (structureSheafRing Y).obj.obj (op V) := r₀
  calc ((AlgebraicGeometry.SheafOfModules.tensorSheafUnitRightIso Y B).hom.val.app (op V)).hom
          (((((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
              ⟨(Y).presheaf, (Y).IsSheaf⟩)).map
                ((g, (𝟙 (SheafOfModules.unit (structureSheafRing Y)))) :
                  (_, _) ⟶ (_, _)))).val.app
            (op V)).hom (toTensorSheafSection Y A _ (op V) (a ⊗ₜ[Y.presheaf.obj (op V)] r₀)))
      = ((AlgebraicGeometry.SheafOfModules.tensorSheafUnitRightIso Y B).hom.val.app (op V)).hom
          (toTensorSheafSection Y B _ (op V)
            ((g.val.app (op V)).hom a ⊗ₜ[Y.presheaf.obj (op V)] r)) :=
        congrArg _ ((tensorSheafMap_app_toTensorSheafSection Y A _ B _ g _ V a r₀).trans rfl)
    _ = r • (g.val.app (op V)).hom a :=
        AlgebraicGeometry.SheafOfModules.tensorSheafUnitRightIso_hom_toTensorSheafSection Y B
          (op V) _ r
    _ = (g.val.app (op V)).hom (r • (show A.val.obj (op V) from a)) :=
        ((g.val.app (op V)).hom.map_smul r a).symm
    _ = (g.val.app (op V)).hom
          (((AlgebraicGeometry.SheafOfModules.tensorSheafUnitRightIso Y A).hom.val.app
            (op V)).hom (toTensorSheafSection Y A _ (op V) (a ⊗ₜ[Y.presheaf.obj (op V)] r₀))) :=
        congrArg _
          (AlgebraicGeometry.SheafOfModules.tensorSheafUnitRightIso_hom_toTensorSheafSection
            Y A (op V) a r).symm

/-- In a commutative square with three isomorphic sides, the fourth side is an isomorphism. -/
private theorem isIso_of_comm_sq_of_isIso {𝒞 : Type*} [Category 𝒞] {A B C D : 𝒞}
    {f : A ⟶ B} {g : C ⟶ D} {u : A ⟶ C} {v : B ⟶ D} (w : f ≫ v = u ≫ g) (hf : IsIso f)
    (hu : IsIso u) (hv : IsIso v) : IsIso g :=
  isIso_of_isIso_comp_left u g hu (isIso_of_eq w (isIso_comp_of_isIso _ _ hf hv))

/-- **Tensoring with the structure sheaf reflects isomorphisms**: `g ⊗ 𝒪_Y` is `g` conjugated by
the right unitors. -/
theorem isIso_of_isIso_tensorSheafMap_unit {Y : RingedSpace.{u, u}}
    {A B : SheafOfModules.{u} (structureSheafRing Y)} (g : A ⟶ B)
    (hg : IsIso (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨(Y).presheaf, (Y).IsSheaf⟩)).map
        ((g, (𝟙 (SheafOfModules.unit (structureSheafRing Y)))) : (_, _) ⟶ (_, _))))) :
    IsIso g :=
  isIso_of_comm_sq_of_isIso (tensorSheafMap_comp_tensorSheafUnitRightIso g) hg
    (AlgebraicGeometry.SheafOfModules.tensorSheafUnitRightIso Y A).isIso_hom
    (AlgebraicGeometry.SheafOfModules.tensorSheafUnitRightIso Y B).isIso_hom

/-- **Tensoring with a module isomorphic to the structure sheaf reflects isomorphisms.** -/
theorem isIso_of_isIso_tensorSheafMap_id_right {Y : RingedSpace.{u, u}}
    {A B G : SheafOfModules.{u} (structureSheafRing Y)} (g : A ⟶ B)
    (e : G ≅ SheafOfModules.unit (structureSheafRing Y))
    (hg : IsIso (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨(Y).presheaf, (Y).IsSheaf⟩)).map ((g, (𝟙 G)) : (_, _) ⟶ (_, _))))) :
    IsIso g :=
  isIso_of_isIso_tensorSheafMap_unit g
    (isIso_of_comm_sq_of_isIso (tensorSheafMap_id_comm g e.hom) hg
      (isIso_tensorSheafMap_id_left A e.hom e.isIso_hom)
      (isIso_tensorSheafMap_id_left B e.hom e.isIso_hom))

/-- **The identification `ℐ = f^* 𝒥` of Section 91.6.** For a strict morphism of thickenings
with `f'` flat, the canonical map `f^* 𝒥 ⟶ i^* ℐ` is an isomorphism. This is **Stacks 08LI**
applied to `𝒪_{X'}`, which is flat over `S'`: the canonical map tensored with
`i^* 𝒪_{X'} ≅ 𝒪_X` is an epimorphism by strictness and a monomorphism because its composite with
the ideal action is invertible. -/
theorem isIso_baseToSourceIdeal_of_isFlat (hs : D.IsStrict) (hf' : AlgebraicGeometry.IsFlat D.f') :
    IsIso D.baseToSourceIdeal := by
  let M := SheafOfModules.unit (structureSheafRing D.X')
  have hM : AlgebraicGeometry.IsFlatOver D.f' M := isFlatOver_unit_of_isFlat D.f' hf'
  have hcomp : IsIso (baseToInfinitesimal D M) := isIso_baseToInfinitesimal_of_isFlatOver D hs M hM
  have hepi : Epi (baseToSourceIdealTensor D M) :=
    @AlgebraicGeometry.SheafOfModules.tensorSheafMap_epi D.X _ _
      ((modulePullback D.i).obj M) D.baseToSourceIdeal (D.epi_baseToSourceIdeal hs)
  have hmono : Mono (baseToSourceIdealTensor D M) := by
    have : Mono (baseToSourceIdealTensor D M ≫ sourceIdealActionImage D M) :=
      ((isIso_iff_mono_and_epi _).mp hcomp).1
    exact mono_of_mono _ (sourceIdealActionImage D M)
  have hp : IsIso (baseToSourceIdealTensor D M) := isIso_of_mono_of_epi _
  exact isIso_of_isIso_tensorSheafMap_id_right D.baseToSourceIdeal (modulePullbackUnitIso D.i) hp

/-- The identification `f^* 𝒥 ⊗_{𝒪_X} ℱ ≅ ℐ ⊗_{𝒪_X} ℱ` produced by the identification
`ℐ = f^* 𝒥` of the section's setup. -/
noncomputable def baseIdealTensorIso (hI : IsIso D.baseToSourceIdeal)
    (F : SheafOfModules.{u} (structureSheafRing D.X)) : baseIdealTensor D F ≅ idealTensor D F :=
  @asIso _ _ _ _ (baseIdealTensorComparison D F)
    (isIso_tensorSheafMap_id_right D.baseToSourceIdeal hI F)

section Ext

variable {C : Type*} [Category C] [Abelian C] [CategoryTheory.HasExt.{w} C]

/-- Composing with an isomorphism of the coefficient object is a bijection of `Ext` groups. -/
noncomputable def extPostcomp {A K K' : C} (e : K ≅ K') (n : ℕ) :
    CategoryTheory.Abelian.Ext.{w} A K n ≃ CategoryTheory.Abelian.Ext.{w} A K' n where
  toFun x := x.comp (CategoryTheory.Abelian.Ext.mk₀ e.hom) (add_zero n)
  invFun y := y.comp (CategoryTheory.Abelian.Ext.mk₀ e.inv) (add_zero n)
  left_inv x := by simp
  right_inv y := by simp

/-- The transported class vanishes exactly when the original one does. -/
theorem extPostcomp_eq_zero_iff {A K K' : C} (e : K ≅ K') (n : ℕ)
    (x : CategoryTheory.Abelian.Ext.{w} A K n) : extPostcomp e n x = 0 ↔ x = 0 := by
  have h0 : extPostcomp (A := A) e n 0 = 0 := by
    change (0 : CategoryTheory.Abelian.Ext.{w} A K n).comp
      (CategoryTheory.Abelian.Ext.mk₀ e.hom) (add_zero n) = 0
    simp
  exact ⟨fun h => (extPostcomp (A := A) e n).injective (h.trans h0.symm), fun h => h ▸ h0⟩

end Ext

/-! ### Clause (1): the obstruction to the existence of a flat deformation -/

section Obstruction

variable [CategoryTheory.HasExt.{w} (SheafOfModules.{u} (structureSheafRing D.X))]
  [HasDerivedCategory.{w'} (SheafOfModules.{u} (structureSheafRing D.X))]

/-- The obstruction class `o(ℱ, f^* 𝒥 ⊗_{𝒪_X} ℱ, 1) ∈ Ext²_{𝒪_X}(ℱ, f^* 𝒥 ⊗_{𝒪_X} ℱ)` of
Tag 08VR: the class of **Stacks 08L8** for the coefficient module `ℐ ⊗_{𝒪_X} ℱ` and the
normalization `c = 1`, read in the coefficient module `f^* 𝒥 ⊗_{𝒪_X} ℱ` through `ℐ = f^* 𝒥`. -/
noncomputable def flatDeformationObstruction (hi : IsFirstOrderThickening D.i)
    (hI : IsIso D.baseToSourceIdeal) (F : SheafOfModules.{u} (structureSheafRing D.X)) :
    CategoryTheory.Abelian.Ext.{w} F (baseIdealTensor D F) 2 :=
  extPostcomp (baseIdealTensorIso D hI F).symm 2
    (obstructionClass D.i hi F (idealTensor D F) (𝟙 (idealTensor D F)))

/-- **Stacks Project, Tag 08VR**, clause (1). Let `(f, f')` be a strict morphism of first order
thickenings of ringed spaces with `f'` flat, and let `ℱ` be an `𝒪_X`-module flat over `S`. There
is an `𝒪_{X'}`-module `ℱ'` flat over `S'` with `i^* ℱ' ≅ ℱ` if and only if the class
`o(ℱ, f^* 𝒥 ⊗_{𝒪_X} ℱ, 1)` of **Stacks 08L8** vanishes.

This is **Stacks 08LN** read through the identification `ℐ = f^* 𝒥`
(`isIso_baseToSourceIdeal_of_isFlat`), which makes its first condition automatic. -/
@[stacks 08VR "clause (1)"]
theorem nonempty_flatLift_iff_flatDeformationObstruction_eq_zero
    (hi : IsFirstOrderThickening D.i) (ht : IsFirstOrderThickening D.t) (hs : D.IsStrict)
    (hf' : AlgebraicGeometry.IsFlat D.f') (F : SheafOfModules.{u} (structureSheafRing D.X))
    (hF : AlgebraicGeometry.IsFlatOver D.f F) :
    Nonempty (FlatLift D F) ↔
      flatDeformationObstruction D hi (isIso_baseToSourceIdeal_of_isFlat D hs hf') F = 0 := by
  have hI := isIso_baseToSourceIdeal_of_isFlat D hs hf'
  refine (nonempty_flatLift_iff D hi ht hs F hF).trans ⟨fun h => ?_, fun h => ⟨?_, ?_⟩⟩
  · exact (extPostcomp_eq_zero_iff _ 2 _).2 h.2
  · exact isIso_tensorSheafMap_id_right D.baseToSourceIdeal hI F
  · exact (extPostcomp_eq_zero_iff _ 2 _).1 h

end Obstruction

/-! ### Clause (2): the action of `Ext¹` on the isomorphism classes of flat deformations -/

section Difference

variable [CategoryTheory.HasExt.{w} (SheafOfModules.{u} (structureSheafRing D.X))]
  [CategoryTheory.HasExt.{w} (SheafOfModules.{u} (structureSheafRing D.X'))]

/-- The difference of two isomorphism classes of flat lifts, as a class in
`Ext¹_{𝒪_X}(ℱ, f^* 𝒥 ⊗_{𝒪_X} ℱ)`: the difference of **Stacks 08LM** read in the coefficient
module of Tag 08VR through `ℐ = f^* 𝒥`. -/
noncomputable def flatLiftClassDifferenceBase (hi : IsFirstOrderThickening D.i)
    (hs : D.IsStrict) (hI : IsIso D.baseToSourceIdeal)
    (F : SheafOfModules.{u} (structureSheafRing D.X)) :
    FlatLiftClass D F → FlatLiftClass D F →
      CategoryTheory.Abelian.Ext.{w} F (baseIdealTensor D F) 1 :=
  fun a b => extPostcomp (baseIdealTensorIso D hI F).symm 1
    (flatLiftClassDifference hi hs F a b)

/-- Two isomorphism classes of flat deformations of `ℱ` agree exactly when their difference in
`Ext¹_{𝒪_X}(ℱ, f^* 𝒥 ⊗_{𝒪_X} ℱ)` vanishes. -/
theorem flatLiftClassDifferenceBase_eq_zero_iff (hi : IsFirstOrderThickening D.i)
    (hs : D.IsStrict) (hI : IsIso D.baseToSourceIdeal)
    {F : SheafOfModules.{u} (structureSheafRing D.X)} (a b : FlatLiftClass D F) :
    flatLiftClassDifferenceBase D hi hs hI F a b = 0 ↔ a = b :=
  (extPostcomp_eq_zero_iff _ 1 _).trans (flatLiftClassDifference_eq_zero_iff hi hs a b)

/-- **Stacks Project, Tag 08VR**, clause (2). Let `(f, f')` be a strict morphism of first order
thickenings of ringed spaces with `f'` flat, and let `ℱ` be an `𝒪_X`-module flat over `S`. The
isomorphism classes of lifts of `ℱ` to `𝒪_{X'}`-modules flat over `S'` form a principal
homogeneous space under `Ext¹_{𝒪_X}(ℱ, f^* 𝒥 ⊗_{𝒪_X} ℱ)`: the difference
`flatLiftClassDifferenceBase` is additive, and for every class `b` the map `a ↦ d(a, b)` is a
bijection onto `Ext¹_{𝒪_X}(ℱ, f^* 𝒥 ⊗_{𝒪_X} ℱ)`. When no lift exists both conditions hold
vacuously.

This is **Stacks 08LM** read through the identification `ℐ = f^* 𝒥`. -/
@[stacks 08VR "clause (2)"]
theorem flatLiftClassDifferenceBase_isPrincipalHomogeneous (hi : IsFirstOrderThickening D.i)
    (ht : IsFirstOrderThickening D.t) (hs : D.IsStrict) (hf' : AlgebraicGeometry.IsFlat D.f')
    {F : SheafOfModules.{u} (structureSheafRing D.X)} (hF : AlgebraicGeometry.IsFlatOver D.f F) :
    (∀ a b c : FlatLiftClass D F,
      flatLiftClassDifferenceBase D hi hs (isIso_baseToSourceIdeal_of_isFlat D hs hf') F a b +
          flatLiftClassDifferenceBase D hi hs (isIso_baseToSourceIdeal_of_isFlat D hs hf') F b c =
        flatLiftClassDifferenceBase D hi hs (isIso_baseToSourceIdeal_of_isFlat D hs hf') F a c) ∧
      ∀ b : FlatLiftClass D F, Function.Bijective fun a : FlatLiftClass D F =>
        flatLiftClassDifferenceBase D hi hs (isIso_baseToSourceIdeal_of_isFlat D hs hf') F a b := by
  obtain ⟨hadd, hbij⟩ := flatLiftClassDifference_isPrincipalHomogeneous.{u, w} hi ht hs hF
  refine ⟨fun a b c => ?_, fun b =>
    (extPostcomp (baseIdealTensorIso D (isIso_baseToSourceIdeal_of_isFlat D hs hf') F).symm
      1).bijective.comp (hbij b)⟩
  change (flatLiftClassDifference hi hs F a b).comp _ (add_zero 1) +
      (flatLiftClassDifference hi hs F b c).comp _ (add_zero 1) =
    (flatLiftClassDifference hi hs F a c).comp _ (add_zero 1)
  rw [← CategoryTheory.Abelian.Ext.add_comp, hadd]

end Difference

/-! ### Clause (3): the endomorphisms of a flat deformation lifting the identity -/

/-- The identification `ℱ ⊗_{𝒪_X} f^* 𝒥 ≅ f^* 𝒥 ⊗_{𝒪_X} ℱ` for a flat lift: the symmetry of
the tensor product followed by the lift's own identification of its restriction with `ℱ`. -/
noncomputable def liftCoefficientIso {F : SheafOfModules.{u} (structureSheafRing D.X)}
    (A : FlatLift D F) : restrictionTensorBaseIdeal D A.module' ≅ baseIdealTensor D F :=
  tensorSheafCommIso D.X ((modulePullback D.i).obj A.module')
      ((modulePullback D.f).obj ((modulePullback D.t).obj D.idealJ)) ≪≫
    ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((D.X)).presheaf, ((D.X)).IsSheaf⟩).obj
      ((modulePullback D.f).obj ((modulePullback D.t).obj D.idealJ))).mapIso A.identification

/-- The acting group of Tag 08VR clause (3), `Hom_{𝒪_X}(ℱ, f^* 𝒥 ⊗_{𝒪_X} ℱ)`, identified with
the acting group of **Stacks 08LJ** for a flat lift. -/
noncomputable def liftHomEquiv {F : SheafOfModules.{u} (structureSheafRing D.X)}
    (A : FlatLift D F) :
    ((modulePullback D.i).obj A.module' ⟶ restrictionTensorBaseIdeal D A.module') ≃
      (F ⟶ baseIdealTensor D F) :=
  Iso.homCongr A.identification (liftCoefficientIso D A)

/-- For a fixed flat deformation `ℱ'` the endomorphisms of `ℱ'` restricting to the identity on
`ℱ` form a principal homogeneous space under `Hom_{𝒪_X}(ℱ, f^* 𝒥 ⊗_{𝒪_X} ℱ)`: any one of them is
carried to any other by exactly one homomorphism. This is **Stacks 08LJ** for the lift of the
identity. -/
theorem existsUnique_identityLiftDifference (hi : IsFirstOrderThickening D.i) (hs : D.IsStrict)
    {F : SheafOfModules.{u} (structureSheafRing D.X)} (A : FlatLift D F)
    (φ₁ φ₂ : MapLift D.i A.module' A.module' (𝟙 ((modulePullback D.i).obj A.module'))) :
    ∃! δ : F ⟶ baseIdealTensor D F,
      infinitesimalHomEquiv D.i hi A.module' A.module'
            ((liftHomEquiv D A).symm δ ≫ (infinitesimalTensorIso D hs A.module' A.flat).hom) ≫
          infinitesimalι D.i A.module' + φ₁.1 = φ₂.1 := by
  obtain ⟨δ₀, hδ₀, huniq⟩ := mapLift_isPrincipalHomogeneous_tensor D hi hs A.module' A.module'
    A.flat (𝟙 ((modulePullback D.i).obj A.module'))
    ⟨⟨𝟙 A.module', (modulePullback D.i).map_id A.module'⟩⟩ φ₁ φ₂
  refine ⟨liftHomEquiv D A δ₀, ?_, fun δ hδ => ?_⟩
  · simpa only [Equiv.symm_apply_apply] using hδ₀
  · rw [← huniq ((liftHomEquiv D A).symm δ) hδ, Equiv.apply_symm_apply]

/-- The endomorphism `ε_δ : ℱ' ⟶ ℐℱ' ⟶ ℱ'` of a flat lift attached to
`δ : ℱ ⟶ f^* 𝒥 ⊗_{𝒪_X} ℱ` by **Stacks 08LJ**: the endomorphisms of `ℱ'` restricting to the
identity are exactly the `1 + ε_δ`. -/
noncomputable def liftInfinitesimalEndo (hi : IsFirstOrderThickening D.i) (hs : D.IsStrict)
    {F : SheafOfModules.{u} (structureSheafRing D.X)} (A : FlatLift D F)
    (δ : F ⟶ baseIdealTensor D F) : A.module' ⟶ A.module' :=
  infinitesimalHomEquiv D.i hi A.module' A.module'
      ((liftHomEquiv D A).symm δ ≫ (infinitesimalTensorIso D hs A.module' A.flat).hom) ≫
    infinitesimalι D.i A.module'

/-- **`ε_δ ε_{δ'} = 0`**: `ε_{δ'}` lands in the ideal multiple `ℐℱ'`, on which `ε_δ` vanishes. -/
theorem liftInfinitesimalEndo_comp (hi : IsFirstOrderThickening D.i) (hs : D.IsStrict)
    {F : SheafOfModules.{u} (structureSheafRing D.X)} (A : FlatLift D F)
    (δ δ' : F ⟶ baseIdealTensor D F) :
    liftInfinitesimalEndo D hi hs A δ' ≫ liftInfinitesimalEndo D hi hs A δ = 0 := by
  unfold liftInfinitesimalEndo
  rw [Category.assoc, ← Category.assoc (infinitesimalι D.i A.module'),
    infinitesimalι_comp_infinitesimalHomEquiv, zero_comp, comp_zero]

/-- `ε_δ` restricts to zero on `X`. -/
theorem modulePullback_map_liftInfinitesimalEndo (hi : IsFirstOrderThickening D.i)
    (hs : D.IsStrict) {F : SheafOfModules.{u} (structureSheafRing D.X)} (A : FlatLift D F)
    (δ : F ⟶ baseIdealTensor D F) :
    (modulePullback D.i).map (liftInfinitesimalEndo D hi hs A δ) = 0 :=
  modulePullback_map_comp_infinitesimalι D.i _

/-- **The automorphism `1 + ε_δ` of a flat lift**, with inverse `1 - ε_δ` since `ε_δ² = 0`. -/
noncomputable def identityLiftAut (hi : IsFirstOrderThickening D.i) (hs : D.IsStrict)
    {F : SheafOfModules.{u} (structureSheafRing D.X)} (A : FlatLift D F)
    (δ : F ⟶ baseIdealTensor D F) : A.module' ≅ A.module' where
  hom := 𝟙 A.module' + liftInfinitesimalEndo D hi hs A δ
  inv := 𝟙 A.module' - liftInfinitesimalEndo D hi hs A δ
  hom_inv_id := by
    rw [Preadditive.add_comp, Preadditive.comp_sub, Preadditive.comp_sub, Category.id_comp,
      Category.id_comp, Category.comp_id, liftInfinitesimalEndo_comp, sub_zero,
      sub_add_cancel]
  inv_hom_id := by
    rw [Preadditive.sub_comp, Preadditive.comp_add, Preadditive.comp_add, Category.id_comp,
      Category.id_comp, Category.comp_id, liftInfinitesimalEndo_comp, add_zero,
      add_sub_cancel_right]

/-- The automorphism `1 + ε_δ` restricts to the identity on `X`. -/
theorem modulePullback_map_identityLiftAut_hom (hi : IsFirstOrderThickening D.i)
    (hs : D.IsStrict) {F : SheafOfModules.{u} (structureSheafRing D.X)} (A : FlatLift D F)
    (δ : F ⟶ baseIdealTensor D F) :
    (modulePullback D.i).map (identityLiftAut D hi hs A δ).hom = 𝟙 _ := by
  have : (modulePullback D.i).Additive :=
    (modulePullbackPushforwardAdjunction D.i).left_adjoint_additive
  change (modulePullback D.i).map (𝟙 A.module' + liftInfinitesimalEndo D hi hs A δ) = 𝟙 _
  rw [Functor.map_add, modulePullback_map_liftInfinitesimalEndo, add_zero]
  exact (modulePullback D.i).map_id A.module'

/-- **Every endomorphism of a flat lift restricting to the identity is `1 + ε_δ`** for exactly
one `δ`. -/
theorem existsUnique_eq_one_add_liftInfinitesimalEndo (hi : IsFirstOrderThickening D.i)
    (hs : D.IsStrict) {F : SheafOfModules.{u} (structureSheafRing D.X)} (A : FlatLift D F)
    (φ : A.module' ⟶ A.module')
    (hφ : (modulePullback D.i).map φ = 𝟙 ((modulePullback D.i).obj A.module')) :
    ∃! δ : F ⟶ baseIdealTensor D F, φ = 𝟙 A.module' + liftInfinitesimalEndo D hi hs A δ := by
  obtain ⟨δ, hδ, huniq⟩ := existsUnique_identityLiftDifference D hi hs A
    ⟨𝟙 A.module', (modulePullback D.i).map_id A.module'⟩ ⟨φ, hφ⟩
  refine ⟨δ, ?_, fun δ' hδ' => huniq δ' ?_⟩
  · exact hδ.symm.trans (add_comm _ _)
  · exact (add_comm _ _).trans hδ'.symm

/-- **The automorphisms of a flat lift restricting to the identity are
`Hom_{𝒪_X}(ℱ, f^* 𝒥 ⊗_{𝒪_X} ℱ)`**, by `δ ↦ 1 + ε_δ`. -/
noncomputable def identityLiftAutEquiv (hi : IsFirstOrderThickening D.i) (hs : D.IsStrict)
    {F : SheafOfModules.{u} (structureSheafRing D.X)} (A : FlatLift D F) :
    { φ : A.module' ≅ A.module' //
        (modulePullback D.i).map φ.hom = 𝟙 ((modulePullback D.i).obj A.module') } ≃
      (F ⟶ baseIdealTensor D F) where
  toFun φ := (existsUnique_eq_one_add_liftInfinitesimalEndo D hi hs A φ.1.hom φ.2).exists.choose
  invFun δ := ⟨identityLiftAut D hi hs A δ, modulePullback_map_identityLiftAut_hom D hi hs A δ⟩
  left_inv φ := Subtype.ext (Iso.ext
    (existsUnique_eq_one_add_liftInfinitesimalEndo D hi hs A φ.1.hom φ.2).exists.choose_spec.symm)
  right_inv δ :=
    (existsUnique_eq_one_add_liftInfinitesimalEndo D hi hs A _
      (modulePullback_map_identityLiftAut_hom D hi hs A δ)).unique
      (existsUnique_eq_one_add_liftInfinitesimalEndo D hi hs A _
        (modulePullback_map_identityLiftAut_hom D hi hs A δ)).exists.choose_spec rfl

/-- The automorphism attached to `identityLiftAutEquiv φ` is `φ`. -/
theorem identityLiftAutEquiv_spec (hi : IsFirstOrderThickening D.i) (hs : D.IsStrict)
    {F : SheafOfModules.{u} (structureSheafRing D.X)} (A : FlatLift D F)
    (φ : { φ : A.module' ≅ A.module' //
      (modulePullback D.i).map φ.hom = 𝟙 ((modulePullback D.i).obj A.module') }) :
    φ.1.hom = 𝟙 A.module' + liftInfinitesimalEndo D hi hs A (identityLiftAutEquiv D hi hs A φ) :=
  (existsUnique_eq_one_add_liftInfinitesimalEndo D hi hs A φ.1.hom φ.2).exists.choose_spec

/-- **Stacks Project, Tag 08VR**, clause (3). Given a lift `ℱ'` of `ℱ` to an `𝒪_{X'}`-module
flat over `S'`, the set of automorphisms of `ℱ'` which pull back to the identity of `ℱ` is
canonically isomorphic to `Ext⁰_{𝒪_X}(ℱ, f^* 𝒥 ⊗_{𝒪_X} ℱ)`: the class `ξ` corresponds to the
automorphism `1 + ε_ξ`, where `ε_ξ` is `ξ ∈ Hom_{𝒪_X}(ℱ, f^* 𝒥 ⊗_{𝒪_X} ℱ)` read through
**Stacks 08LJ** as an endomorphism `ℱ' ⟶ ℐℱ' ⟶ ℱ'`. -/
@[stacks 08VR "clause (3)"]
theorem exists_identityLiftAut_equiv_ext_zero [CategoryTheory.HasExt.{w}
      (SheafOfModules.{u} (structureSheafRing D.X))]
    (hi : IsFirstOrderThickening D.i) (hs : D.IsStrict)
    {F : SheafOfModules.{u} (structureSheafRing D.X)} (A : FlatLift D F) :
    ∃ e : { φ : A.module' ≅ A.module' //
          (modulePullback D.i).map φ.hom = 𝟙 ((modulePullback D.i).obj A.module') } ≃
        CategoryTheory.Abelian.Ext.{w} F (baseIdealTensor D F) 0,
      ∀ φ, φ.1.hom = 𝟙 A.module' +
        liftInfinitesimalEndo D hi hs A (CategoryTheory.Abelian.Ext.homEquiv₀ (e φ)) :=
  ⟨(identityLiftAutEquiv D hi hs A).trans CategoryTheory.Abelian.Ext.homEquiv₀.symm, fun φ => by
    rw [Equiv.trans_apply, Equiv.apply_symm_apply]
    exact identityLiftAutEquiv_spec D hi hs A φ⟩

end AlgebraicGeometry.RingedSpaceThickening.FlatModuleDeformation

end
