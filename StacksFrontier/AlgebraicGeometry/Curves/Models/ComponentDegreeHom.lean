module

public import StacksFrontier.AlgebraicGeometry.Curves.Models.DegreePairingSymmetry
public import StacksFrontier.AlgebraicGeometry.Picard.GaloisDescent.Pullback

/-!
# The degree on a component of the special fibre, as a homomorphism on `Pic(X)`

In the situation of [Stacks, Tag 0C61] the degree `deg(ℒ|_{Cᵢ})` of an invertible `𝒪_X`-module
restricted to an irreducible component `Cᵢ` of the special fibre depends only on the
isomorphism class of `ℒ`, and is additive in the tensor product by [Stacks, Tag 0AYX]. It is
therefore a homomorphism `Pic(X) ⟶ ℤ`.

## Main definitions

* `Stacks.Models.RegularProperModelSituation.specialFiberComponentDegreeHom` — the homomorphism
  `Pic(X) ⟶ ℤ`, `[ℒ] ↦ deg(ℒ|_{Cᵢ})`.

## Main results

* `Stacks.Models.RegularProperModelSituation.specialFiberComponentDegreeHom_picardClass` — its
  value on the class of `ℒ` is `deg(ℒ|_{Cᵢ})`.

## References

* [Stacks Project, Tag 0AYX](https://stacks.math.columbia.edu/tag/0AYX)
* [Stacks Project, Tag 0C61](https://stacks.math.columbia.edu/tag/0C61)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Models

namespace RegularProperModelSituation

variable (S : RegularProperModelSituation.{u}) (Z : irreducibleComponents S.specialFiber)

/-- The degree on `C_Z` of the chosen representative of a Picard class. -/
def specialFiberComponentDegreeOfClass (x : Stacks.Picard.ofScheme S.X) : ℤ :=
  S.specialFiberComponentDegree Z
    (Stacks.Picard.picardRepresentative S.X.toRingedSpace x).obj
    (Stacks.Picard.picardRepresentative S.X.toRingedSpace x).property

/-- The degree on `C_Z` of the representative of the class of `ℒ` is the degree of `ℒ`: the
two modules are isomorphic, and the degree is an isomorphism invariant. -/
theorem specialFiberComponentDegreeOfClass_picardClass (L : S.X.Modules)
    (hL : Stacks.SheafOfModules.IsInvertible S.X.presheaf
      (structureSheafRing S.X.toRingedSpace).property L) :
    S.specialFiberComponentDegreeOfClass Z
        (Stacks.SheafOfModules.picardClass S.X.presheaf
          (Stacks.RingedSpace.structureIsSheaf S.X.toRingedSpace) L hL) =
      S.specialFiberComponentDegree Z L hL := by
  have e := ((Stacks.SheafOfModules.picardClass_eq_iff _ _ _ _ _ _).1
    (Stacks.Picard.classOf_picardRepresentative S.X.toRingedSpace
      (Stacks.SheafOfModules.picardClass S.X.presheaf
        (Stacks.RingedSpace.structureIsSheaf S.X.toRingedSpace) L hL))).some
  exact componentDegree_eq_of_iso S.k _ _ _ _ _ L
    (Stacks.Picard.picardRepresentative S.X.toRingedSpace _).property hL e

/-- **The degree on a component of the special fibre, as a homomorphism `Pic(X) ⟶ ℤ`**:
`[ℒ] ↦ deg(ℒ|_{C_Z})`. It is well defined because the degree is an isomorphism invariant, and
additive because the degree is additive in the tensor product (Tag 0AYX),
`Stacks.Models.componentDegreeAdditive`. -/
def specialFiberComponentDegreeHom : Stacks.Picard.ofScheme S.X →+ ℤ :=
  AddMonoidHom.mk' (S.specialFiberComponentDegreeOfClass Z) fun x y => by
    set Lx := Stacks.Picard.picardRepresentative S.X.toRingedSpace x
    set Ly := Stacks.Picard.picardRepresentative S.X.toRingedSpace y
    have hLxy : Stacks.SheafOfModules.IsInvertible S.X.presheaf
        (Stacks.RingedSpace.structureIsSheaf S.X.toRingedSpace)
        (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨S.X.presheaf,
          Presheaf.isSheaf_of_isSheaf_comp _ S.X.presheaf (forget₂ CommRingCat RingCat)
            (Stacks.RingedSpace.structureIsSheaf S.X.toRingedSpace)⟩).obj Lx.obj).obj Ly.obj) :=
      @Stacks.SheafOfModules.isInvertible_tensorSheaf _ _ _ _ _ _ _ _ _ Lx.property Ly.property
    have hsum : x + y = Stacks.SheafOfModules.picardClass S.X.presheaf
        (Stacks.RingedSpace.structureIsSheaf S.X.toRingedSpace) _ hLxy := by
      conv_lhs => rw [← Stacks.Picard.classOf_picardRepresentative S.X.toRingedSpace x,
        ← Stacks.Picard.classOf_picardRepresentative S.X.toRingedSpace y]
      exact Stacks.SheafOfModules.picardClass_tensorSheaf _ _ _ _ _ _ hLxy
    rw [hsum]
    refine (S.specialFiberComponentDegreeOfClass_picardClass Z _ hLxy).trans ?_
    exact componentDegreeAdditive S (fun W => S.specialFiberComponentIdeal W)
      (fun W => S.specialFiberComponentToSpec W) (fun W => S.isProper_specialFiberComponentToSpec W)
      (fun W => S.toRegularModelSituation.topologicalKrullDim_specialFiberComponent W) Z Lx.obj
      Ly.obj Lx.property Ly.property hLxy

/-- The degree homomorphism on the class of `ℒ` is `deg(ℒ|_{C_Z})`. -/
@[simp] theorem specialFiberComponentDegreeHom_picardClass (L : S.X.Modules)
    (hL : Stacks.SheafOfModules.IsInvertible S.X.presheaf
      (structureSheafRing S.X.toRingedSpace).property L) :
    S.specialFiberComponentDegreeHom Z
        (Stacks.SheafOfModules.picardClass S.X.presheaf
          (Stacks.RingedSpace.structureIsSheaf S.X.toRingedSpace) L hL) =
      S.specialFiberComponentDegree Z L hL :=
  S.specialFiberComponentDegreeOfClass_picardClass Z L hL

end RegularProperModelSituation

end Stacks.Models

end
