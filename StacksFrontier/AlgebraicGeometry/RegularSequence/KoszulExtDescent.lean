module

public import StacksFrontier.AlgebraicGeometry.RegularSequence.KoszulExtComputation
public import StacksFrontier.AlgebraicGeometry.RegularSequence.KoszulQuotientDescent

/-!
# The Ext sheaves of a Koszul-regular quotient as modules over the quotient

Let `O♯` be a sheaf of commutative rings on a space, let `φ : (O♯)ʳ ⟶ O♯` be a morphism of sheaves
of modules with `𝓘` the sheaf of ideals it generates, and let `O_X = O♯/𝓘` be the quotient sheaf
of rings. For a Koszul complex resolving the quotient, the Ext sheaves

`Ext^m_{O♯}(O_X, O_X)`

are annihilated by `𝓘`, hence are restrictions of scalars of sheaves of `O_X`-modules. This file
produces those `O_X`-modules.

The annihilation is immediate from two facts already available: the Ext sheaf is the internal Hom
sheaf out of an exterior power of `(O♯)ʳ` into the quotient, and a homomorphism into a sheaf
annihilated by `𝓘` is annihilated by `𝓘`. Nothing has to be transported along the Ext
identification, because the descent is performed on the internal Hom sheaf and the identification
is then composed with the comparison it produces.

## Main statements

* `Stacks.RegularSequence.KoszulChainData.smul_internalHomSheafExteriorPower_eq_zero`: the sheaf
  of ideals annihilates the internal Hom sheaf out of an exterior power into the quotient.

## Main definitions

* `Stacks.RegularSequence.KoszulChainData.extDescended`: the Ext sheaf in degree `m`, as a sheaf
  of `O_X`-modules.
* `Stacks.RegularSequence.KoszulChainData.extDescendedIso`: the identification of its restriction
  of scalars with `Ext^m_{O♯}(O_X, O_X)`.

## Implementation notes

**The descent is performed on the internal Hom sheaf, not on the Ext sheaf.** Annihilation is a
statement about sections, so transporting it along an isomorphism of sheaves of modules would need
the isomorphism read on sections together with its linearity. That is avoidable: descend the
internal Hom sheaf, whose annihilation is direct, and compose the resulting comparison with the
Ext identification. Only isomorphisms are composed, and no annihilation is transported.

**Why the annihilation of the Hom sheaf is direct.** The action of a section on a section of an
internal Hom sheaf is postcomposition with multiplication on the target, definitionally — which is
what the characterising datum of Stacks 01CO for this sheaf makes visible. So the annihilation is
`Stacks.RegularSequence.smulHom_eq_zero_of_mem_idealOfHom` applied to the quotient, with no
hypothesis on the exterior power in the source: not freeness, not finite presentation.

**The types of the two definitions are left to be inferred,** for the reason recorded in
`StacksFrontier/CategoryTheory/Sites/Modules/QuotientRingSheafEpi.lean`: naming them would make the
elaborator compare a written copy of the quotient ring sheaf against the inferred one, and that
unfolds to a sheafification.

## References

* [Stacks Project, Tag 0BQY](https://stacks.math.columbia.edu/tag/0BQY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf Opposite TopologicalSpace
open AlgebraicGeometry

universe u

namespace Stacks.RegularSequence.KoszulChainData

open Stacks.Sites Stacks.SheafOfModules Stacks.RegularSequence

attribute [local instance] HasDerivedCategory.standard

variable {X : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} X)
  [HasSheafify (Opens.grothendieckTopology ↥X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology ↥X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify (Opens.grothendieckTopology ↥X) CommRingCat.{u}]
  {r : ℕ}
  {A : SheafOfModules.TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology ↥X)
    (koszulFreeSheaf Rc r)}
  {φ : koszulFreeSheaf Rc r ⟶
    SheafOfModules.unit (toRingCat (Opens.grothendieckTopology ↥X) Rc)}

omit [HasWeakSheafify (Opens.grothendieckTopology ↥X) CommRingCat.{u}] in
/-- **The sheaf of ideals annihilates the internal Hom sheaf out of an exterior power into the
quotient.** The action on a section of an internal Hom sheaf is postcomposition with
multiplication on the target, and the sheaf of ideals annihilates the quotient; no hypothesis on
the exterior power in the source is used.

**The scalar is ascribed to `Stacks.SheafOfModules.Tensor.ringSheaf Rc`.** The internal Hom sheaf
is a sheaf of modules over that sheaf of rings, which is where the module structure on its
sections — and so the action written `•` — lives. The sections of `Rc` itself are the same ring,
by `rfl`, but instance search does not cross the two spellings, so the action is found only at the
one the sheaf of modules is indexed by. The ascription names it and changes nothing else. -/
theorem smul_internalHomSheafExteriorPower_eq_zero (m : ℕ) (U : Opens ↥X)
    (a : Rc.obj.obj (op U)) (ha : a ∈ (idealOfHom φ).obj (op U))
    (β : (RingedSite.internalHomSheaf (ringedSite Rc) (A.exteriorPower m)
      (quotient Rc (φ := φ))).val.obj (op U)) :
    (show (Stacks.SheafOfModules.Tensor.ringSheaf Rc).obj.obj (op U) from a) • β = 0 :=
  smulHom_eq_zero_of_mem_idealOfHom φ (A.exteriorPower m) (quotient Rc (φ := φ))
    (smul_koszulQuotient_eq_zero_of_mem_idealOfHom φ) U a ha β

/-- **The Ext sheaves of a Koszul-regular quotient, as sheaves of modules over the quotient.**
The Ext sheaf in degree `m` is the internal Hom sheaf out of the `m`-th exterior power of `(O♯)ʳ`
into the quotient; that sheaf is annihilated by the sheaf of ideals, so it descends. Its type is
left to be inferred. -/
def extDescended (K : KoszulChainData.{u, u, u} A φ) [QuasiIso K.augmentation] (m : ℕ) :=
  descendedModule φ
    (RingedSite.internalHomSheaf (ringedSite Rc) (A.exteriorPower m) (quotient Rc (φ := φ)))
    (fun Y b hb β => smul_internalHomSheafExteriorPower_eq_zero Rc m Y.unop b hb β)

/-- **The descended sheaf is the Ext sheaf.** Restriction of scalars takes `extDescended` to the
internal Hom sheaf, which is `Ext^m_{O♯}(O_X, O_X)`:

`(Ext^m_{O♯}(O_X, O_X))` is the restriction of scalars of a sheaf of `O_X`-modules.

Only isomorphisms are composed here; no annihilation statement is transported. The type is left
to be inferred. -/
def extDescendedIso (K : KoszulChainData.{u, u, u} A φ) [QuasiIso K.augmentation] (m : ℕ) :=
  restrictScalars_descendedModule_iso φ
      (RingedSite.internalHomSheaf (ringedSite Rc) (A.exteriorPower m) (quotient Rc (φ := φ)))
      (fun Y b hb β => smul_internalHomSheafExteriorPower_eq_zero Rc m Y.unop b hb β) ≪≫
    (extIsoInternalHomExteriorPower Rc K m).symm

end Stacks.RegularSequence.KoszulChainData

end
