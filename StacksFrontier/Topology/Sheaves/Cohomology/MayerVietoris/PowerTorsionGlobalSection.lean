module

public import StacksFrontier.Topology.Sheaves.Cohomology.MayerVietoris.PowerTorsionRestriction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GlobalSectionSmul

/-!
# Power-torsion morphism groups and a section over the whole space

`Stacks.ExtensionByZero.homPowerTorsion_of_restrictions` is the Mayer--Vietoris step of
[Stacks, Tag 08EJ] with its scalar an element of
`Stacks.Cohomology.SiteModules.GlobalSectionRing O` — a compatible family of sections over all
the opens — and its three hypotheses read at the restricted families
`Stacks.ExtensionByZero.restrictGlobalSection`. This file shows that the family of a section
`f ∈ Γ(X, 𝒪_X)` restricts to the family of the restricted section `f|_U ∈ Γ(U, 𝒪_U)`, and states
the Mayer--Vietoris step with every scalar a section over the whole space.

## Main definitions

* `ExtensionByZeroModules.imF_obj_top`: the image of the top open of `U` is `U`.
* `Stacks.ExtensionByZero.globalScalar` and `Stacks.ExtensionByZero.globalScalarHom`: a section
  over the whole space, read as a global scalar, and the ring homomorphism it defines.
* `Stacks.ExtensionByZero.restrictGlobalTop`: restriction of a section over the whole space to a
  section of `𝒪_U` over the top open of `U`.

## Main results

* `Stacks.ExtensionByZero.restrictGlobalSection_globalScalar`: the restriction to `U` of the
  global scalar of `f` is the global scalar of `f|_U`.
* `Stacks.ExtensionByZero.restrictGlobalTop_eq`: the restriction of `f` to the top open of `U` is
  the restriction map `Γ(X, 𝒪_X) ⟶ Γ(U, 𝒪_U)`.
* `Stacks.ExtensionByZero.homPowerTorsion_of_restrictions_of_section`: the Mayer--Vietoris step
  of [Stacks, Tag 08EJ] with every scalar a section over the whole space of the ambient or of
  the restricted sheaf.

## References

* [Stacks Project, Tag 08EJ](https://stacks.math.columbia.edu/tag/08EJ)
* [Stacks Project, Tag 08BW](https://stacks.math.columbia.edu/tag/08BW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.Cohomology.SiteModules
open ExtensionByZeroModules
open scoped IsMulCommutative

universe u

namespace ExtensionByZeroModules

/-- The image in `X` of the top open of the open subspace `U` is `U`. -/
public theorem imF_obj_top {X : TopCat.{u}} (U : Opens X) :
    (TopCat.Presheaf.imF U).obj ⊤ = U :=
  U.isOpenEmbedding_obj_top

end ExtensionByZeroModules

namespace Stacks.ExtensionByZero

open Stacks.Koszul.PowerLift

attribute [local implicit_reducible] CategoryTheory.Functor.sheafPushforwardContinuous
attribute [local instance] HasDerivedCategory.standard

variable {X : TopCat.{u}} (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
  [∀ Y : (Opens X)ᵒᵖ, IsMulCommutative (O.obj.obj Y)]

/-- A section over the whole space, as a global scalar: the compatible family of its restrictions
to all the opens. -/
public def globalScalar (f : O.obj.obj (op (⊤ : Opens X))) : GlobalSectionRing O :=
  ⟨(Stacks.SheafOfModules.terminalSection O ⊤ isTerminalTop f).val,
    (Stacks.SheafOfModules.terminalSection O ⊤ isTerminalTop f).property⟩

omit [∀ Y : (Opens X)ᵒᵖ, IsMulCommutative (O.obj.obj Y)] in
/-- The component of `Stacks.ExtensionByZero.globalScalar O f` over an open `W` is the
restriction of `f` to `W`. -/
@[simp]
public theorem globalScalar_val (f : O.obj.obj (op (⊤ : Opens X))) (W : (Opens X)ᵒᵖ) :
    (globalScalar O f).val W = O.obj.map (isTerminalTop.from W.unop).op f := rfl

/-- `Stacks.ExtensionByZero.globalScalar` as a ring homomorphism. -/
public def globalScalarHom : O.obj.obj (op (⊤ : Opens X)) →+* GlobalSectionRing O where
  toFun := globalScalar O
  map_one' := by ext W; exact map_one _
  map_mul' _ _ := by ext W; exact map_mul _ _ _
  map_zero' := by ext W; exact map_zero _
  map_add' _ _ := by ext W; exact map_add _ _ _

/-- The ring homomorphism `Stacks.ExtensionByZero.globalScalarHom O` sends `f` to
`Stacks.ExtensionByZero.globalScalar O f`. -/
@[simp]
public theorem globalScalarHom_apply (f : O.obj.obj (op (⊤ : Opens X))) :
    globalScalarHom O f = globalScalar O f := rfl

/-- The global scalar of `f ^ k` is the `k`-th power of the global scalar of `f`. -/
@[simp]
public theorem globalScalar_pow (f : O.obj.obj (op (⊤ : Opens X))) (k : ℕ) :
    globalScalar O (f ^ k) = globalScalar O f ^ k :=
  map_pow (globalScalarHom O) f k

variable (U : Opens X)

/-- The restriction of a section over the whole space to the open subspace `U`, as a section of
`𝒪_U` over the top open of `U`, which is `Γ(U, 𝒪_U)` by `ExtensionByZeroModules.imF_obj_top`. -/
public def restrictGlobalTop (f : O.obj.obj (op (⊤ : Opens X))) :
    (resRing U O).obj.obj (op (⊤ : Opens (Usp U))) :=
  O.obj.map (homOfLE (le_top (a := (TopCat.Presheaf.imF U).obj ⊤))).op f

omit [∀ Y : (Opens X)ᵒᵖ, IsMulCommutative (O.obj.obj Y)] in
/-- The restriction to `U` of the global scalar of a section `f` over the whole space is the global
scalar of the restriction of `f` to `U`. -/
public theorem restrictGlobalSection_globalScalar (f : O.obj.obj (op (⊤ : Opens X))) :
    restrictGlobalSection U O (globalScalar O f) =
      globalScalar (resRing U O) (restrictGlobalTop O U f) := by
  ext W
  change (O.obj.map (isTerminalTop.from ((TopCat.Presheaf.imF U).obj W.unop)).op) f =
    (O.obj.map ((TopCat.Presheaf.imF U).map (isTerminalTop.from W.unop)).op)
      ((O.obj.map (homOfLE (le_top (a := (TopCat.Presheaf.imF U).obj ⊤))).op) f)
  rw [← RingCat.comp_apply, ← Functor.map_comp, ← op_comp]
  congr 3

omit [∀ Y : (Opens X)ᵒᵖ, IsMulCommutative (O.obj.obj Y)] in
/-- `Stacks.ExtensionByZero.restrictGlobalTop` is the restriction map `Γ(X, 𝒪_X) ⟶ Γ(U, 𝒪_U)`,
read across the identification of the image of the top open of `U` with `U`. -/
public theorem restrictGlobalTop_eq (f : O.obj.obj (op (⊤ : Opens X))) :
    restrictGlobalTop O U f =
      O.obj.map (eqToHom (congrArg op (imF_obj_top U).symm))
        ((O.obj.map (homOfLE (le_top (a := U))).op) f) := by
  rw [← RingCat.comp_apply, ← Functor.map_comp]
  congr 2

/-- Let `X` be a topological space covered by two opens `U` and `V`, let `O` be a sheaf of
commutative rings on `X`, let `f` be a section of `O` over `X` and let `E` and `F` be objects of
`D(𝒪_X)`. If on each of `U`, `V` and `U ∩ V` every morphism from each shift of the restriction
of `E` into the restriction of `F` is annihilated by a power of the restriction of `f`, then
every morphism `E⟦n⟧ ⟶ F` is annihilated by a power of `f`. The scalars are the global scalars
`Stacks.ExtensionByZero.globalScalar` of `f` and of its restrictions. -/
public theorem homPowerTorsion_of_restrictions_of_section
    (f : O.obj.obj (op (⊤ : Opens X))) (U V : Opens X) (hUV : U ⊔ V = ⊤)
    (E F : DerivedCategory (SheafOfModules.{u} O))
    (hU : ∀ n : ℤ, HomPowerTorsion (globalScalar (resRing U O) (restrictGlobalTop O U f))
      (((derivedRestriction O U).obj E)⟦n⟧) ((derivedRestriction O U).obj F))
    (hV : ∀ n : ℤ, HomPowerTorsion (globalScalar (resRing V O) (restrictGlobalTop O V f))
      (((derivedRestriction O V).obj E)⟦n⟧) ((derivedRestriction O V).obj F))
    (hUV' : ∀ n : ℤ,
      HomPowerTorsion (globalScalar (resRing (U ⊓ V) O) (restrictGlobalTop O (U ⊓ V) f))
      (((derivedRestriction O (U ⊓ V)).obj E)⟦n⟧) ((derivedRestriction O (U ⊓ V)).obj F))
    (n : ℤ) : HomPowerTorsion (globalScalar O f) (E⟦n⟧) F :=
  homPowerTorsion_of_restrictions O (globalScalar O f) U V hUV E F
    (fun m => (restrictGlobalSection_globalScalar O U f) ▸ hU m)
    (fun m => (restrictGlobalSection_globalScalar O V f) ▸ hV m)
    (fun m => (restrictGlobalSection_globalScalar O (U ⊓ V) f) ▸ hUV' m) n

end Stacks.ExtensionByZero

end
