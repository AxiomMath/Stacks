module

public import Mathlib.CategoryTheory.Limits.Final
public import Mathlib.CategoryTheory.Sites.GlobalSections
public import Mathlib.CategoryTheory.Sites.Pullback
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Lower shriek takes the constant sheaf to the constant sheaf, with no terminal object

Let `u : C ⥤ D` be a continuous functor of sites whose restriction functor
`g⁻¹ = u.sheafPushforwardContinuous` admits a left adjoint `g_!`.  Assume that `u` is **final**:
for every object `X` of `D` the comma category `I^u_X` of pairs `(U, u(U) ⟶ X)` is nonempty and
connected.  Then

`g_! M_C ≅ M_D`

for every object `M` of the coefficient category, naturally in `M`.

No terminal object of either site is required, and the restriction functor is not assumed to be
an equivalence.  Finality of `u` is exactly the hypothesis the classical proof uses: global
sections of a sheaf are the limit of the underlying presheaf over the opposite site
(`CategoryTheory.Sheaf.isLimitConeΓ`), `uᵒᵖ` is initial as soon as `u` is final, and restricting
a limit cone along an initial functor is again a limit cone.

## Main results

* `Stacks.ConstantSheaf.gammaCompRestrictionIsoOfFinal` — **restriction along a final continuous
  functor does not change global sections**: `g⁻¹ ⋙ Γ(C, -) ≅ Γ(D, -)`.
* `Stacks.ConstantSheaf.constantSheafCompSheafPullbackIsoOfFinal` — **lower shriek takes the
  constant sheaf to the constant sheaf**: `C_C ⋙ g_! ≅ C_D`.

## What is and is not proved

No tag attribute is placed in this file.  The isomorphism `g_! ℤ_C ≅ ℤ_D` is the degree-zero
content of a cohomology comparison rather than a tagged statement of its own, and the two
statements below are the terminal-object-free replacements for
`Stacks.Cohomology.BiggerSiteGlobal.gammaCompRestrictionIso` and
`Stacks.Cohomology.BiggerSiteGlobal.lowerShriekConstantSheafIso`, which carry none either.

What is proved is only the comparison in degree zero.  Nothing here says that the *derived*
lower shriek of the constant sheaf is the constant sheaf, nor that `g_!` is exact.

## References

* [Stacks Project, Tag 00XO](https://stacks.math.columbia.edu/tag/00XO)
* [Stacks Project, Tag 0H0Z](https://stacks.math.columbia.edu/tag/0H0Z)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.ConstantSheaf

universe v₄ u₄ v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  (u : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  (A : Type u₄) [Category.{v₄} A] [u.IsContinuous J K]
  [HasWeakSheafify J A] [HasWeakSheafify K A]
  [HasGlobalSectionsFunctor J A] [HasGlobalSectionsFunctor K A] [u.Final]

/-- **The global sections of a sheaf on `(D, K)`, seen as a cone over the restricted presheaf
`uᵒᵖ ⋙ F`.**  Its components are the restriction maps `Γ(D, F) ⟶ F(u(U))`. -/
@[reducible, simps]
def coneΓRestrict (F : Sheaf K A) : Cone (u.op ⋙ F.obj) where
  pt := (Sheaf.Γ K A).obj F
  π :=
    { app := fun X => F.ΓRes (u.op.obj X)
      naturality := fun X Y g => by simp }

/-- **The global sections cone restricted along `uᵒᵖ` is still a limit cone.**  The global
sections of a sheaf `F` on `(D, K)` are the limit of the underlying presheaf over `Dᵒᵖ`, by
`CategoryTheory.Sheaf.isLimitConeΓ`; finality of `u` makes `uᵒᵖ : Cᵒᵖ ⥤ Dᵒᵖ` initial, and
restricting a limit cone along an initial functor is again limiting. -/
@[sga "4 V 8.1.5" "special case"]
def isLimitConeΓRestrict (F : Sheaf K A) : IsLimit (coneΓRestrict u K A F) :=
  IsLimit.ofIsoLimit ((Functor.Initial.isLimitWhiskerEquiv u.op F.coneΓ).symm F.isLimitConeΓ)
    (Cone.ext (Iso.refl _) fun _ => (Category.id_comp _).symm)

/-- **Restriction along a final continuous functor does not change global sections**, one sheaf
at a time: `Γ(C, g⁻¹ F) ≅ Γ(D, F)`.  Both sides are the limit of `uᵒᵖ ⋙ F`, the left because the
underlying presheaf of `g⁻¹ F` *is* `F ∘ uᵒᵖ`, the right by `isLimitConeΓRestrict`. -/
def gammaRestrictionIsoApp (F : Sheaf K A) :
    (Sheaf.Γ J A).obj ((u.sheafPushforwardContinuous A J K).obj F) ≅ (Sheaf.Γ K A).obj F :=
  IsLimit.conePointUniqueUpToIso
    ((u.sheafPushforwardContinuous A J K).obj F).isLimitConeΓ (isLimitConeΓRestrict u K A F)

/-- The isomorphism `gammaRestrictionIsoApp` followed by the restriction map
`Γ(D, F) ⟶ F(u(X))` is the restriction map `Γ(C, g⁻¹ F) ⟶ (g⁻¹ F)(X)`. -/
@[reassoc]
lemma gammaRestrictionIsoApp_hom_comp (F : Sheaf K A) (X : Cᵒᵖ) :
    (gammaRestrictionIsoApp u J K A F).hom ≫ F.ΓRes (u.op.obj X) =
      ((u.sheafPushforwardContinuous A J K).obj F).ΓRes X :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ _ X

/-- **Restriction along a final continuous functor does not change global sections**:

`g⁻¹ ⋙ Γ(C, -) ≅ Γ(D, -)`,

naturally in the sheaf on `(D, K)`.  This is
`Stacks.Cohomology.BiggerSiteGlobal.gammaCompRestrictionIso` with the two terminal objects
replaced by finality of `u`. -/
def gammaCompRestrictionIsoOfFinal :
    u.sheafPushforwardContinuous A J K ⋙ Sheaf.Γ J A ≅ Sheaf.Γ K A :=
  NatIso.ofComponents (gammaRestrictionIsoApp u J K A) (by
    intro F G f
    refine (isLimitConeΓRestrict u K A G).hom_ext fun X => ?_
    simp only [Category.assoc]
    rw [Sheaf.ΓRes_naturality f (u.op.obj X), gammaRestrictionIsoApp_hom_comp,
      ← Category.assoc, gammaRestrictionIsoApp_hom_comp]
    exact Sheaf.ΓRes_naturality ((u.sheafPushforwardContinuous A J K).map f) X)

variable [(u.sheafPushforwardContinuous A J K).IsRightAdjoint]

/-- **Lower shriek takes the constant sheaf to the constant sheaf, with no terminal object.**
For a continuous and final functor of sites `u : C ⥤ D` whose restriction functor `g⁻¹` on
`A`-valued sheaves has a left adjoint `g_!`,

`C_C ⋙ g_! ≅ C_D`,

naturally in the coefficient object.  In particular `g_! ℤ_C ≅ ℤ_D` for `A` the category of
abelian groups.

Both functors are left adjoint to `Γ(D, -)`: the first because its right adjoint is
`g⁻¹ ⋙ Γ(C, -)`, which `gammaCompRestrictionIsoOfFinal` identifies with `Γ(D, -)`, and the second
because `Γ` is *defined* as the right adjoint of the constant sheaf functor.

This is `Stacks.Cohomology.BiggerSiteGlobal.lowerShriekConstantSheafIso` and
`Stacks.ConstantSheaf.constantSheafCompSheafPullbackIso` with their terminal objects replaced by
finality of `u`: nonemptiness and connectedness of the comma categories `I^u_X` of pairs
`(U, u(U) ⟶ X)`.  Neither site need have a terminal object, and `g⁻¹` need not be an
equivalence. -/
def constantSheafCompSheafPullbackIsoOfFinal :
    constantSheaf J A ⋙ u.sheafPullback A J K ≅ constantSheaf K A :=
  Adjunction.leftAdjointUniq
    (Adjunction.ofNatIsoRight
      ((constantSheafΓAdj J A).comp (u.sheafAdjunctionContinuous A J K))
      (gammaCompRestrictionIsoOfFinal u J K A))
    (constantSheafΓAdj K A)

/-- **`g_! M_C ≅ M_D`**, the comparison of `constantSheafCompSheafPullbackIsoOfFinal` at a single
coefficient object `M`.  This is the datum `e` of
`Stacks.Cohomology.BiggerSiteGlobal.sheafCohomologyIsoOfConstantSheafIsoOfAcyclic`. -/
def sheafPullbackConstantSheafIsoOfFinal (M : A) :
    (u.sheafPullback A J K).obj ((constantSheaf J A).obj M) ≅ (constantSheaf K A).obj M :=
  (constantSheafCompSheafPullbackIsoOfFinal u J K A).app M

end Stacks.ConstantSheaf

end
