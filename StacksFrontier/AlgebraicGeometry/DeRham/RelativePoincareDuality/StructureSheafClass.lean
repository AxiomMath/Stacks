module

public import StacksFrontier.AlgebraicGeometry.DeRham.RelativePoincareDuality.WedgeDegreeZero
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormulaUnitKFlat
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Global functions as classes in `Hom(𝒪_S, Rf_*Ω^0_{X/S})`

Let `f : X ⟶ S` be a morphism of schemes. Every map `𝒪_S ⟶ Rf_*Ω^0_{X/S}` in `D(𝒪_S)` is the
class of a unique global function `g ∈ Γ(X, 𝒪_X)`:

`Γ(X, 𝒪_X) ≅ Hom_{D(𝒪_S)}(𝒪_S, Rf_*Ω^0_{X/S})`, `g ↦ (𝒪_S ⟶ Rf_*Lf^*𝒪_S ≅ Rf_*Ω^0 ⟶ Rf_*Ω^0)`,

the last map being `Rf_*` of multiplication by `g`. This is the identification
`Γ(S, f_*𝒪_X) = Γ(X, 𝒪_X)` with which the proof of [Stacks, Tag 0G8I] reads a map out of
`R^nf_*Ω^n_{X/S}` as a global function.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.globalFunctionClass`: the class of a global function.

## Main results

* `Stacks.Cohomology.InvertibleDerived.bijective_smulHom_unit`: `Γ(X, 𝒪_X) ≅ End(𝒪_X)` on a ringed
  space.
* `AlgebraicGeometry.Scheme.Hom.bijective_globalFunctionClass`: the bijection above.

## References

* [Stacks Project, Tag 0G8I](https://stacks.math.columbia.edu/tag/0G8I)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry

universe u
namespace Stacks.Cohomology.InvertibleDerived

variable {X : RingedSpace.{u, u}}

/-- Multiplication by a global section `s` takes the global section `1` of `𝒪_X` to `s`. -/
theorem smulHom_unit_val_app_top_one (s : X.presheaf.obj (op ⊤)) :
    (smulHom s (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf))).val.app
      (op ⊤) (1 : (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf).obj.obj (op ⊤)) = s :=
  show (globalRes s ⊤ : (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf).obj.obj (op ⊤)) * 1 = s
    from (mul_one _).trans (globalRes_top s)

/-- **Every endomorphism of `𝒪_X` is multiplication by a global section**, namely by the image
of `1`: a morphism out of `𝒪_X` is determined by the image of the global section `1`. -/
theorem eq_smulHom_unit
    (φ : SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf) ⟶
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)) :
    φ = smulHom (φ.val.app (op ⊤)
      (1 : (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf).obj.obj (op ⊤))) _ := by
  refine (SheafOfModules.unitHomEquiv _).injective (Subtype.ext (funext fun U => ?_))
  have := PresheafOfModules.naturality_apply φ.val (homOfLE (le_top : U.unop ≤ ⊤)).op
    (1 : (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf).obj.obj (op ⊤))
  change φ.val.app U (1 : (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf).obj.obj U) =
    (globalRes (φ.val.app (op ⊤)
      (1 : (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf).obj.obj (op ⊤)))
      U.unop : (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf).obj.obj U) * 1
  refine Eq.trans ?_ (mul_one (globalRes (φ.val.app (op ⊤)
    (1 : (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf).obj.obj (op ⊤))) U.unop)).symm
  refine Eq.trans ?_ this
  exact congrArg (φ.val.app U)
    (map_one ((Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf).obj.map
      (homOfLE (le_top : U.unop ≤ ⊤)).op).hom).symm

/-- **`Γ(X, 𝒪_X) ≅ End(𝒪_X)`**: multiplication by global sections is a bijection from
`Γ(X, 𝒪_X)` onto the endomorphisms of the `𝒪_X`-module `𝒪_X`. -/
@[ega "0 5.4.3" "Base case L = O_X"]
theorem bijective_smulHom_unit :
    Function.Bijective (fun s : X.presheaf.obj (op ⊤) =>
      smulHom s (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf))) :=
  ⟨fun s t h => (smulHom_unit_val_app_top_one s).symm.trans
      ((congrArg (fun φ : SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf) ⟶
        SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf) => φ.val.app (op ⊤)
          (1 : (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf).obj.obj (op ⊤))) h).trans
        (smulHom_unit_val_app_top_one t)),
    fun φ => ⟨_, (eq_smulHom_unit φ).symm⟩⟩

/-- For an `𝒪_X`-module `F` isomorphic to `𝒪_X`, multiplication by global sections is a bijection
from `Γ(X, 𝒪_X)` onto the endomorphisms of `F`: multiplication commutes with the isomorphism. -/
theorem bijective_smulHom_of_iso
    {F : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)}
    (e : F ≅ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)) :
    Function.Bijective (fun s : X.presheaf.obj (op ⊤) => smulHom s F) := by
  have h : (fun s : X.presheaf.obj (op ⊤) => smulHom s F) =
      (e.symm.homCongr e.symm) ∘ (fun s : X.presheaf.obj (op ⊤) =>
        smulHom s (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf))) :=
    funext fun s => by
      simp only [Function.comp_apply, Iso.homCongr_apply, Iso.symm_inv, Iso.symm_hom]
      rw [smulHom_naturality_assoc, e.hom_inv_id, Category.comp_id]
  rw [h]
  exact (Equiv.bijective _).comp bijective_smulHom_unit

end Stacks.Cohomology.InvertibleDerived

open scoped Stacks.StandardDerivedModel Stacks.Topology.SheafTensorAdditiveOnOpens
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

namespace AlgebraicGeometry.Scheme.Hom
variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- The isomorphism `Lf^*𝒪_S ≅ 𝒪_X ≅ Ω^0_{X/S}` in `D(𝒪_X)`: the unit comparison of the derived
pullback followed by the identification of forms of degree zero with the structure sheaf. -/
def formsZeroUnitComparison :
    (derivedPullback f.toLRSHom.toShHom).obj
        (Stacks.Cohomology.DerivedProjectionFormula.singleUnit S.toRingedSpace) ≅
      formsInDegreeZero f 0 :=
  Stacks.Cohomology.DerivedProjectionFormula.derivedPullbackUnitIso f.toLRSHom.toShHom ≪≫
    DerivedCategory.Q.mapIso ((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 0).mapIso
      (formsZeroIsoUnit f).symm)

/-- **The class in `Hom(𝒪_S, Rf_*Ω^0_{X/S})` of a global function** `g ∈ Γ(X, 𝒪_X)`: the map
`𝒪_S ⟶ Rf_*Ω^0_{X/S}` adjoint to `Lf^*𝒪_S ≅ Ω^0_{X/S}` followed by multiplication by `g`. -/
def globalFunctionClass (g : Γ(X, ⊤)) :
    Stacks.Cohomology.DerivedProjectionFormula.singleUnit S.toRingedSpace ⟶
      (derivedPushforward f.toLRSHom.toShHom).obj (formsInDegreeZero f 0) :=
  (derivedAdjunction f.toLRSHom.toShHom).homEquiv _ _
    ((formsZeroUnitComparison f).hom ≫ f.formsInDegreeZeroSMul g 0)

/-- **`Γ(X, 𝒪_X) ≅ Hom_{D(𝒪_S)}(𝒪_S, Rf_*Ω^0_{X/S})`**: every map `𝒪_S ⟶ Rf_*Ω^0_{X/S}` is the
class of a unique global function. Under `Lf^* ⊣ Rf_*` and `Lf^*𝒪_S ≅ Ω^0_{X/S} ≅ 𝒪_X` such maps
are the endomorphisms of `𝒪_X` in degree zero of `D(𝒪_X)`, which are those of the module `𝒪_X`
(the single-degree embedding is fully faithful), that is, multiplications by global functions. -/
theorem bijective_globalFunctionClass : Function.Bijective (globalFunctionClass f) := by
  have h1 := Stacks.Cohomology.InvertibleDerived.bijective_smulHom_of_iso (X := X.toRingedSpace)
    (formsZeroIsoUnit f)
  have h2 : Function.Bijective
      (fun φ : relativeDifferentialForms f 0 ⟶ relativeDifferentialForms f 0 =>
      DerivedCategory.Q.map ((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 0).map φ)) :=
    ⟨(DerivedCategory.singleFunctor X.Modules 0).map_injective,
      (DerivedCategory.singleFunctor X.Modules 0).map_surjective⟩
  have h3 : Function.Bijective (fun ψ : formsInDegreeZero f 0 ⟶ formsInDegreeZero f 0 =>
      (formsZeroUnitComparison f).hom ≫ ψ) :=
    (formsZeroUnitComparison f).symm.homFromEquiv.bijective
  exact ((derivedAdjunction f.toLRSHom.toShHom).homEquiv _ _).bijective.comp (h3.comp (h2.comp h1))


/-- The class `𝒪_S ⟶ Rf_*Ω^0_{X/S}` of the unit: the map adjoint to `Lf^*𝒪_S ≅ Ω^0_{X/S}`. -/
def structureSheafClass :
    Stacks.Cohomology.DerivedProjectionFormula.singleUnit S.toRingedSpace ⟶
      (derivedPushforward f.toLRSHom.toShHom).obj (formsInDegreeZero f 0) :=
  (derivedAdjunction f.toLRSHom.toShHom).homEquiv _ _ (formsZeroUnitComparison f).hom

/-- The class of `g` is the class of the unit followed by `Rf_*` of multiplication by `g`. -/
theorem globalFunctionClass_eq (g : Γ(X, ⊤)) :
    globalFunctionClass f g = structureSheafClass f ≫
      (Stacks.Duality.derivedPushforward f).map (f.formsInDegreeZeroSMul g 0) :=
  (derivedAdjunction f.toLRSHom.toShHom).homEquiv_naturality_right _ _

end AlgebraicGeometry.Scheme.Hom

end
