module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InverseImageUnitSection
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackUnitValue
public import StacksFrontier.Deformation.AlgebraExtension.InducedKernelMap
public import StacksFrontier.Deformation.ToposThickening.AlgebraExtensionBaseProblem

/-!
# Global sections of the kernel of an algebra extension, on sheaves of sets

For an extension `0 → ℳ → 𝒪' → 𝒪 → 0` of algebras (`Deformation.AlgebraExtension`), a global
section `w : 𝒪 ⟶ ℳ` of the kernel module is read on underlying sheaves of sets as the unit
section followed by `w` and the inclusion `ℳ ⊆ 𝒪'`: a global section `⊤ ⟶ 𝒪'` of the middle
term. This reading determines `w`, the inclusion being injective, and a homomorphism of middle
terms over `𝒪` acts on it through the map of kernels it induces.

## Main results

* `Deformation.AlgebraExtension.eq_of_ringOneHom_comp_map_comp_inclSheafSets_eq`: a global
  section of the kernel is determined by its image in the middle term.
* `Deformation.AlgebraExtension.ringOneHom_comp_map_inducedKernelMap_comp_inclSheafSets`: a
  homomorphism of middle terms acts on these images through the induced map of kernels.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf

universe u v w

namespace Deformation.AlgebraExtension

variable {C : Type v} [Category.{w} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [J.HasSheafCompose (forget RingCat.{u})] [J.HasSheafCompose (forget AddCommGrpCat.{u})]
  {A A' O : Sheaf J CommRingCat.{u}} {a : A ⟶ O} {a' : A' ⟶ O}
  {M N : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj O)}

/-- **A global section of the kernel is determined by its image in the middle term**, read on
underlying sheaves of sets: the unit section followed by `w` and `ℳ ⊆ 𝒪'`. -/
theorem eq_of_ringOneHom_comp_map_comp_inclSheafSets_eq (P : AlgebraExtension a M)
    {w w' : SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj O) ⟶
      M}
    (h : ringOneHom ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj O) ≫
        (moduleSheafFunctor ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj O)).map
          w ≫ P.inclSheafSets =
      ringOneHom ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj O) ≫
        (moduleSheafFunctor ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj O)).map
          w' ≫ P.inclSheafSets) :
    w = w' :=
  hom_ext_ringOneHom (hom_ext_sections fun U p ↦ P.incl_injective (sectionsFunctor_map_congr h U p))

/-- **A homomorphism of middle terms acts on global sections of the kernel through the induced
map of kernels**: for `h : 𝒪'_P ⟶ 𝒪'_Q` over `𝒪` and a global section `w` of `ℳ`, the image in
`𝒪'_Q` of `w` followed by the induced map `ℳ ⟶ 𝒩` is the image under `h` of the image of `w` in
`𝒪'_P`, on underlying sheaves of sets. -/
theorem ringOneHom_comp_map_inducedKernelMap_comp_inclSheafSets (P : AlgebraExtension a M)
    (Q : AlgebraExtension a' N) (h : P.extension ⟶ Q.extension)
    (hh : h ≫ Q.reduction = P.reduction)
    (w : SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj O) ⟶
      M) :
    ringOneHom ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj O) ≫
        (moduleSheafFunctor ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj O)).map
          (w ≫ inducedKernelMap P Q h hh) ≫ Q.inclSheafSets =
      ringOneHom ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj O) ≫
        (moduleSheafFunctor ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj O)).map
          w ≫ P.inclSheafSets ≫ (sheafCompose J (forget RingCat.{u})).map
            ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map h) :=
  hom_ext_sections fun _ _ ↦ (hom_incl P Q h hh _).symm

end Deformation.AlgebraExtension

end
