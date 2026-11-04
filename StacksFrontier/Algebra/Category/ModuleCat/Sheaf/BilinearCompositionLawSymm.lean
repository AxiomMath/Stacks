module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.BilinearCompositionLaw

/-!
# The composition law for the inverse of the bilinear-pairing bijection

Let `φ` and `ψ` be composable morphisms of topoi, let `O` be a sheaf of rings and let `F`, `G` be
sheaves of `O`-modules. For the bijection

`Bilin_{f⁻¹O}(f⁻¹F × f⁻¹G, N) ⟶ Bilin_O(F × G, f_*N)`

attached to `f = ψ ∘ φ`, the inverse is the inverse for `ψ` followed by the inverse for `φ`, each
stage transposing back across its own adjunction and then precomposing with the inverse of its
own product comparison.

## Main results

* `Stacks.SheafOfModules.inverseImagePairingEquiv_symm_comp`: **the composition law for the
  inverse of the pairing bijection.**
* `Stacks.SheafOfModules.inverseImageBilinearEquiv_symm_comp`: the same for the bilinear-pairing
  bijection, read on the underlying pairing.

## References

* [Stacks Project, Tag 03D3](https://stacks.math.columbia.edu/tag/03D3)
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry CategoryTheory.Sheaf
open AlgebraicGeometry.SheafOfModules Stacks.Sheaves.RingedToposModules
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

namespace Stacks.SheafOfModules

universe w w' w'' v u v' u' v'' u''

section CompSymm

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {E : Type u''} [Category.{v''} E]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} {L : GrothendieckTopology E}
  [J.HasSheafCompose (forget RingCat.{w})] [L.HasSheafCompose (forget RingCat.{w''})]
  [J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [L.HasSheafCompose (forget AddCommGrpCat.{w''})]
  (φ : MorphismOfTopoi (Sheaf J (Type w)) (Sheaf K (Type w')))
  (ψ : MorphismOfTopoi (Sheaf K (Type w')) (Sheaf L (Type w'')))
  (O : Sheaf L RingCat.{w''}) (F G : SheafOfModules.{w''} O)
  (N : SheafOfModules.{w} (inverseImageRingSheaf (ψ.comp φ) O))

/-- **The composition law for the inverse of the pairing bijection.** Let `φ : Sh(C) → Sh(D)`
and `ψ : Sh(D) → Sh(E)` be morphisms of topoi, let `O` be a sheaf of rings on `E` and let `F`,
`G` be sheaves of `O`-modules. A pairing `p` of `F` and `G` with values in the direct image
`(ψ ∘ φ)_*N` is carried back to a pairing of the inverse images along the composite in two
stages: transpose back across `ψ⁻¹ ⊣ ψ_*` and precompose with the inverse of the product
comparison of `ψ⁻¹`, then transpose back across `φ⁻¹ ⊣ φ_*` and precompose with the inverse of
the product comparison of `φ⁻¹`. -/
theorem inverseImagePairingEquiv_symm_comp
    (p : moduleSheaf O F ⨯ moduleSheaf O G ⟶
      moduleSheaf O ((directImageModules (ψ.comp φ) O).obj N)) :
    (inverseImagePairingEquiv (ψ.comp φ) O F G N).symm p =
      (PreservesLimitPair.iso φ.inverseImage (ψ.inverseImage.obj (moduleSheaf O F))
            (ψ.inverseImage.obj (moduleSheaf O G))).inv ≫
        (φ.adj.homEquiv (ψ.inverseImage.obj (moduleSheaf O F) ⨯
              ψ.inverseImage.obj (moduleSheaf O G))
            (moduleSheaf (inverseImageRingSheaf (ψ.comp φ) O) N)).symm
          ((PreservesLimitPair.iso ψ.inverseImage (moduleSheaf O F) (moduleSheaf O G)).inv ≫
            (ψ.adj.homEquiv (moduleSheaf O F ⨯ moduleSheaf O G)
                (φ.pushforward.obj
                  (moduleSheaf (inverseImageRingSheaf (ψ.comp φ) O) N))).symm p) := by
  refine (Equiv.symm_apply_eq _).2 (Eq.symm ?_)
  refine (inverseImagePairingEquiv_comp φ ψ O F G N _).trans ?_
  simp only [← PreservesLimitPair.iso_hom, Iso.hom_inv_id_assoc, Equiv.apply_symm_apply]
  exact Equiv.apply_symm_apply _ p

/-- **The composition law for the inverse of the bilinear-pairing bijection.** The underlying
pairing of the preimage of a bilinear pairing `p` under the bijection for a composite `ψ ∘ φ` is
the two-stage transport of `Stacks.SheafOfModules.inverseImagePairingEquiv_symm_comp`. -/
theorem inverseImageBilinearEquiv_symm_comp
    (p : { p : moduleSheaf O F ⨯ moduleSheaf O G ⟶
        moduleSheaf O ((directImageModules (ψ.comp φ) O).obj N) // IsBilinearPairing O p }) :
    ((inverseImageBilinearEquiv (ψ.comp φ) O F G N).symm p).1 =
      (PreservesLimitPair.iso φ.inverseImage (ψ.inverseImage.obj (moduleSheaf O F))
            (ψ.inverseImage.obj (moduleSheaf O G))).inv ≫
        (φ.adj.homEquiv (ψ.inverseImage.obj (moduleSheaf O F) ⨯
              ψ.inverseImage.obj (moduleSheaf O G))
            (moduleSheaf (inverseImageRingSheaf (ψ.comp φ) O) N)).symm
          ((PreservesLimitPair.iso ψ.inverseImage (moduleSheaf O F) (moduleSheaf O G)).inv ≫
            (ψ.adj.homEquiv (moduleSheaf O F ⨯ moduleSheaf O G)
                (φ.pushforward.obj
                  (moduleSheaf (inverseImageRingSheaf (ψ.comp φ) O) N))).symm p.1) :=
  (inverseImageBilinearEquiv_symm_apply_coe (ψ.comp φ) O F G N p).trans
    (inverseImagePairingEquiv_symm_comp φ ψ O F G N p.1)

end CompSymm

end Stacks.SheafOfModules

end
