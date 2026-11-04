module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.BilinearCompositionLawSymm
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullback

/-!
# The composition law for step 3 of the chain of Tag 03EL

`Stacks.SheafOfModules.pullbackTensorStep3` is the third link of the chain of bijections of
Tag 03EL, the transport of bilinear pairings of Tag 03D3:

`Bilin_{O_E}(F × G, χ_*N) = Bilin_{χ⁻¹O_E}(χ⁻¹F × χ⁻¹G, N|_{χ⁻¹O_E})`.

All the laws it came with — naturality in the sheaf of values, naturality in the two source
modules — hold for one fixed morphism of ringed topoi. This file supplies the law in the
*morphism* variable, for a morphism of ringed topoi presented as a composite `ψ ∘ φ`:

`Stacks.SheafOfModules.pullbackTensorStep3_comp`.

## Main results

* `Stacks.SheafOfModules.pullbackTensorStep3_comp`: **the composition law for step 3.** Step 3
  for a composite `ψ ∘ φ` of morphisms of ringed topoi is the two topos-level halves of the
  bijection of Tag 03D3 unwound one morphism at a time: transpose back across `ψ⁻¹ ⊣ ψ_*` and
  precompose with the inverse of the product comparison of `ψ⁻¹`, then do the same for `φ`.

## Implementation notes

*Why the law is not "step 3 for `φ` after step 3 for `ψ`".* It cannot be: the two do not compose.
Step 3 for `ψ : (Sh(D), O_D) ⟶ (Sh(E), O_E)` lands in pairings of `ψ⁻¹F` and `ψ⁻¹G` over the
sheaf of rings `ψ⁻¹O_E`, whereas step 3 for `φ : (Sh(C), O_C) ⟶ (Sh(D), O_D)` consumes pairings
of sheaves of `O_D`-modules. `ψ⁻¹O_E` and `O_D` are unrelated sheaves of rings — the structure
map `ψ♯` compares them, but only in one direction and not as an identification — so the output of
the one stage is not an input of the other. What *does* compose is the pair of topos-level halves
the bijection is built from, the product comparison of the inverse image and the transposition
across the adjunction, and that is what the law below unwinds. It is
`Stacks.SheafOfModules.inverseImageBilinearEquiv_symm_comp` read at
`AlgebraicGeometry.RingedToposHom.comp`.

*No transport of scalars appears.* One might expect a restriction of scalars along
`Stacks.Sheaves.ToposPullback.pullbackRingSheafCompIso`, since
`inverseImageRingSheaf φ⁻¹ (inverseImageRingSheaf ψ⁻¹ O_E)` and
`inverseImageRingSheaf (ψ ∘ φ)⁻¹ O_E` carry different transported ring structures on the same
underlying sheaf of sets, and `Stacks.Sheaves.RingedToposModules.directImageModulesCompIso`
carries exactly such a prefix for that reason. It does not appear here because the intermediate
sheaf of rings never does: the statement mentions only `(ψ ∘ φ)⁻¹O_E`, and the two intermediate
objects are inverse images of *sheaves of sets*, which compose on the nose.

*The underlying morphism of topoi of the composite.* `pullbackTensorStep3` is taken at the
four-field morphism of ringed topoi
`Stacks.Sheaves.RingedToposModules.RingedToposHom`, which has no composition of its own; the
composite here is the two-field `AlgebraicGeometry.RingedToposHom.comp` of Stacks 01D3 (3),
passed through `AlgebraicGeometry.RingedToposHom.toModulesHom`. That route is what makes the law
statable, and it is the route the consumers of the chain already take. Both
`AlgebraicGeometry.RingedToposHom.comp_toToposHom` and
`AlgebraicGeometry.RingedToposHom.toModulesHom_toToposHom` hold by `rfl`, so the underlying
morphism of topoi of the composite *is* the composite of the underlying morphisms of topoi and no
transport along an equality of morphisms of topoi is needed.

## References

* [Stacks Project, Tag 01D3](https://stacks.math.columbia.edu/tag/01D3)
* [Stacks Project, Tag 03D3](https://stacks.math.columbia.edu/tag/03D3)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry CategoryTheory.Sheaf
open AlgebraicGeometry.SheafOfModules Stacks.Sheaves.RingedToposModules
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

namespace Stacks.SheafOfModules

universe w w' w'' v u v' u' v'' u''

section Step3

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  {Z : RingedTopos.{v'', u'', w''}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{w''} RingCat.{w''})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [Z.J.HasSheafCompose (forget RingCat.{w''})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Z.J.HasSheafCompose (forget AddCommGrpCat.{w''})]
  (φ : AlgebraicGeometry.RingedToposHom X Y) (ψ : AlgebraicGeometry.RingedToposHom Y Z)
  (N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))

/-- The sheaf of modules over the inverse image `(ψ ∘ φ)⁻¹O_E` that step 3 of the chain of
Tag 03EL takes its values in, for a morphism of ringed topoi presented as a composite: the
restriction of scalars of `N` along the inverse-image form of the structure map of the
composite.

It is named because the statement of the composition law mentions it three times, and an
unnamed occurrence of it is what makes the statement's elaboration expensive. -/
abbrev step3CompValues : SheafOfModules.{w}
    (inverseImageRingSheaf (ψ.toToposHom.comp φ.toToposHom)
      (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)) :=
  (SheafOfModules.restrictScalars (ψ.comp φ).toModulesHom.fSharpInverseImage).obj N

/-- **The composition law for step 3 of the chain of Tag 03EL.** Let
`φ : (Sh(C), O_C) ⟶ (Sh(D), O_D)` and `ψ : (Sh(D), O_D) ⟶ (Sh(E), O_E)` be morphisms of ringed
topoi, let `F` and `G` be sheaves of `O_E`-modules and `N` a sheaf of `O_C`-modules. A bilinear
pairing `p` of `F` and `G` with values in the direct image `(ψ ∘ φ)_*N` is carried by step 3 for
the composite to the pairing obtained in two stages: transpose `p` back across `ψ⁻¹ ⊣ ψ_*` and
precompose with the inverse of the product comparison of `ψ⁻¹`, then transpose the result back
across `φ⁻¹ ⊣ φ_*` and precompose with the inverse of the product comparison of `φ⁻¹`.

Only the underlying pairing is asserted; the bilinearity of the image is carried along by the
bijection rather than computed, which is
`Stacks.SheafOfModules.inverseImageBilinearEquiv_symm_apply_coe`.

The implementation notes record why this is the honest shape of the law, and in particular why
it is *not* an equation between step 3 for `ψ` followed by step 3 for `φ`. -/
theorem pullbackTensorStep3_comp
    (F G : SheafOfModules.{w''} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O))
    (p : { p : moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Z.O) F ⨯
          moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Z.O) G ⟶
        moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)
          ((Stacks.Sheaves.RingedToposModules.pushforwardModules
            (ψ.comp φ).toModulesHom).obj N) //
      IsBilinearPairing (Stacks.SheafOfModules.Tensor.ringSheaf Z.O) p }) :
    (pullbackTensorStep3 (ψ.comp φ).toModulesHom F G N p).1 =
      (PreservesLimitPair.iso φ.toToposHom.inverseImage
            (ψ.toToposHom.inverseImage.obj
              (moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Z.O) F))
            (ψ.toToposHom.inverseImage.obj
              (moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Z.O) G))).inv ≫
        (φ.toToposHom.adj.homEquiv
            (ψ.toToposHom.inverseImage.obj
                (moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Z.O) F) ⨯
              ψ.toToposHom.inverseImage.obj
                (moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Z.O) G))
            (moduleSheaf (inverseImageRingSheaf (ψ.toToposHom.comp φ.toToposHom)
              (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)) (step3CompValues φ ψ N))).symm
          ((PreservesLimitPair.iso ψ.toToposHom.inverseImage
                (moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Z.O) F)
                (moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Z.O) G)).inv ≫
            (ψ.toToposHom.adj.homEquiv
                (moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Z.O) F ⨯
                  moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Z.O) G)
                (φ.toToposHom.pushforward.obj
                  (moduleSheaf (inverseImageRingSheaf (ψ.toToposHom.comp φ.toToposHom)
                    (Stacks.SheafOfModules.Tensor.ringSheaf Z.O))
                    (step3CompValues φ ψ N)))).symm p.1) :=
  inverseImageBilinearEquiv_symm_comp φ.toToposHom ψ.toToposHom
    (Stacks.SheafOfModules.Tensor.ringSheaf Z.O) F G (step3CompValues φ ψ N) p

end Step3

end Stacks.SheafOfModules

end
