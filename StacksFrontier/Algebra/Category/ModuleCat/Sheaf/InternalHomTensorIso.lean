module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorHomAdjunction
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.TensorHomAdjunction

/-!
# Internal Hom out of a tensor product of sheaves of modules

Let `O` be a sheaf of commutative rings on a site `(C, J)` and let `F`, `G`, `H` be sheaves of
`O`-modules. The sheaf clause of Stacks 03EO whose subject is the internal Hom of a tensor
product is the currying isomorphism

`Hom_O(F ⊗_O G, H) ≅ Hom_O(F, Hom_O(G, H))`

of sheaves of `O`-modules, where `⊗_O` is the *sheafified* tensor product
`Stacks.SheafOfModules.Tensor.sheafTensor` and `Hom_O` is Stacks 03EM's internal Hom sheaf.

It is the generic currying isomorphism of a braided monoidal closed category,
`CategoryTheory.MonoidalClosed.ihomTensorIso`, read through the sheaf-level internal-Hom bridge
`Stacks.SheafOfModules.InternalHom.ihomIsoInternalHomSecondFunctor`, which identifies
`MonoidalClosed.ihom` on sheaves of modules with Stacks 03EM's internal Hom sheaf. The monoidal
structure used is `SheafOfModules.monoidalCategorySheafTensor`, whose tensor product is
`Stacks.SheafOfModules.Tensor.sheafTensor R` and whose internal hom is that of the localized
structure, so the bridge applies to it unchanged.

## Main definitions

* `Stacks.SheafOfModules.InternalHom.ihomTensorNatIso`: the generic currying isomorphism read
  as an isomorphism of functors `ihom (F ⊗ G) ≅ ihom G ⋙ ihom F`.
* `Stacks.SheafOfModules.InternalHom.sheafInternalHomTensorNatIso`: the currying isomorphism at
  the Stacks 03EM spelling, again as an isomorphism of functors in the target variable.

## Main results

* `Stacks.SheafOfModules.InternalHom.sheafInternalHomTensorIso`: the currying isomorphism
  `Hom_O(F ⊗_O G, H) ≅ Hom_O(F, Hom_O(G, H))`.
* `Stacks.SheafOfModules.InternalHom.sheafInternalHomTensorIso_natural_right`: it is natural
  covariantly in the target.
* `Stacks.SheafOfModules.InternalHom.pre_comp_ihomIsoInternalHomSecondFunctor`: the bridge
  carries `MonoidalClosed.pre` to the conjugate of the tensor whiskering under the two
  sheaf-level adjunctions of Stacks 03EO.

## Implementation notes

The isomorphism is built at the level of functors in the target variable, so its covariant
naturality is the naturality of that isomorphism.

The two contravariant naturality statements, phrased with precomposition on the internal Hom
sheaf (`internalHomMapLeft` of Stacks 03EN), and the value of the isomorphism on local pure
tensors are not proved here. `pre_comp_ihomIsoInternalHomSecondFunctor` carries
`MonoidalClosed.pre k` across the bridge to the conjugate of the tensor whiskering, which
`Stacks.SheafOfModules.InternalHom.conjugateEquiv_tensoringLeft_map` identifies with
precomposition by `k`.

**Universe narrowing, inherited from the chain and recorded rather than decided here.** The
statements are at ring universe `max u v` and module universe `max u v` for a site with objects
in `Type u` and morphisms in `Type v`, the same narrowing already carried by
`Stacks.SheafOfModules.InternalHom.sheafTensorHomAdjunction` and
`SheafOfModules.monoidalClosed`: the bridge is only available there, and the monoidal structure
on sheaves of modules whose tensor product is `Stacks.SheafOfModules.Tensor.sheafTensor` exists
only at module universe `max u v` over a `CommRingCat.{max u v}`-valued structure sheaf.

Nothing here is tagged: this file holds part of a clause of Stacks 03EO, and the tag is placed
once over a clause's whole covering set.

## References

* [Stacks Project, Tag 03EO](https://stacks.math.columbia.edu/tag/03EO)
* [Stacks Project, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM)
* [Stacks Project, Tag 0A8M](https://stacks.math.columbia.edu/tag/0A8M)
-/

@[expose] public section

open CategoryTheory MonoidalCategory MonoidalClosed

noncomputable section

universe v u

namespace Stacks.SheafOfModules.InternalHom

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable (R : Sheaf J CommRingCat.{max u v})
  [HasWeakSheafify J AddCommGrpCat.{max u v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]

section Localized

attribute [local instance] _root_.SheafOfModules.monoidalCategory
  _root_.SheafOfModules.monoidalClosed

/-- **The internal-Hom bridge carries `MonoidalClosed.pre` to a conjugate of the tensor
whiskering.** For `k : F' ⟶ F`, precomposition on the monoidal-closed internal hom becomes, on
the other side of the bridge, the conjugate of `k ▷ -` under the two sheaf-level
tensor--internal-Hom adjunctions of Stacks 03EO. -/
theorem pre_comp_ihomIsoInternalHomSecondFunctor
    {F F' : _root_.SheafOfModules.{max u v} (Stacks.SheafOfModules.Tensor.ringSheaf R)}
    (k : F' ⟶ F) :
    pre k ≫ (ihomIsoInternalHomSecondFunctor R F').hom =
      (ihomIsoInternalHomSecondFunctor R F).hom ≫
        conjugateEquiv (tensorLeftAdjunction R F) (tensorLeftAdjunction R F')
          ((tensoringLeft _).map k) := by
  have h1 := conjugateEquiv_comp (ihom.adjunction F) (ihom.adjunction F')
    (tensorLeftAdjunction R F') ((tensoringLeft _).map k) (𝟙 (tensorLeft F'))
  have h2 := conjugateEquiv_comp (ihom.adjunction F) (tensorLeftAdjunction R F)
    (tensorLeftAdjunction R F') (𝟙 (tensorLeft F)) ((tensoringLeft _).map k)
  rw [Category.id_comp] at h1
  rw [Category.comp_id] at h2
  exact h1.trans h2.symm

end Localized

section Reseated

attribute [local instance] _root_.SheafOfModules.monoidalCategorySheafTensor
  _root_.SheafOfModules.symmetricCategorySheafTensor
  _root_.SheafOfModules.monoidalClosedSheafTensor

variable (F G : _root_.SheafOfModules.{max u v} (Stacks.SheafOfModules.Tensor.ringSheaf R))

/-- **The generic currying isomorphism, as an isomorphism of functors.** For sheaves of
`O`-modules `F` and `G`, the internal hom out of `F ⊗_O G` is the iterated internal hom, and
the identification is natural in the target. This is
`CategoryTheory.MonoidalClosed.ihomTensorIso` and its covariant naturality, packaged as one
datum. -/
def ihomTensorNatIso : ihom (F ⊗ G) ≅ ihom G ⋙ ihom F :=
  (NatIso.ofComponents (fun H ↦ ihomTensorIso F G H)
    (fun {_ _} m ↦ ihomTensorIso_naturality_right F G m)).symm

/-- **Stacks 03EO, sheaf case, internal Hom of a tensor product, as an isomorphism of
functors.** Internal Hom out of the sheafified tensor product `F ⊗_O G` is the iterated
internal Hom sheaf, naturally in the target. -/
def sheafInternalHomTensorNatIso :
    internalHomSecondFunctor.{v, u, max u v, u} J R
        (((Stacks.SheafOfModules.Tensor.sheafTensor R).obj F).obj G) ≅
      internalHomSecondFunctor.{v, u, max u v, u} J R G ⋙
        internalHomSecondFunctor.{v, u, max u v, u} J R F :=
  (ihomIsoInternalHomSecondFunctor R (F ⊗ G)).symm ≪≫ ihomTensorNatIso R F G ≪≫
    Functor.isoWhiskerRight (ihomIsoInternalHomSecondFunctor R G) (ihom F) ≪≫
      Functor.isoWhiskerLeft (internalHomSecondFunctor.{v, u, max u v, u} J R G)
        (ihomIsoInternalHomSecondFunctor R F)

/-- **Stacks 03EO, sheaf case, internal Hom of a tensor product.** The internal Hom sheaf out
of the sheafified tensor product `F ⊗_O G` is the iterated internal Hom sheaf,
`Hom_O(F ⊗_O G, H) ≅ Hom_O(F, Hom_O(G, H))`. -/
def sheafInternalHomTensorIso
    (H : _root_.SheafOfModules.{max u v} (Stacks.SheafOfModules.Tensor.ringSheaf R)) :
    (internalHomSecondFunctor.{v, u, max u v, u} J R
        (((Stacks.SheafOfModules.Tensor.sheafTensor R).obj F).obj G)).obj H ≅
      (internalHomSecondFunctor.{v, u, max u v, u} J R F).obj
        ((internalHomSecondFunctor.{v, u, max u v, u} J R G).obj H) :=
  (sheafInternalHomTensorNatIso R F G).app H

/-- **Stacks 03EO, sheaf case.** The currying isomorphism is natural covariantly in its
target. -/
theorem sheafInternalHomTensorIso_natural_right
    {H H' : _root_.SheafOfModules.{max u v} (Stacks.SheafOfModules.Tensor.ringSheaf R)}
    (h : H ⟶ H') :
    (internalHomSecondFunctor.{v, u, max u v, u} J R
          (((Stacks.SheafOfModules.Tensor.sheafTensor R).obj F).obj G)).map h ≫
        (sheafInternalHomTensorIso R F G H').hom =
      (sheafInternalHomTensorIso R F G H).hom ≫
        (internalHomSecondFunctor.{v, u, max u v, u} J R F).map
          ((internalHomSecondFunctor.{v, u, max u v, u} J R G).map h) :=
  (sheafInternalHomTensorNatIso R F G).hom.naturality h

end Reseated

end Stacks.SheafOfModules.InternalHom

end

end
