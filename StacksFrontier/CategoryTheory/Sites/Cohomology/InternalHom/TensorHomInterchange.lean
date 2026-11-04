module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.CompositionFunctoriality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DiagonalMorphism
import StacksCore.Tactic.StacksAttribute

/-! # Moving a tensor factor inside an internal Hom on a ringed site

Let `(C, O)` be a ringed site and let `K`, `L` and `M` be complexes of `O`-modules. A
homogeneous local section `x` of `K` and a homogeneous local section `φ` of
`SheafHom(M, L)` determine the local section `m ↦ x ⊗ φ(m)` of `SheafHom(M, Tot(K ⊗_O L))`,
and these assemble into the canonical morphism of complexes of `O`-modules of Stacks 0BYT,

`Tot(K ⊗_O SheafHom(M, L)) ⟶ SheafHom(M, Tot(K ⊗_O L))`,

which is functorial in all three complexes.

## Main definitions

* `AlgebraicGeometry.RingedSite.tensorHomInterchange`: the interchange morphism of Stacks 0BYT.
* `AlgebraicGeometry.RingedSite.TensorHomInterchangeConstruction`: that morphism together with
  its characterisation on homogeneous local pure tensors.

## Main results

* `AlgebraicGeometry.RingedSite.tensorHomInterchange_applyHomSection`: the characterisation of
  the interchange morphism on homogeneous local pure tensors.
* `AlgebraicGeometry.RingedSite.tensorHomInterchangeConstruction`: **Stacks 0BYT**, the
  canonical morphism.
* `AlgebraicGeometry.RingedSite.tensorHomInterchange_natural`: **Stacks 0BYT**, functoriality
  in all three complexes, together with the two specialisations
  `AlgebraicGeometry.RingedSite.tensorHomInterchange_natural_tensor` and
  `AlgebraicGeometry.RingedSite.tensorHomInterchange_natural_source` in which the inserted
  identities collapse.

## Implementation notes

Nothing has to be built from local sections here: the diagonal morphism of Stacks 0A93 turns
the tensor factor `K` into `SheafHom(L, Tot(K ⊗_O L))`, and the composition morphism of
Stacks 0A91 then composes it with `SheafHom(M, L)`, so the interchange morphism is the
composite

`Tot(K ⊗ SheafHom(M, L)) ⟶ Tot(SheafHom(L, Tot(K ⊗ L)) ⊗ SheafHom(M, L))
  ⟶ SheafHom(M, Tot(K ⊗ L))`.

Both constituents are already characterised on homogeneous local pure tensors, by
`AlgebraicGeometry.RingedSite.diagonalHomSection_applyOver` and
`AlgebraicGeometry.RingedSite.compositionSection_applyOver`, and the characterisation of the
composite follows by substitution; no sign enters, since neither the diagonal nor composition
carries one. In particular the construction needs no comparison between the two total tensor
products of a ringed site: both the source of the composition morphism and the target of the
diagonal are `AlgebraicGeometry.RingedSite.tensorTotal`.

Both the characterisation and the functoriality are stated at a section of `M` over an
arbitrary object of the slice site over `U`, not just over `U` itself, because that is the form
in which `AlgebraicGeometry.RingedSite.homSection_ext` asks for them; the version over `U` is
the case of the identity arrow. Consequently the uniqueness statement used for the
functoriality, `AlgebraicGeometry.RingedSite.tensorTotalHomSection_ext`, is the combination of
`AlgebraicGeometry.RingedSite.tensorTotal_hom_ext` with
`AlgebraicGeometry.RingedSite.homSection_ext` with no further work.

The three-variable identity is stated so that each variable is absorbed on the side where it
occurs; as for the composition morphism of Stacks 0A91, inserting identities in the other two
slots gives the one-variable statements. Only two of those three are recorded: in the variable
`L` neither inserted identity collapses, so that specialisation is the three-variable identity
itself.

The universes are the diagonal `RingedSite.{u, u, u}`, which is where
`AlgebraicGeometry.RingedSite.tensorTotal` and the morphisms of Stacks 0A91, 0A92 and 0A93 are
stated.

## References

* [Stacks Project, Tag 0BYT](https://stacks.math.columbia.edu/tag/0BYT)
* [Stacks Project, Tag 0A93](https://stacks.math.columbia.edu/tag/0A93)
* [Stacks Project, Tag 0A91](https://stacks.math.columbia.edu/tag/0A91)
* [Stacks Project, Tag 0BYM](https://stacks.math.columbia.edu/tag/0BYM)
-/

@[expose] public section

open CategoryTheory MonoidalCategory Opposite CochainComplex.HomComplex

universe u

namespace AlgebraicGeometry.RingedSite

variable (X : RingedSite.{u, u, u})

attribute [local instance] ringSheafSectionsCommRing presheafOfModulesMonoidalCategory
  curriedTensorPreservesZeroMorphisms curriedTensorObjPreservesZeroMorphisms

/-- A morphism from a total tensor-product complex to an internal Hom complex is determined by
the evaluations of the images of the homogeneous local pure tensors. -/
lemma tensorTotalHomSection_ext
    {A B Z W : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    {α β : tensorTotal X A B ⟶ (sheafHomComplex X Z W).obj}
    (h : ∀ (U V : X.C) (i : V ⟶ U) (t r a q : ℤ) (haq : a + (t + r) = q)
      (x : (A.X t).val.obj (op U)) (y : (B.X r).val.obj (op U)) (z : (Z.X a).val.obj (op V)),
      applyHomSectionOver X (sheafHomComplex X Z W) U V i (t + r) a q haq
          ((α.f (t + r)).val.app (op U) (tensorTotalSection X A B U t r x y)) z =
        applyHomSectionOver X (sheafHomComplex X Z W) U V i (t + r) a q haq
          ((β.f (t + r)).val.app (op U) (tensorTotalSection X A B U t r x y)) z) :
    α = β :=
  tensorTotal_hom_ext X fun U t r x y ↦
    homSection_ext X (sheafHomComplex X Z W) U (t + r)
      fun a q haq V i z ↦ h U V i t r a q haq x y z

section Morphism

variable
  (K L M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)

/-- **The interchange morphism** `Tot(K ⊗_O SheafHom(M, L)) ⟶ SheafHom(M, Tot(K ⊗_O L))` of
Stacks 0BYT: tensor the diagonal morphism of Stacks 0A93 with the identity and compose with the
composition morphism of Stacks 0A91. -/
noncomputable def tensorHomInterchange :
    tensorTotal X K (sheafHomComplex X M L).obj ⟶
      (sheafHomComplex X M (tensorTotal X K L)).obj :=
  tensorTotalMap X (diagonalMap X K L) (𝟙 (sheafHomComplex X M L).obj) ≫
    compositionMap X M L (tensorTotal X K L)

/-- **The characterisation of the interchange morphism**, on a section of `M` over an object of
the slice site over `U`: the pure tensor of a degree-`p` section `x` of `K` and a degree-`q`
section `φ` of `SheafHom(M, L)` is sent to the local section `m ↦ x ⊗ φ(m)`. -/
lemma tensorHomInterchange_applyHomSectionOver (U V : X.C) (i : V ⟶ U) (p q a s b : ℤ)
    (has : a + q = s) (hsb : s + p = b) (x : (K.X p).val.obj (op U))
    (φ : ((sheafHomComplex X M L).obj.X q).val.obj (op U)) (m : (M.X a).val.obj (op V)) :
    applyHomSectionOver X (sheafHomComplex X M (tensorTotal X K L)) U V i (p + q) a b
        (by omega)
        (((tensorHomInterchange X K L M).f (p + q)).val.app (op U)
          (tensorTotalSection X K (sheafHomComplex X M L).obj U p q x φ)) m =
      tensorTotalSectionAt X K L V p s b (by omega) (restrictSection X i x)
        (applyHomSectionOver X (sheafHomComplex X M L) U V i q a s has φ m) := by
  rw [tensorHomInterchange, HomologicalComplex.comp_f,
    AlgebraicGeometry.RingedSite.comp_val_app_apply',
    tensorTotalMap_tensorTotalSection, HomologicalComplex.id_f, SheafOfModules.id_val,
    PresheafOfModules.id_app, compositionMap_tensorTotalSection,
    compositionSection_applyOver X U V i p q (p + q) a s b rfl has hsb,
    diagonalMap_apply, diagonalHomSection_applyOver]
  rfl

/-- **The characterisation of the interchange morphism** on homogeneous local pure tensors: the
pure tensor of a degree-`p` section `x` of `K` and a degree-`q` section `φ` of
`SheafHom(M, L)` is sent to the local section `m ↦ x ⊗ φ(m)`. -/
lemma tensorHomInterchange_applyHomSection (U : X.C) (p q a s b : ℤ) (has : a + q = s)
    (hsb : s + p = b) (x : (K.X p).val.obj (op U))
    (φ : ((sheafHomComplex X M L).obj.X q).val.obj (op U)) (m : (M.X a).val.obj (op U)) :
    applyHomSection X (sheafHomComplex X M (tensorTotal X K L)) U (p + q) a b (by omega)
        (((tensorHomInterchange X K L M).f (p + q)).val.app (op U)
          (tensorTotalSection X K (sheafHomComplex X M L).obj U p q x φ)) m =
      tensorTotalSectionAt X K L U p s b (by omega) x
        (applyHomSection X (sheafHomComplex X M L) U q a s has φ m) := by
  rw [applyHomSection, tensorHomInterchange_applyHomSectionOver X K L M U U (𝟙 U) p q a s b has
    hsb x φ m, restrictSection_id]

end Morphism

/-- An interchange morphism of Stacks 0BYT, characterised by its action on every homogeneous
local pure tensor: the pure tensor of a degree-`p` section `x` of `K` and a degree-`q` section
`φ` of `SheafHom(M, L)` is sent to the local section of `SheafHom(M, Tot(K ⊗_O L))` taking a
degree-`a` section `m` of `M` to the pure tensor `x ⊗ φ(m)`, with no additional sign. -/
structure TensorHomInterchangeConstruction where
  /-- The morphism of complexes of `O`-modules moving the tensor factor inside the internal
  Hom. -/
  interchange (K L M : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    tensorTotal X K (sheafHomComplex X M L).obj ⟶
      (sheafHomComplex X M (tensorTotal X K L)).obj
  /-- Homogeneous local pure tensors act by `m ↦ x ⊗ φ(m)`, with no additional sign. -/
  interchange_tmul : ∀ (K L M : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) (U : X.C)
      (p q a s b : ℤ) (has : a + q = s) (hsb : s + p = b) (x : (K.X p).val.obj (op U))
      (φ : ((sheafHomComplex X M L).obj.X q).val.obj (op U)) (m : (M.X a).val.obj (op U)),
    applyHomSection X (sheafHomComplex X M (tensorTotal X K L)) U (p + q) a b (by omega)
        (((interchange K L M).f (p + q)).val.app (op U)
          (tensorTotalSection X K (sheafHomComplex X M L).obj U p q x φ)) m =
      tensorTotalSectionAt X K L U p s b (by omega) x
        (applyHomSection X (sheafHomComplex X M L) U q a s has φ m)

/-- **Stacks 0BYT.** For complexes `K`, `L`, `M` of modules on a ringed site there is a
canonical morphism of complexes of `O`-modules

`Tot(K ⊗_O SheafHom(M, L)) ⟶ SheafHom(M, Tot(K ⊗_O L))`,

namely the one sending each homogeneous local pure tensor `x ⊗ φ` to the local section
`m ↦ x ⊗ φ(m)`. -/
@[stacks 0BYT "the canonical morphism"]
noncomputable def tensorHomInterchangeConstruction : TensorHomInterchangeConstruction X where
  interchange K L M := tensorHomInterchange X K L M
  interchange_tmul K L M U p q a s b has hsb x φ m :=
    tensorHomInterchange_applyHomSection X K L M U p q a s b has hsb x φ m

section Natural

variable {K K' L L' M M' :
  CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}

/-- **Stacks 0BYT.** The interchange morphism is functorial in all three complexes at once:
covariant in the tensor factor `K` and in the target `L` of the internal Hom, contravariant in
its source `M`. -/
@[stacks 0BYT "functoriality in all three complexes"]
theorem tensorHomInterchange_natural (f : K ⟶ K') (g : L ⟶ L') (h : M' ⟶ M) :
    tensorHomInterchange X K L M ≫ homMap X h (tensorTotalMap X f g) =
      tensorTotalMap X f (homMap X h g) ≫ tensorHomInterchange X K' L' M' := by
  refine tensorTotalHomSection_ext X fun U V i p q a b hab x φ m ↦ ?_
  rw [HomologicalComplex.comp_f, AlgebraicGeometry.RingedSite.comp_val_app_apply',
    applyHomSectionOver_homMap X h (tensorTotalMap X f g) U V i (p + q) a b hab _ m,
    tensorHomInterchange_applyHomSectionOver X K L M U V i p q a (a + q) b rfl (by omega)
      x φ _,
    tensorTotalMap_tensorTotalSectionAt, HomologicalComplex.comp_f,
    AlgebraicGeometry.RingedSite.comp_val_app_apply',
    tensorTotalMap_tensorTotalSection,
    tensorHomInterchange_applyHomSectionOver X K' L' M' U V i p q a (a + q) b rfl (by omega)
      ((f.f p).val.app (op U) x) _ m,
    applyHomSectionOver_homMap X h g U V i q a (a + q) rfl φ m,
    restrictSection_natural X (f.f p) i x]

/-- The interchange morphism is covariant in the tensor factor. -/
theorem tensorHomInterchange_natural_tensor (f : K ⟶ K')
    (L M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    tensorHomInterchange X K L M ≫ homMap X (𝟙 M) (tensorTotalMap X f (𝟙 L)) =
      tensorTotalMap X f (𝟙 (sheafHomComplex X M L).obj) ≫ tensorHomInterchange X K' L M := by
  have hn := tensorHomInterchange_natural X f (𝟙 L) (𝟙 M)
  rwa [homMap_id] at hn

/-- The interchange morphism is contravariant in the source of the internal Hom. -/
theorem tensorHomInterchange_natural_source
    (K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (h : M' ⟶ M) :
    tensorHomInterchange X K L M ≫ homMap X h (𝟙 (tensorTotal X K L)) =
      tensorTotalMap X (𝟙 K) (homMap X h (𝟙 L)) ≫ tensorHomInterchange X K L M' := by
  have hn := tensorHomInterchange_natural X (𝟙 K) (𝟙 L) h
  rwa [tensorTotalMap_id] at hn

end Natural

end AlgebraicGeometry.RingedSite

end
