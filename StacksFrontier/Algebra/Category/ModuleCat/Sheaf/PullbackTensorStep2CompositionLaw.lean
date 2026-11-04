module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposModulesCompIso
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullback

/-!
# The composition law for step 2 of the chain of Tag 03EL

`Stacks.SheafOfModules.pullbackTensorStep2` is the second link of the chain of bijections of
Tag 03EL, the universal property of the tensor product sheaf over the structure sheaf of the
target:

`Hom_{O_E}(F ⊗ G, χ_*N) = Bilin_{O_E}(F × G, χ_*N)`.

The morphism of ringed topoi `χ` enters only through the single object `χ_*N`: the sheaf of rings
is the structure sheaf of the *target*, which a composite shares with its second factor, and the
two source modules are unchanged. So the composition law for step 2 is not a statement about two
different universal properties being composed — there is only one — but the statement that the
*one* universal property is compatible with the comparison `ψ_*(φ_*N) ≅ (ψ ∘ φ)_*N` of successive
direct images. That is what is proved here.

## Main definitions

* `Stacks.SheafOfModules.compPushforwardToposIso`: the comparison of the geometric direct images
  for a composite of morphisms of ringed topoi. It is the identity: `MorphismOfTopoi.comp`
  *defines* the pushforward of the composite to be the composite of the pushforwards.
* `Stacks.SheafOfModules.pushforwardModulesCompAppIso`: the comparison
  `ψ_*(φ_*N) ≅ (ψ ∘ φ)_*N` of direct images of a sheaf of modules, for the four-field morphisms
  of ringed topoi the chain of Tag 03EL is stated at.

## Main results

* `Stacks.SheafOfModules.compPushforwardToposIso_fSharpSet`: the comparison carries the composite
  structure map to the structure map of the composite. This is the one compatibility
  `Stacks.Sheaves.RingedToposModules.pushforwardModulesCompIsoApp` asks for, and it is
  `AlgebraicGeometry.RingedToposHom.comp_fSharpRing_underlying`.
* `Stacks.SheafOfModules.pullbackTensorStep2_comp'`: **the composition law for step 2.**

## Implementation notes

The chain of Tag 03EL is stated at `Stacks.Sheaves.RingedToposModules.RingedToposHom`, the
four-field morphism of ringed topoi, which carries both forms of the structure map. That
structure has *no composition of its own*, and every composition law for it in this development
is therefore parameterized by a third morphism `χ` standing for the composite together with a
comparison `τ` of the geometric direct images and the compatibility of `τ` with the structure
maps. The composite used here is the two-field
`AlgebraicGeometry.RingedToposHom.comp` of Stacks 01D3 (3) read through
`AlgebraicGeometry.RingedToposHom.toModulesHom`; `τ` is then the identity and the compatibility
is the source's own formula for the composite structure map.

The law is stated on the underlying pairing rather than on the bilinear subtype, as
`Stacks.SheafOfModules.inverseImageBilinearEquiv_comp` is: the bilinearity of the image is
carried along by the bijection rather than computed, so asserting it again would add nothing and
would put a proof term into the statement.

## References

* [Stacks Project, Tag 01D3](https://stacks.math.columbia.edu/tag/01D3)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 05NA](https://stacks.math.columbia.edu/tag/05NA)
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry CategoryTheory.Sheaf
open AlgebraicGeometry.SheafOfModules Stacks.Sheaves.RingedToposModules
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

namespace Stacks.SheafOfModules

universe w w' w'' v u v' u' v'' u''

section Step2

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  {Z : RingedTopos.{v'', u'', w''}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{w''} RingCat.{w''})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [Z.J.HasSheafCompose (forget RingCat.{w''})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [Z.J.HasSheafCompose (forget AddCommGrpCat.{w''})]
  (φ : AlgebraicGeometry.RingedToposHom X Y) (ψ : AlgebraicGeometry.RingedToposHom Y Z)

/-- **The comparison of the geometric direct images for a composite of morphisms of ringed
topoi.** It is the identity: `MorphismOfTopoi.comp` defines the pushforward of a composite to be
the composite of the pushforwards, and
`AlgebraicGeometry.RingedToposHom.comp_toToposHom` and
`AlgebraicGeometry.RingedToposHom.toModulesHom_toToposHom` both hold by `rfl`.

It is named because it is the comparison `τ` that every composition law for the four-field
morphism of ringed topoi is parameterized by; being the identity is a fact about this particular
presentation of the composite, not about composition in general. -/
def compPushforwardToposIso :
    φ.toToposHom.pushforward ⋙ ψ.toToposHom.pushforward ≅
      (ψ.comp φ).toModulesHom.toToposHom.pushforward :=
  Iso.refl _

omit [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [Z.J.HasSheafCompose (forget AddCommGrpCat.{w''})] in
/-- **The comparison of the geometric direct images carries the composite structure map to the
structure map of the composite.** This is the compatibility
`Stacks.Sheaves.RingedToposModules.pushforwardModulesCompIsoApp` requires of its comparison, and
it is the source's own formula for the structure map of a composite,
`AlgebraicGeometry.RingedToposHom.comp_fSharpRing_underlying`. -/
theorem compPushforwardToposIso_fSharpSet :
    fSharpSetComp φ.toModulesHom ψ.toModulesHom ≫
        (compPushforwardToposIso φ ψ).hom.app
          (Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) =
      fSharpSet (ψ.comp φ).toModulesHom :=
  (Category.comp_id (fSharpSetComp φ.toModulesHom ψ.toModulesHom)).trans
    ((fSharpSetComp_eq φ.toModulesHom ψ.toModulesHom).trans
      (AlgebraicGeometry.RingedToposHom.comp_fSharpRing_underlying ψ φ).symm)

variable (N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))

/-- **The comparison `ψ_*(φ_*N) ≅ (ψ ∘ φ)_*N` of direct images of a sheaf of modules**, for the
four-field morphisms of ringed topoi the chain of Tag 03EL is stated at. It is
`Stacks.Sheaves.RingedToposModules.pushforwardModulesCompIsoApp` at the identity comparison
`Stacks.SheafOfModules.compPushforwardToposIso` of the geometric direct images.

Naming this is what keeps the statement of the composition law for step 2 short enough to
elaborate cheaply: the comparison occurs three times in it. -/
def pushforwardModulesCompAppIso :
    (pushforwardModules ψ.toModulesHom).obj ((pushforwardModules φ.toModulesHom).obj N) ≅
      (pushforwardModules (ψ.comp φ).toModulesHom).obj N :=
  pushforwardModulesCompIsoApp φ.toModulesHom ψ.toModulesHom (ψ.comp φ).toModulesHom N
    (compPushforwardToposIso φ ψ) (compPushforwardToposIso_fSharpSet φ ψ)

variable [HasWeakSheafify Z.J AddCommGrpCat.{w''}]
  [Z.J.WEqualsLocallyBijective AddCommGrpCat.{w''}]

/-- **The composition law for step 2 of the chain of Tag 03EL.** Let
`φ : (Sh(C), O_C) ⟶ (Sh(D), O_D)` and `ψ : (Sh(D), O_D) ⟶ (Sh(E), O_E)` be morphisms of ringed
topoi, let `F` and `G` be sheaves of `O_E`-modules and `N` a sheaf of `O_C`-modules. A morphism
`t : F ⊗_{O_E} G ⟶ ψ_*(φ_*N)`, pushed along the comparison `ψ_*(φ_*N) ≅ (ψ ∘ φ)_*N` and then
carried to a bilinear pairing by step 2 for the composite, gives the bilinear pairing of `t`
itself composed with that comparison.

Only the underlying pairing is asserted; the bilinearity is carried along by the bijection. The
implementation notes record why this, rather than an equation between two universal properties,
is what a composition law for step 2 can say: `χ` enters step 2 only through the object `χ_*N`.

It is `Stacks.SheafOfModules.bilinearEquivTensorSheafHom_symm_naturality` read at that
comparison. -/
theorem pullbackTensorStep2_comp'
    (F G : SheafOfModules.{w''} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O))
    (t : ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Z.O))).obj (F, G) ⟶
      (pushforwardModules ψ.toModulesHom).obj ((pushforwardModules φ.toModulesHom).obj N)) :
    (pullbackTensorStep2 (ψ.comp φ).toModulesHom F G N
        (t ≫ (pushforwardModulesCompAppIso φ ψ N).hom)).1 =
      (pullbackTensorStep2 ψ.toModulesHom F G
          ((pushforwardModules φ.toModulesHom).obj N) t).1 ≫
        (moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)).map
          (pushforwardModulesCompAppIso φ ψ N).hom :=
  congrArg Subtype.val
    (bilinearEquivTensorSheafHom_symm_naturality
      (hA := (Stacks.SheafOfModules.Tensor.ringSheaf Z.O).property)
      (F := F) (G := G) t (pushforwardModulesCompAppIso φ ψ N).hom)

end Step2

end Stacks.SheafOfModules

end
