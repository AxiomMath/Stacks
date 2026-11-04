module

public import StacksFrontier.AlgebraicGeometry.AlgebraOpenExtension.Basic
public import StacksFrontier.AlgebraicGeometry.AlgebraSheafModuleFunctor.Basic
public import StacksFrontier.AlgebraicGeometry.OpenImmersionAlgebraBridges.AlgebraPushforward
public import StacksFrontier.AlgebraicGeometry.QcohLimits.Basic
public import StacksFrontier.AlgebraicGeometry.RelativeMayerVietoris.Qcoh
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.BiproductQuasicoherent
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A fibre product of quasi-coherent sheaves of algebras is quasi-coherent

Let `X` be a scheme and let `A ⟶ C ⟵ B` be a cospan of sheaves of commutative `𝒪_X`-algebras
with `A`, `B` and `C` quasi-coherent.  This file proves that the fibre product `A ×_C B`,
formed in `Stacks.RelativeSpec.AlgebraSheaf X`, is again quasi-coherent -- with no hypothesis
on `X` and no hypothesis on the two morphisms.

It then instantiates that at the extension algebra `A ×_{j_*(A|_U)} j_*G` of
`StacksFrontier/AlgebraicGeometry/AlgebraOpenExtension/Basic.lean`, which is the one remaining step
in the first piece of the algebra route to Stacks Tag 05JT and Tag 0817.

## Main results

* `Stacks.AlgebraicGeometry.AlgebraFibreProduct.preservesLimitsOfShape_underlyingModuleFunctor`:
  `Stacks.RelativeSpec.AlgebraSheaf.underlyingModuleFunctor` carries a fibre product of algebra
  sheaves to the fibre product of the underlying `𝒪_X`-modules.
* `Stacks.AlgebraicGeometry.AlgebraFibreProduct.isQuasicoherent_fibreProductModules`: a fibre
  product of quasi-coherent sheaves of modules is quasi-coherent.
* `Stacks.AlgebraicGeometry.AlgebraFibreProduct.isQuasicoherent_fibreProduct`: **the main result**,
  a fibre product of quasi-coherent algebra sheaves is quasi-coherent.
* `Stacks.AlgebraicGeometry.AlgebraFibreProduct.underlyingModulePushforwardIso`: the underlying
  module of a direct image of algebra sheaves is the direct image of the underlying module;
  `Stacks.AlgebraicGeometry.AlgebraFibreProduct.isQuasicoherent_algebraPushforward` is
  [Stacks, Tag 01LC] read at the level of algebras.
* `Stacks.AlgebraicGeometry.AlgebraFibreProduct.isQuasicoherent_extensionAlgebra`: the
  extension algebra of `φ : G ⟶ A|_U` across a quasi-compact open immersion is quasi-coherent.

## The two bridges the extension file called absent, and which of them was needed

`AlgebraOpenExtension/Basic.lean` records that quasi-coherence of the fibre product "needs two
bridges that do not exist: that `AlgebraSheaf.underlyingModuleFunctor` carries the fibre product
above to the fibre product of underlying modules, and that it carries `algebraPushforward j` to
`AlgebraicGeometry.Scheme.Modules.pushforward j`."  Both are built here, and the second is an
identity: `underlyingModulePushforwardIso` is `CategoryTheory.Iso.refl`, the two objects being
definitionally equal.  Direct image of algebra sheaves is `Under.post` of the direct image of
sheaves of rings followed by `Under.map` of the comorphism, so its sections over `V` are the
sections of the source over `j⁻¹V` with `𝒪_X(V)` acting through `j.c` -- which is exactly how
`AlgebraicGeometry.Scheme.Modules.pushforward` acts, by
`AlgebraicGeometry.Scheme.Modules.pushforward_obj_obj`.

The first bridge is not an identity, and it is not proved by hand either.  The route is that
`Stacks.RelativeSpec.AlgebraSheaf.underlyingModule` changes neither the sections nor their
addition -- it only restricts the scalars -- so the composite

```
AlgebraSheaf X ⥤ X.Modules ⥤ TopCat.Presheaf Ab X
```

is *definitionally equal* to the composite that forgets the algebra structure, takes underlying
presheaves of commutative rings and then underlying abelian groups.  `algebraAbPresheaf` is that
second composite and `Iso.refl` is the comparison.  Each of its three factors preserves limits
(`CategoryTheory.Under.forget` creates them, `CategoryTheory.sheafToPresheaf` preserves them,
and so does postcomposition with a limit-preserving functor), and
`AlgebraicGeometry.Scheme.Modules.toPresheaf` reflects isomorphisms, hence reflects limits.  So
the bridge is `CategoryTheory.Limits.preservesLimitsOfShape_of_reflects_of_preserves` and
nothing is computed.

**Why `algebraAbPresheaf` is a named definition rather than an inline composite.**
`TopCat.Sheaf CommRingCat X` and `TopCat.Presheaf Ab X` carry their *own* `Category` instances,
distinct from the ones on `CategoryTheory.Sheaf` and on the functor category they unfold to.
Concretely, `PreservesLimitsOfShape WalkingCospan (Under.forget X.sheaf ⋙ sheafToPresheaf _ _
⋙ _)` fails to synthesize, while the same statement about a composite whose factors are
*declared* at the `TopCat` spellings succeeds.  This is the same obstruction that
`Stacks.AlgebraicGeometry.AlgebraOpenExtension.hasPullbacks_topCatSheafCommRingCat` and
`Stacks.AffineAlgebraEquivalence.hasPushouts_topCatSheafCommRingCat` exist for; the fix is to
name the composite at the spelling instance search is going to see.

## `fibreProduct`, not `pullback`, and the reason is a homonym

The two quasi-coherence results below are named `isQuasicoherent_fibreProduct...` rather than
`isQuasicoherent_pullback...` on purpose.  Across `StacksDraft` and `Stacks`, the name
`isQuasicoherent_pullback` is already taken, by `Stacks.Modules.isQuasicoherent_pullback` and
`Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback`, with thirty-two further
files naming one of those -- and both of them are Stacks Tag 01BG, the *inverse image* of a
quasi-coherent module, which has nothing to do with a fibre product.  Reusing the word would put
two unrelated theorems one `open` away from each other.

## What quasi-coherence of a fibre product of modules costs

Nothing new: in an abelian category a fibre product is a kernel, by
`CategoryTheory.Abelian.PullbackToBiproductIsKernel.isLimitPullbackToBiproduct`, the biproduct
of two quasi-coherent modules is quasi-coherent by
`AlgebraicGeometry.directSum_isQuasicoherent_scheme` (Tag 01BF) and a kernel of a morphism of
quasi-coherent modules is quasi-coherent by
`Stacks.AlgebraicGeometry.QcohLimits.isQuasicoherent_kernel`, for an arbitrary scheme.  This is
why the algebra-level statement needs no hypothesis on `X`: unlike
`AlgebraicGeometry.graphKernel_isQuasicoherent`, which reaches the same conclusion through a
direct image and therefore has to assume the open immersion quasi-compact, the fibre product is
formed from the three given objects alone.

The hypotheses reappear in `isQuasicoherent_extensionAlgebra`, where two of the three corners of
the cospan are direct images: `[QuasiCompact j]` is what Tag 01LC needs, and quasi-coherence of
the restriction `(algebraPullback j).obj A` is carried as a hypothesis.  That last one is a real
gap and is recorded as such: for an open immersion
`Stacks.AffineAlgebraEquivalence.algebraPullback` is the plain inverse image, by
`Stacks.OpenImmersionAlgebraBridges.isIso_algebraPullbackMap`, but identifying the *underlying
module* of the inverse image with `AlgebraicGeometry.Scheme.Modules.pullback` is a third bridge,
which quasi-coherence of the fibre product does not need and which is not built here.

## No stacks attribute

Nothing in this file carries a stacks tag and nothing could.  Tag 01PE's three labels are all
assertions about `AlgebraicGeometry.Scheme.Modules`, and the assertions of Tag 05JT and Tag 0817
are about filtered colimits of finite-type quasi-coherent subalgebras, not about a single fibre
product.  This is infrastructure those tags wait on.

## References

* [Stacks Project, Tag 01LC](https://stacks.math.columbia.edu/tag/01LC)
* [Stacks Project, Tag 01PE](https://stacks.math.columbia.edu/tag/01PE)
* [Stacks Project, Tag 05JT](https://stacks.math.columbia.edu/tag/05JT)
* [Stacks Project, Tag 0817](https://stacks.math.columbia.edu/tag/0817)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.AffineAlgebraEquivalence Stacks.RelativeSpec
open Stacks.AlgebraicGeometry.AlgebraOpenExtension

universe u

namespace Stacks.AlgebraicGeometry.AlgebraFibreProduct

/-! ### The underlying module of a fibre product of algebra sheaves -/

/-- The underlying presheaf of abelian groups of a sheaf of commutative rings. -/
public def ringAbPresheaf (X : Scheme.{u}) :
    TopCat.Sheaf CommRingCat.{u} X.toPresheafedSpace.carrier ⥤
      TopCat.Presheaf AddCommGrpCat.{u} X.toPresheafedSpace.carrier :=
  sheafToPresheaf _ _ ⋙ (Functor.whiskeringRight _ _ _).obj
    (forget₂ CommRingCat.{u} RingCat.{u} ⋙ forget₂ RingCat.{u} AddCommGrpCat.{u})

/-- Passing to the underlying presheaf of abelian groups preserves fibre products: sheaves of
rings have theirs computed in presheaves, presheaf limits are pointwise, and the two forgetful
functors out of `CommRingCat` preserve limits. -/
public instance preservesLimitsOfShape_ringAbPresheaf (X : Scheme.{u}) :
    PreservesLimitsOfShape WalkingCospan (ringAbPresheaf X) :=
  inferInstanceAs (PreservesLimitsOfShape WalkingCospan
    (sheafToPresheaf (Opens.grothendieckTopology X) CommRingCat.{u} ⋙
      (Functor.whiskeringRight _ _ _).obj
        (forget₂ CommRingCat.{u} RingCat.{u} ⋙ forget₂ RingCat.{u} AddCommGrpCat.{u})))

/-- The underlying presheaf of abelian groups of a sheaf of commutative `𝒪_X`-algebras: forget
the structure morphism, then forget to abelian groups. -/
public def algebraAbPresheaf (X : Scheme.{u}) :
    AlgebraSheaf X ⥤ TopCat.Presheaf AddCommGrpCat.{u} X.toPresheafedSpace.carrier :=
  Under.forget X.sheaf ⋙ ringAbPresheaf X

/-- `algebraAbPresheaf` preserves fibre products, `CategoryTheory.Under.forget` creating
limits. -/
public instance preservesLimitsOfShape_algebraAbPresheaf (X : Scheme.{u}) :
    PreservesLimitsOfShape WalkingCospan (algebraAbPresheaf X) :=
  inferInstanceAs (PreservesLimitsOfShape WalkingCospan (Under.forget X.sheaf ⋙ ringAbPresheaf X))

/-- **Taking the underlying module of an algebra sheaf does not change the sections or their
addition**, only the scalars that act on them: the underlying presheaf of abelian groups of
`AlgebraSheaf.underlyingModule` is `algebraAbPresheaf`, definitionally. -/
public def algebraAbPresheafIso (X : Scheme.{u}) :
    algebraAbPresheaf X ≅
      AlgebraSheaf.underlyingModuleFunctor X ⋙ Scheme.Modules.toPresheaf X :=
  Iso.refl _

/-- The underlying presheaf of abelian groups of the underlying module preserves fibre
products. -/
public instance preservesLimitsOfShape_underlyingModuleFunctor_toPresheaf (X : Scheme.{u}) :
    PreservesLimitsOfShape WalkingCospan
      (AlgebraSheaf.underlyingModuleFunctor X ⋙ Scheme.Modules.toPresheaf X) :=
  preservesLimitsOfShape_of_natIso (algebraAbPresheafIso X)

/-- **The first bridge: `AlgebraSheaf.underlyingModuleFunctor` carries a fibre product of
algebra sheaves to the fibre product of the underlying `𝒪_X`-modules.**  Underlying presheaves
of abelian groups see the fibre product on both sides, and
`AlgebraicGeometry.Scheme.Modules.toPresheaf` reflects isomorphisms, hence limits. -/
public instance preservesLimitsOfShape_underlyingModuleFunctor (X : Scheme.{u}) :
    PreservesLimitsOfShape WalkingCospan (AlgebraSheaf.underlyingModuleFunctor X) :=
  preservesLimitsOfShape_of_reflects_of_preserves _ (Scheme.Modules.toPresheaf X)

/-- A cartesian square of algebra sheaves stays cartesian on underlying modules. -/
public theorem isPullback_underlyingModuleMap {X : Scheme.{u}} {P A B C : AlgebraSheaf X}
    {p : P ⟶ A} {q : P ⟶ B} {f : A ⟶ C} {g : B ⟶ C} (h : IsPullback p q f g) :
    IsPullback (AlgebraSheaf.underlyingModuleMap p) (AlgebraSheaf.underlyingModuleMap q)
      (AlgebraSheaf.underlyingModuleMap f) (AlgebraSheaf.underlyingModuleMap g) :=
  h.map (AlgebraSheaf.underlyingModuleFunctor X)

/-- Quasi-coherence of the underlying module of an algebra sheaf, in the spelling instance
search meets it after a functor application. -/
public instance isQuasicoherent_underlyingModuleFunctor_obj (X : Scheme.{u})
    (A : AlgebraSheaf X) [A.IsQuasicoherent] :
    ((AlgebraSheaf.underlyingModuleFunctor X).obj A).IsQuasicoherent :=
  ‹_›

/-! ### Fibre products of quasi-coherent modules -/

/-- **A fibre product of quasi-coherent sheaves of modules is quasi-coherent.**  A fibre product
in an abelian category is the kernel of `(f, -g)` out of the biproduct; the biproduct is
quasi-coherent by Tag 01BF and a kernel of a morphism of quasi-coherent modules by
`Stacks.AlgebraicGeometry.QcohLimits.isQuasicoherent_kernel`. -/
public instance isQuasicoherent_fibreProductModules {X : Scheme.{u}} {M N P : X.Modules}
    (f : M ⟶ P) (g : N ⟶ P) [M.IsQuasicoherent] [N.IsQuasicoherent] [P.IsQuasicoherent] :
    (pullback f g).IsQuasicoherent :=
  have e : kernel (biprod.desc f (-g)) ≅ pullback f g :=
    IsLimit.conePointUniqueUpToIso (kernelIsKernel (biprod.desc f (-g)))
      (Abelian.PullbackToBiproductIsKernel.isLimitPullbackToBiproduct f g)
  (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso e
    (QcohLimits.isQuasicoherent_kernel (biprod.desc f (-g)))

/-! ### Fibre products of quasi-coherent algebra sheaves -/

/-- **A fibre product of quasi-coherent sheaves of commutative `𝒪_X`-algebras is
quasi-coherent.**  There is no hypothesis on `X` and none on the two morphisms: the underlying
module of the fibre product is the fibre product of the underlying modules, by
`preservesLimitsOfShape_underlyingModuleFunctor`, and that is quasi-coherent by
`isQuasicoherent_fibreProductModules`. -/
public instance isQuasicoherent_fibreProduct {X : Scheme.{u}} {A B C : AlgebraSheaf X}
    (f : A ⟶ C) (g : B ⟶ C) [A.IsQuasicoherent] [B.IsQuasicoherent] [C.IsQuasicoherent] :
    (pullback f g).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    ((isPullback_underlyingModuleMap (IsPullback.of_hasPullback f g)).isoPullback).symm
    (isQuasicoherent_fibreProductModules (AlgebraSheaf.underlyingModuleMap f)
      (AlgebraSheaf.underlyingModuleMap g))

/-- Faithfulness check for `isQuasicoherent_fibreProduct`, with every hypothesis an explicit
argument: the three quasi-coherence assumptions and nothing else -- no affineness, no
Noetherian hypothesis, no condition on `f` or `g`, and no condition on `X`. -/
example {X : Scheme.{u}} (A B C : AlgebraSheaf X) (f : A ⟶ C) (g : B ⟶ C)
    (_hA : AlgebraSheaf.IsQuasicoherent A) (_hB : AlgebraSheaf.IsQuasicoherent B)
    (_hC : AlgebraSheaf.IsQuasicoherent C) :
    AlgebraSheaf.IsQuasicoherent (pullback f g) :=
  isQuasicoherent_fibreProduct f g

/-! ### Direct images, and the extension algebra -/

/-- **The second bridge, and it is an identity.**  The underlying `𝒪_X`-module of the direct
image of an algebra sheaf is the direct image of its underlying `𝒪_U`-module: both have the
sections of `B` over `j⁻¹V` as their sections over `V`, with `𝒪_X(V)` acting through the
comorphism of `j` followed by the structure morphism of `B`. -/
public def underlyingModulePushforwardIso {U X : Scheme.{u}} (j : U ⟶ X) (B : AlgebraSheaf U) :
    AlgebraSheaf.underlyingModule ((algebraPushforward j).obj B) ≅
      (Scheme.Modules.pushforward j).obj (AlgebraSheaf.underlyingModule B) :=
  Iso.refl _

/-- **[Stacks, Tag 01LC] for algebras:** the direct image of a quasi-coherent algebra sheaf
along a quasi-compact, quasi-separated morphism is quasi-coherent.  Stated at an open immersion,
which is the only case the extension algebra uses, and where quasi-separatedness is automatic. -/
@[ega "I 9.4.2" "(i), special case"]
public instance isQuasicoherent_algebraPushforward {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] [QuasiCompact j] (B : AlgebraSheaf U) [B.IsQuasicoherent] :
    ((algebraPushforward j).obj B).IsQuasicoherent :=
  have : QuasiSeparated j := inferInstance
  (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    (underlyingModulePushforwardIso j B).symm
    (RelativeMayerVietoris.pushforward_isQuasicoherent j (AlgebraSheaf.underlyingModule B))

/-- **The extension algebra `A ×_{j_*(A|_U)} j_*G` is quasi-coherent.**  This is the one remaining
step of the first piece of the algebra route to Tag 05JT and Tag 0817: with
`Stacks.AlgebraicGeometry.AlgebraOpenExtension.mono_extensionProjection` it says that the
extension is a quasi-coherent *subalgebra* of `A` whenever `φ` is a monomorphism.

Three hypotheses beyond quasi-coherence of `A` and `G`: the immersion is quasi-compact, which
is what Tag 01LC asks of the two direct images in the cospan, and the restriction
`(algebraPullback j).obj A` is quasi-coherent, which is not derived here -- see this file's
header. -/
public theorem isQuasicoherent_extensionAlgebra {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] [QuasiCompact j] (A : AlgebraSheaf X) [A.IsQuasicoherent]
    (G : AlgebraSheaf U) [G.IsQuasicoherent] (φ : G ⟶ (algebraPullback j).obj A)
    [((algebraPullback j).obj A).IsQuasicoherent] :
    (extensionAlgebra j A G φ).IsQuasicoherent :=
  isQuasicoherent_fibreProduct (extensionUnit j A) ((algebraPushforward j).map φ)

/-- Faithfulness check for `isQuasicoherent_extensionAlgebra`: the object concluded
quasi-coherent is literally the fibre product of
`Stacks.AlgebraicGeometry.AlgebraOpenExtension.extensionAlgebra`, namely the fibre product of
the adjunction unit `A ⟶ j_*(A|_U)` with the direct image `j_*φ`, and the hypotheses are the
three written out here together with quasi-compactness of the immersion. -/
example {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (A : AlgebraSheaf X) (G : AlgebraSheaf U) (φ : G ⟶ (algebraPullback j).obj A)
    (_hA : AlgebraSheaf.IsQuasicoherent A) (_hG : AlgebraSheaf.IsQuasicoherent G)
    (_hAU : AlgebraSheaf.IsQuasicoherent ((algebraPullback j).obj A)) :
    AlgebraSheaf.IsQuasicoherent
      (pullback (extensionUnit j A) ((algebraPushforward j).map φ)) :=
  isQuasicoherent_extensionAlgebra j A G φ

end Stacks.AlgebraicGeometry.AlgebraFibreProduct

end
