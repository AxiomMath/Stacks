module

public import StacksFrontier.AlgebraicGeometry.Stacks.FibreEssentialSmallness
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Descent.FibredTensor
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.InternalHomSiteAgreement
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LocallyQuasicoherentInternalHom
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.QuasicoherentDirectImage
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.EssentiallySmallTensorHom

/-!
# The quasi-coherent internal Hom on an algebraic stack (Stacks 0GQN)

Let `𝒳` be an algebraic stack, `F` an `𝒪_𝒳`-module and `G` a quasi-coherent `𝒪_𝒳`-module.
**Stacks 0GQN** says that the internal Homs `SheafHom_{𝒪_𝒳}(F, G)` computed in
`Mod(𝒳_étale, 𝒪_𝒳)` and in `Mod(𝒪_𝒳)` agree, that for `F` of finite presentation the common
value lies in `LQCoh^fbc(𝒪_𝒳)`, and that the quasi-coherent module
`hom(F, G) = Q(SheafHom_{𝒪_𝒳}(F, G))`, with `Q` the coherator of Stacks 0781, satisfies
`Hom(H, hom(F, G)) = Hom(H ⊗_{𝒪_𝒳} F, G)` for `H` quasi-coherent.

This file proves the agreement and the universal property.  Neither needs `F` of finite
presentation nor `G` quasi-coherent: the agreement holds because the internal Hom of Stacks 03EM
read at module universe `u` depends only on the underlying presheaves, and the universal property
is the adjunction of the coherator followed by the tensor–Hom correspondence of Stacks 03EO.  The
membership of `SheafHom_{𝒪_𝒳}(F, G)` in `LQCoh^fbc(𝒪_𝒳)` is Stacks 0771 (7) and is not proved here.

## Main definitions

* `AlgebraicGeometry.Stack.AlgebraicStacks.fppfInternalHom`: `SheafHom_{𝒪_𝒳}(F, G)` in
  `Mod(𝒪_𝒳)`.
* `AlgebraicGeometry.Stack.AlgebraicStacks.quasicoherentHom`: `hom(F, G)`.
* `AlgebraicGeometry.Stack.AlgebraicStacks.quasicoherentHomEquiv`: its universal property.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.fppfInternalHom_presheaf_eq_etaleInternalHom`: the
  agreement of the étale and the fppf internal Hom.

## Implementation notes

`AlgebraicGeometry.Stack.AlgebraicStacks.quasicoherentHomOf` and
`AlgebraicGeometry.Stack.AlgebraicStacks.quasicoherentHomOfEquiv` are stated for an arbitrary right
adjoint of the inclusion `QCoh(𝒪_𝒳) ⊆ Mod(𝒪_𝒳)`; the registered forms are their values at the
canonical coherator `AlgebraicGeometry.Stack.AlgebraicStacks.coheratorAdjunction`.

## References

* [Stacks Project, Tag 0GQN](https://stacks.math.columbia.edu/tag/0GQN)
* [Stacks Project, Tag 0781](https://stacks.math.columbia.edu/tag/0781)
* [Stacks Project, Tag 03EO](https://stacks.math.columbia.edu/tag/03EO)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u w

namespace AlgebraicGeometry.Stack.AlgebraicStacks

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 : AlgebraicStacks.{u, w} B S hS)

attribute [local instance] FibredSite.hasWeakSheafify_associatedTopology
  FibredSite.wEqualsLocallyBijective_associatedTopology

/-- The ringed sites attached to an algebraic stack are essentially small. -/
instance essentiallySmall_ringedSite (τ : SiteKind) :
    EssentiallySmall.{u} (FibredSite.ringedSite B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids τ).C :=
  inferInstanceAs (EssentiallySmall.{u} 𝒳.val.val.obj)

/-- Sheafification of abelian presheaves exists on the ringed sites of an algebraic stack. -/
instance hasWeakSheafify_ringedSite (τ : SiteKind) :
    HasWeakSheafify (FibredSite.ringedSite B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids τ).J AddCommGrpCat.{u} :=
  FibredSite.hasWeakSheafify_associatedTopology B S hS _ τ

/-- On the ringed sites of an algebraic stack the weak equivalences of abelian presheaves are the
locally bijective morphisms. -/
instance wEqualsLocallyBijective_ringedSite (τ : SiteKind) :
    (FibredSite.ringedSite B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids τ).J.WEqualsLocallyBijective AddCommGrpCat.{u} :=
  FibredSite.wEqualsLocallyBijective_associatedTopology B S hS _ τ

/-- The internal Hom `SheafHom_{𝒪_𝒳}(F, G)` of Stacks 03EM in `Mod(𝒪_𝒳)`, at module universe
`u`. -/
abbrev fppfInternalHom (F G : Stack.fppfModules B S hS 𝒳) : Stack.fppfModules B S hS 𝒳 :=
  RingedSite.internalHomSheafSmall.{u}
    (FibredSite.ringedSite B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids .fppf) F G

/-- The tensor product `H ⊗_{𝒪_𝒳} F` in `Mod(𝒪_𝒳)`, at module universe `u`: the sheafification
for the fppf topology of the objectwise tensor product. -/
abbrev fppfTensor (H F : Stack.fppfModules B S hS 𝒳) : Stack.fppfModules B S hS 𝒳 :=
  ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
    (FibredSite.ringedSite B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids .fppf).O).obj H).obj F

/-- **Stacks 0GQN**, the agreement of the two internal Homs at module universe `u`.  The internal
Hom `SheafHom_{𝒪_𝒳}(F, G)` computed in `Mod(𝒳_étale, 𝒪_𝒳)` and the one computed in `Mod(𝒪_𝒳)`
have the same underlying presheaf of abelian groups, for arbitrary modules `F` and `G` on the fppf
site; the source states it for `F` of finite presentation and `G` quasi-coherent.

Both are the internal Hom of Stacks 03EM read in the universe `u` of the module sections, and
that construction depends only on the underlying presheaves of `F`, `G` and of the structure
sheaf, none of which changes with the topology. -/
@[stacks 0GQN "the agreement of the internal Homs of Mod(𝒳_étale, 𝒪_𝒳) and Mod(𝒪_𝒳), for \
arbitrary F and G"]
theorem fppfInternalHom_presheaf_eq_etaleInternalHom (F G : Stack.fppfModules B S hS 𝒳) :
    (fppfInternalHom B S hS 𝒳 F G).val.presheaf =
      (etaleInternalHom B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
        (FibredSite.restrictSiteModules B S hS _ _ .etale F)
        (FibredSite.restrictSiteModules B S hS _ _ .etale G)).val.presheaf :=
  rfl

variable {𝒳} {Q : Stack.fppfModules B S hS 𝒳 ⥤ quasicoherentModules B S hS 𝒳}
  (adj : quasicoherentInclusion B S hS 𝒳 ⊣ Q)

variable (Q) in
/-- The quasi-coherent module `hom(F, G) = Q(SheafHom_{𝒪_𝒳}(F, G))` of **Stacks 0GQN**, for a
right adjoint `Q` of the inclusion of `QCoh(𝒪_𝒳)` into `Mod(𝒪_𝒳)`. -/
abbrev quasicoherentHomOf (F G : Stack.fppfModules B S hS 𝒳) : quasicoherentModules B S hS 𝒳 :=
  Q.obj (fppfInternalHom B S hS 𝒳 F G)

/-- **The universal property of `hom(F, G)`** (Stacks 0GQN): for `H` quasi-coherent,
`Hom(H, hom(F, G)) = Hom(H ⊗ F, G)`.  It is the adjunction of `Q` followed by the tensor–Hom
correspondence of Stacks 03EO at module universe `u`,
`AlgebraicGeometry.RingedSite.tensorHomEquivInternalHomSheafSmall`. -/
def quasicoherentHomOfEquiv (F G : Stack.fppfModules B S hS 𝒳)
    (H : quasicoherentModules B S hS 𝒳) :
    (H ⟶ quasicoherentHomOf B S hS Q F G) ≃
      (fppfTensor B S hS 𝒳 ((quasicoherentInclusion B S hS 𝒳).obj H) F ⟶ G) :=
  (adj.homEquiv _ _).symm.trans
    (RingedSite.tensorHomEquivInternalHomSheafSmall.{u}
      (FibredSite.ringedSite B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids .fppf)
      H.obj F G).symm

variable (𝒳) in
/-- **The quasi-coherent internal Hom `hom(F, G) = Q(SheafHom_{𝒪_𝒳}(F, G))` of Stacks 0GQN**, with
`Q` the coherator of Stacks 0781. -/
abbrev quasicoherentHom (F G : Stack.fppfModules B S hS 𝒳) : quasicoherentModules B S hS 𝒳 :=
  quasicoherentHomOf B S hS (coherator B S hS 𝒳) F G

variable (𝒳) in
/-- **The universal property of `hom(F, G)`** (Stacks 0GQN): for `H` quasi-coherent,
`Hom_𝒳(H, hom(F, G)) = Hom_𝒳(H ⊗_{𝒪_𝒳} F, G)`.  This is
`AlgebraicGeometry.Stack.AlgebraicStacks.quasicoherentHomOfEquiv` at the coherator; it holds for
arbitrary `F` and `G`. -/
@[stacks 0GQN "the universal property of hom(F, G) = Q(SheafHom(F, G)), for arbitrary F and G"]
def quasicoherentHomEquiv (F G : Stack.fppfModules B S hS 𝒳)
    (H : quasicoherentModules B S hS 𝒳) :
    (H ⟶ quasicoherentHom B S hS 𝒳 F G) ≃
      (fppfTensor B S hS 𝒳 ((quasicoherentInclusion B S hS 𝒳).obj H) F ⟶ G) :=
  quasicoherentHomOfEquiv B S hS (coheratorAdjunction B S hS 𝒳) F G H

end AlgebraicGeometry.Stack.AlgebraicStacks
