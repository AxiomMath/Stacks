module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.LisseEtaleRingedModules
public import StacksFrontier.AlgebraicGeometry.Stacks.ParasiticLisseEtaleVanishing
public import StacksFrontier.AlgebraicGeometry.Stacks.ParasiticPullbackVanishing

/-!
# Parasitic modules and vanishing of the pullback to the lisse-étale site (Stacks 07AR)

Let `𝒳` be an algebraic stack and `g : Sh(𝒳_{lisse,étale}) ⟶ Sh(𝒳_étale)` the morphism of ringed
topoi of **Stacks 0788** (1). A sheaf of `𝒪_𝒳`-modules on `𝒳_étale` *with the flat base change
property of* **Stacks 0762** is parasitic (**Stacks 0773**) exactly when its pullback `g^*F`
vanishes; this is part (1) of **Stacks 07AR**. Part (2) is the same statement for the flat-fppf
site, with no hypothesis, and is
`AlgebraicGeometry.Stack.FlatFppf.isParasitic_iff_isZero_pullbackModules`.

The lisse-étale site has the smooth objects of `𝒳` for its objects and the pullback along `g` is
restriction to them (`AlgebraicGeometry.Stack.LisseEtale.modulePullbackIso`), so the right-hand
side says exactly that the sections of `F` vanish at every smooth object. The two implications
are then `AlgebraicGeometry.Stack.LisseEtale.subsingleton_of_isParasitic` — a smooth object is
flat — and `AlgebraicGeometry.Stack.LisseEtale.isParasitic_of_subsingleton_smoothObject`, which
is where the flat base change property is used.

## Main definitions

* `AlgebraicGeometry.Stack.LisseEtale.ringedToposModulesHom`: the lisse-étale morphism of ringed
  topoi, presented as the datum the pullback of sheaves of modules is stated for.

## Main results

* `AlgebraicGeometry.Stack.LisseEtale.isParasitic_iff_isZero_pullbackModules`: **Stacks 07AR**
  part (1).
* `AlgebraicGeometry.Stack.isParasitic_iff_isZero_pullbackModules_lisseEtale_and_flatFppf`:
  **Stacks 07AR**, both parts conjoined.

## Implementation notes

The closure condition of **Stacks 07AK** (1) that the lisse-étale morphism of ringed topoi needs
is `AlgebraicGeometry.Stack.LisseEtale.closedUnderSmoothMorphisms`, a theorem for every
algebraic stack, so nothing here is conditional on it. The flat base change property is stated
for a chosen big étale site `E` of the same cardinal cutoff as `B`, which is the shape
`AlgebraicGeometry.Stack.HasFlatBaseChangeProperty` carries; part (1) is therefore read for an
arbitrary such `E`.

The identification of the pullback with restriction is
`AlgebraicGeometry.Stack.LisseEtale.modulePullbackIso` of
`StacksFrontier/AlgebraicGeometry/Stacks/LisseEtaleRingedModules.lean`, the étale instance of
`AlgebraicGeometry.Stack.subsiteModulePullbackIso` for an arbitrary continuous and cocontinuous
full subsite. `AlgebraicGeometry.Stack.LisseEtale.ringedToposModulesHom` below is that file's
`AlgebraicGeometry.Stack.subsiteRingedToposModulesHom` at the smooth objects, so that
identification applies to it as it stands.

## References

* [Stacks Project, Tag 0762](https://stacks.math.columbia.edu/tag/0762)
* [Stacks Project, Tag 0773](https://stacks.math.columbia.edu/tag/0773)
* [Stacks Project, Tag 0787](https://stacks.math.columbia.edu/tag/0787)
* [Stacks Project, Tag 0788](https://stacks.math.columbia.edu/tag/0788)
* [Stacks Project, Tag 07AR](https://stacks.math.columbia.edu/tag/07AR)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Sheaves.RingedToposModules

namespace AlgebraicGeometry.Stack

universe u w

namespace LisseEtale

attribute [local instance] hasSheafCompose_forget_ringCat hasSheafCompose_forget_commRingCat
  Stacks.hasSheafCompose_forget₂_commRingCat

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S) (𝒳 : Stack.AlgebraicStacks.{u, w} B S hS)

/-- **The lisse-étale morphism of ringed topoi of Stacks 0788 (1)(f)**, presented as the datum
the pullback of sheaves of modules of **Stacks 03D6** part (2) is stated for. The closure
condition of **Stacks 07AK** (1) is discharged by
`AlgebraicGeometry.Stack.LisseEtale.closedUnderSmoothMorphisms`, so this is unconditional. -/
noncomputable def ringedToposModulesHom :
    Stacks.Sheaves.RingedToposModules.RingedToposHom
      (ringedTopos.{u, w} B S hS 𝒳 (closedUnderSmoothMorphisms.{u, w} B S hS 𝒳))
      (etaleRingedTopos.{u, w} B S hS 𝒳) :=
  haveI := isContinuous_inclusion.{u, w} B S hS 𝒳 (closedUnderSmoothMorphisms.{u, w} B S hS 𝒳)
  haveI := isCocontinuous_inclusion.{u, w} B S hS 𝒳 (closedUnderSmoothMorphisms.{u, w} B S hS 𝒳)
  subsiteRingedToposModulesHom B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
    (etaleTopology B) (etaleTopology_le_topology B) (smoothObject.{u, w} B S hS 𝒳)

/-- **Stacks 07AR** (1). A sheaf of modules on the étale site of an algebraic stack which has the
flat base change property of **Stacks 0762** is parasitic exactly when its pullback along the
lisse-étale morphism of ringed topoi of **Stacks 0788** (1) vanishes.

The pullback is restriction to the smooth objects
(`AlgebraicGeometry.Stack.LisseEtale.modulePullbackIso`), so the right-hand side says that the
sections of `F` vanish at every smooth object. A smooth object is flat, which gives one
implication with no hypothesis; the converse is where the flat base change property is used, to
carry the vanishing along a flat arrow out of an object covering a given flat object. -/
@[stacks 07AR "part (1), the lisse-étale site"]
theorem isParasitic_iff_isZero_pullbackModules
    (F : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u, u}
      (etaleRingedTopos.{u, w} B S hS 𝒳).O))
    (hfbc : HasFlatBaseChangeProperty B E h S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
      (etaleTopology B) (etaleTopology_le_topology B) F.val) :
    IsParasitic.{u, w, u} B S hS 𝒳 .etale F.val ↔
      IsZero ((RingedToposHom.pullbackModules.{u, u, u, u + 1, u, u + 1}
        (ringedToposModulesHom.{u, w} B S hS 𝒳)).obj F) := by
  have := isContinuous_inclusion.{u, w} B S hS 𝒳 (closedUnderSmoothMorphisms.{u, w} B S hS 𝒳)
  have := isCocontinuous_inclusion.{u, w} B S hS 𝒳 (closedUnderSmoothMorphisms.{u, w} B S hS 𝒳)
  refine Iff.trans ?_ ((modulePullbackIso B S hS 𝒳).app F).isZero_iff.symm
  refine Iff.trans ?_ (isZero_sheafOfModules_iff_forall_subsingleton
    ((subsiteRingedToposModuleRestriction B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
      (etaleTopology B) (etaleTopology_le_topology B) (smoothObject.{u, w} B S hS 𝒳)).obj F)).symm
  constructor
  · intro hpar V
    exact subsingleton_of_isParasitic B S hS F.val hpar V.unop.obj V.unop.property
  · intro hvan
    exact isParasitic_of_subsingleton_smoothObject B E h S hS F.val F.isSheaf hfbc
      fun x hx => hvan (op ⟨x, hx⟩)

end LisseEtale

attribute [local instance] hasSheafCompose_forget_ringCat hasSheafCompose_forget_commRingCat
  Stacks.hasSheafCompose_forget₂_commRingCat FlatFppf.isContinuous_inclusion_topology
  FlatFppf.isCocontinuous_inclusion_topology FlatFppf.hasSheafify_addCommGrpCat
  FlatFppf.wEqualsLocallyBijective_addCommGrpCat

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S) (𝒳 : Stack.AlgebraicStacks.{u, w} B S hS)

/-- **Stacks 07AR, the whole statement.** For an algebraic stack `𝒳`:

* (1) a sheaf of `𝒪_𝒳`-modules `F` on `𝒳_étale` with the flat base change property of
  **Stacks 0762** is parasitic exactly when `g^*F = 0` for the lisse-étale morphism of ringed
  topoi of **Stacks 0788** (1); and
* (2) a sheaf of `𝒪_𝒳`-modules `G` on `𝒳_fppf` is parasitic exactly when `g^*G = 0` for the
  flat-fppf morphism of ringed topoi of **Stacks 0788** (2), with no hypothesis.

The two conjuncts are
`AlgebraicGeometry.Stack.LisseEtale.isParasitic_iff_isZero_pullbackModules` and
`AlgebraicGeometry.Stack.FlatFppf.isParasitic_iff_isZero_pullbackModules`. -/
@[stacks 07AR "the whole statement: parts (1) and (2) conjoined"]
theorem isParasitic_iff_isZero_pullbackModules_lisseEtale_and_flatFppf
    (F : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u, u}
      (LisseEtale.etaleRingedTopos.{u, w} B S hS 𝒳).O))
    (hfbc : HasFlatBaseChangeProperty B E h S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
      (etaleTopology B) (etaleTopology_le_topology B) F.val)
    (G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u, u}
      (FlatFppf.fppfRingedTopos B S hS 𝒳).O)) :
    (IsParasitic.{u, w, u} B S hS 𝒳 .etale F.val ↔
        IsZero ((RingedToposHom.pullbackModules.{u, u, u, u + 1, u, u + 1}
          (LisseEtale.ringedToposModulesHom.{u, w} B S hS 𝒳)).obj F)) ∧
      (IsParasitic.{u, w, u} B S hS 𝒳 .fppf G.val ↔
        IsZero ((RingedToposHom.pullbackModules.{u, u, u, u + 1, u, u + 1}
          (FlatFppf.ringedToposModulesHom B S hS 𝒳)).obj G)) :=
  ⟨LisseEtale.isParasitic_iff_isZero_pullbackModules.{u, w} B E h S hS 𝒳 F hfbc,
    FlatFppf.isParasitic_iff_isZero_pullbackModules B S hS 𝒳 G⟩

end AlgebraicGeometry.Stack

end
