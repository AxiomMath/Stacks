module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposLowerShriekUnit
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackLowerShriek
public import StacksFrontier.CategoryTheory.Sites.Continuous
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatFppfInclusion
public import StacksFrontier.AlgebraicGeometry.Stacks.LisseEtaleClosure
public import StacksFrontier.AlgebraicGeometry.Stacks.LisseEtaleInclusion
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Sites.Equivalence
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite

/-!
# The lower shriek on modules for a full subsite, and the lisse-étale and flat-fppf cases

Let `p : 𝒳 ⥤ (Sch/S)` be a category fibred in groupoids carrying the site of **Stacks 06TP**, and
let `P` cut out a full subcategory whose inclusion is continuous and cocontinuous for the
inherited topology. `StacksFrontier/AlgebraicGeometry/Stacks/SubcategoryRingedTopos.lean` assembles
from this the morphism of ringed topoi `g : (Sh(𝒳'), O_{𝒳'}) ⟶ (Sh(𝒳), O_𝒳)` whose inverse image
is restriction along the inclusion and whose structure map is an isomorphism.

This file produces the **lower shriek on sheaves of modules** for that `g`: the pullback `g^*` of
**Stacks 03D6** admits a left adjoint

`g_! : Mod(𝒳', O_{𝒳'}) ⟶ Mod(𝒳, O_𝒳)`,

together with the adjunction `g_! ⊣ g^*`. The two cases the source names, the lisse-étale site and
the flat-fppf site of an algebraic stack, are its two instantiations.

## Which clauses of Stacks 0789 this is

Each of 0789 (1) and 0789 (2) makes four assertions about `g_!` on sheaves of modules:
(i) it exists, (ii) it is left adjoint to `g^*`, (iii) it agrees with `g_!` on abelian sheaves,
and (iv) `g^*g_! = id`. **Assertions (i), (ii) and (iv) of both clauses are here**, and the tag
sits clause-keyed on them. Assertion (iii) is *not*: that `g_!` on modules agrees with `g_!` on
abelian sheaves is **Stacks 07AJ** together with the comparison transformation of **Stacks 0798**
(`Stacks.SheafOfModules.lowerShriekForgetComparison`, in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/LowerShriekForget.lean`), of which only the
transformation and its characterisation are available; 07AJ is not formalized anywhere in the
library.

Assertion (iv) is proved here by a different route from the source's. The source derives it from
(iii) together with `g^* = g^{-1}` and the corresponding equality for abelian sheaves in
Stacks 0788; `g^* = g^{-1}` is a strictly stronger statement than anything the construction of
`g^*` supplies here (see the implementation notes of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/RingedToposPullbackLowerShriek.lean`), so instead
the adjoint triple `g_! ⊣ g^* ⊣ g_*` is used: the unit of `g_! ⊣ g^*` is an isomorphism exactly
when the counit of the Stacks 03D7 adjunction `g^* ⊣ g_*` is, and that adjunction does not mention
`g_!`. The general statement is
`AlgebraicGeometry.RingedToposHom.isIso_lowerShriekAdjPullbackModules_unit`, in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/RingedToposLowerShriekUnit.lean`.

So 0789 is only partly formalized — (iii) is missing from both clauses — and the tag notes
say which assertion each declaration carries.

The two instantiations assume nothing beyond the data of an algebraic stack. The closure property
of **Stacks 07AK** that the morphism of ringed topoi `g` needs is discharged for every algebraic
stack by `AlgebraicGeometry.Stack.LisseEtale.closedUnderSmoothMorphisms` and
`AlgebraicGeometry.Stack.FlatFppf.closedUnderFlatMorphisms`, and essential smallness of the
category underlying the stack, `EssentiallySmall.{u} 𝒳.val.val.obj`, is the instance
`AlgebraicGeometry.Stack.essentiallySmall_obj_algebraicStack` of
`StacksFrontier/AlgebraicGeometry/Stacks/FibreEssentialSmallness.lean`, which instance search
supplies at each of the six tagged declarations. The general subsite statements earlier in the
file, and the two auxiliary declarations in each of the two namespaces, keep both as hypotheses,
as the bridge pattern of `StacksFrontier/AlgebraicGeometry/Stacks/LisseEtaleInclusion.lean` and
`StacksFrontier/AlgebraicGeometry/Stacks/FlatFppfInclusion.lean` does, and are untagged.

## Main definitions

* `AlgebraicGeometry.Stack.subsiteModulePullback`: the pullback `g^*` of sheaves of modules along
  the morphism of ringed topoi of a full subsite.
* `AlgebraicGeometry.Stack.subsiteModuleLowerShriek` and
  `AlgebraicGeometry.Stack.subsiteModuleLowerShriekAdjunction`: the functor `g_!` and the
  adjunction `g_! ⊣ g^*`.
* `AlgebraicGeometry.Stack.LisseEtale.moduleLowerShriek`,
  `AlgebraicGeometry.Stack.LisseEtale.moduleLowerShriekAdjunction` and the flat-fppf siblings
  `AlgebraicGeometry.Stack.FlatFppf.moduleLowerShriek`,
  `AlgebraicGeometry.Stack.FlatFppf.moduleLowerShriekAdjunction`: the two instantiations, which
  are assertions (i) and (ii) of **Stacks 0789** (1) and (2).

## Main results

* `AlgebraicGeometry.Stack.isIso_fSharpInverseImage_subsiteRingedToposHom`: the structure map of
  `g` is an isomorphism, which is the ringed half of Stacks 0788 read as invertibility.
* `AlgebraicGeometry.Stack.isRightAdjoint_subsiteModulePullback`: `g^*` has a left adjoint.
* `AlgebraicGeometry.Stack.LisseEtale.isRightAdjoint_modulePullback` and
  `AlgebraicGeometry.Stack.FlatFppf.isRightAdjoint_modulePullback'`: the same for the two sites
  of the source.
* `AlgebraicGeometry.Stack.isIso_subsiteToposMorphism_adj_counit`: the counit `g⁻¹g_* ⟶ id` of the
  morphism of topoi of a full subsite is an isomorphism, which is **Stacks 00XT** for the
  inclusion.
* `AlgebraicGeometry.Stack.isIso_subsiteModuleLowerShriekAdjunction_unit` and its two
  instantiations `AlgebraicGeometry.Stack.LisseEtale.isIso_moduleLowerShriekAdjunction_unit`,
  `AlgebraicGeometry.Stack.FlatFppf.isIso_moduleLowerShriekAdjunction_unit`: assertion (iv)
  `g^*g_! = id` of **Stacks 0789** (1) and (2).

## Implementation notes

The criterion applied is
`AlgebraicGeometry.RingedToposHom.isRightAdjoint_pullbackModules`: the pullback of sheaves of
modules is the inverse image followed by extension of scalars along the structure map, and each
factor has a left adjoint here — the inverse image because it is restriction along the inclusion
of an essentially small full subsite, extension of scalars because the structure map is
invertible. Nothing identifies `g^*` with restriction, and nothing needs to — not even for
`g^*g_! = id`, which the source does prove that way.

The sheafification hypotheses are stated for `AddCommGrpCat.{u}`, the universe of the sections of
the structure sheaf of **Stacks 06TV**, whereas
`StacksFrontier/AlgebraicGeometry/Stacks/SubcategoryRingedTopos.lean` needs them only at
`AddCommGrpCat.{max u v w}`. Both follow from essential smallness of the site in `Type u`, through
`CategoryTheory.hasSheafifyEssentiallySmallSite` and
`CategoryTheory.GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall`, whose universe
arguments have to be given explicitly: the universe of the coefficients and the two universes of
the site are independent here, and unification does not determine them.

## References

* [Stacks Project, Tag 00XT](https://stacks.math.columbia.edu/tag/00XT)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
* [Stacks Project, Tag 06TP](https://stacks.math.columbia.edu/tag/06TP)
* [Stacks Project, Tag 06TV](https://stacks.math.columbia.edu/tag/06TV)
* [Stacks Project, Tag 0788](https://stacks.math.columbia.edu/tag/0788)
* [Stacks Project, Tag 0789](https://stacks.math.columbia.edu/tag/0789)
* [Stacks Project, Tag 07AK](https://stacks.math.columbia.edu/tag/07AK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.RingedToposModules

namespace AlgebraicGeometry.Stack

universe u v w t

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X : Type v} [Category.{w} X] (p : X ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)
  (τ : GrothendieckTopology B.Schemes) (hτ : τ ≤ B.topology) (P : ObjectProperty X)

section

variable [EssentiallySmall.{u} X]

/-- Sheafification of presheaves of abelian groups with sections in the universe of the structure
sheaf of **Stacks 06TV** exists on the site of **Stacks 06TP**, because that site is essentially
small in that universe. -/
instance hasSheafifyAddCommGrpCat_associatedTopology :
    HasSheafify (associatedTopology B S hS p τ) AddCommGrpCat.{u} := by
  exact hasSheafifyEssentiallySmallSite.{w, u, v, u + 1, u} _ _

/-- On the site of **Stacks 06TP**, sheafification of presheaves of abelian groups inverts exactly
the locally bijective morphisms. -/
instance wEqualsLocallyBijective_associatedTopology :
    (associatedTopology B S hS p τ).WEqualsLocallyBijective AddCommGrpCat.{u} := by
  exact GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{w, u, v, u + 1, u} _

/-- Sheafification of presheaves of abelian groups exists on a full subsite, which is again
essentially small. -/
instance hasSheafifyAddCommGrpCat_subsiteTopology :
    HasSheafify (subsiteTopology B S hS p τ P) AddCommGrpCat.{u} := by
  exact hasSheafifyEssentiallySmallSite.{w, u, v, u + 1, u} _ _

/-- On a full subsite, sheafification of presheaves of abelian groups inverts exactly the locally
bijective morphisms. -/
instance wEqualsLocallyBijective_subsiteTopology :
    (subsiteTopology B S hS p τ P).WEqualsLocallyBijective AddCommGrpCat.{u} := by
  exact GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{w, u, v, u + 1, u} _

variable [P.ι.IsContinuous (subsiteTopology B S hS p τ P) (associatedTopology B S hS p τ)]
  [P.ι.IsCocontinuous (subsiteTopology B S hS p τ P) (associatedTopology B S hS p τ)]

/-- **The structure map of the morphism of ringed topoi of a full subsite is an isomorphism.** Its
inverse-image form is the comparison `AlgebraicGeometry.Stack.subsiteStructureSheafIso` of the
inverse image of the structure sheaf with the restricted structure sheaf, which is an isomorphism
by construction. This is the ringed half of **Stacks 0788** read as invertibility, and it is what
makes extension of scalars along the structure map an equivalence. -/
theorem isIso_fSharpInverseImage_subsiteRingedToposHom :
    IsIso (subsiteRingedToposHom B S hS p hp τ hτ P).fSharpInverseImage := by
  rw [fSharpInverseImage_subsiteRingedToposHom]
  exact (subsiteStructureSheafIso B S hS p hp τ hτ P).isIso_hom

/-- **The inverse image of sheaves of modules along the morphism of topoi of a full subsite has a
left adjoint.** The inverse image is restriction along the inclusion, up to the comparison of the
inverse-image sheaf of rings with the restricted one, and restriction along a continuous functor
whose source is essentially small has a left adjoint. -/
instance isRightAdjoint_inverseImageModules_subsiteToposMorphism :
    (inverseImageModules (subsiteToposMorphism B S hS p τ P)
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (associatedRingedTopos B S hS p hp τ hτ).O)).IsRightAdjoint :=
  isRightAdjoint_pullbackModuleFunctor_restriction (subsiteTopology B S hS p τ P)
    (associatedTopology B S hS p τ) P.ι
    (Stacks.SheafOfModules.Tensor.ringSheaf (associatedRingedTopos B S hS p hp τ hτ).O)

/-- **The pullback `g^*` of sheaves of modules** along the morphism of ringed topoi of a full
subsite: `g^*G = O_{𝒳'} ⊗_{g⁻¹O_𝒳} g⁻¹G`, which is **Stacks 03D6** part (2) for `g`. -/
abbrev subsiteModulePullback :
    SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (associatedRingedTopos B S hS p hp τ hτ).O) ⥤
      SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (subsiteRingedTopos B S hS p hp τ hτ P).O) :=
  (subsiteRingedToposHom B S hS p hp τ hτ P).toModulesHom.pullbackModules

/-- **The pullback of sheaves of modules along the morphism of ringed topoi of a full subsite has
a left adjoint.** This is the existence assertion of the first sentences of **Stacks 0789** (1)
and (2), stated once for an arbitrary continuous and cocontinuous full subsite.

The pullback is the inverse image followed by extension of scalars along the structure map; the
first factor has a left adjoint because the inverse image is restriction along the inclusion of an
essentially small site, and the second because the structure map is an isomorphism. -/
instance isRightAdjoint_subsiteModulePullback :
    (subsiteModulePullback B S hS p hp τ hτ P).IsRightAdjoint :=
  have := isIso_fSharpInverseImage_subsiteRingedToposHom B S hS p hp τ hτ P
  RingedToposHom.isRightAdjoint_pullbackModules (subsiteRingedToposHom B S hS p hp τ hτ P)
    (isRightAdjoint_inverseImageModules_subsiteToposMorphism B S hS p hp τ hτ P)

/-- **The lower shriek `g_!` on sheaves of modules** for a full subsite: the left adjoint of the
pullback `g^*`. -/
abbrev subsiteModuleLowerShriek :
    SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (subsiteRingedTopos B S hS p hp τ hτ P).O) ⥤
      SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (associatedRingedTopos B S hS p hp τ hτ).O) :=
  (subsiteRingedToposHom B S hS p hp τ hτ P).lowerShriekModules

/-- **The adjunction `g_! ⊣ g^*`** on sheaves of modules for a full subsite. -/
abbrev subsiteModuleLowerShriekAdjunction :
    subsiteModuleLowerShriek B S hS p hp τ hτ P ⊣ subsiteModulePullback B S hS p hp τ hτ P :=
  (subsiteRingedToposHom B S hS p hp τ hτ P).lowerShriekAdjPullbackModules

/-- **The counit `g⁻¹g_* ⟶ id` of the morphism of topoi of a full subsite is an isomorphism**,
which is **Stacks 00XT** for the inclusion: it is continuous, cocontinuous and fully faithful. -/
theorem isIso_subsiteToposMorphism_adj_counit :
    IsIso (subsiteToposMorphism B S hS p τ P).adj.counit := by
  have : ∀ F : P.FullSubcategoryᵒᵖ ⥤ Type u, P.ι.op.HasPointwiseRightKanExtension F :=
    fun F Y => by
      have := hasLimitsOfShape_of_essentiallySmall.{u} (StructuredArrow Y P.ι.op) (Type u)
      infer_instance
  exact Functor.isIso_sheafAdjunctionCocontinuous_counit P.ι (Type u)
    (subsiteTopology B S hS p τ P) (associatedTopology B S hS p τ)

/-- **`g^*g_! = id` on sheaves of modules for a full subsite**: the unit of the adjunction
`g_! ⊣ g^*` is an isomorphism. This is the assertion `g^*g_! = \text{id}` of the clauses of
**Stacks 0789**, stated once for an arbitrary continuous and cocontinuous full subsite.

The source derives it from `g^* = g^{-1}` and the corresponding equality for abelian sheaves;
neither is used. The adjoint triple `g_! ⊣ g^* ⊣ g_*` reduces it to the counit of `g^* ⊣ g_*`
being an isomorphism, and that holds because the inverse-image structure map of `g` is invertible
and the counit `g⁻¹g_* ⟶ id` on sheaves of sets is — see
`AlgebraicGeometry.RingedToposHom.isIso_lowerShriekAdjPullbackModules_unit`. -/
theorem isIso_subsiteModuleLowerShriekAdjunction_unit :
    IsIso (subsiteModuleLowerShriekAdjunction B S hS p hp τ hτ P).unit :=
  have := isIso_fSharpInverseImage_subsiteRingedToposHom B S hS p hp τ hτ P
  have : IsIso (subsiteRingedToposHom B S hS p hp τ hτ P).toToposHom.adj.counit :=
    isIso_subsiteToposMorphism_adj_counit B S hS p τ P
  RingedToposHom.isIso_lowerShriekAdjPullbackModules_unit
    (subsiteRingedToposHom B S hS p hp τ hτ P)

end

/-! ### The lisse-étale site -/

namespace LisseEtale

variable (𝒳 : Stack.AlgebraicStacks.{u, t} B S hS)

section

variable [EssentiallySmall.{u} 𝒳.val.val.obj]

/-- **The pullback `g^*` of sheaves of modules along the lisse-étale morphism of ringed topoi**:
`g^*G = O_{𝒳_{lisse,étale}} ⊗_{g⁻¹O_𝒳} g⁻¹G`. The closure property of **Stacks 07AK** (1) that
the morphism of ringed topoi needs is
`AlgebraicGeometry.Stack.LisseEtale.closedUnderSmoothMorphisms`, which holds for every algebraic
stack. -/
noncomputable abbrev modulePullback :=
  (ringedToposMorphism.{u, t} B S hS 𝒳
    (closedUnderSmoothMorphisms.{u, t} B S hS 𝒳)).toModulesHom.pullbackModules

/-- **Stacks 0789 (1), existence**: the pullback of sheaves of modules along the lisse-étale
morphism of ringed topoi admits a left adjoint. -/
theorem isRightAdjoint_modulePullback :
    (modulePullback.{u, t} B S hS 𝒳).IsRightAdjoint :=
  have := isContinuous_inclusion.{u, t} B S hS 𝒳 (closedUnderSmoothMorphisms.{u, t} B S hS 𝒳)
  have := isCocontinuous_inclusion.{u, t} B S hS 𝒳 (closedUnderSmoothMorphisms.{u, t} B S hS 𝒳)
  isRightAdjoint_subsiteModulePullback B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
    (etaleTopology B) (etaleTopology_le_topology B) (smoothObject.{u, t} B S hS 𝒳)

end

/-! Essential smallness of the category underlying an algebraic stack is a theorem, the instance
`AlgebraicGeometry.Stack.essentiallySmall_obj_algebraicStack`, so the three declarations below
take only the data of the stack. The two above keep it as a hypothesis, their interfaces being
fixed. -/

/-- **The functor `g_!` of Stacks 0789 (1) on sheaves of modules**: the left adjoint of the
pullback `g^*` along the lisse-étale morphism of ringed topoi. -/
@[stacks 0789 "part (1), existence of the functor `g_!` on sheaves of modules for the \
lisse-étale site of an arbitrary algebraic stack"]
noncomputable abbrev moduleLowerShriek :=
  haveI := isRightAdjoint_modulePullback.{u, t} B S hS 𝒳
  (ringedToposMorphism.{u, t} B S hS 𝒳
    (closedUnderSmoothMorphisms.{u, t} B S hS 𝒳)).lowerShriekModules

/-- **The adjunction `g_! ⊣ g^*` of Stacks 0789 (1) on sheaves of modules.** -/
@[stacks 0789 "part (1), left adjointness of `g_!` to `g^*` on sheaves of modules for the \
lisse-étale site of an arbitrary algebraic stack"]
noncomputable abbrev moduleLowerShriekAdjunction :
    moduleLowerShriek.{u, t} B S hS 𝒳 ⊣ modulePullback.{u, t} B S hS 𝒳 :=
  haveI := isRightAdjoint_modulePullback.{u, t} B S hS 𝒳
  (ringedToposMorphism.{u, t} B S hS 𝒳
    (closedUnderSmoothMorphisms.{u, t} B S hS 𝒳)).lowerShriekAdjPullbackModules

/-- **Stacks 0789 (1), `g^*g_! = id`**: the unit of the adjunction `g_! ⊣ g^*` on sheaves of
modules for the lisse-étale site is an isomorphism. -/
@[stacks 0789 "part (1), `g^*g_! = id` on sheaves of modules for the lisse-étale site of an \
arbitrary algebraic stack"]
theorem isIso_moduleLowerShriekAdjunction_unit :
    IsIso (moduleLowerShriekAdjunction.{u, t} B S hS 𝒳).unit :=
  have := isContinuous_inclusion.{u, t} B S hS 𝒳 (closedUnderSmoothMorphisms.{u, t} B S hS 𝒳)
  have := isCocontinuous_inclusion.{u, t} B S hS 𝒳 (closedUnderSmoothMorphisms.{u, t} B S hS 𝒳)
  isIso_subsiteModuleLowerShriekAdjunction_unit B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
    (etaleTopology B) (etaleTopology_le_topology B) (smoothObject.{u, t} B S hS 𝒳)

end LisseEtale

/-! ### The flat-fppf site -/

namespace FlatFppf

variable (𝒳 : Stack.AlgebraicStacks.{u, t} B S hS)

-- the inclusion of the flat objects is continuous and cocontinuous for the inherited topology
-- with no hypothesis, the closure property of **Stacks 07AK** (1) being a theorem here; the
-- general subsite declarations above ask for the two as instances
attribute [local instance] isContinuous_inclusion' isCocontinuous_inclusion'

section

variable [EssentiallySmall.{u} 𝒳.val.val.obj]

/-- **The pullback `g^*` of sheaves of modules along the flat-fppf morphism of ringed topoi**:
`g^*G = O_{𝒳_{flat,fppf}} ⊗_{g⁻¹O_𝒳} g⁻¹G`. The closure property of **Stacks 07AK** (1) that the
morphism of ringed topoi needs is
`AlgebraicGeometry.Stack.FlatFppf.closedUnderFlatMorphisms`, which holds for every algebraic
stack. -/
noncomputable abbrev modulePullback :=
  subsiteModulePullback B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids B.topology le_rfl
    (objectProperty B S hS 𝒳)

/-- **Stacks 0789 (2), existence**: the pullback of sheaves of modules along the flat-fppf
morphism of ringed topoi admits a left adjoint.

This is the assertion for `AlgebraicGeometry.Stack.FlatFppf.modulePullback`, the pullback read
through the inclusion of the flat objects as a subsite.
`AlgebraicGeometry.Stack.FlatFppf.isRightAdjoint_modulePullback` of
`StacksFrontier.AlgebraicGeometry.Stacks.FlatFppfModuleShriek` is the assertion for the other
spelling of `g^*`, the source's
`Stacks.Sheaves.RingedToposModules.pullbackModules` of
`AlgebraicGeometry.Stack.FlatFppf.ringedToposModulesHom`; the two functors are identified by
`AlgebraicGeometry.Stack.FlatFppf.modulePullbackIso`. -/
theorem isRightAdjoint_modulePullback' :
    (modulePullback B S hS 𝒳).IsRightAdjoint :=
  isRightAdjoint_subsiteModulePullback B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
    B.topology le_rfl (objectProperty B S hS 𝒳)

end

/-! As in the lisse-étale case, the three declarations below assume nothing beyond the data of the
stack, essential smallness being the instance
`AlgebraicGeometry.Stack.essentiallySmall_obj_algebraicStack`. -/

/-- **The functor `g_!` of Stacks 0789 (2) on sheaves of modules**: the left adjoint of the
pullback `g^*` along the flat-fppf morphism of ringed topoi. -/
@[stacks 0789 "part (2), existence of the functor `g_!` on sheaves of modules for the flat-fppf \
site of an arbitrary algebraic stack"]
noncomputable abbrev moduleLowerShriek :=
  subsiteModuleLowerShriek B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids B.topology le_rfl
    (objectProperty B S hS 𝒳)

/-- **The adjunction `g_! ⊣ g^*` of Stacks 0789 (2) on sheaves of modules.** -/
@[stacks 0789 "part (2), left adjointness of `g_!` to `g^*` on sheaves of modules for the \
flat-fppf site of an arbitrary algebraic stack"]
noncomputable abbrev moduleLowerShriekAdjunction :
    moduleLowerShriek B S hS 𝒳 ⊣ modulePullback B S hS 𝒳 :=
  subsiteModuleLowerShriekAdjunction B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
    B.topology le_rfl (objectProperty B S hS 𝒳)

/-- **Stacks 0789 (2), `g^*g_! = id`**: the unit of the adjunction `g_! ⊣ g^*` on sheaves of
modules for the flat-fppf site is an isomorphism. -/
@[stacks 0789 "part (2), `g^*g_! = id` on sheaves of modules for the flat-fppf site of an \
arbitrary algebraic stack"]
theorem isIso_moduleLowerShriekAdjunction_unit :
    IsIso (moduleLowerShriekAdjunction B S hS 𝒳).unit :=
  isIso_subsiteModuleLowerShriekAdjunction_unit B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
    B.topology le_rfl (objectProperty B S hS 𝒳)

end FlatFppf

end AlgebraicGeometry.Stack

end
